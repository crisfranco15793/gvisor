// Copyright 2018 The gVisor Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package ipv4

import (
	"gvisor.dev/gvisor/pkg/tcpip/buffer"
	"gvisor.dev/gvisor/pkg/tcpip/header"
	"gvisor.dev/gvisor/pkg/tcpip/stack"
)

// handleControl handles the case when an ICMP packet contains the headers of
// the original packet that caused the ICMP one to be sent. This information is
// used to find out which transport endpoint must be notified about the ICMP
// packet.
func (e *endpoint) handleControl(typ stack.ControlType, extra uint32, pkt *stack.PacketBuffer) {
	h, ok := pkt.Data.PullUp(header.IPv4MinimumSize)
	if !ok {
		return
	}
	hdr := header.IPv4(h)

	// We don't use IsValid() here because ICMP only requires that the IP
	// header plus 8 bytes of the transport header be included. So it's
	// likely that it is truncated, which would cause IsValid to return
	// false.
	//
	// Drop packet if it doesn't have the basic IPv4 header or if the
	// original source address doesn't match an address we own.
	src := hdr.SourceAddress()
	if e.stack.CheckLocalAddress(e.NICID(), ProtocolNumber, src) == 0 {
		return
	}

	hlen := int(hdr.HeaderLength())
	if pkt.Data.Size() < hlen || hdr.FragmentOffset() != 0 {
		// We won't be able to handle this if it doesn't contain the
		// full IPv4 header, or if it's a fragment not at offset 0
		// (because it won't have the transport header).
		return
	}

	// Skip the ip header, then deliver control message.
	pkt.Data.TrimFront(hlen)
	p := hdr.TransportProtocol()
	e.dispatcher.DeliverTransportControlPacket(src, hdr.DestinationAddress(), ProtocolNumber, p, typ, extra, pkt)
}

func (e *endpoint) handleICMP(r *stack.Route, pkt *stack.PacketBuffer) {
	stats := r.Stats()
	received := stats.ICMP.V4PacketsReceived
	// TODO(gvisor.dev/issue/170): ICMP packets don't have their
	// TransportHeader fields set. See icmp/protocol.go:protocol.Parse for a
	// full explanation.
	v, ok := pkt.Data.PullUp(header.ICMPv4MinimumSize)
	if !ok {
		received.Invalid.Increment()
		return
	}
	h := header.ICMPv4(v)

	// TODO(b/112892170): Meaningfully handle all ICMP types.
	switch h.Type() {
	case header.ICMPv4Echo:
		received.Echo.Increment()

		// Only send a reply if the checksum is valid.
		wantChecksum := h.Checksum()
		// Reset the checksum field to 0 to can calculate the proper
		// checksum. We'll have to reset this before we hand the packet
		// off.
		h.SetChecksum(0)
		gotChecksum := ^header.ChecksumVV(pkt.Data, 0 /* initial */)
		if gotChecksum != wantChecksum {
			// It's possible that a raw socket expects to receive this.
			h.SetChecksum(wantChecksum)
			e.dispatcher.DeliverTransportPacket(r, header.ICMPv4ProtocolNumber, pkt)
			received.Invalid.Increment()
			return
		}

		// Make a copy of data before pkt gets sent to raw socket.
		// DeliverTransportPacket will take ownership of pkt.
		replyData := pkt.Data.Clone(nil)
		replyData.TrimFront(header.ICMPv4MinimumSize)

		// It's possible that a raw socket expects to receive this.
		h.SetChecksum(wantChecksum)
		e.dispatcher.DeliverTransportPacket(r, header.ICMPv4ProtocolNumber, pkt)

		remoteLinkAddr := r.RemoteLinkAddress

		// As per RFC 1122 section 3.2.1.3, when a host sends any datagram, the IP
		// source address MUST be one of its own IP addresses (but not a broadcast
		// or multicast address).
		localAddr := r.LocalAddress
		if r.IsInboundBroadcast() || header.IsV4MulticastAddress(r.LocalAddress) {
			localAddr = ""
		}

		r, err := r.Stack().FindRoute(e.NICID(), localAddr, r.RemoteAddress, ProtocolNumber, false /* multicastLoop */)
		if err != nil {
			// If we cannot find a route to the destination, silently drop the packet.
			return
		}
		defer r.Release()

		// Use the remote link address from the incoming packet.
		r.ResolveWith(remoteLinkAddr)

		// Prepare a reply packet.
		icmpHdr := make(header.ICMPv4, header.ICMPv4MinimumSize)
		copy(icmpHdr, h)
		icmpHdr.SetType(header.ICMPv4EchoReply)
		icmpHdr.SetChecksum(0)
		icmpHdr.SetChecksum(^header.Checksum(icmpHdr, header.ChecksumVV(replyData, 0)))
		dataVV := buffer.View(icmpHdr).ToVectorisedView()
		dataVV.Append(replyData)
		replyPkt := stack.NewPacketBuffer(stack.PacketBufferOptions{
			ReserveHeaderBytes: int(r.MaxHeaderLength()),
			Data:               dataVV,
		})

		// Send out the reply packet.
		sent := stats.ICMP.V4PacketsSent
		if err := r.WritePacket(nil /* gso */, stack.NetworkHeaderParams{
			Protocol: header.ICMPv4ProtocolNumber,
			TTL:      r.DefaultTTL(),
			TOS:      stack.DefaultTOS,
		}, replyPkt); err != nil {
			sent.Dropped.Increment()
			return
		}
		sent.EchoReply.Increment()

	case header.ICMPv4EchoReply:
		received.EchoReply.Increment()

		e.dispatcher.DeliverTransportPacket(r, header.ICMPv4ProtocolNumber, pkt)

	case header.ICMPv4DstUnreachable:
		received.DstUnreachable.Increment()

		pkt.Data.TrimFront(header.ICMPv4MinimumSize)
		switch h.Code() {
		case header.ICMPv4HostUnreachable:
			e.handleControl(stack.ControlNoRoute, 0, pkt)

		case header.ICMPv4PortUnreachable:
			e.handleControl(stack.ControlPortUnreachable, 0, pkt)

		case header.ICMPv4FragmentationNeeded:
			mtu := uint32(h.MTU())
			e.handleControl(stack.ControlPacketTooBig, calculateMTU(mtu), pkt)
		}

	case header.ICMPv4SrcQuench:
		received.SrcQuench.Increment()

	case header.ICMPv4Redirect:
		received.Redirect.Increment()

	case header.ICMPv4TimeExceeded:
		received.TimeExceeded.Increment()

	case header.ICMPv4ParamProblem:
		received.ParamProblem.Increment()

	case header.ICMPv4Timestamp:
		received.Timestamp.Increment()

	case header.ICMPv4TimestampReply:
		received.TimestampReply.Increment()

	case header.ICMPv4InfoRequest:
		received.InfoRequest.Increment()

	case header.ICMPv4InfoReply:
		received.InfoReply.Increment()

	default:
		received.Invalid.Increment()
	}
}
