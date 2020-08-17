// Copyright 2020 The gVisor Authors.
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

package verity

import (
	"bytes"
	"io"
	"strconv"

	"gvisor.dev/gvisor/pkg/abi/linux"
	"gvisor.dev/gvisor/pkg/context"
	"gvisor.dev/gvisor/pkg/fspath"
	"gvisor.dev/gvisor/pkg/merkletree"
	"gvisor.dev/gvisor/pkg/sentry/kernel/auth"
	"gvisor.dev/gvisor/pkg/sentry/socket/unix/transport"
	"gvisor.dev/gvisor/pkg/sentry/vfs"
	"gvisor.dev/gvisor/pkg/sync"
	"gvisor.dev/gvisor/pkg/syserror"
)

// Sync implements vfs.FilesystemImpl.Sync.
func (fs *filesystem) Sync(ctx context.Context) error {
	// All files should be read-only.
	return nil
}

var dentrySlicePool = sync.Pool{
	New: func() interface{} {
		ds := make([]*dentry, 0, 4) // arbitrary non-zero initial capacity
		return &ds
	},
}

func appendDentry(ds *[]*dentry, d *dentry) *[]*dentry {
	if ds == nil {
		ds = dentrySlicePool.Get().(*[]*dentry)
	}
	*ds = append(*ds, d)
	return ds
}

// Preconditions: ds != nil.
func putDentrySlice(ds *[]*dentry) {
	// Allow dentries to be GC'd.
	for i := range *ds {
		(*ds)[i] = nil
	}
	*ds = (*ds)[:0]
	dentrySlicePool.Put(ds)
}

// renameMuRUnlockAndCheckDrop calls fs.renameMu.RUnlock(), then calls
// dentry.checkDropLocked on all dentries in *ds with fs.renameMu locked for
// writing.
//
// ds is a pointer-to-pointer since defer evaluates its arguments immediately,
// but dentry slices are allocated lazily, and it's much easier to say "defer
// fs.renameMuRUnlockAndCheckDrop(&ds)" than "defer func() {
// fs.renameMuRUnlockAndCheckDrop(ds) }()" to work around this.
func (fs *filesystem) renameMuRUnlockAndCheckDrop(ctx context.Context, ds **[]*dentry) {
	fs.renameMu.RUnlock()
	if *ds == nil {
		return
	}
	if len(**ds) != 0 {
		fs.renameMu.Lock()
		for _, d := range **ds {
			d.checkDropLocked(ctx)
		}
		fs.renameMu.Unlock()
	}
	putDentrySlice(*ds)
}

func (fs *filesystem) renameMuUnlockAndCheckDrop(ctx context.Context, ds **[]*dentry) {
	if *ds == nil {
		fs.renameMu.Unlock()
		return
	}
	for _, d := range **ds {
		d.checkDropLocked(ctx)
	}
	fs.renameMu.Unlock()
	putDentrySlice(*ds)
}

// stepLocked resolves rp.Component() to an existing file, starting from the
// given directory.
//
// Dentries which may have a reference count of zero, and which therefore
// should be dropped once traversal is complete, are appended to ds.
//
// Preconditions: fs.renameMu must be locked. d.dirMu must be locked.
// !rp.Done().
func (fs *filesystem) stepLocked(ctx context.Context, rp *vfs.ResolvingPath, d *dentry, mayFollowSymlinks bool, ds **[]*dentry) (*dentry, error) {
	if !d.isDir() {
		return nil, syserror.ENOTDIR
	}

	if err := d.checkPermissions(rp.Credentials(), vfs.MayExec); err != nil {
		return nil, err
	}

afterSymlink:
	name := rp.Component()
	if name == "." {
		rp.Advance()
		return d, nil
	}
	if name == ".." {
		if isRoot, err := rp.CheckRoot(ctx, &d.vfsd); err != nil {
			return nil, err
		} else if isRoot || d.parent == nil {
			rp.Advance()
			return d, nil
		}
		if err := rp.CheckMount(ctx, &d.parent.vfsd); err != nil {
			return nil, err
		}
		rp.Advance()
		return d.parent, nil
	}
	child, err := fs.getChildLocked(ctx, d, name, ds)
	if err != nil {
		return nil, err
	}
	if err := rp.CheckMount(ctx, &child.vfsd); err != nil {
		return nil, err
	}
	if child.isSymlink() && mayFollowSymlinks && rp.ShouldFollowSymlink() {
		target, err := child.readlink(ctx)
		if err != nil {
			return nil, err
		}
		if err := rp.HandleSymlink(target); err != nil {
			return nil, err
		}
		goto afterSymlink // don't check the current directory again
	}
	rp.Advance()
	return child, nil
}

// verifyChildRoot verifies the root hash of child against the verified root
// hash of the parent. If verification fails, verity fs crashes the sentry, as
// it indicates a malicious behavior. It returns error instead if in
// noCrashOnVerificationFailure mode.
// verifyChildRoot returns a syserror if fails. The caller is responsible to
// decide whether to crash sentry or return error if verification fails.
// Preconditions: fs.renameMu must be locked. d.dirMu must be locked.
func (fs *filesystem) verifyChildRoot(ctx context.Context, parent *dentry, child *dentry) (*dentry, error) {
	vfsObj := fs.vfsfs.VirtualFilesystem()

	// Read the offset of the current file/directory from the extended
	// attributes of the corresponding Merkle tree file.
	// This is the offset of the root hash for the current file/directory in
	// its parent's Merkle tree file.
	off, err := vfsObj.GetxattrAt(ctx, fs.creds, &vfs.PathOperation{
		Root:  child.lowerMerkleVD,
		Start: child.lowerMerkleVD,
	}, &vfs.GetxattrOptions{
		Name: "user.merkle.offset",
		// Offset is a 32 bit integer.
		Size: 4,
	})
	if err != nil {
		return nil, err
	}
	offset, err := strconv.Atoi(off)
	if err != nil {
		return nil, syserror.EINVAL
	}

	// Open parent Merkle tree file to read and verify child's root hash.
	parentMerkleFD, err := vfsObj.OpenAt(ctx, fs.creds, &vfs.PathOperation{
		Root:  parent.lowerMerkleVD,
		Start: parent.lowerMerkleVD,
	}, &vfs.OpenOptions{
		Flags: linux.O_RDONLY,
	})
	if err != nil {
		return nil, err
	}

	// dataSize is the size of raw data for the Merkle tree. For a file,
	// dataSize is the size of the whole file. For a directory, dataSize is
	// the size of all its children's root hashes.
	dataSize, err := parentMerkleFD.Getxattr(ctx, &vfs.GetxattrOptions{
		Name: "user, merkle.datasize",
		Size: 4,
	})
	if err != nil {
		return nil, err
	}
	parentSize, err := strconv.Atoi(dataSize)
	if err != nil {
		return nil, syserror.EINVAL
	}
	fdReader := vfs.FileReadWriteSeeker{
		Fd:  parentMerkleFD,
		Ctx: ctx,
	}
	var buf bytes.Buffer
	if err := merkletree.Verify(&buf, &fdReader, &fdReader, int64(parentSize), int64(offset), int64(merkletree.DigestSize()), parent.rootHash, true /* dataAndTreeInSameFile */); err != nil && err != io.EOF {
		return nil, syserror.EACCES
	}
	child.rootHash = append(child.rootHash, buf.Bytes()...)
	return child, nil
}

// Preconditions: fs.renameMu must be locked. d.dirMu must be locked.
func (fs *filesystem) getChildLocked(ctx context.Context, parent *dentry, name string, ds **[]*dentry) (*dentry, error) {
	if child, ok := parent.children[name]; ok {
		// If runtime enable is not allowed, all cached children are
		// already verified. If runtime enable is allowed and the
		// parent directory is enabled, we should verify the child root
		// hash here because it may be cached before enabled.
		if fs.allowRuntimeEnable && len(parent.rootHash) != 0 {
			if _, err := fs.verifyChildRoot(ctx, parent, child); err != nil {
				if noCrashOnVerificationFailure {
					return nil, err
				}
				panic("Verification failed")
			}
		}
		return child, nil
	}
	child, err := fs.lookupAndVerifyLocked(ctx, parent, name)
	if err != nil {
		return nil, err
	}
	if parent.children == nil {
		parent.children = make(map[string]*dentry)
	}
	parent.children[name] = child
	// child's refcount is initially 0, so it may be dropped after traversal.
	*ds = appendDentry(*ds, child)
	return child, nil
}

// Preconditions: fs.renameMu must be locked. parent.dirMu must be locked.
func (fs *filesystem) lookupAndVerifyLocked(ctx context.Context, parent *dentry, name string) (*dentry, error) {
	child := fs.newDentry()
	vfsObj := fs.vfsfs.VirtualFilesystem()

	childPath := fspath.Parse(name)
	childVD, childErr := vfsObj.GetDentryAt(ctx, fs.creds, &vfs.PathOperation{
		Root:  parent.lowerVD,
		Start: parent.lowerVD,
		Path:  childPath,
	}, &vfs.GetDentryOptions{})

	childMerklePath := merklePrefix + name
	childMerkleVD, childMerkleErr := vfsObj.GetDentryAt(ctx, fs.creds, &vfs.PathOperation{
		Root:  parent.lowerVD,
		Start: parent.lowerVD,
		Path:  fspath.Parse(childMerklePath),
	}, &vfs.GetDentryOptions{})

	if childErr != nil && childMerkleErr == nil {
		// Failed to get child file/directory dentry. However the
		// corresponding Merkle tree is found. This indicates an attack
		// that removed/renamed the child.
		if noCrashOnVerificationFailure {
			child.destroyLocked(ctx)
			return nil, childErr
		}
		panic("Malicious file operation detected")
	} else if childErr == nil && childMerkleErr != nil {
		// The Merkle tree file should already exist, unless we allow
		// enforcing files to be built as verity in runtime. In that
		// case create the corresponding merkle tree file instead.
		if childMerkleErr == syserror.ENOENT && fs.allowRuntimeEnable {
			childMerkleFD, err := vfsObj.OpenAt(ctx, fs.creds, &vfs.PathOperation{
				Root:  parent.lowerVD,
				Start: parent.lowerVD,
				Path:  fspath.Parse(childMerklePath),
			}, &vfs.OpenOptions{
				Flags: linux.O_RDWR | linux.O_CREAT,
			})
			if err != nil {
				child.destroyLocked(ctx)
				return nil, err
			}
			childMerkleFD.DecRef(ctx)
			childMerkleVD, err = vfsObj.GetDentryAt(ctx, fs.creds, &vfs.PathOperation{
				Root:  parent.lowerVD,
				Start: parent.lowerVD,
				Path:  fspath.Parse(childMerklePath),
			}, &vfs.GetDentryOptions{})
			if err != nil {
				child.destroyLocked(ctx)
				return nil, err
			}
		} else {
			// If runtime enable is not allowed. This indicates an
			// attack that removed/renamed the Merkle tree file.
			if noCrashOnVerificationFailure {
				child.destroyLocked(ctx)
				return nil, childMerkleErr
			}
			panic("Malicious file operation detected")
		}
	} else if childErr != nil && childMerkleErr != nil {
		// Failed to get both child dentry and child Merkle dentry. This
		// could indicate an attack, but could also be that the given
		// name is incorrect. Don't panic in this case.
		child.destroyLocked(ctx)
		return nil, childErr
	}

	child.lowerVD = childVD
	child.lowerMerkleVD = childMerkleVD

	mask := uint32(linux.STATX_TYPE | linux.STATX_MODE | linux.STATX_UID | linux.STATX_GID)
	stat, err := vfsObj.StatAt(ctx, fs.creds, &vfs.PathOperation{
		Root:  childVD,
		Start: childVD,
	}, &vfs.StatOptions{
		Mask: mask,
	})
	if err != nil {
		child.destroyLocked(ctx)
		return nil, err
	}

	parent.IncRef()
	child.parent = parent
	child.name = name

	// TODO(b/162788573): Verify child metadata.
	child.mode = uint32(stat.Mode)
	child.uid = stat.UID
	child.gid = stat.GID

	// Verify child root hash. This should always be performed unless in
	// allowRuntimeEnable mode and the parent directory hasn't been enabled
	// yet.
	if !(fs.allowRuntimeEnable && len(parent.rootHash) == 0) {
		if _, err := fs.verifyChildRoot(ctx, parent, child); err != nil {
			child.destroyLocked(ctx)
			return nil, err
		}
	}

	return child, nil
}

// walkParentDirLocked resolves all but the last path component of rp to an
// existing directory, starting from the given directory (which is usually
// rp.Start().Impl().(*dentry)). It does not check that the returned directory
// is searchable by the provider of rp.
//
// Preconditions: fs.renameMu must be locked. !rp.Done().
func (fs *filesystem) walkParentDirLocked(ctx context.Context, rp *vfs.ResolvingPath, d *dentry, ds **[]*dentry) (*dentry, error) {
	for !rp.Final() {
		d.dirMu.Lock()
		next, err := fs.stepLocked(ctx, rp, d, true /* mayFollowSymlinks */, ds)
		d.dirMu.Unlock()
		if err != nil {
			return nil, err
		}
		d = next
	}
	if !d.isDir() {
		return nil, syserror.ENOTDIR
	}
	return d, nil
}

// resolveLocked resolves rp to an existing file.
//
// Preconditions: fs.renameMu must be locked.
func (fs *filesystem) resolveLocked(ctx context.Context, rp *vfs.ResolvingPath, ds **[]*dentry) (*dentry, error) {
	d := rp.Start().Impl().(*dentry)
	for !rp.Done() {
		d.dirMu.Lock()
		next, err := fs.stepLocked(ctx, rp, d, true /* mayFollowSymlinks */, ds)
		d.dirMu.Unlock()
		if err != nil {
			return nil, err
		}
		d = next
	}
	if rp.MustBeDir() && !d.isDir() {
		return nil, syserror.ENOTDIR
	}
	return d, nil
}

// AccessAt implements vfs.Filesystem.Impl.AccessAt.
func (fs *filesystem) AccessAt(ctx context.Context, rp *vfs.ResolvingPath, creds *auth.Credentials, ats vfs.AccessTypes) error {
	// Verity file system is read-only.
	if ats&vfs.MayWrite != 0 {
		return syserror.EROFS
	}
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	d, err := fs.resolveLocked(ctx, rp, &ds)
	if err != nil {
		return err
	}
	return d.checkPermissions(creds, ats)
}

// GetDentryAt implements vfs.FilesystemImpl.GetDentryAt.
func (fs *filesystem) GetDentryAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.GetDentryOptions) (*vfs.Dentry, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	d, err := fs.resolveLocked(ctx, rp, &ds)
	if err != nil {
		return nil, err
	}
	if opts.CheckSearchable {
		if !d.isDir() {
			return nil, syserror.ENOTDIR
		}
		if err := d.checkPermissions(rp.Credentials(), vfs.MayExec); err != nil {
			return nil, err
		}
	}
	d.IncRef()
	return &d.vfsd, nil
}

// GetParentDentryAt implements vfs.FilesystemImpl.GetParentDentryAt.
func (fs *filesystem) GetParentDentryAt(ctx context.Context, rp *vfs.ResolvingPath) (*vfs.Dentry, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	start := rp.Start().Impl().(*dentry)
	d, err := fs.walkParentDirLocked(ctx, rp, start, &ds)
	if err != nil {
		return nil, err
	}
	d.IncRef()
	return &d.vfsd, nil
}

// LinkAt implements vfs.FilesystemImpl.LinkAt.
func (fs *filesystem) LinkAt(ctx context.Context, rp *vfs.ResolvingPath, vd vfs.VirtualDentry) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// MkdirAt implements vfs.FilesystemImpl.MkdirAt.
func (fs *filesystem) MkdirAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.MkdirOptions) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// MknodAt implements vfs.FilesystemImpl.MknodAt.
func (fs *filesystem) MknodAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.MknodOptions) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// OpenAt implements vfs.FilesystemImpl.OpenAt.
func (fs *filesystem) OpenAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.OpenOptions) (*vfs.FileDescription, error) {
	//TODO(b/159261227): Implement OpenAt.
	return nil, nil
}

// ReadlinkAt implements vfs.FilesystemImpl.ReadlinkAt.
func (fs *filesystem) ReadlinkAt(ctx context.Context, rp *vfs.ResolvingPath) (string, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	d, err := fs.resolveLocked(ctx, rp, &ds)
	if err != nil {
		return "", err
	}
	//TODO(b/162787271): Provide integrity check for ReadlinkAt.
	return fs.vfsfs.VirtualFilesystem().ReadlinkAt(ctx, d.fs.creds, &vfs.PathOperation{
		Root:  d.lowerVD,
		Start: d.lowerVD,
	})
}

// RenameAt implements vfs.FilesystemImpl.RenameAt.
func (fs *filesystem) RenameAt(ctx context.Context, rp *vfs.ResolvingPath, oldParentVD vfs.VirtualDentry, oldName string, opts vfs.RenameOptions) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// RmdirAt implements vfs.FilesystemImpl.RmdirAt.
func (fs *filesystem) RmdirAt(ctx context.Context, rp *vfs.ResolvingPath) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// SetStatAt implements vfs.FilesystemImpl.SetStatAt.
func (fs *filesystem) SetStatAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.SetStatOptions) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// StatAt implements vfs.FilesystemImpl.StatAt.
func (fs *filesystem) StatAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.StatOptions) (linux.Statx, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	d, err := fs.resolveLocked(ctx, rp, &ds)
	if err != nil {
		return linux.Statx{}, err
	}

	var stat linux.Statx
	stat, err = fs.vfsfs.VirtualFilesystem().StatAt(ctx, fs.creds, &vfs.PathOperation{
		Root:  d.lowerVD,
		Start: d.lowerVD,
	}, &opts)
	if err != nil {
		return linux.Statx{}, err
	}
	return stat, nil
}

// StatFSAt implements vfs.FilesystemImpl.StatFSAt.
func (fs *filesystem) StatFSAt(ctx context.Context, rp *vfs.ResolvingPath) (linux.Statfs, error) {
	// TODO(b/159261227): Implement StatFSAt.
	return linux.Statfs{}, nil
}

// SymlinkAt implements vfs.FilesystemImpl.SymlinkAt.
func (fs *filesystem) SymlinkAt(ctx context.Context, rp *vfs.ResolvingPath, target string) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// UnlinkAt implements vfs.FilesystemImpl.UnlinkAt.
func (fs *filesystem) UnlinkAt(ctx context.Context, rp *vfs.ResolvingPath) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// BoundEndpointAt implements FilesystemImpl.BoundEndpointAt.
func (fs *filesystem) BoundEndpointAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.BoundEndpointOptions) (transport.BoundEndpoint, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	if _, err := fs.resolveLocked(ctx, rp, &ds); err != nil {
		return nil, err
	}
	return nil, syserror.ECONNREFUSED
}

// ListxattrAt implements vfs.FilesystemImpl.ListxattrAt.
func (fs *filesystem) ListxattrAt(ctx context.Context, rp *vfs.ResolvingPath, size uint64) ([]string, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	d, err := fs.resolveLocked(ctx, rp, &ds)
	if err != nil {
		return nil, err
	}
	lowerVD := d.lowerVD
	return fs.vfsfs.VirtualFilesystem().ListxattrAt(ctx, d.fs.creds, &vfs.PathOperation{
		Root:  lowerVD,
		Start: lowerVD,
	}, size)
}

// GetxattrAt implements vfs.FilesystemImpl.GetxattrAt.
func (fs *filesystem) GetxattrAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.GetxattrOptions) (string, error) {
	var ds *[]*dentry
	fs.renameMu.RLock()
	defer fs.renameMuRUnlockAndCheckDrop(ctx, &ds)
	d, err := fs.resolveLocked(ctx, rp, &ds)
	if err != nil {
		return "", err
	}
	lowerVD := d.lowerVD
	return fs.vfsfs.VirtualFilesystem().GetxattrAt(ctx, d.fs.creds, &vfs.PathOperation{
		Root:  lowerVD,
		Start: lowerVD,
	}, &opts)
}

// SetxattrAt implements vfs.FilesystemImpl.SetxattrAt.
func (fs *filesystem) SetxattrAt(ctx context.Context, rp *vfs.ResolvingPath, opts vfs.SetxattrOptions) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// RemovexattrAt implements vfs.FilesystemImpl.RemovexattrAt.
func (fs *filesystem) RemovexattrAt(ctx context.Context, rp *vfs.ResolvingPath, name string) error {
	// Verity file system is read-only.
	return syserror.EROFS
}

// PrependPath implements vfs.FilesystemImpl.PrependPath.
func (fs *filesystem) PrependPath(ctx context.Context, vfsroot, vd vfs.VirtualDentry, b *fspath.Builder) error {
	fs.renameMu.RLock()
	defer fs.renameMu.RUnlock()
	mnt := vd.Mount()
	d := vd.Dentry().Impl().(*dentry)
	for {
		if mnt == vfsroot.Mount() && &d.vfsd == vfsroot.Dentry() {
			return vfs.PrependPathAtVFSRootError{}
		}
		if &d.vfsd == mnt.Root() {
			return nil
		}
		if d.parent == nil {
			return vfs.PrependPathAtNonMountRootError{}
		}
		b.PrependComponent(d.name)
		d = d.parent
	}
}
