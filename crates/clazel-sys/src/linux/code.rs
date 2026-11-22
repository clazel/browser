//! Linux code regions (jit.md item J.7): a sealed `memfd` with two mappings.
//!
//! The **writer** (the code process, or a thread of the renderer's launcher
//! before sandboxing) makes a [`SharedCode`], maps it read-write with
//! [`SharedCode::map_writable`] and writes validated blobs. The **renderer**
//! maps the same memory read-execute with [`SharedCode::map_executable`]
//! *before* its seccomp filter goes on; the filter then refuses `PROT_EXEC`
//! on `mmap` and `mprotect` for good (jit.md J.0(b), J.8), so the renderer can
//! run the code but never make memory executable itself. The descriptor is
//! sealed against growing and shrinking (`F_SEAL_GROW`, `F_SEAL_SHRINK`,
//! `F_SEAL_SEAL`), so a writer cannot cut the file under a mapping and make
//! the renderer fault; `F_SEAL_WRITE` is not used, because the writer's
//! mapping is writable by design.
//!
//! Instruction-cache maintenance is the enter stub's first instructions on
//! A64 (`crate::code`: `dc cvau` and `ic ivau` over the region, then `dsb` and
//! `isb`), not a system call. Nothing here decides a size or what to write:
//! the caller does.
//!
//! `vm.memfd_noexec` (Linux 6.3 and later): at 0 (the default) a `memfd` can
//! be mapped executable; at 1 a plain `memfd_create` makes a no-exec file, so
//! [`SharedCode::create`] passes `MFD_EXEC` to say what it needs; at 2
//! `MFD_EXEC` is refused (`EACCES`), the region cannot exist, and `create`
//! fails with that error. On a kernel before 6.3 `MFD_EXEC` is an unknown flag
//! (`EINVAL`) and `create` retries without it.

use std::ffi::c_void;

use crate::code::{STUB, check_size, write_range};
use crate::{CodeError, Errno};

/// `MFD_EXEC` (linux/memfd.h, Linux 6.3): the file may be made executable.
/// Not in `libc` 0.2.190.
const MFD_EXEC: libc::c_uint = 0x0010;

/// A sealed anonymous file the code lives in. It owns its descriptor and
/// closes it on drop.
#[derive(Debug)]
pub struct SharedCode {
    fd: libc::c_int,
    len: usize,
}

/// A read-write mapping of a [`SharedCode`], for the writer. Unmapped on
/// drop.
#[derive(Debug)]
pub struct CodeWriter {
    base: usize,
    len: usize,
}

/// A read-execute mapping of a [`SharedCode`], for the renderer. Unmapped on
/// drop. [`crate::enter`] runs code in it.
#[derive(Debug)]
pub struct CodeRegion {
    base: usize,
    len: usize,
}

/// The seals every region carries: the size can never change.
const SEALS: libc::c_int = libc::F_SEAL_SHRINK | libc::F_SEAL_GROW | libc::F_SEAL_SEAL;

impl SharedCode {
    /// A new region of `len` bytes (a multiple of the page size, larger than
    /// [`crate::CODE_START`]), zero-filled, sealed against resizing, with the enter
    /// stub already written at offset 0. The descriptor is close-on-exec; see
    /// [`SharedCode::inheritable_fd`].
    ///
    /// # Errors
    ///
    /// [`CodeError::BadSize`], or the failing call's `errno`.
    pub fn create(len: usize) -> Result<SharedCode, CodeError> {
        check_size(len)?;
        let size = libc::off_t::try_from(len).map_err(|_| CodeError::BadSize)?;
        let base: libc::c_uint = libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING;
        let mut fd = memfd(base | MFD_EXEC);
        if fd < 0 && Errno::last().0 == libc::EINVAL {
            // Before Linux 6.3 MFD_EXEC is an unknown flag.
            fd = memfd(base);
        }
        if fd < 0 {
            return Err(CodeError::os("memfd_create"));
        }
        // From here `shared` owns `fd` and closes it on any early return.
        let shared = SharedCode { fd, len };
        // SAFETY: man 2 ftruncate: `ftruncate(fd, length)` sets the size of
        // the file open on `fd` to `length` bytes, and returns 0, or -1 and
        // sets errno. The `libc::ftruncate(c_int, off_t) -> c_int` declaration
        // matches. `fd` is the open descriptor `shared` owns, and `size` is
        // `len` converted with a checked conversion.
        let rc = unsafe { libc::ftruncate(shared.fd, size) };
        if rc != 0 {
            return Err(CodeError::os("ftruncate"));
        }
        // SAFETY: man 2 fcntl, "File sealing": `fcntl(fd, F_ADD_SEALS, seals)`
        // adds the seals in the `int` argument to a file opened with
        // MFD_ALLOW_SEALING, and returns 0, or -1 and sets errno. The variadic
        // `libc::fcntl(c_int, c_int, ...) -> c_int` declaration matches: `fd`
        // is open, `F_ADD_SEALS` is the command and `SEALS` (a `c_int`, the
        // type the command reads) is the one variadic argument. No pointer is
        // passed.
        let rc = unsafe { libc::fcntl(shared.fd, libc::F_ADD_SEALS, SEALS) };
        if rc != 0 {
            return Err(CodeError::os("fcntl"));
        }
        let mut writer = shared.map_writable()?;
        writer.install_stub()?;
        drop(writer);
        Ok(shared)
    }

    /// Use the region behind descriptor number `fd`, which a region
    /// [`SharedCode::create`] made (the renderer receives the number from the
    /// writer, by inheritance). Checked: the file must be sealed against
    /// growing and shrinking, which is how its size can be trusted.
    ///
    /// The number is **borrowed, not taken over**: this duplicates it
    /// (`F_DUPFD_CLOEXEC`) and owns only the duplicate, closing it on drop and
    /// on every error path; `fd` itself is left open and never closed, as
    /// `Inherited::open` does on Windows. So a wrong number (`1`, say) or the
    /// number of a value that is still alive cannot be closed twice. Call
    /// [`SharedCode::map_executable`], then drop this value, before the seccomp
    /// filter goes on.
    ///
    /// # Errors
    ///
    /// [`CodeError::NotACodeRegion`] if the descriptor is not sealed as
    /// above or its size is not larger than the stub. The failing call's
    /// `errno` if it is not open.
    pub fn adopt(fd: libc::c_int) -> Result<SharedCode, CodeError> {
        let lowest: libc::c_int = 3;
        // SAFETY: man 2 fcntl: `fcntl(fd, F_DUPFD_CLOEXEC, lowest)` returns a
        // new close-on-exec descriptor for the same open file, the lowest
        // free number at least `lowest`, or -1 and sets errno (EBADF if `fd`
        // is not open). The variadic `libc::fcntl(c_int, c_int, ...) -> c_int`
        // declaration matches: `F_DUPFD_CLOEXEC` is the command and `lowest`
        // is a `c_int`, the type it reads. `fd` is only a number; the call
        // neither reads nor writes memory, and it changes nothing about `fd`.
        let dup = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, lowest) };
        if dup < 0 {
            return Err(CodeError::os("fcntl"));
        }
        // From here `shared` owns the duplicate, which nothing else knows, and
        // closes it on any early return.
        let mut shared = SharedCode { fd: dup, len: 0 };
        // SAFETY: man 2 fcntl, "File sealing": `fcntl(fd, F_GET_SEALS)` returns
        // the seals of the file as a non-negative `int`, or -1 and sets errno
        // (EINVAL if the file does not support sealing). The variadic
        // `libc::fcntl(c_int, c_int, ...) -> c_int` declaration matches: the
        // command takes no further argument. `shared.fd` is the open duplicate
        // this value owns; nothing is read or written through it.
        let seals = unsafe { libc::fcntl(shared.fd, libc::F_GET_SEALS) };
        if seals < 0 {
            return Err(CodeError::os("fcntl"));
        }
        if seals & SEALS != SEALS {
            return Err(CodeError::NotACodeRegion);
        }
        // SAFETY: man 2 lseek: `lseek(fd, 0, SEEK_END)` returns the size of the
        // file as the new offset (a regular file or memfd), or -1 and sets
        // errno. The `libc::lseek(c_int, off_t, c_int) -> off_t` declaration
        // matches. `shared.fd` is open (the call above succeeded).
        let end = unsafe { libc::lseek(shared.fd, 0, libc::SEEK_END) };
        if end < 0 {
            return Err(CodeError::os("lseek"));
        }
        let len = usize::try_from(end).map_err(|_| CodeError::NotACodeRegion)?;
        check_size(len).map_err(|_| CodeError::NotACodeRegion)?;
        shared.len = len;
        Ok(shared)
    }

    /// The region's size in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Always false: a region is larger than the stub.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Clear close-on-exec on the descriptor and return its number, so that
    /// the one child the caller starts next inherits it at that number. The
    /// number stays owned by this value (it is only a number to hand to the
    /// child, which gives it to [`SharedCode::adopt`]); the caller is the
    /// launcher; this makes no other change.
    ///
    /// # Errors
    ///
    /// The failing `fcntl`'s `errno`.
    pub fn inheritable_fd(&self) -> Result<i32, CodeError> {
        let flags: libc::c_int = 0;
        // SAFETY: man 2 fcntl: `fcntl(fd, F_SETFD, arg)` sets the descriptor
        // flags (only FD_CLOEXEC is defined, so 0 clears it) and returns 0, or
        // -1 and sets errno. The variadic `libc::fcntl(c_int, c_int, ...) ->
        // c_int` declaration matches: `fd` is open (this value owns it),
        // `F_SETFD` is the command and `flags` is a `c_int`, the type it reads.
        // No pointer is passed.
        let rc = unsafe { libc::fcntl(self.fd, libc::F_SETFD, flags) };
        if rc == -1 {
            return Err(CodeError::os("fcntl"));
        }
        Ok(self.fd)
    }

    /// Map the whole region read-write: the writer's view.
    ///
    /// # Errors
    ///
    /// The failing `mmap`'s `errno`.
    pub fn map_writable(&self) -> Result<CodeWriter, CodeError> {
        let base = self.map(libc::PROT_READ | libc::PROT_WRITE)?;
        Ok(CodeWriter {
            base,
            len: self.len,
        })
    }

    /// Map the whole region read-execute, and check that it starts with the
    /// enter stub: the renderer's view. Do this before the seccomp filter
    /// goes on. Nothing writes through this mapping, and the descriptor
    /// can be dropped afterwards.
    ///
    /// # Errors
    ///
    /// The failing `mmap`'s `errno`, or [`CodeError::NotACodeRegion`] if the
    /// first bytes are not the stub.
    pub fn map_executable(&self) -> Result<CodeRegion, CodeError> {
        let base = self.map(libc::PROT_READ | libc::PROT_EXEC)?;
        let region = CodeRegion {
            base,
            len: self.len,
        };
        let mut head = vec![0u8; STUB.len()];
        copy_out(region.base, &mut head);
        if head != STUB {
            return Err(CodeError::NotACodeRegion);
        }
        Ok(region)
    }

    /// `mmap` the whole file `MAP_SHARED` with `prot`; the address.
    fn map(&self, prot: libc::c_int) -> Result<usize, CodeError> {
        let any_address: *mut c_void = std::ptr::null_mut();
        // SAFETY: man 2 mmap: `mmap(addr, length, prot, flags, fd, offset)` with
        // a null `addr` (`any_address`) maps `length` bytes of the file at a kernel-chosen
        // address and returns it, or MAP_FAILED and sets errno; MAP_SHARED
        // makes writes through one mapping visible through the others and
        // `offset` 0 is page aligned. The `libc::mmap(*mut c_void, size_t,
        // c_int, c_int, c_int, off_t) -> *mut c_void` declaration matches.
        // `fd` is the open descriptor this value owns, `len` is its sealed size,
        // and `prot` is PROT_READ with PROT_WRITE or PROT_EXEC. The mapping is
        // new memory, so it aliases nothing the program holds.
        let p = unsafe { libc::mmap(any_address, self.len, prot, libc::MAP_SHARED, self.fd, 0) };
        if p == libc::MAP_FAILED {
            return Err(CodeError::os("mmap"));
        }
        Ok(p as usize)
    }
}

impl Drop for SharedCode {
    fn drop(&mut self) {
        // SAFETY: man 2 close: `close(fd)` closes the descriptor. The
        // `libc::close(c_int) -> c_int` declaration matches. `fd` is open and
        // owned by this value (made by `memfd_create` or duplicated by `adopt`,
        // and never handed out as an owned number), which is being dropped, so
        // it is closed once. The result is ignored: nothing can be done about a
        // failed close.
        let _ = unsafe { libc::close(self.fd) };
    }
}

/// `memfd_create` with `flags`; the descriptor, or -1 with `errno` set.
fn memfd(flags: libc::c_uint) -> libc::c_int {
    let name: *const libc::c_char = c"clazel-code".as_ptr();
    // SAFETY: man 2 memfd_create: `memfd_create(name, flags)` creates an
    // anonymous file and returns its descriptor, or -1 and sets errno; the
    // name is only a debugging label and must be a NUL-terminated string of at
    // most 249 bytes, and the flags are those of `create` (MFD_CLOEXEC,
    // MFD_ALLOW_SEALING, and MFD_EXEC, which a kernel before 6.3 refuses with
    // EINVAL). The `libc::memfd_create(*const c_char, c_uint) -> c_int`
    // declaration matches. `name` points to the NUL-terminated string literal
    // `c"clazel-code"`, which lives for the whole program.
    unsafe { libc::memfd_create(name, flags) }
}

impl CodeWriter {
    /// The region's size in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Always false: a region is larger than the stub.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Write `bytes` at `offset` from the region's start. The stub is not
    /// writable: `offset` must be at least [`crate::CODE_START`], and the write must
    /// end inside the region.
    ///
    /// # Errors
    ///
    /// [`CodeError::OutOfRange`].
    pub fn write(&mut self, offset: usize, bytes: &[u8]) -> Result<(), CodeError> {
        write_range(self.len, offset, bytes)?;
        self.copy_in(offset, bytes)
    }

    /// Write the stub at offset 0 (only [`SharedCode::create`] does).
    fn install_stub(&mut self) -> Result<(), CodeError> {
        self.copy_in(0, STUB)
    }

    /// Copy `bytes` to `offset`, which the caller has checked.
    fn copy_in(&mut self, offset: usize, bytes: &[u8]) -> Result<(), CodeError> {
        let end = offset
            .checked_add(bytes.len())
            .ok_or(CodeError::OutOfRange)?;
        if end > self.len {
            return Err(CodeError::OutOfRange);
        }
        if bytes.is_empty() {
            return Ok(());
        }
        let dst = self.base.checked_add(offset).ok_or(CodeError::OutOfRange)? as *mut c_void;
        let src: *const c_void = bytes.as_ptr().cast();
        let n: libc::size_t = bytes.len();
        // SAFETY: man 3 memcpy: `memcpy(dest, src, n)` copies `n` bytes from
        // `src` to `dest`, which must not overlap, and returns `dest`. The
        // `libc::memcpy(*mut c_void, *const c_void, size_t) -> *mut c_void`
        // declaration matches. `dst` is `n` bytes inside this value's read-write
        // mapping (the sum of `base` and `offset` was checked against `len`
        // above, and the mapping lasts as long as `self`); `src` is the live
        // slice `bytes`, a different allocation, and `n` is its length.
        let _ = unsafe { libc::memcpy(dst, src, n) };
        Ok(())
    }
}

impl Drop for CodeWriter {
    fn drop(&mut self) {
        unmap(self.base, self.len);
    }
}

impl CodeRegion {
    /// The region's size in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Always false: a region is larger than the stub.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The address of the region's first byte (the stub).
    pub(crate) fn base(&self) -> usize {
        self.base
    }
}

impl Drop for CodeRegion {
    fn drop(&mut self) {
        unmap(self.base, self.len);
    }
}

/// Copy `out.len()` bytes from the mapping at `base` into `out`.
fn copy_out(base: usize, out: &mut [u8]) {
    let src = base as *const c_void;
    let dst: *mut c_void = out.as_mut_ptr().cast();
    let n: libc::size_t = out.len();
    // SAFETY: man 3 memcpy: `memcpy(dest, src, n)` copies `n` bytes from `src`
    // to `dest`, which must not overlap. The `libc::memcpy(*mut c_void, *const
    // c_void, size_t) -> *mut c_void` declaration matches. `src` is the start of
    // a read-only mapping of at least `STUB.len()` bytes (`n`; `check_size`
    // made every region larger than the stub) that the caller holds, `dst` is
    // the live slice `out`, a different allocation, and `n` is its length.
    let _ = unsafe { libc::memcpy(dst, src, n) };
}

/// `munmap` a mapping this module made.
fn unmap(base: usize, len: usize) {
    // SAFETY: man 2 munmap: `munmap(addr, length)` removes the mappings in the
    // range and returns 0, or -1 and sets errno. The `libc::munmap(*mut c_void,
    // size_t) -> c_int` declaration matches. `base` and `len` are exactly the
    // address and length `mmap` returned and was given for a mapping that its
    // owner (the value being dropped) has not unmapped before, and no reference
    // into it exists. The result is ignored: nothing can be done about it.
    let _ = unsafe { libc::munmap(base as *mut c_void, len) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::{EXIT_42, exit_with};
    use crate::{CODE_START, Context, Exit, Validated, enter};

    /// A multiple of every page size Linux uses.
    const SIZE: usize = 65_536;

    #[test]
    #[cfg_attr(
        miri,
        ignore = "foreign calls and generated code cannot run under Miri"
    )]
    fn a_blob_written_by_the_writer_runs_in_the_executable_mapping() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let mut writer = shared.map_writable()?;
        writer.write(CODE_START, EXIT_42)?;
        let region = shared.map_executable()?;
        let mut ctx = Context::new();
        assert_eq!(ctx.exit_code(), 0);
        let exit = enter(&region, Validated::new(CODE_START), &mut ctx)?;
        assert_eq!(exit, Exit(42));
        assert_eq!(ctx.exit_code(), 42);
        // Re-entry with a fresh context works, and the writer's mapping is
        // still there (the renderer drops its descriptor, not the writer's).
        let mut again = Context::new();
        assert_eq!(
            enter(&region, Validated::new(CODE_START), &mut again)?,
            Exit(42)
        );
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn a_blob_written_after_the_executable_mapping_is_seen() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let region = shared.map_executable()?;
        let mut writer = shared.map_writable()?;
        writer.write(CODE_START, EXIT_42)?;
        let mut ctx = Context::new();
        assert_eq!(
            enter(&region, Validated::new(CODE_START), &mut ctx)?,
            Exit(42)
        );
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn a_blob_replaced_in_place_runs_as_replaced() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let mut writer = shared.map_writable()?;
        let region = shared.map_executable()?;
        for code in [1u8, 2, 3, 1, 7] {
            writer.write(CODE_START, &exit_with(code))?;
            let mut ctx = Context::new();
            assert_eq!(
                enter(&region, Validated::new(CODE_START), &mut ctx)?,
                Exit(u64::from(code))
            );
        }
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn enter_refuses_entries_outside_the_blob_area() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let mut writer = shared.map_writable()?;
        writer.write(CODE_START, EXIT_42)?;
        let region = shared.map_executable()?;
        let mut ctx = Context::new();
        for offset in [
            0,
            1,
            CODE_START.saturating_sub(1),
            SIZE,
            SIZE.saturating_add(16),
            usize::MAX,
        ] {
            assert_eq!(
                enter(&region, Validated::new(offset), &mut ctx),
                Err(CodeError::OutOfRange),
                "offset {offset}"
            );
        }
        assert_eq!(ctx.exit_code(), 0);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(
            enter(
                &region,
                Validated::new(CODE_START.saturating_add(2)),
                &mut ctx
            ),
            Err(CodeError::Misaligned)
        );
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn the_writer_cannot_reach_the_stub_or_leave_the_region() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let mut writer = shared.map_writable()?;
        assert_eq!(writer.write(0, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(
            writer.write(CODE_START.saturating_sub(1), &[0]),
            Err(CodeError::OutOfRange)
        );
        assert_eq!(writer.write(SIZE, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(
            writer.write(SIZE.saturating_sub(1), &[0, 0]),
            Err(CodeError::OutOfRange)
        );
        assert_eq!(writer.write(SIZE.saturating_sub(1), &[0]), Ok(()));
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn sizes_are_checked() {
        assert_eq!(SharedCode::create(0).err(), Some(CodeError::BadSize));
        assert_eq!(
            SharedCode::create(CODE_START).err(),
            Some(CodeError::BadSize)
        );
        assert_eq!(
            SharedCode::create(usize::MAX).err(),
            Some(CodeError::BadSize)
        );
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn adopt_checks_the_descriptor() -> Result<(), CodeError> {
        // A descriptor that is not open.
        assert!(matches!(
            SharedCode::adopt(-1),
            Err(CodeError::Os { call: "fcntl", .. })
        ));
        // An open descriptor that is not a code region: stdin is borrowed
        // (duplicated, the duplicate closed) and stays open.
        assert!(SharedCode::adopt(0).is_err());
        assert!(SharedCode::adopt(0).is_err());
        // An open, sealed one, by number as an inheriting child would get it,
        // while the original is alive: each is closed once.
        let shared = SharedCode::create(SIZE)?;
        let n = shared.inheritable_fd()?;
        let mut writer = shared.map_writable()?;
        writer.write(CODE_START, EXIT_42)?;
        let adopted = SharedCode::adopt(n)?;
        assert_eq!(adopted.len(), SIZE);
        let region = adopted.map_executable()?;
        drop(adopted);
        let mut ctx = Context::new();
        assert_eq!(
            enter(&region, Validated::new(CODE_START), &mut ctx)?,
            Exit(42)
        );
        // The original is still open after the adopted one closed its duplicate.
        assert!(shared.map_executable().is_ok());
        // Adopting twice from one number is fine too.
        let a = SharedCode::adopt(n)?;
        let b = SharedCode::adopt(n)?;
        assert_eq!(a.len(), b.len());
        Ok(())
    }
}
