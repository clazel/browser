//! Windows code regions (jit.md item J.7): a section with a writable view in
//! the writer and a read-execute view in the renderer.
//!
//! The **writer** (the code process) makes a [`SharedCode`] (a pagefile-backed
//! section), maps it read-write in itself ([`SharedCode::map_writable`]) and
//! writes validated blobs. It maps the same section **into the renderer** with
//! `PAGE_EXECUTE_READ` ([`SharedCode::map_into`], `MapViewOfFile2`, which is
//! the documented inline wrapper over `MapViewOfFile3`, called here as
//! `MapViewOfFile3` with the process handle), using a handle to the renderer
//! with `PROCESS_VM_OPERATION` that the host gave it. The renderer keeps
//! Arbitrary Code Guard (`PROHIBIT_DYNAMIC_CODE`): it never maps or protects
//! executable memory, and has no writable view of this section. The renderer
//! gets the view's address over IPC and calls [`CodeRegion::adopt`], which
//! checks that the address really is a committed, mapped, read-execute view
//! that starts with the enter stub. After writing, the writer calls
//! [`RemoteView::flush`] (`FlushInstructionCache` on the renderer). An embedder
//! with no sandbox uses [`SharedCode::map_executable`] to map the view in the
//! current process.
//!
//! None of the functions are in `libc`, `windows-sys` is not a dependency, and
//! so they are declared here, as `windows.rs` does; handles are `isize`.
//! `MapViewOfFile3` and `UnmapViewOfFile2` are linked `raw-dylib` from the API
//! sets Microsoft's metadata binds them to (as `windows-sys` does, and as for
//! `VirtualAlloc2`): `api-ms-win-core-memory-l1-1-6.dll` and
//! `api-ms-win-core-memory-l1-1-5.dll`. They are not in every SDK's
//! `kernel32.lib`, and not exports of `kernel32.dll` by that name here. The
//! citations are Microsoft Learn pages, `docs <function>`.
//!
//! **This module has not been run by its author** (no Windows machine); the
//! x86-64 stub, the declarations and the tests are checked by CI only.

use std::ffi::c_void;
use std::os::windows::io::AsRawHandle;
use std::sync::{Mutex, PoisonError};

use crate::CodeError;
use crate::code::{STUB, check_size, write_range};

type Handle = isize;
type Bool = i32;
type Dword = u32;

/// `MEMORY_BASIC_INFORMATION` (memoryapi.h, 64-bit): 48 bytes.
#[repr(C)]
struct MemoryBasicInformation {
    base_address: *mut c_void,
    allocation_base: *mut c_void,
    allocation_protect: Dword,
    partition_id: u16,
    region_size: usize,
    state: Dword,
    protect: Dword,
    kind: Dword,
}

#[link(name = "kernel32")]
// SAFETY: docs CreateFileMappingW (kernel32, winbase.h: `HANDLE
// CreateFileMappingW(HANDLE hFile, LPSECURITY_ATTRIBUTES, DWORD flProtect, DWORD
// dwMaximumSizeHigh, DWORD dwMaximumSizeLow, LPCWSTR lpName)`); docs
// FlushInstructionCache (processthreadsapi.h: `BOOL FlushInstructionCache(HANDLE
// hProcess, LPCVOID lpBaseAddress, SIZE_T dwSize)`); docs VirtualQuery
// (memoryapi.h: `SIZE_T VirtualQuery(LPCVOID lpAddress, PMEMORY_BASIC_INFORMATION
// lpBuffer, SIZE_T dwLength)`); docs CloseHandle (handleapi.h: `BOOL
// CloseHandle(HANDLE)`). `HANDLE` and `SIZE_T` are pointer-sized (`isize`,
// `usize`), `DWORD` is `u32`, `BOOL` is `i32`, `LPCWSTR` is `*const u16`, and
// `system` is the calling convention. None is `pub` or `safe`, so every call
// needs its own `unsafe` block.
unsafe extern "system" {
    fn CreateFileMappingW(
        file: Handle,
        attributes: *mut c_void,
        protect: Dword,
        size_high: Dword,
        size_low: Dword,
        name: *const u16,
    ) -> Handle;
    fn FlushInstructionCache(process: Handle, base: *const c_void, size: usize) -> Bool;
    fn VirtualQuery(
        address: *const c_void,
        buffer: *mut MemoryBasicInformation,
        length: usize,
    ) -> usize;
    fn CloseHandle(handle: Handle) -> Bool;
}

// Microsoft's metadata (as carried by `windows-sys`) binds `MapViewOfFile3` to
// the API set `api-ms-win-core-memory-l1-1-6.dll`, so that is the DLL imported
// from, by name (`raw-dylib`).
#[link(name = "api-ms-win-core-memory-l1-1-6", kind = "raw-dylib")]
// SAFETY: docs MapViewOfFile3 (memoryapi.h, the function MapViewOfFile2 calls:
// `PVOID MapViewOfFile3(HANDLE FileMapping, HANDLE Process, PVOID BaseAddress,
// ULONG64 Offset, SIZE_T ViewSize, ULONG AllocationType, ULONG PageProtection,
// MEM_EXTENDED_PARAMETER *ExtendedParameters, ULONG ParameterCount)`). `HANDLE`
// and `SIZE_T` are pointer-sized (`isize`, `usize`), `ULONG` is `u32`, `ULONG64`
// is `u64`, and `system` is the calling convention. Not `pub`, not `safe`.
unsafe extern "system" {
    fn MapViewOfFile3(
        section: Handle,
        process: Handle,
        base: *mut c_void,
        offset: u64,
        size: usize,
        allocation_type: Dword,
        protect: Dword,
        parameters: *mut c_void,
        parameter_count: Dword,
    ) -> *mut c_void;
}

// `UnmapViewOfFile2` is bound to `api-ms-win-core-memory-l1-1-5.dll`.
#[link(name = "api-ms-win-core-memory-l1-1-5", kind = "raw-dylib")]
// SAFETY: docs UnmapViewOfFile2 (memoryapi.h: `BOOL UnmapViewOfFile2(HANDLE
// Process, PVOID BaseAddress, ULONG UnmapFlags)`). `HANDLE` is `isize`, `ULONG`
// is `u32`, `BOOL` is `i32`, and `system` is the calling convention. Not `pub`,
// not `safe`.
unsafe extern "system" {
    fn UnmapViewOfFile2(process: Handle, base: *mut c_void, flags: Dword) -> Bool;
}

// SAFETY: docs C runtime `memcpy` (Microsoft Learn, C runtime library
// reference, "memcpy, wmemcpy": `void *memcpy(void *dest, const void *src,
// size_t count)`), in the C runtime every Rust program on this target links.
// `size_t` is `usize`; `C` is its calling convention. Not `pub`, not `safe`.
unsafe extern "C" {
    fn memcpy(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}

/// `PAGE_READWRITE`, `PAGE_EXECUTE_READ`, `PAGE_EXECUTE_READWRITE` (winnt.h).
const PAGE_READWRITE: Dword = 0x04;
const PAGE_EXECUTE_READ: Dword = 0x20;
const PAGE_EXECUTE_READWRITE: Dword = 0x40;
/// `MEM_COMMIT` and `MEM_MAPPED` (winnt.h).
const MEM_COMMIT: Dword = 0x1000;
const MEM_MAPPED: Dword = 0x4_0000;
/// `INVALID_HANDLE_VALUE`: for `CreateFileMappingW`, a pagefile-backed section.
const INVALID_HANDLE_VALUE: Handle = -1;
/// The pseudo-handle for the current process (docs GetCurrentProcess: "a
/// pseudo handle ... the value (HANDLE)-1"), which `MapViewOfFile3` accepts.
const CURRENT_PROCESS: Handle = -1;

/// A section the code lives in. It owns its handle and closes it on drop.
#[derive(Debug)]
pub struct SharedCode {
    section: Handle,
    len: usize,
}

/// A read-write view of a [`SharedCode`] in this process, for the writer.
/// Unmapped on drop.
#[derive(Debug)]
pub struct CodeWriter {
    base: usize,
    len: usize,
}

/// A read-execute view in this process. [`crate::enter`] runs code in it.
///
/// A view made by [`SharedCode::map_executable`] is **owned**: it is unmapped on
/// drop. A view taken over with [`CodeRegion::adopt`] is **not owned** and
/// is never unmapped by this crate (it was mapped by another process, which
/// lives as long as the renderer wants it), so adopting the same view twice
/// is harmless and dropping one value cannot leave another dangling.
#[derive(Debug)]
pub struct CodeRegion {
    base: usize,
    len: usize,
    owned: bool,
}

/// The bases of the owned views that are mapped now, so that
/// [`CodeRegion::adopt`] refuses them: an adopted value never unmaps, and an
/// owned one does, so adopting an owned view could leave the adopted value
/// dangling when the owner drops.
static OWNED_VIEWS: Mutex<Vec<usize>> = Mutex::new(Vec::new());

/// Record `base` as an owned view.
fn register_owned(base: usize) {
    OWNED_VIEWS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .push(base);
}

/// Forget `base`; whether it was recorded.
fn unregister_owned(base: usize) -> bool {
    let mut views = OWNED_VIEWS.lock().unwrap_or_else(PoisonError::into_inner);
    let before = views.len();
    views.retain(|b| *b != base);
    views.len() != before
}

/// Whether `base` is an owned view mapped now.
fn is_owned(base: usize) -> bool {
    OWNED_VIEWS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .contains(&base)
}

/// A read-execute view that [`SharedCode::map_into`] made in another process:
/// its address *in that process*, to send there, and its length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RemoteView {
    /// The view's address in the other process.
    pub address: usize,
    /// Its length in bytes.
    pub len: usize,
}

impl SharedCode {
    /// A new region of `len` bytes (larger than [`crate::CODE_START`]; the OS rounds
    /// it up to whole pages), zero-filled, with the enter stub written at
    /// offset 0.
    ///
    /// # Errors
    ///
    /// [`CodeError::BadSize`], or the failing call's `GetLastError`.
    pub fn create(len: usize) -> Result<SharedCode, CodeError> {
        check_size(len)?;
        let size = u64::try_from(len).map_err(|_| CodeError::BadSize)?;
        let high = (size >> 32) as Dword;
        let low = (size & 0xffff_ffff) as Dword;
        let no_attributes: *mut c_void = std::ptr::null_mut();
        let no_name: *const u16 = std::ptr::null();
        // SAFETY: docs CreateFileMappingW: with `hFile` INVALID_HANDLE_VALUE the
        // section is backed by the pagefile and `dwMaximumSizeHigh/Low` give its
        // size, which is required then; PAGE_EXECUTE_READWRITE is the most
        // permissive page protection and a view cannot be more permissive than the
        // section, so views of any of the three kinds can be made; a null name
        // makes an unnamed section; null attributes give default security and a
        // handle that is not inheritable. It returns a handle, or NULL and
        // `GetLastError`. The declaration above matches the prototype; the null
        // pointers are valid for these parameters, and nothing is read through
        // them.
        let section = unsafe {
            CreateFileMappingW(
                INVALID_HANDLE_VALUE,
                no_attributes,
                PAGE_EXECUTE_READWRITE,
                high,
                low,
                no_name,
            )
        };
        if section == 0 {
            return Err(CodeError::os("CreateFileMappingW"));
        }
        // From here `shared` owns the handle and closes it on any early return.
        let shared = SharedCode { section, len };
        let mut writer = shared.map_writable()?;
        writer.install_stub()?;
        drop(writer);
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

    /// Map the whole section read-write in this process: the writer's view.
    ///
    /// # Errors
    ///
    /// The failing call's `GetLastError`.
    pub fn map_writable(&self) -> Result<CodeWriter, CodeError> {
        let base = self.map(CURRENT_PROCESS, PAGE_READWRITE)?;
        Ok(CodeWriter {
            base,
            len: self.len,
        })
    }

    /// Map the whole section read-execute in this process, for an embedder
    /// with no sandbox, and check that it starts with the enter stub.
    ///
    /// # Errors
    ///
    /// The failing call's `GetLastError`, or [`CodeError::NotACodeRegion`].
    pub fn map_executable(&self) -> Result<CodeRegion, CodeError> {
        let base = self.map(CURRENT_PROCESS, PAGE_EXECUTE_READ)?;
        // From here `region` owns the view and unmaps it on any early return.
        register_owned(base);
        let region = CodeRegion {
            base,
            len: self.len,
            owned: true,
        };
        region.check_stub()?;
        Ok(region)
    }

    /// Map the whole section read-execute in **another process** (`process`: a
    /// handle with `PROCESS_VM_OPERATION`), which gets no writable view. Send
    /// the result's address to that process, which passes it to
    /// [`CodeRegion::adopt`]. The view lasts until that process unmaps it.
    ///
    /// # Errors
    ///
    /// The failing call's `GetLastError`.
    pub fn map_into(&self, process: &impl AsRawHandle) -> Result<RemoteView, CodeError> {
        let handle = process.as_raw_handle() as Handle;
        let address = self.map(handle, PAGE_EXECUTE_READ)?;
        Ok(RemoteView {
            address,
            len: self.len,
        })
    }

    /// `MapViewOfFile3` the whole section into `process` with `protect`; the
    /// address (in that process).
    fn map(&self, process: Handle, protect: Dword) -> Result<usize, CodeError> {
        let any_address: *mut c_void = std::ptr::null_mut();
        let no_parameters: *mut c_void = std::ptr::null_mut();
        // SAFETY: docs MapViewOfFile3: maps a view of the section `FileMapping`
        // into `Process`, at a system-chosen address when `BaseAddress` is NULL,
        // from `Offset` 0 for `ViewSize` 0 meaning the whole section, with
        // `AllocationType` 0 and the page protection `PageProtection` (which the
        // section's must allow), and no extended parameters (NULL, 0). It returns
        // the view's address in `Process`, or NULL and `GetLastError`. The
        // declaration above matches the prototype. `section` is the handle this
        // value owns; `process` is the current-process pseudo-handle or a handle
        // the caller supplied; a view in another process touches no memory of
        // this one, and one in this process is new memory that aliases nothing.
        let p = unsafe {
            MapViewOfFile3(
                self.section,
                process,
                any_address,
                0,
                0,
                0,
                protect,
                no_parameters,
                0,
            )
        };
        if p.is_null() {
            return Err(CodeError::os("MapViewOfFile3"));
        }
        Ok(p as usize)
    }
}

impl Drop for SharedCode {
    fn drop(&mut self) {
        // SAFETY: docs CloseHandle: closes an open object handle. The declaration
        // above matches the prototype. `section` is the open handle this value
        // owns, closed once here; views already made keep the section alive. The
        // result is ignored: nothing can be done about a failed close.
        let _ = unsafe { CloseHandle(self.section) };
    }
}

impl RemoteView {
    /// `FlushInstructionCache` for the view in `process` (the handle given to
    /// [`SharedCode::map_into`]): call it after writing, so that the process
    /// executes what was written.
    ///
    /// # Errors
    ///
    /// The failing call's `GetLastError`.
    pub fn flush(&self, process: &impl AsRawHandle) -> Result<(), CodeError> {
        flush(process.as_raw_handle() as Handle, self.address, self.len)
    }
}

/// `FlushInstructionCache(process, address, len)`.
fn flush(process: Handle, address: usize, len: usize) -> Result<(), CodeError> {
    let base = address as *const c_void;
    // SAFETY: docs FlushInstructionCache: flushes the instruction cache of
    // `hProcess` for `dwSize` bytes from `lpBaseAddress`, so code just written
    // there is seen. It returns nonzero, or 0 and `GetLastError`. The declaration
    // above matches the prototype. `process` is a handle the caller supplied or
    // the current-process pseudo-handle. The address is only a number in that
    // process's address space; nothing is read or written through it here.
    let ok = unsafe { FlushInstructionCache(process, base, len) };
    if ok == 0 {
        Err(CodeError::os("FlushInstructionCache"))
    } else {
        Ok(())
    }
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
    /// end inside the region. Flush the executing process's instruction cache
    /// afterwards ([`RemoteView::flush`], [`CodeRegion::flush`]).
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
        let n = bytes.len();
        // SAFETY: docs C runtime `memcpy`: copies `count` bytes from `src` to
        // `dest`, which must not overlap. `dst` is `n` bytes inside this value's
        // read-write view (the sum of `base` and `offset` was checked against
        // `len`, and the view lasts as long as `self`); `src` is the live slice
        // `bytes`, a different allocation, and `n` is its length.
        let _ = unsafe { memcpy(dst, src, n) };
        Ok(())
    }
}

impl Drop for CodeWriter {
    fn drop(&mut self) {
        unmap(self.base);
    }
}

impl CodeRegion {
    /// Use the read-execute view at `address` in this process that
    /// [`SharedCode::map_into`] made in the writer: the renderer calls this with
    /// the address it received over IPC. Checked, with `VirtualQuery`: the
    /// address is the start of a committed, **mapped** (not private) allocation
    /// of at least `len` bytes, whose protection is exactly `PAGE_EXECUTE_READ`;
    /// it is not a view this crate owns (see [`CodeRegion`]); and its first
    /// bytes are the enter stub. The returned value does **not** own the view
    /// and never unmaps it, so the same view can be adopted more than once and
    /// no drop can leave another value dangling.
    ///
    /// What this cannot check is that the writer is the code process: the
    /// renderer must have got `address` and `len` from it (jit.md J.0(b)).
    ///
    /// # Errors
    ///
    /// [`CodeError::NotACodeRegion`], [`CodeError::BadSize`], or the failing
    /// call's `GetLastError`.
    pub fn adopt(address: usize, len: usize) -> Result<CodeRegion, CodeError> {
        check_size(len)?;
        if is_owned(address) {
            return Err(CodeError::NotACodeRegion);
        }
        let mut info = MemoryBasicInformation {
            base_address: std::ptr::null_mut(),
            allocation_base: std::ptr::null_mut(),
            allocation_protect: 0,
            partition_id: 0,
            region_size: 0,
            state: 0,
            protect: 0,
            kind: 0,
        };
        let at = address as *const c_void;
        let out: *mut MemoryBasicInformation = &mut info;
        let size = size_of::<MemoryBasicInformation>();
        // SAFETY: docs VirtualQuery: writes information about the pages starting at
        // `lpAddress` to the `dwLength` bytes at `lpBuffer`, returns the number of
        // bytes written, or 0 and `GetLastError` (for an address above the user
        // range, for example). The declaration above matches the prototype and
        // `MemoryBasicInformation` is `MEMORY_BASIC_INFORMATION`. `at` is only an
        // address looked up, never dereferenced; `out` points to the live local
        // `info`, and `size` is its size, computed.
        let written = unsafe { VirtualQuery(at, out, size) };
        if written == 0 {
            return Err(CodeError::os("VirtualQuery"));
        }
        let exact = info.base_address as usize == address
            && info.allocation_base as usize == address
            && info.state == MEM_COMMIT
            && info.kind == MEM_MAPPED
            && info.protect == PAGE_EXECUTE_READ
            && info.region_size >= len;
        if !exact {
            return Err(CodeError::NotACodeRegion);
        }
        let region = CodeRegion {
            base: address,
            len,
            owned: false,
        };
        region.check_stub()?;
        Ok(region)
    }

    /// The region's size in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Always false: a region is larger than the stub.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// `FlushInstructionCache` for this process's view: an embedder calls it
    /// after writing through [`CodeWriter`]. (The sandboxed renderer's cache is
    /// flushed by the writer with [`RemoteView::flush`].)
    ///
    /// # Errors
    ///
    /// The failing call's `GetLastError`.
    pub fn flush(&self) -> Result<(), CodeError> {
        flush(CURRENT_PROCESS, self.base, self.len)
    }

    /// The address of the region's first byte (the stub).
    pub(crate) fn base(&self) -> usize {
        self.base
    }

    /// The first bytes are the enter stub.
    fn check_stub(&self) -> Result<(), CodeError> {
        let mut head = vec![0u8; STUB.len()];
        let src = self.base as *const c_void;
        let dst: *mut c_void = head.as_mut_ptr().cast();
        let n = head.len();
        // SAFETY: docs C runtime `memcpy`: copies `count` bytes from `src` to
        // `dest`, which must not overlap. `src` is the start of this value's
        // committed read-execute view, of at least `STUB.len()` bytes (`n`;
        // `check_size` made every region larger than the stub) and readable
        // (PAGE_EXECUTE_READ includes read); `dst` is the live `Vec` `head`, a
        // different allocation, and `n` is its length.
        let _ = unsafe { memcpy(dst, src, n) };
        if head == STUB {
            Ok(())
        } else {
            Err(CodeError::NotACodeRegion)
        }
    }
}

impl Drop for CodeRegion {
    fn drop(&mut self) {
        if self.owned && unregister_owned(self.base) {
            unmap(self.base);
        }
    }
}

/// `UnmapViewOfFile2` a view in this process.
fn unmap(base: usize) {
    // SAFETY: docs UnmapViewOfFile2: unmaps the view at `BaseAddress` in
    // `Process` (the current-process pseudo-handle), with `UnmapFlags` 0, and
    // returns nonzero, or 0 and `GetLastError`. The declaration above matches
    // the prototype. `base` is the address `MapViewOfFile3` returned for a view
    // that the owner being dropped has not unmapped before, and no reference
    // into it exists. The result is ignored: nothing can be done about it.
    let _ = unsafe { UnmapViewOfFile2(CURRENT_PROCESS, base as *mut c_void, 0) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::code::{EXIT_42, exit_with};
    use crate::{CODE_START, Context, Exit, Validated, enter};

    /// A multiple of the page and allocation granularity.
    const SIZE: usize = 65_536;

    #[test]
    #[cfg_attr(
        miri,
        ignore = "foreign calls and generated code cannot run under Miri"
    )]
    fn a_blob_written_by_the_writer_runs_in_the_executable_view() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let mut writer = shared.map_writable()?;
        writer.write(CODE_START, EXIT_42)?;
        let region = shared.map_executable()?;
        region.flush()?;
        let mut ctx = Context::new();
        assert_eq!(ctx.exit_code(), 0);
        let exit = enter(&region, Validated::new(CODE_START), &mut ctx)?;
        assert_eq!(exit, Exit(42));
        assert_eq!(ctx.exit_code(), 42);
        let mut again = Context::new();
        assert_eq!(
            enter(&region, Validated::new(CODE_START), &mut again)?,
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
            region.flush()?;
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
        let region = shared.map_executable()?;
        let mut ctx = Context::new();
        for offset in [0, 1, CODE_START.saturating_sub(1), SIZE, usize::MAX] {
            assert_eq!(
                enter(&region, Validated::new(offset), &mut ctx),
                Err(CodeError::OutOfRange),
                "offset {offset}"
            );
        }
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn the_writer_cannot_reach_the_stub_or_leave_the_region() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        let mut writer = shared.map_writable()?;
        assert_eq!(writer.write(0, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(writer.write(SIZE, &[0]), Err(CodeError::OutOfRange));
        assert_eq!(writer.write(SIZE.saturating_sub(1), &[0]), Ok(()));
        assert_eq!(
            SharedCode::create(CODE_START).err(),
            Some(CodeError::BadSize)
        );
        Ok(())
    }

    /// The current process, as the pseudo-handle `MapViewOfFile3` accepts.
    struct CurrentProcess;

    impl AsRawHandle for CurrentProcess {
        fn as_raw_handle(&self) -> std::os::windows::io::RawHandle {
            CURRENT_PROCESS as std::os::windows::io::RawHandle
        }
    }

    #[test]
    #[cfg_attr(miri, ignore = "foreign calls cannot run under Miri")]
    fn adopt_accepts_only_a_read_execute_mapped_view_with_the_stub() -> Result<(), CodeError> {
        let shared = SharedCode::create(SIZE)?;
        // A writable view is mapped, committed, and not read-execute.
        let writer = shared.map_writable()?;
        assert_eq!(
            CodeRegion::adopt(writer.base, SIZE).err(),
            Some(CodeError::NotACodeRegion)
        );
        // A view this crate owns is refused: the owner would unmap it.
        let owned = shared.map_executable()?;
        assert_eq!(
            CodeRegion::adopt(owned.base(), SIZE).err(),
            Some(CodeError::NotACodeRegion)
        );
        // A view made in "another process" (here this one, by pseudo-handle) is
        // adopted, any number of times, and no drop unmaps it.
        let remote = shared.map_into(&CurrentProcess)?;
        let first = CodeRegion::adopt(remote.address, SIZE)?;
        let second = CodeRegion::adopt(remote.address, SIZE)?;
        assert_eq!(first.base(), second.base());
        drop(first);
        let mut ctx = Context::new();
        let mut w = shared.map_writable()?;
        w.write(CODE_START, EXIT_42)?;
        remote.flush(&CurrentProcess)?;
        assert_eq!(
            enter(&second, Validated::new(CODE_START), &mut ctx)?,
            Exit(42)
        );
        // Nowhere near a view.
        assert!(CodeRegion::adopt(0, SIZE).is_err());
        // A stack address is private memory.
        let local = 0u8;
        let at = std::ptr::from_ref(&local) as usize;
        assert!(CodeRegion::adopt(at, SIZE).is_err());
        Ok(())
    }
}
