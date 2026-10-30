//! Windows: start a process inside an AppContainer and a Job Object, and the
//! two checks and one escape attempt the sandbox tests make.
//!
//! Windows cannot move a running process into an AppContainer, so unlike the
//! Linux and macOS modules this one *spawns*: the host calls [`spawn`] with a
//! [`Policy`] that safe code took from `clazel-sandbox`, and gets the confined
//! process back. Nothing here decides what the policy is.
//!
//! None of these functions are in `libc`, and `windows-sys` is not a
//! dependency (CLAUDE.md rule 1), so each is declared in the `unsafe extern`
//! block below, as `macos.rs` does. Handles are carried as `isize` (the C
//! `HANDLE`, a pointer-sized integer in the same register), so no raw pointer
//! is stored and the types are `Send` without an `unsafe impl`. Every
//! out-parameter points at a live local made before the `unsafe` block.
//!
//! The citations in `// SAFETY:` comments are the Microsoft Learn pages,
//! `https://learn.microsoft.com/windows/win32/api/<header>/nf-<header>-<function>`,
//! written `docs <function>`, since Windows has no man pages.

use std::ffi::c_void;
use std::fmt;
use std::os::windows::ffi::OsStrExt;
use std::os::windows::io::{AsRawHandle, OwnedHandle};
use std::path::Path;

use crate::Errno;

type Handle = isize;
type Bool = i32;
type Dword = u32;

#[repr(C)]
struct SecurityCapabilities {
    app_container_sid: *mut c_void,
    capabilities: *mut c_void,
    capability_count: Dword,
    reserved: Dword,
}

#[repr(C)]
struct StartupInfoW {
    cb: Dword,
    reserved: *mut u16,
    desktop: *mut u16,
    title: *mut u16,
    x: Dword,
    y: Dword,
    x_size: Dword,
    y_size: Dword,
    x_count_chars: Dword,
    y_count_chars: Dword,
    fill_attribute: Dword,
    flags: Dword,
    show_window: u16,
    cb_reserved2: u16,
    reserved2: *mut u8,
    std_input: Handle,
    std_output: Handle,
    std_error: Handle,
}

#[repr(C)]
struct StartupInfoExW {
    startup_info: StartupInfoW,
    attribute_list: *mut c_void,
}

#[repr(C)]
struct ProcessInformation {
    process: Handle,
    thread: Handle,
    process_id: Dword,
    thread_id: Dword,
}

#[repr(C)]
struct JobBasicLimit {
    per_process_user_time_limit: i64,
    per_job_user_time_limit: i64,
    limit_flags: Dword,
    minimum_working_set_size: usize,
    maximum_working_set_size: usize,
    active_process_limit: Dword,
    affinity: usize,
    priority_class: Dword,
    scheduling_class: Dword,
}

#[repr(C)]
struct JobExtendedLimit {
    basic: JobBasicLimit,
    io_info: [u64; 6],
    process_memory_limit: usize,
    job_memory_limit: usize,
    peak_process_memory_used: usize,
    peak_job_memory_used: usize,
}

#[repr(C)]
struct JobUiRestrictions {
    ui_restrictions_class: Dword,
}

#[repr(C)]
struct TokenIsAppContainer {
    value: Dword,
}

#[link(name = "kernel32")]
#[link(name = "advapi32")]
#[link(name = "userenv")]
// SAFETY: docs CreateAppContainerProfile, DeriveAppContainerSidFromAppContainerName
// (userenv.h); docs CreateProcessW, InitializeProcThreadAttributeList,
// UpdateProcThreadAttribute, DeleteProcThreadAttributeList, CloseHandle,
// CreateJobObjectW, SetInformationJobObject, SetHandleInformation,
// WaitForSingleObject, GetExitCodeProcess, TerminateProcess, OpenProcess
// (kernel32, processthreadsapi.h, jobapi2.h, handleapi.h, synchapi.h);
// docs OpenProcessToken, GetTokenInformation, GetLengthSid, CopySid, FreeSid
// (advapi32, securitybaseapi.h, processthreadsapi.h). The declarations below
// match those prototypes on 64-bit Windows: `BOOL` and `DWORD` are 32-bit,
// `HRESULT` is `i32`, `HANDLE` and `SIZE_T` are pointer-sized (`isize`,
// `usize`), `PSID` and the other pointers are `*mut c_void`, and `LPCWSTR` is
// `*const u16`. `system` is the Windows calling convention. The libraries are
// linked by the `#[link]` attributes, none is `pub` or declared `safe`, so
// every call needs its own `unsafe` block.
unsafe extern "system" {
    fn CreateAppContainerProfile(
        name: *const u16,
        display_name: *const u16,
        description: *const u16,
        capabilities: *mut c_void,
        capability_count: Dword,
        sid: *mut *mut c_void,
    ) -> i32;
    fn DeriveAppContainerSidFromAppContainerName(name: *const u16, sid: *mut *mut c_void) -> i32;
    fn GetLengthSid(sid: *mut c_void) -> Dword;
    fn CopySid(length: Dword, destination: *mut u8, source: *mut c_void) -> Bool;
    fn FreeSid(sid: *mut c_void) -> *mut c_void;
    fn InitializeProcThreadAttributeList(
        list: *mut c_void,
        attribute_count: Dword,
        flags: Dword,
        size: *mut usize,
    ) -> Bool;
    fn UpdateProcThreadAttribute(
        list: *mut c_void,
        flags: Dword,
        attribute: usize,
        value: *const c_void,
        size: usize,
        previous: *mut c_void,
        return_size: *mut usize,
    ) -> Bool;
    fn DeleteProcThreadAttributeList(list: *mut c_void);
    fn CreateProcessW(
        application: *const u16,
        command_line: *mut u16,
        process_attributes: *mut c_void,
        thread_attributes: *mut c_void,
        inherit_handles: Bool,
        flags: Dword,
        environment: *mut c_void,
        current_directory: *const u16,
        startup_info: *mut StartupInfoExW,
        process_information: *mut ProcessInformation,
    ) -> Bool;
    fn CloseHandle(handle: Handle) -> Bool;
    fn CreateJobObjectW(attributes: *mut c_void, name: *const u16) -> Handle;
    fn SetInformationJobObject(
        job: Handle,
        class: i32,
        information: *const c_void,
        length: Dword,
    ) -> Bool;
    fn SetHandleInformation(handle: Handle, mask: Dword, flags: Dword) -> Bool;
    fn WaitForSingleObject(handle: Handle, milliseconds: Dword) -> Dword;
    fn GetExitCodeProcess(process: Handle, code: *mut Dword) -> Bool;
    fn TerminateProcess(process: Handle, code: u32) -> Bool;
    fn OpenProcess(access: Dword, inherit: Bool, pid: Dword) -> Handle;
    fn OpenProcessToken(process: Handle, access: Dword, token: *mut Handle) -> Bool;
    fn GetTokenInformation(
        token: Handle,
        class: i32,
        information: *mut c_void,
        length: Dword,
        return_length: *mut Dword,
    ) -> Bool;
}

// Constants from `winnt.h`, `winbase.h`, `processthreadsapi.h`, `jobapi2.h`.
const PROC_THREAD_ATTRIBUTE_HANDLE_LIST: usize = 0x0002_0002;
const PROC_THREAD_ATTRIBUTE_MITIGATION_POLICY: usize = 0x0002_0007;
const PROC_THREAD_ATTRIBUTE_SECURITY_CAPABILITIES: usize = 0x0002_0009;
const PROC_THREAD_ATTRIBUTE_CHILD_PROCESS_POLICY: usize = 0x0002_000E;
const PROC_THREAD_ATTRIBUTE_JOB_LIST: usize = 0x0002_000D;
const PROC_THREAD_ATTRIBUTE_ALL_APPLICATION_PACKAGES_POLICY: usize = 0x0002_000F;
const PROCESS_CREATION_ALL_APPLICATION_PACKAGES_OPT_OUT: Dword = 1;
const PROCESS_CREATION_CHILD_PROCESS_RESTRICTED: Dword = 1;
const EXTENDED_STARTUPINFO_PRESENT: Dword = 0x0008_0000;
const DETACHED_PROCESS: Dword = 0x0000_0008;
const CREATE_UNICODE_ENVIRONMENT: Dword = 0x0000_0400;
const STARTF_USESTDHANDLES: Dword = 0x0000_0100;
const HANDLE_FLAG_INHERIT: Dword = 1;
const JOB_OBJECT_LIMIT_ACTIVE_PROCESS: Dword = 0x0000_0008;
const JOB_OBJECT_LIMIT_PROCESS_MEMORY: Dword = 0x0000_0100;
const JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE: Dword = 0x0000_2000;
const JOB_OBJECT_BASIC_UI_RESTRICTIONS: i32 = 4;
const JOB_OBJECT_EXTENDED_LIMIT_INFORMATION: i32 = 9;
const TOKEN_QUERY: Dword = 0x0008;
const TOKEN_IS_APP_CONTAINER: i32 = 29;
const PROCESS_VM_READ: Dword = 0x0010;
const PROCESS_VM_WRITE: Dword = 0x0020;
const PROCESS_VM_OPERATION: Dword = 0x0008;
const WAIT_OBJECT_0: Dword = 0;
/// `GetCurrentProcess()` is this constant, by definition in `processthreadsapi.h`.
const CURRENT_PROCESS: Handle = -1;
/// The exit code `TerminateProcess` gives a killed renderer.
const KILLED: u32 = 1;
/// `STILL_ACTIVE` from `GetExitCodeProcess`.
const STILL_ACTIVE: Dword = 259;

/// Why a process could not be started or a check made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpawnError {
    /// An argument contains a NUL, so it cannot be a Windows string.
    InteriorNul,
    /// A Win32 call failed: its name and the error it left.
    Call(&'static str, Errno),
    /// A COM-style call failed: its name and the `HRESULT`.
    Hresult(&'static str, i32),
}

impl fmt::Display for SpawnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpawnError::InteriorNul => f.write_str("a string contains a NUL"),
            SpawnError::Call(name, e) => write!(f, "{name} failed: {e}"),
            SpawnError::Hresult(name, h) => write!(f, "{name} failed: HRESULT {h:#010x}"),
        }
    }
}

impl std::error::Error for SpawnError {}

/// What to confine a process with. Data from `clazel-sandbox`'s
/// `appcontainer` module, mapped field by field by safe code.
#[derive(Debug, Clone, Copy)]
pub struct Policy<'a> {
    /// The AppContainer profile name; the SID is derived from it.
    pub container_name: &'a str,
    /// The `PROCESS_CREATION_MITIGATION_POLICY_*` mask.
    pub mitigations: u64,
    /// Forbid creating child processes.
    pub child_process_restricted: bool,
    /// Opt out of the `ALL APPLICATION PACKAGES` group (a less-privileged
    /// AppContainer, LPAC).
    pub opt_out_all_application_packages: bool,
    /// The job's `ActiveProcessLimit`.
    pub active_process_limit: u32,
    /// Kill the process when the job handle closes.
    pub kill_on_close: bool,
    /// `JOB_OBJECT_UILIMIT_*`.
    pub ui_restrictions: u32,
    /// The job's per-process memory limit, in bytes.
    pub process_memory_limit: u64,
}

/// An AppContainer SID as its bytes and its `S-1-15-2-...` text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContainerSid {
    bytes: Vec<u8>,
    text: String,
}

impl ContainerSid {
    /// The `S-1-15-2-...` form, which `icacls` accepts as `*S-1-15-2-...`.
    pub fn text(&self) -> &str {
        &self.text
    }
}

fn wide(s: &str) -> Result<Vec<u16>, SpawnError> {
    if s.contains('\0') {
        return Err(SpawnError::InteriorNul);
    }
    Ok(std::ffi::OsStr::new(s)
        .encode_wide()
        .chain(std::iter::once(0))
        .collect())
}

fn wide_path(p: &Path) -> Result<Vec<u16>, SpawnError> {
    let mut v: Vec<u16> = p.as_os_str().encode_wide().collect();
    if v.contains(&0) {
        return Err(SpawnError::InteriorNul);
    }
    v.push(0);
    Ok(v)
}

fn last(name: &'static str) -> SpawnError {
    SpawnError::Call(name, Errno::last())
}

/// The SID of the AppContainer called `name`, creating the profile if there
/// is none yet (the profile is per user and stays registered). The SID is a
/// function of the name alone, so if the profile cannot be created (it exists,
/// or another thread is creating it) the SID is derived instead; a process
/// can be confined under a SID with no registered profile.
pub fn container_sid(name: &str) -> Result<ContainerSid, SpawnError> {
    let name_w = wide(name)?;
    let mut sid: *mut c_void = std::ptr::null_mut();
    let slot: *mut *mut c_void = &raw mut sid;
    let name_ptr: *const u16 = name_w.as_ptr();
    let none: *mut c_void = std::ptr::null_mut();
    // SAFETY: docs CreateAppContainerProfile: `name`, `display name` and
    // `description` are NUL-terminated wide strings (here three views of the
    // live `name_w`), `capabilities` may be NULL with a count of 0, and `sid`
    // receives a SID that the caller frees with FreeSid. `slot` points to
    // the live local `sid`.
    let hr = unsafe { CreateAppContainerProfile(name_ptr, name_ptr, name_ptr, none, 0, slot) };
    if hr != 0 {
        // Already registered (`ERROR_ALREADY_EXISTS`), or another thread or
        // process is registering it right now (`E_UNEXPECTED`): the SID is a
        // function of the name, so derive it.
        // SAFETY: docs DeriveAppContainerSidFromAppContainerName: the first
        // argument is a NUL-terminated wide string (`name_w`, live) and the
        // second receives a SID freed with FreeSid; `slot` points to the
        // live local `sid`.
        let hr = unsafe { DeriveAppContainerSidFromAppContainerName(name_ptr, slot) };
        if hr != 0 {
            return Err(SpawnError::Hresult(
                "DeriveAppContainerSidFromAppContainerName",
                hr,
            ));
        }
    }
    let copied = copy_sid(sid);
    // SAFETY: docs FreeSid: frees a SID allocated by AllocateAndInitializeSid,
    // which is what CreateAppContainerProfile and
    // DeriveAppContainerSidFromAppContainerName return; `sid` was set by one
    // of them, is freed once, and `copied` no longer refers to it.
    unsafe { FreeSid(sid) };
    copied
}

fn copy_sid(sid: *mut c_void) -> Result<ContainerSid, SpawnError> {
    // SAFETY: docs GetLengthSid: takes a valid SID and returns its length in
    // bytes; `sid` was returned by the OS and has not been freed.
    let len = unsafe { GetLengthSid(sid) };
    if len == 0 {
        return Err(last("GetLengthSid"));
    }
    let mut bytes = vec![0u8; len as usize];
    let dest: *mut u8 = bytes.as_mut_ptr();
    // SAFETY: docs CopySid: copies a SID of `length` bytes from `source` to
    // `destination`, which must hold at least that many; `dest` points to the
    // `len` bytes of `bytes`, and `len` is what GetLengthSid returned for
    // `sid`.
    let ok = unsafe { CopySid(len, dest, sid) };
    if ok == 0 {
        return Err(last("CopySid"));
    }
    let text = sid_text(&bytes).ok_or(SpawnError::Call("CopySid", Errno::UNKNOWN))?;
    Ok(ContainerSid { bytes, text })
}

/// `S-1-<authority>-<subauthority>...` from a SID's bytes: revision (1),
/// sub-authority count (1), 48-bit big-endian authority (6), then the
/// sub-authorities, little-endian `u32`s.
fn sid_text(b: &[u8]) -> Option<String> {
    let (&revision, rest) = b.split_first()?;
    let (&count, rest) = rest.split_first()?;
    let (authority, subs) = rest.split_at_checked(6)?;
    let authority = authority.iter().fold(0u64, |n, byte| {
        n.saturating_mul(256).saturating_add(u64::from(*byte))
    });
    let mut text = format!("S-{revision}-{authority}");
    for chunk in subs.as_chunks::<4>().0.iter().take(usize::from(count)) {
        let n = u32::from_le_bytes(*chunk);
        text.push_str(&format!("-{n}"));
    }
    Some(text)
}

/// A confined process and the job it is in. Dropping it closes both handles,
/// which kills the process when the policy said `kill_on_close`.
#[derive(Debug)]
pub struct Process {
    process: Handle,
    job: Handle,
    pid: u32,
}

impl Process {
    /// The process id.
    pub fn id(&self) -> u32 {
        self.pid
    }

    /// The exit code, if the process has ended.
    pub fn try_wait(&self) -> Result<Option<u32>, SpawnError> {
        let mut code: Dword = 0;
        let slot: *mut Dword = &raw mut code;
        // SAFETY: docs GetExitCodeProcess: `process` is a handle with
        // PROCESS_QUERY_LIMITED_INFORMATION (CreateProcessW's handle has full
        // access) and `code` receives the exit code or STILL_ACTIVE; `slot`
        // points to the live local `code`.
        let ok = unsafe { GetExitCodeProcess(self.process, slot) };
        if ok == 0 {
            return Err(last("GetExitCodeProcess"));
        }
        Ok((code != STILL_ACTIVE).then_some(code))
    }

    /// Wait up to `milliseconds` for the process to end; whether it has.
    pub fn wait_timeout(&self, milliseconds: u32) -> bool {
        // SAFETY: docs WaitForSingleObject: waits until the object is
        // signalled or the timeout passes; a process handle is signalled when
        // the process ends. `process` is open until `drop`.
        let r = unsafe { WaitForSingleObject(self.process, milliseconds) };
        r == WAIT_OBJECT_0
    }

    /// End the process now (`TerminateProcess`); `Ok` if it had already ended.
    pub fn kill(&self) -> Result<(), SpawnError> {
        // SAFETY: docs TerminateProcess: ends the process behind `process`
        // (opened by CreateProcessW with PROCESS_TERMINATE) with an exit
        // code; it takes only the handle and the code.
        let ok = unsafe { TerminateProcess(self.process, KILLED) };
        if ok == 0 && self.try_wait()?.is_none() {
            return Err(last("TerminateProcess"));
        }
        Ok(())
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        // SAFETY: docs CloseHandle: closes a handle opened by CreateProcessW,
        // once. `process` is not used after this.
        unsafe { CloseHandle(self.process) };
        // SAFETY: docs CloseHandle: closes the job handle opened by
        // CreateJobObjectW, once (with KILL_ON_JOB_CLOSE this ends any process
        // left in the job). `job` is not used after this.
        unsafe { CloseHandle(self.job) };
    }
}

/// An open handle that is closed at the end of its scope.
struct Owned(Handle);

impl Drop for Owned {
    fn drop(&mut self) {
        // SAFETY: docs CloseHandle: closes a handle this value owns, once.
        unsafe { CloseHandle(self.0) };
    }
}

/// The attribute list of a `CreateProcessW` call, freed when dropped.
struct AttributeList {
    /// `u64`s so the buffer is 8-byte aligned, as the OS requires.
    buffer: Vec<u64>,
}

impl AttributeList {
    fn new(count: u32) -> Result<AttributeList, SpawnError> {
        let mut size: usize = 0;
        let size_slot: *mut usize = &raw mut size;
        let no_list: *mut c_void = std::ptr::null_mut();
        // SAFETY: docs InitializeProcThreadAttributeList: with a NULL list it
        // reports the required size in `size` and fails with
        // ERROR_INSUFFICIENT_BUFFER, by design; `size_slot` points to the
        // live local `size`.
        unsafe { InitializeProcThreadAttributeList(no_list, count, 0, size_slot) };
        if size == 0 {
            return Err(last("InitializeProcThreadAttributeList"));
        }
        let words = size.div_ceil(8);
        let mut buffer = vec![0u64; words];
        let list: *mut c_void = buffer.as_mut_ptr().cast();
        // SAFETY: docs InitializeProcThreadAttributeList: `list` must point to
        // `size` writable bytes, the size the first call reported; `buffer`
        // holds `words * 8 >= size` bytes, 8-aligned, and lives as long as the
        // returned value. `size_slot` points to the live local `size`.
        let ok = unsafe { InitializeProcThreadAttributeList(list, count, 0, size_slot) };
        if ok == 0 {
            return Err(last("InitializeProcThreadAttributeList"));
        }
        Ok(AttributeList { buffer })
    }

    fn ptr(&mut self) -> *mut c_void {
        self.buffer.as_mut_ptr().cast()
    }

    /// Set attribute `which` to the `size` bytes at `value`, which the caller
    /// keeps alive and unmoved until `CreateProcessW` returns.
    fn set(&mut self, which: usize, value: *const c_void, size: usize) -> Result<(), SpawnError> {
        let list = self.ptr();
        let none: *mut c_void = std::ptr::null_mut();
        let none_len: *mut usize = std::ptr::null_mut();
        // SAFETY: docs UpdateProcThreadAttribute: `list` was initialised by
        // InitializeProcThreadAttributeList for at least this many
        // attributes; `attribute` is one of the PROC_THREAD_ATTRIBUTE_*
        // constants above; `value` points to `size` bytes of the type that
        // attribute takes, which the callers below keep alive and unmoved
        // until CreateProcessW; `previous` and `return_size` are optional and
        // NULL.
        let ok = unsafe { UpdateProcThreadAttribute(list, 0, which, value, size, none, none_len) };
        if ok == 0 {
            return Err(last("UpdateProcThreadAttribute"));
        }
        Ok(())
    }
}

impl Drop for AttributeList {
    fn drop(&mut self) {
        let list = self.ptr();
        // SAFETY: docs DeleteProcThreadAttributeList: releases a list
        // initialised by InitializeProcThreadAttributeList, once; `list` is
        // that list and is not used after this.
        unsafe { DeleteProcThreadAttributeList(list) };
    }
}

fn job(policy: &Policy<'_>) -> Result<Owned, SpawnError> {
    let no_attributes: *mut c_void = std::ptr::null_mut();
    let no_name: *const u16 = std::ptr::null();
    // SAFETY: docs CreateJobObjectW: both arguments may be NULL (default
    // security, unnamed); it returns a new job handle or NULL.
    let handle = unsafe { CreateJobObjectW(no_attributes, no_name) };
    if handle == 0 {
        return Err(last("CreateJobObjectW"));
    }
    let job = Owned(handle);
    let mut flags = JOB_OBJECT_LIMIT_ACTIVE_PROCESS | JOB_OBJECT_LIMIT_PROCESS_MEMORY;
    if policy.kill_on_close {
        flags |= JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    }
    let limit = JobExtendedLimit {
        basic: JobBasicLimit {
            per_process_user_time_limit: 0,
            per_job_user_time_limit: 0,
            limit_flags: flags,
            minimum_working_set_size: 0,
            maximum_working_set_size: 0,
            active_process_limit: policy.active_process_limit,
            affinity: 0,
            priority_class: 0,
            scheduling_class: 0,
        },
        io_info: [0; 6],
        process_memory_limit: usize::try_from(policy.process_memory_limit).unwrap_or(usize::MAX),
        job_memory_limit: 0,
        peak_process_memory_used: 0,
        peak_job_memory_used: 0,
    };
    let limit_ptr: *const JobExtendedLimit = &raw const limit;
    let limit_len = size_of::<JobExtendedLimit>() as Dword;
    let limit_info: *const c_void = limit_ptr.cast();
    // SAFETY: docs SetInformationJobObject: `class` 9
    // (JobObjectExtendedLimitInformation) takes a
    // JOBOBJECT_EXTENDED_LIMIT_INFORMATION of `length` bytes. `JobExtendedLimit`
    // is that struct (`repr(C)`, 144 bytes on 64-bit Windows) and `limit_ptr`
    // points to the live local `limit`.
    let ok = unsafe {
        SetInformationJobObject(
            job.0,
            JOB_OBJECT_EXTENDED_LIMIT_INFORMATION,
            limit_info,
            limit_len,
        )
    };
    if ok == 0 {
        return Err(last("SetInformationJobObject"));
    }
    let ui = JobUiRestrictions {
        ui_restrictions_class: policy.ui_restrictions,
    };
    let ui_ptr: *const JobUiRestrictions = &raw const ui;
    let ui_len = size_of::<JobUiRestrictions>() as Dword;
    let ui_info: *const c_void = ui_ptr.cast();
    // SAFETY: docs SetInformationJobObject: `class` 4
    // (JobObjectBasicUIRestrictions) takes a JOBOBJECT_BASIC_UI_RESTRICTIONS,
    // one DWORD; `JobUiRestrictions` is that struct and `ui_ptr` points to the
    // live local `ui`.
    let ok = unsafe {
        SetInformationJobObject(job.0, JOB_OBJECT_BASIC_UI_RESTRICTIONS, ui_info, ui_len)
    };
    if ok == 0 {
        return Err(last("SetInformationJobObject"));
    }
    Ok(job)
}

/// Make a handle inheritable (or not) by the next `CreateProcessW`.
fn set_inherit(handle: &OwnedHandle, on: bool) -> Result<(), SpawnError> {
    let raw = handle.as_raw_handle() as isize;
    let flags = u32::from(on);
    // SAFETY: docs SetHandleInformation: changes the flags in `mask` of an
    // open handle; `raw` is borrowed from a live `OwnedHandle`, `mask` is
    // HANDLE_FLAG_INHERIT and `flags` is it or 0.
    let ok = unsafe { SetHandleInformation(raw, HANDLE_FLAG_INHERIT, flags) };
    if ok == 0 {
        return Err(last("SetHandleInformation"));
    }
    Ok(())
}

/// Start `program` with `command_line` (the whole line, program name first;
/// see [`quote_arg`]) inside the AppContainer and job of `policy`, with the
/// three handles as its standard input, output and error and nothing else
/// inherited. The environment is exactly `environment`. The process runs from the start under
/// its token: there is no moment when it is unconfined.
pub fn spawn(
    program: &Path,
    command_line: &str,
    policy: &Policy<'_>,
    environment: &[(&str, &str)],
    stdin: &OwnedHandle,
    stdout: &OwnedHandle,
    stderr: &OwnedHandle,
) -> Result<Process, SpawnError> {
    let sid = container_sid(policy.container_name)?;
    let mut sid_bytes = sid.bytes.clone();
    let caps = SecurityCapabilities {
        app_container_sid: sid_bytes.as_mut_ptr().cast(),
        capabilities: std::ptr::null_mut(),
        capability_count: 0,
        reserved: 0,
    };
    let mut mitigations: u64 = policy.mitigations;
    let mut child_policy: Dword = PROCESS_CREATION_CHILD_PROCESS_RESTRICTED;
    let mut lpac: Dword = PROCESS_CREATION_ALL_APPLICATION_PACKAGES_OPT_OUT;
    let job = job(policy)?;
    let mut job_handle: Handle = job.0;
    let mut inherited: [Handle; 3] = [
        stdin.as_raw_handle() as isize,
        stdout.as_raw_handle() as isize,
        stderr.as_raw_handle() as isize,
    ];
    let count = 4u32
        .saturating_add(u32::from(policy.child_process_restricted))
        .saturating_add(u32::from(policy.opt_out_all_application_packages));
    let mut list = AttributeList::new(count)?;
    list.set(
        PROC_THREAD_ATTRIBUTE_SECURITY_CAPABILITIES,
        (&raw const caps).cast(),
        size_of::<SecurityCapabilities>(),
    )?;
    list.set(
        PROC_THREAD_ATTRIBUTE_MITIGATION_POLICY,
        (&raw mut mitigations).cast(),
        size_of::<u64>(),
    )?;
    list.set(
        PROC_THREAD_ATTRIBUTE_JOB_LIST,
        (&raw mut job_handle).cast(),
        size_of::<Handle>(),
    )?;
    list.set(
        PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
        inherited.as_mut_ptr().cast(),
        size_of::<[Handle; 3]>(),
    )?;
    if policy.opt_out_all_application_packages {
        list.set(
            PROC_THREAD_ATTRIBUTE_ALL_APPLICATION_PACKAGES_POLICY,
            (&raw mut lpac).cast(),
            size_of::<Dword>(),
        )?;
    }
    if policy.child_process_restricted {
        list.set(
            PROC_THREAD_ATTRIBUTE_CHILD_PROCESS_POLICY,
            (&raw mut child_policy).cast(),
            size_of::<Dword>(),
        )?;
    }

    let program_w = wide_path(program)?;
    let mut line_w = wide(command_line)?;
    let mut environment = environment_block(environment)?;
    let mut startup = StartupInfoExW {
        startup_info: StartupInfoW {
            cb: size_of::<StartupInfoExW>() as Dword,
            reserved: std::ptr::null_mut(),
            desktop: std::ptr::null_mut(),
            title: std::ptr::null_mut(),
            x: 0,
            y: 0,
            x_size: 0,
            y_size: 0,
            x_count_chars: 0,
            y_count_chars: 0,
            fill_attribute: 0,
            flags: STARTF_USESTDHANDLES,
            show_window: 0,
            cb_reserved2: 0,
            reserved2: std::ptr::null_mut(),
            std_input: inherited[0],
            std_output: inherited[1],
            std_error: inherited[2],
        },
        attribute_list: list.ptr(),
    };
    let mut info = ProcessInformation {
        process: 0,
        thread: 0,
        process_id: 0,
        thread_id: 0,
    };

    let inheritable = set_inherit(stdin, true)
        .and_then(|()| set_inherit(stdout, true))
        .and_then(|()| set_inherit(stderr, true));
    if let Err(e) = inheritable {
        // Put back whatever was already switched on.
        let _ = set_inherit(stdin, false);
        let _ = set_inherit(stdout, false);
        let _ = set_inherit(stderr, false);
        return Err(e);
    }
    let startup_ptr: *mut StartupInfoExW = &raw mut startup;
    let info_ptr: *mut ProcessInformation = &raw mut info;
    let env_ptr: *mut c_void = environment.as_mut_ptr().cast();
    let program_ptr: *const u16 = program_w.as_ptr();
    let line_ptr: *mut u16 = line_w.as_mut_ptr();
    let no_attributes: *mut c_void = std::ptr::null_mut();
    let no_directory: *const u16 = std::ptr::null();
    let flags = EXTENDED_STARTUPINFO_PRESENT | DETACHED_PROCESS | CREATE_UNICODE_ENVIRONMENT;
    // SAFETY: docs CreateProcessW: `application` is a NUL-terminated wide path
    // (`program_w`) and `command_line` a writable NUL-terminated wide buffer
    // (`line_w`); both live to the end of the call. Process and thread
    // attributes are NULL. `inherit_handles` is TRUE, limited by the handle
    // list attribute to the three handles. `flags` has
    // EXTENDED_STARTUPINFO_PRESENT, so `startup_info` is a STARTUPINFOEXW
    // (`StartupInfoExW`, `cb` set to its size) whose `attribute_list` is the
    // initialised list, with every value it refers to still alive. With
    // CREATE_UNICODE_ENVIRONMENT the environment is a block of wide `name=value`
    // strings ending in two NULs (`environment_block`). The directory is NULL.
    // `startup_ptr` and `info_ptr` point to live locals.
    let ok = unsafe {
        CreateProcessW(
            program_ptr,
            line_ptr,
            no_attributes,
            no_attributes,
            1,
            flags,
            env_ptr,
            no_directory,
            startup_ptr,
            info_ptr,
        )
    };
    let failure = if ok == 0 {
        Some(last("CreateProcessW"))
    } else {
        None
    };
    // The handles go back to non-inheritable whether or not the spawn worked,
    // so a later spawn of another renderer cannot inherit this one's pipes.
    let _ = set_inherit(stdin, false);
    let _ = set_inherit(stdout, false);
    let _ = set_inherit(stderr, false);
    if let Some(e) = failure {
        return Err(e);
    }
    drop(Owned(info.thread));
    // The job handle moves into the `Process`; `job` no longer closes it.
    let job_raw = job.0;
    std::mem::forget(job);
    drop(list);
    Ok(Process {
        process: info.process,
        job: job_raw,
        pid: info.process_id,
    })
}

/// A `CreateProcessW` environment block: each `name=value` then a NUL, and a
/// final NUL (two NULs for an empty one).
fn environment_block(pairs: &[(&str, &str)]) -> Result<Vec<u16>, SpawnError> {
    let mut block = Vec::new();
    for (name, value) in pairs {
        block.extend(wide(&format!("{name}={value}"))?);
    }
    block.push(0);
    if pairs.is_empty() {
        block.push(0);
    }
    Ok(block)
}

/// Quote one argument for a Windows command line, the way `CommandLineToArgvW`
/// and the C runtime read it back.
pub fn quote_arg(arg: &str) -> String {
    if !arg.is_empty() && !arg.contains([' ', '\t', '\n', '\x0b', '"']) {
        return arg.to_owned();
    }
    let mut out = String::from("\"");
    let mut backslashes = 0usize;
    for c in arg.chars() {
        match c {
            '\\' => backslashes = backslashes.saturating_add(1),
            '"' => {
                out.push_str(&"\\".repeat(backslashes.saturating_mul(2).saturating_add(1)));
                out.push('"');
                backslashes = 0;
            }
            _ => {
                out.push_str(&"\\".repeat(backslashes));
                out.push(c);
                backslashes = 0;
            }
        }
    }
    out.push_str(&"\\".repeat(backslashes.saturating_mul(2)));
    out.push('"');
    out
}

/// Whether this process's token is an AppContainer token.
pub fn is_appcontainer() -> Result<bool, SpawnError> {
    let mut token: Handle = 0;
    let token_slot: *mut Handle = &raw mut token;
    // SAFETY: docs OpenProcessToken: `process` is the current-process
    // pseudo-handle (-1), `access` TOKEN_QUERY, and `token` receives a handle
    // that is closed below; `token_slot` points to the live local `token`.
    let ok = unsafe { OpenProcessToken(CURRENT_PROCESS, TOKEN_QUERY, token_slot) };
    if ok == 0 {
        return Err(last("OpenProcessToken"));
    }
    let token = Owned(token);
    let mut value = TokenIsAppContainer { value: 0 };
    let mut returned: Dword = 0;
    let value_ptr: *mut TokenIsAppContainer = &raw mut value;
    let returned_slot: *mut Dword = &raw mut returned;
    let value_len = size_of::<TokenIsAppContainer>() as Dword;
    let information: *mut c_void = value_ptr.cast();
    // SAFETY: docs GetTokenInformation: class 29 (TokenIsAppContainer) writes
    // a DWORD (`TokenIsAppContainer`, one `u32`) to `information`, whose
    // `length` is 4 bytes; `value_ptr` and `returned_slot` point to live
    // locals.
    let ok = unsafe {
        GetTokenInformation(
            token.0,
            TOKEN_IS_APP_CONTAINER,
            information,
            value_len,
            returned_slot,
        )
    };
    if ok == 0 {
        return Err(last("GetTokenInformation"));
    }
    Ok(value.value != 0)
}

/// `OpenProcess` with read, write and operation access to `pid`, as an
/// *attempt* for the sandbox tests: `Ok` means the OS gave this process the
/// handle, which is an escape (the analogue of `ptrace` attach). The handle
/// is closed at once. A `pid` of 0 is refused here before the OS is asked.
pub fn attempt_open_process(pid: u32) -> Result<(), Errno> {
    if pid == 0 {
        return Err(Errno(87)); // ERROR_INVALID_PARAMETER
    }
    let access = PROCESS_VM_READ | PROCESS_VM_WRITE | PROCESS_VM_OPERATION;
    // SAFETY: docs OpenProcess: takes an access mask, an inherit flag and a
    // process id, and returns a handle or NULL with the error set; no pointer
    // is passed.
    let handle = unsafe { OpenProcess(access, 0, pid) };
    if handle == 0 {
        return Err(Errno::last());
    }
    drop(Owned(handle));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arguments_are_quoted_for_the_command_line() {
        assert_eq!(quote_arg("plain"), "plain");
        assert_eq!(quote_arg(""), "\"\"");
        assert_eq!(quote_arg("a b"), "\"a b\"");
        assert_eq!(quote_arg("say \"hi\""), "\"say \\\"hi\\\"\"");
        assert_eq!(quote_arg("dir\\ name\\"), "\"dir\\ name\\\\\"");
    }

    #[test]
    fn a_sid_is_written_in_its_text_form() {
        // S-1-15-2-1-2: revision 1, 3 sub-authorities (15 is the authority).
        let bytes = [1, 3, 0, 0, 0, 0, 0, 15, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0];
        assert_eq!(sid_text(&bytes).as_deref(), Some("S-1-15-2-1-2"));
        assert_eq!(sid_text(&[1]), None);
    }

    #[test]
    fn a_string_with_a_nul_never_reaches_the_os() {
        assert_eq!(container_sid("a\0b"), Err(SpawnError::InteriorNul));
        assert_eq!(attempt_open_process(0), Err(Errno(87)));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn this_test_process_is_not_in_an_appcontainer() {
        assert_eq!(is_appcontainer(), Ok(false));
    }
}
