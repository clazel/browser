//! The Windows AppContainer policy: a low-box token with no capabilities, a
//! Job Object that allows one process, and process mitigations.
//!
//! Unlike Seatbelt and the Linux layers, nothing here is applied by the
//! renderer to itself: Windows has no call that moves a running process into
//! an AppContainer. The *host* creates the renderer already confined
//! (`CreateProcessW` with attributes), so this policy is data for the code that
//! does that (`clazel-sys`'s `windows` module, driven from the renderer's
//! `launch` module). The renderer then only checks that it is confined.
//!
//! Modelling choices:
//! - **No capabilities.** The AppContainer SID is derived from
//!   [`CONTAINER_NAME`]. With no `internetClient` (or any other) capability
//!   the token cannot use the network, and it cannot open the user's files:
//!   the container SID is on no file's ACL except those the host grants it
//!   (the renderer binary).
//! - **A less-privileged AppContainer (LPAC).** The process opts out of the
//!   `ALL APPLICATION PACKAGES` group ([`OPT_OUT_ALL_APPLICATION_PACKAGES`]).
//!   That group is what lets an ordinary AppContainer read most of `C:Windows`
//!   and use `DeviceAfd`; the LPAC keeps only `ALL RESTRICTED APPLICATION
//!   PACKAGES`, which the core system files grant. It matters: with only
//!   "no capabilities", a plain AppContainer here could still connect to a
//!   loopback TCP port and bind a UDP socket, and an LPAC cannot even start
//!   Winsock (`tests/escape_windows.rs` found this). What the LPAC can still
//!   read of the system directories is not tested.
//! - **One process.** The job limits the active process count to 1 and
//!   `PROC_THREAD_ATTRIBUTE_CHILD_PROCESS_POLICY` forbids children: both stop
//!   `CreateProcess`, the analogue of the Linux filter's missing `clone`.
//! - **Mitigations** are the ones a Rust binary without a JIT, a GUI or
//!   fonts can run under. `EXTENSION_POINT_DISABLE` and `WIN32K` remove
//!   attack surface (legacy hooks; the whole `win32k` system call table).
//! - **The job dies with its handle** (`KILL_ON_JOB_CLOSE`), so a crashed
//!   host cannot leave a renderer behind.
//!
//! The values are from `winnt.h` and `processthreadsapi.h`
//! (`PROCESS_CREATION_MITIGATION_POLICY_*`, `JOB_OBJECT_*`); the integration
//! tests of item 8.x (a real sandboxed process trying to open files, sockets
//! and processes) are the only check that they deny what they should and
//! allow what a renderer needs.
//!
//! # The GPU process's policy (phase-5.md item 5.21a)
//!
//! Decided in the plan from a measurement on Windows (2026-11-04, one RTX 5060 Ti
//! and WARP; the table is in `docs/phases/phase-5.md`, section 5.21a), not measured
//! again here: this crate was changed on a Mac. **The renderer's whole policy (its
//! mitigations, job and no children) less `WIN32K_SYSTEM_CALL_DISABLE` and plus the
//! `registryRead` capability, under its own container name.** Direct3D needs
//! `win32k` with or without the capability, and the driver cannot read the
//! registry keys it needs without it. The cost, which the plan states: a
//! compromised GPU process can read `HKCU\Software`, `HKCU\Environment` and
//! `HKLM\SOFTWARE`, and it has the whole `win32k` system call table. The separate
//! [`GPU_CONTAINER_NAME`] keeps it from sharing the renderer's writable folder.
//!
//! Only the data is here. `clazel-renderer`'s `launch` starts the GPU process
//! with it, through `clazel_sys::windows::spawn`, which takes capabilities by
//! name (`DeriveCapabilitySidsFromName`). That code was written on a Mac and
//! compiled for Windows; **no process has been started with this policy by this
//! code** (the plan's measurement used a throwaway probe).

/// The AppContainer profile name, which the SID is derived from. Changing it
/// changes the SID, so files granted to the old one are no longer readable.
pub const CONTAINER_NAME: &str = "clazel.renderer";

/// Capabilities the token carries (SIDs). None: no network, no file pickers,
/// no devices.
pub const CAPABILITIES: &[&str] = &[];

/// One process mitigation flag of `PROC_THREAD_ATTRIBUTE_MITIGATION_POLICY`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mitigation {
    /// The `PROCESS_CREATION_MITIGATION_POLICY_*` name.
    pub name: &'static str,
    /// Its `DWORD64` mask (`ALWAYS_ON`).
    pub mask: u64,
    /// Why the renderer is run with it.
    pub reason: &'static str,
}

/// The mitigations, all `ALWAYS_ON`.
pub const MITIGATIONS: &[Mitigation] = &[
    Mitigation {
        name: "DEP_ENABLE",
        mask: 0x1,
        reason: "data pages are not executable",
    },
    Mitigation {
        name: "HEAP_TERMINATE_ALWAYS_ON",
        mask: 1 << 12,
        reason: "heap corruption ends the process instead of continuing",
    },
    Mitigation {
        name: "BOTTOM_UP_ASLR_ALWAYS_ON",
        mask: 1 << 16,
        reason: "randomise allocation bases",
    },
    Mitigation {
        name: "HIGH_ENTROPY_ASLR_ALWAYS_ON",
        mask: 1 << 20,
        reason: "64-bit address space randomisation",
    },
    Mitigation {
        name: "STRICT_HANDLE_CHECKS_ALWAYS_ON",
        mask: 1 << 24,
        reason: "an invalid handle ends the process instead of being ignored",
    },
    Mitigation {
        name: "WIN32K_SYSTEM_CALL_DISABLE_ALWAYS_ON",
        mask: 1 << 28,
        reason: "the renderer draws nothing through win32k; its system calls are attack surface",
    },
    Mitigation {
        name: "EXTENSION_POINT_DISABLE_ALWAYS_ON",
        mask: 1 << 32,
        reason: "no legacy extension points (AppInit DLLs, global hooks)",
    },
    Mitigation {
        name: "PROHIBIT_DYNAMIC_CODE_ALWAYS_ON",
        mask: 1 << 36,
        reason: "no executable memory can be created: there is no JIT",
    },
    Mitigation {
        name: "FONT_DISABLE_ALWAYS_ON",
        mask: 1 << 48,
        reason: "the renderer loads no non-system fonts",
    },
    Mitigation {
        name: "IMAGE_LOAD_NO_REMOTE_ALWAYS_ON",
        mask: 1 << 52,
        reason: "no DLL from a network share",
    },
    Mitigation {
        name: "IMAGE_LOAD_NO_LOW_LABEL_ALWAYS_ON",
        mask: 1 << 56,
        reason: "no DLL from a low-integrity location",
    },
];

/// The union of [`MITIGATIONS`].
pub fn mitigation_mask() -> u64 {
    MITIGATIONS.iter().fold(0, |mask, m| mask | m.mask)
}

/// The Job Object the renderer is created in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Job {
    /// `ActiveProcessLimit`: the renderer itself is the one process.
    pub active_process_limit: u32,
    /// `JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE`.
    pub kill_on_close: bool,
    /// `JOB_OBJECT_UILIMIT_*`: all of them (handles, clipboard, system
    /// parameters, display settings, global atoms, desktop, exit windows).
    pub ui_restrictions: u32,
    /// `ProcessMemoryLimit` in bytes; a runaway renderer is stopped here.
    pub process_memory_limit: u64,
}

/// The renderer's job.
pub const RENDERER_JOB: Job = Job {
    active_process_limit: 1,
    kill_on_close: true,
    ui_restrictions: 0xFF,
    process_memory_limit: 2 * 1024 * 1024 * 1024,
};

/// `PROCESS_CREATION_ALL_APPLICATION_PACKAGES_OPT_OUT`: make the AppContainer an
/// LPAC.
pub const OPT_OUT_ALL_APPLICATION_PACKAGES: bool = true;

/// `PROCESS_CREATION_CHILD_PROCESS_RESTRICTED`: the renderer cannot create a
/// child process at all.
pub const CHILD_PROCESS_RESTRICTED: bool = true;

/// The GPU process's AppContainer profile name (item 5.21a): its own, so that it
/// shares no writable folder with renderers.
pub const GPU_CONTAINER_NAME: &str = "clazel.gpu";

/// The GPU process's capabilities (item 5.21a): `registryRead`, without which the
/// driver cannot read `Control\Class`, `GraphicsDrivers` or `Microsoft\DirectX`
/// under `HKLM` (measured in the plan).
pub const GPU_CAPABILITIES: &[&str] = &["registryRead"];

/// The mitigation the GPU process goes without (item 5.21a): Direct3D needs
/// `win32k`.
pub const GPU_WITHOUT: &[&str] = &["WIN32K_SYSTEM_CALL_DISABLE_ALWAYS_ON"];

/// The GPU process's mitigations: [`MITIGATIONS`] less [`GPU_WITHOUT`].
pub fn gpu_mitigation_mask() -> u64 {
    MITIGATIONS
        .iter()
        .filter(|m| !GPU_WITHOUT.contains(&m.name))
        .fold(0, |mask, m| mask | m.mask)
}

/// The GPU process's job: the renderer's (one process, killed with its handle,
/// every UI limit, the same memory limit).
pub const GPU_JOB: Job = RENDERER_JOB;
