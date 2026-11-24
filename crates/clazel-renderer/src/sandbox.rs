//! Entering the OS sandbox: the renderer's first act, before it reads a byte.
//!
//! The policies are data from `clazel-sandbox`; the only code that hands
//! them to the OS is `clazel-sys`, whose functions are safe. Fail closed:
//! the first layer that returns an error stops the renderer, and the error
//! names the layer. The allowlist has no `clone`, so no thread can be made
//! once the filter is on; and `unshare(USER)` fails in a multithreaded
//! process. [`enter`] is for a process that stays single-threaded. A process
//! that wants one big-stack thread (the page's engine parses and compiles on
//! its caller's stack, `clazel_js::set_inline_parsing`) makes it in between:
//! [`enter_process`] on the only thread, then the thread is spawned, then
//! [`enter_thread`] in it, which filters every thread of the process
//! (`SECCOMP_FILTER_FLAG_TSYNC`, `clazel_sys::linux::
//! seccomp_set_mode_filter_all_threads`), the waiting one included.

use std::fmt;

/// A sandbox layer that could not be applied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    /// The layer: `no_new_privs`, `namespaces`, `landlock`, `seccomp`,
    /// `seatbelt`, `appcontainer` or `platform`.
    pub layer: &'static str,
    /// What the OS or `clazel-sys` reported.
    pub detail: String,
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "sandbox layer `{}` failed: {}", self.layer, self.detail)
    }
}

fn layer<T, E: fmt::Display>(layer: &'static str, r: Result<T, E>) -> Result<T, Failure> {
    r.map_err(|e| Failure {
        layer,
        detail: e.to_string(),
    })
}

/// The whole sandbox, for a process that is single-threaded: [`enter_process`]
/// then [`enter_thread`].
///
/// # Errors
/// The first layer that fails.
pub fn enter() -> Result<(), Failure> {
    enter_process()?;
    enter_thread()
}

/// What is process-wide and must be done while the process has one thread:
/// on Linux `no_new_privs` and the namespaces (`unshare(USER)` is an error
/// once there is a second thread); on macOS Seatbelt, which confines the whole
/// process, every thread (`sandbox_init`); on Windows the check that the host
/// started the renderer in its AppContainer and job, which are the process's.
///
/// # Errors
/// The first layer that fails.
#[cfg(target_os = "macos")]
pub fn enter_process() -> Result<(), Failure> {
    let profile = clazel_sandbox::seatbelt::renderer_profile();
    layer(
        "seatbelt",
        clazel_sys::macos::sandbox_init_profile(&profile),
    )
}

/// Linux: `no_new_privs`, namespaces, Landlock, then seccomp last, since its
/// allowlist forbids the calls before it.
/// What the calling thread adds to [`enter_process`]'s: nothing on macOS and
/// Windows, whose confinement is the process's.
///
/// # Errors
/// Never.
#[cfg(any(target_os = "macos", windows))]
pub fn enter_thread() -> Result<(), Failure> {
    Ok(())
}

/// Linux: `no_new_privs` and the namespaces; see the module's header.
///
/// # Errors
/// The first layer that fails.
#[cfg(target_os = "linux")]
pub fn enter_process() -> Result<(), Failure> {
    use clazel_sandbox::namespaces::Namespace;
    use clazel_sys::linux::{self, Namespaces};

    layer("no_new_privs", linux::set_no_new_privs())?;
    let namespaces =
        clazel_sandbox::namespaces::RENDERER
            .iter()
            .fold(Namespaces::NONE, |acc, n| {
                acc.union(match n {
                    Namespace::User => Namespaces::USER,
                    Namespace::Mount => Namespaces::MOUNT,
                    Namespace::Pid => Namespaces::PID,
                    Namespace::Net => Namespaces::NETWORK,
                    Namespace::Ipc => Namespaces::IPC,
                })
            });
    layer("namespaces", linux::unshare(namespaces))
}

/// Linux: Landlock for the calling thread, then the seccomp filter on every
/// thread of the process at once. The other threads need no Landlock domain
/// of their own: the filter has no `open`, `openat`, `socket` or `connect`, so
/// the only thread that can still make an access is this one.
///
/// # Errors
/// The first layer that fails.
#[cfg(target_os = "linux")]
pub fn enter_thread() -> Result<(), Failure> {
    layer("landlock", landlock())?;
    layer("seccomp", seccomp())
}

/// `clazel-sys` passes the ABI 1 ruleset attributes and cannot ask the kernel
/// its Landlock ABI, so try the newest filesystem rights first and fall back
/// to older ones when the kernel refuses them with `EINVAL`. Any other error
/// (Landlock disabled, `ENOSYS`, `EOPNOTSUPP`) is a failure, never a skip.
/// Network rights and scopes cannot be applied through `clazel-sys`: the
/// network namespace and the seccomp allowlist (no `socket`) cover them.
#[cfg(target_os = "linux")]
fn landlock() -> Result<(), clazel_sys::Errno> {
    const EINVAL: i32 = 22; // the same on x86-64 and aarch64 Linux
    let mut last = clazel_sys::Errno(EINVAL);
    for abi in [clazel_sandbox::landlock::LATEST_ABI, 3, 2, 1] {
        let rights = clazel_sandbox::landlock::RENDERER
            .for_abi(abi)
            .handled_access_fs;
        match clazel_sys::linux::landlock_deny_filesystem(rights) {
            Ok(()) => return Ok(()),
            Err(e) if e.0 == EINVAL => last = e,
            Err(e) => return Err(e),
        }
    }
    Err(last)
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const ARCH: Option<clazel_sandbox::syscalls::Arch> = Some(clazel_sandbox::syscalls::Arch::X86_64);
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const ARCH: Option<clazel_sandbox::syscalls::Arch> = Some(clazel_sandbox::syscalls::Arch::Aarch64);
#[cfg(all(
    target_os = "linux",
    not(any(target_arch = "x86_64", target_arch = "aarch64"))
))]
const ARCH: Option<clazel_sandbox::syscalls::Arch> = None;

/// The seccomp-BPF allowlist, mapped instruction by instruction to
/// `clazel-sys`'s type.
#[cfg(target_os = "linux")]
fn seccomp() -> Result<(), String> {
    let arch = ARCH.ok_or("no seccomp program for this architecture")?;
    let program = clazel_sandbox::seccomp::renderer_program(arch).map_err(|e| format!("{e:?}"))?;
    let program: Vec<clazel_sys::linux::SockFilter> = program
        .iter()
        .map(|i| clazel_sys::linux::SockFilter {
            code: i.code,
            jt: i.jt,
            jf: i.jf,
            k: i.k,
        })
        .collect();
    clazel_sys::linux::seccomp_set_mode_filter_all_threads(&program).map_err(|e| e.to_string())
}

/// Windows cannot confine a running process: the host starts the renderer
/// inside the AppContainer and job (`launch`), and this only checks that it
/// did. A renderer started any other way (for example by hand) is refused.
#[cfg(windows)]
pub fn enter_process() -> Result<(), Failure> {
    match clazel_sys::windows::is_appcontainer() {
        Ok(true) => Ok(()),
        Ok(false) => layer::<(), &str>(
            "appcontainer",
            Err("not started inside the renderer AppContainer by the host"),
        ),
        Err(e) => layer::<(), _>("appcontainer", Err(e)),
    }
}

/// Other targets have no sandbox (`clazel-sys` is empty there): refuse.
#[cfg(not(any(target_os = "macos", target_os = "linux", windows)))]
pub fn enter_process() -> Result<(), Failure> {
    layer::<(), &str>("platform", Err("no sandbox for this operating system"))
}

/// Other targets: nothing (`enter_process` refused already).
#[cfg(not(any(target_os = "macos", target_os = "linux", windows)))]
pub fn enter_thread() -> Result<(), Failure> {
    Ok(())
}
