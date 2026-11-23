//! Item 5.21a: the GPU process enters its sandbox, on macOS on Apple silicon and
//! on Linux.
//!
//! The policy is data from `clazel-sandbox`; the only code that hands it to the OS
//! is `clazel-sys`, whose functions are safe. This module decides the order,
//! which is what the measured policy depends on.
//!
//! **macOS** ([`start_metal`]):
//!
//! 1. make the Metal backend: the device, its command queue and the one fixed
//!    pipeline, compiled from our own shader source (`shaders/quad.metal`);
//! 2. enter the Seatbelt profile (`seatbelt::gpu_profile`), for good;
//! 3. only then may the caller check the blocklist (`Gpu::start`) and read a
//!    message.
//!
//! **Linux** ([`start_vulkan`]):
//!
//! 0. the environment must hold [`LINUX_ENVIRONMENT`], which the host sets
//!    when it starts the process (`clazel-renderer`'s `launch::spawn_gpu`): it
//!    turns off Mesa's on-disk shader cache, whose worker thread otherwise
//!    opens, locks and writes cache files at any time, the filter below
//!    included. A process started without it is refused here, every time,
//!    rather than killed by its filter some of the time;
//! 1. `no_new_privs`, then the namespaces (`namespaces::GPU`: user, mount,
//!    network, IPC), while the process still has one thread, which a user
//!    namespace needs;
//! 2. make the Vulkan backend: the loader finds and loads the driver, which
//!    opens what it needs (a device node; nothing for lavapipe), and the one
//!    fixed pipeline is made from our own SPIR-V;
//! 3. draw one frame of our own ([`warm_up_frame`]: a fill, a mask from an
//!    uploaded atlas, two scissors) and read it back, so that the driver has
//!    started its worker threads and compiled every variant of our shaders
//!    before anything is forbidden. Its pixels are checked: a driver that draws
//!    the warm-up wrong is refused here;
//! 4. Landlock with no rule (no filesystem access; it binds the calling thread
//!    and the threads it creates, not the driver's existing workers);
//! 5. the seccomp list on **every thread at once**
//!    (`SECCOMP_FILTER_FLAG_TSYNC`), so the workers of step 3 are filtered too:
//!    no `open`, `openat`, `socket` or `connect` for any of them. On a software
//!    device it is `seccomp::gpu_program`, measured on lavapipe; on a hardware
//!    device `seccomp::gpu_hardware_program`, which also allows `ioctl` and has
//!    never been measured, so a hardware driver may be killed here or later;
//! 6. only then may the caller check the blocklist and read a message.
//!
//! No byte from a page or a renderer is read before the last step, so a page
//! cannot reach what the warm-up opens except through what it leaves open, which
//! is the sandbox's stated weakness (`clazel-sandbox`'s `seatbelt` and `syscalls`
//! modules). Fail closed: an error in any step ends the GPU process before
//! `GpuReady`, which the crash policy (item 5.17c) counts as a refusal of the
//! machine's GPU.
//!
//! **Windows** ([`start_d3d12`]), where a running process cannot be confined:
//! the host starts the GPU process already inside its AppContainer and Job
//! Object (`clazel-renderer`'s `launch`, with `clazel_sandbox::appcontainer`'s
//! `GPU_*` policy), so there is no moment before the sandbox and nothing to
//! enter. The order here is:
//!
//! 1. check that the process is in an AppContainer, and stop if it is not;
//! 2. make the Direct3D 12 backend;
//! 3. draw and check the warm-up frame, as on Linux.
//!
//! None of this has run on Windows.

use std::fmt;

use crate::backend::BackendError;

/// Why the GPU process could not start sandboxed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    /// No usable device, queue or pipeline, or the warm-up frame failed.
    Device(BackendError),
    /// The warm-up frame's pixels were not the expected ones.
    WarmUp,
    /// A sandbox layer was refused: its name, and the OS's reason.
    Layer(&'static str, String),
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Failure::Device(e) => write!(f, "no GPU device: {} ({})", e.what, e.code),
            Failure::WarmUp => f.write_str("the warm-up frame was drawn wrong"),
            Failure::Layer(layer, why) => write!(f, "sandbox layer `{layer}` failed: {why}"),
        }
    }
}

impl std::error::Error for Failure {}

/// What the host adds to the Linux GPU process's environment, and what
/// [`start_vulkan`] checks is there before it makes the backend.
///
/// `MESA_SHADER_CACHE_DISABLE=true` turns off Mesa's on-disk shader cache
/// (`util/disk_cache.c`, read when the driver makes its device). With the cache
/// on, lavapipe hands each compiled shader to a worker thread (named `disk$0`)
/// that writes it under `~/.cache/mesa_shader_cache` later, with `openat`,
/// `flock` and more. With a cold cache, as on every CI runner, those writes can
/// still be queued when the seccomp filter is installed, and the first one kills
/// the process. **Observed** on lavapipe (Mesa 25.2.8) in an aarch64 container,
/// over `clazel`'s `tests/browse_gpu.rs` with the cache emptied before each run:
/// 3 runs in 10 failed, each with the kernel's audit line naming `disk$0`'s
/// `openat` (twice) or `flock` (once) as the call refused. The filter is not
/// widened for it: a cache that writes files is what the sandbox exists to
/// forbid, and reading compiled machine code back from a file any program of
/// the user can write is a way in. The warm-up frame compiles every shader
/// before the filter, so nothing needs the cache after it.
pub const LINUX_ENVIRONMENT: &[(&str, &str)] = &[("MESA_SHADER_CACHE_DISABLE", "true")];

/// Whether `get` (the environment, by name) holds [`LINUX_ENVIRONMENT`].
pub fn has_environment(get: impl Fn(&str) -> Option<std::ffi::OsString>) -> bool {
    LINUX_ENVIRONMENT
        .iter()
        .all(|(name, value)| get(name).is_some_and(|v| v == *value))
}

/// Steps 1 and 2 on macOS: the Metal backend, made before this process entered
/// the GPU process's Seatbelt profile, which it now has. On `Err` the process may
/// or may not be sandboxed and must exit.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub fn start_metal() -> Result<crate::metal::MetalBackend, Failure> {
    let backend = crate::metal::MetalBackend::new().map_err(Failure::Device)?;
    let profile = clazel_sandbox::seatbelt::gpu_profile();
    clazel_sys::macos::sandbox_init_profile(&profile)
        .map_err(|e| Failure::Layer("seatbelt", e.to_string()))?;
    Ok(backend)
}

/// The frame step 3 draws on Linux, and the pixels it must give: a 4 by 2
/// target; an opaque red fill over the left 2 by 2 under one scissor, then a
/// mask of coverage 255, 0 / 0, 255 in opaque blue over the right 2 by 2 under
/// another. Ours, fixed, and read by no page.
pub fn warm_up_frame() -> (crate::backend::Frame, Vec<u8>) {
    use crate::backend::{Frame, Op, Quad};
    use crate::geom::{Rect, Viewport};

    let (left, right) = (
        Rect {
            x0: 0,
            y0: 0,
            x1: 2,
            y1: 2,
        },
        Rect {
            x0: 2,
            y0: 0,
            x1: 4,
            y1: 2,
        },
    );
    let frame = Frame {
        viewport: Viewport::new(4, 2),
        ops: vec![
            Op::Atlas { capacity: 4 },
            Op::Upload {
                offset: 0,
                start: 0,
                len: 4,
            },
            Op::Draw {
                scissor: left,
                first: 0,
                count: 1,
            },
            Op::Draw {
                scissor: right,
                first: 1,
                count: 1,
            },
        ],
        quads: vec![
            Quad {
                rect: left,
                origin_x: 0,
                origin_y: 0,
                offset: 0,
                columns: 0,
                colour: 0xFFFF_0000,
            },
            Quad {
                rect: right,
                origin_x: 2,
                origin_y: 0,
                offset: 0,
                columns: 2,
                colour: 0xFF00_00FF,
            },
        ],
        bytes: vec![255, 0, 0, 255],
        image_draws: Vec::new(),
    };
    const RED: [u8; 4] = [255, 0, 0, 255];
    const BLUE: [u8; 4] = [0, 0, 255, 255];
    const NONE: [u8; 4] = [0, 0, 0, 0];
    let pixels = [RED, RED, BLUE, NONE, RED, RED, NONE, BLUE].concat();
    (frame, pixels)
}

/// Draw [`warm_up_frame`] with `backend` and check its pixels.
pub fn warm_up<B: crate::backend::Backend>(backend: &mut B) -> Result<(), Failure> {
    let (frame, want) = warm_up_frame();
    backend.draw_frame(&frame).map_err(Failure::Device)?;
    let mut got = Vec::new();
    backend.read_pixels(&mut got).map_err(Failure::Device)?;
    if got == want {
        Ok(())
    } else {
        Err(Failure::WarmUp)
    }
}

/// Steps 0 to 5 on Linux: the Vulkan backend (`software` chooses the device,
/// `crate::vulkan`), in a process that is now in the GPU process's namespaces,
/// Landlock domain and seccomp filter. On `Err` the process may or may not be
/// sandboxed and must exit.
#[cfg(target_os = "linux")]
pub fn start_vulkan(software: bool) -> Result<crate::vulkan::VulkanBackend, Failure> {
    use clazel_sandbox::namespaces::Namespace;
    use clazel_sys::linux::{self, Namespaces};

    if !has_environment(|name| std::env::var_os(name)) {
        return Err(Failure::Layer(
            "environment",
            format!("the host did not set {LINUX_ENVIRONMENT:?}"),
        ));
    }
    let layer = |name: &'static str, r: Result<(), clazel_sys::Errno>| {
        r.map_err(|e| Failure::Layer(name, e.to_string()))
    };
    layer("no_new_privs", linux::set_no_new_privs())?;
    let namespaces = clazel_sandbox::namespaces::GPU
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
    layer("namespaces", linux::unshare(namespaces))?;
    let mut backend = crate::vulkan::VulkanBackend::new(software).map_err(Failure::Device)?;
    warm_up(&mut backend)?;
    layer("landlock", landlock())?;
    let software = crate::backend::Backend::adapter(&backend).software;
    seccomp(software).map_err(|e| Failure::Layer("seccomp", e))?;
    Ok(backend)
}

/// Steps 1 to 3 on Windows: the Direct3D 12 backend (`software` chooses the
/// adapter, `crate::d3d12`), in a process that the host started inside the GPU
/// process's AppContainer. On `Err` the process must exit.
#[cfg(windows)]
pub fn start_d3d12(software: bool) -> Result<crate::d3d12::D3d12Backend, Failure> {
    match clazel_sys::windows::is_appcontainer() {
        Ok(true) => {}
        Ok(false) => {
            return Err(Failure::Layer(
                "appcontainer",
                "the GPU process was not started inside an AppContainer".to_owned(),
            ));
        }
        Err(e) => return Err(Failure::Layer("appcontainer", e.to_string())),
    }
    let mut backend = crate::d3d12::D3d12Backend::new(software).map_err(Failure::Device)?;
    warm_up(&mut backend)?;
    Ok(backend)
}

/// Landlock with no rule, as the renderer's (`clazel-renderer`'s `sandbox`):
/// the newest filesystem rights the kernel knows.
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

/// The GPU process's seccomp list, on every thread: the software driver's
/// (measured on lavapipe), or with a hardware device the one that also allows
/// `ioctl` (not measured).
#[cfg(target_os = "linux")]
fn seccomp(software: bool) -> Result<(), String> {
    let arch = ARCH.ok_or("no seccomp program for this architecture")?;
    let program = if software {
        clazel_sandbox::seccomp::gpu_program(arch)
    } else {
        clazel_sandbox::seccomp::gpu_hardware_program(arch)
    }
    .map_err(|e| format!("{e:?}"))?;
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

#[cfg(test)]
mod tests {
    use super::{Failure, LINUX_ENVIRONMENT, has_environment, warm_up, warm_up_frame};
    use crate::soft::SoftBackend;
    use std::ffi::OsString;

    /// The cache is off only when the variable says so exactly.
    #[test]
    fn the_environment_must_turn_the_shader_cache_off() {
        assert_eq!(
            LINUX_ENVIRONMENT,
            &[("MESA_SHADER_CACHE_DISABLE", "true")][..]
        );
        let with = |value: Option<&str>| {
            has_environment(|name| {
                (name == "MESA_SHADER_CACHE_DISABLE")
                    .then_some(value)
                    .flatten()
                    .map(OsString::from)
            })
        };
        assert!(with(Some("true")));
        assert!(!with(None));
        assert!(!with(Some("false")));
        assert!(!with(Some("")));
    }

    /// The software reference draws the warm-up frame to the pixels it names, so
    /// a GPU that does not is the one that is wrong.
    #[test]
    fn the_warm_up_frame_draws_to_its_pixels() {
        let mut soft = SoftBackend::new();
        assert_eq!(warm_up(&mut soft), Ok(()));
        let (frame, pixels) = warm_up_frame();
        assert_eq!(pixels.len(), frame.viewport.map_or(0, |v| v.bytes()));
    }

    #[test]
    fn failures_name_their_layer() {
        let f = Failure::Layer("seccomp", "refused".to_owned());
        assert_eq!(f.to_string(), "sandbox layer `seccomp` failed: refused");
        assert!(Failure::WarmUp.to_string().contains("warm-up"));
    }
}
