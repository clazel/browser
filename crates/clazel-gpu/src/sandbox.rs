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
//! Windows has no GPU backend yet (item 5.17b's rest), so nothing here enters
//! its policy; `clazel-sandbox` holds it as data.

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

/// Steps 1 to 5 on Linux: the Vulkan backend (`software` chooses the device,
/// `crate::vulkan`), in a process that is now in the GPU process's namespaces,
/// Landlock domain and seccomp filter. On `Err` the process may or may not be
/// sandboxed and must exit.
#[cfg(target_os = "linux")]
pub fn start_vulkan(software: bool) -> Result<crate::vulkan::VulkanBackend, Failure> {
    use clazel_sandbox::namespaces::Namespace;
    use clazel_sys::linux::{self, Namespaces};

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
    use super::{Failure, warm_up, warm_up_frame};
    use crate::soft::SoftBackend;

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
