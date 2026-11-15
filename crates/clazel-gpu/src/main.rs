//! The GPU process (items 5.17b, 5.18, 5.21a, 5.23): one per tab, started by the
//! host when the kernel says `SpawnGpu`, paired with that tab's renderer.
//!
//! `clazel-gpu --list-fd N --surface-fd M [--ignore-blocklist] [--software]`
//!
//! - Standard input and output are the kernel's channel (one socket, as the
//!   renderer's), standard error the host's log.
//! - `N` is the list channel's descriptor, `M` the surface channel's
//!   ([`clazel_gpu::channel`]), inherited from the host, which cleared their
//!   close-on-exec flags for this start: socket pairs on macOS, pipes on Linux,
//!   where `/dev/fd/N` cannot open a socket. Each is opened again through
//!   `/dev/fd`, which needs no `unsafe`, **before** the sandbox is entered. On
//!   Windows they are the values of two inherited pipe handles, each duplicated
//!   and read or written through `clazel_sys::windows::Inherited`.
//! - `--ignore-blocklist` is `browse --gpu=hardware` (item 5.17c).
//! - `--software` is `browse --gpu=software`: the software driver (lavapipe on
//!   Linux, WARP on Windows). On macOS there is none, so the start is refused.
//!
//! Then the backend and the sandbox (`clazel_gpu::sandbox`, item 5.21a: Metal on
//! macOS on Apple silicon, Vulkan on Linux, Direct3D 12 on Windows, where the
//! host has already confined the process), the blocklist (`Gpu::start`), the
//! answer (`GpuReady` or `GpuRefused`) and the loop (`process::run`). Every other
//! target has no GPU backend yet (item 5.17b's rest), so the process says so and
//! exits, which the crash policy counts as a refusal.

use std::process::ExitCode;

/// The descriptor numbers given as `--list-fd` and `--surface-fd`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Args {
    list: u32,
    surface: u32,
    ignore_blocklist: bool,
    software: bool,
}

fn parse(args: &[String]) -> Option<Args> {
    let value = |name: &str| {
        let i = args.iter().position(|a| a == name)?;
        args.get(i.checked_add(1)?)?.parse::<u32>().ok()
    };
    Some(Args {
        list: value("--list-fd")?,
        surface: value("--surface-fd")?,
        ignore_blocklist: args.iter().any(|a| a == "--ignore-blocklist"),
        software: args.iter().any(|a| a == "--software"),
    })
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let Some(args) = parse(&args) else {
        eprintln!("usage: clazel-gpu --list-fd N --surface-fd M [--ignore-blocklist] [--software]");
        return ExitCode::from(2);
    };
    match run(args) {
        Ok(why) => {
            eprintln!("clazel-gpu: ended: {why}");
            ExitCode::SUCCESS
        }
        Err(why) => {
            eprintln!("clazel-gpu: {why}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(not(any(
    all(target_os = "macos", target_arch = "aarch64"),
    target_os = "linux",
    windows
)))]
fn run(_: Args) -> Result<String, String> {
    Err("no GPU backend on this platform yet (phase-5.md item 5.17b)".to_owned())
}

/// The backend, made and sandboxed (`clazel_gpu::sandbox`).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn backend(_software: bool) -> Result<clazel_gpu::metal::MetalBackend, String> {
    clazel_gpu::sandbox::start_metal().map_err(|e| e.to_string())
}

/// The backend, made and sandboxed (`clazel_gpu::sandbox`). The device is the
/// machine's GPU if the loader lists one, else its software driver; with
/// `software`, the software driver if there is one.
#[cfg(target_os = "linux")]
fn backend(software: bool) -> Result<clazel_gpu::vulkan::VulkanBackend, String> {
    let backend = clazel_gpu::sandbox::start_vulkan(software).map_err(|e| e.to_string())?;
    eprintln!("clazel-gpu: drawing with {}", backend.device_name());
    Ok(backend)
}

/// The backend (`clazel_gpu::sandbox`), in a process the host started inside
/// the GPU process's AppContainer. The adapter is the machine's GPU if DXGI
/// lists one, else WARP; with `software`, WARP.
#[cfg(windows)]
fn backend(software: bool) -> Result<clazel_gpu::d3d12::D3d12Backend, String> {
    let backend = clazel_gpu::sandbox::start_d3d12(software).map_err(|e| e.to_string())?;
    eprintln!("clazel-gpu: drawing with {}", backend.device_name());
    Ok(backend)
}

/// The list channel to read and the surface channel to write, from their
/// descriptor numbers. Before the sandbox, which refuses every open after it.
#[cfg(any(all(target_os = "macos", target_arch = "aarch64"), target_os = "linux"))]
fn channels(args: Args) -> Result<(std::fs::File, std::fs::File), String> {
    let list = std::fs::File::open(format!("/dev/fd/{}", args.list))
        .map_err(|e| format!("cannot open the list channel {}: {e}", args.list))?;
    let surface = std::fs::OpenOptions::new()
        .write(true)
        .open(format!("/dev/fd/{}", args.surface))
        .map_err(|e| format!("cannot open the surface channel {}: {e}", args.surface))?;
    Ok((list, surface))
}

/// The list channel to read and the surface channel to write, from the values
/// of the two handles this process inherited.
#[cfg(windows)]
fn channels(
    args: Args,
) -> Result<
    (
        clazel_sys::windows::Inherited,
        clazel_sys::windows::Inherited,
    ),
    String,
> {
    use clazel_sys::windows::Inherited;
    let list = Inherited::open(u64::from(args.list))
        .map_err(|e| format!("cannot open the list channel {}: {e}", args.list))?;
    let surface = Inherited::open(u64::from(args.surface))
        .map_err(|e| format!("cannot open the surface channel {}: {e}", args.surface))?;
    Ok((list, surface))
}

#[cfg(any(
    all(target_os = "macos", target_arch = "aarch64"),
    target_os = "linux",
    windows
))]
fn run(args: Args) -> Result<String, String> {
    use std::io::Write;

    use clazel_gpu::Gpu;
    use clazel_gpu::process::{Server, ready_frame, refused_frame, run};
    use clazel_gpu::start::{Check, Launch, Mode};

    let (list, surface) = channels(args)?;
    let backend = backend(args.software)?;
    let launch = Launch {
        mode: if args.software {
            Mode::Software
        } else {
            Mode::Hardware
        },
        check: if args.ignore_blocklist {
            Check::Ignore
        } else {
            Check::Obey
        },
    };
    let mut out = std::io::stdout();
    let answer = |out: &mut std::io::Stdout, frame: Option<Vec<u8>>| {
        let frame = frame.ok_or("cannot encode the answer")?;
        out.write_all(&frame)
            .and_then(|()| out.flush())
            .map_err(|e| format!("cannot answer the kernel: {e}"))
    };
    match Gpu::start(backend, launch) {
        Ok((gpu, ready)) => {
            answer(&mut out, ready_frame(ready))?;
            let why = run(Server::new(gpu), std::io::stdin(), out, list, surface);
            Ok(why.to_string())
        }
        Err(refusal) => {
            if refusal.is_gpu_refused() {
                answer(&mut out, refused_frame())?;
            }
            Err(format!("refused: {refusal:?}"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Args, parse};

    fn strings(a: &[&str]) -> Vec<String> {
        a.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn both_descriptors_are_needed() {
        let got = parse(&strings(&["gpu", "--list-fd", "7", "--surface-fd", "9"]));
        assert_eq!(
            got,
            Some(Args {
                list: 7,
                surface: 9,
                ignore_blocklist: false,
                software: false
            })
        );
        assert_eq!(parse(&strings(&["gpu", "--list-fd", "7"])), None);
        assert_eq!(
            parse(&strings(&["gpu", "--list-fd", "x", "--surface-fd", "9"])),
            None
        );
        let ignore = parse(&strings(&[
            "gpu",
            "--surface-fd",
            "1",
            "--list-fd",
            "2",
            "--ignore-blocklist",
        ]));
        assert!(ignore.is_some_and(|a| a.ignore_blocklist && !a.software));
        let software = parse(&strings(&[
            "gpu",
            "--list-fd",
            "1",
            "--surface-fd",
            "2",
            "--software",
        ]));
        assert!(software.is_some_and(|a| a.software && !a.ignore_blocklist));
    }
}
