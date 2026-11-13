//! Every scene (`clazel_gpu::scenes`) drawn with Metal, against the software
//! reference and against stored pixels (`tests/pixels/<scene>-<list>.rgba`, RGBA8,
//! rows from the top), on macOS on Apple silicon.
//!
//! - Against the reference: each channel within one level, since a GPU blends in
//!   floating point and the reference rounds the exact value once (`src/soft.rs`).
//!   The largest difference and how many channels differ are printed.
//! - Against the stored pixels: equal. They were drawn by this backend on the
//!   development machine (an Apple M1 Pro); another GPU may round differently, and
//!   then this part fails while the reference part still holds. To store them again,
//!   run with `CLAZEL_GPU_BLESS=1`.
//!
//! These make foreign calls, which Miri cannot run, so they are ignored under Miri.
//!
//! **A missing device is a skip only on a developer's machine.** When the `CI`
//! environment variable is set (GitHub Actions sets `CI=true`), no usable Metal
//! device is a test failure, saying so. CI's macOS job runs on `macos-15` (Apple
//! silicon, virtualised), which is expected to offer a paravirtual Metal device.
//!
//! The test binary writes what it ran on once, in a line starting `clazel-gpu: Metal
//! device`, and, on a developer's machine with no device, the skip once, in a line
//! starting `clazel-gpu: skipped`. Both go straight to standard error, not through
//! `print!` or `eprint!`, which libtest captures and drops for a passing test: so
//! they appear in CI's log, which runs `cargo test` without `--nocapture`.
//! The name comes from the OS (`system_profiler SPDisplaysDataType`'s chipset model,
//! and `sysctl`'s `hw.model` and `kern.hv_vmm_present`, which is 1 in a virtual
//! machine), run as subprocesses: the `clazel-sys` wrappers cannot read the Metal
//! device's own name without new foreign calls, which this test does not add.

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

use std::io::Write;
use std::path::PathBuf;
use std::sync::Once;

use clazel_displaylist::exec::encode_list;
use clazel_gpu::metal::MetalBackend;
use clazel_gpu::reference::{self, Masks};
use clazel_gpu::start::Launch;
use clazel_gpu::{Backend, Gpu, Viewport, scenes};

/// What the OS says the GPU is, for the log. Never fails: a missing tool prints
/// "unknown".
fn describe_device() -> String {
    let run = |cmd: &str, args: &[&str]| {
        std::process::Command::new(cmd)
            .args(args)
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
            .unwrap_or_default()
    };
    let displays = run("system_profiler", &["SPDisplaysDataType"]);
    let pick = |key: &str| {
        displays
            .lines()
            .find_map(|l| l.trim().strip_prefix(key).map(|v| v.trim().to_owned()))
            .unwrap_or_else(|| "unknown".to_owned())
    };
    let sysctl = |name: &str| {
        let v = run("sysctl", &["-n", name]);
        let v = v.trim();
        if v.is_empty() {
            "unknown".to_owned()
        } else {
            v.to_owned()
        }
    };
    format!(
        "clazel-gpu: Metal device \"{}\" (Metal support: {}; hw.model {}; kern.hv_vmm_present {}; \
         names from the OS, not from the MTLDevice)",
        pick("Chipset Model:"),
        pick("Metal Support:"),
        sysctl("hw.model"),
        sysctl("kern.hv_vmm_present"),
    )
}

/// Write `line` to standard error in one call, past libtest's capture, so it is in
/// the log whether the test passes or fails and parallel tests cannot interleave it.
/// A failed write is ignored: the line is for the log, not part of the test.
fn log(line: &str) {
    let mut err = std::io::stderr().lock();
    let _ignored = err.write_all(format!("{line}\n").as_bytes());
}

/// Once per test binary: the device line.
static DEVICE: Once = Once::new();
/// Once per test binary: the skip line.
static SKIPPED: Once = Once::new();

/// The backend, or why there is none: an error under CI (`CI` set), else `None` and
/// a logged skip.
fn backend_or_skip() -> Result<Option<MetalBackend>, String> {
    DEVICE.call_once(|| log(&describe_device()));
    match MetalBackend::new() {
        Ok(b) => Ok(Some(b)),
        Err(e) if std::env::var_os("CI").is_some() => Err(format!(
            "no usable Metal device under CI ({e:?}); a missing device is a skip only on a \
             developer's machine"
        )),
        Err(e) => {
            SKIPPED.call_once(|| {
                log(&format!(
                    "clazel-gpu: skipped: no usable Metal device ({e:?}), and CI is not set"
                ));
            });
            Ok(None)
        }
    }
}

/// Start drawing as the GPU process does, through the shipped blocklist (item
/// 5.17c): a Metal adapter is never refused while the table is empty.
fn start(backend: MetalBackend) -> Result<Gpu<MetalBackend>, String> {
    let (gpu, ready) = Gpu::start(backend, Launch::HARDWARE).map_err(|e| format!("{e:?}"))?;
    if ready.software {
        return Err("a Metal adapter reported as software".to_owned());
    }
    Ok(gpu)
}

fn stored(name: &str, n: usize) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/pixels")
        .join(format!("{name}-{n}.rgba"))
}

#[test]
#[cfg_attr(miri, ignore)]
fn every_scene_on_metal() -> Result<(), String> {
    let Some(backend) = backend_or_skip()? else {
        return Ok(());
    };
    let bless = std::env::var_os("CLAZEL_GPU_BLESS").is_some();
    let mut gpu = start(backend)?;
    let mut failures = Vec::new();
    for scene in scenes::all() {
        let viewport = Viewport::new(scene.width, scene.height).ok_or("viewport")?;
        // Each scene starts a fresh GPU process's masks.
        gpu = start(gpu.into_backend())?;
        let mut masks = Masks::default();
        for (n, list) in scene.lists.iter().enumerate() {
            let bytes = encode_list(list).ok_or("encode")?;
            gpu.draw(&bytes, viewport)
                .map_err(|e| format!("{} list {n}: {e}", scene.name))?;
            let mut got = Vec::new();
            gpu.backend()
                .read_pixels(&mut got)
                .map_err(|e| format!("{e:?}"))?;
            let want = reference::draw(list, viewport, &mut masks).ok_or("reference")?;
            let diffs = got
                .iter()
                .zip(&want)
                .filter(|(a, b)| a != b)
                .map(|(a, b)| a.abs_diff(*b))
                .collect::<Vec<u8>>();
            let worst = diffs.iter().copied().max().unwrap_or(0);
            println!(
                "{} list {n}: {} of {} channels differ from the reference, by at most {worst}",
                scene.name,
                diffs.len(),
                want.len()
            );
            if got.len() != want.len() || worst > 1 {
                failures.push(format!(
                    "{} list {n}: differs from the reference by {worst}",
                    scene.name
                ));
            }
            let path = stored(scene.name, n);
            if bless {
                std::fs::write(&path, &got).map_err(|e| format!("{}: {e}", path.display()))?;
            } else {
                match std::fs::read(&path) {
                    Ok(saved) if saved == got => {}
                    Ok(_) => failures.push(format!("{}: pixels differ", path.display())),
                    Err(e) => failures.push(format!("{}: {e}", path.display())),
                }
            }
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n"))
    }
}

/// A list that breaks a rule draws nothing on Metal either, and the backend still
/// draws the next good list.
#[test]
#[cfg_attr(miri, ignore)]
fn a_refused_list_reaches_no_gpu_call() -> Result<(), String> {
    let Some(backend) = backend_or_skip()? else {
        return Ok(());
    };
    let mut gpu = start(backend)?;
    let viewport = Viewport::new(4, 4).ok_or("viewport")?;
    assert!(gpu.draw(&[3], viewport).is_err());
    assert!(gpu.backend().target().is_none());
    gpu.draw(&[], viewport).map_err(|e| e.to_string())?;
    let mut px = Vec::new();
    gpu.backend()
        .read_pixels(&mut px)
        .map_err(|e| format!("{e:?}"))?;
    assert_eq!(px, vec![0; 64]);
    Ok(())
}
