//! Every scene (`clazel_gpu::scenes`) drawn with Vulkan, against the software
//! reference, on Linux.
//!
//! - Against the reference: each channel within one level, since a GPU blends in
//!   floating point and the reference rounds the exact value once (`src/soft.rs`).
//!   The largest difference and how many channels differ are printed.
//! - On a software device (lavapipe, which CI uses) the pixels are also compared
//!   with stored ones (`tests/pixels-lavapipe-<arch>/<scene>-<list>.rgba`, RGBA8,
//!   rows from the top), equal, **where pixels are stored for the architecture**.
//!   Only aarch64's are: they were drawn by this backend on lavapipe (Mesa
//!   25.2.8, LLVM 20.1.2) in an aarch64 Linux container. lavapipe compiles its
//!   shaders for the CPU it runs on, so x86-64 may round differently; no x86-64
//!   machine has drawn them, so there (CI) this part is skipped, with a logged
//!   line, until someone stores them with `CLAZEL_GPU_BLESS=1`. Another Mesa may
//!   also round differently, and then this part fails while the reference part
//!   still holds. A hardware device is compared with the reference only.
//!
//! These make foreign calls, which Miri cannot run, so they are ignored under Miri.
//!
//! **A missing device is a skip only on a developer's machine.** When the `CI`
//! environment variable is set (GitHub Actions sets `CI=true`), no usable Vulkan
//! device is a test failure, saying so: CI's Linux jobs install lavapipe.
//!
//! The test binary writes what it ran on once, in a line starting `clazel-gpu:
//! Vulkan device`, and, on a developer's machine with no device, the skip once, in
//! a line starting `clazel-gpu: skipped`. Both go straight to standard error, not
//! through `print!` or `eprint!`, which libtest captures and drops for a passing
//! test: so they appear in CI's log, which runs `cargo test` without `--nocapture`.

#![cfg(target_os = "linux")]

use std::io::Write;
use std::path::PathBuf;
use std::sync::Once;

use clazel_displaylist::exec::encode_list;
use clazel_gpu::reference::{self, Masks};
use clazel_gpu::start::Launch;
use clazel_gpu::vulkan::VulkanBackend;
use clazel_gpu::{Backend, Gpu, Viewport, scenes};

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
/// Once per test binary: the line saying no stored pixels were compared.
static UNSTORED: Once = Once::new();

/// The backend, or why there is none: an error under CI (`CI` set), else `None` and
/// a logged skip.
fn backend_or_skip() -> Result<Option<VulkanBackend>, String> {
    match VulkanBackend::new(false) {
        Ok(b) => {
            DEVICE.call_once(|| {
                log(&format!(
                    "clazel-gpu: Vulkan device \"{}\" ({:?})",
                    b.device_name(),
                    b.adapter()
                ));
            });
            Ok(Some(b))
        }
        Err(e) if std::env::var_os("CI").is_some() => Err(format!(
            "no usable Vulkan device under CI ({e:?}); a missing device is a skip only on a \
             developer's machine"
        )),
        Err(e) => {
            SKIPPED.call_once(|| {
                log(&format!(
                    "clazel-gpu: skipped: no usable Vulkan device ({e:?}), and CI is not set"
                ));
            });
            Ok(None)
        }
    }
}

/// Start drawing as the GPU process does, through the shipped blocklist (item
/// 5.17c): no adapter is refused while the table is empty. Also whether the
/// device is a software driver.
fn start(backend: VulkanBackend) -> Result<(Gpu<VulkanBackend>, bool), String> {
    let (gpu, ready) = Gpu::start(backend, Launch::HARDWARE).map_err(|e| format!("{e:?}"))?;
    Ok((gpu, ready.software))
}

fn stored(name: &str, n: usize) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join(format!("tests/pixels-lavapipe-{}", std::env::consts::ARCH))
        .join(format!("{name}-{n}.rgba"))
}

#[test]
#[cfg_attr(miri, ignore)]
fn every_scene_on_vulkan() -> Result<(), String> {
    let Some(backend) = backend_or_skip()? else {
        return Ok(());
    };
    let bless = std::env::var_os("CLAZEL_GPU_BLESS").is_some();
    let (mut gpu, software) = start(backend)?;
    let mut failures = Vec::new();
    for scene in scenes::all() {
        let viewport = Viewport::new(scene.width, scene.height).ok_or("viewport")?;
        // Each scene starts a fresh GPU process's masks.
        gpu = start(gpu.into_backend())?.0;
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
            let have_stored = path.parent().is_some_and(std::path::Path::is_dir);
            if !software || !(bless || have_stored) {
                UNSTORED.call_once(|| {
                    log(&format!(
                        "clazel-gpu: skipped: no stored pixels compared (software device: \
                         {software}; pixels stored for {}: {have_stored})",
                        std::env::consts::ARCH
                    ));
                });
                continue;
            }
            if bless {
                if let Some(dir) = path.parent() {
                    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
                }
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

/// A list that breaks a rule draws nothing on Vulkan either, and the backend still
/// draws the next good list.
#[test]
#[cfg_attr(miri, ignore)]
fn a_refused_list_reaches_no_gpu_call() -> Result<(), String> {
    let Some(backend) = backend_or_skip()? else {
        return Ok(());
    };
    let (mut gpu, _) = start(backend)?;
    let viewport = Viewport::new(4, 4).ok_or("viewport")?;
    assert!(gpu.draw(&[3], viewport).is_err());
    // Nothing was drawn, so there is nothing to read.
    assert!(gpu.backend().read_pixels(&mut Vec::new()).is_err());
    gpu.draw(&[], viewport).map_err(|e| e.to_string())?;
    let mut px = Vec::new();
    gpu.backend()
        .read_pixels(&mut px)
        .map_err(|e| format!("{e:?}"))?;
    assert_eq!(px, vec![0; 64]);
    Ok(())
}

/// The frame the GPU process draws before it enters its sandbox
/// (`clazel_gpu::sandbox::warm_up`) gives exactly its pixels, and resizing the
/// target afterwards works.
#[test]
#[cfg_attr(miri, ignore)]
fn the_warm_up_frame_is_exact_and_the_target_resizes() -> Result<(), String> {
    let Some(mut backend) = backend_or_skip()? else {
        return Ok(());
    };
    clazel_gpu::sandbox::warm_up(&mut backend).map_err(|e| e.to_string())?;
    let (mut gpu, _) = start(backend)?;
    for (w, h) in [(64, 32), (1, 1), (300, 200)] {
        let viewport = Viewport::new(w, h).ok_or("viewport")?;
        gpu.draw(&[], viewport).map_err(|e| e.to_string())?;
        let mut px = Vec::new();
        gpu.backend()
            .read_pixels(&mut px)
            .map_err(|e| format!("{e:?}"))?;
        assert_eq!(px, vec![0; viewport.bytes()], "{w} by {h}");
    }
    Ok(())
}
