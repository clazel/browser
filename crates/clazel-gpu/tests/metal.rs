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
//! CI's macOS runner may have no GPU: then each test prints why and passes without
//! drawing.

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

use std::path::PathBuf;

use clazel_displaylist::exec::encode_list;
use clazel_gpu::metal::MetalBackend;
use clazel_gpu::reference::{self, Masks};
use clazel_gpu::{Backend, Gpu, Viewport, scenes};

fn stored(name: &str, n: usize) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/pixels")
        .join(format!("{name}-{n}.rgba"))
}

#[test]
#[cfg_attr(miri, ignore)]
fn every_scene_on_metal() -> Result<(), String> {
    let backend = match MetalBackend::new() {
        Ok(b) => b,
        Err(e) => {
            eprintln!("skipped: no usable Metal device ({e:?})");
            return Ok(());
        }
    };
    let bless = std::env::var_os("CLAZEL_GPU_BLESS").is_some();
    let mut gpu = Gpu::new(backend);
    let mut failures = Vec::new();
    for scene in scenes::all() {
        let viewport = Viewport::new(scene.width, scene.height).ok_or("viewport")?;
        // Each scene starts a fresh GPU process's masks.
        gpu = Gpu::new(gpu.into_backend());
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
    let Ok(backend) = MetalBackend::new() else {
        eprintln!("skipped: no usable Metal device");
        return Ok(());
    };
    let mut gpu = Gpu::new(backend);
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
