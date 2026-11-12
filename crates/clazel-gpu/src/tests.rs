//! Every scene ([`crate::scenes`]) through the decoder, the validator, the batching
//! and the fake backend, against the software reference: the pixels must be equal.
//!
//! The fake backend makes no foreign call, so these run under Miri, which is how
//! Miri covers the batching (the plan: "Miri runs the batching with a fake backend
//! and no foreign calls"). The scene "atlas" uploads 2.3 MB of coverage; it runs
//! under Miri too, measured in the README.

use clazel_displaylist::exec::{ExecItem, encode_list};

use crate::reference::{self, Masks};
use crate::scenes::{self, Scene};
use crate::soft::SoftBackend;
use crate::{Backend, Error, Gpu, Viewport};

fn run(scene: &Scene) -> Result<(), String> {
    let viewport = Viewport::new(scene.width, scene.height).ok_or_else(|| "viewport".to_owned())?;
    let mut gpu = Gpu::new(SoftBackend::new());
    let mut masks = Masks::default();
    for (n, list) in scene.lists.iter().enumerate() {
        let bytes = encode_list(list).ok_or_else(|| format!("{}: encode", scene.name))?;
        gpu.draw(&bytes, viewport)
            .map_err(|e| format!("{} list {n}: {e}", scene.name))?;
        let mut got = Vec::new();
        gpu.backend()
            .read_pixels(&mut got)
            .map_err(|e| format!("{e:?}"))?;
        let want = reference::draw(list, viewport, &mut masks)
            .ok_or_else(|| format!("{} list {n}: reference", scene.name))?;
        if got != want {
            let first = got.iter().zip(&want).position(|(a, b)| a != b);
            return Err(format!(
                "{} list {n}: pixels differ, first at byte {first:?}",
                scene.name
            ));
        }
    }
    Ok(())
}

fn scene(name: &str) -> Result<(), String> {
    let scene = scenes::all()
        .into_iter()
        .find(|s| s.name == name)
        .ok_or_else(|| format!("no scene {name}"))?;
    run(&scene)
}

#[test]
fn every_scene_is_tested() {
    let names: Vec<&str> = scenes::all().iter().map(|s| s.name).collect();
    assert_eq!(names, ["fill", "clips", "masks", "frames", "atlas"]);
}

#[test]
fn scene_fill() -> Result<(), String> {
    scene("fill")
}

#[test]
fn scene_clips() -> Result<(), String> {
    scene("clips")
}

#[test]
fn scene_masks() -> Result<(), String> {
    scene("masks")
}

#[test]
fn scene_frames() -> Result<(), String> {
    scene("frames")
}

/// Ignored under Miri: its 2.3 MB of coverage go through the byte-by-byte encoder
/// and decoder, and the whole scene list took 523 s on Miri's clock, past CI's 300 s
/// per test. Under Miri, a compaction in the middle of a list is covered by
/// `batch::tests::a_compaction_closes_the_open_batch` and
/// `atlas::tests::a_full_store_is_compacted_in_id_order`.
#[test]
#[cfg_attr(miri, ignore)]
fn scene_atlas() -> Result<(), String> {
    scene("atlas")
}

#[test]
fn bad_lists_are_refused_before_drawing() -> Result<(), Error> {
    let viewport = Viewport::new(4, 4).ok_or(Error::Range)?;
    let mut gpu = Gpu::new(SoftBackend::new());
    assert_eq!(gpu.draw(&[9], viewport), Err(Error::NotAList));
    let unbalanced = encode_list(&[ExecItem::PopClip]).ok_or(Error::Range)?;
    assert_eq!(gpu.draw(&unbalanced, viewport), Err(Error::Refused));
    let unknown = encode_list(&[ExecItem::DrawMask {
        id: 1,
        x: 0,
        y: 0,
        colour: 0,
    }])
    .ok_or(Error::Range)?;
    assert_eq!(gpu.draw(&unknown, viewport), Err(Error::Refused));
    assert_eq!(gpu.backend().frames, 0);
    Ok(())
}
