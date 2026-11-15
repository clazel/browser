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
use crate::start::Launch;
use crate::{Backend, Error, Gpu, Viewport};

fn run(scene: &Scene) -> Result<(), String> {
    let viewport = Viewport::new(scene.width, scene.height).ok_or_else(|| "viewport".to_owned())?;
    let (mut gpu, _) =
        Gpu::start(SoftBackend::new(), Launch::SOFTWARE).map_err(|e| format!("{e:?}"))?;
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

/// A compaction in the middle of a list, between two draws. 56 s on Miri's clock.
#[test]
fn scene_atlas() -> Result<(), String> {
    scene("atlas")
}

#[test]
fn bad_lists_are_refused_before_drawing() -> Result<(), Error> {
    let viewport = Viewport::new(4, 4).ok_or(Error::Range)?;
    let (mut gpu, _) =
        Gpu::start(SoftBackend::new(), Launch::SOFTWARE).map_err(|_| Error::Range)?;
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

/// The plan's test "a fake adapter matching a blocklist entry falls to software",
/// through every piece built so far: the GPU process started in hardware on a fake
/// device the table lists refuses before any list; the crash policy starts the tab
/// in software; the software start goes through; and every scene drawn there equals
/// the reference.
#[test]
fn a_listed_fake_adapter_falls_to_software() -> Result<(), String> {
    use crate::blocklist::{Adapter, Api, Version};
    use crate::policy::{Action, Config, Event, Policy, SiteId, TabId};

    let table = b"vulkan 0x1234 0x0001 1-1.5 https://example.org/evidence draws nothing";
    let device = Adapter {
        api: Api::Vulkan,
        vendor: 0x1234,
        device: 1,
        driver: Some(Version([1, 2, 0, 0])),
        software: false,
    };
    let mut policy = Policy::new(Config {
        fallback: true,
        software_only: false,
    });
    let tab = TabId(1);
    let start = policy.step(
        Event::Opened {
            tab,
            site: SiteId(7),
        },
        0,
    );
    assert_eq!(
        start,
        Some(Action::Start {
            tab,
            software: false
        })
    );
    let refused = Gpu::start_with(SoftBackend::with_adapter(device), Launch::HARDWARE, table);
    assert!(refused.is_err_and(|r| r.is_gpu_refused()));
    let next = policy.step(Event::Refused { tab }, 1);
    assert_eq!(
        next,
        Some(Action::Start {
            tab,
            software: true
        })
    );
    let (mut gpu, ready) = Gpu::start_with(SoftBackend::new(), Launch::SOFTWARE, table)
        .map_err(|e| format!("{e:?}"))?;
    assert!(ready.software);
    assert_eq!(
        policy.step(
            Event::Ready {
                tab,
                software: true
            },
            2
        ),
        Some(Action::Drawing {
            tab,
            software: true
        })
    );
    // Under Miri, the first scene only: each scene runs under Miri on its own
    // already (`scene_*`), and all five here would take about three minutes there.
    let all = scenes::all();
    let take = if cfg!(miri) { 1 } else { all.len() };
    for scene in all.iter().take(take) {
        let viewport =
            Viewport::new(scene.width, scene.height).ok_or_else(|| "viewport".to_owned())?;
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
            assert!(got == want, "{} list {n}: pixels differ", scene.name);
        }
        // A new scene is a new GPU process's masks.
        (gpu, _) = Gpu::start_with(gpu.into_backend(), Launch::SOFTWARE, table)
            .map_err(|e| format!("{e:?}"))?;
    }
    Ok(())
}
