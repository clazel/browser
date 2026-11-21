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
    assert_eq!(
        names,
        [
            "fill",
            "clips",
            "masks",
            "frames",
            "atlas",
            "images",
            "image-frames",
            "image-store"
        ]
    );
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

/// Every image item, with each filter, at the edges, under a clip, scaled and
/// cut to a source rectangle.
/// Ignored under Miri: 1,920 pixels of exact rational filtering, far over the budget there.
#[test]
#[cfg_attr(miri, ignore)]
fn scene_images() -> Result<(), String> {
    scene("images")
}

/// An image kept from one list to the next, freed, its id uploaded again, and a
/// list with no draw between.
/// Ignored under Miri, as `scene_images`.
#[test]
#[cfg_attr(miri, ignore)]
fn scene_image_frames() -> Result<(), String> {
    scene("image-frames")
}

/// A compaction of the image store in the middle of a list, between two draws.
/// Ignored under Miri: 1 MiB of images, as the atlas scene is its own budget.
#[test]
#[cfg_attr(miri, ignore)]
fn scene_image_store() -> Result<(), String> {
    scene("image-store")
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
    // already (`scene_*`), and all eight here would take far longer there.
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

/// Item 6.12: the image items through the decoder, the validator, the batching and
/// the fake backend, with expected pixels worked out by hand.
mod images {
    use clazel_displaylist::exec::{ExecItem, encode_list};

    use crate::soft::SoftBackend;
    use crate::start::Launch;
    use crate::{Backend, Error, Gpu, Viewport};

    fn upload(id: u32, width: u16, height: u16, pixels: Vec<u8>) -> ExecItem {
        ExecItem::UploadImage {
            id,
            image_width: width,
            image_height: height,
            pixels,
        }
    }

    fn put(
        id: u32,
        dest: (i32, i32, u32, u32),
        src: (u16, u16, u16, u16),
        linear: bool,
    ) -> ExecItem {
        ExecItem::DrawImage {
            id,
            x: dest.0,
            y: dest.1,
            width: dest.2,
            height: dest.3,
            src_x: src.0,
            src_y: src.1,
            src_width: src.2,
            src_height: src.3,
            linear,
        }
    }

    fn gpu() -> Result<Gpu<SoftBackend>, String> {
        Gpu::start(SoftBackend::new(), Launch::SOFTWARE)
            .map(|(g, _)| g)
            .map_err(|e| format!("{e:?}"))
    }

    /// Draw `items` at `w` by `h` and give the target's pixels.
    fn draw_on(
        gpu: &mut Gpu<SoftBackend>,
        items: &[ExecItem],
        w: u32,
        h: u32,
    ) -> Result<Vec<u8>, String> {
        let viewport = Viewport::new(w, h).ok_or("viewport")?;
        let bytes = encode_list(items).ok_or("encode")?;
        gpu.draw(&bytes, viewport).map_err(|e| e.to_string())?;
        let mut px = Vec::new();
        gpu.backend()
            .read_pixels(&mut px)
            .map_err(|e| format!("{e:?}"))?;
        Ok(px)
    }

    /// The red channel of each pixel of a one-row target.
    fn reds(px: &[u8]) -> Vec<u8> {
        px.iter().step_by(4).copied().collect()
    }

    /// Opaque grey pixels of the given levels.
    fn greys(levels: &[u8]) -> Vec<u8> {
        levels.iter().flat_map(|&v| [v, v, v, 255]).collect()
    }

    #[test]
    fn nearest_takes_the_pixel_the_centre_falls_in() -> Result<(), String> {
        let mut g = gpu()?;
        // Two pixels to four: the centres are at 0.25, 0.75, 1.25 and 1.75.
        let items = [
            upload(0, 2, 1, greys(&[10, 200])),
            put(0, (0, 0, 4, 1), (0, 0, 2, 1), false),
        ];
        assert_eq!(reds(&draw_on(&mut g, &items, 4, 1)?), [10, 10, 200, 200]);
        Ok(())
    }

    #[test]
    fn linear_blends_by_the_fractions_and_clamps_at_the_ends() -> Result<(), String> {
        let mut g = gpu()?;
        // 0 and 255 to four pixels: weights 0, 1/4, 3/4 and 1 of the second; the
        // first and last are the ends exactly, not blended with anything outside.
        let items = [
            upload(0, 2, 1, greys(&[0, 255])),
            put(0, (0, 0, 4, 1), (0, 0, 2, 1), true),
        ];
        // 255 / 4 = 63.75 and 3 × 255 / 4 = 191.25, rounded to nearest.
        assert_eq!(reds(&draw_on(&mut g, &items, 4, 1)?), [0, 64, 191, 255]);
        Ok(())
    }

    /// A source rectangle is a fence: the pixel outside it (0) never mixes in.
    #[test]
    fn linear_never_reads_outside_the_source_rectangle() -> Result<(), String> {
        let mut g = gpu()?;
        let items = [
            upload(0, 3, 1, greys(&[0, 128, 255])),
            put(0, (0, 0, 4, 1), (1, 0, 2, 1), true),
        ];
        // 128, 128 × 3/4 + 255 / 4 = 159.75, 128 / 4 + 255 × 3/4 = 223.25, 255.
        assert_eq!(reds(&draw_on(&mut g, &items, 4, 1)?), [128, 160, 223, 255]);
        Ok(())
    }

    /// Premultiplied source-over: half-alpha white over opaque black is grey, and
    /// over transparent black is itself.
    #[test]
    fn images_blend_source_over() -> Result<(), String> {
        let mut g = gpu()?;
        let half_white = vec![128, 128, 128, 128];
        let items = [
            upload(0, 1, 1, half_white),
            ExecItem::FillRect {
                x: 0,
                y: 0,
                width: 1,
                height: 1,
                colour: 0xff00_0000,
            },
            put(0, (0, 0, 1, 1), (0, 0, 1, 1), false),
            put(0, (1, 0, 1, 1), (0, 0, 1, 1), false),
        ];
        assert_eq!(
            draw_on(&mut g, &items, 2, 1)?,
            [128, 128, 128, 255, 128, 128, 128, 128]
        );
        Ok(())
    }

    /// An image drawn after it was freed, an upload of a live id, a draw of an id
    /// never uploaded, and a source outside the image, all break the validator's
    /// rules: refused before any backend call.
    #[test]
    fn broken_image_lists_are_refused_before_drawing() -> Result<(), String> {
        let mut g = gpu()?;
        let one = || upload(0, 1, 1, vec![1, 2, 3, 4]);
        let lists: [Vec<ExecItem>; 5] = [
            vec![put(0, (0, 0, 1, 1), (0, 0, 1, 1), false)],
            vec![one(), one()],
            vec![
                one(),
                ExecItem::FreeImage { id: 0 },
                put(0, (0, 0, 1, 1), (0, 0, 1, 1), false),
            ],
            vec![one(), put(0, (0, 0, 1, 1), (0, 0, 2, 1), false)],
            vec![ExecItem::FreeImage { id: 9 }],
        ];
        for list in &lists {
            let bytes = encode_list(list).ok_or("encode")?;
            let viewport = Viewport::new(2, 2).ok_or("viewport")?;
            assert_eq!(g.draw(&bytes, viewport), Err(Error::Refused), "{list:?}");
        }
        assert_eq!(g.backend().frames, 0);
        Ok(())
    }

    /// The image budget (`MAX_IMAGE_BYTES`, 2^28): one image over it is refused by
    /// the validator, before anything is allocated on the backend. 256 MiB of
    /// pixels and as many again encoded, so not under Miri.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn an_upload_past_the_budget_is_refused() -> Result<(), String> {
        let mut g = gpu()?;
        // 8192 × 8193 × 4 = 2^28 + 2^15 bytes.
        let items = [upload(0, 8192, 8193, vec![0; 8192 * 8193 * 4])];
        let bytes = encode_list(&items).ok_or("encode")?;
        let viewport = Viewport::new(2, 2).ok_or("viewport")?;
        assert_eq!(g.draw(&bytes, viewport), Err(Error::Refused));
        assert_eq!(g.backend().frames, 0);
        Ok(())
    }

    /// Ids are reused after a free, and the images of one list are there for the
    /// next.
    #[test]
    fn images_outlive_lists_and_ids_are_reused() -> Result<(), String> {
        let mut g = gpu()?;
        draw_on(&mut g, &[upload(3, 1, 1, vec![9, 9, 9, 255])], 2, 1)?;
        let again = [put(3, (0, 0, 2, 1), (0, 0, 1, 1), false)];
        assert_eq!(reds(&draw_on(&mut g, &again, 2, 1)?), [9, 9]);
        let swap = [
            ExecItem::FreeImage { id: 3 },
            upload(3, 1, 1, vec![50, 50, 50, 255]),
            put(3, (0, 0, 2, 1), (0, 0, 1, 1), false),
        ];
        assert_eq!(reds(&draw_on(&mut g, &swap, 2, 1)?), [50, 50]);
        Ok(())
    }

    /// A draw under a clip is cut to it, and one that misses its clip adds no row to
    /// the table the shaders read.
    #[test]
    fn a_clipped_draw_is_cut_and_a_missed_one_adds_nothing() -> Result<(), String> {
        use crate::atlas::Atlas;
        use crate::batch::build_with;
        use crate::images::Images;

        let items = [
            upload(0, 1, 1, vec![255, 0, 0, 255]),
            ExecItem::PushClip {
                x: 2,
                y: 0,
                width: 2,
                height: 1,
            },
            put(0, (0, 0, 8, 1), (0, 0, 1, 1), false),
            put(0, (6, 0, 2, 1), (0, 0, 1, 1), false),
            ExecItem::PopClip,
        ];
        let viewport = Viewport::new(8, 1).ok_or("viewport")?;
        let frame = build_with(&items, viewport, &mut Atlas::new(), &mut Images::new())
            .map_err(|e| e.to_string())?;
        assert_eq!(frame.image_draws.len(), 1);
        assert_eq!(frame.quads.len(), 1);
        let mut g = gpu()?;
        let px = draw_on(&mut g, &items, 8, 1)?;
        assert_eq!(reds(&px), [0, 0, 255, 255, 0, 0, 0, 0]);
        Ok(())
    }

    /// The reference's pixels for the image scenes, stored (`tests/pixels-reference/
    /// <scene>-<list>.rgba`, RGBA8, rows from the top): a change to the filter or the
    /// blending shows as a diff in them. They were written by the reference itself
    /// (`CLAZEL_GPU_BLESS=1`), so they pin it, and are no evidence that it is right:
    /// the hand-worked tests above are.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn the_references_image_pixels_are_stored() -> Result<(), String> {
        use crate::reference::{self, Masks};
        use crate::scenes;

        let dir =
            std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/pixels-reference");
        let bless = std::env::var_os("CLAZEL_GPU_BLESS").is_some();
        let mut failures = Vec::new();
        for scene in scenes::all().iter().filter(|s| s.name.starts_with("image")) {
            let viewport = Viewport::new(scene.width, scene.height).ok_or("viewport")?;
            let mut masks = Masks::default();
            for (n, list) in scene.lists.iter().enumerate() {
                let want = reference::draw(list, viewport, &mut masks).ok_or("reference")?;
                let path = dir.join(format!("{}-{n}.rgba", scene.name));
                if bless {
                    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
                    std::fs::write(&path, &want).map_err(|e| e.to_string())?;
                } else {
                    match std::fs::read(&path) {
                        Ok(saved) if saved == want => {}
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
}
