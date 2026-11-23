//! The lists every backend is tested on: each list item, alone and together, small
//! enough for Miri. Each scene is a run of lists drawn one after another, so masks
//! carry from list to list as they do in the GPU process. The software reference
//! ([`crate::reference`]) gives the expected pixels of each list.

use clazel_displaylist::exec::ExecItem;

/// A named run of lists on one viewport.
#[derive(Debug, Clone)]
pub struct Scene {
    /// What it covers; also the stored pixels' file name.
    pub name: &'static str,
    /// Viewport width.
    pub width: u32,
    /// Viewport height.
    pub height: u32,
    /// The lists, drawn in order.
    pub lists: Vec<Vec<ExecItem>>,
}

fn fill(x: i32, y: i32, width: u32, height: u32, colour: u32) -> ExecItem {
    ExecItem::FillRect {
        x,
        y,
        width,
        height,
        colour,
    }
}

fn clip(x: i32, y: i32, width: u32, height: u32) -> ExecItem {
    ExecItem::PushClip {
        x,
        y,
        width,
        height,
    }
}

/// A mask whose coverage is a ramp, byte `i` being `37 × i mod 256`: every value 0
/// to 255 appears in each 256 bytes. That sequence has period 256, so one period is
/// computed and repeated, which is a block copy: computing every byte of the
/// 2.3 MB scene "atlas" took over 350 s of Miri's clock in every test that lists
/// the scenes.
fn ramp(id: u32, columns: u16, rows: u16) -> ExecItem {
    let n = usize::from(columns).saturating_mul(usize::from(rows));
    let period: Vec<u8> = (0..256usize)
        .map(|i| u8::try_from(i.saturating_mul(37) % 256).unwrap_or(0))
        .collect();
    let mut coverage = period.repeat(n.div_ceil(256));
    coverage.truncate(n);
    ExecItem::UploadMask {
        id,
        columns,
        rows,
        coverage,
    }
}

fn draw(id: u32, x: i32, y: i32, colour: u32) -> ExecItem {
    ExecItem::DrawMask { id, x, y, colour }
}

/// An image of `width` × `height` whose red grows to the right, green downwards and
/// blue alternates by pixel, all scaled by `alpha` (premultiplied), so that a filter
/// has something to do on every row and column.
fn gradient(id: u32, width: u16, height: u16, alpha: u8) -> ExecItem {
    let axis = |v: u32, n: u32| {
        let top = n.saturating_sub(1).max(1);
        v.saturating_mul(255).checked_div(top).unwrap_or(0)
    };
    let premultiplied = |c: u32| {
        u8::try_from(
            c.saturating_mul(u32::from(alpha))
                .checked_div(255)
                .unwrap_or(0),
        )
        .unwrap_or(255)
    };
    let mut pixels = Vec::new();
    for y in 0..u32::from(height) {
        for x in 0..u32::from(width) {
            let blue = if x.saturating_add(y) & 1 == 0 { 255 } else { 0 };
            pixels.extend_from_slice(&[
                premultiplied(axis(x, width.into())),
                premultiplied(axis(y, height.into())),
                premultiplied(blue),
                alpha,
            ]);
        }
    }
    ExecItem::UploadImage {
        id,
        image_width: width,
        image_height: height,
        pixels,
    }
}

/// An image of `width` × `height` pixels from a byte ramp of period 251 (prime, so
/// every row differs) shifted by the id, like [`ramp`]: one period is computed and
/// repeated.
fn noise(id: u32, width: u16, height: u16) -> ExecItem {
    let n = usize::from(width)
        .saturating_mul(usize::from(height))
        .saturating_mul(4);
    let period: Vec<u8> = (0..251usize)
        .map(|i| {
            let seed = usize::try_from(id).unwrap_or(0).saturating_mul(61);
            u8::try_from(i.saturating_mul(37).saturating_add(13).saturating_add(seed) % 256)
                .unwrap_or(0)
        })
        .collect();
    // Sixteen periods first, so that the repeat that fills the image is 16 times
    // fewer copies (it runs under Miri, which counts copies).
    let block = period.repeat(16);
    let mut pixels = block.repeat(n.div_ceil(block.len()));
    pixels.truncate(n);
    ExecItem::UploadImage {
        id,
        image_width: width,
        image_height: height,
        pixels,
    }
}

/// A draw of the whole of an image of `iw` × `ih`, or of a source rectangle `src`
/// (x, y, width, height), into the destination `(x, y, width, height)`.
fn put(id: u32, dest: (i32, i32, u32, u32), src: (u16, u16, u16, u16), linear: bool) -> ExecItem {
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

/// Every scene.
pub fn all() -> Vec<Scene> {
    vec![
        Scene {
            name: "fill",
            width: 32,
            height: 24,
            lists: vec![vec![
                fill(0, 0, 32, 24, 0xffff_ffff),
                fill(3, 4, 10, 7, 0xff20_4060),
                // Partly off the target on every side.
                fill(-5, -5, 8, 8, 0xff00_80ff),
                fill(28, 20, 100, 100, 0xffff_0000),
                // Translucent, premultiplied: half-alpha green over both.
                fill(8, 6, 12, 10, 0x8000_8000),
                // A colour above its alpha clamps.
                fill(1, 18, 6, 4, 0x40ff_ffff),
                // Empty and wholly off-target fills draw nothing.
                fill(5, 5, 0, 9, 0xff00_0000),
                fill(40, 40, 4, 4, 0xff00_0000),
            ]],
        },
        Scene {
            name: "clips",
            width: 32,
            height: 24,
            lists: vec![vec![
                fill(0, 0, 32, 24, 0xff10_1010),
                clip(4, 4, 20, 14),
                fill(0, 0, 32, 24, 0xff80_0000),
                clip(10, -3, 30, 12),
                fill(0, 0, 32, 24, 0xc000_c000),
                // A clip disjoint from the one under it: nothing draws.
                clip(0, 20, 4, 4),
                fill(0, 0, 32, 24, 0xffff_ffff),
                ExecItem::PopClip,
                ExecItem::PopClip,
                fill(2, 2, 6, 6, 0xff00_00ff),
                ExecItem::PopClip,
                fill(26, 18, 6, 6, 0xffff_ff00),
            ]],
        },
        Scene {
            name: "masks",
            width: 40,
            height: 32,
            lists: vec![vec![
                fill(0, 0, 40, 32, 0xffff_ffff),
                ramp(0, 16, 16),
                ramp(7, 5, 9),
                draw(0, 2, 3, 0xff00_0000),
                draw(0, 20, 10, 0x8040_0000),
                // Off the left and the bottom edges.
                draw(7, -2, 26, 0xff00_00c0),
                // A mask under a clip, which cuts it.
                clip(30, 0, 6, 32),
                draw(0, 26, 0, 0xff00_8000),
                ExecItem::PopClip,
            ]],
        },
        Scene {
            name: "frames",
            width: 24,
            height: 16,
            lists: vec![
                vec![ramp(1, 8, 8), ramp(2, 4, 4), draw(1, 0, 0, 0xffff_0000)],
                // A mask from the frame before, then one freed and another
                // uploaded and drawn.
                vec![
                    draw(1, 4, 4, 0xff00_ff00),
                    ExecItem::FreeMask { id: 1 },
                    ramp(3, 6, 3),
                    draw(3, 12, 2, 0xff00_00ff),
                    draw(2, 18, 10, 0xffff_ffff),
                ],
                // Nothing at all: a cleared target.
                vec![],
            ],
        },
        Scene {
            name: "atlas",
            width: 32,
            height: 32,
            lists: vec![
                // Three 512 × 512 masks nearly fill the first 1 MiB store; the
                // fourth, after a free, forces a compaction in the middle of the
                // list, between two draws.
                vec![
                    ramp(0, 512, 512),
                    ramp(1, 512, 512),
                    ramp(2, 512, 512),
                    draw(0, -100, -100, 0xff00_0000),
                    ExecItem::FreeMask { id: 1 },
                    ramp(3, 512, 600),
                    draw(2, -300, -20, 0xff80_0000),
                    draw(3, -50, -250, 0x8000_0080),
                ],
            ],
        },
        Scene {
            name: "images",
            width: 48,
            height: 40,
            lists: vec![vec![
                fill(0, 0, 48, 40, 0xffe0_e0e0),
                gradient(0, 8, 8, 255),
                gradient(1, 4, 4, 128),
                gradient(3, 15, 15, 255),
                // One to one, nearest.
                put(0, (2, 2, 8, 8), (0, 0, 8, 8), false),
                // Three times larger, nearest: each source pixel is a 3 × 3 block.
                put(0, (12, 2, 24, 24), (0, 0, 8, 8), false),
                // Twice larger, linear, over the one before.
                put(0, (2, 12, 16, 16), (0, 0, 8, 8), true),
                // Smaller (15 to 6; odd sides, so no pixel centre lies on a source
                // edge), with each filter.
                put(3, (38, 2, 6, 6), (0, 0, 15, 15), false),
                put(3, (38, 10, 6, 6), (0, 0, 15, 15), true),
                // A source rectangle, linear: the filter clamps to it.
                put(0, (2, 30, 8, 8), (2, 2, 4, 4), true),
                // A translucent image over a fill, linear and nearest.
                fill(26, 30, 12, 8, 0xff20_60c0),
                put(1, (26, 30, 12, 8), (0, 0, 4, 4), true),
                put(1, (40, 30, 4, 4), (0, 0, 4, 4), false),
                // At the edges: off the top left, off the bottom right, scaled off
                // the top right.
                put(0, (-3, -3, 8, 8), (0, 0, 8, 8), false),
                put(0, (44, 36, 8, 8), (0, 0, 8, 8), true),
                put(0, (40, -6, 16, 16), (0, 0, 8, 8), false),
                // Under a clip, which cuts it.
                clip(14, 28, 6, 10),
                put(0, (10, 26, 16, 16), (0, 0, 8, 8), true),
                ExecItem::PopClip,
                // Empty destination, empty source and wholly off the target draw
                // nothing.
                put(0, (5, 5, 0, 4), (0, 0, 8, 8), false),
                put(0, (5, 5, 4, 4), (0, 0, 0, 4), true),
                put(0, (100, 100, 8, 8), (0, 0, 8, 8), false),
            ]],
        },
        Scene {
            name: "image-frames",
            width: 24,
            height: 16,
            lists: vec![
                vec![
                    gradient(1, 8, 8, 255),
                    put(1, (0, 0, 8, 8), (0, 0, 8, 8), false),
                ],
                // An image from the list before, then it is freed, its id uploaded
                // again with other pixels and drawn, beside another.
                vec![
                    put(1, (8, 0, 16, 8), (0, 0, 8, 8), true),
                    ExecItem::FreeImage { id: 1 },
                    gradient(1, 4, 4, 255),
                    put(1, (0, 8, 8, 8), (0, 0, 4, 4), false),
                    gradient(2, 2, 2, 200),
                    put(2, (16, 8, 8, 8), (0, 0, 2, 2), true),
                ],
                // Nothing at all: a cleared target; the images stay.
                vec![],
                vec![put(2, (0, 0, 6, 6), (0, 0, 2, 2), false)],
            ],
        },
        Scene {
            name: "image-store",
            width: 32,
            height: 32,
            lists: vec![
                // Four 256 × 256 images (256 KiB each) fill the first 1 MiB store
                // exactly; the fifth, after a free, forces a compaction in the middle
                // of the list, between two draws.
                vec![
                    noise(0, 256, 256),
                    noise(1, 256, 256),
                    noise(2, 256, 256),
                    noise(3, 256, 256),
                    put(0, (0, 0, 16, 16), (0, 0, 255, 255), false),
                    ExecItem::FreeImage { id: 1 },
                    noise(4, 256, 256),
                    put(2, (16, 0, 16, 16), (0, 0, 255, 255), false),
                    put(3, (0, 16, 16, 16), (1, 1, 255, 255), true),
                    put(4, (16, 16, 16, 16), (0, 0, 255, 255), true),
                ],
            ],
        },
    ]
}
