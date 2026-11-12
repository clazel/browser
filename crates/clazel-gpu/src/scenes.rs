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

/// A mask whose coverage is a ramp: every value 0 to 255 appears for 16 × 16.
fn ramp(id: u32, columns: u16, rows: u16) -> ExecItem {
    let n = usize::from(columns).saturating_mul(usize::from(rows));
    let coverage = (0..n)
        .map(|i| u8::try_from(i.saturating_mul(37) % 256).unwrap_or(0))
        .collect();
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
    ]
}
