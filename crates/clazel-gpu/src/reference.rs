//! The software reference: the pixels a list means, computed straight from the
//! items, sharing nothing with the batching, the atlas or the fake backend but the
//! blending rule ([`crate::soft::blend_pixel`]) and [`Rect`]. Every backend is
//! tested against it.
//!
//! It walks the items in order with its own clip stack and its own table of masks,
//! and paints each covered pixel at once: a fill pixel by pixel of the target, a
//! mask pixel by pixel of the mask. It assumes nothing of the list and returns
//! `None` for one it cannot read (an unbalanced clip, an unknown mask, an edge out
//! of range), so a test fails rather than panics.

use std::collections::BTreeMap;

use clazel_displaylist::exec::ExecItem;

use crate::geom::{Rect, Viewport};
use crate::soft::blend_pixel;

/// A mask the reference knows: width, height and coverage.
type Known = (i32, i32, Vec<u8>);

/// The masks a list leaves for the next one, by id.
#[derive(Debug, Default, Clone)]
pub struct Masks(BTreeMap<u32, Known>);

/// The RGBA8 pixels, rows from the top, of `items` drawn into a fresh `viewport`
/// with `masks` from earlier lists, which it updates.
pub fn draw(items: &[ExecItem], viewport: Viewport, masks: &mut Masks) -> Option<Vec<u8>> {
    let mut pixels = vec![0u8; viewport.bytes()];
    let width = i32::try_from(viewport.width).ok()?;
    let height = i32::try_from(viewport.height).ok()?;
    let mut clips: Vec<Rect> = Vec::new();
    // Paint one pixel, if it is on the target and inside every clip.
    let paint = |pixels: &mut Vec<u8>, clips: &[Rect], px: i32, py: i32, colour: u32, k: u8| {
        if px < 0 || py < 0 || px >= width || py >= height {
            return Some(());
        }
        if !clips.iter().all(|c| c.contains(px, py)) {
            return Some(());
        }
        let at = usize::try_from(py.checked_mul(width)?.checked_add(px)?.checked_mul(4)?).ok()?;
        blend_pixel(pixels.get_mut(at..at.checked_add(4)?)?, colour, k);
        Some(())
    };
    for item in items {
        match item {
            ExecItem::FillRect {
                x,
                y,
                width: w,
                height: h,
                colour,
            } => {
                let r = Rect::at(*x, *y, *w, *h)?;
                // Only the part on the target is walked; the rest paints nothing.
                for py in r.y0.max(0)..r.y1.min(height) {
                    for px in r.x0.max(0)..r.x1.min(width) {
                        paint(&mut pixels, &clips, px, py, *colour, 255)?;
                    }
                }
            }
            ExecItem::PushClip {
                x,
                y,
                width: w,
                height: h,
            } => clips.push(Rect::at(*x, *y, *w, *h)?),
            ExecItem::PopClip => {
                clips.pop()?;
            }
            ExecItem::UploadMask {
                id,
                columns,
                rows,
                coverage,
            } => {
                if masks.0.contains_key(id) {
                    return None;
                }
                masks
                    .0
                    .insert(*id, ((*columns).into(), (*rows).into(), coverage.clone()));
            }
            ExecItem::DrawMask { id, x, y, colour } => {
                let (columns, rows, coverage) = masks.0.get(id)?;
                // Only the mask's rows and columns on the target are walked.
                let (j0, j1) = (y.checked_neg()?.max(0), height.checked_sub(*y)?.min(*rows));
                let (i0, i1) = (
                    x.checked_neg()?.max(0),
                    width.checked_sub(*x)?.min(*columns),
                );
                for j in j0..j1 {
                    for i in i0..i1 {
                        let k = *coverage
                            .get(usize::try_from(j.checked_mul(*columns)?.checked_add(i)?).ok()?)?;
                        paint(
                            &mut pixels,
                            &clips,
                            x.checked_add(i)?,
                            y.checked_add(j)?,
                            *colour,
                            k,
                        )?;
                    }
                }
            }
            ExecItem::FreeMask { id } => {
                masks.0.remove(id)?;
            }
        }
    }
    clips.is_empty().then_some(pixels)
}
