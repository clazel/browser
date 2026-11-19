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

/// An image the reference knows: width, height and premultiplied RGBA8 pixels.
type KnownImage = (i32, i32, Vec<u8>);

/// The masks and images a list leaves for the next one, by id (the two id spaces
/// are separate).
#[derive(Debug, Default, Clone)]
pub struct Masks(BTreeMap<u32, Known>, BTreeMap<u32, KnownImage>);

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
            ExecItem::UploadImage {
                id,
                image_width,
                image_height,
                pixels,
            } => {
                if masks.1.contains_key(id) {
                    return None;
                }
                let (w, h) = (i32::from(*image_width), i32::from(*image_height));
                if w.checked_mul(h)?.checked_mul(4)? != i32::try_from(pixels.len()).ok()? {
                    return None;
                }
                masks.1.insert(*id, (w, h, pixels.clone()));
            }
            ExecItem::DrawImage {
                id,
                x,
                y,
                width: w,
                height: h,
                src_x,
                src_y,
                src_width,
                src_height,
                linear,
            } => {
                let (image_w, image_h, data) = masks.1.get(id)?;
                let source = Source {
                    x: i32::from(*src_x),
                    y: i32::from(*src_y),
                    w: i32::from(*src_width),
                    h: i32::from(*src_height),
                };
                if source.x.checked_add(source.w)? > *image_w
                    || source.y.checked_add(source.h)? > *image_h
                {
                    return None;
                }
                let r = Rect::at(*x, *y, *w, *h)?;
                if source.w == 0 || source.h == 0 {
                    continue;
                }
                let (dest_w, dest_h) = (i32::try_from(*w).ok()?, i32::try_from(*h).ok()?);
                for py in r.y0.max(0)..r.y1.min(height) {
                    for px in r.x0.max(0)..r.x1.min(width) {
                        let (i, j) = (px.checked_sub(*x)?, py.checked_sub(*y)?);
                        let rgba =
                            filtered(data, *image_w, &source, (i, j, dest_w, dest_h), *linear)?;
                        let [red, green, blue, alpha] = rgba;
                        let colour = u32::from_be_bytes([alpha, red, green, blue]);
                        paint(&mut pixels, &clips, px, py, colour, 255)?;
                    }
                }
            }
            ExecItem::FreeImage { id } => {
                masks.1.remove(id)?;
            }
        }
    }
    clips.is_empty().then_some(pixels)
}

/// A draw's source rectangle in the image's pixels.
struct Source {
    x: i32,
    y: i32,
    w: i32,
    h: i32,
}

/// What [`along`] gives: the nearest source pixel, the two linear taps with their
/// weights, and the weights' denominator.
type Along = (i32, [(i32, i128); 2], i128);

/// Along one axis, for the destination pixel `i` of `n` and a source of `len` pixels
/// starting at `start`: the pixel the centre of `i` falls in (*nearest*), and the two
/// pixels around it less half a pixel (*linear*), clamped to the source, each with
/// its weight as a fraction of `2n`. The position of the centre inside the source is
/// `(2i + 1) · len / 2n`.
fn along(i: i32, n: i32, start: i32, len: i32) -> Option<Along> {
    let (i, n, len) = (i128::from(i), i128::from(n), i128::from(len));
    let two_n = n.checked_mul(2)?;
    let centre = i.checked_mul(2)?.checked_add(1)?.checked_mul(len)?;
    let nearest = centre.div_euclid(two_n);
    // The centre less half a pixel is `(centre - n) / 2n`: its floor `k`, and the
    // remainder over `2n` is the weight of pixel `k + 1`.
    let below = centre.checked_sub(n)?;
    let k = below.div_euclid(two_n);
    let frac = below.checked_sub(k.checked_mul(two_n)?)?;
    let clamp = |v: i128| -> Option<i32> {
        let v = v.clamp(0, len.checked_sub(1)?);
        i32::try_from(v.checked_add(i128::from(start))?).ok()
    };
    Some((
        i32::try_from(nearest.checked_add(i128::from(start))?).ok()?,
        [
            (clamp(k)?, two_n.checked_sub(frac)?),
            (clamp(k.checked_add(1)?)?, frac),
        ],
        two_n,
    ))
}

/// The premultiplied RGBA of destination pixel `(i, j)` of a `w × h` destination
/// (`dest`), from an image `image_w` wide, rounded once.
fn filtered(
    data: &[u8],
    image_w: i32,
    source: &Source,
    dest: (i32, i32, i32, i32),
    linear: bool,
) -> Option<[u8; 4]> {
    let (i, j, w, h) = dest;
    let (near_x, taps_x, den_x) = along(i, w, source.x, source.w)?;
    let (near_y, taps_y, den_y) = along(j, h, source.y, source.h)?;
    let fetch = |x: i32, y: i32| -> Option<[i128; 4]> {
        let at = usize::try_from(y.checked_mul(image_w)?.checked_add(x)?.checked_mul(4)?).ok()?;
        let px = data.get(at..at.checked_add(4)?)?;
        let mut out = [0i128; 4];
        for (slot, v) in out.iter_mut().zip(px) {
            *slot = i128::from(*v);
        }
        Some(out)
    };
    if !linear {
        let v = fetch(near_x, near_y)?;
        let mut out = [0u8; 4];
        for (slot, c) in out.iter_mut().zip(v) {
            *slot = u8::try_from(c).ok()?;
        }
        return Some(out);
    }
    // Sum of weight × value over the four taps, over `den_x × den_y`.
    let denominator = den_x.checked_mul(den_y)?;
    let mut sum = [0i128; 4];
    for (y, wy) in taps_y {
        for (x, wx) in taps_x {
            let v = fetch(x, y)?;
            let weight = wx.checked_mul(wy)?;
            for (acc, c) in sum.iter_mut().zip(v) {
                *acc = acc.checked_add(c.checked_mul(weight)?)?;
            }
        }
    }
    let mut out = [0u8; 4];
    for (slot, total) in out.iter_mut().zip(sum) {
        // Round half up: floor(total / denominator + 1/2).
        let doubled = total.checked_mul(2)?.checked_add(denominator)?;
        let value = doubled.div_euclid(denominator.checked_mul(2)?);
        *slot = u8::try_from(value.min(255)).ok()?;
    }
    Some(out)
}
