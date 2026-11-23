//! The blending rule, and the fake backend: a [`Backend`] that runs a [`Frame`] in
//! software, with no foreign call, as the shaders would. Miri runs the batching
//! through it.
//!
//! # Modelling choices
//!
//! - **Source-over in 8-bit sRGB, premultiplied, with no gamma correction** (the
//!   plan's listed choice): stored values are blended as they are, as a GPU does
//!   with an `RGBA8Unorm` target that is not marked sRGB.
//! - **The exact result, rounded once** ([`blend`]): with colour channel `c` and
//!   alpha `a` (premultiplied, 0 to 255), coverage `k` (0 to 255) and the stored
//!   channel `d`, the stored result is `c·k/255 + d·(1 − a·k/255²)` in units of
//!   1/255, rounded to nearest (halves up) and clamped to 255. A GPU computes the
//!   same in floating point, often half precision, and rounds at the end, so it may
//!   differ by one level; the Metal tests measure that.
//! - **Colours have no rule** in the list, so a channel may exceed its alpha; the
//!   sum is then clamped at 255, as an unsigned normalized target does.

use crate::atlas::texel_index;
use crate::backend::{Backend, BackendError, Frame, IMAGE_COLUMNS, ImageDraw, Op};
use crate::blocklist::{Adapter, Api};
use crate::geom::Viewport;

/// One channel of premultiplied source-over: colour channel `c`, colour alpha `a`,
/// coverage `k`, stored value `d`, each 0 to 255.
pub fn blend(c: u8, a: u8, k: u8, d: u8) -> u8 {
    let (c, a, k, d) = (u32::from(c), u32::from(a), u32::from(k), u32::from(d));
    // 255² = 65,025. Each product is below 2^24, the sum below 2^25: no overflow.
    let src = c.saturating_mul(k).saturating_mul(255);
    let keep = 65_025u32.saturating_sub(a.saturating_mul(k));
    let sum = src
        .saturating_add(d.saturating_mul(keep))
        .saturating_add(32_512);
    u8::try_from((sum / 65_025).min(255)).unwrap_or(u8::MAX)
}

/// Blend a premultiplied `0xAARRGGBB` colour at coverage `k` over the RGBA8 pixel
/// at `px`.
pub fn blend_pixel(px: &mut [u8], colour: u32, k: u8) {
    let [a, r, g, b] = colour.to_be_bytes();
    for (slot, c) in px.iter_mut().zip([r, g, b, a]) {
        *slot = blend(c, a, k, *slot);
    }
}

/// The source pixel `(x, y)` of an image draw, premultiplied RGBA, read from the
/// image store. `None` if it lies outside the store or the image.
fn texel(store: &[u8], d: &ImageDraw, x: i64, y: i64) -> Option<[i128; 4]> {
    let (x, y) = (u64::try_from(x).ok()?, u64::try_from(y).ok()?);
    if x >= u64::from(d.image_width) || y >= u64::from(d.image_height) {
        return None;
    }
    let index = y
        .checked_mul(u64::from(d.image_width))?
        .checked_add(x)?
        .checked_mul(4)?
        .checked_add(u64::from(d.offset))?;
    let at = usize::try_from(index).ok()?;
    let px = store.get(at..at.checked_add(4)?)?;
    let mut out = [0i128; 4];
    for (slot, v) in out.iter_mut().zip(px) {
        *slot = i128::from(*v);
    }
    Some(out)
}

/// What [`axis`] gives: the nearest source pixel, the two linear taps with their
/// weights, and the weights' denominator.
type Axis = (i64, [(i64, i64); 2], i64);

/// One axis of the filter (`crate::backend`'s modelling choices): for the
/// destination pixel `i` of `w`, source start `s` and length `len`, the sample
/// position is `s + (2i + 1) · len / (2w)`. Returns the nearest source pixel, and for
/// linear the two pixels (clamped to the source) with their weights over `2w`.
fn axis(i: i64, w: i64, s: i64, len: i64) -> Option<Axis> {
    let den = w.checked_mul(2)?;
    let pos = i.checked_mul(2)?.checked_add(1)?.checked_mul(len)?;
    // Nearest: floor(pos / den) is below `len`, as `2i + 1 < 2w`.
    let near = s.checked_add(pos.div_euclid(den))?;
    // Linear: the position less a half is `(pos - w) / den`.
    let num = pos.checked_sub(w)?;
    let a = num.div_euclid(den);
    let r = num.rem_euclid(den);
    let last = s.checked_add(len)?.checked_sub(1)?;
    let at = |k: i64| s.checked_add(k).map(|v| v.clamp(s, last));
    let taps = [(at(a)?, den.checked_sub(r)?), (at(a.checked_add(1)?)?, r)];
    Some((near, taps, den))
}

/// The premultiplied RGBA of the destination pixel `(i, j)` of an image draw:
/// the exact filter, rounded once (halves up). `None` for an input no validated
/// list produces.
fn sample(store: &[u8], d: &ImageDraw, i: i64, j: i64) -> Option<[u8; 4]> {
    let (w, h) = (i64::from(d.width), i64::from(d.height));
    if i < 0 || j < 0 || i >= w || j >= h || w == 0 || h == 0 {
        return None;
    }
    let (sx, sy) = (i64::from(d.src_x), i64::from(d.src_y));
    let (sw, sh) = (i64::from(d.src_width), i64::from(d.src_height));
    let (near_x, taps_x, den_x) = axis(i, w, sx, sw)?;
    let (near_y, taps_y, den_y) = axis(j, h, sy, sh)?;
    if !d.linear {
        let t = texel(store, d, near_x, near_y)?;
        let mut out = [0u8; 4];
        for (slot, v) in out.iter_mut().zip(t) {
            *slot = u8::try_from(v).ok()?;
        }
        return Some(out);
    }
    let mut total = [0i128; 4];
    for (y, wy) in taps_y {
        for (x, wx) in taps_x {
            let t = texel(store, d, x, y)?;
            let weight = i128::from(wx).checked_mul(i128::from(wy))?;
            for (acc, v) in total.iter_mut().zip(t) {
                *acc = acc.checked_add(v.checked_mul(weight)?)?;
            }
        }
    }
    let scale = i128::from(den_x).checked_mul(i128::from(den_y))?;
    let mut out = [0u8; 4];
    for (slot, v) in out.iter_mut().zip(total) {
        let rounded = v
            .checked_mul(2)?
            .checked_add(scale)?
            .checked_div(scale.checked_mul(2)?)?;
        *slot = u8::try_from(rounded.min(255)).ok()?;
    }
    Some(out)
}

/// The fake backend: a target, an atlas and an image store in memory.
#[derive(Debug, Default)]
pub struct SoftBackend {
    viewport: Option<Viewport>,
    target: Vec<u8>,
    atlas: Vec<u8>,
    images: Vec<u8>,
    /// How many frames it drew, for tests.
    pub frames: usize,
    /// The adapter it reports, if not [`SOFT_ADAPTER`].
    adapter: Option<Adapter>,
}

/// The adapter the fake backend reports by default: a software driver, which the
/// blocklist never checks.
pub const SOFT_ADAPTER: Adapter = Adapter {
    api: Api::Vulkan,
    vendor: 0,
    device: 0,
    driver: None,
    software: true,
};

impl SoftBackend {
    /// A backend with no target yet.
    pub fn new() -> SoftBackend {
        SoftBackend::default()
    }

    /// A backend reporting `adapter`: a fake device for the blocklist's tests.
    pub fn with_adapter(adapter: Adapter) -> SoftBackend {
        SoftBackend {
            adapter: Some(adapter),
            ..SoftBackend::default()
        }
    }
}

fn fail(what: &'static str) -> BackendError {
    BackendError { what, code: 0 }
}

impl Backend for SoftBackend {
    fn draw_frame(&mut self, frame: &Frame) -> Result<(), BackendError> {
        let viewport = frame.viewport.ok_or(fail("no viewport"))?;
        self.viewport = Some(viewport);
        self.target.clear();
        self.target.resize(viewport.bytes(), 0);
        let width = usize::try_from(viewport.width).map_err(|_| fail("width"))?;
        for op in &frame.ops {
            match op {
                Op::Atlas { capacity } => {
                    let n = usize::try_from(*capacity).map_err(|_| fail("capacity"))?;
                    self.atlas = vec![0; n];
                }
                Op::Images { capacity } => {
                    let n = usize::try_from(*capacity).map_err(|_| fail("capacity"))?;
                    self.images = vec![0; n];
                }
                Op::ImageUpload { offset, pixels } => {
                    let at = usize::try_from(*offset).map_err(|_| fail("offset"))?;
                    let to = at.checked_add(pixels.len()).ok_or(fail("upload range"))?;
                    self.images
                        .get_mut(at..to)
                        .ok_or(fail("upload past the image store"))?
                        .copy_from_slice(pixels);
                }
                Op::Upload { offset, start, len } => {
                    let end = start.checked_add(*len).ok_or(fail("upload range"))?;
                    let src = frame.bytes.get(*start..end).ok_or(fail("upload bytes"))?;
                    let at = usize::try_from(*offset).map_err(|_| fail("offset"))?;
                    let to = at.checked_add(*len).ok_or(fail("upload range"))?;
                    self.atlas
                        .get_mut(at..to)
                        .ok_or(fail("upload past the atlas"))?
                        .copy_from_slice(src);
                }
                Op::Draw {
                    scissor,
                    first,
                    count,
                } => {
                    let first = usize::try_from(*first).map_err(|_| fail("first"))?;
                    let end = first
                        .checked_add(usize::try_from(*count).map_err(|_| fail("count"))?)
                        .ok_or(fail("count"))?;
                    let quads = frame.quads.get(first..end).ok_or(fail("quads"))?;
                    for q in quads {
                        let area = q.rect.intersect(*scissor);
                        let image = if q.columns == IMAGE_COLUMNS {
                            let index = usize::try_from(q.offset).map_err(|_| fail("offset"))?;
                            Some(frame.image_draws.get(index).ok_or(fail("image draw"))?)
                        } else {
                            None
                        };
                        for py in area.y0..area.y1.max(area.y0) {
                            for px in area.x0..area.x1.max(area.x0) {
                                if let Some(draw) = image {
                                    let i = i64::from(px)
                                        .checked_sub(i64::from(draw.x))
                                        .ok_or(fail("i"))?;
                                    let j = i64::from(py)
                                        .checked_sub(i64::from(draw.y))
                                        .ok_or(fail("j"))?;
                                    let [r, g, b, a] = sample(&self.images, draw, i, j)
                                        .ok_or(fail("image sample"))?;
                                    let x = usize::try_from(px).map_err(|_| fail("px"))?;
                                    let y = usize::try_from(py).map_err(|_| fail("py"))?;
                                    let at = y
                                        .checked_mul(width)
                                        .and_then(|row| row.checked_add(x))
                                        .and_then(|p| p.checked_mul(4))
                                        .ok_or(fail("pixel"))?;
                                    let end = at.checked_add(4).ok_or(fail("pixel"))?;
                                    let pixel =
                                        self.target.get_mut(at..end).ok_or(fail("pixel"))?;
                                    let colour = u32::from_be_bytes([a, r, g, b]);
                                    blend_pixel(pixel, colour, 255);
                                    continue;
                                }
                                let k = if q.columns == 0 {
                                    255
                                } else {
                                    // The shader's computation, in the same order.
                                    let i = px.checked_sub(q.origin_x).ok_or(fail("x"))?;
                                    let j = py.checked_sub(q.origin_y).ok_or(fail("y"))?;
                                    let index = texel_index(
                                        q.offset,
                                        q.columns,
                                        u32::try_from(i).map_err(|_| fail("i"))?,
                                        u32::try_from(j).map_err(|_| fail("j"))?,
                                    )
                                    .ok_or(fail("index"))?;
                                    let index =
                                        usize::try_from(index).map_err(|_| fail("index"))?;
                                    // The shaders read 0 past the end; so does this.
                                    self.atlas.get(index).copied().unwrap_or(0)
                                };
                                let x = usize::try_from(px).map_err(|_| fail("px"))?;
                                let y = usize::try_from(py).map_err(|_| fail("py"))?;
                                let at = y
                                    .checked_mul(width)
                                    .and_then(|r| r.checked_add(x))
                                    .and_then(|p| p.checked_mul(4))
                                    .ok_or(fail("pixel"))?;
                                let end = at.checked_add(4).ok_or(fail("pixel"))?;
                                let pixel = self.target.get_mut(at..end).ok_or(fail("pixel"))?;
                                blend_pixel(pixel, q.colour, k);
                            }
                        }
                    }
                }
            }
        }
        self.frames = self.frames.saturating_add(1);
        Ok(())
    }

    fn read_pixels(&mut self, out: &mut Vec<u8>) -> Result<(), BackendError> {
        out.clear();
        out.extend_from_slice(&self.target);
        Ok(())
    }

    fn adapter(&self) -> Adapter {
        self.adapter.unwrap_or(SOFT_ADAPTER)
    }
}

#[cfg(test)]
mod tests {
    use super::{blend, blend_pixel};

    #[test]
    fn blending_corners() {
        // Opaque full coverage replaces.
        assert_eq!(blend(17, 255, 255, 200), 17);
        // No coverage keeps.
        assert_eq!(blend(17, 255, 0, 200), 200);
        // Transparent black keeps.
        assert_eq!(blend(0, 0, 255, 99), 99);
        // Half alpha white over black: 128 (the colour itself).
        assert_eq!(blend(128, 128, 255, 0), 128);
        // A channel above its alpha clamps.
        assert_eq!(blend(255, 0, 255, 255), 255);
    }

    /// Every input of one channel: the result is the exact value rounded, never
    /// more than half a level off, and opaque full coverage gives the colour.
    /// 2^32 cases are too many for a test, so `c` and `a` take every value, `k` a
    /// spread of 16 and `d` every 15th. Under `cfg(miri)`, which is far slower, `c`
    /// and `a` take every 5th value and `k` and `d` 2 each: with every value of `c`
    /// and `a` it measured 290 s on Miri's clock, too near CI's 300 s per test.
    #[test]
    fn blending_is_the_exact_value_rounded() {
        let ks: &[u8] = if cfg!(miri) {
            &[128, 255]
        } else {
            &[
                0, 1, 2, 3, 17, 64, 100, 127, 128, 129, 200, 250, 253, 254, 255, 77,
            ]
        };
        let ds: Vec<u8> = if cfg!(miri) {
            vec![0, 200]
        } else {
            (0..=255).step_by(15).collect()
        };
        for &k in ks {
            let step = if cfg!(miri) { 5 } else { 1 };
            for a in (0..=255u8).step_by(step) {
                for c in (0..=255u8).step_by(step) {
                    for &d in &ds {
                        let exact = (f64::from(c) * f64::from(k) / 255.0
                            + f64::from(d) * (1.0 - f64::from(a) * f64::from(k) / 65_025.0))
                            .min(255.0);
                        let got = f64::from(blend(c, a, k, d));
                        assert!((got - exact).abs() <= 0.5 + 1e-9, "{c} {a} {k} {d}");
                    }
                }
            }
        }
    }

    #[test]
    fn a_pixel_is_rgba() {
        let mut px = [0u8; 4];
        blend_pixel(&mut px, 0xff10_2030, 255);
        assert_eq!(px, [0x10, 0x20, 0x30, 0xff]);
    }
}
