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
use crate::backend::{Backend, BackendError, Frame, Op};
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

/// The fake backend: a target and an atlas in memory.
#[derive(Debug, Default)]
pub struct SoftBackend {
    viewport: Option<Viewport>,
    target: Vec<u8>,
    atlas: Vec<u8>,
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
                        for py in area.y0..area.y1.max(area.y0) {
                            for px in area.x0..area.x1.max(area.x0) {
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
