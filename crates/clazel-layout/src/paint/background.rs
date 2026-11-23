//! Background image layers: the size, the position and the tiles of one layer (phase-6.md
//! item 6.11, decision 6.0(c)'s U2).
//!
//! Sources: CSS Backgrounds 3 (W3C Candidate Recommendation Draft,
//! <https://www.w3.org/TR/css-backgrounds-3/>), cited by its section numbers: §2.1
//! "Layering Multiple Background Images", §2.4 "Tiling Images: the background-repeat
//! property", §2.6 "Positioning Images: the background-position property", §2.7 "Painting
//! Area: the background-clip property", §2.8 "Positioning Area: the background-origin
//! property", §2.9 "Sizing Images: the background-size property", §2.11 "Backgrounds of
//! Special Elements". phase-6.md marks them †: the text was read in the CRD at that URL.
//!
//! Everything here is in 1/64 CSS px, in document coordinates, before snapping to device
//! pixels; `order.rs` snaps each tile's edges on its own, so that tiles that share an edge
//! in CSS pixels share it in device pixels.
//!
//! Modelling choices:
//!
//! - **A raster image has a natural size and so a natural ratio**; the "neither natural
//!   size" cases of §2.9 do not arise (an SVG image is a broken image, 6.0(c)'s S1). An
//!   image with a zero side paints nothing (§2.9: "If the background image's width or
//!   height resolves to zero, this causes the image not to be displayed").
//! - **`auto`** is §2.9's: "An auto value for one dimension is resolved by using the image's
//!   natural aspect ratio and the size of the other dimension"; both `auto` is the natural
//!   size.
//! - **`round`** is §2.9's second step and third ("If background-repeat is round for one
//!   dimension only and if background-size is auto for the other dimension, then ... that
//!   other dimension is scaled so that the original aspect ratio is restored"): `X' = W /
//!   round(W / X)`, `round()` returning "the nearest natural number (integer greater than
//!   zero)", halves up.
//! - **`space`** places `floor(area / tile)` copies when that is at least 2, the first
//!   and the last touching the edges of the positioning area, evenly spaced; the position
//!   of that axis is ignored; "unless there is not enough space for two copies of the image
//!   in this axis, in which case only one image is placed, and background-position
//!   determines its position in this axis" (§2.4). The spaced pattern, like `repeat`'s and
//!   `round`'s, continues across the painting area where it is larger than the positioning
//!   area (§2.4).
//! - **Percentage positions** are of "(width of background positioning area - width of
//!   background image)" (§2.6), so they can be negative.
//! - **Tiles are the ones that touch the painting area**, in rows from the top, each row
//!   from the left, at most [`MAX_TILES`] of them: past that bound the rest of the layer
//!   is not drawn (a 1 px image over a very large box would otherwise be millions of
//!   items; listed). The display list's own bound, 5.17a's 1,048,576 items per list, is
//!   5.20's, after culling.

use clazel_style::cascade::computed::{BgLayer, BgRepeat, BgSize, Lp};
use clazel_style::values::number::percentage_px64;

use crate::flow::fragment::Rect;
use crate::images::Dims;

/// The most tiles one layer yields (the module's modelling choices).
pub const MAX_TILES: usize = 1 << 14;

/// The tiles of one layer.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Tiles {
    /// The tiles that touch the painting area, each the image's size, row by row.
    pub rects: Vec<Rect>,
    /// More than [`MAX_TILES`] touched it, and the rest were not made.
    pub truncated: bool,
}

/// A computed `<length-percentage>` against `basis`.
fn resolve(v: Lp, basis: i64) -> i64 {
    match v {
        Lp::Px64(p) => i64::from(p),
        Lp::Percent(p) => i64::from(percentage_px64(
            p,
            i32::try_from(basis).unwrap_or(if basis < 0 { i32::MIN } else { i32::MAX }),
        )),
    }
}

/// `a * b / c` rounded to nearest (halves up), for `c > 0`.
fn mul_div(a: i64, b: i64, c: i64) -> i64 {
    let c = c.max(1);
    a.saturating_mul(b).saturating_add(c / 2).div_euclid(c)
}

/// §2.9: the size of the layer's image, in a positioning area of `area` (width, height),
/// given its natural size `n` and the layer's `background-size` and `background-repeat`;
/// `None` if either side is zero or less (nothing is displayed).
pub fn tile_size(layer: &BgLayer, n: Dims, area: (i64, i64)) -> Option<(i64, i64)> {
    let nat = (
        i64::from(n.width).saturating_mul(64),
        i64::from(n.height).saturating_mul(64),
    );
    if nat.0 <= 0 || nat.1 <= 0 {
        return None;
    }
    let (aw, ah) = area;
    let (mut w, mut h) = match layer.size {
        // "contain: Scale the image, while preserving its natural aspect ratio, to the
        // largest size such that both its width and its height can fit inside the
        // background positioning area." "cover: ... the smallest size such that both its
        // width and its height can completely cover the background positioning area."
        BgSize::Contain | BgSize::Cover => {
            let width_limits = aw.saturating_mul(nat.1) <= ah.saturating_mul(nat.0);
            let by_width = if layer.size == BgSize::Contain {
                width_limits
            } else {
                !width_limits
            };
            if by_width {
                (aw, mul_div(aw, nat.1, nat.0))
            } else {
                (mul_div(ah, nat.0, nat.1), ah)
            }
        }
        BgSize::Explicit([sw, sh]) => {
            match (sw.map(|l| resolve(l, aw)), sh.map(|l| resolve(l, ah))) {
                (Some(w), Some(h)) => (w, h),
                (Some(w), None) => (w, mul_div(w, nat.1, nat.0)),
                (None, Some(h)) => (mul_div(h, nat.0, nat.1), h),
                (None, None) => nat,
            }
        }
    };
    let auto = |i: usize| match layer.size {
        BgSize::Explicit(s) => s.get(i).copied().flatten().is_none(),
        _ => false,
    };
    let [rx, ry] = layer.repeat;
    // §2.9: "X' = W / round(W / X)", round() "the nearest natural number (integer
    // greater than zero)".
    let rounded = |len: i64, tile: i64| {
        if tile <= 0 {
            return tile;
        }
        let n = mul_div(len, 1, tile).max(1);
        len.checked_div(n).unwrap_or(tile)
    };
    if rx == BgRepeat::Round {
        w = rounded(aw, w);
        if ry != BgRepeat::Round && auto(1) {
            h = mul_div(w, nat.1, nat.0);
        }
    }
    if ry == BgRepeat::Round {
        h = rounded(ah, h);
        if rx != BgRepeat::Round && auto(0) {
            w = mul_div(h, nat.0, nat.1);
        }
    }
    (w > 0 && h > 0).then_some((w, h))
}

/// One axis' tile origins: `at(k) = base + floor(k * num / den)` for `k` in `first ..=
/// last`.
#[derive(Debug, Clone, Copy)]
struct Axis {
    base: i64,
    num: i64,
    den: i64,
    first: i64,
    last: i64,
}

impl Axis {
    fn at(&self, k: i64) -> i64 {
        self.base
            .saturating_add(k.saturating_mul(self.num).div_euclid(self.den.max(1)))
    }
}

/// §2.4, §2.6: the origins of the tiles of size `t` along one axis of a positioning area
/// starting at `area_start` and `area` long, for a painting area `paint` (start, end): with
/// `repeat`, and the position `pos`.
fn axis(repeat: BgRepeat, area_start: i64, area: i64, t: i64, pos: Lp, paint: (i64, i64)) -> Axis {
    let offset = resolve(pos, area.saturating_sub(t));
    let single = Axis {
        base: area_start.saturating_add(offset),
        num: 0,
        den: 1,
        first: 0,
        last: 0,
    };
    let (base, num, den) = match repeat {
        BgRepeat::NoRepeat => return single,
        BgRepeat::Repeat | BgRepeat::Round => (area_start.saturating_add(offset), t, 1),
        BgRepeat::Space => {
            let n = area.checked_div(t).unwrap_or(0);
            if n < 2 {
                return single;
            }
            (area_start, area.saturating_sub(t), n.saturating_sub(1))
        }
    };
    // The `k` whose tile `[at(k), at(k) + t)` may touch `paint`: widened by one each way,
    // the exact test is made on each tile.
    let first = paint
        .0
        .saturating_sub(t)
        .saturating_sub(base)
        .saturating_mul(den)
        .div_euclid(num.max(1))
        .saturating_sub(1);
    let last = paint
        .1
        .saturating_sub(base)
        .saturating_mul(den)
        .div_euclid(num.max(1))
        .saturating_add(1);
    Axis {
        base,
        num,
        den,
        first,
        last,
    }
}

/// The tiles of `layer`'s image (of natural size `natural`) positioned in `positioning` and
/// painted within `painting` (§2.4 to §2.9, the module's modelling choices).
pub fn tiles(layer: &BgLayer, natural: Dims, positioning: Rect, painting: Rect) -> Tiles {
    tiles_up_to(layer, natural, positioning, painting, MAX_TILES)
}

/// [`tiles`] with the bound on the tiles as a parameter (the tests use a small one under
/// Miri).
fn tiles_up_to(
    layer: &BgLayer,
    natural: Dims,
    positioning: Rect,
    painting: Rect,
    max: usize,
) -> Tiles {
    let area = (i64::from(positioning.width), i64::from(positioning.height));
    let Some((tw, th)) = tile_size(layer, natural, area) else {
        return Tiles::default();
    };
    let (px, py) = (
        (i64::from(painting.x), i64::from(painting.right())),
        (i64::from(painting.y), i64::from(painting.bottom())),
    );
    let xs = axis(
        layer.repeat[0],
        i64::from(positioning.x),
        area.0,
        tw,
        layer.position[0],
        px,
    );
    let ys = axis(
        layer.repeat[1],
        i64::from(positioning.y),
        area.1,
        th,
        layer.position[1],
        py,
    );
    let touches = |p: i64, t: i64, (lo, hi): (i64, i64)| p < hi && p.saturating_add(t) > lo;
    let clamp = |v: i64| i32::try_from(v).unwrap_or(if v < 0 { i32::MIN } else { i32::MAX });
    let mut out = Tiles::default();
    // An axis' range is at most two tiles wider than the tiles that touch the painting area
    // (`axis`), so the loops are bounded by the area's size over the tile's; the tile bound
    // stops them at `MAX_TILES` tiles.
    let mut ky = ys.first;
    while ky <= ys.last {
        let y = ys.at(ky);
        ky = ky.saturating_add(1);
        if !touches(y, th, py) {
            continue;
        }
        let mut kx = xs.first;
        while kx <= xs.last {
            let x = xs.at(kx);
            kx = kx.saturating_add(1);
            if !touches(x, tw, px) {
                continue;
            }
            if out.rects.len() >= max {
                out.truncated = true;
                return out;
            }
            out.rects.push(Rect {
                x: clamp(x),
                y: clamp(y),
                width: clamp(tw),
                height: clamp(th),
            });
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use clazel_style::cascade::computed::{BgBox, BgImage};
    use clazel_style::values::number::Num;

    fn px(v: i32) -> i32 {
        v.saturating_mul(64)
    }

    fn r(x: i32, y: i32, w: i32, h: i32) -> Rect {
        Rect {
            x: px(x),
            y: px(y),
            width: px(w),
            height: px(h),
        }
    }

    fn pct(v: i64) -> Lp {
        Lp::Percent(Num::from_int(v))
    }

    fn layer(repeat: [BgRepeat; 2], position: [Lp; 2], size: BgSize) -> BgLayer {
        BgLayer {
            image: BgImage::None,
            repeat,
            position,
            size,
            origin: BgBox::Padding,
            clip: BgBox::Border,
        }
    }

    const D: Dims = Dims {
        width: 10,
        height: 5,
    };
    const REPEAT: [BgRepeat; 2] = [BgRepeat::Repeat; 2];
    const NO: [BgRepeat; 2] = [BgRepeat::NoRepeat; 2];
    const TOP_LEFT: [Lp; 2] = [Lp::Px64(0), Lp::Px64(0)];
    const AUTO: BgSize = BgSize::Explicit([None, None]);

    fn area(w: i32, h: i32) -> (i64, i64) {
        (i64::from(px(w)), i64::from(px(h)))
    }

    #[test]
    fn sizes() {
        let a = area(100, 60);
        let s = |size| tile_size(&layer(NO, TOP_LEFT, size), D, a).map(|(w, h)| (w / 64, h / 64));
        // auto auto: the natural size.
        assert_eq!(s(AUTO), Some((10, 5)));
        // 50% auto: half the area's width, the height from the ratio (2:1).
        assert_eq!(s(BgSize::Explicit([Some(pct(50)), None])), Some((50, 25)));
        // auto 20px: the width from the ratio.
        assert_eq!(
            s(BgSize::Explicit([None, Some(Lp::Px64(px(20)))])),
            Some((40, 20))
        );
        // Both given: stretched.
        assert_eq!(
            s(BgSize::Explicit([
                Some(Lp::Px64(px(7))),
                Some(Lp::Px64(px(9)))
            ])),
            Some((7, 9))
        );
        // A 100 by 60 area and a 2:1 image: contain is limited by the width, cover by the
        // height.
        assert_eq!(s(BgSize::Contain), Some((100, 50)));
        assert_eq!(s(BgSize::Cover), Some((120, 60)));
        // A zero side shows nothing.
        assert_eq!(s(BgSize::Explicit([Some(Lp::Px64(0)), None])), None);
    }

    #[test]
    fn round_fits_a_whole_number_of_times() {
        // §2.9's example: 30% high, rounded: 100 / round(100 / 30) = 100 / 3; the width
        // 20% is not rounded.
        let l = layer(
            [BgRepeat::NoRepeat, BgRepeat::Round],
            TOP_LEFT,
            BgSize::Explicit([Some(pct(20)), Some(pct(30))]),
        );
        let (w, h) = tile_size(&l, D, area(100, 100)).unwrap_or((0, 0));
        assert_eq!(w, i64::from(px(20)));
        assert_eq!(h, i64::from(px(100) / 3));
        // Round in one dimension only, `auto` in the other: the ratio is restored (the
        // third step): 30 wide -> 100 / 3, and the height follows at 2:1.
        let l = layer(
            [BgRepeat::Round, BgRepeat::Repeat],
            TOP_LEFT,
            BgSize::Explicit([Some(Lp::Px64(px(30))), None]),
        );
        let (w, h) = tile_size(&l, D, area(100, 100)).unwrap_or((0, 0));
        assert_eq!(w, i64::from(px(100) / 3));
        assert_eq!(h, mul_div(w, 5, 10));
    }

    #[test]
    fn no_repeat_places_one_tile_by_position() {
        let a = r(10, 20, 100, 60);
        let at = |x: Lp, y: Lp| tiles(&layer(NO, [x, y], AUTO), D, a, a).rects;
        // 0% 0%: the top left corner of the image on the area's.
        assert_eq!(at(pct(0), pct(0)), vec![r(10, 20, 10, 5)]);
        // 100% 100%: the bottom right corners meet (§2.6).
        assert_eq!(at(pct(100), pct(100)), vec![r(100, 75, 10, 5)]);
        // 50% 50%: centred; (60 - 5) / 2 = 27.5 px down.
        assert_eq!(
            at(pct(50), pct(50)),
            vec![Rect {
                y: px(47) + 32,
                ..r(55, 0, 10, 5)
            }]
        );
        // Lengths are offsets from the top left.
        assert_eq!(at(Lp::Px64(px(3)), Lp::Px64(px(4))), vec![r(13, 24, 10, 5)]);
        // Outside the painting area: nothing.
        assert!(at(Lp::Px64(px(500)), Lp::Px64(0)).is_empty());
    }

    #[test]
    fn repeat_covers_the_painting_area_from_the_position() {
        // A 10 by 5 image repeating over 25 by 12 from the top left: 3 columns by 3 rows.
        let a = r(0, 0, 25, 12);
        let t = tiles(&layer(REPEAT, TOP_LEFT, AUTO), D, a, a);
        assert_eq!(t.rects.len(), 9);
        assert_eq!(t.rects.first(), Some(&r(0, 0, 10, 5)));
        assert_eq!(t.rects.get(2), Some(&r(20, 0, 10, 5)));
        assert_eq!(t.rects.get(8), Some(&r(20, 10, 10, 5)));
        // From 50% 0%: shifted by (25 - 10) / 2 = 7.5, so the pattern also covers the
        // left edge: tiles at -2.5, 7.5, 17.5.
        let t = tiles(&layer(REPEAT, [pct(50), Lp::Px64(0)], AUTO), D, a, a);
        let xs: Vec<i32> = t.rects.iter().take(3).map(|r| r.x).collect();
        assert_eq!(xs, vec![-160, 480, 1120]);
        // repeat-x: one row.
        let t = tiles(
            &layer([BgRepeat::Repeat, BgRepeat::NoRepeat], TOP_LEFT, AUTO),
            D,
            a,
            a,
        );
        assert_eq!(t.rects.len(), 3);
    }

    #[test]
    fn space_spreads_whole_tiles_between_the_edges() {
        // 35 wide, 10 wide tiles: 3 copies, gaps of (35 - 30) / 2 = 2.5; first at 0, last at
        // 25; the position (100%) is ignored.
        let a = r(0, 0, 35, 5);
        let sp = [BgRepeat::Space, BgRepeat::NoRepeat];
        let t = tiles(&layer(sp, [pct(100), Lp::Px64(0)], AUTO), D, a, a);
        let xs: Vec<i32> = t.rects.iter().map(|r| r.x).collect();
        assert_eq!(xs, vec![0, 800, 1600]);
        // Only one copy fits: it goes by the position, and is not repeated.
        let small = r(0, 0, 15, 5);
        let t = tiles(&layer(sp, [pct(100), Lp::Px64(0)], AUTO), D, small, small);
        assert_eq!(t.rects, vec![r(5, 0, 10, 5)]);
    }

    #[test]
    fn a_bound_on_tiles() {
        let big = r(0, 0, 100_000, 100_000);
        let one = Dims {
            width: 1,
            height: 1,
        };
        // Under Miri (CI measured 25,000 to 30,000 times slower than native debug) the bound is 64, not
        // 16,384: the same code path, 64 tiles, microseconds natively.
        let max = if cfg!(miri) { 64 } else { MAX_TILES };
        let t = tiles_up_to(&layer(REPEAT, TOP_LEFT, AUTO), one, big, big, max);
        assert_eq!(t.rects.len(), max);
        assert!(t.truncated);
    }

    #[test]
    fn a_larger_painting_area_continues_the_pattern() {
        // Positioned in a 20 by 10 box, painted over a 40 by 10 one that starts 10 earlier.
        let positioning = r(10, 0, 20, 10);
        let painting = r(0, 0, 40, 10);
        let t = tiles(
            &layer([BgRepeat::Repeat, BgRepeat::NoRepeat], TOP_LEFT, AUTO),
            D,
            positioning,
            painting,
        );
        let xs: Vec<i32> = t.rects.iter().map(|r| r.x / 64).collect();
        assert_eq!(xs, vec![0, 10, 20, 30]);
    }
}
