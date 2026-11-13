//! Used lengths from computed ones (phase-5.md item 5.14): percentages
//! resolved against their basis, numbers multiplied out, all in 1/64 px
//! with saturating arithmetic.
//!
//! Source: CSS 2.1 §8.3 and §8.4 (margins and padding: "percentages: refer
//! to width of containing block"), §10.2, §10.4, §10.5 and §10.7 (sizes and
//! their percentages), §10.8.1 (`line-height`: "<number>: the used value of
//! the property is this number multiplied by the element's font size").
//!
//! Modelling choices:
//!
//! - **Rounding**: a percentage of a length, or a number times a length, is
//!   rounded half away from zero to 1/64 px and clamped to `i32`, as
//!   `clazel-style`'s `percentage_px64` does for computed values.
//! - **A negative containing block width** (an over-wide border and padding
//!   can make one) is used as it is for margins and padding; §10.4's "If
//!   the containing block's width is negative, the used value is zero" is
//!   applied to `min-width` and `max-width` only, where it is written.

use clazel_style::cascade::computed::{Lp, MaxSize, Size};
use clazel_style::values::number::{Num, SCALE, percentage_px64};

/// `v` resolved against `basis` (CSS 2.1's "percentages refer to …").
pub fn lp(v: Lp, basis: i32) -> i32 {
    match v {
        Lp::Px64(x) => x,
        Lp::Percent(p) => percentage_px64(p, basis),
    }
}

/// `v` if it is a length, or a percentage with a basis; `None` for a
/// percentage without one (§10.5: "If the height of the containing block is
/// not specified explicitly … the value computes to 'auto'").
pub fn lp_opt(v: Lp, basis: Option<i32>) -> Option<i32> {
    match v {
        Lp::Px64(x) => Some(x),
        Lp::Percent(p) => basis.map(|b| percentage_px64(p, b)),
    }
}

/// `auto` as `None`, any other size resolved against `basis`.
pub fn size(v: Size, basis: i32) -> Option<i32> {
    match v {
        Size::Auto => None,
        Size::Lp(x) => Some(lp(x, basis)),
    }
}

/// `auto`, or a percentage without a basis, as `None`.
pub fn size_opt(v: Size, basis: Option<i32>) -> Option<i32> {
    match v {
        Size::Auto => None,
        Size::Lp(x) => lp_opt(x, basis),
    }
}

/// `none`, or a percentage without a basis, as `None`.
pub fn max_size_opt(v: MaxSize, basis: Option<i32>) -> Option<i32> {
    match v {
        MaxSize::None => None,
        MaxSize::Lp(x) => lp_opt(x, basis),
    }
}

/// `n` times `px` (a `<number>` times a length), rounded half away from
/// zero and clamped to `i32`.
pub fn times(n: Num, px: i32) -> i32 {
    let product = i128::from(n.millionths).saturating_mul(i128::from(px));
    let scale = i128::from(SCALE);
    let half = scale.checked_div(2).unwrap_or(0);
    let rounded = if product >= 0 {
        product.saturating_add(half)
    } else {
        product.saturating_sub(half)
    };
    let q = rounded.checked_div(scale).unwrap_or(0);
    i32::try_from(q).unwrap_or(if q < 0 { i32::MIN } else { i32::MAX })
}

/// Half of `v`, rounded down (towards negative infinity).
pub fn half_down(v: i32) -> i32 {
    v.div_euclid(2)
}

/// The rest of `v` after [`half_down`]: the two always add up to `v`.
pub fn half_up(v: i32) -> i32 {
    v.saturating_sub(half_down(v))
}

/// The larger of `a` and zero.
pub fn non_negative(a: i32) -> i32 {
    a.max(0)
}
