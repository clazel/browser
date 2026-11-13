//! Column widths: CSS Tables 3 §3.9.3's distribution of the assignable
//! width among columns (automatic layout), CSS 2.1 §17.5.2.1's fixed
//! layout, and the running share every proportional distribution uses
//! (phase-5.md item 5.15).
//!
//! Sources: CSS Tables 3 (csswg-drafts `e13fe879`) §3.9.3
//! `#width-distribution-algorithm`, §3.9.3.1
//! `#width-distribution-in-fixed-mode`, §3.9.3.2
//! `#distributing-width-to-columns`; CSS 2.1 §17.5.2.1.
//!
//! Modelling choices (with `mod.rs`'s):
//!
//! - **Shares are exact** ([`share_step`], `state.rs`): a length shared "in
//!   proportion to" weights, or a "linear combination" of two guesses, is
//!   given out as the differences of `floor(total · seen / weights)`, so the
//!   pieces add up to the total (§3.9.2's Rule 3) and each is within one
//!   1/64 px of its exact value. Shares "by equal amounts" are shares with
//!   every weight 1.
//! - **The sizing guesses' percentages** are of the assignable width,
//!   rounded down to 1/64 px.

use super::measure::Column;
use super::state::{HUNDRED, Share};

impl Share {
    /// A share of `total` among weights adding up to `weights` (requires
    /// `total >= 0` and `weights > 0`, `state.rs`).
    pub fn new(total: i64, weights: i64) -> Share {
        Share {
            total,
            weights,
            seen: 0,
            given: 0,
        }
    }
}

/// The next piece of share `s`, for weight `w` (`state.rs`'s contract).
pub fn share_step(s: Share, w: i64) -> (i64, Share) {
    let seen = s.seen.saturating_add(w).min(s.weights).max(s.seen);
    let product = i128::from(s.total).saturating_mul(i128::from(seen));
    let floor = product
        .checked_div_euclid(i128::from(s.weights))
        .unwrap_or(0);
    let given = i64::try_from(floor).unwrap_or(s.given);
    let piece = given.saturating_sub(s.given).max(0);
    (
        piece,
        Share {
            seen,
            given: s.given.saturating_add(piece),
            ..s
        },
    )
}

/// `total` (at least zero) shared among `weights` (each at least zero) in
/// proportion to them, or equally if they are all zero; the pieces add up
/// to `total` whenever there is a weight.
pub fn share(total: i64, weights: &[i64]) -> Vec<i64> {
    let total = total.max(0);
    let positive = weights
        .iter()
        .fold(0i64, |a, &w| a.saturating_add(w.max(0)));
    let ones: Vec<i64>;
    let (weights, sum) = if positive == 0 {
        ones = vec![1i64; weights.len()];
        (&ones[..], i64::try_from(ones.len()).unwrap_or(i64::MAX))
    } else {
        (weights, positive)
    };
    if sum == 0 {
        return Vec::new();
    }
    let mut s = Share::new(total, sum);
    let mut out = Vec::with_capacity(weights.len());
    for &w in weights {
        let (piece, next) = share_step(s, w.max(0));
        s = next;
        out.push(piece);
    }
    out
}

/// A length in 1/64 px from an `i64`, clamped to `i32`.
pub fn to_px(v: i64) -> i32 {
    i32::try_from(v).unwrap_or(if v < 0 { i32::MIN } else { i32::MAX })
}

/// `pct` (millionths of a percent) of `basis`, rounded down.
pub fn percent_of(pct: i64, basis: i32) -> i32 {
    let product = i128::from(pct).saturating_mul(i128::from(basis));
    let q = product.checked_div_euclid(i128::from(HUNDRED)).unwrap_or(0);
    i32::try_from(q).unwrap_or(if q < 0 { i32::MIN } else { i32::MAX })
}

/// What a column is to §3.9.3: "percent-column: a column whose any
/// constraint is defined to use a percentage only (with a value different
/// from 0%) - pixel-column: column whose any constraint is defined to use a
/// defined length only (and is not a percent-column) - auto-column: any
/// other column".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sizing {
    Percent,
    Pixel,
    Auto,
}

fn sizing(c: &Column) -> Sizing {
    if c.measure.pct > 0 {
        Sizing::Percent
    } else if c.constrained {
        Sizing::Pixel
    } else {
        Sizing::Auto
    }
}

/// CSS Tables 3 §3.9.3: the used widths of columns `cols` for an assignable
/// width `assignable` (automatic layout).
pub fn auto_widths(cols: &[Column], assignable: i32) -> Vec<i32> {
    let a = assignable.max(0);
    // A percent-column "is assigned the larger of: its intrinsic percentage
    // width times the assignable width and its min-content width".
    let pct = |c: &Column| percent_of(c.measure.pct, a).max(c.measure.min);
    // "The min-content sizing-guess is the set of column width assignments
    // where each column is assigned its min-content width."
    let g1: Vec<i32> = cols.iter().map(|c| c.measure.min).collect();
    // "The min-content-percentage sizing-guess": percent-columns as above,
    // "all other columns are assigned their min-content width".
    let g2: Vec<i32> = cols
        .iter()
        .map(|c| match sizing(c) {
            Sizing::Percent => pct(c),
            _ => c.measure.min,
        })
        .collect();
    // "The min-content-specified sizing-guess": percent-columns as above,
    // "any other column that is constrained is assigned its max-content
    // width", "all other columns are assigned their min-content width".
    let g3: Vec<i32> = cols
        .iter()
        .map(|c| match sizing(c) {
            Sizing::Percent => pct(c),
            Sizing::Pixel => c.measure.max,
            Sizing::Auto => c.measure.min,
        })
        .collect();
    // "The max-content sizing-guess": percent-columns as above, "all other
    // columns are assigned their max-content width".
    let g4: Vec<i32> = cols
        .iter()
        .map(|c| match sizing(c) {
            Sizing::Percent => pct(c),
            _ => c.measure.max,
        })
        .collect();
    let sum = |g: &[i32]| g.iter().fold(0i64, |s, &w| s.saturating_add(i64::from(w)));
    let guesses = [&g1, &g2, &g3, &g4];
    let a64 = i64::from(a);
    if a64 <= sum(&g1) {
        // The assignable width is never below the min-content guess
        // (§3.9.3's note); if it is (fixed borders wider than the table),
        // the columns keep their min-content widths and overflow.
        return g1;
    }
    // "If the assignable table width is less than or equal to the
    // max-content sizing-guess, the used widths of the columns must be the
    // linear combination (with weights adding to 1) of the two consecutive
    // sizing-guesses whose width sums bound the available width."
    for pair in guesses.windows(2) {
        let (Some(lo), Some(hi)) = (pair.first(), pair.get(1)) else {
            continue;
        };
        let (sl, sh) = (sum(lo), sum(hi));
        if sl <= a64 && a64 <= sh {
            let weights: Vec<i64> = lo
                .iter()
                .zip(hi.iter())
                .map(|(&l, &h)| i64::from(h).saturating_sub(i64::from(l)).max(0))
                .collect();
            let pieces = if sh == sl {
                vec![0; lo.len()]
            } else {
                share(a64.saturating_sub(sl), &weights)
            };
            return lo
                .iter()
                .zip(pieces)
                .map(|(&l, p)| l.saturating_add(to_px(p)))
                .collect();
        }
    }
    // "Otherwise, the used widths of the columns are the result of starting
    // from the max-content sizing-guess and distributing the excess width to
    // the columns of the table according to the rules for distributing
    // excess width to columns (for used width)."
    let excess = a64.saturating_sub(sum(&g4));
    let extra = excess_shares(cols, excess);
    g4.iter()
        .zip(extra)
        .map(|(&w, e)| w.saturating_add(to_px(e)))
        .collect()
}

/// §3.9.3.2's rules for distributing excess width to columns (automatic
/// layout): `excess` shared among the columns the first rule that applies
/// allows to grow.
pub fn excess_shares(cols: &[Column], excess: i64) -> Vec<i64> {
    let n = cols.len();
    let take = |allowed: &dyn Fn(&Column) -> bool, weight: &dyn Fn(&Column) -> i64| {
        let mask: Vec<bool> = cols.iter().map(allowed).collect();
        if !mask.iter().any(|&m| m) {
            return None;
        }
        let weights: Vec<i64> = cols
            .iter()
            .zip(&mask)
            .map(|(c, &m)| if m { weight(c) } else { 0 })
            .collect();
        // Shares by weight among the allowed columns; equal shares (weight
        // 1 each) when every weight is zero.
        let any = weights.iter().any(|&w| w > 0);
        let weights: Vec<i64> = if any {
            weights
        } else {
            mask.iter().map(|&m| i64::from(m)).collect()
        };
        Some(share(excess, &weights))
    };
    let free = |c: &Column| !c.constrained && c.originating && c.measure.pct == 0;
    let by_max = |c: &Column| i64::from(c.measure.max);
    let equal = |_: &Column| 0i64;
    // 1. "If there are non-constrained columns that have originating cells
    // with intrinsic percentage width of 0% and with nonzero max-content
    // width …, the distributed widths of the columns allowed to grow by this
    // rule are increased in proportion to max-content width".
    take(&|c| free(c) && c.measure.max > 0, &by_max)
        // 2. "Otherwise, if there are non-constrained columns that have
        // originating cells with intrinsic percentage width of 0% …
        // increased by equal amounts".
        .or_else(|| take(&free, &equal))
        // 3. "Otherwise, if there are constrained columns with intrinsic
        // percentage width of 0% and with nonzero max-content width …
        // increased in proportion to max-content width".
        .or_else(|| {
            take(
                &|c| c.constrained && c.measure.pct == 0 && c.measure.max > 0,
                &by_max,
            )
        })
        // 4. "Otherwise, if there are columns with intrinsic percentage width
        // greater than 0% … increased in proportion to intrinsic percentage
        // width".
        .or_else(|| take(&|c| c.measure.pct > 0, &|c| c.measure.pct))
        // 5. "Otherwise, if there is any such column, the distributed widths
        // of all columns that have originating cells are increased by equal
        // amounts".
        .or_else(|| take(&|c| c.originating, &equal))
        // 6. "Otherwise, the distributed widths of all columns are increased
        // by equal amounts".
        .or_else(|| take(&|_| true, &equal))
        .unwrap_or_else(|| vec![0; n])
}

/// A column's width as CSS 2.1 §17.5.2.1's fixed layout finds it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fixed {
    /// A length.
    Length(i32),
    /// A percentage of the assignable width (millionths of a percent).
    Percent(i64),
    /// Not set: one of the "remaining columns".
    Auto,
}

/// CSS 2.1 §17.5.2.1 with §3.9.3.1's changes: the used widths of columns
/// whose widths the column boxes and the first row give as `given`, for
/// an assignable width `assignable`.
pub fn fixed_widths(given: &[Fixed], assignable: i32) -> Vec<i32> {
    let a = i64::from(assignable.max(0));
    let lengths = given.iter().fold(0i64, |s, g| match g {
        Fixed::Length(w) => s.saturating_add(i64::from((*w).max(0))),
        _ => s,
    });
    let pcts: Vec<i64> = given
        .iter()
        .map(|g| match g {
            Fixed::Percent(p) => (*p).max(0),
            _ => 0,
        })
        .collect();
    let resolved: Vec<i64> = pcts
        .iter()
        .map(|&p| i64::from(percent_of(p, assignable.max(0))))
        .collect();
    let pct_sum = resolved.iter().fold(0i64, |s, &v| s.saturating_add(v));
    // §3.9.3.1: "If, when percentages are resolved based on the assignable
    // table width, the sum of columns widths based on this resolution would
    // exceed the assignable table width, they are instead to be resolved
    // relative to their percentage value such that the sum of columns width
    // meets the assignable table width exactly."
    let room = a.saturating_sub(lengths).max(0);
    let resolved = if pct_sum > room {
        share(room, &pcts)
    } else {
        resolved
    };
    let mut widths: Vec<i64> = given
        .iter()
        .zip(&resolved)
        .map(|(g, &r)| match g {
            Fixed::Length(w) => i64::from((*w).max(0)),
            Fixed::Percent(_) => r,
            Fixed::Auto => 0,
        })
        .collect();
    let set = widths.iter().fold(0i64, |s, &w| s.saturating_add(w));
    let rest = a.saturating_sub(set).max(0);
    // 3. "Any remaining columns equally divide the remaining horizontal
    // table space (minus borders or cell spacing)."
    let auto: Vec<i64> = given
        .iter()
        .map(|g| i64::from(matches!(g, Fixed::Auto)))
        .collect();
    let extra = if auto.iter().any(|&m| m > 0) {
        share(rest, &auto)
    } else if rest > 0 {
        // "If the table is wider than the columns, the extra space should be
        // distributed over the columns", by §3.9.3.2's rules for fixed mode:
        // "otherwise, if there are columns with non-zero length widths from
        // the base assignment, the excess width is distributed
        // proportionally to width among those columns; otherwise, if there
        // are columns with non-zero percentage widths …, proportionally to
        // percentage width …; otherwise, the excess width is distributed
        // equally to the zero-sized columns".
        let by_length: Vec<i64> = given
            .iter()
            .map(|g| match g {
                Fixed::Length(w) => i64::from((*w).max(0)),
                _ => 0,
            })
            .collect();
        if by_length.iter().any(|&w| w > 0) {
            share(rest, &by_length)
        } else if pcts.iter().any(|&p| p > 0) {
            share(rest, &pcts)
        } else {
            let zero: Vec<i64> = widths.iter().map(|&w| i64::from(w == 0)).collect();
            share(rest, &zero)
        }
    } else {
        vec![0; given.len()]
    };
    for (w, e) in widths.iter_mut().zip(extra) {
        *w = w.saturating_add(e);
    }
    widths.into_iter().map(to_px).collect()
}
