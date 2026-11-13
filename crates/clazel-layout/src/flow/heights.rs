//! Heights (CSS 2.1 §10.5 to §10.7), the used `line-height` (§10.8.1), and
//! the Quirks Mode Standard's height quirks (§3.5 to §3.7) (phase-5.md item
//! 5.14).
//!
//! Sources: CSS 2.1 (W3C Recommendation, 7 June 2011), §10.5 "Content
//! height", §10.6 "Calculating heights and margins", §10.7 "Minimum and
//! maximum heights", §10.8.1 "Leading and half-leading",
//! <https://www.w3.org/TR/2011/REC-CSS2-20110607/visudet.html>; the Quirks
//! Mode Standard (commit `5a06deb5`), §3.5, §3.6 and §3.7,
//! <https://quirks.spec.whatwg.org/#the-percentage-height-calculation-quirk>.
//!
//! Modelling choices:
//!
//! - **The percentage basis for a box's children** ([`child_basis`]): its
//!   content height when its `height` is "specified explicitly" (§10.5: a
//!   length, or a percentage of a basis that exists), else none, so a
//!   child's percentage `height` computes to `auto` and its percentage
//!   `min-height` and `max-height` are 0 and `none` (§10.7). In quirks mode
//!   §3.5 looks past an ancestor whose `height` is `auto`: such a block
//!   container passes its own basis on, except a table cell (§3.5 step 2,
//!   "return a UA-defined value": none here, so `auto`, as in no-quirks
//!   mode) and a table wrapper box (step 4). The initial containing block's
//!   basis is the viewport's height (§10.5: "A percentage height on the root
//!   element is relative to the initial containing block").
//! - **§3.6 and §3.7's "normal border box size"** is the height this module
//!   gives without the quirk; the `body`'s parent's content box is the
//!   `html` element's as §3.6 makes it at least (the viewport's height less
//!   its margins, borders and padding) when that quirk applies to it, since
//!   the `html` element's final height depends on the `body`'s.

use clazel_style::cascade::computed::{ComputedStyle, LineHeight};

use super::fonts::FontMetrics;
use super::length::{half_down, half_up, times};

/// CSS 2.1 §10.7: the used height from the tentative one (`tentative`:
/// the computed `height`, or the content height for `auto`), "1. The
/// tentative used height is calculated (without 'min-height' and
/// 'max-height') … 2. If this tentative height is greater than
/// 'max-height', the rules above are applied again, but this time using the
/// value of 'max-height' as the computed value for 'height'. 3. If the
/// resulting height is smaller than 'min-height', the rules above are
/// applied again, but this time using the value of 'min-height' as the
/// computed value for 'height'." Applying the rules again to a given height
/// gives that height, so step 2 gives `max` and step 3 `min`.
pub fn min_max(tentative: i32, min: i32, max: Option<i32>) -> i32 {
    let h = max.map_or(tentative, |m| tentative.min(m));
    h.max(min).max(0)
}

/// The basis of the percentage heights of a box's children (see the
/// module's modelling choices): the box's content height `definite` when
/// its `height` is specified explicitly; else, in quirks mode, for a box
/// §3.5's walk goes past (`passes_on`: a block container that is neither a
/// table cell nor a table wrapper box), its own basis `inherited`.
pub fn child_basis(
    definite: Option<i32>,
    quirks: bool,
    passes_on: bool,
    inherited: Option<i32>,
) -> Option<i32> {
    // §3.5 step 3: "If element has a computed value of the height property
    // that is not auto, then return element."
    definite.or(if quirks && passes_on {
        // Step 5: "Jump to the first step" with the next ancestor.
        inherited
    } else {
        None
    })
}

/// The Quirks Mode Standard's §3.6 and §3.7 algorithm: "Let margins be the
/// sum of the used values of the margin-top and margin-bottom properties
/// … Let size be the size of [the initial containing block / body's parent
/// element's content box] in the block flow direction minus margins. Return
/// the bigger value of size and the normal border box size the element
/// would have according to the CSS specification."
pub fn quirk_fill(normal_border: i32, available: i32, margins: i32) -> i32 {
    available.saturating_sub(margins).max(normal_border)
}

/// The used `line-height` of an element with style `style` and first
/// available font metrics `m` (§10.8.1): `normal` is the font's ascent,
/// descent and line gap (`fonts.rs`), a `<number>` "multiplied by the
/// element's font size", a length as it is.
pub fn line_height(style: &ComputedStyle, m: &FontMetrics) -> i32 {
    match style.line_height {
        LineHeight::Normal => m
            .ascent
            .saturating_add(m.descent)
            .saturating_add(m.line_gap),
        LineHeight::Number(n) => times(n, style.font_size),
        LineHeight::Px64(x) => x,
    }
}

/// §10.8.1, the step `state.rs` states: a box with font height `a` above the
/// baseline, depth `d` below it and line height `line_height` reaches
/// `A' = A + L/2` above its baseline and `D' = D + L/2` below, where
/// `L = 'line-height' - AD` ("L may be negative"). The two halves are
/// rounded so that they add up to `L`: the half above down, the half below
/// up.
pub fn half_leading(a: i32, d: i32, line_height: i32) -> (i32, i32) {
    let l = line_height.saturating_sub(a.saturating_add(d));
    (a.saturating_add(half_down(l)), d.saturating_add(half_up(l)))
}
