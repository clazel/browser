//! Widths and horizontal margins (CSS 2.1 §10.3, §10.4) and HTML's "align
//! descendants": the steps whose contracts `state.rs` states, and the
//! intrinsic sizes of replaced elements.
//!
//! Source: CSS 2.1 (W3C Recommendation, 7 June 2011), §10.3 "Calculating
//! widths and margins",
//! <https://www.w3.org/TR/2011/REC-CSS2-20110607/visudet.html#Computing_widths_and_margins>:
//! §10.3.1 inline non-replaced, §10.3.2 inline replaced, §10.3.3
//! block-level non-replaced, §10.3.4 block-level replaced, §10.3.5's
//! shrink-to-fit width, §10.3.9 and §10.3.10 inline blocks; §10.4
//! "Minimum and maximum widths". §10.3.3's rules are paragraphs, numbered
//! here 1 to 5 in their order in the text; §10.4's algorithm is numbered
//! in the text. HTML at commit `4c54fae1`, §15.2 "align descendants"
//! (`#align-descendants`).
//!
//! Modelling choices:
//!
//! - **`direction` is `ltr`** in this phase, so rule 2 always gives the
//!   equality's slack to `margin-right`.
//! - **A width that would be negative is zero.** Rule 4 makes `width`
//!   "follow from the resulting equality", which is negative when the
//!   margins, borders and padding alone are wider than the containing
//!   block; a negative `width` is not a value CSS allows ("Negative values
//!   for 'width' are illegal", §10.2), so the width is zero and the box is
//!   then over-constrained: `margin-right` follows from the equality, as
//!   rule 2 does.
//! - **Align descendants** (HTML §15.2): "align only those descendants that
//!   have both their 'margin-inline-start' and 'margin-inline-end'
//!   properties computing to a value other than 'auto', that are
//!   over-constrained and that have one of those two margins with a used
//!   value forced to a greater value, and that do not themselves have an
//!   applicable align attribute … by having the used values of their
//!   margins on the line-left and line-right sides be set accordingly".
//!   "Accordingly" is read as `auto` margins would place the border box:
//!   centring shares the two margins' sum equally (the odd 1/64 px going
//!   right, as rule 5 here), right-aligning gives all of it to
//!   `margin-left`, and left-aligning keeps what rule 2 gave.
//! - **Shrink-to-fit**: §10.3.5's formula, with item 5.12's min-content and
//!   max-content sizes (`intrinsic.rs`) as the "preferred minimum width" and
//!   the "preferred width", which CSS 2.1 does not define exactly.
//! - **Replaced elements' intrinsic sizes** (item 5.13's `Replaced`): an
//!   `img` has natural size 0 by 0 and no ratio (HTML §15.4.2, "represents
//!   nothing"), so §10.3.2's first rule gives 0; an `iframe` has none, so
//!   the 300px rule and §10.6.2's 150px rule give CSS's default object size;
//!   an `input` and a `textarea` have the sizes HTML §15.5.6 and §15.5.17
//!   give, converted with their font (`block.rs`).

use super::state::{Align, UsedWidths, WidthInput};

/// §10.3.3's equality solved for one unknown: `total` minus the others.
fn rest(total: i32, others: [i32; 3]) -> i32 {
    others.iter().fold(total, |acc, &x| acc.saturating_sub(x))
}

/// CSS 2.1 §10.3.3 for a block-level non-replaced box in normal flow (and
/// §10.3.4's margins for a replaced one, given its used width).
pub fn solve_block(input: WidthInput) -> UsedWidths {
    let cb = input.containing;
    let mut ml = input.margin_left;
    let mut mr = input.margin_right;
    // Rule 1: "If 'width' is not 'auto' and 'border-left-width' +
    // 'padding-left' + 'width' + 'padding-right' + 'border-right-width'
    // (plus any of 'margin-left' or 'margin-right' that are not 'auto') is
    // larger than the width of the containing block, then any 'auto' values
    // for 'margin-left' or 'margin-right' are, for the following rules,
    // treated as zero."
    if let Some(w) = input.width {
        let used = input
            .edges
            .saturating_add(w)
            .saturating_add(ml.unwrap_or(0))
            .saturating_add(mr.unwrap_or(0));
        if used > cb {
            ml = Some(ml.unwrap_or(0));
            mr = Some(mr.unwrap_or(0));
        }
    }
    let over_constrained = |ml: i32, w: i32, computed_mr: i32| {
        // Rule 2: "If all of the above have a computed value other than
        // 'auto', the values are said to be "over-constrained" … If the
        // 'direction' property of the containing block has the value 'ltr',
        // the specified value of 'margin-right' is ignored and the value is
        // calculated so as to make the equality true."
        let margin_right = rest(cb, [ml, input.edges, w]);
        UsedWidths {
            margin_left: ml,
            width: w,
            margin_right,
            forced_right: margin_right > computed_mr,
        }
    };
    match (ml, input.width, mr) {
        (Some(l), Some(w), Some(r)) => over_constrained(l, w.max(0), r),
        // Rule 3: "If there is exactly one value specified as 'auto', its
        // used value follows from the equality."
        (None, Some(w), Some(r)) => {
            let w = w.max(0);
            UsedWidths {
                margin_left: rest(cb, [input.edges, w, r]),
                width: w,
                margin_right: r,
                forced_right: false,
            }
        }
        (Some(l), Some(w), None) => {
            let w = w.max(0);
            UsedWidths {
                margin_left: l,
                width: w,
                margin_right: rest(cb, [l, input.edges, w]),
                forced_right: false,
            }
        }
        (Some(l), None, Some(r)) => {
            // Rule 3 for the width, which is never negative (see the
            // module's modelling choices).
            let w = rest(cb, [l, input.edges, r]);
            if w < 0 {
                over_constrained(l, 0, r)
            } else {
                UsedWidths {
                    margin_left: l,
                    width: w,
                    margin_right: r,
                    forced_right: false,
                }
            }
        }
        // Rule 4: "If 'width' is set to 'auto', any other 'auto' values
        // become '0' and 'width' follows from the resulting equality."
        (l, None, r) => {
            let l = l.unwrap_or(0);
            let r = r.unwrap_or(0);
            let w = rest(cb, [l, input.edges, r]);
            if w < 0 {
                over_constrained(l, 0, r)
            } else {
                UsedWidths {
                    margin_left: l,
                    width: w,
                    margin_right: r,
                    forced_right: false,
                }
            }
        }
        // Rule 5: "If both 'margin-left' and 'margin-right' are 'auto', their
        // used values are equal. This horizontally centers the element with
        // respect to the edges of the containing block." The odd 1/64 px
        // goes right.
        (None, Some(w), None) => {
            let w = w.max(0);
            let slack = rest(cb, [input.edges, w, 0]);
            let left = slack.div_euclid(2);
            UsedWidths {
                margin_left: left,
                width: w,
                margin_right: slack.saturating_sub(left),
                forced_right: false,
            }
        }
    }
}

/// HTML §15.2's "align descendants" applied to a box whose used widths are
/// `used` (see the module's modelling choices).
pub fn align(used: UsedWidths, to: Align) -> UsedWidths {
    if !used.forced_right {
        return used;
    }
    let total = used.margin_left.saturating_add(used.margin_right);
    match to {
        Align::Left => used,
        Align::Center => {
            // Both margins share what the border box leaves, as `auto`
            // margins would (rule 5), the odd 1/64 px going right.
            let margin_left = total.div_euclid(2);
            UsedWidths {
                margin_left,
                margin_right: total.saturating_sub(margin_left),
                ..used
            }
        }
        Align::Right => UsedWidths {
            margin_left: total,
            margin_right: 0,
            ..used
        },
    }
}

/// CSS 2.1 §10.4's steps 2 and 3: with tentative used width `tentative`,
/// the width to apply the rules again with, if any. "2. If the tentative
/// used width is greater than 'max-width', the rules above are applied
/// again, but this time using the computed value of 'max-width' as the
/// computed value for 'width'. 3. If the resulting width is smaller than
/// 'min-width', the rules above are applied again, but this time using the
/// value of 'min-width' as the computed value for 'width'." The result of
/// step 2 is taken to be `max` itself: §10.3.3's rules keep a width they
/// are given unless it is negative, and `max-width` is not.
pub fn min_max(tentative: i32, min: i32, max: Option<i32>) -> Option<i32> {
    let mut again = None;
    let mut width = tentative;
    if let Some(m) = max
        && width > m
    {
        again = Some(m);
        width = m;
    }
    if width < min {
        again = Some(min);
    }
    again
}

/// §10.3.5's shrink-to-fit width: "min(max(preferred minimum width,
/// available width), preferred width)".
pub fn shrink_to_fit(min: i32, max: i32, available: i32) -> i32 {
    min.max(available).min(max)
}
