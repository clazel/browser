//! White space and line breaking (phase-5.md item 5.12).
//!
//! # Sources
//!
//! - **CSS Text Module Level 3**, W3C Candidate Recommendation Draft,
//!   14 August 2026, <https://www.w3.org/TR/2026/CRD-css-text-3-20260814/>:
//!   §3 `white-space` (its six values; `break-spaces` too, since
//!   `clazel-style` parses it), §4 and §4.1 white space processing
//!   ([`collapse`]: §4.1.1 Phase I, §4.1.3 segment breaks; [`lines`]:
//!   §4.1.2 Phase II, §4.2 tab stops), §5 line breaking ([`wrap`]: §5.1
//!   `word-break`, §5.4 `overflow-wrap`, §5.5 details; [`lines`]: choosing
//!   where to wrap, min-content and max-content). phase-5.md's section
//!   numbers were written from memory (its † marks); the pinned text has
//!   Phase II at §4.1.2, `word-break` at §5.1 and `overflow-wrap` at §5.4,
//!   which is what the code cites. `text-transform` is not in the subset.
//! - **UAX #14**, "Unicode Line Breaking Algorithm", revision 57 (Unicode
//!   18.0.0), <https://www.unicode.org/reports/tr14/tr14-57.html>: LB1
//!   ([`classes`]) and the rules LB2 to LB31 ([`uax14`]), with the
//!   character data of Unicode 18.0.0 generated into [`data`] by `cargo
//!   xtask tables` from `crates/clazel-layout/data/unicode-18.0.0/`.
//!
//! # The pipeline
//!
//! An inline formatting context's content, as [`Item`]s (text with its
//! inline's [`TextStyle`], and atomic inlines), goes through:
//!
//! 1. [`collapse::collapse`], Phase I: the [`Unit`]s that remain;
//! 2. [`wrap::opportunities`]: the [`Wrap`] after each unit (none, soft,
//!    forced, or an `overflow-wrap` emergency one);
//! 3. [`lines::break_lines`] with the units' advances (item 5.11's shaper)
//!    and the available width: the [`lines::Line`]s; and [`lines::trim`]
//!    per line, Phase II.
//!
//! [`lines::min_content`] and [`lines::max_content`] give the intrinsic
//! sizes table layout (item 5.15) needs.
//!
//! # Modelling choices
//!
//! Each file lists its own; these are the ones that cross files.
//!
//! - **The property types are `clazel-style`'s** computed values
//!   (`WhiteSpace`, `WordBreak`, `OverflowWrap`), which item 5.7 defines;
//!   `clazel-style` does not depend on this crate, so there is no cycle.
//! - **CSS's tailorings of UAX #14** are in LB1's resolution
//!   (`Props::css`): SA letters as ID (§5.5: a soft wrap opportunity between
//!   letters of a script whose lexical analysis we cannot do: Thai, Lao,
//!   Khmer, Myanmar), control characters as AL (§4), and `word-break:
//!   break-all` (§5.1). The pair rules themselves are UAX #14's, unchanged,
//!   which `tests/conformance_linebreak.rs` checks against every line of
//!   `LineBreakTest.txt`; [`wrap`] then applies `white-space`, `keep-all`,
//!   `overflow-wrap` and §5.5's atomic inlines on top.
//! - **No bidi reordering** (UAX #9 is Phase 8): lines are in logical
//!   order, so "at the end of a line (after bidi reordering)" is the
//!   logical end.
//! - **Lengths** are 26.6 fixed point in `i32`, as in [`crate::shape`].

pub mod classes;
pub mod collapse;
pub mod data;
pub mod lines;
pub mod uax14;
pub mod wrap;

#[cfg(kani)]
mod proofs;
#[cfg(test)]
mod tests;

pub use classes::{Lb, Props};
pub use collapse::{Item, Kind, Unit};
pub use lines::{Line, Trim};
pub use uax14::{Break, Rule, breaks, breaks_with_rules};
pub use wrap::Wrap;

use clazel_style::cascade::computed::{OverflowWrap, WhiteSpace, WordBreak};

/// The computed values that white space processing and line breaking read
/// from an inline (CSS Text 3 §3, §5.1, §5.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct TextStyle {
    /// `white-space`.
    pub white_space: WhiteSpace,
    /// `word-break`.
    pub word_break: WordBreak,
    /// `overflow-wrap`.
    pub overflow_wrap: OverflowWrap,
}

impl TextStyle {
    /// The initial values: `normal` for all three.
    pub const INITIAL: TextStyle = TextStyle {
        white_space: WhiteSpace::Normal,
        word_break: WordBreak::Normal,
        overflow_wrap: OverflowWrap::Normal,
    };

    /// The initial values with `white-space` set.
    pub fn with_white_space(white_space: WhiteSpace) -> TextStyle {
        TextStyle {
            white_space,
            ..TextStyle::INITIAL
        }
    }
}
