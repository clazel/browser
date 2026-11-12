//! CSS Text 3 §4.1.2, Phase II: trimming and positioning at a line's
//! start and end, hanging, and tab stops; §5's choice of where lines wrap;
//! and the min-content and max-content sizes §5.1 and §5.4 affect.
//!
//! Source: CSS Text Module Level 3, W3C Candidate Recommendation Draft,
//! 14 August 2026, <https://www.w3.org/TR/2026/CRD-css-text-3-20260814/>,
//! §4.1.2 "Phase II: Trimming and Positioning" (phase-5.md says §4.2 from
//! memory; §4.2 in the pinned text is `tab-size`), §4.2 "Tab Character
//! Size", §5 "Line Breaking and Word Boundaries" and §5.4. Phase II's steps
//! are a bulleted list in the text; they are numbered here in their order
//! (step 1, leading collapsible spaces; step 2, tabs; step 3, trailing
//! collapsible spaces; step 4, hanging).
//!
//! Modelling choices:
//!
//! - **Lengths are 26.6 fixed point** in `i32` (as `shape::place`), given
//!   by the caller per unit through a `width` function that also receives
//!   the pen position from the line's start, for tabs. Sums saturate.
//! - **Phase II's removals and hanging are reported**, not performed: a
//!   [`Trim`] says which units of a line are removed and which hang;
//!   drawing and alignment (item 5.14) use it. A forced break unit (a
//!   preserved segment break, a BK or NL character) ends its line and is
//!   never content.
//! - **A trailing sequence of mixed `white-space`**: each unit hangs or is
//!   removed by its own style; the sequence hangs conditionally only if
//!   every hanging unit is `pre-wrap` and a forced break follows. A forced
//!   break includes the end of the block (§5: a line broken "due to the
//!   start or end of a block … is a forced line break").
//! - **pre-wrap's optional visual collapse** ("It may also visually collapse
//!   the character advance widths of any that would otherwise overflow") is
//!   not done.
//! - **Choosing breaks** ([`break_lines`]) is first fit: each line takes as
//!   much content as fits, breaking at the last soft wrap opportunity that
//!   keeps the content within the available width ("the UA must minimize
//!   the amount of content overflowing a line by wrapping the line at a soft
//!   wrap opportunity, if one exists"); with none, at the last
//!   `overflow-wrap` opportunity that fits; with neither, the line overflows
//!   up to the next opportunity of either kind. Content that hangs, or that
//!   Phase II removes, is not measured for fit ("characters that
//!   conditionally hang are not considered when measuring the line's
//!   contents for fit"). Opportunities are not prioritized (§5.5 leaves
//!   that to the UA).
//! - **Steps.** [`break_lines`] runs [`fit_step`] along the units over a
//!   [`FitState`] (`state.rs`), and [`Measure::add`] is the measuring both
//!   it and the intrinsic sizes use, so their Kani harnesses cover lines and
//!   texts of every length. [`trim`] walks back from a line's end and is
//!   checked on bounded inputs only.
//! - **`tab-size` is not in the subset**: its initial value is 8, "a
//!   multiple of the advance width of the space character (U+0020)"; the
//!   caller gives the space's advance ([`initial_tab_size`]).

use super::collapse::{Kind, Unit, collapsible};
use super::state::{Fit, FitState, Measure};
use super::wrap::Wrap;
use clazel_style::cascade::computed::WhiteSpace;

/// What Phase II does at a line's ends: units `start..hang` are the
/// line's content, `hang..end` hang, and the rest of the line (from the
/// line's own start to `start`, and from `end` to its end) is removed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Trim {
    /// The first unit drawn.
    pub start: usize,
    /// The first unit that hangs (equal to `end` if none does).
    pub hang: usize,
    /// One past the last unit that is drawn (content or hanging).
    pub end: usize,
    /// Whether the hanging units hang only conditionally (`pre-wrap`
    /// before a forced break): they hang only where they would overflow.
    pub conditional: bool,
}

/// Step 3: "A sequence of collapsible spaces at the end of a line is
/// removed, as well as any trailing U+1680 OGHAM SPACE MARK whose
/// white-space property is normal, nowrap, or pre-line."
fn removed_at_end(u: &Unit) -> bool {
    u.kind == Kind::CollapsibleSpace || (u.ch == '\u{1680}' && collapsible(u.style.white_space))
}

/// Step 4: "If there remains any sequence of white space, other space
/// separators, and/or preserved tabs at the end of a line": with
/// `white-space` normal, nowrap, pre-line or pre-wrap, the UA hangs it.
/// (`break-spaces` makes them "the same as other visible characters"; `pre`
/// is not listed, and does not wrap.)
fn hangs(u: &Unit) -> bool {
    matches!(
        u.kind,
        Kind::CollapsibleSpace | Kind::PreservedSpace | Kind::PreservedTab | Kind::OtherSpace
    ) && matches!(
        u.style.white_space,
        WhiteSpace::Normal | WhiteSpace::Nowrap | WhiteSpace::PreLine | WhiteSpace::PreWrap
    )
}

/// Whether a unit at the end of a line is not measured for fit: it is
/// removed (step 3), it hangs (step 4), or it is the forced break itself.
fn trailing(u: &Unit) -> bool {
    removed_at_end(u) || hangs(u) || u.kind == Kind::ForcedBreak
}

/// Phase II at the ends of the line made of `units[start..end]`, which
/// ends in a forced break if `forced` (§4.1.2).
pub fn trim(units: &[Unit], start: usize, end: usize, forced: bool) -> Trim {
    let end = end.min(units.len());
    let kind = |k: usize| units.get(k).map(|u| u.kind);
    // Step 1: "A sequence of collapsible spaces at the beginning of a line
    // is removed."
    let mut s = start.min(end);
    while s < end && kind(s) == Some(Kind::CollapsibleSpace) {
        s = s.saturating_add(1);
    }
    // The forced break that ends the line is not content.
    let mut e = end;
    if forced && e > s && kind(e.saturating_sub(1)) == Some(Kind::ForcedBreak) {
        e = e.saturating_sub(1);
    }
    // Step 3, trailing removal.
    while e > s && units.get(e.saturating_sub(1)).is_some_and(removed_at_end) {
        e = e.saturating_sub(1);
    }
    // Step 4: hanging. "If white-space is set to pre-wrap, the UA must
    // (unconditionally) hang this sequence, unless the sequence is followed
    // by a forced line break, in which case it must conditionally hang the
    // sequence instead."
    let mut h = e;
    let mut all_pre_wrap = true;
    while h > s
        && let Some(u) = units.get(h.saturating_sub(1))
        && hangs(u)
    {
        all_pre_wrap &= u.style.white_space == WhiteSpace::PreWrap;
        h = h.saturating_sub(1);
    }
    let conditional = forced && h < e && all_pre_wrap;
    Trim {
        start: s,
        hang: h,
        end: e,
        conditional,
    }
}

/// §4.2: `tab-size`'s initial value, 8 spaces, for a space advance of
/// `space` (26.6).
pub fn initial_tab_size(space: i32) -> i32 {
    space.saturating_mul(8)
}

/// Step 2: a preserved tab's advance at pen position `pen` from the start
/// of the line's block container (26.6). "If the tab size is zero,
/// preserved tabs are not rendered. Otherwise, each preserved tab is
/// rendered as a horizontal shift that lines up the start edge of the next
/// glyph with the next tab stop. If this distance is less than 0.5ch, then
/// the subsequent tab stop is used instead. Tab stops occur at points that
/// are multiples of the tab size from the starting content edge". A
/// negative tab size (not allowed by §4.2's grammar) is not rendered either.
pub fn tab_advance(pen: i32, tab_size: i32, half_ch: i32) -> i32 {
    if tab_size <= 0 {
        return 0;
    }
    // The next stop is `tab_size - (pen mod tab_size)` away, in
    // `1..=tab_size` (the remainder is in `0..tab_size` for any pen).
    let mut distance = i64::from(tab_size).saturating_sub(i64::from(pen.rem_euclid(tab_size)));
    if distance < i64::from(half_ch) {
        distance = distance.saturating_add(i64::from(tab_size));
    }
    i32::try_from(distance.max(0)).unwrap_or(i32::MAX)
}

/// One line chosen by [`break_lines`]: units `start..end`, of which the
/// last is followed by a forced break if `forced`, and the content's width
/// as measured for fit (26.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Line {
    /// The first unit.
    pub start: usize,
    /// One past the last unit.
    pub end: usize,
    /// Whether the line ends in a forced break.
    pub forced: bool,
    /// The width of its content, without what Phase II removes or hangs.
    pub width: i32,
}

impl Measure {
    /// The line with unit `u` added, whose advance is `advance` (26.6, the
    /// caller's `width` at this pen; not read when [`Measure::takes_width`]
    /// is false): leading collapsible spaces (Phase II step 1) and forced
    /// breaks take no width, and the width for fit stops before what Phase
    /// II removes or hangs at the end ([`trailing`]).
    pub fn add(self, u: &Unit, advance: i32) -> Measure {
        if !self.takes_width(u) {
            return self;
        }
        let pen = self.pen.saturating_add(advance);
        Measure {
            pen,
            fit: if trailing(u) { self.fit } else { pen },
            leading: false,
        }
    }
}

/// §5: the lines of `units`, given the opportunity after each unit
/// (`wraps`, from `super::wrap::opportunities`; a missing one counts as
/// forced), the available width and each unit's advance (26.6). See the
/// modelling choices for the rule. Every line holds at least one unit, and
/// the lines cover `units` in order. [`fit_step`] along the units.
pub fn break_lines(
    units: &[Unit],
    wraps: &[Wrap],
    available: i32,
    mut width: impl FnMut(usize, i32) -> i32,
) -> Vec<Line> {
    let n = units.len();
    let mut lines = Vec::new();
    let mut state = FitState::new(0);
    let mut i = 0;
    while state.start < n {
        let Some(u) = units.get(i) else {
            // Only when `wraps` does not end in a forced break.
            lines.push(Line {
                start: state.start,
                end: n,
                forced: true,
                width: state.m.fit,
            });
            break;
        };
        let advance = if state.m.takes_width(u) {
            width(i, state.m.pen)
        } else {
            0
        };
        let wrap = wraps.get(i).copied().unwrap_or(Wrap::Forced);
        match fit_step(&state, i, u, advance, wrap, available) {
            Fit::Continue(next) => {
                state = next;
                i = i.saturating_add(1);
            }
            Fit::End { end, forced, width } => {
                lines.push(Line {
                    start: state.start,
                    end,
                    forced,
                    width,
                });
                state = FitState::new(end);
                i = end;
            }
        }
    }
    lines
}

/// One step of choosing lines (§5, modelling choices): unit `i` (`u`, of
/// advance `advance`, followed by `wrap`) added to the line being filled
/// (`state`, which must satisfy [`FitState::invariant`] at `i`). The line
/// ends at the last soft opportunity that fits, else the last emergency one,
/// once its content no longer fits `available`; with neither, it overflows
/// to the next opportunity of either kind; a forced break always ends it.
pub fn fit_step(
    state: &FitState,
    i: usize,
    u: &Unit,
    advance: i32,
    wrap: Wrap,
    available: i32,
) -> Fit {
    let m = state.m.add(u, advance);
    let after = i.saturating_add(1);
    let mut next = FitState { m, ..*state };
    if m.fit > available && !next.overflowed {
        // The content so far does not fit: wrap at the last soft
        // opportunity, else the last emergency one.
        if let Some((end, width)) = next.soft.or(next.emergency) {
            return Fit::End {
                end,
                forced: false,
                width,
            };
        }
        next.overflowed = true;
    }
    let end = |forced: bool| Fit::End {
        end: after,
        forced,
        width: m.fit,
    };
    match wrap {
        Wrap::Forced => return end(true),
        Wrap::Soft | Wrap::Emergency { .. } if next.overflowed => return end(false),
        Wrap::Soft => next.soft = Some((after, m.fit)),
        Wrap::Emergency { .. } => next.emergency = Some((after, m.fit)),
        Wrap::None => {}
    }
    Fit::Continue(next)
}

/// The widest of the pieces `units` is cut into after every unit where
/// `cut` holds, each measured for fit as a line (26.6).
fn widest(
    units: &[Unit],
    wraps: &[Wrap],
    cut: impl Fn(Wrap) -> bool,
    mut width: impl FnMut(usize, i32) -> i32,
) -> i32 {
    let mut widest = 0;
    let mut m = Measure::START;
    for (i, u) in units.iter().enumerate() {
        let advance = if m.takes_width(u) { width(i, m.pen) } else { 0 };
        m = m.add(u, advance);
        if cut(wraps.get(i).copied().unwrap_or(Wrap::Forced)) {
            widest = widest.max(m.fit);
            m = Measure::START;
        }
    }
    widest.max(m.fit)
}

/// The min-content inline size: the widest piece between opportunities,
/// "taking all soft wrap opportunities" (CSS Sizing 3), with `overflow-wrap:
/// anywhere`'s (§5.4: "Soft wrap opportunities introduced by anywhere are
/// considered when calculating min-content intrinsic sizes") and not
/// `break-word`'s ("are not considered").
pub fn min_content(units: &[Unit], wraps: &[Wrap], width: impl FnMut(usize, i32) -> i32) -> i32 {
    widest(
        units,
        wraps,
        |w| {
            matches!(
                w,
                Wrap::Soft | Wrap::Forced | Wrap::Emergency { min_content: true }
            )
        },
        width,
    )
}

/// The max-content inline size: the widest line when wrapping only at
/// forced breaks.
pub fn max_content(units: &[Unit], wraps: &[Wrap], width: impl FnMut(usize, i32) -> i32) -> i32 {
    widest(units, wraps, |w| w == Wrap::Forced, width)
}
