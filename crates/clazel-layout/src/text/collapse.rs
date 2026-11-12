//! CSS Text 3 §4.1.1, Phase I: collapsing and transformation, with §4.1.3's
//! segment break transformation and §4's handling of control characters.
//!
//! Source: CSS Text Module Level 3, W3C Candidate Recommendation Draft,
//! 14 August 2026, <https://www.w3.org/TR/2026/CRD-css-text-3-20260814/>,
//! §4 "White Space Processing & Control Characters", §4.1.1 "Phase I:
//! Collapsing and Transformation" and §4.1.3 "Segment Break Transformation
//! Rules". The phase's steps are a bulleted list in the text; they are
//! numbered here in their order (step 1 to step 4 under "normal, nowrap, or
//! pre-line", step 5 for "pre, pre-wrap, or break-spaces").
//!
//! Modelling choices:
//!
//! - **The input is one inline formatting context** as a list of
//!   [`Item`]s in document order: text, each with its computed style, and
//!   atomic inlines. Collapsing runs across item boundaries ("even one
//!   outside the boundary of the inline containing that space, provided both
//!   spaces are within the same inline formatting context"). Out-of-flow
//!   boxes are not items.
//! - **A segment break is a line feed** (U+000A): "each line feed (U+000A)
//!   … is treated as a segment break", as HTML's DOM gives them.
//! - **A carriage return becomes a space** (U+0020) before anything else:
//!   "Carriage returns (U+000D) are treated identically to spaces (U+0020) in
//!   all respects". Its [`Unit`] keeps its offset in the item.
//! - **Bidi formatting characters are skipped when looking for neighbours**
//!   ("ignoring bidi formatting characters (characters with the
//!   Bidi_Control property \[UAX9\]) as if they were not there"); they stay in
//!   the output. Bidi_Control is U+061C, U+200E, U+200F, U+202A to U+202E
//!   and U+2066 to U+2069 (PropList.txt; the set is stable).
//! - **"Collapsed to have zero advance width"**: such a space is removed. Its
//!   soft wrap opportunity is the one after the space it follows, at the
//!   same place on the line, except where the two spaces' boxes have
//!   different `white-space` (listed).
//! - **Segment break transformation (§4.1.3)**: the rules for keeping or
//!   removing a remaining segment break are "UA-defined in this level". We
//!   always transform it into a space, as HTML and CSS historically do (the
//!   section's last note); Chinese and Japanese text broken across source
//!   lines then gets spaces (listed).
//! - **One pass, one step per character.** The phase's steps are written
//!   in the text as passes over the whole content, and step 1 removes
//!   spaces *before* a segment break. [`step`] does all of them left to
//!   right over a [`CollapseState`] (`state.rs`): a collapsible space that a
//!   later segment break would remove stays *pending*, and the break
//!   retracts it ([`Emit::Retract`]). Within a run of spaces, tabs and bidi
//!   formatting characters, only the first collapsible space can be kept
//!   (step 4 removes the others), so one pending space is enough.
//!   `reference.rs` keeps the five-pass reading as the oracle.
//! - **Control characters** (Cc other than tab, line feed and carriage
//!   return) are kept as ordinary characters; §4's "visible glyph" is the
//!   shaper's (it draws `.notdef`), and their line breaking class is
//!   `Props::css`'s.

use super::TextStyle;
use super::classes::{Gc, Lb, general_category, line_break};
use super::state::{CollapseState, Emit, Last};
use clazel_style::cascade::computed::WhiteSpace;

/// One piece of an inline formatting context's content.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Item<'a> {
    /// A text node's text (or part of one) with its inline's style.
    Text {
        /// The text.
        text: &'a str,
        /// The computed style of the inline that contains it.
        style: TextStyle,
    },
    /// An atomic inline (an inline-block, a replaced element): one unit of
    /// content that is not text (CSS Text 3 §5.5).
    Atomic {
        /// The style of its parent inline, which governs breaking around it.
        style: TextStyle,
    },
}

/// What a unit of content is after Phase I.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Kind {
    /// Any other character.
    Char,
    /// A collapsible space (U+0020), from a space, a tab, a carriage return
    /// or a segment break.
    CollapsibleSpace,
    /// A preserved space (`pre`, `pre-wrap`, `break-spaces`).
    PreservedSpace,
    /// A preserved tab (`pre`, `pre-wrap`, `break-spaces`).
    PreservedTab,
    /// An "other space separator" (§4.1: General_Category Zs other than
    /// U+0020 and U+00A0).
    OtherSpace,
    /// A forced line break: a preserved segment break (U+000A), or a
    /// character of class BK or NL (§5.5).
    ForcedBreak,
    /// An atomic inline.
    Atomic,
}

/// One unit of content after Phase I: a character, or an atomic inline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Unit {
    /// The character as rendered (U+0020 for a collapsible space, U+FFFC for
    /// an atomic inline).
    pub ch: char,
    /// What it is.
    pub kind: Kind,
    /// The index of its [`Item`].
    pub item: usize,
    /// Its byte offset in the item's text (0 for an atomic inline).
    pub offset: usize,
    /// Its inline's style.
    pub style: TextStyle,
}

/// A character as read, before Phase I.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Raw {
    /// A space (U+0020), or a carriage return (§4).
    Space,
    /// A tab (U+0009).
    Tab,
    /// A segment break (U+000A).
    SegmentBreak,
    /// A bidi formatting character (Bidi_Control).
    Bidi,
    /// Anything else, with its kind after Phase I.
    Other(Kind),
}

/// Whether `c` has Bidi_Control (PropList.txt).
fn is_bidi_control(c: char) -> bool {
    matches!(
        c,
        '\u{061C}' | '\u{200E}' | '\u{200F}' | '\u{202A}'..='\u{202E}' | '\u{2066}'..='\u{2069}'
    )
}

/// How a character is read before Phase I.
pub fn classify(c: char) -> Raw {
    match c {
        // §4: "Carriage returns (U+000D) are treated identically to spaces".
        ' ' | '\r' => Raw::Space,
        '\t' => Raw::Tab,
        '\n' => Raw::SegmentBreak,
        c if is_bidi_control(c) => Raw::Bidi,
        // §5.5: "any Unicode character with the BK and NL line breaking
        // class, must be treated as forced line breaks".
        c if matches!(line_break(c), Lb::BK | Lb::NL) => Raw::Other(Kind::ForcedBreak),
        // §4.1: "all characters in the Unicode general category Zs except
        // space (U+0020) and no-break space (U+00A0)".
        c if c != '\u{00A0}' && general_category(c) == Some(Gc::Zs) => Raw::Other(Kind::OtherSpace),
        _ => Raw::Other(Kind::Char),
    }
}

/// §4.1.1: "If white-space is set to normal, nowrap, or pre-line, white
/// space characters are considered collapsible".
pub fn collapsible(ws: WhiteSpace) -> bool {
    matches!(
        ws,
        WhiteSpace::Normal | WhiteSpace::Nowrap | WhiteSpace::PreLine
    )
}

/// Phase I over an inline formatting context's items (§4.1.1, §4.1.3):
/// the units that remain, in order.
pub fn collapse(items: &[Item<'_>]) -> Vec<Unit> {
    let mut raw = Vec::new();
    for (index, item) in items.iter().enumerate() {
        match *item {
            Item::Text { text, style } => {
                for (offset, c) in text.char_indices() {
                    let ch = if c == '\r' { ' ' } else { c };
                    let unit = Unit {
                        ch,
                        kind: Kind::Char,
                        item: index,
                        offset,
                        style,
                    };
                    raw.push((classify(c), unit));
                }
            }
            Item::Atomic { style } => raw.push((
                Raw::Other(Kind::Atomic),
                Unit {
                    ch: '\u{FFFC}',
                    kind: Kind::Atomic,
                    item: index,
                    offset: 0,
                    style,
                },
            )),
        }
    }
    collapse_raw(&raw)
}

/// Phase I over classified characters, each with its unit (whose `kind`
/// is replaced): [`step`] along them.
pub fn collapse_raw(raw: &[(Raw, Unit)]) -> Vec<Unit> {
    let mut out: Vec<Unit> = Vec::with_capacity(raw.len());
    let mut state = CollapseState::START;
    // Where the pending collapsible space is in `out`.
    let mut pending: Option<usize> = None;
    for &(r, unit) in raw {
        let (emit, after) = step(&state, r, unit.style.white_space);
        let retract = matches!(emit, Emit::Retract | Emit::RetractAndPush(_));
        if retract && let Some(k) = pending.take() {
            // Only bidi formatting characters follow it in `out`.
            if k < out.len() {
                out.remove(k);
            }
        }
        if let Emit::Push(kind) | Emit::RetractAndPush(kind) = emit {
            let ch = match kind {
                Kind::CollapsibleSpace | Kind::PreservedSpace => ' ',
                _ => unit.ch,
            };
            // A space just became pending: it is the unit pushed now.
            if after.pending.is_some() && state.pending.is_none() {
                pending = Some(out.len());
            }
            out.push(Unit { ch, kind, ..unit });
        }
        if after.pending.is_none() {
            pending = None;
        }
        state = after;
    }
    out
}

/// One step of Phase I (CSS Text 3 §4.1.1 steps 1 to 5, §4.1.3): what
/// becomes of the next character, read as `raw`, whose inline's
/// `white-space` is `ws`, given what was kept before it (`state`, which
/// must satisfy [`CollapseState::invariant`]); and the state after it.
pub fn step(state: &CollapseState, raw: Raw, ws: WhiteSpace) -> (Emit, CollapseState) {
    let keep = |emit: Emit, last: Last, pending: Option<Last>, after_break: bool| {
        (
            emit,
            CollapseState {
                last,
                pending,
                after_break,
            },
        )
    };
    match raw {
        // "ignoring bidi formatting characters … as if they were not
        // there": kept, and the state is unchanged.
        Raw::Bidi => (Emit::Push(Kind::Char), *state),
        // A collapsible space or tab (step 3 makes a tab a space).
        Raw::Space | Raw::Tab if collapsible(ws) => {
            if state.after_break || matches!(state.last, Last::Space | Last::ConvertedBreak) {
                // Step 1: "Any sequence of collapsible spaces and tabs
                // immediately … following a segment break is removed"; step
                // 4: "Any collapsible space immediately following another
                // collapsible space … is collapsed".
                (Emit::Nothing, *state)
            } else {
                keep(
                    Emit::Push(Kind::CollapsibleSpace),
                    Last::Space,
                    Some(state.last),
                    false,
                )
            }
        }
        Raw::SegmentBreak => {
            // Step 1: "Any sequence of collapsible spaces and tabs
            // immediately preceding … a segment break is removed": the
            // pending space, and `last` is what came before it.
            let (retract, last) = match state.pending {
                Some(before) => (true, before),
                None => (false, state.last),
            };
            let with = |kind: Option<Kind>| match (retract, kind) {
                (true, Some(k)) => Emit::RetractAndPush(k),
                (true, None) => Emit::Retract,
                (false, Some(k)) => Emit::Push(k),
                (false, None) => Emit::Nothing,
            };
            if matches!(ws, WhiteSpace::Normal | WhiteSpace::Nowrap) {
                // §4.1.3: "any collapsible segment break immediately
                // following another collapsible segment break is removed.
                // Then any remaining segment break is either transformed
                // into a space (U+0020) or removed": a space (modelling
                // choices).
                if last == Last::ConvertedBreak {
                    keep(with(None), last, None, true)
                } else {
                    keep(
                        with(Some(Kind::CollapsibleSpace)),
                        Last::ConvertedBreak,
                        None,
                        true,
                    )
                }
            } else {
                // §4.1.3: "When white-space is pre, pre-wrap, break-spaces,
                // or pre-line, segment breaks are not collapsible and are
                // instead transformed into a preserved line feed".
                keep(
                    with(Some(Kind::ForcedBreak)),
                    Last::PreservedBreak,
                    None,
                    true,
                )
            }
        }
        // Step 5: "any sequence of spaces is treated as a sequence of
        // non-breaking spaces": preserved.
        Raw::Space => keep(Emit::Push(Kind::PreservedSpace), Last::Other, None, false),
        Raw::Tab => keep(Emit::Push(Kind::PreservedTab), Last::Other, None, false),
        Raw::Other(kind) => keep(Emit::Push(kind), Last::Other, None, false),
    }
}
