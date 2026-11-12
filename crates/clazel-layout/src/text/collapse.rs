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
//! - **Control characters** (Cc other than tab, line feed and carriage
//!   return) are kept as ordinary characters; §4's "visible glyph" is the
//!   shaper's (it draws `.notdef`), and their line breaking class is
//!   `Props::css`'s.

use super::TextStyle;
use super::classes::{Gc, Lb, general_category, line_break};
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

/// What a character becomes in the steps below.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    /// Still as read.
    Raw(Raw),
    /// Removed.
    Removed,
    /// A collapsible space (a converted tab or segment break, or a space).
    Space,
}

/// The neighbour of `i` in direction `forward` among the characters not
/// removed and not bidi formatting characters ("ignoring bidi formatting
/// characters … as if they were not there").
fn neighbour(states: &[State], i: usize, forward: bool) -> Option<usize> {
    let mut k = i;
    loop {
        k = if forward {
            k.checked_add(1)?
        } else {
            k.checked_sub(1)?
        };
        match states.get(k)? {
            State::Removed | State::Raw(Raw::Bidi) => {}
            _ => return Some(k),
        }
    }
}

/// Phase I over classified characters, each with its unit (whose `kind`
/// is replaced).
pub fn collapse_raw(raw: &[(Raw, Unit)]) -> Vec<Unit> {
    let mut states: Vec<State> = raw.iter().map(|(r, _)| State::Raw(*r)).collect();
    let coll = |i: usize| {
        raw.get(i)
            .is_some_and(|(_, u)| collapsible(u.style.white_space))
    };
    // §4.1.3: "When white-space is pre, pre-wrap, break-spaces, or pre-line,
    // segment breaks are not collapsible".
    let coll_break = |i: usize| {
        raw.get(i).is_some_and(|(_, u)| {
            matches!(u.style.white_space, WhiteSpace::Normal | WhiteSpace::Nowrap)
        })
    };

    // Step 1: "Any sequence of collapsible spaces and tabs immediately
    // preceding or following a segment break is removed."
    for i in 0..states.len() {
        if states.get(i) != Some(&State::Raw(Raw::SegmentBreak)) {
            continue;
        }
        for forward in [false, true] {
            let mut k = i;
            while let Some(j) = neighbour(&states, k, forward)
                && matches!(states.get(j), Some(State::Raw(Raw::Space | Raw::Tab)))
                && coll(j)
            {
                if let Some(s) = states.get_mut(j) {
                    *s = State::Removed;
                }
                k = j;
            }
        }
    }

    // Step 2: "Collapsible segment breaks are transformed for rendering
    // according to the segment break transformation rules" (§4.1.3):
    // "First, any collapsible segment break immediately following another
    // collapsible segment break is removed. Then any remaining segment break
    // is either transformed into a space (U+0020) or removed": we always
    // transform it into a space (modelling choices).
    for i in 0..states.len() {
        if states.get(i) == Some(&State::Raw(Raw::SegmentBreak))
            && coll_break(i)
            && neighbour(&states, i, false).is_some_and(|p| {
                states.get(p) == Some(&State::Raw(Raw::SegmentBreak)) && coll_break(p)
            })
            && let Some(s) = states.get_mut(i)
        {
            *s = State::Removed;
        }
    }
    for (i, s) in states.iter_mut().enumerate() {
        if *s == State::Raw(Raw::SegmentBreak) && coll_break(i) {
            *s = State::Space;
        }
    }

    // Step 3: "Every collapsible tab is converted to a collapsible space
    // (U+0020)." Spaces that remain collapsible become `Space` too.
    for (i, s) in states.iter_mut().enumerate() {
        if matches!(s, State::Raw(Raw::Tab | Raw::Space)) && coll(i) {
            *s = State::Space;
        }
    }

    // Step 4: "Any collapsible space immediately following another
    // collapsible space … is collapsed to have zero advance width": removed
    // (modelling choices).
    for i in 0..states.len() {
        if states.get(i) == Some(&State::Space)
            && neighbour(&states, i, false).is_some_and(|p| states.get(p) == Some(&State::Space))
            && let Some(s) = states.get_mut(i)
        {
            *s = State::Removed;
        }
    }

    // Step 5 ("If white-space is set to pre, pre-wrap, or break-spaces, any
    // sequence of spaces is treated as a sequence of non-breaking spaces"):
    // what remains as read is preserved; `super::wrap` gives preserved
    // spaces their soft wrap opportunities. A preserved segment break is
    // "transformed into a preserved line feed" (§4.1.3), a forced break.
    let mut out = Vec::with_capacity(raw.len());
    for (state, (_, unit)) in states.iter().zip(raw) {
        let kind = match state {
            State::Removed => continue,
            State::Space => Kind::CollapsibleSpace,
            State::Raw(Raw::Space) => Kind::PreservedSpace,
            State::Raw(Raw::Tab) => Kind::PreservedTab,
            State::Raw(Raw::SegmentBreak) => Kind::ForcedBreak,
            State::Raw(Raw::Bidi) => Kind::Char,
            State::Raw(Raw::Other(k)) => *k,
        };
        let ch = match kind {
            Kind::CollapsibleSpace | Kind::PreservedSpace => ' ',
            _ => unit.ch,
        };
        out.push(Unit { ch, kind, ..*unit });
    }
    out
}
