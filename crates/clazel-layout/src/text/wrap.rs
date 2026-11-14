//! CSS Text 3 §5: soft wrap opportunities, from UAX #14 with `white-space`
//! (§3), `word-break` (§5.1), `overflow-wrap` (§5.4) and §5.5's details.
//!
//! Source: CSS Text Module Level 3, W3C Candidate Recommendation Draft,
//! 14 August 2026, <https://www.w3.org/TR/2026/CRD-css-text-3-20260814/>,
//! §3 "White Space and Wrapping: the white-space property", §5 "Line
//! Breaking and Word Boundaries", §5.1 "Breaking Rules for Letters: the
//! word-break property", §5.4 "Overflow Wrapping: the overflow-wrap
//! (word-wrap) property" and §5.5 "Line Breaking Details". (phase-5.md
//! names these §5.2 and §5.5 from memory; the pinned text numbers them §5.1
//! and §5.4, with `line-break` at §5.2 and `hyphens` at §5.3.) CSS gives no
//! numbered steps; the citations name the section and quote the sentence.
//!
//! Modelling choices:
//!
//! - **The opportunities are UAX #14's** ([`super::uax14`]) over the units
//!   of Phase I, with the classes of `Props::css` (SA letters as ID,
//!   controls as AL, and `word-break: break-all`'s letters as ID). A
//!   collapsible or preserved space is U+0020 (SP), a preserved tab U+0009
//!   (BA), a preserved segment break U+000A (LF) and an atomic inline
//!   U+FFFC (CB).
//! - **`line-break` is not in the subset**: it is `auto`, for which "the UA
//!   determines the set of line-breaking restrictions"; ours is UAX #14's
//!   default with CJ as NS, which §5.2's `strict` matches. §5.2's informative
//!   note on UAX #14 deviations ("!important", "23/Jan/2024") is not
//!   applied. `hyphens` is not in the subset: no hyphenation.
//! - **Which box's properties decide a position.** §5.5: "For soft wrap
//!   opportunities created by characters that disappear at the line break
//!   (e.g. U+0020 SPACE), properties on the box directly containing that
//!   character control the line breaking at that opportunity"; we take the
//!   position after a space, tab or other space separator to be such an
//!   opportunity, decided by that character's style. Otherwise "the
//!   white-space property on the nearest common ancestor of the two
//!   characters controls breaking"; we have no tree here, and allow
//!   wrapping only if both characters' `white-space` allow it (the common
//!   ancestor's value is inherited by both unless one of them sets its own,
//!   and that one would then not wrap with the other's value either).
//!   Which `word-break` and `overflow-wrap` decide "is undefined in this
//!   level": we use the character before the position.
//! - **`word-break: keep-all`**: "breaks are prohibited between pairs of
//!   such characters", typographic letter units and NU, AL, AI and ID. We
//!   take the letter classes to be AL (AI by LB1), HL, NU, ID (with SA by
//!   `Props::css`), the Hangul classes H2, H3, JL, JV and JT, the Brahmic
//!   AK, AP, AS, VI and VF, and EB and EM ("Symbols that line-break the same
//!   way as letters of a particular category are affected the same way").
//!   `overflow-wrap: normal`'s permission to relax `keep-all` when a line
//!   has no other opportunity ("may") is not taken.
//! - **`word-break: break-word`** is "the same effect as word-break: normal
//!   and overflow-wrap: anywhere, regardless of the actual value of the
//!   overflow-wrap property" (§5.1).
//! - **`overflow-wrap: anywhere` and `break-word`** add an [`Wrap::Emergency`]
//!   opportunity at every position UAX #14 prohibits, except where that
//!   would split a typographic character unit ("grapheme clusters must stay
//!   together as one unit"). We have no UAX #29 segmentation; the positions
//!   kept whole are those UAX #14 decides by its rules that approximate
//!   grapheme clusters: LB5 (CR × LF), LB8a (after ZWJ), LB9 (before an
//!   absorbed mark), LB26 (Hangul syllable blocks), LB30a (regional
//!   indicator pairs) and LB30b (emoji modifiers). Positions before a space
//!   or a forced break (LB6, LB7) are not added either: the break would come
//!   after the space anyway. Listed.
//! - **Atomic inlines** (§5.5): "there is a soft wrap opportunity before and
//!   after each replaced element or other atomic inline, even when adjacent
//!   to a character that would normally suppress them, including U+00A0
//!   NO-BREAK SPACE. However, with the exception of U+00A0 NO-BREAK SPACE,
//!   there must be no soft wrap opportunity between atomic inlines and
//!   adjacent characters belonging to the Unicode GL, WJ, or ZWJ line
//!   breaking classes." Before a space, a forced break or a combining mark
//!   that LB9 attaches to the atomic inline, UAX #14 decides as for any
//!   other character (a mark is not split from its base, and the break
//!   comes after the space).

use super::classes::{Lb, Props};
use super::collapse::{Kind, Unit};
use super::state::Side;
use super::uax14::{Break, Rule, absorbed, breaks_with_rules, effective};
use clazel_style::cascade::computed::{OverflowWrap, WhiteSpace, WordBreak};

/// The kind of line break possible after a unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Wrap {
    /// No line break here.
    None,
    /// A soft wrap opportunity (§5).
    Soft,
    /// A forced line break (§5: "explicit line-breaking controls", the end
    /// of the block).
    Forced,
    /// An opportunity `overflow-wrap` adds (§5.4), taken only "if there are
    /// no otherwise-acceptable break points in the line".
    Emergency {
        /// Whether it counts "when calculating min-content intrinsic sizes"
        /// (`anywhere`), or not (`break-word`).
        min_content: bool,
    },
}

/// §3: whether `white-space` lets lines wrap ("Text Wrapping" in the
/// summary table: `pre` and `nowrap` do not).
pub fn wraps(ws: WhiteSpace) -> bool {
    !matches!(ws, WhiteSpace::Pre | WhiteSpace::Nowrap)
}

/// The `overflow-wrap` in effect: `anywhere` under `word-break: break-word`
/// (§5.1), the property's value otherwise.
pub fn overflow_wrap(word_break: WordBreak, overflow_wrap: OverflowWrap) -> OverflowWrap {
    if word_break == WordBreak::BreakWord {
        OverflowWrap::Anywhere
    } else {
        overflow_wrap
    }
}

/// Whether a unit is white space or another space separator, whose own
/// style decides the opportunity after it (§5.5).
fn is_space(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::CollapsibleSpace | Kind::PreservedSpace | Kind::PreservedTab | Kind::OtherSpace
    )
}

/// §5.1 `keep-all`'s "typographic letter units (or other typographic
/// character units belonging to the NU, AL, AI, or ID Unicode line breaking
/// classes)", by class (modelling choices).
fn letter(class: Lb) -> bool {
    matches!(
        class,
        Lb::AL
            | Lb::HL
            | Lb::NU
            | Lb::ID
            | Lb::H2
            | Lb::H3
            | Lb::JL
            | Lb::JV
            | Lb::JT
            | Lb::AK
            | Lb::AP
            | Lb::AS
            | Lb::VI
            | Lb::VF
            | Lb::EB
            | Lb::EM
    )
}

/// The rules whose "×" keeps a typographic character unit whole, where
/// `overflow-wrap` adds no opportunity (modelling choices).
fn keeps_unit(rule: Rule) -> bool {
    matches!(
        rule,
        Rule::Lb5
            | Rule::Lb6
            | Rule::Lb7
            | Rule::Lb8a
            | Rule::Lb9
            | Rule::Lb26
            | Rule::Lb30a
            | Rule::Lb30b
    )
}

/// The properties each unit gives UAX #14's rules: `Props::css` of its
/// character, with `word-break: break-all` from its style.
pub fn props(units: &[Unit]) -> Vec<Props> {
    units
        .iter()
        .map(|u| Props::css(u.ch, u.style.word_break == WordBreak::BreakAll))
        .collect()
}

/// The line break possible after each unit of an inline formatting
/// context, after Phase I. The last is always [`Wrap::Forced`] (the end of
/// the block; UAX #14 LB3).
pub fn opportunities(units: &[Unit]) -> Vec<Wrap> {
    wraps_from(units, &props(units))
}

/// [`opportunities`] with each unit's properties given (`props`, one per
/// unit; a missing one counts as U+0041's).
pub fn wraps_from(units: &[Unit], props: &[Props]) -> Vec<Wrap> {
    let props: Vec<Props> = (0..units.len())
        .map(|i| props.get(i).copied().unwrap_or(Props::LETTER_A))
        .collect();
    let rules = breaks_with_rules(&props);
    wraps_from_breaks(units, &props, &rules)
}

/// [`wraps_from`] with UAX #14's decision after each unit given (`rules`,
/// as `breaks_with_rules` gives them for `props`; a missing one counts as
/// eot's). The CSS layer alone, for the Kani harnesses.
pub fn wraps_from_breaks(units: &[Unit], props: &[Props], rules: &[(Break, Rule)]) -> Vec<Wrap> {
    let props: Vec<Props> = (0..units.len())
        .map(|i| props.get(i).copied().unwrap_or(Props::LETTER_A))
        .collect();
    let absorbed = absorbed(&props);
    let effective = effective(&props, &absorbed);
    let sides: Vec<Side> = units
        .iter()
        .zip(&props)
        .zip(absorbed.iter().zip(&effective))
        .map(|((u, p), (a, e))| Side {
            unit: *u,
            class: p.class,
            absorbed: *a,
            effective: e.class,
        })
        .collect();
    sides
        .iter()
        .enumerate()
        .map(|(i, here)| {
            let (b, rule) = rules
                .get(i)
                .copied()
                .unwrap_or((Break::Mandatory, Rule::Lb3));
            wrap_at(here, sides.get(i.saturating_add(1)), b, rule)
        })
        .collect()
}

/// The line break possible after a unit (`here`), before the next one
/// (`next`, `None` at the end), given UAX #14's decision `b` by `rule`
/// there. It reads nothing else, so it holds for a position anywhere in a
/// text of any length.
pub fn wrap_at(here: &Side, next: Option<&Side>, b: Break, rule: Rule) -> Wrap {
    let u = &here.unit;
    // §5.5: "Preserved segment breaks, and—regardless of the white-space
    // value—any Unicode character with the BK and NL line breaking class,
    // must be treated as forced line breaks." UAX #14's mandatory breaks
    // are exactly these (LB4, LB5 after LF and NL; a CR is a space, §4) and
    // the end of the text (LB3), the end of the block.
    if b == Break::Mandatory {
        return Wrap::Forced;
    }
    let Some(there) = next else {
        // Unreachable from `wraps_from_breaks`: the last position is LB3's.
        return Wrap::Forced;
    };
    let next = &there.unit;
    // §3 and §5.5: which `white-space` decides (modelling choices).
    let ws = u.style.white_space;
    let wrapping = if is_space(u.kind) {
        wraps(ws)
    } else {
        wraps(ws) && wraps(next.style.white_space)
    };
    if !wrapping {
        return Wrap::None;
    }

    // §5.5, atomic inlines.
    if u.kind == Kind::Atomic || next.kind == Kind::Atomic {
        let by_uax14 = matches!(
            there.class,
            Lb::SP | Lb::ZW | Lb::BK | Lb::CR | Lb::LF | Lb::NL
        ) || there.absorbed;
        if by_uax14 {
            return from_break(b);
        }
        let other = if u.kind == Kind::Atomic {
            (next.kind != Kind::Atomic).then_some(there)
        } else {
            Some(here)
        };
        return match other {
            Some(c) if c.unit.ch != '\u{00A0}' && matches!(c.class, Lb::GL | Lb::WJ | Lb::ZWJ) => {
                Wrap::None
            }
            _ => Wrap::Soft,
        };
    }

    // §4.1.1: "for pre-wrap, a soft wrap opportunity exists at the end of a
    // sequence of spaces and/or tabs", and so not inside one.
    let preserved = |k: Kind| matches!(k, Kind::PreservedSpace | Kind::PreservedTab);
    if ws == WhiteSpace::PreWrap && preserved(u.kind) && preserved(next.kind) {
        return Wrap::None;
    }
    // §3 `break-spaces`: "A soft wrap opportunity exists after every
    // preserved white space character and after every other space separator
    // (including between adjacent spaces)."
    if ws == WhiteSpace::BreakSpaces && (preserved(u.kind) || u.kind == Kind::OtherSpace) {
        return Wrap::Soft;
    }

    let mut wrap = from_break(b);
    // §5.1 `keep-all`: "breaks are prohibited between pairs of such
    // characters".
    if wrap == Wrap::Soft
        && u.style.word_break == WordBreak::KeepAll
        && letter(here.effective)
        && letter(there.effective)
    {
        wrap = Wrap::None;
    }
    // §5.4: "An otherwise unbreakable sequence of characters may be broken
    // at an arbitrary point if there are no otherwise-acceptable break
    // points in the line."
    if wrap == Wrap::None && !keeps_unit(rule) {
        match overflow_wrap(u.style.word_break, u.style.overflow_wrap) {
            OverflowWrap::Normal => {}
            OverflowWrap::Anywhere => wrap = Wrap::Emergency { min_content: true },
            OverflowWrap::BreakWord => wrap = Wrap::Emergency { min_content: false },
        }
    }
    wrap
}

/// A UAX #14 decision as a CSS opportunity.
fn from_break(b: Break) -> Wrap {
    match b {
        Break::Prohibited => Wrap::None,
        Break::Allowed => Wrap::Soft,
        Break::Mandatory => Wrap::Forced,
    }
}
