//! Line breaking classes and the other character properties UAX #14's rules
//! read, with LB1's resolution (UAX #14 revision 57, §5.1 and §6.1, LB1).
//!
//! Modelling choices:
//!
//! - **Properties are looked up in the generated tables** of [`super::data`]
//!   (Unicode 18.0.0, `xtask/src/linebreak.rs`), each a sorted list of
//!   disjoint ranges searched by bisection. A code point in no range of
//!   `LINE_BREAK` cannot occur (the table covers U+0000..U+10FFFF); if it did,
//!   it would be XX, LineBreak.txt's `@missing` default.
//! - **[`Props`] keeps only what the rules read**: the resolved class, whether
//!   the character is in `\p{Pi}` or `\p{Pf}` (LB15a, LB15b, LB19), in
//!   `$EastAsian` (LB19a, LB30), in `[\p{Extended_Pictographic}&\p{Cn}]`
//!   (LB30b), and whether it is U+25CC DOTTED CIRCLE, which LB28a names.
//! - **LB1's resolution is the annex's default table**: AI, SG and XX to AL;
//!   SA to CM when General_Category is Mn or Mc, and to AL otherwise; CJ to
//!   NS. CB stays CB (LB20 handles it). [`Props::css`] adds the tailorings
//!   CSS Text 3 asks for (see `super` and `super::wrap`).

use super::data::{EAST_ASIAN, EXTENDED_PICTOGRAPHIC, GENERAL_CATEGORY, LINE_BREAK};

/// A Line_Break property value (UAX #14 §5.1, Table 1), by its short name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Lb {
    /// Ambiguous (Alphabetic or Ideographic).
    AI,
    /// Aksara.
    AK,
    /// Ordinary alphabetic and symbol characters.
    AL,
    /// Aksara pre-base.
    AP,
    /// Aksara start.
    AS,
    /// Break opportunity before and after.
    B2,
    /// Break after.
    BA,
    /// Break before.
    BB,
    /// Mandatory break.
    BK,
    /// Contingent break opportunity.
    CB,
    /// Conditional Japanese starter.
    CJ,
    /// Close punctuation.
    CL,
    /// Combining mark.
    CM,
    /// Close parenthesis.
    CP,
    /// Carriage return.
    CR,
    /// Emoji base.
    EB,
    /// Emoji modifier.
    EM,
    /// Exclamation or interrogation.
    EX,
    /// Non-breaking ("glue").
    GL,
    /// Hangul LV syllable.
    H2,
    /// Hangul LVT syllable.
    H3,
    /// Unambiguous hyphen.
    HH,
    /// Hebrew letter.
    HL,
    /// Hyphen.
    HY,
    /// Ideographic.
    ID,
    /// Inseparable.
    IN,
    /// Infix numeric separator.
    IS,
    /// Hangul L jamo.
    JL,
    /// Hangul T jamo.
    JT,
    /// Hangul V jamo.
    JV,
    /// Line feed.
    LF,
    /// Next line.
    NL,
    /// Nonstarter.
    NS,
    /// Numeric.
    NU,
    /// Open punctuation.
    OP,
    /// Postfix numeric.
    PO,
    /// Prefix numeric.
    PR,
    /// Quotation.
    QU,
    /// Regional indicator.
    RI,
    /// Complex context dependent (South East Asian).
    SA,
    /// Surrogate.
    SG,
    /// Space.
    SP,
    /// Symbols allowing break after.
    SY,
    /// Virama final.
    VF,
    /// Virama.
    VI,
    /// Word joiner.
    WJ,
    /// Unknown.
    XX,
    /// Zero width space.
    ZW,
    /// Zero width joiner.
    ZWJ,
}

impl Lb {
    /// This class's bit in a set of classes (`lb_set!`).
    pub const fn bit(self) -> u64 {
        match 1u64.checked_shl(self as u32) {
            Some(b) => b,
            None => 0,
        }
    }
}

/// The General_Category values that line breaking reads; every other value
/// is `None` where a category is returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gc {
    /// Nonspacing_Mark.
    Mn,
    /// Spacing_Mark.
    Mc,
    /// Initial_Punctuation.
    Pi,
    /// Final_Punctuation.
    Pf,
    /// Unassigned.
    Cn,
    /// Space_Separator.
    Zs,
    /// Control.
    Cc,
}

/// The value of the range of `table` holding `c`, by bisection.
fn lookup<T: Copy>(table: &[(u32, u32, T)], c: u32) -> Option<T> {
    let i = table.partition_point(|&(_, last, _)| last < c);
    match table.get(i) {
        Some(&(first, _, v)) if first <= c => Some(v),
        _ => None,
    }
}

/// Whether `c` is in a range of `table`, by bisection.
fn contains(table: &[(u32, u32)], c: u32) -> bool {
    let i = table.partition_point(|&(_, last)| last < c);
    table.get(i).is_some_and(|&(first, _)| first <= c)
}

/// `c`'s Line_Break value as LineBreak.txt gives it, before LB1.
pub fn line_break(c: char) -> Lb {
    lookup(&LINE_BREAK, u32::from(c)).unwrap_or(Lb::XX)
}

/// `c`'s General_Category, if it is one of [`Gc`]'s.
pub fn general_category(c: char) -> Option<Gc> {
    lookup(&GENERAL_CATEGORY, u32::from(c))
}

/// Whether `c` is in UAX #14's `$EastAsian`, `[\p{ea=F}\p{ea=W}\p{ea=H}]`
/// (§6, the paragraph before LB1).
pub fn east_asian(c: char) -> bool {
    contains(&EAST_ASIAN, u32::from(c))
}

/// Whether `c` has Extended_Pictographic (UTS #51, emoji-data.txt).
pub fn extended_pictographic(c: char) -> bool {
    contains(&EXTENDED_PICTOGRAPHIC, u32::from(c))
}

/// UAX #14 LB1, the default resolution: "In the absence of such criteria
/// all characters with a specific combination of original class and
/// General_Category property value are resolved as follows": AI, SG and XX
/// (any category) to AL; SA to CM if Mn or Mc, else AL; CJ to NS.
pub fn resolve(original: Lb, gc: Option<Gc>) -> Lb {
    match original {
        Lb::AI | Lb::SG | Lb::XX => Lb::AL,
        Lb::SA if matches!(gc, Some(Gc::Mn | Gc::Mc)) => Lb::CM,
        Lb::SA => Lb::AL,
        Lb::CJ => Lb::NS,
        other => other,
    }
}

/// The properties of one character that UAX #14's rules LB2 to LB31 read,
/// after LB1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Props {
    /// The resolved line breaking class.
    pub class: Lb,
    /// General_Category Initial_Punctuation (`\p{Pi}`).
    pub pi: bool,
    /// General_Category Final_Punctuation (`\p{Pf}`).
    pub pf: bool,
    /// In `$EastAsian`.
    pub east_asian: bool,
    /// In `[\p{Extended_Pictographic}&\p{Cn}]` (LB30b).
    pub pictographic_unassigned: bool,
    /// U+25CC DOTTED CIRCLE, the `[◌]` of LB28a.
    pub dotted_circle: bool,
}

impl Props {
    /// LB10: "the properties of U+0041 A LATIN CAPITAL LETTER A, that is,
    /// Line_Break=AL, General_Category=Lu, East_Asian_Width=Na,
    /// Extended_Pictographic=N".
    pub const LETTER_A: Props = Props {
        class: Lb::AL,
        pi: false,
        pf: false,
        east_asian: false,
        pictographic_unassigned: false,
        dotted_circle: false,
    };

    /// `c`'s properties with `class` as its resolved class.
    fn with_class(c: char, class: Lb, gc: Option<Gc>) -> Props {
        Props {
            class,
            pi: gc == Some(Gc::Pi),
            pf: gc == Some(Gc::Pf),
            east_asian: east_asian(c),
            pictographic_unassigned: gc == Some(Gc::Cn) && extended_pictographic(c),
            dotted_circle: c == '\u{25CC}',
        }
    }

    /// `c`'s properties with LB1's default resolution ([`resolve`]): the
    /// algorithm as `LineBreakTest.txt` tests it.
    pub fn of(c: char) -> Props {
        let gc = general_category(c);
        Props::with_class(c, resolve(line_break(c), gc), gc)
    }

    /// `c`'s properties with the tailorings of LB1 that CSS Text 3 asks for
    /// (`super`'s modelling choices):
    ///
    /// - SA other than Mn and Mc resolves to ID, not AL: §5.5 "it must
    ///   assume a soft wrap opportunity between pairs of typographic letter
    ///   units in that writing system" when the UA cannot do the lexical
    ///   analysis, which we never do;
    /// - a control character (Cc) of class CM resolves to AL: §4 "must be
    ///   otherwise treated as any other character of the Other Symbols (So)
    ///   general category", which is not a combining mark;
    /// - with `break_all` (`word-break: break-all`, §5.1), AL, HL and NU
    ///   (AI by LB1 included) are "instead treated as ID".
    pub fn css(c: char, break_all: bool) -> Props {
        let gc = general_category(c);
        let original = line_break(c);
        let class = match original {
            Lb::SA if !matches!(gc, Some(Gc::Mn | Gc::Mc)) => Lb::ID,
            Lb::CM if gc == Some(Gc::Cc) => Lb::AL,
            other => resolve(other, gc),
        };
        let class = match class {
            Lb::AL | Lb::HL | Lb::NU if break_all => Lb::ID,
            other => other,
        };
        Props::with_class(c, class, gc)
    }
}
