//! UAX #14 §6, the line breaking rules LB2 to LB31, in order.
//!
//! Source: Unicode Standard Annex #14, "Unicode Line Breaking Algorithm",
//! revision 57 (Unicode 18.0.0, 2026-09-01),
//! <https://www.unicode.org/reports/tr14/tr14-57.html#Algorithm>. Each rule
//! below carries its number and quotes its expression.
//!
//! Modelling choices:
//!
//! - **Input**: the characters' properties after LB1 ([`Props`], built by
//!   [`Props::of`] or [`Props::css`]). LB1 is done by the caller.
//! - **Output**: one [`Break`] per character, for the position *after* it;
//!   the last one is the position before eot. The position before the first
//!   character (after sot) is never a break (LB2) and has no entry.
//! - **"The rules are applied in order"**: [`decide`] tries each rule at a
//!   position and returns at the first that matches, so the implicit
//!   "otherwise" before each rule is the order of the `if`s.
//! - **LB9 and LB10** are a rewrite of the sequence, which we do once:
//!   [`absorbed`] marks every CM or ZWJ that LB9 attaches to the character
//!   before it ("Treat X (CM | ZWJ)* as if it were X"), and [`effective`]
//!   gives each character the properties the later rules see: an absorbed
//!   character those of its base X, a CM or ZWJ that LB9 left those of
//!   U+0041 (LB10), and any other its own. Rules LB11 to LB31 then work on
//!   the *items*, the characters LB9 did not absorb ("any CM or ZWJ
//!   characters affected by this rule are ignored"). Rules LB4 to LB8a,
//!   which come before LB9, see the characters themselves.
//! - **A position inside an absorbed sequence** (before an absorbed CM or
//!   ZWJ) is decided by LB9 as "×", unless LB4 to LB8a decided it first.
//! - **Context to the left and right** (`SP*`, `(SY | IS)*`, the
//!   characters after the position in LB15b, LB15c, LB19a, LB25 and
//!   LB28a) is read over the items, so an absorbed mark between them is
//!   skipped, as LB9 says.

use super::classes::{Lb, Props};

/// What a position between two characters is (UAX #14 §6: "!", "×", "÷").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Break {
    /// "×": no break allowed.
    Prohibited,
    /// "÷": break allowed.
    Allowed,
    /// "!": mandatory break.
    Mandatory,
}

/// The rule that decided a position, for diagnostics and for CSS's
/// emergency wrapping (`super::wrap`), which must not split what some
/// rules keep together.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    /// Rule LB3.
    Lb3,
    /// Rule LB4.
    Lb4,
    /// Rule LB5.
    Lb5,
    /// Rule LB6.
    Lb6,
    /// Rule LB7.
    Lb7,
    /// Rule LB8.
    Lb8,
    /// Rule LB8a.
    Lb8a,
    /// Rule LB9.
    Lb9,
    /// Rule LB11.
    Lb11,
    /// Rule LB12.
    Lb12,
    /// Rule LB12a.
    Lb12a,
    /// Rule LB13.
    Lb13,
    /// Rule LB14.
    Lb14,
    /// Rule LB15a.
    Lb15a,
    /// Rule LB15b.
    Lb15b,
    /// Rule LB15c.
    Lb15c,
    /// Rule LB15d.
    Lb15d,
    /// Rule LB16.
    Lb16,
    /// Rule LB17.
    Lb17,
    /// Rule LB18.
    Lb18,
    /// Rule LB19.
    Lb19,
    /// Rule LB19a.
    Lb19a,
    /// Rule LB20.
    Lb20,
    /// Rule LB20a.
    Lb20a,
    /// Rule LB21.
    Lb21,
    /// Rule LB21a.
    Lb21a,
    /// Rule LB21b.
    Lb21b,
    /// Rule LB22.
    Lb22,
    /// Rule LB23.
    Lb23,
    /// Rule LB23a.
    Lb23a,
    /// Rule LB24.
    Lb24,
    /// Rule LB25.
    Lb25,
    /// Rule LB26.
    Lb26,
    /// Rule LB27.
    Lb27,
    /// Rule LB28.
    Lb28,
    /// Rule LB28a.
    Lb28a,
    /// Rule LB29.
    Lb29,
    /// Rule LB30.
    Lb30,
    /// Rule LB30a.
    Lb30a,
    /// Rule LB30b.
    Lb30b,
    /// Rule LB31.
    Lb31,
}

/// LB9's "X", the classes a CM or ZWJ attaches to: "any line break class
/// except BK, CR, LF, NL, SP, or ZW".
fn is_base(c: Lb) -> bool {
    !matches!(c, Lb::BK | Lb::CR | Lb::LF | Lb::NL | Lb::SP | Lb::ZW)
}

/// LB9: for each character, whether it is a CM or ZWJ in "X (CM | ZWJ)*",
/// that is, whether it follows (directly) a character of a class X. The
/// first of two marks after a space is not absorbed, and the second is,
/// its X being the first (LB10 then makes that one AL).
pub fn absorbed(text: &[Props]) -> Vec<bool> {
    let mut out = Vec::with_capacity(text.len());
    let mut prev: Option<Lb> = None;
    for p in text {
        out.push(matches!(p.class, Lb::CM | Lb::ZWJ) && prev.is_some_and(is_base));
        prev = Some(p.class);
    }
    out
}

/// LB9 and LB10: the properties the rules after LB9 see for each
/// character. An absorbed character has its base's ("as if it has the line
/// breaking class of the base character"); a remaining CM or ZWJ has
/// U+0041's (LB10, [`Props::LETTER_A`]); any other its own.
pub fn effective(text: &[Props], absorbed: &[bool]) -> Vec<Props> {
    let mut out: Vec<Props> = Vec::with_capacity(text.len());
    for (p, &a) in text.iter().zip(absorbed) {
        let e = match out.last() {
            Some(&base) if a => base,
            _ if matches!(p.class, Lb::CM | Lb::ZWJ) => Props::LETTER_A,
            _ => *p,
        };
        out.push(e);
    }
    out
}

/// The break after each character of `text` (UAX #14 §6), with the rule
/// that decided it.
pub fn breaks_with_rules(text: &[Props]) -> Vec<(Break, Rule)> {
    let absorbed = absorbed(text);
    let effective = effective(text, &absorbed);
    // The items: the effective properties of the characters LB9 did not
    // absorb, and for each character the index of the item it is in.
    let mut items: Vec<Props> = Vec::with_capacity(text.len());
    let mut item_of: Vec<usize> = Vec::with_capacity(text.len());
    for (&e, &a) in effective.iter().zip(&absorbed) {
        if !a {
            items.push(e);
        }
        item_of.push(items.len().saturating_sub(1));
    }
    let ctx = Context {
        text,
        absorbed: &absorbed,
        items: &items,
        item_of: &item_of,
    };
    (1..=text.len()).map(|i| ctx.decide(i)).collect()
}

/// The break after each character of `text` (UAX #14 §6).
pub fn breaks(text: &[Props]) -> Vec<Break> {
    breaks_with_rules(text)
        .into_iter()
        .map(|(b, _)| b)
        .collect()
}

/// What the rules read.
struct Context<'a> {
    /// The characters, after LB1.
    text: &'a [Props],
    /// LB9, per character.
    absorbed: &'a [bool],
    /// The items (LB9 and LB10), in order.
    items: &'a [Props],
    /// For each character, its item's index.
    item_of: &'a [usize],
}

impl Context<'_> {
    /// The class of character `i`, after LB1.
    fn raw(&self, i: usize) -> Option<Lb> {
        self.text.get(i).map(|p| p.class)
    }

    /// Item `j`.
    fn item(&self, j: usize) -> Option<&Props> {
        self.items.get(j)
    }

    /// The class of item `j`.
    fn class(&self, j: usize) -> Option<Lb> {
        self.item(j).map(|p| p.class)
    }

    /// Whether item `j` exists and its class is in `set`.
    fn is(&self, j: usize, set: &[Lb]) -> bool {
        self.class(j).is_some_and(|c| set.contains(&c))
    }

    /// Item `j - 1`, the one before `j` (`None` at sot).
    fn before(j: usize) -> Option<usize> {
        j.checked_sub(1)
    }

    /// The last item before item `j` that is not SP, skipping `SP*`
    /// (`None` if only spaces, or nothing, are before `j`).
    fn before_spaces(&self, j: usize) -> Option<usize> {
        let mut k = Context::before(j)?;
        while self.class(k) == Some(Lb::SP) {
            k = Context::before(k)?;
        }
        Some(k)
    }

    /// The last item at or before item `k` that is not SY or IS, skipping
    /// `(SY | IS)*` backwards (LB25).
    fn before_sy_is(&self, k: usize) -> Option<usize> {
        let mut k = k;
        while self.is(k, &[Lb::SY, Lb::IS]) {
            k = Context::before(k)?;
        }
        Some(k)
    }

    /// LB28a's `(AK | [◌] | AS)`.
    fn ak_dc_as(&self, j: usize) -> bool {
        self.item(j)
            .is_some_and(|p| matches!(p.class, Lb::AK | Lb::AS) || p.dotted_circle)
    }

    /// LB28a's `(AK | [◌])`.
    fn ak_dc(&self, j: usize) -> bool {
        self.item(j)
            .is_some_and(|p| p.class == Lb::AK || p.dotted_circle)
    }

    /// The break at position `i`, between characters `i - 1` and `i`
    /// (`i == text.len()` is eot). `i` is at least 1: "sot ×" (LB2) is never
    /// asked.
    fn decide(&self, i: usize) -> (Break, Rule) {
        use Break::{Allowed as Yes, Mandatory as Must, Prohibited as No};
        let n = self.text.len();
        let before = self.raw(i.saturating_sub(1));
        let after = self.raw(i);

        // LB3: "! eot".
        if i >= n {
            return (Must, Rule::Lb3);
        }
        // LB4: "BK !".
        if before == Some(Lb::BK) {
            return (Must, Rule::Lb4);
        }
        // LB5: "CR × LF", "CR !", "LF !", "NL !".
        if before == Some(Lb::CR) && after == Some(Lb::LF) {
            return (No, Rule::Lb5);
        }
        if matches!(before, Some(Lb::CR | Lb::LF | Lb::NL)) {
            return (Must, Rule::Lb5);
        }
        // LB6: "× ( BK | CR | LF | NL )".
        if matches!(after, Some(Lb::BK | Lb::CR | Lb::LF | Lb::NL)) {
            return (No, Rule::Lb6);
        }
        // LB7: "× SP", "× ZW".
        if matches!(after, Some(Lb::SP | Lb::ZW)) {
            return (No, Rule::Lb7);
        }
        // LB8: "ZW SP* ÷", over the characters (LB9 comes later).
        let mut k = i.saturating_sub(1);
        while self.raw(k) == Some(Lb::SP) && k > 0 {
            k = k.saturating_sub(1);
        }
        if self.raw(k) == Some(Lb::ZW) {
            return (Yes, Rule::Lb8);
        }
        // LB8a: "ZWJ ×".
        if before == Some(Lb::ZWJ) {
            return (No, Rule::Lb8a);
        }
        // LB9: "Treat X (CM | ZWJ)* as if it were X": no break inside.
        if self.absorbed.get(i).copied().unwrap_or(false) {
            return (No, Rule::Lb9);
        }

        // From here on, items (LB9, LB10): `a` is the item before the
        // position, `b` the one after.
        let b = self.item_of.get(i).copied().unwrap_or(0);
        let Some(a) = Context::before(b) else {
            // Unreachable: character 0 is in item 0 and i >= 1 is not
            // absorbed, so b >= 1. LB31 decides, as for any other pair.
            return (Yes, Rule::Lb31);
        };
        let ca = self.class(a);
        let cb = self.class(b);
        let pa = self.item(a).copied().unwrap_or(Props::LETTER_A);
        let pb = self.item(b).copied().unwrap_or(Props::LETTER_A);
        let next = b.checked_add(1).filter(|&k| k < self.items.len());
        let cnext = next.and_then(|k| self.class(k));
        let is = |c: Option<Lb>, set: &[Lb]| c.is_some_and(|c| set.contains(&c));

        // LB11: "× WJ", "WJ ×".
        if cb == Some(Lb::WJ) || ca == Some(Lb::WJ) {
            return (No, Rule::Lb11);
        }
        // LB12: "GL ×".
        if ca == Some(Lb::GL) {
            return (No, Rule::Lb12);
        }
        // LB12a: "[^SP HY HH] × GL".
        if cb == Some(Lb::GL) && !is(ca, &[Lb::SP, Lb::HY, Lb::HH]) {
            return (No, Rule::Lb12a);
        }
        // LB13: "× CL", "× CP", "× EX", "× SY".
        if is(cb, &[Lb::CL, Lb::CP, Lb::EX, Lb::SY]) {
            return (No, Rule::Lb13);
        }
        // LB14: "OP SP* ×".
        let s = self.before_spaces(b);
        if s.is_some_and(|s| self.class(s) == Some(Lb::OP)) {
            return (No, Rule::Lb14);
        }
        // LB15a: "(sot | BK | CR | LF | NL | OP | QU | GL | SP | ZW)
        // [\p{Pi}&QU] SP* ×".
        if let Some(q) = s
            && self.item(q).is_some_and(|p| p.class == Lb::QU && p.pi)
        {
            let start = match Context::before(q) {
                None => true,
                Some(k) => self.is(
                    k,
                    &[
                        Lb::BK,
                        Lb::CR,
                        Lb::LF,
                        Lb::NL,
                        Lb::OP,
                        Lb::QU,
                        Lb::GL,
                        Lb::SP,
                        Lb::ZW,
                    ],
                ),
            };
            if start {
                return (No, Rule::Lb15a);
            }
        }
        // LB15b: "× [\p{Pf}&QU] ( SP | GL | WJ | CL | QU | CP | EX | IS | SY
        // | BK | CR | LF | NL | ZW | eot)".
        if pb.class == Lb::QU
            && pb.pf
            && (next.is_none()
                || is(
                    cnext,
                    &[
                        Lb::SP,
                        Lb::GL,
                        Lb::WJ,
                        Lb::CL,
                        Lb::QU,
                        Lb::CP,
                        Lb::EX,
                        Lb::IS,
                        Lb::SY,
                        Lb::BK,
                        Lb::CR,
                        Lb::LF,
                        Lb::NL,
                        Lb::ZW,
                    ],
                ))
        {
            return (No, Rule::Lb15b);
        }
        // LB15c: "SP ÷ IS NU".
        if ca == Some(Lb::SP) && cb == Some(Lb::IS) && cnext == Some(Lb::NU) {
            return (Yes, Rule::Lb15c);
        }
        // LB15d: "× IS".
        if cb == Some(Lb::IS) {
            return (No, Rule::Lb15d);
        }
        // LB16: "(CL | CP) SP* × NS".
        if cb == Some(Lb::NS) && s.is_some_and(|s| self.is(s, &[Lb::CL, Lb::CP])) {
            return (No, Rule::Lb16);
        }
        // LB17: "B2 SP* × B2".
        if cb == Some(Lb::B2) && s.is_some_and(|s| self.class(s) == Some(Lb::B2)) {
            return (No, Rule::Lb17);
        }
        // LB18: "SP ÷".
        if ca == Some(Lb::SP) {
            return (Yes, Rule::Lb18);
        }
        // LB19: "× [ QU - \p{Pi} ]", "[ QU - \p{Pf} ] ×".
        if (pb.class == Lb::QU && !pb.pi) || (pa.class == Lb::QU && !pa.pf) {
            return (No, Rule::Lb19);
        }
        // LB19a: "[^$EastAsian] × QU", "× QU ( [^$EastAsian] | eot )",
        // "QU × [^$EastAsian]", "( sot | [^$EastAsian] ) QU ×".
        if pb.class == Lb::QU
            && (!pa.east_asian
                || next
                    .and_then(|k| self.item(k))
                    .is_none_or(|p| !p.east_asian))
        {
            return (No, Rule::Lb19a);
        }
        if pa.class == Lb::QU
            && (!pb.east_asian
                || Context::before(a)
                    .and_then(|k| self.item(k))
                    .is_none_or(|p| !p.east_asian))
        {
            return (No, Rule::Lb19a);
        }
        // LB20: "÷ CB", "CB ÷".
        if cb == Some(Lb::CB) || ca == Some(Lb::CB) {
            return (Yes, Rule::Lb20);
        }
        // LB20a: "( sot | BK | CR | LF | NL | SP | ZW | CB | GL ) ( HY | HH )
        // × ( AL | HL )".
        if is(ca, &[Lb::HY, Lb::HH]) && is(cb, &[Lb::AL, Lb::HL]) {
            let start = match Context::before(a) {
                None => true,
                Some(k) => self.is(
                    k,
                    &[
                        Lb::BK,
                        Lb::CR,
                        Lb::LF,
                        Lb::NL,
                        Lb::SP,
                        Lb::ZW,
                        Lb::CB,
                        Lb::GL,
                    ],
                ),
            };
            if start {
                return (No, Rule::Lb20a);
            }
        }
        // LB21: "× BA", "× HH", "× HY", "× NS", "BB ×".
        if is(cb, &[Lb::BA, Lb::HH, Lb::HY, Lb::NS]) || ca == Some(Lb::BB) {
            return (No, Rule::Lb21);
        }
        // LB21a: "HL (HY | HH) × [^HL]".
        if is(ca, &[Lb::HY, Lb::HH])
            && cb != Some(Lb::HL)
            && Context::before(a).is_some_and(|k| self.class(k) == Some(Lb::HL))
        {
            return (No, Rule::Lb21a);
        }
        // LB21b: "SY × HL".
        if ca == Some(Lb::SY) && cb == Some(Lb::HL) {
            return (No, Rule::Lb21b);
        }
        // LB22: "× IN".
        if cb == Some(Lb::IN) {
            return (No, Rule::Lb22);
        }
        // LB23: "(AL | HL) × NU", "NU × (AL | HL)".
        if (is(ca, &[Lb::AL, Lb::HL]) && cb == Some(Lb::NU))
            || (ca == Some(Lb::NU) && is(cb, &[Lb::AL, Lb::HL]))
        {
            return (No, Rule::Lb23);
        }
        // LB23a: "PR × (ID | EB | EM)", "(ID | EB | EM) × PO".
        if (ca == Some(Lb::PR) && is(cb, &[Lb::ID, Lb::EB, Lb::EM]))
            || (is(ca, &[Lb::ID, Lb::EB, Lb::EM]) && cb == Some(Lb::PO))
        {
            return (No, Rule::Lb23a);
        }
        // LB24: "(PR | PO) × (AL | HL)", "(AL | HL) × (PR | PO)".
        if (is(ca, &[Lb::PR, Lb::PO]) && is(cb, &[Lb::AL, Lb::HL]))
            || (is(ca, &[Lb::AL, Lb::HL]) && is(cb, &[Lb::PR, Lb::PO]))
        {
            return (No, Rule::Lb24);
        }
        // LB25, in the annex's order:
        if is(cb, &[Lb::PO, Lb::PR]) {
            // "NU ( SY | IS )* CL × PO", "NU ( SY | IS )* CP × PO",
            // "NU ( SY | IS )* CL × PR", "NU ( SY | IS )* CP × PR".
            if is(ca, &[Lb::CL, Lb::CP])
                && Context::before(a)
                    .and_then(|k| self.before_sy_is(k))
                    .is_some_and(|k| self.class(k) == Some(Lb::NU))
            {
                return (No, Rule::Lb25);
            }
            // "NU ( SY | IS )* × PO", "NU ( SY | IS )* × PR".
            if self
                .before_sy_is(a)
                .is_some_and(|k| self.class(k) == Some(Lb::NU))
            {
                return (No, Rule::Lb25);
            }
        }
        // "PO × OP NU", "PO × OP IS NU", "PO × NU", "PR × OP NU",
        // "PR × OP IS NU", "PR × NU".
        if is(ca, &[Lb::PO, Lb::PR]) {
            let after_next = next
                .and_then(|k| k.checked_add(1))
                .and_then(|k| self.class(k));
            if cb == Some(Lb::NU)
                || (cb == Some(Lb::OP) && cnext == Some(Lb::NU))
                || (cb == Some(Lb::OP) && cnext == Some(Lb::IS) && after_next == Some(Lb::NU))
            {
                return (No, Rule::Lb25);
            }
        }
        // "HY × NU", "IS × NU".
        if is(ca, &[Lb::HY, Lb::IS]) && cb == Some(Lb::NU) {
            return (No, Rule::Lb25);
        }
        // "NU ( SY | IS )* × NU".
        if cb == Some(Lb::NU)
            && self
                .before_sy_is(a)
                .is_some_and(|k| self.class(k) == Some(Lb::NU))
        {
            return (No, Rule::Lb25);
        }
        // LB26: "JL × (JL | JV | H2 | H3)", "(JV | H2) × (JV | JT)",
        // "(JT | H3) × JT".
        if (ca == Some(Lb::JL) && is(cb, &[Lb::JL, Lb::JV, Lb::H2, Lb::H3]))
            || (is(ca, &[Lb::JV, Lb::H2]) && is(cb, &[Lb::JV, Lb::JT]))
            || (is(ca, &[Lb::JT, Lb::H3]) && cb == Some(Lb::JT))
        {
            return (No, Rule::Lb26);
        }
        // LB27: "(JL | JV | JT | H2 | H3) × PO", "PR × (JL | JV | JT | H2 |
        // H3)".
        let korean = [Lb::JL, Lb::JV, Lb::JT, Lb::H2, Lb::H3];
        if (is(ca, &korean) && cb == Some(Lb::PO)) || (ca == Some(Lb::PR) && is(cb, &korean)) {
            return (No, Rule::Lb27);
        }
        // LB28: "(AL | HL) × (AL | HL)".
        if is(ca, &[Lb::AL, Lb::HL]) && is(cb, &[Lb::AL, Lb::HL]) {
            return (No, Rule::Lb28);
        }
        // LB28a: "AP × (AK | [◌] | AS)", "(AK | [◌] | AS) × (VF | VI)",
        // "(AK | [◌] | AS) VI × (AK | [◌])", "(AK | [◌] | AS) × (AK | [◌] |
        // AS) VF".
        if (ca == Some(Lb::AP) && self.ak_dc_as(b))
            || (self.ak_dc_as(a) && is(cb, &[Lb::VF, Lb::VI]))
            || (ca == Some(Lb::VI)
                && Context::before(a).is_some_and(|k| self.ak_dc_as(k))
                && self.ak_dc(b))
            || (self.ak_dc_as(a) && self.ak_dc_as(b) && cnext == Some(Lb::VF))
        {
            return (No, Rule::Lb28a);
        }
        // LB29: "IS × (AL | HL)".
        if ca == Some(Lb::IS) && is(cb, &[Lb::AL, Lb::HL]) {
            return (No, Rule::Lb29);
        }
        // LB30: "(AL | HL | NU) × [OP-$EastAsian]", "[CP-$EastAsian] × (AL |
        // HL | NU)".
        if (is(ca, &[Lb::AL, Lb::HL, Lb::NU]) && pb.class == Lb::OP && !pb.east_asian)
            || (pa.class == Lb::CP && !pa.east_asian && is(cb, &[Lb::AL, Lb::HL, Lb::NU]))
        {
            return (No, Rule::Lb30);
        }
        // LB30a: "sot (RI RI)* RI × RI", "[^RI] (RI RI)* RI × RI": the
        // number of RIs ending at `a` is odd.
        if ca == Some(Lb::RI) && cb == Some(Lb::RI) {
            let mut count: usize = 0;
            let mut k = Some(a);
            while let Some(j) = k
                && self.class(j) == Some(Lb::RI)
            {
                count = count.saturating_add(1);
                k = Context::before(j);
            }
            if !count.is_multiple_of(2) {
                return (No, Rule::Lb30a);
            }
        }
        // LB30b: "EB × EM", "[\p{Extended_Pictographic}&\p{Cn}] × EM".
        if cb == Some(Lb::EM) && (ca == Some(Lb::EB) || pa.pictographic_unassigned) {
            return (No, Rule::Lb30b);
        }
        // LB31: "ALL ÷", "÷ ALL".
        (Yes, Rule::Lb31)
    }
}
