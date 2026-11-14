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
//! - **"The rules are applied in order"**: [`step`] tries each rule at a
//!   position and returns at the first that matches, so the implicit
//!   "otherwise" before each rule is the order of the `if`s.
//! - **One pass, one step per character.** [`step`] decides the position
//!   before a character from a [`BreakState`], a summary of everything the
//!   rules read to the left (`state.rs` lists it field by field), and the
//!   at most two items to the right that LB15b, LB15c, LB19a, LB25 and LB28a
//!   read; it returns the state after the character. No rule needs more:
//!   every unbounded left context in the rules (`SP*` in LB8, LB14 to LB17;
//!   `( SY | IS )*` in LB25; `(RI RI)*` in LB30a) is a regular expression,
//!   which the state's flags follow. [`breaks_with_rules`] runs the step
//!   along the text. `reference.rs` keeps the first reading of the rules,
//!   which looks through the whole text from each position, as the oracle.
//! - **LB9 and LB10** are a rewrite of the sequence: [`absorbed`] marks every
//!   CM or ZWJ that LB9 attaches to the character before it ("Treat X (CM |
//!   ZWJ)* as if it were X"), and [`effective`] gives each character the
//!   properties the later rules see: an absorbed character those of its
//!   base X, a CM or ZWJ that LB9 left those of U+0041 (LB10), and any other
//!   its own. Rules LB11 to LB31 then work on the *items*, the characters
//!   LB9 did not absorb ("any CM or ZWJ characters affected by this rule are
//!   ignored"). Rules LB4 to LB8a, which come before LB9, see the
//!   characters themselves. The step does the same rewrite as it goes (an
//!   absorbed character leaves the item state as it was); the driver uses
//!   [`absorbed`] and [`effective`] only to find the items to the right.
//! - **A position inside an absorbed sequence** (before an absorbed CM or
//!   ZWJ) is decided by LB9 as "×", unless LB4 to LB8a decided it first.

use super::classes::{Lb, Props};
use super::state::{BreakState, LB15A_START};

/// Whether `c` is a class and in `set`.
fn is(c: Option<Lb>, set: u64) -> bool {
    c.is_some_and(|c| set & c.bit() != 0)
}

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
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Rule {
    /// Rule LB2 (the position before the first character).
    Lb2,
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
/// that decided it: [`step`] along the text, then LB3 at eot.
pub fn breaks_with_rules(text: &[Props]) -> Vec<(Break, Rule)> {
    let absorbed = absorbed(text);
    let effective = effective(text, &absorbed);
    // The items to the right of each character: for character `i`, the
    // index in `items` of the first item after its own.
    let items: Vec<Props> = effective
        .iter()
        .zip(&absorbed)
        .filter(|(_, a)| !**a)
        .map(|(e, _)| *e)
        .collect();
    let mut out = Vec::with_capacity(text.len());
    let mut state = BreakState::START;
    let mut item: usize = 0;
    for (i, (c, &a)) in text.iter().zip(&absorbed).enumerate() {
        if !a && i > 0 {
            item = item.saturating_add(1);
        }
        let next = items.get(item.saturating_add(1)).copied();
        let after_next = items.get(item.saturating_add(2)).copied();
        let (b, rule, after) = step(&state, *c, next, after_next);
        if i > 0 {
            out.push((b, rule));
        }
        state = after;
    }
    if !text.is_empty() {
        // LB3: "! eot".
        out.push((Break::Mandatory, Rule::Lb3));
    }
    out
}

/// The break after each character of `text` (UAX #14 §6).
pub fn breaks(text: &[Props]) -> Vec<Break> {
    breaks_with_rules(text)
        .into_iter()
        .map(|(b, _)| b)
        .collect()
}

/// The state after character `c`, which LB9 absorbed or not, with `e` its
/// properties after LB9 and LB10.
fn advance(state: &BreakState, c: Props, absorbed: bool, e: Props) -> BreakState {
    let raw_prev = Some(c.class);
    // LB8: "ZW SP*".
    let zw_spaces = c.class == Lb::ZW || (c.class == Lb::SP && state.zw_spaces);
    if absorbed {
        // "In subsequent rules, any CM or ZWJ characters affected by this
        // rule are ignored": the items are unchanged.
        return BreakState {
            raw_prev,
            zw_spaces,
            ..*state
        };
    }
    let class = e.class;
    let (before_spaces, lb15a_start) = if class == Lb::SP {
        (state.before_spaces, state.lb15a_start)
    } else {
        // The item before `e` is `a`; LB15a's start is "sot" or its set.
        (
            Some(e),
            state.a.is_none_or(|a| is(Some(a.class), LB15A_START)),
        )
    };
    BreakState {
        raw_prev,
        zw_spaces,
        a: Some(e),
        a_prev: state.a,
        before_spaces,
        lb15a_start,
        // LB25: "NU ( SY | IS )*" and "NU ( SY | IS )* ( CL | CP )".
        numeric: class == Lb::NU || (is(Some(class), lb_set![SY, IS]) && state.numeric),
        numeric_close: is(Some(class), lb_set![CL, CP]) && state.numeric,
        // LB30a: the parity of the RIs ending here.
        ri_odd: class == Lb::RI && !state.ri_odd,
    }
}

/// One step of UAX #14 (§6): the break at the position before character `c`
/// (after LB1), given what the rules remember of the text before it
/// (`state`, which must satisfy [`BreakState::invariant`]) and the two items
/// after `c`'s item (`None` past eot); and the state after `c`. For the
/// first character (`state` at sot) the position is LB2's "sot ×".
pub fn step(
    state: &BreakState,
    c: Props,
    next: Option<Props>,
    after_next: Option<Props>,
) -> (Break, Rule, BreakState) {
    use Break::{Allowed as Yes, Mandatory as Must, Prohibited as No};
    // LB9: is `c` a CM or ZWJ after an X? LB10: else a CM or ZWJ is U+0041.
    let absorbed = matches!(c.class, Lb::CM | Lb::ZWJ) && state.raw_prev.is_some_and(is_base);
    let e = match state.a {
        Some(base) if absorbed => base,
        _ if matches!(c.class, Lb::CM | Lb::ZWJ) => Props::LETTER_A,
        _ => c,
    };
    let after = advance(state, c, absorbed, e);
    let decide = |b: Break, r: Rule| (b, r, after);

    let before = state.raw_prev;
    let Some(pa) = state.a else {
        // LB2: "sot ×".
        return decide(No, Rule::Lb2);
    };
    // LB4: "BK !".
    if before == Some(Lb::BK) {
        return decide(Must, Rule::Lb4);
    }
    // LB5: "CR × LF", "CR !", "LF !", "NL !".
    if before == Some(Lb::CR) && c.class == Lb::LF {
        return decide(No, Rule::Lb5);
    }
    if is(before, lb_set![CR, LF, NL]) {
        return decide(Must, Rule::Lb5);
    }
    // LB6: "× ( BK | CR | LF | NL )".
    if is(Some(c.class), lb_set![BK, CR, LF, NL]) {
        return decide(No, Rule::Lb6);
    }
    // LB7: "× SP", "× ZW".
    if is(Some(c.class), lb_set![SP, ZW]) {
        return decide(No, Rule::Lb7);
    }
    // LB8: "ZW SP* ÷", over the characters (LB9 comes later).
    if state.zw_spaces {
        return decide(Yes, Rule::Lb8);
    }
    // LB8a: "ZWJ ×".
    if before == Some(Lb::ZWJ) {
        return decide(No, Rule::Lb8a);
    }
    // LB9: "Treat X (CM | ZWJ)* as if it were X": no break inside.
    if absorbed {
        return decide(No, Rule::Lb9);
    }

    // From here on, items (LB9, LB10): `pa` is the item before the
    // position, `pb` the one after.
    let pb = e;
    let ca = Some(pa.class);
    let cb = Some(pb.class);
    let cnext = next.map(|p| p.class);
    let s = state.before_spaces;
    let ak_dc_as = |p: &Props| matches!(p.class, Lb::AK | Lb::AS) || p.dotted_circle;
    let ak_dc = |p: &Props| p.class == Lb::AK || p.dotted_circle;

    // LB11: "× WJ", "WJ ×".
    if cb == Some(Lb::WJ) || ca == Some(Lb::WJ) {
        return decide(No, Rule::Lb11);
    }
    // LB12: "GL ×".
    if ca == Some(Lb::GL) {
        return decide(No, Rule::Lb12);
    }
    // LB12a: "[^SP HY HH] × GL".
    if cb == Some(Lb::GL) && !is(ca, lb_set![SP, HY, HH]) {
        return decide(No, Rule::Lb12a);
    }
    // LB13: "× CL", "× CP", "× EX", "× SY".
    if is(cb, lb_set![CL, CP, EX, SY]) {
        return decide(No, Rule::Lb13);
    }
    // LB14: "OP SP* ×".
    if s.is_some_and(|s| s.class == Lb::OP) {
        return decide(No, Rule::Lb14);
    }
    // LB15a: "(sot | BK | CR | LF | NL | OP | QU | GL | SP | ZW)
    // [\p{Pi}&QU] SP* ×".
    if s.is_some_and(|s| s.class == Lb::QU && s.pi) && state.lb15a_start {
        return decide(No, Rule::Lb15a);
    }
    // LB15b: "× [\p{Pf}&QU] ( SP | GL | WJ | CL | QU | CP | EX | IS | SY
    // | BK | CR | LF | NL | ZW | eot)".
    if pb.class == Lb::QU
        && pb.pf
        && (next.is_none()
            || is(
                cnext,
                lb_set![SP, GL, WJ, CL, QU, CP, EX, IS, SY, BK, CR, LF, NL, ZW],
            ))
    {
        return decide(No, Rule::Lb15b);
    }
    // LB15c: "SP ÷ IS NU".
    if ca == Some(Lb::SP) && cb == Some(Lb::IS) && cnext == Some(Lb::NU) {
        return decide(Yes, Rule::Lb15c);
    }
    // LB15d: "× IS".
    if cb == Some(Lb::IS) {
        return decide(No, Rule::Lb15d);
    }
    // LB16: "(CL | CP) SP* × NS".
    if cb == Some(Lb::NS) && s.is_some_and(|s| is(Some(s.class), lb_set![CL, CP])) {
        return decide(No, Rule::Lb16);
    }
    // LB17: "B2 SP* × B2".
    if cb == Some(Lb::B2) && s.is_some_and(|s| s.class == Lb::B2) {
        return decide(No, Rule::Lb17);
    }
    // LB18: "SP ÷".
    if ca == Some(Lb::SP) {
        return decide(Yes, Rule::Lb18);
    }
    // LB19: "× [ QU - \p{Pi} ]", "[ QU - \p{Pf} ] ×".
    if (pb.class == Lb::QU && !pb.pi) || (pa.class == Lb::QU && !pa.pf) {
        return decide(No, Rule::Lb19);
    }
    // LB19a: "[^$EastAsian] × QU", "× QU ( [^$EastAsian] | eot )",
    // "QU × [^$EastAsian]", "( sot | [^$EastAsian] ) QU ×".
    if pb.class == Lb::QU && (!pa.east_asian || next.is_none_or(|p| !p.east_asian)) {
        return decide(No, Rule::Lb19a);
    }
    if pa.class == Lb::QU && (!pb.east_asian || state.a_prev.is_none_or(|p| !p.east_asian)) {
        return decide(No, Rule::Lb19a);
    }
    // LB20: "÷ CB", "CB ÷".
    if cb == Some(Lb::CB) || ca == Some(Lb::CB) {
        return decide(Yes, Rule::Lb20);
    }
    // LB20a: "( sot | BK | CR | LF | NL | SP | ZW | CB | GL ) ( HY | HH )
    // × ( AL | HL )".
    if is(ca, lb_set![HY, HH])
        && is(cb, lb_set![AL, HL])
        && state
            .a_prev
            .is_none_or(|p| is(Some(p.class), lb_set![BK, CR, LF, NL, SP, ZW, CB, GL]))
    {
        return decide(No, Rule::Lb20a);
    }
    // LB21: "× BA", "× HH", "× HY", "× NS", "BB ×".
    if is(cb, lb_set![BA, HH, HY, NS]) || ca == Some(Lb::BB) {
        return decide(No, Rule::Lb21);
    }
    // LB21a: "HL (HY | HH) × [^HL]".
    if is(ca, lb_set![HY, HH])
        && cb != Some(Lb::HL)
        && state.a_prev.is_some_and(|p| p.class == Lb::HL)
    {
        return decide(No, Rule::Lb21a);
    }
    // LB21b: "SY × HL".
    if ca == Some(Lb::SY) && cb == Some(Lb::HL) {
        return decide(No, Rule::Lb21b);
    }
    // LB22: "× IN".
    if cb == Some(Lb::IN) {
        return decide(No, Rule::Lb22);
    }
    // LB23: "(AL | HL) × NU", "NU × (AL | HL)".
    if (is(ca, lb_set![AL, HL]) && cb == Some(Lb::NU))
        || (ca == Some(Lb::NU) && is(cb, lb_set![AL, HL]))
    {
        return decide(No, Rule::Lb23);
    }
    // LB23a: "PR × (ID | EB | EM)", "(ID | EB | EM) × PO".
    if (ca == Some(Lb::PR) && is(cb, lb_set![ID, EB, EM]))
        || (is(ca, lb_set![ID, EB, EM]) && cb == Some(Lb::PO))
    {
        return decide(No, Rule::Lb23a);
    }
    // LB24: "(PR | PO) × (AL | HL)", "(AL | HL) × (PR | PO)".
    if (is(ca, lb_set![PR, PO]) && is(cb, lb_set![AL, HL]))
        || (is(ca, lb_set![AL, HL]) && is(cb, lb_set![PR, PO]))
    {
        return decide(No, Rule::Lb24);
    }
    // LB25, in the annex's order: "NU ( SY | IS )* CL × PO", "NU ( SY | IS
    // )* CP × PO", "NU ( SY | IS )* CL × PR", "NU ( SY | IS )* CP × PR";
    // "NU ( SY | IS )* × PO", "NU ( SY | IS )* × PR".
    if is(cb, lb_set![PO, PR]) && (state.numeric_close || state.numeric) {
        return decide(No, Rule::Lb25);
    }
    // "PO × OP NU", "PO × OP IS NU", "PO × NU", "PR × OP NU", "PR × OP IS
    // NU", "PR × NU".
    if is(ca, lb_set![PO, PR])
        && (cb == Some(Lb::NU)
            || (cb == Some(Lb::OP) && cnext == Some(Lb::NU))
            || (cb == Some(Lb::OP)
                && cnext == Some(Lb::IS)
                && after_next.map(|p| p.class) == Some(Lb::NU)))
    {
        return decide(No, Rule::Lb25);
    }
    // "HY × NU", "IS × NU".
    if is(ca, lb_set![HY, IS]) && cb == Some(Lb::NU) {
        return decide(No, Rule::Lb25);
    }
    // "NU ( SY | IS )* × NU".
    if cb == Some(Lb::NU) && state.numeric {
        return decide(No, Rule::Lb25);
    }
    // LB26: "JL × (JL | JV | H2 | H3)", "(JV | H2) × (JV | JT)",
    // "(JT | H3) × JT".
    if (ca == Some(Lb::JL) && is(cb, lb_set![JL, JV, H2, H3]))
        || (is(ca, lb_set![JV, H2]) && is(cb, lb_set![JV, JT]))
        || (is(ca, lb_set![JT, H3]) && cb == Some(Lb::JT))
    {
        return decide(No, Rule::Lb26);
    }
    // LB27: "(JL | JV | JT | H2 | H3) × PO", "PR × (JL | JV | JT | H2 |
    // H3)".
    let korean = lb_set![JL, JV, JT, H2, H3];
    if (is(ca, korean) && cb == Some(Lb::PO)) || (ca == Some(Lb::PR) && is(cb, korean)) {
        return decide(No, Rule::Lb27);
    }
    // LB28: "(AL | HL) × (AL | HL)".
    if is(ca, lb_set![AL, HL]) && is(cb, lb_set![AL, HL]) {
        return decide(No, Rule::Lb28);
    }
    // LB28a: "AP × (AK | [◌] | AS)", "(AK | [◌] | AS) × (VF | VI)",
    // "(AK | [◌] | AS) VI × (AK | [◌])", "(AK | [◌] | AS) × (AK | [◌] |
    // AS) VF".
    if (ca == Some(Lb::AP) && ak_dc_as(&pb))
        || (ak_dc_as(&pa) && is(cb, lb_set![VF, VI]))
        || (ca == Some(Lb::VI) && state.a_prev.is_some_and(|p| ak_dc_as(&p)) && ak_dc(&pb))
        || (ak_dc_as(&pa) && ak_dc_as(&pb) && cnext == Some(Lb::VF))
    {
        return decide(No, Rule::Lb28a);
    }
    // LB29: "IS × (AL | HL)".
    if ca == Some(Lb::IS) && is(cb, lb_set![AL, HL]) {
        return decide(No, Rule::Lb29);
    }
    // LB30: "(AL | HL | NU) × [OP-$EastAsian]", "[CP-$EastAsian] × (AL |
    // HL | NU)".
    if (is(ca, lb_set![AL, HL, NU]) && pb.class == Lb::OP && !pb.east_asian)
        || (pa.class == Lb::CP && !pa.east_asian && is(cb, lb_set![AL, HL, NU]))
    {
        return decide(No, Rule::Lb30);
    }
    // LB30a: "sot (RI RI)* RI × RI", "[^RI] (RI RI)* RI × RI": the
    // number of RIs ending at `a` is odd.
    if ca == Some(Lb::RI) && cb == Some(Lb::RI) && state.ri_odd {
        return decide(No, Rule::Lb30a);
    }
    // LB30b: "EB × EM", "[\p{Extended_Pictographic}&\p{Cn}] × EM".
    if cb == Some(Lb::EM) && (ca == Some(Lb::EB) || pa.pictographic_unassigned) {
        return decide(No, Rule::Lb30b);
    }
    // LB31: "ALL ÷", "÷ ALL".
    decide(Yes, Rule::Lb31)
}
