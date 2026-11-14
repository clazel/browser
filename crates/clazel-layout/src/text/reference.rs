//! Direct readings of UAX #14's rules and of CSS Text 3's Phase I, kept as
//! the oracles the step formulations are tested against.
//!
//! These are `text/`'s first implementations: UAX #14 read with the whole
//! text at hand (looking left and right through it from each position), and
//! Phase I as five passes over the whole text, one per step of §4.1.1. The
//! shipped code (`uax14::breaks_with_rules`, `collapse::collapse_raw`) is the
//! same algorithms as one left-to-right pass of a step over a small state
//! (`state`), which the Kani harnesses cover for every length. The unit tests
//! compare the two on every line of `LineBreakTest.txt` and on every string
//! of a small alphabet up to a fixed length, and a bounded Kani harness
//! compares them on any short string. Citations are as in the shipped files.

use super::classes::{Lb, Props};
use super::collapse::{Kind, Raw, Unit, collapsible};
use super::uax14::{Break, Rule, absorbed, effective};
use clazel_style::cascade::computed::WhiteSpace;

/// Whether `c` is a class and in `set`.
fn is(c: Option<Lb>, set: u64) -> bool {
    c.is_some_and(|c| set & c.bit() != 0)
}

// UAX #14, read over the whole text.

/// What LB9 and LB10 make of `text`, computed once for every position.
struct Prepared {
    /// LB9, per character.
    absorbed: Vec<bool>,
    /// The items (LB9 and LB10), in order.
    items: Vec<Props>,
    /// For each character, its item's index.
    item_of: Vec<usize>,
}

impl Prepared {
    fn new(text: &[Props]) -> Prepared {
        let absorbed = absorbed(text);
        let effective = effective(text, &absorbed);
        // The items: the effective properties of the characters LB9 did
        // not absorb, and for each character the index of the item it is in.
        let mut items: Vec<Props> = Vec::with_capacity(text.len());
        let mut item_of: Vec<usize> = Vec::with_capacity(text.len());
        for (&e, &a) in effective.iter().zip(&absorbed) {
            if !a {
                items.push(e);
            }
            item_of.push(items.len().saturating_sub(1));
        }
        Prepared {
            absorbed,
            items,
            item_of,
        }
    }

    fn context<'a>(&'a self, text: &'a [Props]) -> Context<'a> {
        Context {
            text,
            absorbed: &self.absorbed,
            items: &self.items,
            item_of: &self.item_of,
        }
    }
}

/// The break after each character of `text` (UAX #14 §6), with the rule
/// that decided it.
pub fn breaks_with_rules(text: &[Props]) -> Vec<(Break, Rule)> {
    let prepared = Prepared::new(text);
    let ctx = prepared.context(text);
    (1..=text.len()).map(|i| ctx.decide(i)).collect()
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
    fn is(&self, j: usize, set: u64) -> bool {
        is(self.class(j), set)
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
        while self.is(k, lb_set![SY, IS]) {
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

        // LB11: "× WJ", "WJ ×".
        if cb == Some(Lb::WJ) || ca == Some(Lb::WJ) {
            return (No, Rule::Lb11);
        }
        // LB12: "GL ×".
        if ca == Some(Lb::GL) {
            return (No, Rule::Lb12);
        }
        // LB12a: "[^SP HY HH] × GL".
        if cb == Some(Lb::GL) && !is(ca, lb_set![SP, HY, HH]) {
            return (No, Rule::Lb12a);
        }
        // LB13: "× CL", "× CP", "× EX", "× SY".
        if is(cb, lb_set![CL, CP, EX, SY]) {
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
                Some(k) => self.is(k, lb_set![BK, CR, LF, NL, OP, QU, GL, SP, ZW]),
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
                    lb_set![SP, GL, WJ, CL, QU, CP, EX, IS, SY, BK, CR, LF, NL, ZW],
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
        if cb == Some(Lb::NS) && s.is_some_and(|s| self.is(s, lb_set![CL, CP])) {
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
        if is(ca, lb_set![HY, HH]) && is(cb, lb_set![AL, HL]) {
            let start = match Context::before(a) {
                None => true,
                Some(k) => self.is(k, lb_set![BK, CR, LF, NL, SP, ZW, CB, GL]),
            };
            if start {
                return (No, Rule::Lb20a);
            }
        }
        // LB21: "× BA", "× HH", "× HY", "× NS", "BB ×".
        if is(cb, lb_set![BA, HH, HY, NS]) || ca == Some(Lb::BB) {
            return (No, Rule::Lb21);
        }
        // LB21a: "HL (HY | HH) × [^HL]".
        if is(ca, lb_set![HY, HH])
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
        if (is(ca, lb_set![AL, HL]) && cb == Some(Lb::NU))
            || (ca == Some(Lb::NU) && is(cb, lb_set![AL, HL]))
        {
            return (No, Rule::Lb23);
        }
        // LB23a: "PR × (ID | EB | EM)", "(ID | EB | EM) × PO".
        if (ca == Some(Lb::PR) && is(cb, lb_set![ID, EB, EM]))
            || (is(ca, lb_set![ID, EB, EM]) && cb == Some(Lb::PO))
        {
            return (No, Rule::Lb23a);
        }
        // LB24: "(PR | PO) × (AL | HL)", "(AL | HL) × (PR | PO)".
        if (is(ca, lb_set![PR, PO]) && is(cb, lb_set![AL, HL]))
            || (is(ca, lb_set![AL, HL]) && is(cb, lb_set![PR, PO]))
        {
            return (No, Rule::Lb24);
        }
        // LB25, in the annex's order:
        if is(cb, lb_set![PO, PR]) {
            // "NU ( SY | IS )* CL × PO", "NU ( SY | IS )* CP × PO",
            // "NU ( SY | IS )* CL × PR", "NU ( SY | IS )* CP × PR".
            if is(ca, lb_set![CL, CP])
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
        if is(ca, lb_set![PO, PR]) {
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
        if is(ca, lb_set![HY, IS]) && cb == Some(Lb::NU) {
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
        if (ca == Some(Lb::JL) && is(cb, lb_set![JL, JV, H2, H3]))
            || (is(ca, lb_set![JV, H2]) && is(cb, lb_set![JV, JT]))
            || (is(ca, lb_set![JT, H3]) && cb == Some(Lb::JT))
        {
            return (No, Rule::Lb26);
        }
        // LB27: "(JL | JV | JT | H2 | H3) × PO", "PR × (JL | JV | JT | H2 |
        // H3)".
        let korean = lb_set![JL, JV, JT, H2, H3];
        if (is(ca, korean) && cb == Some(Lb::PO)) || (ca == Some(Lb::PR) && is(cb, korean)) {
            return (No, Rule::Lb27);
        }
        // LB28: "(AL | HL) × (AL | HL)".
        if is(ca, lb_set![AL, HL]) && is(cb, lb_set![AL, HL]) {
            return (No, Rule::Lb28);
        }
        // LB28a: "AP × (AK | [◌] | AS)", "(AK | [◌] | AS) × (VF | VI)",
        // "(AK | [◌] | AS) VI × (AK | [◌])", "(AK | [◌] | AS) × (AK | [◌] |
        // AS) VF".
        if (ca == Some(Lb::AP) && self.ak_dc_as(b))
            || (self.ak_dc_as(a) && is(cb, lb_set![VF, VI]))
            || (ca == Some(Lb::VI)
                && Context::before(a).is_some_and(|k| self.ak_dc_as(k))
                && self.ak_dc(b))
            || (self.ak_dc_as(a) && self.ak_dc_as(b) && cnext == Some(Lb::VF))
        {
            return (No, Rule::Lb28a);
        }
        // LB29: "IS × (AL | HL)".
        if ca == Some(Lb::IS) && is(cb, lb_set![AL, HL]) {
            return (No, Rule::Lb29);
        }
        // LB30: "(AL | HL | NU) × [OP-$EastAsian]", "[CP-$EastAsian] × (AL |
        // HL | NU)".
        if (is(ca, lb_set![AL, HL, NU]) && pb.class == Lb::OP && !pb.east_asian)
            || (pa.class == Lb::CP && !pa.east_asian && is(cb, lb_set![AL, HL, NU]))
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

// CSS Text 3 §4.1.1 Phase I, as five passes.

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
