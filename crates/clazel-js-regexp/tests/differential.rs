//! A differential: the matcher against a reference matcher, on random small
//! patterns and inputs.
//!
//! The reference is a direct transcription of ECMA-262 §22.2.2† (Pattern
//! Semantics): Matchers are closures from a state and a continuation to a
//! state or failure, RepeatMatcher recurses exactly as the standard's steps
//! do, and the input is a list of characters (code points with `u` or `v`),
//! indexed by character, not by code unit. It is exponential and recursive,
//! which is the point: it shares nothing with the real matcher's loop, its
//! instruction list or its stack. It reads the same syntax tree
//! ([`clazel_js_regexp::parse`]) and the same case-folding function and
//! property tables (`src/tables.rs`, checked in `tests/tables.rs`); it does not
//! use the real matcher's tables of equivalent characters: for `i` it searches
//! a universe of characters for those with the same `Canonicalize`
//! (CharacterSetMatcher step 3, read literally).
//!
//! Patterns come from a small random grammar over a few letters and the
//! characters where case mappings are interesting: alternation, groups
//! (capturing, named, non-capturing, with modifiers), the quantifiers (greedy
//! and lazy, counted), lookahead and lookbehind, backreferences, `^ $ \b \B`,
//! `.`, classes and escapes, and for `v` class set operations; with
//! the flags `i m s u v` at random. Inputs are random strings over the same
//! characters. For each pattern and input, every start index is tried with and
//! without `y`, and the captures must be equal.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use clazel_js_regexp::ast::{
    Assertion, Atom, ClassContents, ClassEscape, ClassItem, ClassSetExpr, ClassSetItem,
    ClassSetOperand, Disjunction, Property, Term, TermKind,
};
use clazel_js_regexp::unicode::{
    Prop, binary_property, canonicalize, category_mask, script_property, string_property,
};
use clazel_js_regexp::{Flags, Limits, Pattern, Program, compile, parse};

// ---------------------------------------------------------------------------
// The reference matcher.

type Caps = Vec<Option<(usize, usize)>>;

/// MatchState: an end index (in characters) and the captures.
#[derive(Clone)]
struct State {
    end: usize,
    caps: Caps,
}

/// The flags in scope (modifiers can change them).
#[derive(Clone, Copy)]
struct Fl {
    ic: bool,
    ml: bool,
    dot_all: bool,
}

type Cont<'k> = &'k dyn Fn(State) -> Option<State>;

/// The input as characters, with each one's code unit index.
struct Input {
    chars: Vec<u32>,
    /// `pos[i]` is the code unit index of character `i`; `pos[chars.len()]` is
    /// the length in code units.
    pos: Vec<usize>,
}

fn decode(units: &[u16], unicode: bool) -> Input {
    let mut chars = Vec::new();
    let mut pos = Vec::new();
    let mut i = 0usize;
    while i < units.len() {
        pos.push(i);
        let u = units.get(i).copied().unwrap_or(0);
        let next = units.get(i.saturating_add(1)).copied();
        match next {
            Some(l)
                if unicode && (0xD800..0xDC00).contains(&u) && (0xDC00..0xE000).contains(&l) =>
            {
                let cp = 0x10000u32
                    .wrapping_add(u32::from(u).wrapping_sub(0xD800).wrapping_mul(0x400))
                    .wrapping_add(u32::from(l).wrapping_sub(0xDC00));
                chars.push(cp);
                i = i.saturating_add(2);
            }
            _ => {
                chars.push(u32::from(u));
                i = i.saturating_add(1);
            }
        }
    }
    pos.push(units.len());
    Input { chars, pos }
}

struct Reference<'a> {
    input: &'a Input,
    unicode: bool,
    /// Matchers entered before giving up (the reference is exponential).
    fuel: Cell<u64>,
    memo: RefCell<HashMap<u32, Vec<u32>>>,
}

/// Characters among which equivalents are searched: ASCII and Latin-1 and
/// Latin Extended, the places the test alphabet's case mappings live.
fn universe() -> impl Iterator<Item = u32> {
    (0u32..0x300)
        .chain([0x17F, 0x1E9E, 0x212A, 0x2126, 0x3A3, 0x3C2, 0x3C3, 0x1FBE])
        // Greek and Cyrillic, where `Script` and `Script_Extensions` differ
        // from what the case folding relates (U+0345 folds to U+03B9).
        .chain(0x300..0x460)
        .chain(0x10400..0x10450)
}

fn is_lt(c: u32) -> bool {
    matches!(c, 0x0A | 0x0D | 0x2028 | 0x2029)
}

fn basic_word(c: u32) -> bool {
    matches!(c, 0x30..=0x39 | 0x41..=0x5A | 0x61..=0x7A | 0x5F)
}

fn is_space(c: u32) -> bool {
    matches!(
        c,
        0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0xFEFF | 0x2028 | 0x2029 | 0x1680 | 0x2000
            ..=0x200A | 0x202F | 0x205F | 0x3000
    )
}

/// The count of left-capturing groups at or inside a term: their numbers.
fn caps_in_kind(k: &TermKind, out: &mut Vec<u32>) {
    match k {
        TermKind::Atom(Atom::Group(g)) => {
            if let Some(i) = g.index {
                out.push(i);
            }
            caps_in_disj(&g.body, out);
        }
        TermKind::Atom(Atom::Modified(m)) => caps_in_disj(&m.body, out),
        TermKind::Look(l) => caps_in_disj(&l.body, out),
        _ => {}
    }
}

fn caps_in_disj(d: &Disjunction, out: &mut Vec<u32>) {
    for a in &d.alternatives {
        for t in &a.terms {
            caps_in_kind(&t.kind, out);
        }
    }
}

impl Reference<'_> {
    fn burn(&self) -> bool {
        let f = self.fuel.get();
        if f == 0 {
            return false;
        }
        self.fuel.set(f.saturating_sub(1));
        true
    }

    fn exhausted(&self) -> bool {
        self.fuel.get() == 0
    }

    fn canon(&self, c: u32) -> u32 {
        canonicalize(c, self.unicode)
    }

    /// Every `a` in the universe (and `ch`) with the same Canonicalize as `ch`.
    fn equivalents(&self, ch: u32) -> Vec<u32> {
        let cc = self.canon(ch);
        let mut memo = self.memo.borrow_mut();
        let mut v = memo
            .entry(cc)
            .or_insert_with(|| universe().filter(|&a| self.canon(a) == cc).collect())
            .clone();
        if self.canon(ch) == cc && !v.contains(&ch) {
            v.push(ch);
        }
        v
    }

    fn is_word(&self, c: u32, fl: Fl) -> bool {
        basic_word(c) || (self.unicode && fl.ic && basic_word(self.canon(c)))
    }

    /// Disjunction.
    fn disj(&self, d: &Disjunction, fl: Fl, fwd: bool, x: &State, c: Cont<'_>) -> Option<State> {
        if !self.burn() {
            return None;
        }
        for alt in &d.alternatives {
            if let Some(r) = self.seq(&alt.terms, fl, fwd, x, c) {
                return Some(r);
            }
        }
        None
    }

    /// Alternative: the terms left to right, or right to left.
    fn seq(&self, terms: &[Term], fl: Fl, fwd: bool, x: &State, c: Cont<'_>) -> Option<State> {
        let split = if fwd {
            terms.split_first()
        } else {
            terms.split_last()
        };
        match split {
            None => c(x.clone()),
            Some((t, rest)) => self.term(t, fl, fwd, x, &|y| self.seq(rest, fl, fwd, &y, c)),
        }
    }

    fn term(&self, t: &Term, fl: Fl, fwd: bool, x: &State, c: Cont<'_>) -> Option<State> {
        match &t.quantifier {
            None => self.kind(&t.kind, fl, fwd, x, c),
            Some(q) => {
                let mut parens = Vec::new();
                caps_in_kind(&t.kind, &mut parens);
                self.repeat(&t.kind, (q.min, q.max, q.greedy), &parens, (fl, fwd), x, c)
            }
        }
    }

    /// RepeatMatcher (§22.2.2.3.2†), step by step.
    fn repeat(
        &self,
        kind: &TermKind,
        (min, max, greedy): (u64, Option<u64>, bool),
        parens: &[u32],
        (fl, fwd): (Fl, bool),
        x: &State,
        c: Cont<'_>,
    ) -> Option<State> {
        if !self.burn() {
            return None;
        }
        // 1. If max = 0, return c(x).
        if max == Some(0) {
            return c(x.clone());
        }
        // 2. The continuation d.
        let d = |y: State| -> Option<State> {
            // 2.a. If min = 0 and y's endIndex = x's endIndex, return failure.
            if min == 0 && y.end == x.end {
                return None;
            }
            let min2 = if min == 0 { 0 } else { min.saturating_sub(1) };
            let max2 = max.map(|m| m.saturating_sub(1));
            self.repeat(kind, (min2, max2, greedy), parens, (fl, fwd), &y, c)
        };
        // 3-4. Clear the captures inside.
        let mut xr = x.clone();
        for &i in parens {
            if let Some(slot) = xr.caps.get_mut(i as usize) {
                *slot = None;
            }
        }
        // 5. If min != 0, return m(xr, d).
        if min != 0 {
            return self.kind(kind, fl, fwd, &xr, &d);
        }
        // 6. If greedy is false, try c(x) first.
        if !greedy {
            if let Some(z) = c(x.clone()) {
                return Some(z);
            }
            return self.kind(kind, fl, fwd, &xr, &d);
        }
        // 7. Try m(xr, d), then c(x).
        if let Some(z) = self.kind(kind, fl, fwd, &xr, &d) {
            return Some(z);
        }
        c(x.clone())
    }

    fn kind(&self, k: &TermKind, fl: Fl, fwd: bool, x: &State, c: Cont<'_>) -> Option<State> {
        if !self.burn() {
            return None;
        }
        let chars = &self.input.chars;
        let at = |i: usize| chars.get(i).copied();
        match k {
            TermKind::Assertion(a) => {
                let e = x.end;
                let before = e.checked_sub(1).and_then(at);
                let after = at(e);
                let ok = match a {
                    Assertion::Start => before.is_none_or(|ch| fl.ml && is_lt(ch)),
                    Assertion::End => after.is_none_or(|ch| fl.ml && is_lt(ch)),
                    Assertion::WordBoundary | Assertion::NotWordBoundary => {
                        let a1 = before.is_some_and(|ch| self.is_word(ch, fl));
                        let b1 = after.is_some_and(|ch| self.is_word(ch, fl));
                        (a1 != b1) == matches!(a, Assertion::WordBoundary)
                    }
                };
                if ok { c(x.clone()) } else { None }
            }
            TermKind::Look(l) => {
                let r = self.disj(&l.body, fl, !l.behind, x, &Some);
                if l.negative {
                    if r.is_some() { None } else { c(x.clone()) }
                } else {
                    let y = r?;
                    c(State {
                        end: x.end,
                        caps: y.caps,
                    })
                }
            }
            TermKind::Atom(a) => self.atom(a, fl, fwd, x, c),
        }
    }

    /// CharacterSetMatcher (§22.2.2.7.1†).
    fn set(
        &self,
        pred: &dyn Fn(u32) -> bool,
        invert: bool,
        fl: Fl,
        fwd: bool,
        x: &State,
        c: Cont<'_>,
    ) -> Option<State> {
        let idx = if fwd { x.end } else { x.end.checked_sub(1)? };
        let ch = *self.input.chars.get(idx)?;
        let found = if fl.ic {
            self.equivalents(ch).into_iter().any(pred)
        } else {
            pred(ch)
        };
        if found == invert {
            return None;
        }
        let end = if fwd { x.end.saturating_add(1) } else { idx };
        c(State {
            end,
            caps: x.caps.clone(),
        })
    }

    fn escape_has(&self, e: &ClassEscape, a: u32, fl: Fl) -> bool {
        match e {
            ClassEscape::Digit => (0x30..=0x39).contains(&a),
            ClassEscape::NotDigit => !(0x30..=0x39).contains(&a),
            ClassEscape::Space => is_space(a),
            ClassEscape::NotSpace => !is_space(a),
            ClassEscape::Word => self.is_word(a, fl),
            ClassEscape::NotWord => !self.is_word(a, fl),
            ClassEscape::Property { negated, property } => {
                self.property_has(property, a) != *negated
            }
        }
    }

    fn property_has(&self, p: &Property, a: u32) -> bool {
        match p {
            Property::GeneralCategory(v) => {
                category_mask(v).is_some_and(|m| Prop::Category(m).contains(a))
            }
            Property::Binary(n) => binary_property(n).is_some_and(|p| p.contains(a)),
            Property::Script(v) => script_property(v, false).is_some_and(|p| p.contains(a)),
            Property::ScriptExtensions(v) => {
                script_property(v, true).is_some_and(|p| p.contains(a))
            }
            // The members of one character (the longer ones are `has_multi`'s).
            Property::Strings(n) => string_property(n).is_some_and(|s| s.chars.contains(a)),
        }
    }

    /// Whether the string `s` (not one character, already Canonicalized with
    /// `i`) is an element of the set of an operand: CompileToCharSet
    /// (§22.2.2.7†) with strings, read as a predicate on strings.
    fn operand_has_multi(&self, o: &ClassSetOperand, s: &[u32], fl: Fl) -> bool {
        let same = |t: &[u32]| {
            t.len() == s.len()
                && t.iter()
                    .zip(s)
                    .all(|(&a, &b)| if fl.ic { self.canon(a) == b } else { a == b })
        };
        match o {
            ClassSetOperand::Char(_) => false,
            ClassSetOperand::Escape(ClassEscape::Property {
                property: Property::Strings(n),
                ..
            }) => string_property(n).is_some_and(|set| set.strings.iter().any(|t| same(t))),
            ClassSetOperand::Escape(_) => false,
            ClassSetOperand::Nested { negated, expr } => !*negated && self.has_multi(expr, s, fl),
            ClassSetOperand::Strings(list) => list.iter().any(|t| same(t)),
        }
    }

    /// [`Self::operand_has_multi`] for an expression.
    fn has_multi(&self, e: &ClassSetExpr, s: &[u32], fl: Fl) -> bool {
        match e {
            ClassSetExpr::Union(items) => items.iter().any(|it| match it {
                ClassSetItem::Operand(o) => self.operand_has_multi(o, s, fl),
                ClassSetItem::Range(..) => false,
            }),
            ClassSetExpr::Intersection(os) => os.iter().all(|o| self.operand_has_multi(o, s, fl)),
            ClassSetExpr::Subtraction(os) => match os.split_first() {
                Some((first, rest)) => {
                    self.operand_has_multi(first, s, fl)
                        && !rest.iter().any(|o| self.operand_has_multi(o, s, fl))
                }
                None => false,
            },
        }
    }

    /// A `v` class that may contain strings, as CompileAtom (§22.2.2.7†)
    /// builds it: the strings of the set that are not one character,
    /// longest first; then the characters; then the empty string, if the set
    /// has it. A string is tried as the input's slice of its length, which is
    /// the only string of that length that can match there.
    fn set_with_strings(
        &self,
        expr: &ClassSetExpr,
        fl: Fl,
        fwd: bool,
        x: &State,
        c: Cont<'_>,
    ) -> Option<State> {
        let avail = if fwd {
            self.input.chars.len().saturating_sub(x.end)
        } else {
            x.end
        };
        for len in (2..=avail.min(32)).rev() {
            if !self.burn() {
                return None;
            }
            let slice = if fwd {
                self.input.chars.get(x.end..x.end.saturating_add(len))?
            } else {
                self.input.chars.get(x.end.checked_sub(len)?..x.end)?
            };
            let s: Vec<u32> = slice
                .iter()
                .map(|&ch| if fl.ic { self.canon(ch) } else { ch })
                .collect();
            if self.has_multi(expr, &s, fl) {
                let end = if fwd {
                    x.end.saturating_add(len)
                } else {
                    x.end.saturating_sub(len)
                };
                if let Some(r) = c(State {
                    end,
                    caps: x.caps.clone(),
                }) {
                    return Some(r);
                }
            }
        }
        if avail >= 1 {
            let idx = if fwd { x.end } else { x.end.saturating_sub(1) };
            let ch = *self.input.chars.get(idx)?;
            let cc = if fl.ic { self.canon(ch) } else { ch };
            if self.vset_has(expr, cc, fl) {
                let end = if fwd { x.end.saturating_add(1) } else { idx };
                if let Some(r) = c(State {
                    end,
                    caps: x.caps.clone(),
                }) {
                    return Some(r);
                }
            }
        }
        if self.has_multi(expr, &[], fl) {
            return c(x.clone());
        }
        None
    }

    /// A positive escape (for `v`, where negation is the complement of the
    /// folded set).
    fn positive_escape_has(&self, e: &ClassEscape, a: u32, fl: Fl) -> bool {
        match e {
            ClassEscape::Digit | ClassEscape::NotDigit => (0x30..=0x39).contains(&a),
            ClassEscape::Space | ClassEscape::NotSpace => is_space(a),
            ClassEscape::Word | ClassEscape::NotWord => self.is_word(a, fl),
            ClassEscape::Property { property, .. } => self.property_has(property, a),
        }
    }

    fn is_negated_escape(e: &ClassEscape) -> bool {
        matches!(
            e,
            ClassEscape::NotDigit
                | ClassEscape::NotSpace
                | ClassEscape::NotWord
                | ClassEscape::Property { negated: true, .. }
        )
    }

    /// Membership in a `v` set, with the standard's folding: with `i`, the set
    /// is the Canonicalize of each element, and `target` is the input
    /// character's Canonicalize.
    fn vset_has(&self, e: &ClassSetExpr, target: u32, fl: Fl) -> bool {
        let same = |a: u32| {
            if fl.ic {
                self.canon(a) == target
            } else {
                a == target
            }
        };
        let operand = |o: &ClassSetOperand| -> bool {
            match o {
                ClassSetOperand::Char(c) => same(*c),
                ClassSetOperand::Escape(esc) => {
                    let pos = self.exists(target, fl, |a| self.positive_escape_has(esc, a, fl));
                    pos != Self::is_negated_escape(esc)
                }
                ClassSetOperand::Nested { negated, expr } => {
                    self.vset_has(expr, target, fl) != *negated
                }
                ClassSetOperand::Strings(list) => {
                    list.iter().any(|s| matches!(s.as_slice(), [c] if same(*c)))
                }
            }
        };
        match e {
            ClassSetExpr::Union(items) => items.iter().any(|it| match it {
                ClassSetItem::Operand(o) => operand(o),
                ClassSetItem::Range(lo, hi) => {
                    if fl.ic {
                        (*lo..=*hi).any(&same)
                    } else {
                        *lo <= target && target <= *hi
                    }
                }
            }),
            ClassSetExpr::Intersection(os) => os.iter().all(operand),
            ClassSetExpr::Subtraction(os) => match os.split_first() {
                Some((first, rest)) => operand(first) && !rest.iter().any(operand),
                None => false,
            },
        }
    }

    /// Whether some character that Canonicalizes to `target` (with `i`) or is
    /// `target` (without) satisfies `f`.
    fn exists(&self, target: u32, fl: Fl, f: impl Fn(u32) -> bool) -> bool {
        if fl.ic {
            self.equivalents(target).into_iter().any(f)
        } else {
            f(target)
        }
    }

    fn atom(&self, a: &Atom, fl: Fl, fwd: bool, x: &State, c: Cont<'_>) -> Option<State> {
        match a {
            Atom::Char(ch) => self.set(&|a| a == *ch, false, fl, fwd, x, c),
            Atom::Dot => {
                let idx = if fwd { x.end } else { x.end.checked_sub(1)? };
                let ch = *self.input.chars.get(idx)?;
                if !fl.dot_all && is_lt(ch) {
                    return None;
                }
                let end = if fwd { x.end.saturating_add(1) } else { idx };
                c(State {
                    end,
                    caps: x.caps.clone(),
                })
            }
            Atom::Escape(e) if e.may_contain_strings() => {
                let expr = ClassSetExpr::Union(vec![ClassSetItem::Operand(
                    ClassSetOperand::Escape(e.clone()),
                )]);
                self.set_with_strings(&expr, fl, fwd, x, c)
            }
            Atom::Escape(e) => {
                if self.v_mode() && Self::is_negated_escape(e) {
                    // `\P{..}` with `v`: the complement of the folded set.
                    let idx = if fwd { x.end } else { x.end.checked_sub(1)? };
                    let ch = *self.input.chars.get(idx)?;
                    let cc = if fl.ic { self.canon(ch) } else { ch };
                    let pos = self.exists(cc, fl, |a| self.positive_escape_has(e, a, fl));
                    return if pos {
                        None
                    } else {
                        let end = if fwd { x.end.saturating_add(1) } else { idx };
                        c(State {
                            end,
                            caps: x.caps.clone(),
                        })
                    };
                }
                self.set(&|a| self.escape_has(e, a, fl), false, fl, fwd, x, c)
            }
            Atom::Class(cls) => match &cls.contents {
                ClassContents::Ranges(items) => {
                    let pred = |a: u32| {
                        items.iter().any(|it| match it {
                            ClassItem::Char(ch) => a == *ch,
                            ClassItem::Range(lo, hi) => *lo <= a && a <= *hi,
                            ClassItem::Escape(e) => self.escape_has(e, a, fl),
                        })
                    };
                    self.set(&pred, cls.negated, fl, fwd, x, c)
                }
                ClassContents::Set(expr) if !cls.negated && expr.may_contain_strings() => {
                    self.set_with_strings(expr, fl, fwd, x, c)
                }
                ClassContents::Set(expr) => {
                    let idx = if fwd { x.end } else { x.end.checked_sub(1)? };
                    let ch = *self.input.chars.get(idx)?;
                    let cc = if fl.ic { self.canon(ch) } else { ch };
                    let has = self.vset_has(expr, cc, fl) != cls.negated;
                    if !has {
                        return None;
                    }
                    let end = if fwd { x.end.saturating_add(1) } else { idx };
                    c(State {
                        end,
                        caps: x.caps.clone(),
                    })
                }
            },
            Atom::Group(g) => {
                let after = |y: State| -> Option<State> {
                    match g.index {
                        None => c(y),
                        Some(i) => {
                            let (s, e) = if fwd { (x.end, y.end) } else { (y.end, x.end) };
                            let mut caps = y.caps.clone();
                            if let Some(slot) = caps.get_mut(i as usize) {
                                *slot = Some((s, e));
                            }
                            c(State { end: y.end, caps })
                        }
                    }
                };
                self.disj(&g.body, fl, fwd, x, &after)
            }
            Atom::Modified(m) => {
                let flag = |cur: bool, add: bool, remove: bool| (cur || add) && !remove;
                let inner = Fl {
                    ic: flag(fl.ic, m.add.ignore_case, m.remove.ignore_case),
                    ml: flag(fl.ml, m.add.multiline, m.remove.multiline),
                    dot_all: flag(fl.dot_all, m.add.dot_all, m.remove.dot_all),
                };
                self.disj(&m.body, inner, fwd, x, c)
            }
            Atom::BackReference(n) => self.backref(&[*n], fl, fwd, x, c),
            Atom::NamedBackReference(name) => {
                let ns: Vec<u32> = self
                    .names()
                    .iter()
                    .filter(|(n, _)| n == name)
                    .map(|&(_, i)| i)
                    .collect();
                self.backref(&ns, fl, fwd, x, c)
            }
        }
    }

    /// BackreferenceMatcher (§22.2.2.7.2†), over the first group of `ns` that
    /// has a capture.
    fn backref(&self, ns: &[u32], fl: Fl, fwd: bool, x: &State, c: Cont<'_>) -> Option<State> {
        let r = ns
            .iter()
            .find_map(|&n| x.caps.get(n as usize).copied().flatten());
        let Some((rs, re)) = r else {
            return c(x.clone());
        };
        let len = re.checked_sub(rs)?;
        let e = x.end;
        let f = if fwd {
            e.checked_add(len)?
        } else {
            e.checked_sub(len)?
        };
        if f > self.input.chars.len() {
            return None;
        }
        let g = e.min(f);
        for i in 0..len {
            let a = *self.input.chars.get(rs.checked_add(i)?)?;
            let b = *self.input.chars.get(g.checked_add(i)?)?;
            let (a, b) = if fl.ic {
                (self.canon(a), self.canon(b))
            } else {
                (a, b)
            };
            if a != b {
                return None;
            }
        }
        c(State {
            end: f,
            caps: x.caps.clone(),
        })
    }

    fn v_mode(&self) -> bool {
        V_MODE.with(Cell::get)
    }

    fn names(&self) -> Vec<(Vec<u32>, u32)> {
        NAMES.with(|n| n.borrow().clone())
    }
}

thread_local! {
    static V_MODE: Cell<bool> = const { Cell::new(false) };
    static NAMES: RefCell<Vec<(Vec<u32>, u32)>> = const { RefCell::new(Vec::new()) };
}

/// The reference's answer for a match starting at character `start`:
/// the captures in code unit indices, or `Err` if it ran out of fuel.
fn reference_at(
    pattern: &Pattern,
    flags: Flags,
    input: &Input,
    start: usize,
) -> Result<Option<Caps>, ()> {
    V_MODE.with(|v| v.set(flags.unicode_sets));
    NAMES.with(|n| *n.borrow_mut() = pattern.group_names.clone());
    let r = Reference {
        input,
        unicode: flags.unicode_mode(),
        fuel: Cell::new(300_000),
        memo: RefCell::new(HashMap::new()),
    };
    let fl = Fl {
        ic: flags.ignore_case,
        ml: flags.multiline,
        dot_all: flags.dot_all,
    };
    let x = State {
        end: start,
        caps: vec![None; (pattern.capture_count as usize).saturating_add(1)],
    };
    let res = r.disj(&pattern.disjunction, fl, true, &x, &Some);
    if r.exhausted() {
        return Err(());
    }
    let to_unit = |i: usize| input.pos.get(i).copied().unwrap_or(usize::MAX);
    Ok(res.map(|st| {
        let mut caps: Caps = st
            .caps
            .iter()
            .map(|c| c.map(|(s, e)| (to_unit(s), to_unit(e))))
            .collect();
        if let Some(first) = caps.first_mut() {
            *first = Some((to_unit(start), to_unit(st.end)));
        }
        caps
    }))
}

// ---------------------------------------------------------------------------
// Random patterns and inputs.

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x.wrapping_shr(12);
        x ^= x.wrapping_shl(25);
        x ^= x.wrapping_shr(27);
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(1).max(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    fn pick<'a, T>(&mut self, list: &'a [T]) -> Option<&'a T> {
        list.get(self.below(list.len()))
    }
}

const LETTERS: &[&str] = &["a", "b", "c", "a", "b", "A", "B"];
const SPECIAL: &[&str] = &[
    "k", "K", "\u{212a}", "s", "S", "\u{17f}", "\u{e9}", "\u{c9}", "1", "_", " ", "-",
];
const ASTRAL: &[&str] = &["\u{1F600}", "\u{10400}", "\u{10428}"];

struct Gen<'r> {
    rng: &'r mut Rng,
    unicode: bool,
    v: bool,
    groups: u32,
    names: u32,
}

impl Gen<'_> {
    fn s(&mut self, list: &[&str]) -> String {
        self.rng.pick(list).copied().unwrap_or("a").to_string()
    }

    fn literal(&mut self) -> String {
        let r = self.rng.below(100);
        if r < 70 {
            self.s(LETTERS)
        } else if r < 92 || !self.unicode {
            self.s(SPECIAL)
        } else {
            self.s(ASTRAL)
        }
    }

    fn disjunction(&mut self, depth: u32) -> String {
        let n = if self.rng.chance(35) {
            self.rng.below(2).saturating_add(2)
        } else {
            1
        };
        let alts: Vec<String> = (0..n).map(|_| self.alternative(depth)).collect();
        alts.join("|")
    }

    fn alternative(&mut self, depth: u32) -> String {
        let n = self.rng.below(4);
        (0..n).map(|_| self.term(depth)).collect()
    }

    fn quantifier(&mut self) -> String {
        let q = self
            .rng
            .pick(&[
                "*", "+", "?", "{1,2}", "{0,2}", "{2}", "{2,}", "{0,1}", "{1}",
            ])
            .copied()
            .unwrap_or("*");
        let lazy = if self.rng.chance(30) { "?" } else { "" };
        format!("{q}{lazy}")
    }

    fn term(&mut self, depth: u32) -> String {
        let r = self.rng.below(100);
        let (text, quantifiable) = if r < 36 {
            (self.literal(), true)
        } else if r < 44 {
            (".".to_string(), true)
        } else if r < 56 {
            (self.class(), true)
        } else if r < 62 {
            (self.escape(), true)
        } else if r < 78 && depth < 3 {
            (self.group(depth), true)
        } else if r < 85 && depth < 3 {
            self.look(depth)
        } else if r < 92 {
            (self.s(&["^", "$", "\\b", "\\B"]), false)
        } else {
            (self.backref(), true)
        };
        if quantifiable && self.rng.chance(35) {
            format!("{text}{}", self.quantifier())
        } else {
            text
        }
    }

    fn escape(&mut self) -> String {
        let mut list: Vec<&str> = vec!["\\d", "\\w", "\\s", "\\D", "\\W", "\\S"];
        if self.unicode {
            list.extend([
                "\\p{Lu}",
                "\\P{Lu}",
                "\\p{L}",
                "\\p{Ll}",
                "\\p{sc=Latin}",
                "\\P{sc=Greek}",
                "\\p{scx=Grek}",
                "\\P{scx=Greek}",
                "\\p{Script=Cyrillic}",
                "\\p{scx=Latn}",
                "\\p{sc=Zinh}",
                "\\p{Lowercase}",
            ]);
        }
        if self.v {
            list.extend([
                "\\p{RGI_Emoji}",
                "\\p{Emoji_Keycap_Sequence}",
                "\\p{Basic_Emoji}",
                "\\p{RGI_Emoji_Flag_Sequence}",
                "\\p{RGI_Emoji_ZWJ_Sequence}",
            ]);
        }
        self.s(&list)
    }

    /// `\q{..}` (`v`): strings of several lengths, some empty.
    fn v_string(&mut self) -> String {
        self.s(&[
            "\\q{ab|c}",
            "\\q{ab|abc|a}",
            "\\q{ba|}",
            "\\q{\u{1F600}a|b}",
            "\\q{A\u{3b9}|\u{345}}",
        ])
    }

    fn backref(&mut self) -> String {
        if self.names > 0 && self.rng.chance(40) {
            let n = self.rng.below(self.names as usize).saturating_add(1);
            format!("\\k<n{n}>")
        } else {
            format!("\\{}", self.rng.below(3).saturating_add(1))
        }
    }

    fn group(&mut self, depth: u32) -> String {
        let r = self.rng.below(100);
        if r < 45 {
            self.groups = self.groups.saturating_add(1);
            format!("({})", self.disjunction(depth.saturating_add(1)))
        } else if r < 62 {
            self.names = self.names.saturating_add(1);
            self.groups = self.groups.saturating_add(1);
            let n = self.names;
            format!("(?<n{n}>{})", self.disjunction(depth.saturating_add(1)))
        } else if r < 88 {
            format!("(?:{})", self.disjunction(depth.saturating_add(1)))
        } else {
            let m = self
                .rng
                .pick(&["i", "-i", "s", "-s", "m", "-m", "i-s", "s-i", "ms"])
                .copied()
                .unwrap_or("i");
            format!("(?{m}:{})", self.disjunction(depth.saturating_add(1)))
        }
    }

    fn look(&mut self, depth: u32) -> (String, bool) {
        let kind = self
            .rng
            .pick(&["=", "!", "<=", "<!"])
            .copied()
            .unwrap_or("=");
        let body = self.disjunction(depth.saturating_add(1));
        // Annex B: only a lookahead may be quantified, and not with `u`/`v`.
        let ahead = !kind.starts_with('<');
        (
            format!("(?{kind}{body})"),
            ahead && !self.unicode && self.rng.chance(20),
        )
    }

    fn class_char(&mut self) -> String {
        self.s(&["a", "b", "c", "A", "B", "k", "s", "1", "_", "\u{e9}"])
    }

    fn class(&mut self) -> String {
        let neg = if self.rng.chance(25) { "^" } else { "" };
        if self.v {
            return format!("[{neg}{}]", self.v_contents(0));
        }
        let n = self.rng.below(3).saturating_add(1);
        let items: String = (0..n)
            .map(|_| {
                let r = self.rng.below(100);
                if r < 50 {
                    self.class_char()
                } else if r < 80 {
                    self.s(&["a-c", "b-b", "A-C", "0-9", "a-z", "A-Z", "\u{c0}-\u{ff}"])
                } else {
                    self.escape()
                }
            })
            .collect();
        format!("[{neg}{items}]")
    }

    /// The contents of a `v` class: a union, an intersection or a subtraction.
    fn v_contents(&mut self, depth: u32) -> String {
        let r = self.rng.below(100);
        if r < 55 || depth >= 2 {
            let n = self.rng.below(3).saturating_add(1);
            (0..n)
                .map(|_| {
                    let r = self.rng.below(100);
                    if r < 40 {
                        self.class_char()
                    } else if r < 65 {
                        self.s(&["a-c", "A-C", "0-9", "a-z"])
                    } else if r < 74 {
                        self.escape()
                    } else if r < 82 {
                        self.v_string()
                    } else {
                        format!("[{}]", self.v_contents(depth.saturating_add(1)))
                    }
                })
                .collect()
        } else {
            let op = if r < 78 { "&&" } else { "--" };
            let n = self.rng.below(2).saturating_add(2);
            let operands: Vec<String> = (0..n)
                .map(|_| {
                    let r = self.rng.below(100);
                    if r < 40 {
                        format!("[{}]", self.v_contents(depth.saturating_add(1)))
                    } else if r < 55 {
                        self.escape()
                    } else if r < 65 {
                        self.v_string()
                    } else if r < 80 {
                        format!("[^{}]", self.class_char())
                    } else {
                        self.class_char()
                    }
                })
                .collect();
            operands.join(op)
        }
    }
}

const INPUT_CHARS: &[&str] = &[
    "a",
    "b",
    "c",
    "a",
    "b",
    "A",
    "B",
    "k",
    "K",
    "\u{212a}",
    "s",
    "S",
    "\u{17f}",
    "\u{e9}",
    "\u{c9}",
    "1",
    "_",
    " ",
    "\n",
    "-",
    "\u{1F600}",
    "\u{3b1}",
    "\u{3b9}",
    "\u{399}",
    "\u{345}",
    "\u{b7}",
    "\u{430}",
    "\u{fe0f}",
    "1\u{fe0f}\u{20e3}",
    "\u{1F1E6}\u{1F1E8}",
    "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}",
    "\u{263a}\u{fe0f}",
    "\u{10400}",
    "\u{10428}",
];

fn random_input(rng: &mut Rng, max_len: usize) -> String {
    let n = rng.below(max_len.saturating_add(1));
    (0..n)
        .map(|_| rng.pick(INPUT_CHARS).copied().unwrap_or("a"))
        .collect()
}

/// The three kinds of mode, so each gets a share of the patterns.
fn random_flags(rng: &mut Rng) -> (String, Flags) {
    let mut s = String::new();
    for (flag, pct) in [('i', 50), ('m', 30), ('s', 30)] {
        if rng.chance(pct) {
            s.push(flag);
        }
    }
    match rng.below(10) {
        0..=2 => s.push('u'),
        3 | 4 => s.push('v'),
        _ => {}
    }
    let units: Vec<u16> = s.encode_utf16().collect();
    let f = Flags::parse(&units).unwrap_or_default();
    (s, f)
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

struct Tally {
    patterns: usize,
    parse_errors: usize,
    compile_errors: usize,
    compared: usize,
    matched: usize,
    out_of_fuel: usize,
}

/// A pattern under test.
struct Subject<'a> {
    pattern: &'a str,
    flag_text: &'a str,
    flags: Flags,
    pat: &'a Pattern,
    prog: &'a Program,
}

fn compare_one(
    subject: &Subject<'_>,
    input_text: &str,
    tally: &mut Tally,
    rng: &mut Rng,
) -> Result<(), String> {
    let Subject {
        pattern,
        flag_text,
        flags,
        pat,
        prog,
    } = *subject;
    let text = units(input_text);
    let input = decode(&text, flags.unicode_mode());
    // The standard scan: the first start index (in characters) that matches.
    let mut expected: Option<Caps> = None;
    for k in 0..=input.chars.len() {
        match reference_at(pat, flags, &input, k) {
            Ok(Some(c)) => {
                expected = Some(c);
                break;
            }
            Ok(None) => {}
            Err(()) => {
                tally.out_of_fuel = tally.out_of_fuel.saturating_add(1);
                return Ok(());
            }
        }
    }
    let limits = Limits {
        max_stack: 1 << 20,
        max_steps: Some(50_000_000),
    };
    let got = prog
        .exec(&text, 0, false, &limits, None)
        .map_err(|e| format!("/{pattern}/{flag_text} on {input_text:?}: {e}"))?;
    tally.compared = tally.compared.saturating_add(1);
    if got.is_some() {
        tally.matched = tally.matched.saturating_add(1);
    }
    if got.map(|m| m.captures) != expected {
        return Err(format!(
            "/{pattern}/{flag_text} on {input_text:?} (scan): got {:?}, reference {expected:?}",
            prog.exec(&text, 0, false, &limits, None)
                .ok()
                .flatten()
                .map(|m| m.captures)
        ));
    }
    // A sticky match at one start index, chosen at random among the
    // characters' boundaries.
    let k = rng.below(input.chars.len().saturating_add(1));
    let start = input.pos.get(k).copied().unwrap_or(0);
    let want = match reference_at(pat, flags, &input, k) {
        Ok(c) => c,
        Err(()) => return Ok(()),
    };
    let got = prog
        .exec(&text, start, true, &limits, None)
        .map_err(|e| format!("/{pattern}/{flag_text} on {input_text:?} at {start}: {e}"))?;
    if got.map(|m| m.captures) != want {
        return Err(format!(
            "/{pattern}/{flag_text} on {input_text:?} sticky at {start}: differs from the reference ({want:?})"
        ));
    }
    Ok(())
}

fn run_differential(
    seed: u64,
    patterns: usize,
    inputs: usize,
    max_len: usize,
) -> Result<Tally, String> {
    let mut rng = Rng(seed);
    let mut tally = Tally {
        patterns: 0,
        parse_errors: 0,
        compile_errors: 0,
        compared: 0,
        matched: 0,
        out_of_fuel: 0,
    };
    for _ in 0..patterns {
        let (flag_text, flags) = random_flags(&mut rng);
        let text = {
            let mut g = Gen {
                rng: &mut rng,
                unicode: flags.unicode_mode(),
                v: flags.unicode_sets,
                groups: 0,
                names: 0,
            };
            g.disjunction(0)
        };
        tally.patterns = tally.patterns.saturating_add(1);
        let Ok(pat) = parse(&units(&text), flags) else {
            tally.parse_errors = tally.parse_errors.saturating_add(1);
            continue;
        };
        let Ok(prog) = compile(&pat, flags) else {
            tally.compile_errors = tally.compile_errors.saturating_add(1);
            continue;
        };
        for _ in 0..inputs {
            let input = random_input(&mut rng, max_len);
            let subject = Subject {
                pattern: &text,
                flag_text: &flag_text,
                flags,
                pat: &pat,
                prog: &prog,
            };
            compare_one(&subject, &input, &mut tally, &mut rng)?;
        }
    }
    Ok(tally)
}

#[test]
fn matcher_agrees_with_the_reference() -> Result<(), String> {
    let (patterns, inputs) = if cfg!(miri) { (10, 2) } else { (6000, 8) };
    let mut total = Tally {
        patterns: 0,
        parse_errors: 0,
        compile_errors: 0,
        compared: 0,
        matched: 0,
        out_of_fuel: 0,
    };
    for seed in [0x9E37_79B9_7F4A_7C15u64, 0xD1B5_4A32_D192_ED03] {
        let t = run_differential(seed, patterns, inputs, 7)?;
        total.patterns = total.patterns.saturating_add(t.patterns);
        total.parse_errors = total.parse_errors.saturating_add(t.parse_errors);
        total.compile_errors = total.compile_errors.saturating_add(t.compile_errors);
        total.compared = total.compared.saturating_add(t.compared);
        total.matched = total.matched.saturating_add(t.matched);
        total.out_of_fuel = total.out_of_fuel.saturating_add(t.out_of_fuel);
    }
    println!(
        "clazel-conformance: suite=\"differential vs reference matcher\" pass={} xfail=0 fail=0 total={}",
        total.compared, total.compared
    );
    println!(
        "differential: {} patterns, {} parse errors, {} compile errors, {} comparisons ({} with a match), {} out of fuel",
        total.patterns,
        total.parse_errors,
        total.compile_errors,
        total.compared,
        total.matched,
        total.out_of_fuel
    );
    // The test must not be vacuous.
    assert!(total.compared > total.patterns / 2, "too few comparisons");
    assert!(
        total.matched.saturating_mul(10) > total.compared,
        "fewer than a tenth of the comparisons found a match"
    );
    assert!(total.out_of_fuel.saturating_mul(20) < total.compared);
    Ok(())
}

/// Patterns that put `Script`, `Script_Extensions` and the properties of
/// strings where the order of the alternatives or the folding matters, run on
/// every input of up to a few tokens from a small alphabet. The random
/// differential reaches them only by chance.
#[test]
fn properties_and_strings_agree_with_the_reference() -> Result<(), String> {
    // (pattern, flags)
    let cases: &[(&str, &str)] = &[
        ("\\p{sc=Greek}+", "u"),
        ("\\P{sc=Greek}", "u"),
        ("\\P{sc=Greek}", "iu"),
        ("\\P{sc=Greek}", "iv"),
        ("\\p{scx=Greek}+", "u"),
        ("\\P{scx=Greek}", "iu"),
        ("\\p{scx=Grek}", "iv"),
        ("\\p{sc=Inherited}", "u"),
        ("\\p{sc=Common}\\p{scx=Latin}?", "u"),
        ("[\\p{sc=Greek}--\\p{Lu}]+", "v"),
        ("[\\p{sc=Greek}&&\\p{Lu}]", "iv"),
        ("[^\\p{scx=Greek}]", "iv"),
        ("[\\q{ab|a}]b", "v"),
        ("[\\q{a|ab|abc}]c", "v"),
        ("^(?:[\\q{ab|a}]|b)(b*)$", "v"),
        ("[\\q{ab|a|}]*c", "v"),
        ("(?<=[\\q{ab|b}])c", "v"),
        ("[\\q{AB|a}]b", "iv"),
        ("[\\q{ab|abc|a}--\\q{ab}]c?", "v"),
        ("[\\q{ab|abc}&&\\q{abc|a}]", "v"),
        ("\\p{Emoji_Keycap_Sequence}", "v"),
        ("\\p{Emoji_Keycap_Sequence}\\p{Emoji_Keycap_Sequence}?", "v"),
        ("(\\p{Emoji_Keycap_Sequence}|1)\\u{FE0F}", "v"),
        ("\\p{RGI_Emoji}\\u{200D}", "v"),
        ("\\p{RGI_Emoji}+$", "v"),
        ("^\\p{RGI_Emoji}$", "iv"),
        ("(?<=\\p{RGI_Emoji})x", "v"),
        ("\\p{Basic_Emoji}\\p{Basic_Emoji}?", "v"),
        ("[\\p{RGI_Emoji}--\\q{\u{1F1E6}\u{1F1E8}}]", "v"),
        (
            "[\\p{RGI_Emoji_Flag_Sequence}&&\\q{\u{1F1E6}\u{1F1E8}|a}]",
            "v",
        ),
        ("[\\p{Basic_Emoji}--\\p{Emoji_Keycap_Sequence}]", "v"),
        ("\\p{RGI_Emoji_ZWJ_Sequence}", "v"),
        ("\\p{RGI_Emoji}{2}", "v"),
    ];
    let alphabet: &[&str] = &[
        "a",
        "b",
        "A",
        "c",
        "x",
        "1",
        "\u{3b9}",
        "\u{399}",
        "\u{345}",
        "\u{b7}",
        "\u{fe0f}",
        "\u{200d}",
        "1\u{fe0f}\u{20e3}",
        "\u{1F1E6}\u{1F1E8}",
        "\u{1F468}",
        "\u{1F468}\u{200D}\u{1F469}",
        "\u{1F600}",
        "\u{263a}\u{fe0f}",
    ];
    let len = if cfg!(miri) { 1 } else { 3 };
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    let mut tally = Tally {
        patterns: 0,
        parse_errors: 0,
        compile_errors: 0,
        compared: 0,
        matched: 0,
        out_of_fuel: 0,
    };
    // Every sequence of up to `len` tokens.
    let mut inputs: Vec<(usize, String)> = vec![(0, String::new())];
    // And the ones that make the alternatives' order show: more than one
    // string of the set matches at a start, and they end differently.
    for s in [
        "abb",
        "abc",
        "abcc",
        "abbc",
        "aabbc",
        "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}x",
        "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F467}\u{200D}",
        "\u{1F468}\u{200D}\u{1F469}\u{200D}\u{1F466}\u{200D}\u{1F466}",
        "1\u{fe0f}\u{20e3}1\u{fe0f}\u{20e3}x",
        "\u{1F1E6}\u{1F1E8}\u{1F1E6}\u{1F1E8}a",
        "\u{263a}\u{fe0f}\u{263a}\u{fe0f}",
        "A\u{3b9}\u{345}\u{399}",
    ] {
        inputs.push((0, s.to_string()));
    }
    let mut layer: Vec<String> = vec![String::new()];
    for n in 1..=len {
        let mut next = Vec::new();
        for p in &layer {
            for t in alphabet {
                next.push(format!("{p}{t}"));
            }
        }
        inputs.extend(next.iter().map(|s| (n, s.clone())));
        layer = next;
    }
    let mut idle = Vec::new();
    for &(pattern, flag_text) in cases {
        let flags = Flags::parse(&units(flag_text)).map_err(|e| format!("{e:?}"))?;
        let pat = parse(&units(pattern), flags).map_err(|e| format!("/{pattern}/: {e}"))?;
        let prog = compile(&pat, flags).map_err(|e| format!("/{pattern}/: {e}"))?;
        let before = tally.matched;
        for (n, input) in &inputs {
            // The longest inputs are many: take a twenty-fifth of them.
            if *n > 2 && rng.below(25) != 0 {
                continue;
            }
            let subject = Subject {
                pattern,
                flag_text,
                flags,
                pat: &pat,
                prog: &prog,
            };
            compare_one(&subject, input, &mut tally, &mut rng)?;
        }
        if tally.matched == before {
            idle.push(format!("/{pattern}/{flag_text} matched no input"));
        }
    }
    println!(
        "clazel-conformance: suite=\"differential: scripts and strings\" pass={} xfail=0 fail=0 total={}",
        tally.compared, tally.compared
    );
    // Every pattern must match something, or it tests nothing.
    assert!(idle.is_empty(), "{}", idle.join("\n"));
    assert!(tally.out_of_fuel.saturating_mul(20) < tally.compared);
    Ok(())
}
