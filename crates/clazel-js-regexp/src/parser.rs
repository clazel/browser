//! The pattern parser: ECMA-262 §22.2.1† (the pattern grammar), Annex B
//! §B.1.2† (its web-compatibility grammar, without `u` or `v`) and §22.2.1.1†
//! (its early errors).
//!
//! # Modelling choices
//!
//! - **Input.** A pattern is UTF-16 code units. With `u` or `v` the grammar's
//!   source characters are code points (a surrogate pair is one character; a
//!   lone surrogate is itself); without, each code unit is one (§22.2.3.4†
//!   RegExpInitialize, "patternText"). Group names are read as code points in
//!   both modes (RegExpIdentifierStart's `UnicodeLeadSurrogate
//!   UnicodeTrailSurrogate` alternative).
//! - **The parameters `[UnicodeMode]`, `[UnicodeSetsMode]`,
//!   `[NamedCaptureGroups]`** are fields of the parser. `u` or `v` sets
//!   `UnicodeMode`; `v` sets `UnicodeSetsMode`; `NamedCaptureGroups` is
//!   always on with `u` or `v`, and otherwise on only if a first parse found
//!   a group name (§22.2.3.4†, "parse again with `+NamedCaptureGroups`").
//! - **"Only if" in AtomEscape (Annex B).** `\n` is a backreference only if
//!   `n` is at most the pattern's number of capturing groups
//!   (CountLeftCapturingParensWithin). Without `u` or `v` that count comes
//!   from the first parse, which reads every `\n` as a backreference: the
//!   count does not depend on that choice, because an octal escape or an
//!   identity escape holds no parenthesis.
//! - **Early errors that quantify over the whole Pattern** (undeclared
//!   `\k<name>`, a backreference beyond the last group with `u` or `v`,
//!   duplicate group names) are checked after the parse, over what it
//!   recorded.
//! - **A recursive-descent parser** reads the grammar's productions directly
//!   (the alternatives are separated by the longest-match the standard's
//!   lookaheads imply), with the nesting of groups, lookarounds and classes
//!   bounded by [`MAX_DEPTH`]; deeper patterns are rejected with
//!   [`ErrorKind::TooDeep`], a deviation, because the standard has no limit.
//! - **Quantifier bounds** above `u64::MAX` are stored as `u64::MAX`; the
//!   out-of-order early error compares the digits exactly.
//! - **Property names** are checked as [`crate::props`] says.
//!
//! The section numbers are marked † (phase-7.md's convention): they are from
//! memory, because the specification's text is not vendored
//! (`clazel-js-lexer/SPEC-PIN.md`) and no tool here reads it.

use std::collections::BTreeSet;

use crate::ast::{
    Alternative, Assertion, Atom, CharacterClass, ClassContents, ClassEscape, ClassItem,
    ClassSetExpr, ClassSetItem, ClassSetOperand, Disjunction, Group, Look, ModifiedGroup,
    Modifiers, Pattern, Property, Quantifier, Term, TermKind,
};
use crate::error::{Error, ErrorKind};
use crate::flags::Flags;
use crate::props::{self, Names};

/// The deepest nesting of groups, lookarounds and classes the parser reads:
/// a pattern with more is rejected with [`ErrorKind::TooDeep`].
pub const MAX_DEPTH: usize = 128;

type R<T> = Result<T, Error>;

#[cfg(kani)]
mod proofs;

/// Parses `pattern` (UTF-16 code units) with `flags`, accepting every
/// syntactically valid `Script` value in `\p{sc=..}`.
///
/// ECMA-262 §22.2.3.4† RegExpInitialize step 7 (ParsePattern) and §22.2.1†,
/// with the early errors of §22.2.1.1†.
///
/// # Errors
///
/// [`Error`] if the pattern is a Syntax Error.
pub fn parse(pattern: &[u16], flags: Flags) -> Result<Pattern, Error> {
    parse_with(pattern, flags, &props::SyntaxOnly)
}

/// [`parse`], checking `Script` and `Script_Extensions` values with `names`.
///
/// # Errors
///
/// [`Error`] if the pattern is a Syntax Error.
pub fn parse_with(pattern: &[u16], flags: Flags, names: &dyn Names) -> Result<Pattern, Error> {
    // §22.2.3.4† ParsePattern.
    if flags.unicode_mode() {
        // "If u or v is set": [+UnicodeMode, +NamedCaptureGroups].
        return run(pattern, flags, true, None, names);
    }
    // Otherwise parse with ~NamedCaptureGroups, then again with
    // +NamedCaptureGroups if the pattern has a GroupName. The first run also
    // gives CountLeftCapturingParensWithin, which Annex B's AtomEscape needs.
    let first = run(pattern, flags, false, None, names)?;
    run(
        pattern,
        flags,
        !first.group_names.is_empty(),
        Some(first.capture_count),
        names,
    )
}

fn run(
    pattern: &[u16],
    flags: Flags,
    named: bool,
    total: Option<u32>,
    names: &dyn Names,
) -> R<Pattern> {
    let mut p = Parser {
        src: pattern,
        pos: 0,
        unicode: flags.unicode_mode(),
        sets: flags.unicode_sets,
        named,
        total,
        names,
        depth: 0,
        groups: 0,
        group_names: Vec::new(),
        backrefs: Vec::new(),
        named_refs: Vec::new(),
    };
    let disjunction = p.disjunction()?;
    if p.pos < p.src.len() {
        // The parse of a Disjunction stops only at the end or at a `)`.
        return p.fail(ErrorKind::UnmatchedCloseParen);
    }
    p.early_errors(&disjunction)?;
    Ok(Pattern {
        disjunction,
        capture_count: p.groups,
        group_names: p.group_names,
    })
}

struct Parser<'a> {
    src: &'a [u16],
    pos: usize,
    unicode: bool,
    sets: bool,
    named: bool,
    total: Option<u32>,
    names: &'a dyn Names,
    depth: usize,
    groups: u32,
    group_names: Vec<(Vec<u32>, u32)>,
    backrefs: Vec<(u32, usize)>,
    named_refs: Vec<(Vec<u32>, usize)>,
}

/// The string of ASCII `bytes`.
fn ascii_string(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| char::from(b)).collect()
}

fn is_lead(u: u16) -> bool {
    (0xD800..0xDC00).contains(&u)
}

fn is_trail(u: u16) -> bool {
    (0xDC00..0xE000).contains(&u)
}

fn combine(lead: u16, trail: u16) -> u32 {
    // (lead - 0xD800) * 0x400 + (trail - 0xDC00) + 0x10000, without overflow:
    // both differences are below 0x400.
    let hi = u32::from(lead).saturating_sub(0xD800);
    let lo = u32::from(trail).saturating_sub(0xDC00);
    hi.saturating_mul(0x400)
        .saturating_add(lo)
        .saturating_add(0x1_0000)
}

fn hex_value(u: u16) -> Option<u32> {
    char::from_u32(u32::from(u)).and_then(|c| c.to_digit(16))
}

fn ascii(u: Option<u16>) -> Option<u8> {
    u.and_then(|u| u8::try_from(u).ok())
}

fn is_digit(u: Option<u16>) -> bool {
    matches!(ascii(u), Some(b'0'..=b'9'))
}

fn is_letter(u: Option<u16>) -> bool {
    matches!(ascii(u), Some(b'a'..=b'z' | b'A'..=b'Z'))
}

/// SyntaxCharacter (§22.2.1†): `^ $ \ . * + ? ( ) [ ] { } |`.
fn is_syntax_character(c: u32) -> bool {
    matches!(
        u8::try_from(c).ok(),
        Some(
            b'^' | b'$'
                | b'\\'
                | b'.'
                | b'*'
                | b'+'
                | b'?'
                | b'('
                | b')'
                | b'['
                | b']'
                | b'{'
                | b'}'
                | b'|'
        )
    )
}

/// IdentifierStartChar (§22.2.1†, RegExpIdentifierStart): `UnicodeIDStart`,
/// `$` or `_`.
fn is_id_start(c: u32) -> bool {
    match c {
        0x24 | 0x5F | 0x41..=0x5A | 0x61..=0x7A => true,
        0..=0x7F => false,
        _ => clazel_js_lexer::unicode::id_start_non_ascii(c),
    }
}

/// IdentifierPartChar (§22.2.1†, RegExpIdentifierPart): `UnicodeIDContinue`,
/// `$`, ZWNJ or ZWJ.
fn is_id_continue(c: u32) -> bool {
    match c {
        0x24 | 0x5F | 0x30..=0x39 | 0x41..=0x5A | 0x61..=0x7A | 0x200C | 0x200D => true,
        0..=0x7F => false,
        _ => clazel_js_lexer::unicode::id_continue_non_ascii(c),
    }
}

/// ClassSetSyntaxCharacter (§22.2.1†): `( ) [ ] { } / - \ |`.
fn is_class_set_syntax(c: u32) -> bool {
    matches!(
        u8::try_from(c).ok(),
        Some(b'(' | b')' | b'[' | b']' | b'{' | b'}' | b'/' | b'-' | b'\\' | b'|')
    )
}

/// ClassSetReservedPunctuator (§22.2.1†): `& - ! # % , : ; < = > @ ` ~`.
fn is_class_set_reserved_punctuator(c: u8) -> bool {
    matches!(
        c,
        b'&' | b'-'
            | b'!'
            | b'#'
            | b'%'
            | b','
            | b':'
            | b';'
            | b'<'
            | b'='
            | b'>'
            | b'@'
            | b'`'
            | b'~'
    )
}

/// The characters that make a ClassSetReservedDoublePunctuator when doubled:
/// `& ! # $ % * + , . : ; < = > ? @ ^ ` ~`.
fn is_class_set_double_punctuator(c: u8) -> bool {
    matches!(
        c,
        b'&' | b'!'
            | b'#'
            | b'$'
            | b'%'
            | b'*'
            | b'+'
            | b','
            | b'.'
            | b':'
            | b';'
            | b'<'
            | b'='
            | b'>'
            | b'?'
            | b'@'
            | b'^'
            | b'`'
            | b'~'
    )
}

/// An item of a class without `v`, before it is known to be a range end.
enum ClassAtomValue {
    Char(u32),
    Escape(ClassEscape),
}

/// Where a run of decimal digits is: its value (saturated) and its slice.
struct Digits {
    end: usize,
    value: u64,
    start: usize,
}

impl Parser<'_> {
    fn fail<T>(&self, kind: ErrorKind) -> R<T> {
        Err(Error { kind, at: self.pos })
    }

    fn adv(&mut self, n: usize) {
        self.pos = self.pos.saturating_add(n).min(self.src.len());
    }

    /// The code unit `off` ahead.
    fn unit(&self, off: usize) -> Option<u16> {
        self.src.get(self.pos.saturating_add(off)).copied()
    }

    /// Whether the code unit `off` ahead is the ASCII character `c`.
    fn is(&self, off: usize, c: u8) -> bool {
        self.unit(off) == Some(u16::from(c))
    }

    fn eat(&mut self, c: u8) -> bool {
        if self.is(0, c) {
            self.adv(1);
            true
        } else {
            false
        }
    }

    /// The next source character and its width in code units: a code point
    /// if `pairs` and a surrogate pair is next, otherwise a code unit.
    fn peek_with(&self, pairs: bool) -> Option<(u32, usize)> {
        let u = self.unit(0)?;
        if pairs
            && is_lead(u)
            && let Some(t) = self.unit(1)
            && is_trail(t)
        {
            return Some((combine(u, t), 2));
        }
        Some((u32::from(u), 1))
    }

    fn peek_cp(&self) -> Option<(u32, usize)> {
        self.peek_with(self.unicode)
    }

    fn bump_cp(&mut self) -> Option<u32> {
        let (c, w) = self.peek_cp()?;
        self.adv(w);
        Some(c)
    }

    fn enter(&mut self) -> R<()> {
        if self.depth >= MAX_DEPTH {
            return self.fail(ErrorKind::TooDeep);
        }
        self.depth = self.depth.saturating_add(1);
        Ok(())
    }

    fn leave(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    // ---- Disjunction, Alternative, Term (§22.2.1†) ----

    /// Disjunction :: Alternative | Alternative `|` Disjunction.
    fn disjunction(&mut self) -> R<Disjunction> {
        self.enter()?;
        let mut alternatives = Vec::new();
        loop {
            alternatives.push(self.alternative()?);
            if !self.eat(b'|') {
                break;
            }
        }
        self.leave();
        Ok(Disjunction { alternatives })
    }

    /// Alternative :: [empty] | Alternative Term. Stops before `|`, `)` and
    /// the end.
    fn alternative(&mut self) -> R<Alternative> {
        let mut terms = Vec::new();
        while let Some(u) = self.unit(0) {
            if u == u16::from(b'|') || u == u16::from(b')') {
                break;
            }
            terms.push(self.term()?);
        }
        Ok(Alternative { terms })
    }

    fn atom_term(atom: Atom, quantifier: Option<Quantifier>) -> Term {
        Term {
            kind: TermKind::Atom(atom),
            quantifier,
        }
    }

    fn assertion_term(a: Assertion) -> Term {
        Term {
            kind: TermKind::Assertion(a),
            quantifier: None,
        }
    }

    /// Term. Always consumes at least one code unit or fails.
    fn term(&mut self) -> R<Term> {
        let Some(u) = self.unit(0) else {
            return self.fail(ErrorKind::UnterminatedGroup);
        };
        match ascii(Some(u)) {
            // Assertion :: ^ | $ (not quantifiable: a quantifier after it
            // starts a Term, and none starts with one).
            Some(b'^') => {
                self.adv(1);
                Ok(Self::assertion_term(Assertion::Start))
            }
            Some(b'$') => {
                self.adv(1);
                Ok(Self::assertion_term(Assertion::End))
            }
            Some(b'(') => self.group(),
            Some(b'.') => {
                self.adv(1);
                let q = self.quantifier()?;
                Ok(Self::atom_term(Atom::Dot, q))
            }
            Some(b'[') => {
                let class = self.class()?;
                let q = self.quantifier()?;
                Ok(Self::atom_term(Atom::Class(class), q))
            }
            Some(b'\\') => self.escape_term(),
            // A quantifier with nothing before it.
            Some(b'*' | b'+' | b'?') => self.fail(ErrorKind::NothingToRepeat),
            Some(b'{') => {
                if self.unicode {
                    // `{` is a SyntaxCharacter, not a PatternCharacter.
                    self.fail(ErrorKind::LoneBracket)
                } else if self.scan_braces().is_some() {
                    // §B.1.2† ExtendedAtom :: InvalidBracedQuantifier.
                    self.fail(ErrorKind::InvalidBracedQuantifier)
                } else {
                    // §B.1.2† ExtendedPatternCharacter.
                    self.adv(1);
                    let q = self.quantifier()?;
                    Ok(Self::atom_term(Atom::Char(u32::from(u)), q))
                }
            }
            Some(b'}' | b']') if self.unicode => self.fail(ErrorKind::LoneBracket),
            _ => {
                // PatternCharacter, or §B.1.2† ExtendedPatternCharacter.
                let c = self.bump_cp().unwrap_or(u32::from(u));
                let q = self.quantifier()?;
                Ok(Self::atom_term(Atom::Char(c), q))
            }
        }
    }

    /// A Term that starts with `\`: `\b`, `\B` (Assertion), or an Atom.
    fn escape_term(&mut self) -> R<Term> {
        self.adv(1);
        match ascii(self.unit(0)) {
            None if self.unit(0).is_none() => self.fail(ErrorKind::TrailingBackslash),
            Some(b'b') => {
                self.adv(1);
                Ok(Self::assertion_term(Assertion::WordBoundary))
            }
            Some(b'B') => {
                self.adv(1);
                Ok(Self::assertion_term(Assertion::NotWordBoundary))
            }
            _ => {
                let atom = self.atom_escape()?;
                let q = self.quantifier()?;
                Ok(Self::atom_term(atom, q))
            }
        }
    }

    // ---- Quantifier (§22.2.1†) ----

    /// A run of ASCII digits starting at `from`.
    fn digits_at(&self, from: usize) -> Digits {
        let mut end = from;
        let mut value: u64 = 0;
        while let Some(&u) = self.src.get(end) {
            let Some(d) = hex_value(u).filter(|_| is_digit(Some(u))) else {
                break;
            };
            value = value.saturating_mul(10).saturating_add(u64::from(d));
            end = end.saturating_add(1);
        }
        Digits {
            end,
            value,
            start: from,
        }
    }

    /// The braced quantifier at `{`, without consuming it: `{n}`, `{n,}`,
    /// `{n,m}`, with its two digit runs.
    fn scan_braces(&self) -> Option<(Digits, Option<Digits>)> {
        let lo = self.digits_at(self.pos.saturating_add(1));
        if lo.end == lo.start {
            return None;
        }
        match self
            .src
            .get(lo.end)
            .copied()
            .and_then(|u| u8::try_from(u).ok())
        {
            Some(b'}') => Some((lo, None)),
            Some(b',') => {
                let hi = self.digits_at(lo.end.saturating_add(1));
                match self
                    .src
                    .get(hi.end)
                    .copied()
                    .and_then(|u| u8::try_from(u).ok())
                {
                    Some(b'}') => Some((lo, Some(hi))),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Whether the number written in `a` is greater than the one in `b`
    /// (digit runs, leading zeros ignored), exactly.
    fn digits_greater(&self, a: &Digits, b: &Digits) -> bool {
        let sa = self.significant(a);
        let sb = self.significant(b);
        if sa.len() != sb.len() {
            return sa.len() > sb.len();
        }
        sa.iter()
            .zip(sb.iter())
            .find(|(x, y)| x != y)
            .is_some_and(|(x, y)| x > y)
    }

    fn significant(&self, d: &Digits) -> &[u16] {
        let run = self.src.get(d.start..d.end).unwrap_or_default();
        let zeros = run.iter().take_while(|&&u| u == u16::from(b'0')).count();
        run.get(zeros..).unwrap_or_default()
    }

    /// Quantifier :: QuantifierPrefix | QuantifierPrefix `?`, if one is next.
    fn quantifier(&mut self) -> R<Option<Quantifier>> {
        let (min, max) = match ascii(self.unit(0)) {
            Some(b'*') => {
                self.adv(1);
                (0, None)
            }
            Some(b'+') => {
                self.adv(1);
                (1, None)
            }
            Some(b'?') => {
                self.adv(1);
                (0, Some(1))
            }
            Some(b'{') => {
                let Some((lo, hi)) = self.scan_braces() else {
                    // Not a quantifier: without `u` or `v` the `{` is a
                    // character (§B.1.2†); with, the next Term fails on it.
                    return Ok(None);
                };
                let max = match &hi {
                    None => Some(lo.value),
                    Some(hi) if hi.end == hi.start => None,
                    Some(hi) => Some(hi.value),
                };
                if let Some(hi) = &hi
                    && hi.end != hi.start
                    && self.digits_greater(&lo, hi)
                {
                    // §22.2.1.1†: `{n,m}` with n greater than m.
                    return self.fail(ErrorKind::QuantifierOutOfOrder);
                }
                let end = hi.as_ref().map_or(lo.end, |h| h.end);
                self.pos = end.saturating_add(1).min(self.src.len());
                (lo.value, max)
            }
            _ => return Ok(None),
        };
        let greedy = !self.eat(b'?');
        Ok(Some(Quantifier { min, max, greedy }))
    }

    // ---- Groups and lookarounds (§22.2.1†, Atom and Assertion) ----

    fn group(&mut self) -> R<Term> {
        self.adv(1);
        if !self.eat(b'?') {
            // `( Disjunction )`
            let index = self.open_capture()?;
            let body = self.group_body()?;
            let q = self.quantifier()?;
            return Ok(Self::atom_term(
                Atom::Group(Group {
                    index: Some(index),
                    name: None,
                    body,
                }),
                q,
            ));
        }
        match ascii(self.unit(0)) {
            Some(b':') => {
                self.adv(1);
                let body = self.group_body()?;
                let q = self.quantifier()?;
                Ok(Self::atom_term(
                    Atom::Group(Group {
                        index: None,
                        name: None,
                        body,
                    }),
                    q,
                ))
            }
            Some(c @ (b'=' | b'!')) => {
                self.adv(1);
                let body = self.group_body()?;
                // §B.1.2† QuantifiableAssertion: lookaheads, without `u`/`v`.
                let quantifier = if self.unicode {
                    None
                } else {
                    self.quantifier()?
                };
                Ok(Term {
                    kind: TermKind::Look(Look {
                        behind: false,
                        negative: c == b'!',
                        body,
                    }),
                    quantifier,
                })
            }
            Some(b'<') if self.is(1, b'=') || self.is(1, b'!') => {
                let negative = self.is(1, b'!');
                self.adv(2);
                let body = self.group_body()?;
                Ok(Term {
                    kind: TermKind::Look(Look {
                        behind: true,
                        negative,
                        body,
                    }),
                    quantifier: None,
                })
            }
            Some(b'<') => {
                // GroupSpecifier :: ? GroupName
                let name = self.group_name()?;
                let index = self.open_capture()?;
                self.group_names.push((name.clone(), index));
                let body = self.group_body()?;
                let q = self.quantifier()?;
                Ok(Self::atom_term(
                    Atom::Group(Group {
                        index: Some(index),
                        name: Some(name),
                        body,
                    }),
                    q,
                ))
            }
            _ => {
                // ( ? RegularExpressionModifiers : Disjunction ) and its `-` form.
                let (add, remove) = self.modifiers()?;
                let body = self.group_body()?;
                let q = self.quantifier()?;
                Ok(Self::atom_term(
                    Atom::Modified(ModifiedGroup { add, remove, body }),
                    q,
                ))
            }
        }
    }

    /// Counts a capturing `(`; §22.2.1.1† limits the count below 2^32 - 1.
    fn open_capture(&mut self) -> R<u32> {
        match self.groups.checked_add(1) {
            Some(n) if n < u32::MAX => {
                self.groups = n;
                Ok(n)
            }
            _ => self.fail(ErrorKind::TooManyGroups),
        }
    }

    /// `Disjunction )`: the body of a group.
    fn group_body(&mut self) -> R<Disjunction> {
        let body = self.disjunction()?;
        if self.eat(b')') {
            Ok(body)
        } else {
            self.fail(ErrorKind::UnterminatedGroup)
        }
    }

    /// RegularExpressionModifiers, after `(?` and up to the `:`: the letters
    /// to add and to remove (§22.2.1.1† Atom: no letter twice, none in both,
    /// and not both lists empty).
    fn modifiers(&mut self) -> R<(Modifiers, Modifiers)> {
        let mut add = Modifiers::default();
        let mut remove = Modifiers::default();
        let mut add_n = 0u8;
        let mut remove_n = 0u8;
        let mut removing = false;
        loop {
            let Some(u) = self.unit(0) else {
                return self.fail(ErrorKind::InvalidGroupSpecifier);
            };
            match ascii(Some(u)) {
                Some(b':') => {
                    self.adv(1);
                    break;
                }
                Some(b'-') if !removing => {
                    removing = true;
                    self.adv(1);
                }
                Some(c @ (b'i' | b'm' | b's')) => {
                    let target = if removing { &mut remove } else { &mut add };
                    let slot = match c {
                        b'i' => &mut target.ignore_case,
                        b'm' => &mut target.multiline,
                        _ => &mut target.dot_all,
                    };
                    if *slot {
                        return self.fail(ErrorKind::InvalidModifiers);
                    }
                    *slot = true;
                    if removing {
                        remove_n = remove_n.saturating_add(1);
                    } else {
                        add_n = add_n.saturating_add(1);
                    }
                    self.adv(1);
                }
                _ => return self.fail(ErrorKind::InvalidGroupSpecifier),
            }
        }
        let overlap = (add.ignore_case && remove.ignore_case)
            || (add.multiline && remove.multiline)
            || (add.dot_all && remove.dot_all);
        if overlap || (add_n == 0 && remove_n == 0) {
            return self.fail(ErrorKind::InvalidModifiers);
        }
        Ok((add, remove))
    }

    /// GroupName :: `<` RegExpIdentifierName `>`, at the `<`.
    fn group_name(&mut self) -> R<Vec<u32>> {
        self.adv(1);
        let mut name: Vec<u32> = Vec::new();
        loop {
            if self.eat(b'>') {
                if name.is_empty() {
                    return self.fail(ErrorKind::InvalidGroupName);
                }
                return Ok(name);
            }
            let c = if self.is(0, b'\\') {
                // RegExpIdentifierStart/Part :: `\` RegExpUnicodeEscapeSequence[+UnicodeMode]
                self.adv(1);
                if !self.eat(b'u') {
                    return self.fail(ErrorKind::InvalidGroupName);
                }
                self.unicode_escape_body(true)?
            } else {
                // UnicodeLeadSurrogate UnicodeTrailSurrogate is one character
                // in a name in both modes.
                match self.peek_with(true) {
                    Some((c, w)) => {
                        self.adv(w);
                        c
                    }
                    None => return self.fail(ErrorKind::InvalidGroupName),
                }
            };
            let ok = if name.is_empty() {
                is_id_start(c)
            } else {
                is_id_continue(c)
            };
            if !ok {
                return self.fail(ErrorKind::InvalidGroupName);
            }
            name.push(c);
        }
    }

    // ---- Escapes (§22.2.1†, AtomEscape, CharacterEscape, ...) ----

    /// AtomEscape, after the `\` (and with `\b`, `\B` already read).
    fn atom_escape(&mut self) -> R<Atom> {
        let Some(u) = self.unit(0) else {
            return self.fail(ErrorKind::TrailingBackslash);
        };
        match ascii(Some(u)) {
            Some(b'1'..=b'9') => return self.decimal_escape(),
            Some(b'k') if self.named => {
                // [+NamedCaptureGroups] `k` GroupName
                self.adv(1);
                if !self.is(0, b'<') {
                    return self.fail(ErrorKind::MissingGroupName);
                }
                let at = self.pos;
                let name = self.group_name()?;
                self.named_refs.push((name.clone(), at));
                return Ok(Atom::NamedBackReference(name));
            }
            Some(b'c') if !self.unicode && !is_letter(self.unit(1)) => {
                // §B.1.2† ExtendedAtom :: `\` [lookahead = c]
                return Ok(Atom::Char(0x5C));
            }
            _ => {}
        }
        if let Some(e) = self.class_escape_letter()? {
            return Ok(Atom::Escape(e));
        }
        Ok(Atom::Char(self.character_escape()?))
    }

    /// DecimalEscape (the digit is 1 to 9), with Annex B's "only if" in
    /// AtomEscape: otherwise the digits are a CharacterEscape.
    fn decimal_escape(&mut self) -> R<Atom> {
        let at = self.pos;
        let d = self.digits_at(self.pos);
        let n = u32::try_from(d.value).unwrap_or(u32::MAX);
        if self.unicode {
            // [+UnicodeMode] DecimalEscape; §22.2.1.1† bounds it by the count,
            // checked after the parse.
            self.pos = d.end;
            self.backrefs.push((n, at));
            return Ok(Atom::BackReference(n));
        }
        match self.total {
            Some(total) if n > total => {
                // Not a DecimalEscape: LegacyOctalEscapeSequence, or
                // IdentityEscape for `8` and `9`.
                Ok(Atom::Char(self.character_escape()?))
            }
            _ => {
                self.pos = d.end;
                Ok(Atom::BackReference(n))
            }
        }
    }

    /// CharacterClassEscape at `d D s S w W p P`, after the `\`: `None` if
    /// the next character is none of them (or is `p`/`P` without `u`/`v`).
    fn class_escape_letter(&mut self) -> R<Option<ClassEscape>> {
        let e = match ascii(self.unit(0)) {
            Some(b'd') => ClassEscape::Digit,
            Some(b'D') => ClassEscape::NotDigit,
            Some(b's') => ClassEscape::Space,
            Some(b'S') => ClassEscape::NotSpace,
            Some(b'w') => ClassEscape::Word,
            Some(b'W') => ClassEscape::NotWord,
            Some(c @ (b'p' | b'P')) if self.unicode => {
                return self.property_escape(c == b'P').map(Some);
            }
            _ => return Ok(None),
        };
        self.adv(1);
        Ok(Some(e))
    }

    /// CharacterEscape (without `c`'s Annex B fallback, which the callers
    /// handle), after the `\`: its character value.
    fn character_escape(&mut self) -> R<u32> {
        let Some((c, w)) = self.peek_cp() else {
            return self.fail(ErrorKind::TrailingBackslash);
        };
        match u8::try_from(c).ok() {
            // ControlEscape
            Some(b'f') => self.simple(0x0C),
            Some(b'n') => self.simple(0x0A),
            Some(b'r') => self.simple(0x0D),
            Some(b't') => self.simple(0x09),
            Some(b'v') => self.simple(0x0B),
            // c AsciiLetter
            Some(b'c') => {
                if let Some(l) = ascii(self.unit(1)).filter(|b| b.is_ascii_alphabetic()) {
                    self.adv(2);
                    Ok(u32::from(l % 32))
                } else if self.unicode {
                    self.fail(ErrorKind::InvalidControlEscape)
                } else {
                    self.identity_escape()
                }
            }
            // 0 [lookahead ∉ DecimalDigit], and §B.1.2† LegacyOctalEscapeSequence
            Some(b'0') => {
                if is_digit(self.unit(1)) {
                    if self.unicode {
                        self.fail(ErrorKind::InvalidDecimalEscape)
                    } else {
                        Ok(self.legacy_octal())
                    }
                } else {
                    self.simple(0)
                }
            }
            Some(b'1'..=b'7') if !self.unicode => Ok(self.legacy_octal()),
            Some(b'1'..=b'9') if self.unicode => self.fail(ErrorKind::InvalidDecimalEscape),
            // HexEscapeSequence
            Some(b'x') => {
                let hi = self.unit(1).and_then(hex_value);
                let lo = self.unit(2).and_then(hex_value);
                if let (Some(hi), Some(lo)) = (hi, lo) {
                    self.adv(3);
                    Ok(hi.saturating_mul(16).saturating_add(lo))
                } else if self.unicode {
                    self.fail(ErrorKind::InvalidUnicodeEscape)
                } else {
                    // §B.1.2† IdentityEscape: `x`.
                    self.adv(w);
                    Ok(c)
                }
            }
            // RegExpUnicodeEscapeSequence
            Some(b'u') => {
                self.adv(1);
                self.unicode_escape_body(self.unicode)
            }
            _ => self.identity_escape(),
        }
    }

    fn simple(&mut self, v: u32) -> R<u32> {
        self.adv(1);
        Ok(v)
    }

    /// §B.1.2† LegacyOctalEscapeSequence, at its first digit (0 to 7).
    fn legacy_octal(&mut self) -> u32 {
        let first = ascii(self.unit(0)).map_or(0, |b| u32::from(b.saturating_sub(b'0')));
        self.adv(1);
        let max_len = if first <= 3 { 3 } else { 2 };
        let mut value = first;
        let mut len = 1u32;
        while len < max_len {
            match ascii(self.unit(0)) {
                Some(b @ b'0'..=b'7') => {
                    value = value
                        .saturating_mul(8)
                        .saturating_add(u32::from(b.saturating_sub(b'0')));
                    self.adv(1);
                    len = len.saturating_add(1);
                }
                _ => break,
            }
        }
        value
    }

    /// The rest of RegExpUnicodeEscapeSequence after `u`, in the
    /// `[+UnicodeMode]` form if `plus_u`, else `u Hex4Digits` or (§B.1.2†) the
    /// identity escape `u`.
    fn unicode_escape_body(&mut self, plus_u: bool) -> R<u32> {
        if !plus_u {
            return match self.hex4(0) {
                Some(v) => {
                    self.adv(4);
                    Ok(v)
                }
                // IdentityEscape: the `u` is already consumed.
                None => Ok(u32::from(b'u')),
            };
        }
        if self.eat(b'{') {
            // `{` CodePoint `}`
            let start = self.pos;
            let mut value: u32 = 0;
            while let Some(d) = self.unit(0).and_then(hex_value) {
                value = value.saturating_mul(16).saturating_add(d).min(0x11_0000);
                self.adv(1);
            }
            if self.pos == start || value > 0x10_FFFF || !self.eat(b'}') {
                return self.fail(ErrorKind::InvalidUnicodeEscape);
            }
            return Ok(value);
        }
        let Some(first) = self.hex4(0) else {
            return self.fail(ErrorKind::InvalidUnicodeEscape);
        };
        self.adv(4);
        if let Ok(lead) = u16::try_from(first)
            && is_lead(lead)
            && self.is(0, b'\\')
            && self.is(1, b'u')
            && let Some(second) = self.hex4(2)
            && let Ok(trail) = u16::try_from(second)
            && is_trail(trail)
        {
            // `u` HexLeadSurrogate `\u` HexTrailSurrogate
            self.adv(6);
            return Ok(combine(lead, trail));
        }
        Ok(first)
    }

    /// Four hex digits at `off` ahead.
    fn hex4(&self, off: usize) -> Option<u32> {
        let mut v: u32 = 0;
        for i in 0..4usize {
            let d = self.unit(off.saturating_add(i)).and_then(hex_value)?;
            v = v.saturating_mul(16).saturating_add(d);
        }
        Some(v)
    }

    /// IdentityEscape.
    fn identity_escape(&mut self) -> R<u32> {
        let Some((c, w)) = self.peek_cp() else {
            return self.fail(ErrorKind::TrailingBackslash);
        };
        let ok = if self.unicode {
            // [+UnicodeMode] SyntaxCharacter | `/`
            is_syntax_character(c) || c == u32::from(b'/')
        } else {
            // [~UnicodeMode] SourceCharacterIdentityEscape: not `c`, and not
            // `k` with +NamedCaptureGroups.
            c != u32::from(b'c') && !(self.named && c == u32::from(b'k'))
        };
        if !ok {
            return self.fail(ErrorKind::InvalidEscape);
        }
        self.adv(w);
        Ok(c)
    }

    // ---- \p{..} (§22.2.1†, UnicodePropertyValueExpression) ----

    /// `p{..}` or `P{..}`, at the letter (`\` read).
    fn property_escape(&mut self, negated: bool) -> R<ClassEscape> {
        self.adv(1);
        if !self.eat(b'{') {
            return self.fail(ErrorKind::InvalidProperty);
        }
        // The text up to `}`: ASCII letters, digits, `_` and `=`.
        let mut text: Vec<u8> = Vec::new();
        while let Some(b) = ascii(self.unit(0)) {
            if b.is_ascii_alphanumeric() || b == b'_' || b == b'=' {
                text.push(b);
                self.adv(1);
            } else {
                break;
            }
        }
        if !self.eat(b'}') {
            return self.fail(ErrorKind::InvalidProperty);
        }
        let property = match text.iter().position(|&b| b == b'=') {
            Some(eq) => self.name_value(
                text.get(..eq).unwrap_or_default(),
                text.get(eq.saturating_add(1)..).unwrap_or_default(),
            ),
            None => self.lone_name(&text),
        };
        match property {
            Some(Property::Strings(_)) if negated => {
                self.fail(ErrorKind::NegatedClassMayContainStrings)
            }
            Some(property) => Ok(ClassEscape::Property { negated, property }),
            None => self.fail(ErrorKind::InvalidProperty),
        }
    }

    /// `UnicodePropertyName = UnicodePropertyValue`. The bytes are ASCII.
    fn name_value(&self, name: &[u8], value: &[u8]) -> Option<Property> {
        let name_ok =
            !name.is_empty() && name.iter().all(|b| b.is_ascii_alphabetic() || *b == b'_');
        let value_ok = !value.is_empty()
            && value
                .iter()
                .all(|b| b.is_ascii_alphanumeric() || *b == b'_');
        if !name_ok || !value_ok {
            return None;
        }
        let owned = || ascii_string(value);
        if name == b"General_Category" || name == b"gc" {
            props::is_general_category(value).then(|| Property::GeneralCategory(owned()))
        } else if name == b"Script" || name == b"sc" {
            self.is_script(value).then(|| Property::Script(owned()))
        } else if name == b"Script_Extensions" || name == b"scx" {
            self.is_script(value)
                .then(|| Property::ScriptExtensions(owned()))
        } else {
            None
        }
    }

    fn is_script(&self, value: &[u8]) -> bool {
        self.names.is_script(&ascii_string(value))
    }

    /// `LoneUnicodePropertyNameOrValue`. The bytes are ASCII.
    fn lone_name(&self, text: &[u8]) -> Option<Property> {
        if text.is_empty() || !text.iter().all(|b| b.is_ascii_alphanumeric() || *b == b'_') {
            return None;
        }
        let owned = || ascii_string(text);
        if props::is_general_category(text) {
            Some(Property::GeneralCategory(owned()))
        } else if props::is_binary_property(text) {
            Some(Property::Binary(owned()))
        } else if self.sets && props::is_string_property(text) {
            Some(Property::Strings(owned()))
        } else {
            None
        }
    }

    // ---- CharacterClass (§22.2.1†, §B.1.2†) ----

    /// CharacterClass, at the `[`.
    fn class(&mut self) -> R<CharacterClass> {
        self.adv(1);
        let negated = self.eat(b'^');
        let contents = if self.sets {
            let expr = self.class_set_expr()?;
            if negated && expr.may_contain_strings() {
                return self.fail(ErrorKind::NegatedClassMayContainStrings);
            }
            ClassContents::Set(expr)
        } else {
            ClassContents::Ranges(self.class_ranges()?)
        };
        if !self.eat(b']') {
            return self.fail(ErrorKind::UnterminatedClass);
        }
        Ok(CharacterClass { negated, contents })
    }

    /// ClassRanges (without `v`), up to the `]`, which it leaves.
    fn class_ranges(&mut self) -> R<Vec<ClassItem>> {
        let mut items = Vec::new();
        loop {
            match self.unit(0) {
                None => return self.fail(ErrorKind::UnterminatedClass),
                Some(u) if u == u16::from(b']') => return Ok(items),
                Some(_) => {}
            }
            let a = self.class_atom()?;
            // ClassAtom `-` ClassAtom, unless the `-` is last.
            if self.is(0, b'-') && self.unit(1).is_some() && !self.is(1, b']') {
                self.adv(1);
                let b = self.class_atom()?;
                match (a, b) {
                    (ClassAtomValue::Char(x), ClassAtomValue::Char(y)) => {
                        if x > y {
                            return self.fail(ErrorKind::RangeOutOfOrder);
                        }
                        items.push(ClassItem::Range(x, y));
                    }
                    (a, b) => {
                        if self.unicode {
                            return self.fail(ErrorKind::ClassEscapeInRange);
                        }
                        // §B.1.2† NonemptyClassRanges: the `-` is a character.
                        items.push(Self::class_item(a));
                        items.push(ClassItem::Char(u32::from(b'-')));
                        items.push(Self::class_item(b));
                    }
                }
            } else {
                items.push(Self::class_item(a));
            }
        }
    }

    fn class_item(a: ClassAtomValue) -> ClassItem {
        match a {
            ClassAtomValue::Char(c) => ClassItem::Char(c),
            ClassAtomValue::Escape(e) => ClassItem::Escape(e),
        }
    }

    /// ClassAtom.
    fn class_atom(&mut self) -> R<ClassAtomValue> {
        let Some(c) = self.bump_cp() else {
            return self.fail(ErrorKind::UnterminatedClass);
        };
        if c != u32::from(b'\\') {
            return Ok(ClassAtomValue::Char(c));
        }
        // ClassEscape
        let Some(u) = self.unit(0) else {
            return self.fail(ErrorKind::TrailingBackslash);
        };
        match ascii(Some(u)) {
            Some(b'b') => {
                self.adv(1);
                return Ok(ClassAtomValue::Char(0x08));
            }
            Some(b'-') if self.unicode => {
                self.adv(1);
                return Ok(ClassAtomValue::Char(u32::from(b'-')));
            }
            Some(b'c') if !self.unicode => {
                // §B.1.2† ClassEscape :: `c` ClassControlLetter, and
                // ClassAtomNoDash :: `\` [lookahead = c].
                let next = self.unit(1);
                if is_letter(next) || is_digit(next) || self.is(1, b'_') {
                    let v = ascii(next).map_or(0, |b| u32::from(b % 32));
                    self.adv(2);
                    return Ok(ClassAtomValue::Char(v));
                }
                return Ok(ClassAtomValue::Char(0x5C));
            }
            _ => {}
        }
        if let Some(e) = self.class_escape_letter()? {
            return Ok(ClassAtomValue::Escape(e));
        }
        Ok(ClassAtomValue::Char(self.character_escape()?))
    }

    // ---- Class set expressions, `v` mode (§22.2.1†) ----

    /// ClassSetExpression, up to the `]`, which it leaves.
    fn class_set_expr(&mut self) -> R<ClassSetExpr> {
        self.enter()?;
        let r = self.class_set_expr_body();
        self.leave();
        r
    }

    fn at_pair(&self, c: u8) -> bool {
        self.is(0, c) && self.is(1, c)
    }

    fn class_set_expr_body(&mut self) -> R<ClassSetExpr> {
        match self.unit(0) {
            None => return self.fail(ErrorKind::UnterminatedClass),
            Some(u) if u == u16::from(b']') => return Ok(ClassSetExpr::Union(Vec::new())),
            Some(_) => {}
        }
        let first = self.class_set_item()?;
        let intersection = self.at_pair(b'&');
        if intersection || self.at_pair(b'-') {
            // ClassIntersection / ClassSubtraction: the first is an operand.
            let ClassSetItem::Operand(first) = first else {
                return self.fail(ErrorKind::InvalidClassSetOperation);
            };
            let op = if intersection { b'&' } else { b'-' };
            let mut operands = vec![first];
            while self.at_pair(op) {
                self.adv(2);
                if intersection && self.is(0, b'&') {
                    // `&&` [lookahead ≠ &]
                    return self.fail(ErrorKind::InvalidClassSetOperation);
                }
                operands.push(self.class_set_operand()?);
            }
            return match self.unit(0) {
                Some(u) if u == u16::from(b']') => Ok(if intersection {
                    ClassSetExpr::Intersection(operands)
                } else {
                    ClassSetExpr::Subtraction(operands)
                }),
                None => self.fail(ErrorKind::UnterminatedClass),
                Some(_) => self.fail(ErrorKind::InvalidClassSetOperation),
            };
        }
        let mut items = vec![first];
        loop {
            match self.unit(0) {
                None => return self.fail(ErrorKind::UnterminatedClass),
                Some(u) if u == u16::from(b']') => return Ok(ClassSetExpr::Union(items)),
                Some(_) => {}
            }
            if self.at_pair(b'&') || self.at_pair(b'-') {
                return self.fail(ErrorKind::InvalidClassSetOperation);
            }
            items.push(self.class_set_item()?);
        }
    }

    /// ClassSetRange or ClassSetOperand.
    fn class_set_item(&mut self) -> R<ClassSetItem> {
        let operand = self.class_set_operand()?;
        if let ClassSetOperand::Char(a) = operand
            && self.is(0, b'-')
            && !self.is(1, b'-')
        {
            // ClassSetRange :: ClassSetCharacter `-` ClassSetCharacter
            self.adv(1);
            if self.is(0, b'\\') && self.class_escape_follows(1) {
                return self.fail(ErrorKind::ClassEscapeInRange);
            }
            let b = self.class_set_character()?;
            if a > b {
                return self.fail(ErrorKind::RangeOutOfOrder);
            }
            return Ok(ClassSetItem::Range(a, b));
        }
        Ok(ClassSetItem::Operand(operand))
    }

    /// Whether the code unit `off` ahead starts a CharacterClassEscape.
    fn class_escape_follows(&self, off: usize) -> bool {
        matches!(
            ascii(self.unit(off)),
            Some(b'd' | b'D' | b's' | b'S' | b'w' | b'W' | b'p' | b'P')
        )
    }

    /// ClassSetOperand.
    fn class_set_operand(&mut self) -> R<ClassSetOperand> {
        if self.is(0, b'[') {
            // NestedClass
            self.adv(1);
            let negated = self.eat(b'^');
            let expr = self.class_set_expr()?;
            if !self.eat(b']') {
                return self.fail(ErrorKind::UnterminatedClass);
            }
            if negated && expr.may_contain_strings() {
                return self.fail(ErrorKind::NegatedClassMayContainStrings);
            }
            return Ok(ClassSetOperand::Nested {
                negated,
                expr: Box::new(expr),
            });
        }
        if self.is(0, b'\\') {
            if self.is(1, b'q') && self.is(2, b'{') {
                return self.class_string_disjunction();
            }
            if self.class_escape_follows(1) {
                self.adv(1);
                if let Some(e) = self.class_escape_letter()? {
                    return Ok(ClassSetOperand::Escape(e));
                }
                return self.fail(ErrorKind::InvalidEscape);
            }
        }
        Ok(ClassSetOperand::Char(self.class_set_character()?))
    }

    /// ClassStringDisjunction, at `\q{`.
    fn class_string_disjunction(&mut self) -> R<ClassSetOperand> {
        self.adv(3);
        let mut list: Vec<Vec<u32>> = Vec::new();
        let mut current: Vec<u32> = Vec::new();
        loop {
            match ascii(self.unit(0)) {
                None if self.unit(0).is_none() => {
                    return self.fail(ErrorKind::InvalidClassStringDisjunction);
                }
                Some(b'}') => {
                    self.adv(1);
                    list.push(current);
                    return Ok(ClassSetOperand::Strings(list));
                }
                Some(b'|') => {
                    self.adv(1);
                    list.push(core::mem::take(&mut current));
                }
                _ => current.push(self.class_set_character()?),
            }
        }
    }

    /// ClassSetCharacter.
    fn class_set_character(&mut self) -> R<u32> {
        let Some((c, w)) = self.peek_cp() else {
            return self.fail(ErrorKind::UnterminatedClass);
        };
        if c == u32::from(b'\\') {
            self.adv(1);
            let Some(u) = self.unit(0) else {
                return self.fail(ErrorKind::TrailingBackslash);
            };
            return match ascii(Some(u)) {
                Some(b'b') => self.simple(0x08),
                Some(p) if is_class_set_reserved_punctuator(p) => self.simple(u32::from(p)),
                _ => self.character_escape(),
            };
        }
        if is_class_set_syntax(c) {
            return self.fail(ErrorKind::InvalidClassSetCharacter);
        }
        if let Some(b) = u8::try_from(c)
            .ok()
            .filter(|&b| is_class_set_double_punctuator(b))
            && self.unit(w) == Some(u16::from(b))
        {
            // ClassSetReservedDoublePunctuator
            return self.fail(ErrorKind::InvalidClassSetCharacter);
        }
        self.adv(w);
        Ok(c)
    }

    // ---- Early errors over the whole pattern (§22.2.1.1†) ----

    fn early_errors(&self, d: &Disjunction) -> R<()> {
        // §22.2.1.1† AtomEscape :: DecimalEscape [+UnicodeMode]: the number
        // is at most CountLeftCapturingParensWithin.
        if let Some(&(_, at)) = self.backrefs.iter().find(|(n, _)| *n > self.groups) {
            return Err(Error {
                kind: ErrorKind::InvalidDecimalEscape,
                at,
            });
        }
        // §22.2.1.1† AtomEscape :: `k` GroupName: some group has that name.
        let declared: BTreeSet<&Vec<u32>> = self.group_names.iter().map(|(n, _)| n).collect();
        if let Some(&(_, at)) = self.named_refs.iter().find(|(n, _)| !declared.contains(n)) {
            return Err(Error {
                kind: ErrorKind::UndeclaredGroupName,
                at,
            });
        }
        // §22.2.1.1† Pattern :: Disjunction: no two groups of one name that
        // might both participate.
        if self.group_names.len() >= 2 && names_in_disjunction(d).is_err() {
            return Err(Error {
                kind: ErrorKind::DuplicateGroupName,
                at: self.src.len(),
            });
        }
        Ok(())
    }
}

type NameSet = BTreeSet<Vec<u32>>;

/// The names of the groups in `d`. `Err` if two with one name can take part
/// in one match (MightBothParticipate): that is, they are not in different
/// alternatives of a Disjunction.
fn names_in_disjunction(d: &Disjunction) -> Result<NameSet, ()> {
    let mut all = NameSet::new();
    for alt in &d.alternatives {
        // Different alternatives may repeat a name: union, no check.
        all.extend(names_in_alternative(alt)?);
    }
    Ok(all)
}

fn names_in_alternative(a: &Alternative) -> Result<NameSet, ()> {
    let mut all = NameSet::new();
    for term in &a.terms {
        let inner = match &term.kind {
            TermKind::Atom(Atom::Group(g)) => {
                let mut s = names_in_disjunction(&g.body)?;
                if let Some(n) = &g.name
                    && !s.insert(n.clone())
                {
                    return Err(());
                }
                s
            }
            TermKind::Atom(Atom::Modified(m)) => names_in_disjunction(&m.body)?,
            TermKind::Look(l) => names_in_disjunction(&l.body)?,
            _ => continue,
        };
        // Terms of one alternative all take part together.
        for n in inner {
            if !all.insert(n) {
                return Err(());
            }
        }
    }
    Ok(all)
}
