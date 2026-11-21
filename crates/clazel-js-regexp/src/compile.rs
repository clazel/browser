//! From the syntax tree to instructions: ECMA-262 §22.2.2† (Pattern
//! Semantics), one production at a time. Section numbers marked † are from
//! memory (the specification's text is not vendored).
//!
//! # Modelling choices
//!
//! - **Continuations become jumps.** The standard's Matcher is a closure from
//!   a MatchState and a continuation to a MatchState or failure. Here a
//!   Matcher is a run of instructions that falls through to the next one on
//!   success, and a failure is a pop of the backtrack stack. Every place the
//!   standard tries one continuation and then another (alternation, a greedy
//!   or lazy quantifier, a class with strings) is a [`Inst::Split`] or a
//!   stack entry, in the order the standard tries them.
//! - **Direction.** A lookbehind body is compiled with `direction` backward
//!   (§22.2.2.3.1† Alternative: "the terms are matched right to left"): its
//!   terms in reverse order, its characters read before the position, and its
//!   groups closing with the end first. A lookahead inside a lookbehind is
//!   forward again, and the other way round.
//! - **Modifiers.** `i`, `m` and `s` are compile-time state: `(?i-s:..)`
//!   compiles its body with them changed, so no instruction asks for the flag
//!   at match time. `u` and `v` are the pattern's, and cannot be modified.
//! - **Counting.** `{n,m}` is a counter register and a loop, never `n` copies
//!   of the body. A greedy quantifier over one character with no captures is
//!   one instruction ([`Inst::Run`]) and one stack entry for the whole run.
//! - **Classes.** A character class is a postfix program over its leaves (a
//!   character, a range, an escape) and `not`, `or`, `and`, `minus`, so that
//!   matching a character needs no recursion over the class's nesting. With
//!   `i`, each leaf asks whether *some* character with the same `Canonicalize`
//!   as the input's is in it (CharacterSetMatcher, §22.2.2.7.1†), which is the
//!   standard's rule for classes without `v`; with `v` the standard folds each
//!   leaf first and then combines them, which is the same formula applied leaf
//!   by leaf, with `\P`, `\D`, `\S`, `\W` and `[^..]` as a `not` over the
//!   positive leaf. (Without `v`, `\P{Lu}` with `iu` matches `a`: the complement
//!   is taken before folding, as the standard does.)
//! - **Strings in classes (`v`).** A class that can match strings of more or
//!   fewer than one character is an alternation: the strings, longest first
//!   (ties in code point order), then the single characters, then the empty
//!   string (§22.2.2.7† CompileAtom, "CharacterClass").
//! - **Recursion** over the tree is bounded by [`MAX_DEPTH`]: the parser
//!   never builds a deeper one, and a tree built by hand that is deeper is
//!   [`CompileError::TooDeep`]. The matcher itself does not recurse.

use std::collections::BTreeSet;

use crate::ast::{
    Alternative, Assertion, Atom, CharacterClass, ClassContents, ClassEscape, ClassItem,
    ClassSetExpr, ClassSetItem, ClassSetOperand, Disjunction, Group, Look, Pattern, Property,
    Quantifier, Term, TermKind,
};
use crate::flags::Flags;
use crate::parser::MAX_DEPTH;
use crate::program::{ClassOp, ClassProg, EscKind, Inst, One, OneKind, Program};
use crate::unicode::{self, Prop, canonicalize, simple_fold};

/// Why a pattern cannot be compiled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError {
    /// The tree nests deeper than [`MAX_DEPTH`] (a tree from
    /// [`crate::parse`] never does).
    TooDeep,
    /// A backreference to a group that does not exist (a tree from
    /// [`crate::parse`] never has one).
    BackReference(u32),
    /// A `\p{..}` whose table is not generated: `Script`, `Script_Extensions`
    /// and the properties of strings (`v`). The text names it.
    UnsupportedProperty(String),
    /// More than 2^32 instructions or registers.
    TooLarge,
}

impl core::fmt::Display for CompileError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CompileError::TooDeep => write!(f, "pattern nests too deeply"),
            CompileError::BackReference(n) => write!(f, "no group {n} to refer to"),
            CompileError::UnsupportedProperty(p) => write!(f, "unsupported property {p}"),
            CompileError::TooLarge => write!(f, "pattern too large"),
        }
    }
}

type R<T = ()> = Result<T, CompileError>;

/// Compiles `pattern`, parsed with `flags`, into a [`Program`].
///
/// # Errors
///
/// [`CompileError`]: a `\p{..}` that has no table, or (for a tree not made by
/// [`crate::parse`]) too deep or with a dangling backreference.
pub fn compile(pattern: &Pattern, flags: Flags) -> Result<Program, CompileError> {
    let regs0 = pattern
        .capture_count
        .checked_add(1)
        .and_then(|n| n.checked_mul(2))
        .ok_or(CompileError::TooLarge)?;
    let mut c = Compiler {
        unicode: flags.unicode_mode(),
        v: flags.unicode_sets,
        capture_count: pattern.capture_count,
        group_names: &pattern.group_names,
        insts: Vec::new(),
        classes: Vec::new(),
        backrefs: Vec::new(),
        next_reg: regs0,
    };
    let st = St {
        ic: flags.ignore_case,
        ml: flags.multiline,
        dot_all: flags.dot_all,
        back: false,
    };
    c.disjunction(&pattern.disjunction, st, 1)?;
    c.emit(Inst::Match)?;
    Ok(Program {
        insts: c.insts,
        classes: c.classes,
        backrefs: c.backrefs,
        regs: usize::try_from(c.next_reg).map_err(|_| CompileError::TooLarge)?,
        capture_count: pattern.capture_count,
        unicode: c.unicode,
        group_names: pattern.group_names.clone(),
    })
}

/// The compile-time state: the flags in scope and the direction.
#[derive(Debug, Clone, Copy)]
struct St {
    ic: bool,
    ml: bool,
    dot_all: bool,
    back: bool,
}

struct Compiler<'a> {
    unicode: bool,
    v: bool,
    capture_count: u32,
    group_names: &'a [(Vec<u32>, u32)],
    insts: Vec<Inst>,
    classes: Vec<ClassProg>,
    backrefs: Vec<Vec<u32>>,
    next_reg: u32,
}

/// What a quantifier repeats.
enum Body<'t> {
    One(One),
    Kind(&'t TermKind),
}

/// An alternative of a class with strings.
enum Alt {
    Str(Vec<u32>),
    One(One),
    Empty,
}

fn to_usize(n: u64) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

impl Compiler<'_> {
    fn pc(&self) -> R<u32> {
        u32::try_from(self.insts.len()).map_err(|_| CompileError::TooLarge)
    }

    fn emit(&mut self, i: Inst) -> R<u32> {
        let at = self.pc()?;
        self.insts.push(i);
        Ok(at)
    }

    fn set(&mut self, at: u32, i: Inst) {
        if let Some(slot) = self.insts.get_mut(at as usize) {
            *slot = i;
        }
    }

    fn reg(&mut self) -> R<u32> {
        let r = self.next_reg;
        self.next_reg = r.checked_add(1).ok_or(CompileError::TooLarge)?;
        Ok(r)
    }

    fn add_class(&mut self, c: ClassProg) -> R<u32> {
        let id = u32::try_from(self.classes.len()).map_err(|_| CompileError::TooLarge)?;
        self.classes.push(c);
        Ok(id)
    }

    /// Disjunction (§22.2.2.3.1†): `Alternative | Disjunction` tries the left
    /// alternative, then the right one.
    fn disjunction(&mut self, d: &Disjunction, st: St, depth: usize) -> R {
        if depth > MAX_DEPTH.saturating_add(1) {
            return Err(CompileError::TooDeep);
        }
        let n = d.alternatives.len();
        let mut jumps = Vec::new();
        for (i, alt) in d.alternatives.iter().enumerate() {
            if i.saturating_add(1) >= n {
                self.alternative(alt, st, depth)?;
            } else {
                let split = self.emit(Inst::Split {
                    first: 0,
                    second: 0,
                })?;
                let first = self.pc()?;
                self.alternative(alt, st, depth)?;
                jumps.push(self.emit(Inst::Jmp(0))?);
                let second = self.pc()?;
                self.set(split, Inst::Split { first, second });
            }
        }
        let end = self.pc()?;
        for j in jumps {
            self.set(j, Inst::Jmp(end));
        }
        Ok(())
    }

    /// Alternative (§22.2.2.3.1†): the terms in order, or with `direction`
    /// backward in reverse order.
    fn alternative(&mut self, a: &Alternative, st: St, depth: usize) -> R {
        if st.back {
            for t in a.terms.iter().rev() {
                self.term(t, st, depth)?;
            }
        } else {
            for t in &a.terms {
                self.term(t, st, depth)?;
            }
        }
        Ok(())
    }

    fn term(&mut self, t: &Term, st: St, depth: usize) -> R {
        match &t.quantifier {
            None => self.kind(&t.kind, st, depth),
            Some(q) => self.quantified(&t.kind, q, st, depth),
        }
    }

    fn kind(&mut self, k: &TermKind, st: St, depth: usize) -> R {
        match k {
            TermKind::Assertion(a) => {
                let extras = self.unicode && st.ic;
                let inst = match a {
                    Assertion::Start => Inst::LineStart { multiline: st.ml },
                    Assertion::End => Inst::LineEnd { multiline: st.ml },
                    Assertion::WordBoundary => Inst::WordBoundary { neg: false, extras },
                    Assertion::NotWordBoundary => Inst::WordBoundary { neg: true, extras },
                };
                self.emit(inst).map(|_| ())
            }
            TermKind::Look(l) => self.look(l, st, depth),
            TermKind::Atom(a) => self.atom(a, st, depth),
        }
    }

    /// Assertion `(?=`, `(?!`, `(?<=`, `(?<!` (§22.2.2.3.2†).
    fn look(&mut self, l: &Look, st: St, depth: usize) -> R {
        let start = self.emit(Inst::LookStart {
            neg: l.negative,
            end: 0,
        })?;
        let inner = St {
            back: l.behind,
            ..st
        };
        self.disjunction(&l.body, inner, depth.saturating_add(1))?;
        self.emit(Inst::LookEnd { neg: l.negative })?;
        let end = self.pc()?;
        self.set(
            start,
            Inst::LookStart {
                neg: l.negative,
                end,
            },
        );
        Ok(())
    }

    fn emit_body(&mut self, b: &Body<'_>, st: St, depth: usize) -> R {
        match b {
            Body::One(o) => self.emit(Inst::One(o.clone())).map(|_| ()),
            Body::Kind(k) => self.kind(k, st, depth),
        }
    }

    /// Term :: Atom Quantifier (§22.2.2.3.1†, RepeatMatcher §22.2.2.3.2†).
    fn quantified(&mut self, k: &TermKind, q: &Quantifier, st: St, depth: usize) -> R {
        let min = to_usize(q.min);
        let max = q.max.map_or(usize::MAX, to_usize);
        // RepeatMatcher step 1: "If max = 0, return c(x)".
        if max == 0 {
            return Ok(());
        }
        let one = match k {
            TermKind::Atom(a) => self.one_of(a, st, depth)?,
            _ => None,
        };
        if q.greedy
            && let Some(o) = &one
        {
            return self
                .emit(Inst::Run {
                    one: o.clone(),
                    min,
                    max,
                })
                .map(|_| ());
        }
        let body = match one {
            Some(o) => Body::One(o),
            None => Body::Kind(k),
        };
        if min == 1 && max == 1 {
            return self.emit_body(&body, st, depth);
        }
        let counter = self.reg()?;
        let pos_reg = self.reg()?;
        self.emit(Inst::CounterInit { reg: counter })?;
        let head = self.emit(Inst::LoopHead {
            counter,
            min,
            max,
            greedy: q.greedy,
            body: 0,
            exit: 0,
        })?;
        let body_pc = self.pc()?;
        // Step 4: "For each integer k in the inclusive interval from
        // parenIndex + 1 to parenIndex + parenCount, set cap[k] to undefined."
        if let Some((first, last)) = cap_range(k) {
            self.emit(Inst::ResetCaps { first, last })?;
        }
        self.emit(Inst::SavePos { reg: pos_reg })?;
        self.emit_body(&body, st, depth)?;
        // Step 2.b: "If min = 0 and y's endIndex = x's endIndex, return
        // failure."
        self.emit(Inst::LoopEnd {
            counter,
            pos_reg,
            min,
            head,
        })?;
        let exit = self.pc()?;
        self.set(
            head,
            Inst::LoopHead {
                counter,
                min,
                max,
                greedy: q.greedy,
                body: body_pc,
                exit,
            },
        );
        Ok(())
    }

    /// The matcher for an atom that is one character, with no captures, or
    /// `None` for the others (groups, backreferences, a class with strings).
    fn one_of(&mut self, a: &Atom, st: St, depth: usize) -> R<Option<One>> {
        let kind = match a {
            Atom::Char(c) => OneKind::Char {
                c: if st.ic {
                    canonicalize(*c, self.unicode)
                } else {
                    *c
                },
                ic: st.ic,
            },
            Atom::Dot => OneKind::Dot { all: st.dot_all },
            Atom::Escape(e) => {
                let mut ops = Vec::new();
                self.escape(e, &mut ops)?;
                let id = self.add_class(ClassProg {
                    ops,
                    ic: st.ic,
                    invert: false,
                    word_extras: self.unicode && st.ic,
                })?;
                OneKind::Class(id)
            }
            Atom::Class(c) => {
                if !self.class_strings_set(c, st, depth)?.is_empty() {
                    return Ok(None);
                }
                let prog = self.class_prog(c, st, depth)?;
                OneKind::Class(self.add_class(prog)?)
            }
            _ => return Ok(None),
        };
        Ok(Some(One {
            kind,
            back: st.back,
        }))
    }

    fn atom(&mut self, a: &Atom, st: St, depth: usize) -> R {
        if let Some(one) = self.one_of(a, st, depth)? {
            return self.emit(Inst::One(one)).map(|_| ());
        }
        match a {
            Atom::Group(g) => self.group(g, st, depth),
            Atom::Modified(m) => {
                // §22.2.1†, RegularExpressionModifiers: `add` turns a flag on
                // and `remove` turns it off, for the body only.
                let flag = |cur: bool, add: bool, remove: bool| (cur || add) && !remove;
                let inner = St {
                    ic: flag(st.ic, m.add.ignore_case, m.remove.ignore_case),
                    ml: flag(st.ml, m.add.multiline, m.remove.multiline),
                    dot_all: flag(st.dot_all, m.add.dot_all, m.remove.dot_all),
                    back: st.back,
                };
                self.disjunction(&m.body, inner, depth.saturating_add(1))
            }
            Atom::BackReference(n) => {
                if *n == 0 || *n > self.capture_count {
                    return Err(CompileError::BackReference(*n));
                }
                self.backref(vec![*n], st)
            }
            Atom::NamedBackReference(name) => {
                let groups: Vec<u32> = self
                    .group_names
                    .iter()
                    .filter(|(n, _)| n == name)
                    .map(|&(_, i)| i)
                    .collect();
                if groups.is_empty() {
                    return Err(CompileError::BackReference(0));
                }
                self.backref(groups, st)
            }
            Atom::Class(c) => self.class_with_strings(c, st, depth),
            // One character, handled by `one_of`.
            Atom::Char(_) | Atom::Dot | Atom::Escape(_) => Ok(()),
        }
    }

    fn backref(&mut self, groups: Vec<u32>, st: St) -> R {
        let id = u32::try_from(self.backrefs.len()).map_err(|_| CompileError::TooLarge)?;
        self.backrefs.push(groups);
        self.emit(Inst::BackRef {
            id,
            ic: st.ic,
            back: st.back,
        })
        .map(|_| ())
    }

    /// Atom :: `(` GroupSpecifier Disjunction `)` (§22.2.2.3.1†): the group
    /// records where it began, and sets the capture when it ends.
    fn group(&mut self, g: &Group, st: St, depth: usize) -> R {
        let inner_depth = depth.saturating_add(1);
        match g.index {
            Some(cap) => {
                let reg = self.reg()?;
                self.emit(Inst::GroupOpen { reg })?;
                self.disjunction(&g.body, st, inner_depth)?;
                self.emit(Inst::GroupClose {
                    cap,
                    reg,
                    back: st.back,
                })
                .map(|_| ())
            }
            None => self.disjunction(&g.body, st, inner_depth),
        }
    }

    /// A `\d`-like escape as a leaf (or, with `v`, a leaf and a `not`).
    fn escape(&self, e: &ClassEscape, ops: &mut Vec<ClassOp>) -> R {
        let (kind, neg) = match e {
            ClassEscape::Digit => (EscKind::Digit, false),
            ClassEscape::NotDigit => (EscKind::Digit, true),
            ClassEscape::Space => (EscKind::Space, false),
            ClassEscape::NotSpace => (EscKind::Space, true),
            ClassEscape::Word => (EscKind::Word, false),
            ClassEscape::NotWord => (EscKind::Word, true),
            ClassEscape::Property { negated, property } => {
                (EscKind::Prop(self.property(property)?), *negated)
            }
        };
        if self.v && neg {
            ops.push(ClassOp::Esc { kind, neg: false });
            ops.push(ClassOp::Not);
        } else {
            ops.push(ClassOp::Esc { kind, neg });
        }
        Ok(())
    }

    /// UnicodePropertyValueExpression (§22.2.2.9†).
    fn property(&self, p: &Property) -> R<Prop> {
        let unsupported = |what: &str, v: &str| {
            CompileError::UnsupportedProperty(format!("{what}={v}: no table is generated"))
        };
        match p {
            Property::GeneralCategory(v) => unicode::category_mask(v)
                .map(Prop::Category)
                .ok_or_else(|| unsupported("General_Category", v)),
            Property::Binary(n) => {
                unicode::binary_property(n).ok_or_else(|| unsupported("binary property", n))
            }
            Property::Script(v) => Err(unsupported("Script", v)),
            Property::ScriptExtensions(v) => Err(unsupported("Script_Extensions", v)),
            Property::Strings(n) => Err(unsupported("property of strings", n)),
        }
    }

    /// CharacterClass (§22.2.2.7† CompileToCharSet) as a postfix program.
    fn class_prog(&self, c: &CharacterClass, st: St, depth: usize) -> R<ClassProg> {
        let mut ops = Vec::new();
        let mut invert = false;
        match &c.contents {
            ClassContents::Ranges(items) => {
                for it in items {
                    match it {
                        ClassItem::Char(x) => ops.push(ClassOp::Char(*x)),
                        ClassItem::Range(a, b) => ops.push(ClassOp::Range(*a, *b)),
                        ClassItem::Escape(e) => self.escape(e, &mut ops)?,
                    }
                }
                ops.push(ClassOp::Or(
                    u32::try_from(items.len()).map_err(|_| CompileError::TooLarge)?,
                ));
                invert = c.negated;
            }
            ClassContents::Set(expr) => {
                self.set_expr(expr, &mut ops, depth.saturating_add(1))?;
                if c.negated {
                    ops.push(ClassOp::Not);
                }
            }
        }
        Ok(ClassProg {
            ops,
            ic: st.ic,
            invert,
            word_extras: self.unicode && st.ic,
        })
    }

    /// ClassSetExpression (`v`): union, intersection or subtraction of its
    /// operands.
    fn set_expr(&self, e: &ClassSetExpr, ops: &mut Vec<ClassOp>, depth: usize) -> R {
        if depth > MAX_DEPTH.saturating_add(2) {
            return Err(CompileError::TooDeep);
        }
        let count = |n: usize| u32::try_from(n).map_err(|_| CompileError::TooLarge);
        match e {
            ClassSetExpr::Union(items) => {
                for it in items {
                    match it {
                        ClassSetItem::Operand(o) => self.operand(o, ops, depth)?,
                        ClassSetItem::Range(a, b) => ops.push(ClassOp::Range(*a, *b)),
                    }
                }
                ops.push(ClassOp::Or(count(items.len())?));
            }
            ClassSetExpr::Intersection(os) => {
                for o in os {
                    self.operand(o, ops, depth)?;
                }
                ops.push(ClassOp::And(count(os.len())?));
            }
            ClassSetExpr::Subtraction(os) => {
                for o in os {
                    self.operand(o, ops, depth)?;
                }
                ops.push(ClassOp::Sub(count(os.len())?));
            }
        }
        Ok(())
    }

    fn operand(&self, o: &ClassSetOperand, ops: &mut Vec<ClassOp>, depth: usize) -> R {
        match o {
            ClassSetOperand::Char(c) => ops.push(ClassOp::Char(*c)),
            ClassSetOperand::Escape(e) => self.escape(e, ops)?,
            ClassSetOperand::Nested { negated, expr } => {
                self.set_expr(expr, ops, depth.saturating_add(1))?;
                if *negated {
                    ops.push(ClassOp::Not);
                }
            }
            ClassSetOperand::Strings(list) => {
                // The one-character strings are characters of the set; the
                // others are in `strings_of`.
                let mut n = 0u32;
                for s in list {
                    if let [c] = s.as_slice() {
                        ops.push(ClassOp::Char(*c));
                        n = n.saturating_add(1);
                    }
                }
                ops.push(ClassOp::Or(n));
            }
        }
        Ok(())
    }

    /// The strings a `v` class can match that are not one character (the empty
    /// string included), folded if the class ignores case; empty for a class
    /// without `v` or a negated one.
    fn class_strings_set(&self, c: &CharacterClass, st: St, depth: usize) -> R<BTreeSet<Vec<u32>>> {
        match &c.contents {
            ClassContents::Set(e) if !c.negated => {
                self.strings_of(e, self.v && st.ic, depth.saturating_add(1))
            }
            _ => Ok(BTreeSet::new()),
        }
    }

    /// The strings of a ClassSetExpression that are not one character:
    /// MayContainStrings's sets (§22.2.1.1†), computed. A union holds those of
    /// its operands, an intersection those of all, a subtraction those of the
    /// first that the others lack.
    fn strings_of(&self, e: &ClassSetExpr, fold: bool, depth: usize) -> R<BTreeSet<Vec<u32>>> {
        if depth > MAX_DEPTH.saturating_add(2) {
            return Err(CompileError::TooDeep);
        }
        let next = depth.saturating_add(1);
        match e {
            ClassSetExpr::Union(items) => {
                let mut out = BTreeSet::new();
                for it in items {
                    if let ClassSetItem::Operand(o) = it {
                        out.extend(self.operand_strings(o, fold, next)?);
                    }
                }
                Ok(out)
            }
            ClassSetExpr::Intersection(os) => {
                let mut it = os.iter();
                let mut out = match it.next() {
                    Some(o) => self.operand_strings(o, fold, next)?,
                    None => BTreeSet::new(),
                };
                for o in it {
                    let other = self.operand_strings(o, fold, next)?;
                    out.retain(|s| other.contains(s));
                }
                Ok(out)
            }
            ClassSetExpr::Subtraction(os) => {
                let mut it = os.iter();
                let mut out = match it.next() {
                    Some(o) => self.operand_strings(o, fold, next)?,
                    None => BTreeSet::new(),
                };
                for o in it {
                    let other = self.operand_strings(o, fold, next)?;
                    out.retain(|s| !other.contains(s));
                }
                Ok(out)
            }
        }
    }

    fn operand_strings(
        &self,
        o: &ClassSetOperand,
        fold: bool,
        depth: usize,
    ) -> R<BTreeSet<Vec<u32>>> {
        match o {
            ClassSetOperand::Char(_) | ClassSetOperand::Escape(_) => Ok(BTreeSet::new()),
            ClassSetOperand::Nested { negated, expr } => {
                if *negated {
                    Ok(BTreeSet::new())
                } else {
                    self.strings_of(expr, fold, depth)
                }
            }
            ClassSetOperand::Strings(list) => Ok(list
                .iter()
                .filter(|s| s.len() != 1)
                .map(|s| {
                    if fold {
                        s.iter().map(|&c| simple_fold(c)).collect()
                    } else {
                        s.clone()
                    }
                })
                .collect()),
        }
    }

    /// A `v` class with strings: the strings longest first, then the single
    /// characters, then the empty string if it is in the set.
    fn class_with_strings(&mut self, c: &CharacterClass, st: St, depth: usize) -> R {
        let set = self.class_strings_set(c, st, depth)?;
        let has_empty = set.contains(&Vec::new());
        let mut multi: Vec<Vec<u32>> = set.into_iter().filter(|s| !s.is_empty()).collect();
        multi.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));
        let prog = self.class_prog(c, st, depth)?;
        let id = self.add_class(prog)?;
        let mut alts: Vec<Alt> = multi.into_iter().map(Alt::Str).collect();
        alts.push(Alt::One(One {
            kind: OneKind::Class(id),
            back: st.back,
        }));
        if has_empty {
            alts.push(Alt::Empty);
        }
        let n = alts.len();
        let mut jumps = Vec::new();
        for (i, alt) in alts.iter().enumerate() {
            let last = i.saturating_add(1) >= n;
            let split = if last {
                None
            } else {
                Some(self.emit(Inst::Split {
                    first: 0,
                    second: 0,
                })?)
            };
            let first = self.pc()?;
            match alt {
                Alt::Str(s) => {
                    let one = |c: u32| One {
                        kind: OneKind::Char {
                            c: if st.ic { simple_fold(c) } else { c },
                            ic: st.ic,
                        },
                        back: st.back,
                    };
                    if st.back {
                        for &c in s.iter().rev() {
                            self.emit(Inst::One(one(c)))?;
                        }
                    } else {
                        for &c in s {
                            self.emit(Inst::One(one(c)))?;
                        }
                    }
                }
                Alt::One(o) => {
                    self.emit(Inst::One(o.clone()))?;
                }
                Alt::Empty => {}
            }
            if let Some(split) = split {
                jumps.push(self.emit(Inst::Jmp(0))?);
                let second = self.pc()?;
                self.set(split, Inst::Split { first, second });
            }
        }
        let end = self.pc()?;
        for j in jumps {
            self.set(j, Inst::Jmp(end));
        }
        Ok(())
    }
}

/// The first and last capture number of the groups inside a term (with the
/// term itself, if it is a group), by an explicit walk: no recursion.
fn cap_range(k: &TermKind) -> Option<(u32, u32)> {
    /// Records a group's number and queues the bodies a kind holds.
    fn visit<'t>(k: &'t TermKind, work: &mut Vec<&'t Disjunction>, lo: &mut u32, hi: &mut u32) {
        match k {
            TermKind::Atom(Atom::Group(g)) => {
                if let Some(i) = g.index {
                    *lo = (*lo).min(i);
                    *hi = (*hi).max(i);
                }
                work.push(&g.body);
            }
            TermKind::Atom(Atom::Modified(m)) => work.push(&m.body),
            TermKind::Look(l) => work.push(&l.body),
            _ => {}
        }
    }
    let mut lo = u32::MAX;
    let mut hi = 0u32;
    let mut work: Vec<&Disjunction> = Vec::new();
    visit(k, &mut work, &mut lo, &mut hi);
    while let Some(d) = work.pop() {
        for alt in &d.alternatives {
            for t in &alt.terms {
                visit(&t.kind, &mut work, &mut lo, &mut hi);
            }
        }
    }
    (hi != 0).then_some((lo, hi))
}
