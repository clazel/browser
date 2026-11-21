//! The matcher: a loop over a [`Program`]'s instructions and an explicit
//! backtrack stack of bounded size. ECMA-262 §22.2.2† (Pattern Semantics),
//! with `[[Input]]` the code units of the string (read as code points with `u`
//! or `v`). Section numbers marked † are from memory.
//!
//! # Modelling choices
//!
//! - **No recursion**, over the pattern or over the input: the standard's
//!   closures became instructions ([`crate::compile`]) and a failure is a pop.
//!   Every choice point is a stack entry, and so is every change to a
//!   register (a capture, a loop counter) that a failure must undo.
//! - **A bounded stack, the one deviation.** The stack holds at most
//!   [`Limits::max_stack`] entries; a match that needs more is
//!   [`MatchError::StackOverflow`], where the standard has no limit. The
//!   engine turns it into a `RangeError` (phase-7.md item 7.10). The `Vec`
//!   grows by doubling, so its allocation can be up to twice that many
//!   entries. The registers and the class scratch space depend only on the
//!   pattern.
//! - **A step budget and an interrupt hook** (phase-7.md 7.0(g)): every
//!   instruction, every entry popped and every character a greedy run
//!   consumed is a step; past [`Limits::max_steps`] the match is
//!   [`MatchError::StepLimit`], and every 4096 steps the hook is asked
//!   whether to stop ([`MatchError::Interrupted`]). A catastrophic pattern
//!   runs until one of these, or until the stack is full.
//! - **Indices** are code unit indices, in both modes. In `u`/`v` mode a match
//!   that starts inside a surrogate pair starts at the pair's first unit
//!   (RegExpBuiltinExec §22.2.7.2† step 12.a: the input index is that of the
//!   character that contains the code unit `lastIndex`), and an unanchored
//!   search advances by whole code points (AdvanceStringIndex §22.2.7.3†).
//! - **`lastIndex`, `g` and `y`** are the caller's: [`Program::exec`] takes a
//!   start index and says whether to try only there (`y`) or to scan forward.
//! - **Lookaround** bodies are atomic (§22.2.2.3.2† Assertion: the body is
//!   matched with a continuation that returns its state): when a positive
//!   lookahead's body has matched, its choices are dropped, its captures kept.
//!   A negative one that matches undoes everything its body did.

use crate::program::{ClassOp, ClassProg, EscKind, Inst, One, OneKind, Program};
use crate::stack::{BtStack, Entry};
use crate::unicode::{canonicalize, equivalents};

/// The value of a register that holds no position.
const NONE: usize = usize::MAX;

/// How many steps pass between asks of the interrupt hook.
const TICK: u64 = 4096;

/// The matcher's resource limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most entries the backtrack stack may hold (16 to 24 bytes each).
    pub max_stack: usize,
    /// The most steps one [`Program::exec`] may take, or `None` for no limit.
    pub max_steps: Option<u64>,
}

impl Default for Limits {
    /// A million stack entries (at most 24 MB, 48 with the `Vec`'s growth) and no
    /// step limit.
    fn default() -> Limits {
        Limits {
            max_stack: 1 << 20,
            max_steps: None,
        }
    }
}

/// Why a match was abandoned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MatchError {
    /// The backtrack stack reached [`Limits::max_stack`] entries. The engine
    /// throws a `RangeError`.
    StackOverflow,
    /// [`Limits::max_steps`] steps were taken.
    StepLimit,
    /// The interrupt hook returned `true`.
    Interrupted,
    /// The program is malformed (an instruction or register that does not
    /// exist). Not reachable from [`crate::compile`]'s output.
    Corrupt,
}

impl core::fmt::Display for MatchError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MatchError::StackOverflow => write!(f, "regular expression backtrack stack is full"),
            MatchError::StepLimit => write!(f, "regular expression step limit reached"),
            MatchError::Interrupted => write!(f, "regular expression match interrupted"),
            MatchError::Corrupt => write!(f, "malformed regular expression program"),
        }
    }
}

/// A successful match: the whole match and each group's capture, as code unit
/// indices `(start, end)`, or `None` for a group that did not take part.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Match {
    /// Index 0 is the whole match; index `n` is group `n`.
    pub captures: Vec<Option<(usize, usize)>>,
}

impl Match {
    /// The capture of group `n` (0 for the whole match).
    #[must_use]
    pub fn get(&self, n: usize) -> Option<(usize, usize)> {
        self.captures.get(n).copied().flatten()
    }
}

impl Program {
    /// Matches the pattern against `input`, starting at code unit index
    /// `start`.
    ///
    /// With `sticky` the match must start at `start` (the `y` flag); without,
    /// the starting index advances until a match is found or the input ends
    /// (RegExpBuiltinExec §22.2.7.2†, steps 12 and 13). The caller decides
    /// `start` (`lastIndex`, or 0) and what to do with the result.
    ///
    /// `interrupt`, if given, is asked every 4096 steps whether to stop.
    ///
    /// # Errors
    ///
    /// [`MatchError`]: a limit of `limits` was reached, or the hook said stop.
    pub fn exec(
        &self,
        input: &[u16],
        start: usize,
        sticky: bool,
        limits: &Limits,
        interrupt: Option<&mut dyn FnMut() -> bool>,
    ) -> Result<Option<Match>, MatchError> {
        if start > input.len() {
            return Ok(None);
        }
        let mut vm = Vm {
            prog: self,
            input,
            regs: vec![NONE; self.regs],
            stack: BtStack::new(limits.max_stack),
            steps: 0,
            max_steps: limits.max_steps.unwrap_or(u64::MAX),
            next_tick: TICK,
            hook: interrupt,
            eq: Vec::new(),
            bools: Vec::new(),
            end: 0,
        };
        let unicode = self.unicode;
        let mut s = start;
        // Inside a surrogate pair, the character that contains the unit is the
        // pair.
        if unicode
            && s > 0
            && input.get(s).is_some_and(|u| (0xDC00..0xE000).contains(u))
            && s.checked_sub(1)
                .and_then(|p| input.get(p))
                .is_some_and(|u| (0xD800..0xDC00).contains(u))
        {
            s = s.saturating_sub(1);
        }
        loop {
            if vm.run(s)? {
                return Ok(Some(vm.take_match(s)));
            }
            if sticky || s >= input.len() {
                return Ok(None);
            }
            // AdvanceStringIndex.
            s = match read(input, unicode, s, false) {
                Some((_, next)) => next,
                None => return Ok(None),
            };
        }
    }
}

struct Vm<'a, 'h> {
    prog: &'a Program,
    input: &'a [u16],
    regs: Vec<usize>,
    stack: BtStack,
    steps: u64,
    max_steps: u64,
    next_tick: u64,
    hook: Option<&'h mut dyn FnMut() -> bool>,
    /// Scratch space for class matching.
    eq: Vec<u32>,
    bools: Vec<bool>,
    /// Where the last successful run ended.
    end: usize,
}

/// A code point from a high and a low surrogate.
fn combine(high: u16, low: u16) -> u32 {
    0x10000u32
        .wrapping_add(u32::from(high.wrapping_sub(0xD800)).wrapping_mul(0x400))
        .wrapping_add(u32::from(low.wrapping_sub(0xDC00)))
}

/// The character at `pos` (forward) or ending at `pos` (backward), and the
/// position past (before) it: a code unit, or with `unicode` a code point.
pub(crate) fn read(input: &[u16], unicode: bool, pos: usize, back: bool) -> Option<(u32, usize)> {
    if back {
        let p1 = pos.checked_sub(1)?;
        let u = *input.get(p1)?;
        if unicode
            && (0xDC00..0xE000).contains(&u)
            && let Some(p0) = p1.checked_sub(1)
            && let Some(&h) = input.get(p0)
            && (0xD800..0xDC00).contains(&h)
        {
            return Some((combine(h, u), p0));
        }
        Some((u32::from(u), p1))
    } else {
        let u = *input.get(pos)?;
        let p1 = pos.saturating_add(1);
        if unicode
            && (0xD800..0xDC00).contains(&u)
            && let Some(&l) = input.get(p1)
            && (0xDC00..0xE000).contains(&l)
        {
            return Some((combine(u, l), p1.saturating_add(1)));
        }
        Some((u32::from(u), p1))
    }
}

/// LineTerminator (§12.3†).
fn is_line_terminator(c: u32) -> bool {
    matches!(c, 0x0A | 0x0D | 0x2028 | 0x2029)
}

/// WhiteSpace and LineTerminator (§12.2†, §12.3†): what `\s` matches.
fn is_space(c: u32) -> bool {
    matches!(
        c,
        0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x20 | 0xA0 | 0x1680 | 0x2000
            ..=0x200A | 0x2028 | 0x2029 | 0x202F | 0x205F | 0x3000 | 0xFEFF
    )
}

/// WordCharacters (§22.2.2.9†): ASCII letters, digits and `_`, and with
/// `extras` (`u` or `v` with `i`) the two characters that fold to them.
fn is_word(c: u32, extras: bool) -> bool {
    matches!(c, 0x30..=0x39 | 0x41..=0x5A | 0x61..=0x7A | 0x5F)
        || (extras && matches!(c, 0x17F | 0x212A))
}

fn escape_has(kind: &EscKind, c: u32, extras: bool) -> bool {
    match kind {
        EscKind::Digit => (0x30..=0x39).contains(&c),
        EscKind::Space => is_space(c),
        EscKind::Word => is_word(c, extras),
        EscKind::Prop(p) => p.contains(c),
    }
}

/// CharacterSetMatcher (§22.2.2.7.1†) for a class: whether the input
/// character `ch` is matched. Runs the class's postfix program on a stack of
/// booleans.
fn class_matches(
    cls: &ClassProg,
    unicode: bool,
    ch: u32,
    eq: &mut Vec<u32>,
    st: &mut Vec<bool>,
) -> bool {
    eq.clear();
    if cls.ic {
        // Step 3: "there exists a member a of A such that Canonicalize(rer, a)
        // is cc", with cc the canonical form of the input character.
        equivalents(canonicalize(ch, unicode), unicode, eq);
    } else {
        eq.push(ch);
    }
    st.clear();
    for op in &cls.ops {
        match op {
            ClassOp::Char(c) => st.push(eq.contains(c)),
            ClassOp::Range(lo, hi) => st.push(eq.iter().any(|a| lo <= a && a <= hi)),
            ClassOp::Esc { kind, neg } => st.push(
                eq.iter()
                    .any(|&a| escape_has(kind, a, cls.word_extras) != *neg),
            ),
            ClassOp::Not => {
                let t = st.pop().unwrap_or(false);
                st.push(!t);
            }
            ClassOp::Or(n) => {
                let mut acc = false;
                for _ in 0..*n {
                    acc |= st.pop().unwrap_or(false);
                }
                st.push(acc);
            }
            ClassOp::And(n) => {
                let mut acc = true;
                for _ in 0..*n {
                    acc &= st.pop().unwrap_or(false);
                }
                st.push(acc);
            }
            ClassOp::Sub(n) => {
                // The operands were pushed in order, so the first is popped last.
                let mut first = false;
                let mut rest = false;
                for i in 0..*n {
                    let v = st.pop().unwrap_or(false);
                    if i.saturating_add(1) == *n {
                        first = v;
                    } else {
                        rest |= v;
                    }
                }
                st.push(first && !rest);
            }
        }
    }
    let found = st.pop().unwrap_or(false);
    found != cls.invert
}

impl Vm<'_, '_> {
    fn tick(&mut self, n: u64) -> Result<(), MatchError> {
        self.steps = self.steps.saturating_add(n);
        if self.steps > self.max_steps {
            return Err(MatchError::StepLimit);
        }
        if self.steps >= self.next_tick {
            self.next_tick = self.steps.saturating_add(TICK);
            let stop = match self.hook {
                Some(ref mut h) => h(),
                None => false,
            };
            if stop {
                return Err(MatchError::Interrupted);
            }
        }
        Ok(())
    }

    fn push(&mut self, e: Entry) -> Result<(), MatchError> {
        self.stack.push(e).map_err(|_| MatchError::StackOverflow)
    }

    fn reg(&self, r: u32) -> Result<usize, MatchError> {
        self.regs
            .get(r as usize)
            .copied()
            .ok_or(MatchError::Corrupt)
    }

    /// Writes a register, and pushes what undoes it.
    fn set(&mut self, r: u32, v: usize) -> Result<(), MatchError> {
        let slot = self.regs.get_mut(r as usize).ok_or(MatchError::Corrupt)?;
        let old = *slot;
        *slot = v;
        self.push(Entry::Restore { reg: r, old })
    }

    fn restore(&mut self, r: u32, old: usize) {
        if let Some(slot) = self.regs.get_mut(r as usize) {
            *slot = old;
        }
    }

    /// Matches one character at `pos` (CharacterSetMatcher §22.2.2.7.1† and
    /// the matchers for a character and for `.`), returning the new position.
    fn step_one(&mut self, one: &One, pos: usize) -> Option<usize> {
        let unicode = self.prog.unicode;
        let (ch, np) = read(self.input, unicode, pos, one.back)?;
        let ok = match &one.kind {
            OneKind::Char { c, ic } => {
                if *ic {
                    canonicalize(ch, unicode) == *c
                } else {
                    ch == *c
                }
            }
            OneKind::Dot { all } => *all || !is_line_terminator(ch),
            OneKind::Class(id) => {
                let cls = self.prog.classes.get(*id as usize)?;
                class_matches(cls, unicode, ch, &mut self.eq, &mut self.bools)
            }
        };
        ok.then_some(np)
    }

    /// BackreferenceMatcher (§22.2.2.7.2†) against the capture `s..e`: the
    /// new position, or `None` if the text does not match.
    fn backref(&self, s: usize, e: usize, pos: usize, ic: bool, back: bool) -> Option<usize> {
        let unicode = self.prog.unicode;
        let input = self.input;
        if !ic && !unicode {
            let len = e.checked_sub(s)?;
            let target = if back {
                pos.checked_sub(len)?
            } else {
                pos.checked_add(len)?
            };
            let (from, to) = if back { (target, pos) } else { (pos, target) };
            let a = input.get(s..e)?;
            let b = input.get(from..to)?;
            return (a == b).then_some(target);
        }
        let canon = |c: u32| if ic { canonicalize(c, unicode) } else { c };
        let mut b = pos;
        if back {
            let mut a = e;
            while a > s {
                let (c1, na) = read(input, unicode, a, true)?;
                let (c2, nb) = read(input, unicode, b, true)?;
                if canon(c1) != canon(c2) {
                    return None;
                }
                a = na;
                b = nb;
            }
        } else {
            let mut a = s;
            while a < e {
                let (c1, na) = read(input, unicode, a, false)?;
                let (c2, nb) = read(input, unicode, b, false)?;
                if canon(c1) != canon(c2) {
                    return None;
                }
                a = na;
                b = nb;
            }
        }
        Some(b)
    }

    /// The instruction `Run`: as many repetitions as match, up to `max`; fail
    /// if fewer than `min`; leave one stack entry for the shorter runs.
    fn run_loop(
        &mut self,
        one: &One,
        min: usize,
        max: usize,
        pos: usize,
        next_pc: usize,
    ) -> Result<Option<(usize, usize)>, MatchError> {
        let mut p = pos;
        let mut limit = pos;
        let mut count = 0usize;
        while count < max {
            match self.step_one(one, p) {
                Some(np) => {
                    p = np;
                    count = count.saturating_add(1);
                    if count == min {
                        limit = p;
                    }
                }
                None => break,
            }
        }
        self.tick(u64::try_from(count).unwrap_or(u64::MAX))?;
        if count < min {
            return Ok(None);
        }
        if p != limit {
            let pc = u32::try_from(next_pc).map_err(|_| MatchError::Corrupt)?;
            self.push(Entry::Run {
                pc,
                back: one.back,
                cur: p,
                limit,
            })?;
        }
        Ok(Some((next_pc, p)))
    }

    /// Pops the stack, undoing registers, to the nearest choice: the `pc` and
    /// position to resume at, or `None` if there is none (the match failed).
    fn backtrack(&mut self) -> Result<Option<(usize, usize)>, MatchError> {
        let unicode = self.prog.unicode;
        loop {
            let Some(e) = self.stack.pop() else {
                return Ok(None);
            };
            self.tick(1)?;
            match e {
                Entry::Branch { pc, pos } => return Ok(Some((pc as usize, pos))),
                Entry::Restore { reg, old } => self.restore(reg, old),
                Entry::Run {
                    pc,
                    back,
                    cur,
                    limit,
                } => {
                    // One character nearer to the limit, never past it.
                    let n = if back {
                        read(self.input, unicode, cur, false)
                            .map_or(limit, |(_, np)| np)
                            .min(limit)
                    } else {
                        read(self.input, unicode, cur, true)
                            .map_or(limit, |(_, np)| np)
                            .max(limit)
                    };
                    if n != limit {
                        self.push(Entry::Run {
                            pc,
                            back,
                            cur: n,
                            limit,
                        })?;
                    }
                    return Ok(Some((pc as usize, n)));
                }
                Entry::LookMark { neg, pc, pos } => {
                    // The body of a lookaround failed: a negative one succeeds.
                    if neg {
                        return Ok(Some((pc as usize, pos)));
                    }
                }
            }
        }
    }

    /// A negative lookaround whose body matched: undo what the body did, down
    /// to and including its mark. The caller then fails.
    fn unwind_look(&mut self) -> Result<(), MatchError> {
        loop {
            let Some(e) = self.stack.pop() else {
                return Err(MatchError::Corrupt);
            };
            self.tick(1)?;
            match e {
                Entry::Restore { reg, old } => self.restore(reg, old),
                Entry::LookMark { .. } => return Ok(()),
                Entry::Branch { .. } | Entry::Run { .. } => {}
            }
        }
    }

    /// Runs the program from the beginning at input position `start`: whether
    /// it matched. On a match, the registers hold the captures and `end` the
    /// end of the whole match.
    fn run(&mut self, start: usize) -> Result<bool, MatchError> {
        let prog = self.prog;
        self.regs.fill(NONE);
        self.stack.clear();
        let input = self.input;
        let mut pc = 0usize;
        let mut pos = start;
        loop {
            self.tick(1)?;
            let inst = prog.insts.get(pc).ok_or(MatchError::Corrupt)?;
            let next = pc.saturating_add(1);
            let step: Option<(usize, usize)> = match inst {
                Inst::One(one) => self.step_one(one, pos).map(|np| (next, np)),
                Inst::Run { one, min, max } => self.run_loop(one, *min, *max, pos, next)?,
                Inst::LineStart { multiline } => {
                    // §22.2.2.6.1† Assertion, `^`.
                    let at_start = pos == 0
                        || (*multiline
                            && pos
                                .checked_sub(1)
                                .and_then(|p| input.get(p))
                                .is_some_and(|&u| is_line_terminator(u32::from(u))));
                    at_start.then_some((next, pos))
                }
                Inst::LineEnd { multiline } => {
                    // `$`.
                    let at_end = pos >= input.len()
                        || (*multiline
                            && input
                                .get(pos)
                                .is_some_and(|&u| is_line_terminator(u32::from(u))));
                    at_end.then_some((next, pos))
                }
                Inst::WordBoundary { neg, extras } => {
                    // `\b`, `\B`: IsWordChar(e - 1) and IsWordChar(e).
                    let before = pos
                        .checked_sub(1)
                        .and_then(|p| input.get(p))
                        .is_some_and(|&u| is_word(u32::from(u), *extras));
                    let after = input
                        .get(pos)
                        .is_some_and(|&u| is_word(u32::from(u), *extras));
                    ((before != after) != *neg).then_some((next, pos))
                }
                Inst::BackRef { id, ic, back } => {
                    let groups = prog.backrefs.get(*id as usize).ok_or(MatchError::Corrupt)?;
                    let mut cap = None;
                    for &g in groups {
                        let a = g.saturating_mul(2);
                        let s = self.reg(a)?;
                        if s != NONE {
                            cap = Some((s, self.reg(a.saturating_add(1))?));
                            break;
                        }
                    }
                    match cap {
                        // "If r is undefined, return c(x)."
                        None => Some((next, pos)),
                        Some((s, e)) => self.backref(s, e, pos, *ic, *back).map(|np| (next, np)),
                    }
                }
                Inst::Split { first, second } => {
                    self.push(Entry::Branch { pc: *second, pos })?;
                    Some((*first as usize, pos))
                }
                Inst::Jmp(t) => Some((*t as usize, pos)),
                Inst::GroupOpen { reg } => {
                    self.set(*reg, pos)?;
                    Some((next, pos))
                }
                Inst::GroupClose { cap, reg, back } => {
                    let s = self.reg(*reg)?;
                    let (a, b) = if *back { (pos, s) } else { (s, pos) };
                    let r = cap.saturating_mul(2);
                    self.set(r, a)?;
                    self.set(r.saturating_add(1), b)?;
                    Some((next, pos))
                }
                Inst::ResetCaps { first, last } => {
                    for i in *first..=*last {
                        let r = i.saturating_mul(2);
                        if self.reg(r)? != NONE {
                            self.set(r, NONE)?;
                            self.set(r.saturating_add(1), NONE)?;
                        }
                    }
                    Some((next, pos))
                }
                Inst::CounterInit { reg } => {
                    self.set(*reg, 0)?;
                    Some((next, pos))
                }
                Inst::SavePos { reg } => {
                    self.set(*reg, pos)?;
                    Some((next, pos))
                }
                Inst::LoopHead {
                    counter,
                    min,
                    max,
                    greedy,
                    body,
                    exit,
                } => {
                    let n = self.reg(*counter)?;
                    if n < *min {
                        Some((*body as usize, pos))
                    } else if n >= *max {
                        Some((*exit as usize, pos))
                    } else if *greedy {
                        self.push(Entry::Branch { pc: *exit, pos })?;
                        Some((*body as usize, pos))
                    } else {
                        self.push(Entry::Branch { pc: *body, pos })?;
                        Some((*exit as usize, pos))
                    }
                }
                Inst::LoopEnd {
                    counter,
                    pos_reg,
                    min,
                    head,
                } => {
                    let n = self.reg(*counter)?;
                    let began = self.reg(*pos_reg)?;
                    if n >= *min && began == pos {
                        None
                    } else {
                        self.set(*counter, n.saturating_add(1))?;
                        Some((*head as usize, pos))
                    }
                }
                Inst::LookStart { neg, end } => {
                    self.push(Entry::LookMark {
                        neg: *neg,
                        pc: *end,
                        pos,
                    })?;
                    Some((next, pos))
                }
                Inst::LookEnd { neg } => {
                    if *neg {
                        self.unwind_look()?;
                        None
                    } else {
                        let (p, work) = self.stack.commit_look().ok_or(MatchError::Corrupt)?;
                        self.tick(u64::try_from(work).unwrap_or(u64::MAX))?;
                        Some((next, p))
                    }
                }
                Inst::Match => {
                    self.end = pos;
                    return Ok(true);
                }
            };
            match step {
                Some((p, q)) => {
                    pc = p;
                    pos = q;
                }
                None => match self.backtrack()? {
                    Some((p, q)) => {
                        pc = p;
                        pos = q;
                    }
                    None => return Ok(false),
                },
            }
        }
    }

    fn take_match(&self, start: usize) -> Match {
        let mut captures = Vec::new();
        captures.push(Some((start, self.end)));
        let n = self.prog.capture_count;
        for i in 1..=n {
            let a = usize::try_from(i.saturating_mul(2)).unwrap_or(usize::MAX);
            let s = self.regs.get(a).copied().unwrap_or(NONE);
            let e = self.regs.get(a.saturating_add(1)).copied().unwrap_or(NONE);
            captures.push((s != NONE && e != NONE).then_some((s, e)));
        }
        Match { captures }
    }
}
