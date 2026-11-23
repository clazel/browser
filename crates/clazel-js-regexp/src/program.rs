//! The compiled form of a pattern: a list of instructions for the backtracking
//! matcher of [`crate::vm`].
//!
//! The standard (ECMA-262 §22.2.2†) defines matching with closures: each
//! Matcher takes a state and a continuation. An instruction list is the same
//! thing with the continuation made explicit, so the matcher can be a loop
//! over a heap stack instead of recursion. [`crate::compile`] does that
//! translation, one production at a time, and cites the algorithm it takes
//! each instruction from.

use crate::unicode::Prop;

/// A matcher for one character (a code unit, or with `u`/`v` a code point).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum OneKind {
    /// A character; with `ic`, `c` is already canonicalized and the input's
    /// character is too, before the comparison.
    Char {
        /// The character.
        c: u32,
        /// `i` is on.
        ic: bool,
    },
    /// `.`: any character, or any but a line terminator.
    Dot {
        /// `s` is on.
        all: bool,
    },
    /// A character class, by index into [`Program::classes`].
    Class(u32),
}

/// [`OneKind`] and the direction it reads in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct One {
    pub(crate) kind: OneKind,
    /// Reads the character before the position, and moves back (lookbehind).
    pub(crate) back: bool,
}

/// An instruction. `pc` values are indices into [`Program::insts`]; register
/// numbers index [`Program`]'s registers (the captures come first: capture
/// `n` is registers `2n` and `2n + 1`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Inst {
    /// Match one character and move past it.
    One(One),
    /// A greedy loop over one character, `min` to `max` times, as one
    /// instruction and one stack entry (RepeatMatcher, §22.2.2.3.1†).
    Run {
        /// The character.
        one: One,
        /// The least number of repetitions.
        min: usize,
        /// The most.
        max: usize,
    },
    /// `^` (§22.2.2.6.1† Assertion, step for `^`).
    LineStart {
        /// `m` is on.
        multiline: bool,
    },
    /// `$`.
    LineEnd {
        /// `m` is on.
        multiline: bool,
    },
    /// `\b` and `\B`.
    WordBoundary {
        /// `\B`.
        neg: bool,
        /// `u` or `v` with `i`: U+017F and U+212A are word characters.
        extras: bool,
    },
    /// A backreference (BackreferenceMatcher, §22.2.2.7.2†): the first group
    /// of the list `Program::backrefs[id]` that has a capture is the one used.
    BackRef {
        /// Index into the program's list of group lists.
        id: u32,
        /// `i` is on.
        ic: bool,
        /// Matches backwards.
        back: bool,
    },
    /// Try `first`, and on failure `second`.
    Split {
        /// Tried first.
        first: u32,
        /// Tried after `first` fails.
        second: u32,
    },
    /// Go to `target`.
    Jmp(u32),
    /// A capturing group begins: remember the position in `reg`.
    GroupOpen {
        /// The register.
        reg: u32,
    },
    /// A capturing group ends: capture `cap` becomes the text between the
    /// remembered position and this one.
    GroupClose {
        /// The capture's number.
        cap: u32,
        /// The register `GroupOpen` wrote.
        reg: u32,
        /// The group was matched backwards, so the end comes first.
        back: bool,
    },
    /// Undefine captures `first` to `last` (RepeatMatcher step 4).
    ResetCaps {
        /// The first capture.
        first: u32,
        /// The last.
        last: u32,
    },
    /// Set a loop's counter to zero.
    CounterInit {
        /// The register.
        reg: u32,
    },
    /// The top of a general loop (RepeatMatcher steps 1, 5, 6 and 7).
    LoopHead {
        /// The counter's register.
        counter: u32,
        /// The least number of iterations.
        min: usize,
        /// The most.
        max: usize,
        /// No `?` after the quantifier.
        greedy: bool,
        /// The first instruction of the body.
        body: u32,
        /// The instruction after the loop.
        exit: u32,
    },
    /// Remember the position a loop iteration began at.
    SavePos {
        /// The register.
        reg: u32,
    },
    /// The end of a loop iteration (RepeatMatcher step 2.b): an iteration
    /// beyond the least number that matched nothing fails; else count it.
    LoopEnd {
        /// The counter's register.
        counter: u32,
        /// The register `SavePos` wrote.
        pos_reg: u32,
        /// The least number of iterations.
        min: usize,
        /// The instruction of the loop's `LoopHead`.
        head: u32,
    },
    /// The start of a lookaround's body (§22.2.2.3.2† Assertion).
    LookStart {
        /// `(?!` and `(?<!`.
        neg: bool,
        /// The instruction after the lookaround.
        end: u32,
    },
    /// The end of a lookaround's body.
    LookEnd {
        /// `(?!` and `(?<!`.
        neg: bool,
    },
    /// The pattern matched.
    Match,
}

/// An escape in a class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EscKind {
    /// `\d`.
    Digit,
    /// `\s`.
    Space,
    /// `\w`.
    Word,
    /// `\p{..}`.
    Prop(Prop),
}

/// One step of a class's postfix program (a stack machine over booleans: does
/// the character belong to the set so far).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ClassOp {
    /// Push whether the character is `c`.
    Char(u32),
    /// Push whether the character is in `lo..=hi`.
    Range(u32, u32),
    /// Push whether the character is in the escape's set (or, with `neg`, in
    /// its complement).
    Esc { kind: EscKind, neg: bool },
    /// Replace the top by its negation.
    Not,
    /// Replace the top `n` by their disjunction (false for none).
    Or(u32),
    /// Replace the top `n` by their conjunction.
    And(u32),
    /// Replace the top `n` by: the deepest of them, and none of the rest
    /// (ClassSubtraction).
    Sub(u32),
}

/// A character class as a postfix program over its leaves. See
/// [`crate::compile`] for how each of the standard's set operations maps to it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClassProg {
    pub(crate) ops: Vec<ClassOp>,
    /// `i` is on: a leaf holds if it holds for some character with the same
    /// `Canonicalize` as the input's (CharacterSetMatcher, §22.2.2.7.1†).
    pub(crate) ic: bool,
    /// The class is `[^..]` without `v` (with `v`, a `Not` op does it).
    pub(crate) invert: bool,
    /// `\w` includes U+017F and U+212A (`u` or `v`, with `i`).
    pub(crate) word_extras: bool,
}

/// A compiled pattern: see [`crate::compile`] and [`Program::exec`].
#[derive(Debug, Clone)]
pub struct Program {
    pub(crate) insts: Vec<Inst>,
    pub(crate) classes: Vec<ClassProg>,
    pub(crate) backrefs: Vec<Vec<u32>>,
    pub(crate) regs: usize,
    pub(crate) capture_count: u32,
    pub(crate) unicode: bool,
    pub(crate) group_names: Vec<(Vec<u32>, u32)>,
}

impl Program {
    /// The number of capturing groups (not counting the whole match).
    #[must_use]
    pub fn capture_count(&self) -> u32 {
        self.capture_count
    }

    /// Every named group, as its name (code points) and its number: the
    /// parser's [`crate::ast::Pattern::group_names`].
    #[must_use]
    pub fn group_names(&self) -> &[(Vec<u32>, u32)] {
        &self.group_names
    }

    /// Whether the pattern reads code points (`u` or `v`) rather than code
    /// units.
    #[must_use]
    pub fn unicode(&self) -> bool {
        self.unicode
    }

    /// The group named `name` that took part in `m` (§22.2.2.3.1†'s duplicate
    /// named groups: at most one does): its capture, if any.
    #[must_use]
    pub fn named_capture(&self, m: &crate::vm::Match, name: &[u32]) -> Option<(usize, usize)> {
        self.group_names
            .iter()
            .filter(|(n, _)| n.as_slice() == name)
            .find_map(|&(_, i)| m.captures.get(usize::try_from(i).ok()?).copied().flatten())
    }
}
