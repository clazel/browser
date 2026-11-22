//! The ways a pattern or a flag string is rejected.

/// Why a pattern is a Syntax Error (§22.2.1† and §22.2.1.1†, Annex B §B.1.2†).
///
/// The variants group the grammar's failures and its early errors by the
/// production they come from; the position in [`Error`] says where the parser
/// stopped, not where a person would point.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// More than [`crate::MAX_DEPTH`] nested groups, lookarounds and classes.
    /// An engine-defined limit (the standard has none): the parser is
    /// recursive, and this bounds the stack it uses.
    TooDeep,
    /// A pattern with 2^32 - 1 or more capturing groups (§22.2.1.1†).
    TooManyGroups,
    /// `)` with no `(` before it.
    UnmatchedCloseParen,
    /// A `(` whose `)` is missing.
    UnterminatedGroup,
    /// A `[` whose `]` is missing.
    UnterminatedClass,
    /// A quantifier (`*`, `+`, `?`, `{n}`) with no atom before it, or after
    /// an assertion that cannot be quantified.
    NothingToRepeat,
    /// `{n,m}` with `n` greater than `m` (§22.2.1.1†, QuantifierPrefix).
    QuantifierOutOfOrder,
    /// Annex B's `InvalidBracedQuantifier`: `{1}`, `{1,}` or `{1,2}` where
    /// an atom is expected (§B.1.2†, without `u` or `v`).
    InvalidBracedQuantifier,
    /// `{`, `}` or `]` standing for itself, with `u` or `v` set.
    LoneBracket,
    /// A `\` at the end of the pattern.
    TrailingBackslash,
    /// A `\` followed by something that is no escape (with `u` or `v`, or
    /// `\k` where the pattern has named groups).
    InvalidEscape,
    /// `\x`, `\u` or `\u{..}` that is malformed, or out of range, with `u`
    /// or `v`.
    InvalidUnicodeEscape,
    /// `\c` without a letter, with `u` or `v`.
    InvalidControlEscape,
    /// A decimal escape (backreference) larger than the number of capturing
    /// groups, with `u` or `v`; `\0` followed by a digit, with `u` or `v`;
    /// `\1` to `\9` in a class, with `u` or `v`.
    InvalidDecimalEscape,
    /// A `(?` that begins no group (§22.2.1†, Atom).
    InvalidGroupSpecifier,
    /// A group name that is not a RegExpIdentifierName, or is unterminated.
    InvalidGroupName,
    /// Two groups with one name that can take part in one match
    /// (§22.2.1.1†, Pattern).
    DuplicateGroupName,
    /// `\k<name>` where no group has that name.
    UndeclaredGroupName,
    /// `\k` not followed by `<name>`, in a pattern with named groups.
    MissingGroupName,
    /// Modifiers (`(?i-m:`) that are empty, repeated or contradictory
    /// (§22.2.1.1†, Atom).
    InvalidModifiers,
    /// A class escape (`\d`, `\p{..}`) as an end of a range, with `u` or `v`.
    ClassEscapeInRange,
    /// A range whose first end is greater than its last.
    RangeOutOfOrder,
    /// A `\p` or `\P` that is not `\p{Name}` or `\p{Name=Value}`, or names a
    /// property that does not exist.
    InvalidProperty,
    /// `v` mode: a character that must be escaped in a class, or one of the
    /// reserved double punctuators (`&&`, `!!`, ...).
    InvalidClassSetCharacter,
    /// `v` mode: `&&` or `--` mixed with a union, or with each other, or a
    /// range as an operand.
    InvalidClassSetOperation,
    /// `v` mode: a negated class (`[^..]`, `\P{..}`) that can match strings.
    NegatedClassMayContainStrings,
    /// `v` mode: a malformed `\q{..}`.
    InvalidClassStringDisjunction,
}

/// A rejected pattern.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Error {
    /// Why.
    pub kind: ErrorKind,
    /// An index into the pattern's code units where the parser stopped (at
    /// most the pattern's length).
    pub at: usize,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?} at {}", self.kind, self.at)
    }
}

/// Why a flag string is a Syntax Error (§13.2.7.1†, §22.2.3.4†).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FlagsError {
    /// A code unit that is not one of `d g i m s u v y`.
    Invalid,
    /// A flag written twice.
    Duplicate,
    /// Both `u` and `v`.
    UnicodeAndUnicodeSets,
}
