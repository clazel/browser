//! The syntax tree of a pattern: one node kind per production of §22.2.1†
//! that carries meaning (punctuation and productions that only choose
//! between alternatives are folded away).
//!
//! Character values are `u32`: a code point with `u` or `v`, a code unit
//! without (so a lone surrogate is possible in both). Group names are code
//! points.

/// The parsed pattern: Pattern :: Disjunction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pattern {
    /// The pattern's body.
    pub disjunction: Disjunction,
    /// CountLeftCapturingParensWithin of the pattern: the number of capturing
    /// groups, named or not.
    pub capture_count: u32,
    /// Every named group, in source order, as its name and its index
    /// (1-based). A name may appear more than once (§22.2.1.1†: duplicates
    /// in different alternatives).
    pub group_names: Vec<(Vec<u32>, u32)>,
}

/// Disjunction :: Alternative | Alternative `|` Disjunction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Disjunction {
    /// The alternatives, at least one.
    pub alternatives: Vec<Alternative>,
}

/// Alternative :: [empty] | Alternative Term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Alternative {
    /// The terms, in order; none for the empty alternative.
    pub terms: Vec<Term>,
}

/// Term, with the quantifier after it if any.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Term {
    /// What is matched.
    pub kind: TermKind,
    /// The quantifier. Only an atom, or (Annex B, without `u` or `v`) a
    /// lookahead, has one.
    pub quantifier: Option<Quantifier>,
}

/// The alternatives of Term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermKind {
    /// `^`, `$`, `\b` or `\B`.
    Assertion(Assertion),
    /// `(?=..)`, `(?!..)`, `(?<=..)` or `(?<!..)`.
    Look(Look),
    /// An atom.
    Atom(Atom),
}

/// The assertions with no body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assertion {
    /// `^`.
    Start,
    /// `$`.
    End,
    /// `\b`.
    WordBoundary,
    /// `\B`.
    NotWordBoundary,
}

/// A lookaround.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Look {
    /// `(?<=` and `(?<!`.
    pub behind: bool,
    /// `(?!` and `(?<!`.
    pub negative: bool,
    /// The body.
    pub body: Disjunction,
}

/// QuantifierPrefix, and whether it is greedy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Quantifier {
    /// The least number of repetitions.
    pub min: u64,
    /// The most, or `None` for no limit. A written number above `u64::MAX` is
    /// stored as `u64::MAX`.
    pub max: Option<u64>,
    /// No `?` after the prefix.
    pub greedy: bool,
}

/// The modifier letters `i`, `m` and `s` (§22.2.1†, RegularExpressionModifier).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Modifiers {
    /// `i`.
    pub ignore_case: bool,
    /// `m`.
    pub multiline: bool,
    /// `s`.
    pub dot_all: bool,
}

/// Atom.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    /// A PatternCharacter or an escape that stands for one character.
    Char(u32),
    /// `.`.
    Dot,
    /// `\d`, `\D`, `\s`, `\S`, `\w`, `\W`, `\p{..}`, `\P{..}`.
    Escape(ClassEscape),
    /// `\1`: a backreference by number (1 or more).
    BackReference(u32),
    /// `\k<name>`: a backreference by name.
    NamedBackReference(Vec<u32>),
    /// `[..]`.
    Class(CharacterClass),
    /// `(..)`, `(?<name>..)` and `(?:..)`.
    Group(Group),
    /// `(?ims-ims:..)`.
    Modified(ModifiedGroup),
}

/// A group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Group {
    /// The group's number (1-based, in the order of the `(`), or `None` for
    /// `(?:`.
    pub index: Option<u32>,
    /// The name of `(?<name>`.
    pub name: Option<Vec<u32>>,
    /// The body.
    pub body: Disjunction,
}

/// `(?add-remove:body)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModifiedGroup {
    /// The flags turned on.
    pub add: Modifiers,
    /// The flags turned off.
    pub remove: Modifiers,
    /// The body.
    pub body: Disjunction,
}

/// CharacterClassEscape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassEscape {
    /// `\d`.
    Digit,
    /// `\D`.
    NotDigit,
    /// `\s`.
    Space,
    /// `\S`.
    NotSpace,
    /// `\w`.
    Word,
    /// `\W`.
    NotWord,
    /// `\p{..}` (`negated` false) or `\P{..}`.
    Property {
        /// `\P`.
        negated: bool,
        /// The property.
        property: Property,
    },
}

/// A Unicode property named by `\p{..}`, with the value as written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Property {
    /// `General_Category=Lu`, `gc=Lu`, or `Lu` alone.
    GeneralCategory(String),
    /// `Script=Latn` or `sc=Latn`.
    Script(String),
    /// `Script_Extensions=Latn` or `scx=Latn`.
    ScriptExtensions(String),
    /// A binary property such as `Alphabetic` (ECMA-262's table of binary
    /// Unicode property aliases and their canonical property names).
    Binary(String),
    /// A binary property of strings such as `RGI_Emoji`; only with `v`.
    Strings(String),
}

/// CharacterClass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharacterClass {
    /// `[^`.
    pub negated: bool,
    /// ClassContents.
    pub contents: ClassContents,
}

/// ClassContents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassContents {
    /// Without `v`: ClassRanges, as the items in order. Annex B's `[\d-x]` is
    /// three items.
    Ranges(Vec<ClassItem>),
    /// With `v`: ClassSetExpression.
    Set(ClassSetExpr),
}

/// An item of ClassRanges.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassItem {
    /// One character.
    Char(u32),
    /// `a-z`, with the first end at most the last.
    Range(u32, u32),
    /// `\d` and the like.
    Escape(ClassEscape),
}

/// ClassSetExpression (`v` mode).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassSetExpr {
    /// ClassUnion: the items (none for `[]`).
    Union(Vec<ClassSetItem>),
    /// ClassIntersection: `a&&b&&c`, at least two operands.
    Intersection(Vec<ClassSetOperand>),
    /// ClassSubtraction: `a--b--c`, at least two operands.
    Subtraction(Vec<ClassSetOperand>),
}

/// An element of a ClassUnion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassSetItem {
    /// ClassSetOperand.
    Operand(ClassSetOperand),
    /// ClassSetRange, with the first end at most the last.
    Range(u32, u32),
}

/// ClassSetOperand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassSetOperand {
    /// ClassSetCharacter.
    Char(u32),
    /// `\d`, `\p{..}` and the like.
    Escape(ClassEscape),
    /// NestedClass `[..]` or `[^..]`.
    Nested {
        /// `[^`.
        negated: bool,
        /// The contents.
        expr: Box<ClassSetExpr>,
    },
    /// `\q{a|bc|}`: ClassStringDisjunction, each string as its code points.
    Strings(Vec<Vec<u32>>),
}

impl ClassEscape {
    /// MayContainStrings (§22.2.1.1†): a `\p` of a property of strings.
    #[must_use]
    pub fn may_contain_strings(&self) -> bool {
        matches!(
            self,
            ClassEscape::Property {
                property: Property::Strings(_),
                ..
            }
        )
    }
}

impl ClassSetOperand {
    /// MayContainStrings (§22.2.1.1†, Static Semantics) of an operand: a
    /// negated class matches no strings; a `\q` may, unless each of its
    /// strings is one character.
    #[must_use]
    pub fn may_contain_strings(&self) -> bool {
        match self {
            ClassSetOperand::Char(_) => false,
            ClassSetOperand::Escape(e) => e.may_contain_strings(),
            ClassSetOperand::Nested { negated, expr } => !*negated && expr.may_contain_strings(),
            ClassSetOperand::Strings(list) => list.iter().any(|s| s.len() != 1),
        }
    }
}

impl ClassSetExpr {
    /// MayContainStrings (§22.2.1.1†, Static Semantics): a union, if any
    /// element may; an intersection, if all operands may; a subtraction, if
    /// its first operand may.
    #[must_use]
    pub fn may_contain_strings(&self) -> bool {
        match self {
            ClassSetExpr::Union(items) => items.iter().any(|i| match i {
                ClassSetItem::Operand(o) => o.may_contain_strings(),
                ClassSetItem::Range(..) => false,
            }),
            ClassSetExpr::Intersection(ops) => {
                !ops.is_empty() && ops.iter().all(ClassSetOperand::may_contain_strings)
            }
            ClassSetExpr::Subtraction(ops) => ops
                .first()
                .is_some_and(ClassSetOperand::may_contain_strings),
        }
    }
}
