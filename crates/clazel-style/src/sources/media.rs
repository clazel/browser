//! Media queries: Media Queries Level 4, W3C Candidate Recommendation Draft of 8 October
//! 2026, <https://www.w3.org/TR/2026/CRD-mediaqueries-4-20261008/> (the text
//! <https://drafts.csswg.org/mediaqueries-4/> served on 2026-11-11), for the subset item
//! 5.8 names: the media types `all`, `screen` and `print` (§2.3), `not` and `only` (§2.2),
//! `and`, `or` and `not` in conditions (§2.5), comma lists (§2.1), and the features `width`
//! and `height` (§4.1, §4.2, with their `min-` and `max-` forms, §2.4.4, and the range
//! context, §2.4.3) and `orientation` (§4.4), evaluated against the viewport. Every other
//! feature is an unknown `<mf-name>`, whose value is "unknown" (§3.2), so a query that needs
//! it is false (§3.1).
//!
//! Serialization is CSSOM §4.2 "serialize a media query list" (CSS Object Model, Editor's
//! Draft of 13 October 2026, <https://drafts.csswg.org/cssom/>), extended to Level 4's
//! conditions as engines extend it.
//!
//! # Modelling choices
//!
//! - **A condition is a postfix list of [`Op`]s**: features and `<general-enclosed>` push a
//!   value, `not` replaces the top one, `and` and `or` replace their operands with one.
//!   Evaluating it is one loop with a stack ([`evaluate_condition`]), so nesting never
//!   recurses there; the tree of §3 is the order of the list.
//! - **Strings live beside the queries** ([`MediaQueryList::strings`]): an unknown media
//!   type, feature name, unit or identifier is an index there, so every [`Op`] is a few
//!   words and the evaluator never reads text. Only the serializer does.
//! - **Nesting is bounded**: a `( … )` nested more than [`MAX_DEPTH`] deep is not read as a
//!   condition, so it is `<general-enclosed>` if it can be (it is "unknown") and the query
//!   fails to parse otherwise. This keeps the parser's recursion bounded on hostile input;
//!   no real query nests so deep.
//! - **Lengths** are compared in 1/64 px as [`crate::values::number::to_px64`] gives them,
//!   with `em` and `rem` against the initial `font-size`, `medium`, 16 px (§4.1: "The em
//!   value is relative to the initial value of font-size"), and `ex` half that, as in
//!   `values/`. A zero `<number>` is a `<length>` (CSS Values 4 §6†).
//! - **Unknown is kept, not replaced.** §3.2 says a `<media-query>` whose value is
//!   "unknown" "must be replaced with not all". Its value is unknown exactly when it would
//!   evaluate to false for that reason, so replacing changes no result; it would change
//!   the serialization, and WPT's `test_media_queries.html` expects such a query to stay
//!   parseable (`expression_should_be_parseable`), as engines keep it. So the query is
//!   kept and evaluates to false (`docs/ERRATA.md`).
//! - **The list is split at top-level commas** after trimming whitespace, not by CSS
//!   Syntax 3 §5.4.10 read literally (see [`parse_media_query_list`] and `docs/ERRATA.md`).
//! - **Serialization of `<general-enclosed>`** writes its tokens back with one space for
//!   each run of whitespace, and a `[ … ]` for any square or curly block; engines keep the
//!   original text. No test reads it.

use super::tokens::{Tok, Toks};
use crate::values::items::{Span, eq_ignore_case, lookup, lower};
use crate::values::number::{LENGTH_UNITS, Length, LengthUnit, MAX_PX64, Num, to_px64, write_num};

/// How deep `( <media-condition> )` may nest before a `( … )` is read only as a feature or
/// `<general-enclosed>`.
pub const MAX_DEPTH: usize = 32;

/// The initial value of `font-size`, `medium`, in 1/64 px: 16 px (CSS Fonts 4 §2.5†, the
/// value user agents use).
pub const INITIAL_FONT_SIZE_PX64: i32 = 16 * 64;

/// The medium a document is shown on: what `screen` and `print` match (§2.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Medium {
    /// A screen: matches `screen` and `all`.
    Screen,
    /// A printer or print preview: matches `print` and `all`.
    Print,
}

/// What media queries are evaluated against: the medium and the viewport (for continuous
/// media, "the width of the viewport ... including the size of a rendered scroll bar",
/// §4.1, and its height, §4.2), in 1/64 px.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Device {
    /// The medium.
    pub medium: Medium,
    /// The viewport's width.
    pub width_px64: i32,
    /// The viewport's height.
    pub height_px64: i32,
}

impl Device {
    /// A screen whose viewport is `width` by `height` CSS pixels, clamped to the largest
    /// length `values/` holds.
    pub fn screen(width: u32, height: u32) -> Device {
        let px64 = |v: u32| {
            i32::try_from(i64::from(v).saturating_mul(64).min(i64::from(MAX_PX64))).unwrap_or(0)
        };
        Device {
            medium: Medium::Screen,
            width_px64: px64(width),
            height_px64: px64(height),
        }
    }
}

/// Kleene's three-valued logic (§3.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Tri {
    /// True.
    True,
    /// False.
    False,
    /// Unknown.
    Unknown,
}

impl Tri {
    /// True or false.
    pub fn of(b: bool) -> Tri {
        if b { Tri::True } else { Tri::False }
    }

    /// `<media-not>`: "the negation of the `<media-in-parens>` term. The negation of
    /// unknown is unknown."
    pub fn negate(self) -> Tri {
        match self {
            Tri::True => Tri::False,
            Tri::False => Tri::True,
            Tri::Unknown => Tri::Unknown,
        }
    }

    /// `<media-and>`: "true if [all] are true, false if at least one ... [is] false, and
    /// unknown otherwise."
    pub fn and(self, other: Tri) -> Tri {
        match (self, other) {
            (Tri::False, _) | (_, Tri::False) => Tri::False,
            (Tri::True, Tri::True) => Tri::True,
            _ => Tri::Unknown,
        }
    }

    /// `<media-or>`: "false if [all] are false, true if at least one ... [is] true, and
    /// unknown otherwise."
    pub fn or(self, other: Tri) -> Tri {
        match (self, other) {
            (Tri::True, _) | (_, Tri::True) => Tri::True,
            (Tri::False, Tri::False) => Tri::False,
            _ => Tri::Unknown,
        }
    }

    /// "If the result ... is used in any context that expects a two-valued boolean,
    /// 'unknown' must be converted to 'false'" (§3.1).
    pub fn holds(self) -> bool {
        self == Tri::True
    }
}

/// A media query modifier (§2.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Modifier {
    /// `not` (§2.2.1).
    Not,
    /// `only` (§2.2.2): no effect on the result.
    Only,
}

/// A media type (§2.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum MediaType {
    /// `all`: "Matches all devices."
    All,
    /// `print`.
    Print,
    /// `screen`: "all devices that aren't matched by print".
    Screen,
    /// One of the deprecated types, which user agents "must recognize ... as valid, but
    /// must make them match nothing": its name's index in [`DEPRECATED_TYPES`].
    Deprecated(u8),
    /// "An unknown `<media-type>` must be treated as not matching" (§3.2): its name, as an
    /// index into the list's strings.
    Unknown(u32),
}

/// The deprecated media types (§2.3).
pub const DEPRECATED_TYPES: &[&str] = &[
    "tty",
    "tv",
    "projection",
    "handheld",
    "braille",
    "embossed",
    "aural",
    "speech",
];

/// "The `<media-type>` production does not include the keywords only, not, and, or, and
/// layer" (§3).
const NOT_MEDIA_TYPES: &[&str] = &["only", "not", "and", "or", "layer"];

/// A media feature's name, with its prefix resolved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Name {
    /// `width` (§4.1).
    Width,
    /// `height` (§4.2).
    Height,
    /// `orientation` (§4.4).
    Orientation,
    /// Any other name, an index into the list's strings: "an unknown `<mf-name>` ...
    /// results in the value 'unknown'" (§3.2). `orientation` is discrete, so a prefixed
    /// `min-orientation` is "simply ... an unknown feature name" (§2.4.4).
    Unknown(u32),
}

/// The `min-` or `max-` prefix of a range feature (§2.4.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Prefix {
    /// No prefix.
    None,
    /// `min-`: "equivalent to using the '>=' operator".
    Min,
    /// `max-`: "equivalent to using the '<=' operator".
    Max,
}

/// `<mf-comparison>` (§3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Cmp {
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `=`.
    Eq,
}

impl Cmp {
    /// `<mf-lt>`.
    fn is_lt(self) -> bool {
        matches!(self, Cmp::Lt | Cmp::Le)
    }

    /// `<mf-gt>`.
    fn is_gt(self) -> bool {
        matches!(self, Cmp::Gt | Cmp::Ge)
    }

    /// `a OP b`.
    fn holds(self, a: i64, b: i64) -> bool {
        match self {
            Cmp::Lt => a < b,
            Cmp::Le => a <= b,
            Cmp::Gt => a > b,
            Cmp::Ge => a >= b,
            Cmp::Eq => a == b,
        }
    }

    fn text(self) -> &'static str {
        match self {
            Cmp::Lt => "<",
            Cmp::Le => "<=",
            Cmp::Gt => ">",
            Cmp::Ge => ">=",
            Cmp::Eq => "=",
        }
    }
}

/// An identifier `<mf-value>`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Ident {
    /// `portrait` (§4.4).
    Portrait,
    /// `landscape` (§4.4).
    Landscape,
    /// Any other, an index into the list's strings.
    Other(u32),
}

/// A dimension's unit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Unit {
    /// A `<length>` unit of the subset.
    Length(LengthUnit),
    /// Any other, an index into the list's strings.
    Other(u32),
}

/// `<mf-value> = <number> | <dimension> | <ident> | <ratio>` (§3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Value {
    /// `<number>`.
    Number(Num),
    /// `<dimension>`.
    Dimension(Num, Unit),
    /// `<ident>`.
    Ident(Ident),
    /// `<ratio>` with both numbers (CSS Values 4 §5.6†), non-negative.
    Ratio(Num, Num),
}

impl Value {
    /// The value as a `<length>` in 1/64 px, if it is one.
    fn length_px64(self) -> Option<i64> {
        match self {
            Value::Dimension(value, Unit::Length(unit)) => Some(i64::from(to_px64(
                Length { value, unit },
                INITIAL_FONT_SIZE_PX64,
                INITIAL_FONT_SIZE_PX64,
            ))),
            Value::Number(n) if n.is_zero() => Some(0),
            _ => None,
        }
    }
}

/// How a feature is tested (§2.4, §3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Test {
    /// `<mf-boolean>`: the name alone (§2.4.2).
    Boolean,
    /// `<mf-plain>`: `name : value`.
    Plain(Value),
    /// `<mf-range>`: `value OP name`, `name OP value`, or both (§2.4.3).
    Range {
        /// The value and comparison before the name.
        left: Option<(Value, Cmp)>,
        /// The comparison and value after it.
        right: Option<(Cmp, Value)>,
    },
}

/// `<media-feature>` (§3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Feature {
    /// The name.
    pub name: Name,
    /// Its prefix (only ever on `width` and `height`).
    pub prefix: Prefix,
    /// How it is tested.
    pub test: Test,
}

/// One step of a condition in postfix order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum Op {
    /// `( <media-feature> )`: pushes its value.
    Feature(Feature),
    /// `<general-enclosed>`: pushes unknown. Its serialization, an index into the strings.
    General(u32),
    /// `<media-not>`: negates the top value.
    Not,
    /// `<media-in-parens> <media-and>*`: replaces the top `n` values with their conjunction.
    And(u32),
    /// `<media-in-parens> <media-or>*`: replaces the top `n` values with their disjunction.
    Or(u32),
    /// `( <media-condition> )`: the value is unchanged; kept for serialization.
    Parens,
}

/// `<media-query>` (§3). A query that "does not match the grammar ... must be replaced by
/// not all" (§3.2): [`MediaQuery::not_all`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MediaQuery {
    /// `not` or `only`.
    pub modifier: Option<Modifier>,
    /// The media type, if given.
    pub media_type: Option<MediaType>,
    /// The condition, in postfix order; empty if there is none.
    pub condition: Vec<Op>,
}

impl MediaQuery {
    /// `not all`.
    pub fn not_all() -> MediaQuery {
        MediaQuery {
            modifier: Some(Modifier::Not),
            media_type: Some(MediaType::All),
            condition: Vec::new(),
        }
    }
}

/// A `<media-query-list>`, and the strings its queries name.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MediaQueryList {
    /// The queries.
    pub queries: Vec<MediaQuery>,
    /// The unknown names, units, identifiers and general-enclosed serializations.
    pub strings: Vec<Vec<u32>>,
}

// -------------------------------------------------------------------------------------------
// Evaluation (§3.1)
// -------------------------------------------------------------------------------------------

/// The media type's match on `device` (§2.3; unknown types, §3.2).
pub fn type_matches(t: MediaType, medium: Medium) -> bool {
    match t {
        MediaType::All => true,
        MediaType::Print => medium == Medium::Print,
        MediaType::Screen => medium == Medium::Screen,
        MediaType::Deprecated(_) | MediaType::Unknown(_) => false,
    }
}

/// A `width` or `height` feature whose value on the device is `actual` (1/64 px): §2.4.2 in
/// a boolean context, §4.1 or §4.2 with a value, §2.4.4 with a prefix and §2.4.3 in a range
/// context. A value that is not a `<length>` "does not match the value syntax for that media
/// feature" and is unknown (§3.2). Both features are "false in the negative range" (§2.4.3):
/// the viewport is never negative, so equal-to, less-than and less-or-equal comparisons with
/// a negative value are false as the comparison gives them.
fn evaluate_length(actual: i64, prefix: Prefix, test: Test) -> Tri {
    match test {
        // "Attempting to evaluate a min/max prefixed media feature in a boolean context is
        // invalid and a syntax error" (§2.4.4): the parser never builds one; unknown here.
        Test::Boolean => match prefix {
            Prefix::None => Tri::of(actual != 0),
            Prefix::Min | Prefix::Max => Tri::Unknown,
        },
        Test::Plain(v) => match v.length_px64() {
            None => Tri::Unknown,
            Some(x) => Tri::of(match prefix {
                Prefix::None => actual == x,
                Prefix::Min => actual >= x,
                Prefix::Max => actual <= x,
            }),
        },
        // A prefixed name is not a range feature's name, so in a range context it is an
        // unknown name.
        Test::Range { left, right } => {
            if prefix != Prefix::None {
                return Tri::Unknown;
            }
            // "with the feature name nested between two value comparisons, returns true if
            // both comparisons are true."
            let mut out = Tri::True;
            if let Some((v, cmp)) = left {
                out = out.and(match v.length_px64() {
                    Some(x) => Tri::of(cmp.holds(x, actual)),
                    None => Tri::Unknown,
                });
            }
            if let Some((cmp, v)) = right {
                out = out.and(match v.length_px64() {
                    Some(x) => Tri::of(cmp.holds(actual, x)),
                    None => Tri::Unknown,
                });
            }
            out
        }
    }
}

/// `<media-feature>`: "the result of evaluating the specified media feature" (§3.1).
pub fn evaluate_feature(f: Feature, device: Device) -> Tri {
    match f.name {
        Name::Unknown(_) => Tri::Unknown,
        Name::Width => evaluate_length(i64::from(device.width_px64), f.prefix, f.test),
        Name::Height => evaluate_length(i64::from(device.height_px64), f.prefix, f.test),
        Name::Orientation => {
            // §4.4: "portrait when the value of the height media feature is greater than or
            // equal to the value of the width media feature. ... Otherwise orientation is
            // landscape."
            let portrait = device.height_px64 >= device.width_px64;
            match (f.prefix, f.test) {
                (Prefix::None, Test::Boolean) => {
                    // §2.4.2: true if the feature "would be true for any value other than
                    // the number 0, a <dimension> with the value 0, or the keyword none";
                    // it is always portrait or landscape.
                    Tri::True
                }
                (Prefix::None, Test::Plain(Value::Ident(Ident::Portrait))) => Tri::of(portrait),
                (Prefix::None, Test::Plain(Value::Ident(Ident::Landscape))) => Tri::of(!portrait),
                // Any other value, a prefix, or a range context (orientation is "discrete",
                // §2.4.1): unknown (§3.2).
                _ => Tri::Unknown,
            }
        }
    }
}

/// A condition in postfix order (§3.1). A list that is not well formed (an operator with
/// too few values below it, or several values left) gives the last value computed, or
/// unknown if there is none; the parser never builds one.
pub fn evaluate_condition(ops: &[Op], device: Device) -> Tri {
    let mut stack: Vec<Tri> = Vec::new();
    for op in ops {
        match *op {
            Op::Feature(f) => stack.push(evaluate_feature(f, device)),
            // "<general-enclosed>: The result is unknown."
            Op::General(_) => stack.push(Tri::Unknown),
            Op::Not => {
                let v = stack.pop().unwrap_or(Tri::Unknown);
                stack.push(v.negate());
            }
            Op::And(n) | Op::Or(n) => {
                let is_and = matches!(op, Op::And(_));
                let k = usize::try_from(n).unwrap_or(usize::MAX).min(stack.len());
                let mut acc = if is_and { Tri::True } else { Tri::False };
                let mut any = false;
                for _ in 0..k {
                    if let Some(v) = stack.pop() {
                        acc = if is_and { acc.and(v) } else { acc.or(v) };
                        any = true;
                    }
                }
                stack.push(if any { acc } else { Tri::Unknown });
            }
            Op::Parens => {}
        }
    }
    stack.pop().unwrap_or(Tri::Unknown)
}

/// A media query's value (§2): true "if the media type, if specified, matches the media
/// type of the device ... and the media condition is true", negated by `not` (§2.2.1, as
/// Kleene's negation, so an unknown query stays unknown) and unchanged by `only` (§2.2.2).
pub fn evaluate_query_tri(q: &MediaQuery, device: Device) -> Tri {
    let media_type = q
        .media_type
        .map_or(Tri::True, |t| Tri::of(type_matches(t, device.medium)));
    let condition = if q.condition.is_empty() {
        Tri::True
    } else {
        evaluate_condition(&q.condition, device)
    };
    let value = media_type.and(condition);
    match q.modifier {
        Some(Modifier::Not) => value.negate(),
        Some(Modifier::Only) | None => value,
    }
}

/// A media query as a two-valued boolean (§3.1).
pub fn evaluate_query(q: &MediaQuery, device: Device) -> bool {
    evaluate_query_tri(q, device).holds()
}

/// A media query list (§2.1): "true if any of its component media queries are true, and
/// false only if all of its component media queries are false. ... An empty media query
/// list evaluates to true."
pub fn evaluate(list: &MediaQueryList, device: Device) -> bool {
    list.queries.is_empty() || list.queries.iter().any(|q| evaluate_query(q, device))
}

// -------------------------------------------------------------------------------------------
// Parsing (§3)
// -------------------------------------------------------------------------------------------

/// A position in a list of tokens: `pos` up to `end`.
#[derive(Clone, Copy)]
struct Parser<'a> {
    toks: &'a [Tok],
    text: &'a [u32],
    pos: usize,
    end: usize,
}

impl<'a> Parser<'a> {
    fn budget(&self) -> usize {
        self.toks.len().saturating_add(1)
    }

    fn str(&self, s: Span) -> &'a [u32] {
        let start = s.start as usize;
        self.text
            .get(start..start.saturating_add(s.len as usize))
            .unwrap_or_default()
    }

    /// The token at `pos`, if inside the list.
    fn at(&self, pos: usize) -> Option<Tok> {
        if pos >= self.end {
            None
        } else {
            self.toks.get(pos).copied()
        }
    }

    /// Where the token at `pos` ends: past its contents, clamped to this list.
    fn item_end(&self, pos: usize) -> usize {
        let next = pos.saturating_add(1);
        match self.at(pos) {
            Some(Tok::Paren { end } | Tok::Function { end, .. } | Tok::Block { end }) => {
                (end as usize).clamp(next, self.end.max(next))
            }
            _ => next,
        }
    }

    fn skip_ws(&mut self) {
        for _ in 0..self.budget() {
            if self.at(self.pos) == Some(Tok::Ws) {
                self.pos = self.pos.saturating_add(1);
            } else {
                break;
            }
        }
    }

    /// The next token after any whitespace (which is consumed).
    fn peek(&mut self) -> Option<Tok> {
        self.skip_ws();
        self.at(self.pos)
    }

    fn at_end(&mut self) -> bool {
        self.peek().is_none()
    }

    /// The next token, if an identifier, consumed.
    fn ident(&mut self) -> Option<&'a [u32]> {
        if let Some(Tok::Ident(s)) = self.peek() {
            self.pos = self.pos.saturating_add(1);
            Some(self.str(s))
        } else {
            None
        }
    }

    /// The next token, if the identifier `k` (in lower case), consumed.
    fn eat_keyword(&mut self, k: &str) -> bool {
        let save = self.pos;
        if self.ident().is_some_and(|s| eq_ignore_case(s, k)) {
            true
        } else {
            self.pos = save;
            false
        }
    }

    fn delim(&mut self, c: char) -> bool {
        if self.peek() == Some(Tok::Delim(u32::from(c))) {
            self.pos = self.pos.saturating_add(1);
            true
        } else {
            false
        }
    }

    /// A parser over the contents of the block or function at `pos`.
    fn contents(&self, pos: usize) -> Parser<'a> {
        Parser {
            toks: self.toks,
            text: self.text,
            pos: pos.saturating_add(1),
            end: self.item_end(pos),
        }
    }
}

/// What parsing builds besides the ops: the strings.
struct Out {
    strings: Vec<Vec<u32>>,
}

impl Out {
    fn string(&mut self, s: &[u32]) -> u32 {
        let i = u32::try_from(self.strings.len()).unwrap_or(u32::MAX);
        self.strings.push(s.to_vec());
        i
    }
}

/// The ASCII lower case of a name.
fn lowered(s: &[u32]) -> Vec<u32> {
    s.iter().map(|&c| lower(c)).collect()
}

/// `<mf-name>`, with the `min-` and `max-` prefixes of §2.4.4 resolved. Names are ASCII
/// case-insensitive (§3: "tokens are ASCII case-insensitive").
fn feature_name(s: &[u32], out: &mut Out) -> (Name, Prefix) {
    let known = [
        ("width", Name::Width, Prefix::None),
        ("height", Name::Height, Prefix::None),
        ("orientation", Name::Orientation, Prefix::None),
        ("min-width", Name::Width, Prefix::Min),
        ("max-width", Name::Width, Prefix::Max),
        ("min-height", Name::Height, Prefix::Min),
        ("max-height", Name::Height, Prefix::Max),
    ];
    for (k, name, prefix) in known {
        if eq_ignore_case(s, k) {
            return (name, prefix);
        }
    }
    (Name::Unknown(out.string(&lowered(s))), Prefix::None)
}

/// `<mf-comparison>`: `<mf-lt> = '<' '='?`, `<mf-gt> = '>' '='?`, `<mf-eq> = '='`. "No
/// whitespace is allowed between the '<' or '>' <delim-token>s and the following '='
/// <delim-token>, if it's present" (§3), so the `=` must be the very next token.
fn comparison(p: &mut Parser<'_>) -> Option<Cmp> {
    let lt = u32::from('<');
    let gt = u32::from('>');
    let eq = u32::from('=');
    let first = match p.peek()? {
        Tok::Delim(c) if c == lt || c == gt || c == eq => c,
        _ => return None,
    };
    p.pos = p.pos.saturating_add(1);
    if first == eq {
        return Some(Cmp::Eq);
    }
    let or_equal = p.at(p.pos) == Some(Tok::Delim(eq));
    if or_equal {
        p.pos = p.pos.saturating_add(1);
    }
    Some(match (first == lt, or_equal) {
        (true, false) => Cmp::Lt,
        (true, true) => Cmp::Le,
        (false, false) => Cmp::Gt,
        (false, true) => Cmp::Ge,
    })
}

/// `<mf-value> = <number> | <dimension> | <ident> | <ratio>`, with `<ratio> = <number
/// [0,∞]> [ / <number [0,∞]> ]?` (CSS Values 4 §5.6†); a lone number is read as a
/// `<number>`.
fn mf_value(p: &mut Parser<'_>, out: &mut Out) -> Option<Value> {
    match p.peek()? {
        Tok::Number { value, .. } => {
            p.pos = p.pos.saturating_add(1);
            let save = p.pos;
            if !value.is_negative()
                && p.delim('/')
                && let Some(Tok::Number { value: d, .. }) = p.peek()
                && !d.is_negative()
            {
                p.pos = p.pos.saturating_add(1);
                return Some(Value::Ratio(value, d));
            }
            p.pos = save;
            Some(Value::Number(value))
        }
        Tok::Dimension { value, unit } => {
            p.pos = p.pos.saturating_add(1);
            let u = p.str(unit);
            let unit = match lookup(LENGTH_UNITS, u) {
                Some(l) => Unit::Length(l),
                None => Unit::Other(out.string(&lowered(u))),
            };
            Some(Value::Dimension(value, unit))
        }
        Tok::Ident(s) => {
            p.pos = p.pos.saturating_add(1);
            let s = p.str(s);
            Some(Value::Ident(if eq_ignore_case(s, "portrait") {
                Ident::Portrait
            } else if eq_ignore_case(s, "landscape") {
                Ident::Landscape
            } else {
                Ident::Other(out.string(s))
            }))
        }
        _ => None,
    }
}

/// `<media-feature> = [ <mf-plain> | <mf-boolean> | <mf-range> ]`, the whole of `p`.
fn media_feature(p: &Parser<'_>, out: &mut Out) -> Option<Feature> {
    // <mf-plain> = <mf-name> : <mf-value>
    let mut q = *p;
    if let Some(name) = q.ident()
        && q.peek() == Some(Tok::Colon)
    {
        q.pos = q.pos.saturating_add(1);
        if let Some(v) = mf_value(&mut q, out)
            && q.at_end()
        {
            let (name, prefix) = feature_name(name, out);
            return Some(Feature {
                name,
                prefix,
                test: Test::Plain(v),
            });
        }
    }
    // <mf-boolean> = <mf-name>
    let mut q = *p;
    if let Some(name) = q.ident()
        && q.at_end()
    {
        let (name, prefix) = feature_name(name, out);
        // "Attempting to evaluate a min/max prefixed media feature in a boolean context
        // is invalid and a syntax error" (§2.4.4).
        if prefix != Prefix::None {
            return None;
        }
        return Some(Feature {
            name,
            prefix,
            test: Test::Boolean,
        });
    }
    // <mf-range> = <mf-name> <mf-comparison> <mf-value>
    let mut q = *p;
    if let Some(name) = q.ident()
        && let Some(cmp) = comparison(&mut q)
        && let Some(v) = mf_value(&mut q, out)
        && q.at_end()
    {
        let (name, prefix) = feature_name(name, out);
        return Some(Feature {
            name,
            prefix,
            test: Test::Range {
                left: None,
                right: Some((cmp, v)),
            },
        });
    }
    //   | <mf-value> <mf-comparison> <mf-name>
    //   | <mf-value> <mf-lt> <mf-name> <mf-lt> <mf-value>
    //   | <mf-value> <mf-gt> <mf-name> <mf-gt> <mf-value>
    let mut q = *p;
    let v1 = mf_value(&mut q, out)?;
    let c1 = comparison(&mut q)?;
    let name = q.ident()?;
    if q.at_end() {
        let (name, prefix) = feature_name(name, out);
        return Some(Feature {
            name,
            prefix,
            test: Test::Range {
                left: Some((v1, c1)),
                right: None,
            },
        });
    }
    let c2 = comparison(&mut q)?;
    let v2 = mf_value(&mut q, out)?;
    if !q.at_end() || !((c1.is_lt() && c2.is_lt()) || (c1.is_gt() && c2.is_gt())) {
        return None;
    }
    let (name, prefix) = feature_name(name, out);
    Some(Feature {
        name,
        prefix,
        test: Test::Range {
            left: Some((v1, c1)),
            right: Some((c2, v2)),
        },
    })
}

/// True if the tokens of `p` hold none that `<any-value>` excludes.
fn any_value(p: &Parser<'_>) -> bool {
    let lo = p.pos.min(p.end);
    p.toks
        .get(lo..p.end.min(p.toks.len()))
        .unwrap_or_default()
        .iter()
        .all(|t| *t != Tok::Bad)
}

/// The tokens `lo .. hi` written back as text, for a `<general-enclosed>`.
fn write_tokens(p: &Parser<'_>, lo: usize, hi: usize, s: &mut Vec<u32>) {
    // Closing brackets still owed, as (the index where the block ends, its closer).
    let mut closers: Vec<(usize, char)> = Vec::new();
    let push = |s: &mut Vec<u32>, t: &str| s.extend(t.chars().map(u32::from));
    let mut i = lo;
    for _ in 0..p.budget().saturating_mul(2) {
        while let Some(&(e, c)) = closers.last() {
            if e <= i {
                push(s, &c.to_string());
                closers.pop();
            } else {
                break;
            }
        }
        if i >= hi {
            break;
        }
        let Some(t) = p.toks.get(i) else { break };
        let end = p.item_end(i).min(hi);
        match *t {
            Tok::Ws => {
                if s.last() != Some(&0x20) {
                    s.push(0x20);
                }
            }
            Tok::Ident(n) => s.extend_from_slice(p.str(n)),
            Tok::Number { value, .. } => {
                let mut t = String::new();
                write_num(&mut t, value);
                push(s, &t);
            }
            Tok::Dimension { value, unit } => {
                let mut t = String::new();
                write_num(&mut t, value);
                push(s, &t);
                s.extend_from_slice(p.str(unit));
            }
            Tok::Delim(c) => s.push(c),
            Tok::Colon => s.push(0x3A),
            Tok::Comma => s.push(0x2C),
            Tok::Paren { .. } => {
                s.push(0x28);
                closers.push((end, ')'));
            }
            Tok::Function { name, .. } => {
                s.extend_from_slice(p.str(name));
                s.push(0x28);
                closers.push((end, ')'));
            }
            Tok::Block { .. } => {
                s.push(0x5B);
                closers.push((end, ']'));
            }
            Tok::Bad | Tok::Other => {}
        }
        i = i.saturating_add(1);
    }
    while let Some((_, c)) = closers.pop() {
        push(s, &c.to_string());
    }
}

/// `<media-in-parens> = ( <media-condition> ) | ( <media-feature> ) | <general-enclosed>`,
/// "the `<general-enclosed>` branch [chosen] only ... if the input does not match either of
/// the preceding branches" (§3). Appends its ops.
fn media_in_parens(p: &mut Parser<'_>, depth: usize, ops: &mut Vec<Op>, out: &mut Out) -> bool {
    let Some(t) = p.peek() else { return false };
    let at = p.pos;
    let after = p.item_end(at);
    match t {
        Tok::Paren { .. } => {
            let inner = p.contents(at);
            p.pos = after;
            // ( <media-condition> )
            if depth < MAX_DEPTH {
                let mark = ops.len();
                let strings = out.strings.len();
                let mut q = inner;
                if media_condition(&mut q, true, depth.saturating_add(1), ops, out) && q.at_end() {
                    ops.push(Op::Parens);
                    return true;
                }
                ops.truncate(mark);
                out.strings.truncate(strings);
            }
            // ( <media-feature> )
            let strings = out.strings.len();
            let mut q = inner;
            q.skip_ws();
            if let Some(f) = media_feature(&q, out) {
                ops.push(Op::Feature(f));
                return true;
            }
            out.strings.truncate(strings);
            // <general-enclosed> = ( <any-value>? )
            general_enclosed(p, at, after, &inner, ops, out)
        }
        // <general-enclosed> = <function-token> <any-value>? )
        Tok::Function { .. } => {
            let inner = p.contents(at);
            p.pos = after;
            general_enclosed(p, at, after, &inner, ops, out)
        }
        _ => false,
    }
}

fn general_enclosed(
    p: &Parser<'_>,
    at: usize,
    after: usize,
    inner: &Parser<'_>,
    ops: &mut Vec<Op>,
    out: &mut Out,
) -> bool {
    if !any_value(inner) {
        return false;
    }
    let mut s = Vec::new();
    write_tokens(p, at, after, &mut s);
    let i = out.string(&s);
    ops.push(Op::General(i));
    true
}

/// `<media-condition> = <media-not> | <media-in-parens> [ <media-and>* | <media-or>* ]`, or
/// with `allow_or` false `<media-condition-without-or> = <media-not> | <media-in-parens>
/// <media-and>*`. Appends its ops; false if the input does not start with one.
fn media_condition(
    p: &mut Parser<'_>,
    allow_or: bool,
    depth: usize,
    ops: &mut Vec<Op>,
    out: &mut Out,
) -> bool {
    // <media-not> = not <media-in-parens>
    if p.eat_keyword("not") {
        if !media_in_parens(p, depth, ops, out) {
            return false;
        }
        ops.push(Op::Not);
        return true;
    }
    if !media_in_parens(p, depth, ops, out) {
        return false;
    }
    // <media-and> = and <media-in-parens>; <media-or> = or <media-in-parens>. "It is invalid
    // to mix and and or and not at the same 'level'" (§2.5): the first keyword fixes which.
    let mut joiner: Option<bool> = None;
    let mut n: u32 = 1;
    for _ in 0..p.budget() {
        let save = p.pos;
        let is_and = if p.eat_keyword("and") {
            true
        } else if allow_or && p.eat_keyword("or") {
            false
        } else {
            break;
        };
        if joiner.is_some_and(|j| j != is_and) {
            // The rest does not continue this condition; the caller finds it unread.
            p.pos = save;
            break;
        }
        joiner = Some(is_and);
        if !media_in_parens(p, depth, ops, out) {
            return false;
        }
        n = n.saturating_add(1);
    }
    match joiner {
        Some(true) => ops.push(Op::And(n)),
        Some(false) => ops.push(Op::Or(n)),
        None => {}
    }
    true
}

/// `<media-query> = <media-condition> | [ not | only ]? <media-type> [ and
/// <media-condition-without-or> ]?`, the whole of `p`; `None` if it does not match.
fn media_query(p: &Parser<'_>, out: &mut Out) -> Option<MediaQuery> {
    // <media-condition>
    let strings = out.strings.len();
    let mut q = *p;
    let mut ops = Vec::new();
    if media_condition(&mut q, true, 0, &mut ops, out) && q.at_end() {
        return Some(MediaQuery {
            modifier: None,
            media_type: None,
            condition: ops,
        });
    }
    out.strings.truncate(strings);
    // [ not | only ]? <media-type> [ and <media-condition-without-or> ]?
    let mut q = *p;
    let modifier = if q.eat_keyword("not") {
        Some(Modifier::Not)
    } else if q.eat_keyword("only") {
        Some(Modifier::Only)
    } else {
        None
    };
    let name = q.ident()?;
    if NOT_MEDIA_TYPES.iter().any(|k| eq_ignore_case(name, k)) {
        return None;
    }
    let media_type = if eq_ignore_case(name, "all") {
        MediaType::All
    } else if eq_ignore_case(name, "print") {
        MediaType::Print
    } else if eq_ignore_case(name, "screen") {
        MediaType::Screen
    } else if let Some(i) = DEPRECATED_TYPES
        .iter()
        .position(|k| eq_ignore_case(name, k))
    {
        MediaType::Deprecated(u8::try_from(i).unwrap_or(0))
    } else {
        MediaType::Unknown(out.string(&lowered(name)))
    };
    let mut ops = Vec::new();
    if !q.at_end() {
        if !q.eat_keyword("and") || !media_condition(&mut q, false, 0, &mut ops, out) {
            return None;
        }
        if !q.at_end() {
            return None;
        }
    }
    Some(MediaQuery {
        modifier,
        media_type: Some(media_type),
        condition: ops,
    })
}

/// "To parse a `<media-query-list>` production, parse a comma-separated list of component
/// values, then parse each entry in the returned list as a `<media-query>`" (§3), each that
/// does not match becoming `not all` (§3.2).
///
/// The list is split as engines and WPT's `match-media-parsing.html` split it, not as CSS
/// Syntax 3 §5.4.10 reads literally (`docs/ERRATA.md`): input of only whitespace is the
/// empty list, and otherwise every top-level comma ends a query, so `foo,` is `foo, not all`
/// and `,` is `not all, not all`. §5.4.10 gives one group for `foo,` and for `,`, and one
/// group of whitespace for ` `.
pub fn parse_media_query_list(toks: &Toks) -> MediaQueryList {
    let mut out = Out {
        strings: Vec::new(),
    };
    let all = Parser {
        toks: &toks.toks,
        text: &toks.text,
        pos: 0,
        end: toks.toks.len(),
    };
    let mut queries = Vec::new();
    let mut p = all;
    if p.at_end() {
        return MediaQueryList {
            queries,
            strings: out.strings,
        };
    }
    let mut start = 0usize;
    let mut pos = 0usize;
    for _ in 0..all.budget() {
        let t = all.at(pos);
        if t.is_none() || t == Some(Tok::Comma) {
            let group = Parser {
                pos: start,
                end: pos.min(all.end),
                ..all
            };
            let strings = out.strings.len();
            queries.push(media_query(&group, &mut out).unwrap_or_else(|| {
                out.strings.truncate(strings);
                MediaQuery::not_all()
            }));
            if t.is_none() {
                break;
            }
            start = pos.saturating_add(1);
        }
        pos = all.item_end(pos);
    }
    MediaQueryList {
        queries,
        strings: out.strings,
    }
}

/// Parse `input` (a `media` attribute's value, or any string) as a media query list.
pub fn parse(input: &[u32]) -> MediaQueryList {
    parse_media_query_list(&Toks::parse(input))
}

/// HTML §2.3.10: "A string matches the environment of the user if it is the empty string,
/// a string consisting of only ASCII whitespace, or is a media query list that matches the
/// user's environment according to the definitions given in Media Queries." The empty and
/// all-whitespace strings parse to the empty list, which is true (§2.1).
pub fn matches_environment(input: &[u32], device: Device) -> bool {
    evaluate(&parse(input), device)
}

// -------------------------------------------------------------------------------------------
// Serialization (CSSOM §4.2)
// -------------------------------------------------------------------------------------------

fn string_of(list: &MediaQueryList, i: u32) -> String {
    list.strings
        .get(i as usize)
        .map(|s| s.iter().filter_map(|&c| char::from_u32(c)).collect())
        .unwrap_or_default()
}

fn write_value(list: &MediaQueryList, v: Value, s: &mut String) {
    match v {
        Value::Number(n) => write_num(s, n),
        Value::Dimension(n, u) => {
            write_num(s, n);
            match u {
                Unit::Length(l) => s.push_str(l.name()),
                Unit::Other(i) => s.push_str(&string_of(list, i)),
            }
        }
        Value::Ident(Ident::Portrait) => s.push_str("portrait"),
        Value::Ident(Ident::Landscape) => s.push_str("landscape"),
        Value::Ident(Ident::Other(i)) => s.push_str(&string_of(list, i)),
        Value::Ratio(a, b) => {
            write_num(s, a);
            s.push_str(" / ");
            write_num(s, b);
        }
    }
}

fn write_feature(list: &MediaQueryList, f: Feature, s: &mut String) {
    let name = match (f.name, f.prefix) {
        (Name::Width, Prefix::None) => "width".to_owned(),
        (Name::Width, Prefix::Min) => "min-width".to_owned(),
        (Name::Width, Prefix::Max) => "max-width".to_owned(),
        (Name::Height, Prefix::None) => "height".to_owned(),
        (Name::Height, Prefix::Min) => "min-height".to_owned(),
        (Name::Height, Prefix::Max) => "max-height".to_owned(),
        (Name::Orientation, _) => "orientation".to_owned(),
        (Name::Unknown(i), _) => string_of(list, i),
    };
    // "Append a '(' (U+0028), followed by the media feature name, converted to ASCII
    // lowercase ... If a value is given append a ':' (U+003A), followed by a single SPACE
    // (U+0020), followed by the serialized media feature value ... Append a ')'."
    s.push('(');
    match f.test {
        Test::Boolean => s.push_str(&name),
        Test::Plain(v) => {
            s.push_str(&name);
            s.push_str(": ");
            write_value(list, v, s);
        }
        Test::Range { left, right } => {
            if let Some((v, c)) = left {
                write_value(list, v, s);
                s.push(' ');
                s.push_str(c.text());
                s.push(' ');
            }
            s.push_str(&name);
            if let Some((c, v)) = right {
                s.push(' ');
                s.push_str(c.text());
                s.push(' ');
                write_value(list, v, s);
            }
        }
    }
    s.push(')');
}

/// A condition written back: `not X`, `X and Y`, `X or Y`, `(X)`.
fn write_condition(list: &MediaQueryList, ops: &[Op]) -> String {
    let mut stack: Vec<String> = Vec::new();
    for op in ops {
        match *op {
            Op::Feature(f) => {
                let mut s = String::new();
                write_feature(list, f, &mut s);
                stack.push(s);
            }
            Op::General(i) => stack.push(string_of(list, i)),
            Op::Not => {
                let v = stack.pop().unwrap_or_default();
                stack.push(format!("not {v}"));
            }
            Op::And(n) | Op::Or(n) => {
                let word = if matches!(op, Op::And(_)) {
                    " and "
                } else {
                    " or "
                };
                let k = usize::try_from(n).unwrap_or(usize::MAX).min(stack.len());
                let parts = stack.split_off(stack.len().saturating_sub(k));
                stack.push(parts.join(word));
            }
            Op::Parens => {
                let v = stack.pop().unwrap_or_default();
                stack.push(format!("({v})"));
            }
        }
    }
    stack.join(" ")
}

/// CSSOM §4.2 "serialize a media query".
pub fn serialize_query(list: &MediaQueryList, q: &MediaQuery) -> String {
    let mut s = String::new();
    // 1. "If the media query is negated append 'not', followed by a single SPACE (U+0020),
    // to s." (`only` is kept likewise, as engines keep it.)
    match q.modifier {
        Some(Modifier::Not) => s.push_str("not "),
        Some(Modifier::Only) => s.push_str("only "),
        None => {}
    }
    // 2. "Let type be the serialization as an identifier of the media type of the media
    // query, converted to ASCII lowercase."
    let media_type = q.media_type.map(|t| match t {
        MediaType::All => "all".to_owned(),
        MediaType::Print => "print".to_owned(),
        MediaType::Screen => "screen".to_owned(),
        MediaType::Deprecated(i) => DEPRECATED_TYPES
            .get(usize::from(i))
            .copied()
            .unwrap_or("")
            .to_owned(),
        MediaType::Unknown(i) => string_of(list, i),
    });
    // 3. "If the media query does not contain media features append type, to s, then
    // return s."
    if q.condition.is_empty() {
        s.push_str(media_type.as_deref().unwrap_or("all"));
        return s;
    }
    // 4. "If type is not 'all' or if the media query is negated append type, followed by a
    // single SPACE (U+0020), followed by 'and', followed by a single SPACE (U+0020), to s."
    if let Some(t) = media_type
        && (t != "all" || q.modifier.is_some())
    {
        s.push_str(&t);
        s.push_str(" and ");
    }
    // 5. "Then, for each media feature: ..." (Level 4's conditions, written back.)
    s.push_str(&write_condition(list, &q.condition));
    s
}

/// CSSOM §4.2 "serialize a media query list": "If the media query list is empty, then
/// return the empty string. Serialize each media query in the list of media queries, in the
/// same order as they appear in the media query list, and then serialize the list" (with ",
/// " between, CSSOM §2.1† "serialize a comma-separated list").
pub fn serialize(list: &MediaQueryList) -> String {
    list.queries
        .iter()
        .map(|q| serialize_query(list, q))
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn ser(s: &str) -> String {
        serialize(&parse(&u(s)))
    }

    fn applies(s: &str, w: u32, h: u32) -> bool {
        matches_environment(&u(s), Device::screen(w, h))
    }

    #[test]
    fn serializes_like_match_media() {
        let cases = [
            ("", ""),
            (" ", ""),
            ("all", "all"),
            ("   all   ", "all"),
            (" all , all ", "all, all"),
            ("(color", "(color)"),
            (" ( color   ", "(color)"),
            ("color)", "not all"),
            ("  color ), ( color", "not all, (color)"),
            (" foo ", "foo"),
            (",", "not all, not all"),
            (",,", "not all, not all, not all"),
            (" foo,", "foo, not all"),
            (
                "not screen and (min-WIDTH:5px) AND (max-width:40px)",
                "not screen and (min-width: 5px) and (max-width: 40px)",
            ),
            ("all and (color) and (color)", "(color) and (color)"),
            ("(0px < WIDTH <= 10em)", "(0px < width <= 10em)"),
            ("not ((a) or (b))", "not ((a) or (b))"),
            (
                "only screen and (orientation:portrait)",
                "only screen and (orientation: portrait)",
            ),
            ("(aspect-ratio: 16/9)", "(aspect-ratio: 16 / 9)"),
            (
                "(width 500px) or (min-width: 0)",
                "(width 500px) or (min-width: 0)",
            ),
        ];
        for (input, want) in cases {
            assert_eq!(ser(input), want, "{input:?}");
        }
    }

    #[test]
    fn grammar_mismatches_are_not_all() {
        for q in [
            "only (orientation)",
            "not not (orientation)",
            "all and (orientation) or (orientation)",
            "(orientation) and (orientation) or (orientation)",
            "(orientation) and not (orientation)",
            "not and",
            "and",
            "or",
            "not",
            "only",
            "layer",
            "not layer",
            "screen and (min-width: 480px) screen",
            "screen and",
            "screen (color)",
            "\"x\" (",
        ] {
            assert_eq!(ser(q), "not all", "{q}");
        }
        for q in [
            "(orientation)",
            "not (orientation)",
            "all and (orientation)",
            "not all and (orientation)",
            "only all and (orientation)",
            "(orientation) or ((orientation) and ((orientation) or (orientation) or (not (orientation))))",
            "(min-width)",
            "(width > = 0px)",
            "(0px = width = 100px)",
            "(min-width > 0)",
            "(unknown(1, [2]))",
            "f(x)",
        ] {
            assert_ne!(ser(q), "not all", "{q}");
        }
    }

    #[test]
    fn width_height_orientation() {
        assert!(applies("all and (width: 117px)", 117, 76));
        assert!(!applies("all and (width: 118px)", 117, 76));
        assert!(applies(
            "(min-width: 117px) and (max-height: 76px)",
            117,
            76
        ));
        assert!(!applies("(min-width: 118px)", 117, 76));
        assert!(applies("(0px < width <= 117px)", 117, 76));
        assert!(!applies("(0px < width < 117px)", 117, 76));
        assert!(applies("(117px >= width > 0px)", 117, 76));
        assert!(applies("(116px < width)", 117, 76));
        assert!(applies("not all and (width)", 0, 76));
        assert!(applies("(height)", 0, 76));
        assert!(applies("(orientation: landscape)", 236, 160));
        assert!(applies("(orientation: portrait)", 236, 320));
        assert!(applies("(orientation)", 1, 1));
        assert!(applies("(min-width: 1em)", 16, 1));
        assert!(!applies("(min-width: 1em)", 15, 1));
        assert!(!applies("(min-width: 9999999999px)", 800, 600));
        assert!(applies("(min-width: -100px)", 800, 600));
        assert!(applies("not (width <= -100px)", 800, 600));
        assert!(applies("(width: 0)", 0, 600));
        assert!(applies("(width: -0)", 0, 600));
    }

    #[test]
    fn media_types_and_modifiers() {
        assert!(applies("screen", 1, 1));
        assert!(!applies("print", 1, 1));
        assert!(applies("not print", 1, 1));
        assert!(applies("only screen", 1, 1));
        assert!(!applies("not only screen", 1, 1));
        assert!(!applies("tv", 1, 1));
        assert!(applies("not tv", 1, 1));
        assert!(!applies("foo", 1, 1));
        assert!(applies("not foo", 1, 1));
        assert!(applies("aLL and (Height)", 1, 1));
        assert!(applies("", 1, 1));
        assert!(applies("print, screen", 1, 1));
        let print = Device {
            medium: Medium::Print,
            ..Device::screen(1, 1)
        };
        assert!(evaluate(&parse(&u("print")), print));
        assert!(!evaluate(&parse(&u("screen")), print));
    }

    #[test]
    fn unknown_is_false_both_ways() {
        // An unknown feature is false, and so is its negation (Kleene, §3.1).
        for q in [
            "(-webkit-min-device-pixel-ratio: 2)",
            "(min-device-pixel-ratio: 2)",
            "not all and (-webkit-min-device-pixel-ratio: 2)",
            "not (color)",
            "(color) and (width)",
            "(min-orientation: portrait)",
            "(orientation: sideways)",
            "(width: 1)",
            "(width: red)",
            "(heİght)",
            "(orientation > 0)",
        ] {
            assert!(!applies(q, 800, 600), "{q}");
        }
        // ... unless the other side settles it.
        assert!(applies("(unknown) or (min-width: 0)", 800, 600));
        assert!(!applies("not ((unknown) or (min-width: 0))", 800, 600));
        assert!(!applies("(width 500px) and (min-width: 0)", 800, 600));
        assert!(applies("(width 500px) or (min-width: 0)", 800, 600));
    }

    #[test]
    fn deep_nesting_is_bounded() {
        let deep = |n: usize| format!("{}(width){}", "(".repeat(n), ")".repeat(n));
        assert!(applies(&deep(MAX_DEPTH), 1, 1));
        // Deeper than the bound: general-enclosed, so unknown.
        assert!(!applies(&deep(MAX_DEPTH.saturating_add(5)), 1, 1));
        assert!(!applies(&deep(100_000), 1, 1));
    }
}
