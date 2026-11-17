//! Specification of what a correct parse of an ECMAScript `Script` or `Module`
//! is, transcribed from ECMA-262, 2026 edition (`es2026`), §12.10 "Automatic
//! Semicolon Insertion", §13 to §16 (the syntactic grammar and its static
//! semantics: early errors, BoundNames, LexicallyDeclaredNames, ...), and Annex B.3
//! (the syntax that web browsers add), at commit
//! `0248456c758431e4bb8e5d26333ff1865123c9cd` of
//! <https://github.com/tc39/ecma262> (31 March 2026; `SPEC-PIN.md` of
//! `clazel-js-lexer`). Section numbers are those `spec.html` numbers at that
//! commit, and every rule quoted is checked against that text. Nothing here
//! runs; it defines what "correct" means. Every definition cites the standard.
//!
//! # What this file covers
//!
//! - **The syntactic grammar** (§13.1 to §16.2), for both goal symbols, as a
//!   relation `d` between nodes of an arena AST ([`crate::ast`]) and the token
//!   stream they derive: identifiers, literals (templates included), array and
//!   object literals, function, generator, async and async generator expressions
//!   and declarations, arrow and async arrow functions, methods, classes (fields,
//!   private names, static blocks), every operator with its precedence (the
//!   exponent, `??` and optional chaining rules included), assignment and its
//!   patterns, binding patterns, `yield`, `await`, every statement of §14,
//!   parameter lists and bodies, and the module items: `import` and `export` in
//!   all their forms, with import attributes. The grammar parameters `[Yield]`,
//!   `[Await]`, `[In]`, `[Return]` and `[Default]` are `Ctx`; `[Tagged]` is
//!   `EarlyEnv::tagged` (it affects only early errors); the lookaheads and the
//!   `[no LineTerminator here]` restrictions are written where the standard has
//!   them. Annex B.3.1 (labelled functions), B.3.3 (functions as `if` clauses) and
//!   B.3.5 (`for (var a = 1 in x)`) are in the grammar; Annex B's HTML-like
//!   comments and legacy octal syntax are in the lexer.
//! - **Automatic semicolon insertion** (§12.10.1): rules 1 to 4 (`gap_justified`).
//! - **Early errors** (`early`, `early_local`): the rules of §12.9.3.1, §12.9.4.1,
//!   §13.1.1, §13.2.5.1, §13.2.7.1, §13.2.8.1, §13.3.1.1, §13.4.1, §13.5.1.1, §13.15.1,
//!   §13.15.5.1, §14.2.1, §14.3.1.1, §14.6.1, §14.7.2.1 to §14.7.5.1, §14.8.1,
//!   §14.9.1, §14.11.1, §14.12.1, §14.13.1, §14.15.1, §15.1.1 to §15.9.1, §15.7.1,
//!   §16.1.1, §16.2.1.1 and §16.2.2.1 (names declared twice, names that are both
//!   lexical and var, labels and the targets of `break` and `continue`, strict
//!   mode, the targets of assignments, `super`, `new.target`, `import.meta`,
//!   `yield` and `await` in parameters, private names and the constructors of
//!   classes, directive prologues, duplicate `__proto__`, `arguments` in field
//!   initializers), and §16.2.3.1's rule on the local names of `export {..};`,
//!   with Annex B.3.2 (duplicate sloppy function declarations in a block), B.3.3,
//!   B.3.4 (`var` of a `catch` parameter's name), B.3.5 and B.3.9 (calls as
//!   assignment targets: `~web-compat~`).
//! - **The recursion limit** ([`MAX_DEPTH`]), as the listed deviation of item 7.3.
//!
//! # What it leaves out
//!
//! - **Early errors not yet specified.** §13.2.8.1's limit of 2^32 template strings;
//!   §16.2.1.1's rules on ExportedNames (no duplicate), ExportedBindings (each is
//!   declared) and `IsStringWellFormedUnicode` of module export names; the
//!   exception of Annex B.3.4 for a `for (var e of ...)` inside a `catch (e)`;
//!   the rules about the *contents* of a regular expression (§22.2.1.1, Annex
//!   B.1.2), which are `regexp_valid` of its token, supplied by `clazel-js-regexp`;
//!   the additional rules of §16.1.1 for code that a direct `eval` processes (the
//!   embedder's, item 7.19); and `for await` outside an `async`
//!   function, which the grammar parameter `[+Await]` already excludes.
//! - **Everything about values**: the numeric value of a literal, the SV of a
//!   string other than for `__proto__` and a directive (`Tok::name` for a
//!   `StringLiteral`), and TV and TRV, which the lexer item has, and run-time
//!   semantics. The parser does not compute them.
//! - **Cover grammars as a technique.** See the modelling choices.
//! - **The lexer.** Tokens come from the lexer's specification through the
//!   [`LexerSpec`] trait, and `lexes_as` states only how a parser drives it.
//!
//! # Modelling choices
//!
//! Each one is a deliberate difference in form, never in meaning, except where
//! it is listed under *Deviations*.
//!
//! - **An AST is a derivation.** The standard has a grammar; a parser's output
//!   is a derivation, here an arena of nodes whose kinds name the productions
//!   (`NodeKind`), whose children are in the productions' order, and whose spans
//!   are in the source text. `d(a, ts, n, cx, i, j)` says node `n` derives exactly the
//!   tokens `ts[i..j)` in context `cx`: each `NodeKind` has one arm, written from the
//!   production(s) it is named after, in the standard's order and with its
//!   alternatives' numbers where there are several. The relation is checked from
//!   the root, which derives the whole stream. Since a node's span says where it
//!   ends, no arm guesses where a child ends: `ed` reads it off the span, and
//!   `span_ok` checks that the span is the range of tokens derived.
//! - **Optional symbols are `Absent` nodes**, with an empty span where they
//!   would be, so a kind's children are at fixed positions, as the production's symbols
//!   are. A list is one child per item. A comma-separated list with an optional
//!   trailing `,` is `dsep`, and an `ElementList` with `Elision`s is `darray`.
//! - **Precedence is `lvl`.** The chain of productions from `Expression` down to
//!   `PrimaryExpression` (`X : Y | X op Z`) is one number per node kind; a binary
//!   node says which operands it takes by comparing them (`binary_operands_ok`),
//!   which is the same as writing each level's production, in a few lines instead of
//!   one production per level. `ExponentiationExpression`, `RelationalExpression`'s `#x in y`
//!   and `CoalesceExpression` are written out as the standard has them.
//! - **Cover grammars** (§13.2.9, §13.3.6 and §15.9 CoverCallExpressionAndAsyncArrowHead,
//!   §13.2.5.1's `CoverInitializedName`, §13.15.5's `AssignmentPattern`) are
//!   specified by the refined production that the text is read as, not by the
//!   cover: the standard says "the interpretation of [the cover] is refined using
//!   the following grammar", and a derivation by the refined grammar is such a
//!   refinement. A `ParenthesizedExpression` and an `ArrowFunction`'s parameters
//!   are different nodes, an `AssignmentPattern` is its own kind of node (so
//!   "`LeftHandSideExpression` must cover an `AssignmentPattern`" is that the
//!   target of `=`, of a `for` head, or of a pattern element is one, and an
//!   `ObjectLiteral` or `ArrayLiteral` is not), and a `CoverInitializedName` is
//!   an `ObjectLiteral`'s child that is always an early error. Two nodes can derive
//!   the same text (`({a = 1} = x)` and `({a = 1})`), as two productions can.
//! - **Tokens are chosen with the grammar.** The lexer's goal symbol is the
//!   syntactic grammar's choice (§12, "the syntactic grammar chooses the goal
//!   symbol"): `lexes_as` lets each token be a step of the lexer with *some* goal.
//!   Every position of the grammar accepts only the token kinds of one goal (a
//!   `/` is `DivPunctuator` after an operand, the start of a
//!   `RegularExpressionLiteral` before one), so the existential does not admit a
//!   second parse. Trivia are the lexer's: `Tok::nl_before` is the one fact of
//!   them the parser reads.
//! - **Automatic semicolon insertion is the one rule that looks at what could
//!   come next.** The standard says a `;` is inserted before a token that is "not
//!   allowed by any production of the grammar" (rule 1), or at the end if the
//!   tokens do not make a `Script` (rule 2), left to right. The `;` is in the
//!   stream, in the gap where it goes (`Stream::gaps`), and in no token's range,
//!   so spans never include text that is not in the source; the production that
//!   ends with `;` ends at the gap (`semi`). It is justified (`gap_justified`) if no
//!   sentence of the grammar *without* semicolon insertion begins with the tokens
//!   before it (inserted `;`s included) and the offending token, under any
//!   goal symbol the text there can lex with (`viable_free`). That is the standard's
//!   test and nothing else: the grammar itself has no insertion, so the
//!   definition is not circular. The restricted productions of §12.10.1 are
//!   `[no LineTerminator here]` in the grammar, so a token after a line terminator
//!   there is "not allowed", as the standard says rule 3 amounts to. The overriding
//!   condition (no `;` as an empty statement or in a `for` header) is that those
//!   productions accept a real `;` only. The `;` after a `do`-`while` is `Ins::DoWhile`.
//! - **Context is a parameter, strictness is a position.** `Ctx` is the
//!   grammar's parameters. `EarlyEnv` is what the early errors read of a node's
//!   position, passed down the tree as `child_env` (mirroring `d`): `IsStrict`
//!   (§11.2.2), the labels in scope, whether a `break` or `continue` is allowed,
//!   whether `super` and `new.target` are, and so on. "Contains" is not
//!   recursion into the node, but the flag of the position (`super_call`), which
//!   a function, class or `static` block boundary resets and an arrow function
//!   does not.
//! - **Names are code points.** The StringValue of an identifier is `Tok::name`
//!   (§13.1.2, IdentifierCodePoints, escapes resolved), and a name is a
//!   `Seq<u32>`. A `PrivateIdentifier`'s name is the part after the `#`.
//! - **Strictness has no grammar effect.** The grammar does not read the strict
//!   mode (the parse of `yield` as an identifier is by `[Yield]` alone); every
//!   strict mode difference of the standard is an early error here, and a Use
//!   Strict Directive makes the whole function, parameters and name included,
//!   strict (§11.2.2, §15.2.1's note).
//! - **Reserved words.** `Identifier : IdentifierName but not ReservedWord` is
//!   `is_reserved_token`: an `IdentifierName` written without escapes that is a
//!   `ReservedWord` is not an `Identifier`, and one with escapes whose StringValue
//!   is one is the early error of §13.1.1.
//!
//! # Deviations from the standard
//!
//! - **Recursion depth.** A program whose AST is higher than [`MAX_DEPTH`] is
//!   rejected (item 7.3: "a listed deviation with its number"). `height` counts every
//!   node, so a chain of 1024 binary operators is too high. The standard has no
//!   limit; the contract (`crate::contract`) says the parser accepts every valid
//!   program that has a parse within the limit.
//! - **Annex B is on.** The web legacy compatibility syntax and semantics that
//!   the standard marks as normative optional is specified as present, as a
//!   browser needs it (Annex B is required of a web browser).

/// The arena AST, whose kinds the grammar below is written over, re-exported so
/// that the other modules reach it with `use super::spec::*`.
pub use crate::ast::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §11.1 source text: a sequence of code points.
pub type Src = Seq<u32>;

/// The code points of an ASCII word or punctuator, for comparing with a
/// token's text.
pub open spec fn cps(s: Seq<char>) -> Seq<u32> {
    s.map_values(|c: char| c as u32)
}

// ---------------------------------------------------------------------
// The lexer, as the parser sees it
// ---------------------------------------------------------------------

/// The lexical goal symbols of §12, the argument of every lexer step. The same
/// five as `clazel_js_lexer::spec::Goal`; this crate depends on `vstd` only,
/// so it names them itself, and the bridge to the lexer crate is the
/// [`LexerSpec`] trait.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LexGoal {
    /// `InputElementDiv`.
    InputElementDiv,
    /// `InputElementRegExp`.
    InputElementRegExp,
    /// `InputElementRegExpOrTemplateTail`.
    InputElementRegExpOrTemplateTail,
    /// `InputElementTemplateTail`.
    InputElementTemplateTail,
    /// `InputElementHashbangOrRegExp`: the first token of a `Script` or
    /// `Module`.
    InputElementHashbangOrRegExp,
}

/// The kind of a template literal lexical component (§12.9.6).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TemplateKind {
    /// `NoSubstitutionTemplate`.
    NoSubstitution,
    /// `TemplateHead`.
    Head,
    /// `TemplateMiddle`.
    Middle,
    /// `TemplateTail`.
    Tail,
}

/// The kinds of token the syntactic grammar sees (the input elements of §12
/// that are not trivia).
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TokKind {
    /// `IdentifierName`, a `ReservedWord` or not.
    IdentifierName,
    /// `PrivateIdentifier`.
    PrivateIdentifier,
    /// `Punctuator`, `DivPunctuator` or `RightBracePunctuator`.
    Punctuator,
    /// `NumericLiteral`.
    NumericLiteral,
    /// `StringLiteral`.
    StringLiteral,
    /// A template component.
    Template(TemplateKind),
    /// `RegularExpressionLiteral`.
    RegularExpressionLiteral,
}

/// What automatic semicolon insertion (§12.10) puts in the gap before a token
/// (or before the end of the input): nothing, or a `;` that is not in the
/// source text.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Ins {
    /// Nothing is inserted.
    None,
    /// A `;` inserted by §12.10.1 rule 1 or rule 2 (an offending token, or the
    /// end of the input).
    Semicolon,
    /// A `;` inserted by §12.10.1 rule 1, third condition: after the `)` that ends a `do`-`while`
    /// statement, whatever follows.
    DoWhile,
}

/// A token: what the parser reads. The fields are the lexer's output
/// (`clazel_js_lexer::api::Element` and `Token`).
pub struct Tok {
    /// The kind.
    pub kind: TokKind,
    /// The index of the first code point.
    pub start: int,
    /// One past the last code point.
    pub end: int,
    /// The code points `src[start..end)`.
    pub text: Seq<u32>,
    /// For an `IdentifierName` or `PrivateIdentifier`, its
    /// IdentifierCodePoints (§12.7.1.2), escapes resolved; for a `StringLiteral`,
    /// its SV (§12.9.4.2) as UTF-16 code units. Empty otherwise.
    pub name: Seq<u32>,
    /// For an `IdentifierName` or `PrivateIdentifier`, whether it was written
    /// with a `UnicodeEscapeSequence`.
    pub escaped: bool,
    /// Whether a line terminator precedes the token since the previous one
    /// (the flag §12.10 needs).
    pub nl_before: bool,
    /// For a `NumericLiteral`, a `LegacyOctalIntegerLiteral` or
    /// `NonOctalDecimalIntegerLiteral` (§12.9.3.1); for a `StringLiteral`, one
    /// that holds a `LegacyOctalEscapeSequence` or
    /// `NonOctalDecimalEscapeSequence` (§12.9.4.1). False otherwise.
    pub legacy: bool,
    /// For a `NumericLiteral`, a BigInt literal.
    pub bigint: bool,
    /// For a template component, that its TV is *undefined*: it holds a
    /// `NotEscapeSequence` (§12.9.6.1).
    pub invalid_escape: bool,
    /// For a `RegularExpressionLiteral`, whether `IsValidRegularExpressionLiteral`
    /// (§13.2.7.1) holds.
    pub regexp_valid: bool,
}

/// What the parser reads: the tokens of the source text (trivia dropped), and
/// for each gap before a token, and the one before the end of the input, what
/// §12.10 inserts there. `gaps[k]` is before `toks[k]`, and `gaps[toks.len()]`
/// is at the end, so `gaps.len() == toks.len() + 1`. An inserted `;` is in no
/// token's range: a production that ends with `;` ends at the gap, consuming
/// no token (`semi`), so a node's span never includes anything that is not in
/// the source text.
pub struct Stream {
    /// The tokens of the source text, in order.
    pub toks: Seq<Tok>,
    /// What is inserted before each token and before the end.
    pub gaps: Seq<Ins>,
}

/// The number of tokens.
pub open spec fn tn(ts: Stream) -> int {
    ts.toks.len() as int
}

/// The result of one lexer step, `clazel_js_lexer::api::JsLexer::next_token`.
pub enum LexStep {
    /// Only trivia remain.
    Eof,
    /// A lexical error (`LexError`).
    Error,
    /// The next token.
    Token(Tok),
}

/// What the parser assumes of the lexer: the lexer's own specification
/// (`clazel_js_lexer::spec`, through `next_token_ensures`) says what
/// `next_token` is, and `clazel-js-regexp`'s says what
/// `regexp_literal_valid` is. The parser's contract is stated for any lexer
/// that is a model of this trait, so this crate need not depend on the lexer
/// crate; the implementation of 7.3's second half instantiates it.
pub trait LexerSpec {
    /// The step at `pos` (`0 <= pos <= src.len()`) with `goal`: skip trivia,
    /// then the longest input element of `goal` (§12), as
    /// `clazel_js_lexer::contract::next_token_ensures`.
    spec fn next_token(src: Src, pos: int, goal: LexGoal) -> LexStep;

    /// `IsValidRegularExpressionLiteral` (§13.2.7.1) of the regular
    /// expression literal with this text, `/ body / flags`.
    spec fn regexp_literal_valid(text: Seq<u32>) -> bool;
}

/// The end of token `k - 1`, or 0 before the first token: where the lexer step
/// for token `k` starts.
pub open spec fn prev_end(ts: Stream, k: int) -> int {
    if k <= 0 || k > tn(ts) {
        0
    } else {
        ts.toks[k - 1].end
    }
}

/// `toks` is a lexing of `src`, as a parser drives the lexer (§12: "the
/// syntactic grammar chooses the goal symbol"): each token is the result of
/// a lexer step from the end of the one before, with some goal (the first with
/// `InputElementHashbangOrRegExp`), and only trivia follow the last. The goal
/// is existential, so which of the lexical grammars applied at each token
/// is the grammar's choice (a `/` the grammar reads as a division is
/// `DivPunctuator`, as a regular expression is `RegularExpressionLiteral`): a
/// token sequence the syntactic grammar derives is a lexing with the
/// right goals at once, because each position of the grammar accepts only
/// the token kinds of one goal.
pub open spec fn lexes_as<L: LexerSpec>(src: Src, toks: Seq<Tok>) -> bool {
    let last_end = if toks.len() == 0 {
        0
    } else {
        toks[toks.len() - 1].end
    };
    (exists|goals: Seq<LexGoal>|
        #![auto]
        goals.len() == toks.len() && (toks.len() > 0 ==> goals[0]
            == LexGoal::InputElementHashbangOrRegExp) && (forall|k: int|
            0 <= k < toks.len() ==> L::next_token(
                src,
                if k == 0 {
                    0
                } else {
                    toks[k - 1].end
                },
                #[trigger] goals[k],
            ) == LexStep::Token(toks[k]) && (toks[k].kind == TokKind::RegularExpressionLiteral
                ==> toks[k].regexp_valid == L::regexp_literal_valid(toks[k].text))))
        && (exists|g: LexGoal|
        L::next_token(src, last_end, g) == LexStep::Eof && (toks.len() == 0 ==> g == LexGoal::InputElementHashbangOrRegExp))
}

// ---------------------------------------------------------------------
// Token predicates
// ---------------------------------------------------------------------

/// Token `i` exists and is the punctuator `lit`.
pub open spec fn is_p(ts: Stream, i: int, lit: Seq<char>) -> bool {
    0 <= i < tn(ts) && ts.toks[i].kind == TokKind::Punctuator && ts.toks[i].text =~= cps(lit)
}

/// Token `i` is the keyword or contextual keyword `w`: an `IdentifierName`
/// written without escapes (§12.7.2: a keyword is matched as source
/// characters; a contextual keyword the same way).
pub open spec fn is_kw(ts: Stream, i: int, w: Seq<char>) -> bool {
    0 <= i < tn(ts) && ts.toks[i].kind == TokKind::IdentifierName && !ts.toks[i].escaped
        && ts.toks[i].text =~= cps(w)
}

/// Token `i` is an `IdentifierName` token.
pub open spec fn is_name(ts: Stream, i: int) -> bool {
    0 <= i < tn(ts) && ts.toks[i].kind == TokKind::IdentifierName
}

/// Token `i` is a token of kind `k`.
pub open spec fn is_kind(ts: Stream, i: int, k: TokKind) -> bool {
    0 <= i < tn(ts) && ts.toks[i].kind == k
}

/// A line terminator separates token `i` from the one before.
pub open spec fn nl(ts: Stream, i: int) -> bool {
    0 <= i < tn(ts) && ts.toks[i].nl_before
}

/// §12.7.2 `ReservedWord`.
pub open spec fn reserved_words() -> Seq<Seq<char>> {
    seq![
        "await"@, "break"@, "case"@, "catch"@, "class"@, "const"@, "continue"@, "debugger"@,
        "default"@, "delete"@, "do"@, "else"@, "enum"@, "export"@, "extends"@, "false"@,
        "finally"@, "for"@, "function"@, "if"@, "import"@, "in"@, "instanceof"@, "new"@,
        "null"@, "return"@, "super"@, "switch"@, "this"@, "throw"@, "true"@, "try"@,
        "typeof"@, "var"@, "void"@, "while"@, "with"@, "yield"@,
    ]
}

/// The code points `text` are a `ReservedWord`.
pub open spec fn is_reserved_text(text: Seq<u32>) -> bool {
    exists|w: int| 0 <= w < reserved_words().len() && text =~= cps(#[trigger] reserved_words()[w])
}

/// §12.7.2, §13.1 `Identifier :: IdentifierName but not ReservedWord`: the
/// `but not` excludes a token whose source characters are a `ReservedWord`.
/// An identifier with an escape is never excluded here: §13.1.1 makes one
/// whose StringValue is a reserved word an early error
/// ([`early_identifier_ok`]).
pub open spec fn is_reserved_token(t: Tok) -> bool {
    !t.escaped && is_reserved_text(t.text)
}

// ---------------------------------------------------------------------
// The parameters of the syntactic grammar (§5.1.5)
// ---------------------------------------------------------------------

/// The grammar parameters `[Yield]`, `[Await]`, `[In]`, `[Return]` and
/// `[Default]` (§5.1.5, §13.1, §14.7, §15, §16.2), as booleans (`+Yield` is
/// `true`, `~Yield` is `false`). `[Tagged]` is [`EarlyEnv::tagged`].
pub struct Ctx {
    /// `[Yield]`.
    pub yield_: bool,
    /// `[Await]`.
    pub await_: bool,
    /// `[In]`.
    pub in_: bool,
    /// `[Return]`.
    pub return_: bool,
    /// `[Default]`: this declaration is the one `export default` names, so its
    /// `BindingIdentifier` may be absent.
    pub deflt: bool,
}

/// The same context with `[In]` set to `b` and `[Default]` cleared.
pub open spec fn cx_in(cx: Ctx, b: bool) -> Ctx {
    Ctx { yield_: cx.yield_, await_: cx.await_, in_: b, return_: cx.return_, deflt: false }
}

/// A context for the parts of a function, generator, async function or async
/// generator (`yield_`: a generator, `await_`: async): `[+Yield]`, `[+Await]`
/// as the kind of function says, `[+In]`, and `[Return]` as given.
pub open spec fn cx_fn(yield_: bool, await_: bool, return_: bool) -> Ctx {
    Ctx { yield_: yield_, await_: await_, in_: true, return_: return_, deflt: false }
}

} // verus!

verus! {

// ---------------------------------------------------------------------
// The arena, read totally
// ---------------------------------------------------------------------

/// Which goal symbol of §16 the source text is parsed as.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SourceGoal {
    /// `Script` (§16.1), with Annex B's HTML-like comments in the lexer.
    Script,
    /// `Module` (§16.2).
    Module,
}

/// The kind of node `c`; `Script` for an index outside the arena (a value no
/// positional check accepts, since [`ast_wf`] makes `Script` the root only).
pub open spec fn kd(a: AstV, c: int) -> NodeKind {
    if 0 <= c < a.nodes.len() {
        a.nodes[c].kind
    } else {
        NodeKind::Script
    }
}

/// The [`Op`] of node `c`, `Op::None` outside the arena.
pub open spec fn op_of(a: AstV, c: int) -> Op {
    if 0 <= c < a.nodes.len() {
        a.nodes[c].op
    } else {
        Op::None
    }
}

/// The `flag` of node `c`, `false` outside the arena.
pub open spec fn flag_of(a: AstV, c: int) -> bool {
    0 <= c < a.nodes.len() && a.nodes[c].flag
}

/// The children of node `n`, none outside the arena.
pub open spec fn kids(a: AstV, n: int) -> Seq<int> {
    if 0 <= n < a.nodes.len() {
        a.nodes[n].children
    } else {
        Seq::empty()
    }
}

/// `ks[k]`, or `-1` (no node) when `k` is out of range.
pub open spec fn kid(ks: Seq<int>, k: int) -> int {
    if 0 <= k < ks.len() {
        ks[k]
    } else {
        -1
    }
}

/// The kind of the first child of node `c`, `Script` if there is none.
pub open spec fn first_kid_kind(a: AstV, c: int) -> NodeKind {
    kd(a, kid(kids(a, c), 0))
}

/// §14 `Statement`: the kinds a `Statement` is.
pub open spec fn is_statement_kind(k: NodeKind) -> bool {
    k == NodeKind::BlockStatement || k == NodeKind::VariableStatement || k
        == NodeKind::EmptyStatement || k == NodeKind::ExpressionStatement || k
        == NodeKind::IfStatement || k == NodeKind::DoWhileStatement || k
        == NodeKind::WhileStatement || k == NodeKind::ForStatement || k == NodeKind::ForInStatement
        || k == NodeKind::ForOfStatement || k == NodeKind::ContinueStatement || k
        == NodeKind::BreakStatement || k == NodeKind::ReturnStatement || k
        == NodeKind::WithStatement || k == NodeKind::SwitchStatement || k
        == NodeKind::LabelledStatement || k == NodeKind::ThrowStatement || k
        == NodeKind::TryStatement || k == NodeKind::DebuggerStatement
}

/// §15.2 `HoistableDeclaration`.
pub open spec fn is_hoistable_kind(k: NodeKind) -> bool {
    k == NodeKind::FunctionDeclaration || k == NodeKind::GeneratorDeclaration || k
        == NodeKind::AsyncFunctionDeclaration || k == NodeKind::AsyncGeneratorDeclaration
}

/// §14 `Declaration`.
pub open spec fn is_declaration_kind(k: NodeKind) -> bool {
    is_hoistable_kind(k) || k == NodeKind::ClassDeclaration || k == NodeKind::LexicalDeclaration
}

/// §14.2 `StatementListItem`.
pub open spec fn is_item_kind(k: NodeKind) -> bool {
    is_statement_kind(k) || is_declaration_kind(k)
}

/// §16.2 `ModuleItem`.
pub open spec fn is_module_item_kind(k: NodeKind) -> bool {
    is_item_kind(k) || k == NodeKind::ImportDeclaration || k == NodeKind::ExportDeclaration
}

/// §14.3.3 `BindingPattern`.
pub open spec fn is_binding_pattern_kind(k: NodeKind) -> bool {
    k == NodeKind::ObjectBindingPattern || k == NodeKind::ArrayBindingPattern
}

/// A `BindingIdentifier` or a `BindingPattern`.
pub open spec fn is_binding_target_kind(k: NodeKind) -> bool {
    k == NodeKind::BindingIdentifier || is_binding_pattern_kind(k)
}

/// §13.15.5 `AssignmentPattern`.
pub open spec fn is_assignment_pattern_kind(k: NodeKind) -> bool {
    k == NodeKind::ObjectAssignmentPattern || k == NodeKind::ArrayAssignmentPattern
}

/// §13.2.5 `PropertyName`.
pub open spec fn is_prop_name_kind(k: NodeKind) -> bool {
    k == NodeKind::IdentifierName || k == NodeKind::StringLiteral || k == NodeKind::NumericLiteral
        || k == NodeKind::ComputedPropertyName
}

/// §15.7 `ClassElementName`.
pub open spec fn is_class_element_name_kind(k: NodeKind) -> bool {
    is_prop_name_kind(k) || k == NodeKind::PrivateIdentifier
}

/// A kind that ends a list and takes no comma after it: `...rest`.
pub open spec fn is_rest_kind(k: NodeKind) -> bool {
    k == NodeKind::FunctionRestParameter || k == NodeKind::BindingRestElement || k
        == NodeKind::BindingRestProperty || k == NodeKind::AssignmentRestElement || k
        == NodeKind::AssignmentRestProperty
}

/// The binding strength of an expression node, the standard's chain of
/// productions in one number: how many of the productions between
/// `Expression` and `PrimaryExpression` the node is an instance of.
///
/// `-1` `Expression` (comma); `0` `AssignmentExpression` and the
/// productions at its level, and `CoalesceExpression`; `1` `LogicalORExpression`;
/// `2` `LogicalANDExpression`; `3` `BitwiseORExpression`; `4`
/// `BitwiseXORExpression`; `5` `BitwiseANDExpression`; `6`
/// `EqualityExpression`; `7` `RelationalExpression`; `8` `ShiftExpression`;
/// `9` `AdditiveExpression`; `10` `MultiplicativeExpression`; `11`
/// `ExponentiationExpression`; `12` `UnaryExpression`; `13`
/// `UpdateExpression`; `14` `OptionalExpression`; `15` `CallExpression`; `16`
/// `NewExpression` without arguments; `17` `MemberExpression` and
/// `PrimaryExpression`. A node that is not an expression is `-100`.
///
/// A production `X : Y | X op Z` allows an operand of level at least `Y`'s;
/// §13.6 to §13.13, §13.3 and §13.14 are written this way, and the checks in
/// [`d_expr`] read the levels off them. A `MemberExpression` or
/// `TaggedTemplate` node is a `MemberExpression` (17) when its object is, and
/// a `CallExpression` (15) when its object is a `CallExpression`.
pub open spec fn lvl(a: AstV, n: int) -> int
    decreases n,
{
    if n < 0 || n >= a.nodes.len() {
        -100
    } else {
        let nd = a.nodes[n];
        match nd.kind {
            NodeKind::Expression => -1,
            NodeKind::ConditionalExpression | NodeKind::AssignmentExpression
            | NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction | NodeKind::YieldExpression
            | NodeKind::CoalesceExpression => 0,
            NodeKind::LogicalORExpression => 1,
            NodeKind::LogicalANDExpression => 2,
            NodeKind::BitwiseORExpression => 3,
            NodeKind::BitwiseXORExpression => 4,
            NodeKind::BitwiseANDExpression => 5,
            NodeKind::EqualityExpression => 6,
            NodeKind::RelationalExpression => 7,
            NodeKind::ShiftExpression => 8,
            NodeKind::AdditiveExpression => 9,
            NodeKind::MultiplicativeExpression => 10,
            NodeKind::ExponentiationExpression => 11,
            NodeKind::UnaryExpression | NodeKind::AwaitExpression => 12,
            NodeKind::UpdateExpression => 13,
            NodeKind::OptionalExpression => 14,
            NodeKind::CallExpression | NodeKind::SuperCall | NodeKind::ImportCall => 15,
            NodeKind::NewExpression => if nd.children.len() == 2 && kd(a, nd.children[1])
                == NodeKind::Absent {
                16
            } else {
                17
            },
            NodeKind::MemberExpression | NodeKind::TaggedTemplate => if nd.children.len() > 0
                && 0 <= nd.children[0] < n && lvl(a, nd.children[0]) == 17 {
                17
            } else {
                15
            },
            NodeKind::IdentifierReference | NodeKind::ThisExpression | NodeKind::NullLiteral
            | NodeKind::BooleanLiteral | NodeKind::NumericLiteral | NodeKind::StringLiteral
            | NodeKind::RegularExpressionLiteral | NodeKind::TemplateLiteral
            | NodeKind::ArrayLiteral | NodeKind::ObjectLiteral | NodeKind::ParenthesizedExpression
            | NodeKind::FunctionExpression | NodeKind::GeneratorExpression
            | NodeKind::AsyncFunctionExpression | NodeKind::AsyncGeneratorExpression
            | NodeKind::ClassExpression | NodeKind::SuperProperty | NodeKind::ImportMeta
            | NodeKind::NewTarget => 17,
            _ => -100,
        }
    }
}

/// An `AssignmentExpression` (level 0 or above).
pub open spec fn is_assign_expr(a: AstV, c: int) -> bool {
    lvl(a, c) >= 0
}

/// A `MemberExpression` or a `CallExpression`: what can be the object of a
/// property access, the callee of a call or the tag of a template.
pub open spec fn is_member_or_call(a: AstV, c: int) -> bool {
    lvl(a, c) == 17 || lvl(a, c) == 15
}

/// A `LeftHandSideExpression` (level 14 or above).
pub open spec fn is_lhs_expr(a: AstV, c: int) -> bool {
    lvl(a, c) >= 14
}

/// §13.15.5 `DestructuringAssignmentTarget` and the target of an
/// assignment with `=`: a `LeftHandSideExpression` that is not an
/// `ObjectLiteral` or `ArrayLiteral` (those are covers, read as the
/// pattern), or an `AssignmentPattern`.
pub open spec fn is_destructuring_target(a: AstV, c: int) -> bool {
    (is_lhs_expr(a, c) && kd(a, c) != NodeKind::ObjectLiteral && kd(a, c) != NodeKind::ArrayLiteral)
        || is_assignment_pattern_kind(kd(a, c))
}

// ---------------------------------------------------------------------
// The shape of an arena
// ---------------------------------------------------------------------

/// The arena is well formed: the root is the last node and the only
/// `Script` or `Module`; every child has a smaller index than its parent
/// (so the arena is a forest in post-order, and recursion on the index is
/// well-founded); every node but the root is a child of some node (no garbage).
pub open spec fn ast_wf(a: AstV) -> bool {
    a.nodes.len() > 0 && a.root == a.nodes.len() - 1 && (forall|m: int|
        0 <= m < a.nodes.len() ==> {
            let nd = #[trigger] a.nodes[m];
            (forall|k: int|
                0 <= k < nd.children.len() ==> 0 <= #[trigger] nd.children[k] < m) && ((nd.kind
                == NodeKind::Script || nd.kind == NodeKind::Module) <==> m == a.root)
        }) && (forall|m: int| 0 <= m < a.root ==> #[trigger] has_parent(a, m))
}

/// Node `m` is a child of some node.
pub open spec fn has_parent(a: AstV, m: int) -> bool {
    exists|p: int, k: int|
        m < p < a.nodes.len() && 0 <= k < a.nodes[p].children.len()
            && #[trigger] a.nodes[p].children[k] == m
}

/// Every span is within `0..len`, `start <= end`, and a child's span is within its
/// parent's: spans inside the input.
pub open spec fn spans_wf(a: AstV, len: int) -> bool {
    forall|m: int|
        0 <= m < a.nodes.len() ==> {
            let nd = #[trigger] a.nodes[m];
            0 <= nd.start <= nd.end <= len && (forall|k: int|
                0 <= k < nd.children.len() ==> nd.start <= a.nodes[#[trigger] nd.children[k]].start
                    && a.nodes[nd.children[k]].end <= nd.end)
        }
}

/// The height of the tree under node `n`, in nodes: 1 for a leaf. The
/// recursion limit (item 7.3, "a listed deviation") is on this number.
pub open spec fn height(a: AstV, n: int) -> int
    decreases n, 1int,
{
    if n < 0 || n >= a.nodes.len() {
        0
    } else {
        1 + max_height(a, n, a.nodes[n].children, 0)
    }
}

/// The largest height among `ks[k..]`, each of which is a child of `n`.
pub open spec fn max_height(a: AstV, n: int, ks: Seq<int>, k: int) -> int
    decreases n, 0int, ks.len() - k,
{
    if k < 0 || k >= ks.len() {
        0
    } else {
        let c = ks[k];
        let h = if 0 <= c < n {
            height(a, c)
        } else {
            0
        };
        let rest = max_height(a, n, ks, k + 1);
        if h > rest {
            h
        } else {
            rest
        }
    }
}

/// The deviation of phase-7.md item 7.3 ("Recursion: depth is bounded by an
/// explicit limit; deeper nesting is a `SyntaxError`, a listed deviation with its
/// number"): the parser rejects a program whose AST is higher than this. The
/// standard has no such limit; every program it accepts and whose parse is
/// at most this high is accepted, and the others get [`ParseError::TooDeep`]
/// or [`ParseError::Syntax`]. The height counts every node, so a chain of
/// binary operators `a + b + c + ...` is as high as it is long.
pub const MAX_DEPTH: usize = 1024;

} // verus!

verus! {

// ---------------------------------------------------------------------
// The grammar, as a relation between nodes and tokens
// ---------------------------------------------------------------------
//
// `d(a, ts, n, cx, i, j)`: node `n` of the arena `a` is an instance of its
// production, in context `cx`, deriving exactly the tokens `ts.toks[i..j)`.
// Each node kind has one arm, written from the production(s) it is named
// after. A child is checked with `dc` at the range the production gives it,
// which starts where the production puts it and ends where the child's own
// span says (`ed`), so no arm guesses a position: where the production has
// fixed positions for optional symbols, an absent one is an `Absent` child
// with the empty range at its place.

/// §13.1, §13.2.2 `Identifier`, `IdentifierReference[?Yield, ?Await]`,
/// `BindingIdentifier[?Yield, ?Await]` and `LabelIdentifier[?Yield, ?Await]`
/// at token `i`: an `IdentifierName` that is not a `ReservedWord`, or
/// `yield` when `[~Yield]`, or `await` when `[~Await]`.
pub open spec fn ident_tok(ts: Stream, i: int, cx: Ctx) -> bool {
    is_name(ts, i) && (!is_reserved_token(ts.toks[i]) || (is_kw(ts, i, "yield"@) && !cx.yield_)
        || (is_kw(ts, i, "await"@) && !cx.await_))
}

/// The text of the punctuator or keyword of an operator.
pub open spec fn op_text(op: Op) -> Seq<char> {
    match op {
        Op::Delete => "delete"@,
        Op::Void => "void"@,
        Op::Typeof => "typeof"@,
        Op::Plus => "+"@,
        Op::Minus => "-"@,
        Op::BitNot => "~"@,
        Op::LogicalNot => "!"@,
        Op::PrefixIncrement | Op::PostfixIncrement => "++"@,
        Op::PrefixDecrement | Op::PostfixDecrement => "--"@,
        Op::Exp => "**"@,
        Op::Mul => "*"@,
        Op::Div => "/"@,
        Op::Rem => "%"@,
        Op::Add => "+"@,
        Op::Sub => "-"@,
        Op::Shl => "<<"@,
        Op::Shr => ">>"@,
        Op::UShr => ">>>"@,
        Op::Lt => "<"@,
        Op::Gt => ">"@,
        Op::Le => "<="@,
        Op::Ge => ">="@,
        Op::InstanceOf => "instanceof"@,
        Op::In => "in"@,
        Op::Eq => "=="@,
        Op::Ne => "!="@,
        Op::StrictEq => "==="@,
        Op::StrictNe => "!=="@,
        Op::BitAnd => "&"@,
        Op::BitXor => "^"@,
        Op::BitOr => "|"@,
        Op::LogicalAnd => "&&"@,
        Op::LogicalOr => "||"@,
        Op::Coalesce => "??"@,
        Op::Assign => "="@,
        Op::MulAssign => "*="@,
        Op::DivAssign => "/="@,
        Op::RemAssign => "%="@,
        Op::AddAssign => "+="@,
        Op::SubAssign => "-="@,
        Op::ShlAssign => "<<="@,
        Op::ShrAssign => ">>="@,
        Op::UShrAssign => ">>>="@,
        Op::BitAndAssign => "&="@,
        Op::BitXorAssign => "^="@,
        Op::BitOrAssign => "|="@,
        Op::ExpAssign => "**="@,
        Op::LogicalAndAssign => "&&="@,
        Op::LogicalOrAssign => "||="@,
        Op::CoalesceAssign => "??="@,
        _ => ""@,
    }
}

/// The operator `op` is at token `i`: a keyword for `delete`, `void`,
/// `typeof`, `instanceof` and `in`, a punctuator for the others.
pub open spec fn is_op_tok(ts: Stream, i: int, op: Op) -> bool {
    if op == Op::Delete || op == Op::Void || op == Op::Typeof || op == Op::InstanceOf || op
        == Op::In {
        is_kw(ts, i, op_text(op))
    } else {
        is_p(ts, i, op_text(op))
    }
}

/// §13.5 the `UnaryOperator`s.
pub open spec fn is_unary_op(op: Op) -> bool {
    op == Op::Delete || op == Op::Void || op == Op::Typeof || op == Op::Plus || op == Op::Minus
        || op == Op::BitNot || op == Op::LogicalNot
}

/// §13.15 `AssignmentOperator`, and `=`.
pub open spec fn is_assign_op(op: Op) -> bool {
    op == Op::Assign || op == Op::MulAssign || op == Op::DivAssign || op == Op::RemAssign || op
        == Op::AddAssign || op == Op::SubAssign || op == Op::ShlAssign || op == Op::ShrAssign
        || op == Op::UShrAssign || op == Op::BitAndAssign || op == Op::BitXorAssign || op
        == Op::BitOrAssign || op == Op::ExpAssign || op == Op::LogicalAndAssign || op
        == Op::LogicalOrAssign || op == Op::CoalesceAssign
}

/// §13.6 to §13.13: the operators of a binary expression production.
pub open spec fn bin_op_ok(k: NodeKind, op: Op) -> bool {
    match k {
        NodeKind::ExponentiationExpression => op == Op::Exp,
        NodeKind::MultiplicativeExpression => op == Op::Mul || op == Op::Div || op == Op::Rem,
        NodeKind::AdditiveExpression => op == Op::Add || op == Op::Sub,
        NodeKind::ShiftExpression => op == Op::Shl || op == Op::Shr || op == Op::UShr,
        NodeKind::RelationalExpression => op == Op::Lt || op == Op::Gt || op == Op::Le || op
            == Op::Ge || op == Op::InstanceOf || op == Op::In,
        NodeKind::EqualityExpression => op == Op::Eq || op == Op::Ne || op == Op::StrictEq || op
            == Op::StrictNe,
        NodeKind::BitwiseANDExpression => op == Op::BitAnd,
        NodeKind::BitwiseXORExpression => op == Op::BitXor,
        NodeKind::BitwiseORExpression => op == Op::BitOr,
        NodeKind::LogicalANDExpression => op == Op::LogicalAnd,
        NodeKind::LogicalORExpression => op == Op::LogicalOr,
        NodeKind::CoalesceExpression => op == Op::Coalesce,
        _ => false,
    }
}

/// The operands of a binary expression, by the productions of §13.6 to
/// §13.13: `X : Y | X op Z` (left associative) takes a left operand that is
/// an `X` and a right operand that is a `Z`; the levels are [`lvl`]'s.
/// §13.6 `ExponentiationExpression : UpdateExpression ** ExponentiationExpression`
/// (the left operand is not a `UnaryExpression`, and the operator is right
/// associative). §13.10 `RelationalExpression : [+In] PrivateIdentifier in
/// ShiftExpression`. §13.13 `CoalesceExpression : CoalesceExpressionHead ??
/// BitwiseORExpression`, where the head is a `CoalesceExpression` or a
/// `BitwiseORExpression`: `??` never mixes with `&&` or `||` unparenthesized.
pub open spec fn binary_operands_ok(a: AstV, k: NodeKind, op: Op, l: int, r: int) -> bool {
    match k {
        NodeKind::ExponentiationExpression => lvl(a, l) >= 13 && lvl(a, r) >= 11,
        NodeKind::MultiplicativeExpression => lvl(a, l) >= 10 && lvl(a, r) >= 11,
        NodeKind::AdditiveExpression => lvl(a, l) >= 9 && lvl(a, r) >= 10,
        NodeKind::ShiftExpression => lvl(a, l) >= 8 && lvl(a, r) >= 9,
        NodeKind::RelationalExpression => (lvl(a, l) >= 7 || (op == Op::In && kd(a, l)
            == NodeKind::PrivateIdentifier)) && lvl(a, r) >= 8,
        NodeKind::EqualityExpression => lvl(a, l) >= 6 && lvl(a, r) >= 7,
        NodeKind::BitwiseANDExpression => lvl(a, l) >= 5 && lvl(a, r) >= 6,
        NodeKind::BitwiseXORExpression => lvl(a, l) >= 4 && lvl(a, r) >= 5,
        NodeKind::BitwiseORExpression => lvl(a, l) >= 3 && lvl(a, r) >= 4,
        NodeKind::LogicalANDExpression => lvl(a, l) >= 2 && lvl(a, r) >= 3,
        NodeKind::LogicalORExpression => lvl(a, l) >= 1 && lvl(a, r) >= 2,
        NodeKind::CoalesceExpression => (lvl(a, l) >= 3 || kd(a, l) == NodeKind::CoalesceExpression)
            && lvl(a, r) >= 3,
        _ => false,
    }
}

/// The index just past the tokens of child `c` of a node, when the child starts
/// at token `p`: the token whose end is the end of `c`'s span, if `c` has a
/// span; `p` itself if it is empty. The span of a node is part of the AST,
/// so this is not a guess: the grammar's checks apply to the range it gives,
/// and a node whose span is not the range of tokens it derives is not a
/// derivation (`span_ok`).
pub open spec fn ed(a: AstV, ts: Stream, c: int, p: int) -> int {
    if c < 0 || c >= a.nodes.len() || a.nodes[c].start >= a.nodes[c].end {
        p
    } else {
        1 + choose|x: int| p <= x < tn(ts) && ts.toks[x].end == a.nodes[c].end
    }
}

/// The source range of node `n` is the range of tokens `ts[i..j)`: it starts at
/// the first token and ends at the last; a node with no tokens is the empty
/// range at the end of the token before.
pub open spec fn span_ok(a: AstV, ts: Stream, n: int, i: int, j: int) -> bool {
    if i == j {
        a.nodes[n].start == prev_end(ts, i) && a.nodes[n].end == a.nodes[n].start
    } else {
        a.nodes[n].start == ts.toks[i].start && a.nodes[n].end == ts.toks[j - 1].end
    }
}

/// §12.10 the `;` that ends a production, whose last child ends at token `m`
/// (the production's range ends at `j`): an explicit `;` at `m` (`j == m + 1`),
/// or one inserted in the gap before token `m` (`j == m`, nothing consumed). `dw`
/// also accepts the `;` of §12.10.1 rule 1 (third condition), inserted after a `do`-`while`.
pub open spec fn semi(ts: Stream, m: int, j: int, dw: bool) -> bool {
    (is_p(ts, m, ";"@) && j == m + 1) || (0 <= m < ts.gaps.len() && j == m && (ts.gaps[m]
        == Ins::Semicolon || (dw && ts.gaps[m] == Ins::DoWhile)))
}

/// Node `n` derives `ts[i..j)` in context `cx`.
pub open spec fn d(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 4int, 0int, 0int,
{
    0 <= n < a.nodes.len() && 0 <= i <= j <= tn(ts) && span_ok(a, ts, n, i, j) && (d_stmt(
        a,
        ts,
        n,
        cx,
        i,
        j,
    ) || d_func(a, ts, n, cx, i, j) || d_pat(a, ts, n, cx, i, j) || d_expr(a, ts, n, cx, i, j)
        || d_module(a, ts, n, cx, i, j))
}

/// Child `c` of a node whose index is `bound` derives `ts[i..j)`.
pub open spec fn dc(a: AstV, ts: Stream, bound: int, c: int, cx: Ctx, i: int, j: int) -> bool
    decreases bound, 0int, 0int, 0int,
{
    0 <= c < bound && d(a, ts, c, cx, i, j)
}

/// The children `ks[k..]` derive consecutive ranges that make `ts[i..j)`,
/// with nothing between them (the statements of a `StatementList`).
pub open spec fn dl(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    j: int,
) -> bool
    decreases bound, 1int, ks.len() - k, 0int,
{
    if k >= ks.len() {
        i == j
    } else {
        let m = ed(a, ts, ks[k], i);
        dc(a, ts, bound, ks[k], cx, i, m) && dl(a, ts, bound, ks, k + 1, cx, m, j)
    }
}

/// The index after the last child of the list `ks[k..]` of [`dsep`] when its
/// first starts at `i`, before any trailing `,`; `i` for an empty list.
pub open spec fn list_next(a: AstV, ts: Stream, ks: Seq<int>, k: int, i: int) -> int
    decreases ks.len() - k,
{
    if k >= ks.len() {
        i
    } else if k + 1 == ks.len() {
        ed(a, ts, ks[k], i)
    } else {
        list_next(a, ts, ks, k + 1, ed(a, ts, ks[k], i) + 1)
    }
}

/// The children `ks[k..]` are separated by `,` and, when `trail` and the last is
/// not a `...rest`, may be followed by one more `,`: the shape of
/// `ArgumentList`, `PropertyDefinitionList`, `FormalParameterList`, `BindingList`
/// and the like. An empty list derives the empty range.
pub open spec fn dsep(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    j: int,
    trail: bool,
) -> bool
    decreases bound, 1int, ks.len() - k, 0int,
{
    if k >= ks.len() {
        i == j
    } else {
        let m = ed(a, ts, ks[k], i);
        dc(a, ts, bound, ks[k], cx, i, m) && (if k + 1 < ks.len() {
            is_p(ts, m, ","@) && dsep(a, ts, bound, ks, k + 1, cx, m + 1, j, trail)
        } else {
            j == m || (trail && !is_rest_kind(kd(a, ks[k])) && is_p(ts, m, ","@) && j == m + 1)
        })
    }
}

/// §13.2.4 `ElementList` with `Elision`s, and §14.3.3 `BindingElementList`: the
/// children are elements and [`NodeKind::Elision`]s (each one `,`, a hole).
/// After an element comes a `,` if anything follows (the elements' separator, which
/// for a hole is the hole's own comma), or, last, an optional `,`; after
/// an `Elision` comes the next child directly.
pub open spec fn darray(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    j: int,
) -> bool
    decreases bound, 1int, ks.len() - k, 0int,
{
    if k >= ks.len() {
        i == j
    } else {
        let m = ed(a, ts, ks[k], i);
        dc(a, ts, bound, ks[k], cx, i, m) && (if kd(a, ks[k]) == NodeKind::Elision {
            darray(a, ts, bound, ks, k + 1, cx, m, j)
        } else if k + 1 < ks.len() {
            is_p(ts, m, ","@) && darray(a, ts, bound, ks, k + 1, cx, m + 1, j)
        } else {
            j == m || (!is_rest_kind(kd(a, ks[k])) && is_p(ts, m, ","@) && j == m + 1)
        })
    }
}

/// §13.2.8 `TemplateLiteral`: the children alternate `TemplateElement`,
/// `Expression`, ..., `TemplateElement`; a template component is one token,
/// whose lexical kind is `Head` first, `Middle` between, and `Tail` last, or a
/// lone `NoSubstitution`.
pub open spec fn dtemplate(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    j: int,
) -> bool
    decreases bound, 1int, ks.len() - k, 0int,
{
    let ce = kid(ks, k + 1);
    let e = ed(a, ts, ce, i + 1);
    if k + 1 == ks.len() {
        // The last component: a `NoSubstitutionTemplate` or a `TemplateTail`.
        j == i + 1 && kd(a, ks[k]) == NodeKind::TemplateElement && dc(a, ts, bound, ks[k], cx, i, j)
            && (if k == 0 {
            is_kind(ts, i, TokKind::Template(TemplateKind::NoSubstitution))
        } else {
            is_kind(ts, i, TokKind::Template(TemplateKind::Tail))
        })
    } else if k + 1 < ks.len() {
        // `TemplateHead` or `TemplateMiddle`, an `Expression`, and the rest.
        kd(a, ks[k]) == NodeKind::TemplateElement && dc(a, ts, bound, ks[k], cx, i, i + 1)
            && (if k == 0 {
            is_kind(ts, i, TokKind::Template(TemplateKind::Head))
        } else {
            is_kind(ts, i, TokKind::Template(TemplateKind::Middle))
        }) && lvl(a, ce) >= -1 && dc(a, ts, bound, ce, cx, i + 1, e) && dtemplate(
            a,
            ts,
            bound,
            ks,
            k + 2,
            cx,
            e,
            j,
        )
    } else {
        false
    }
}

/// §15.7 `ClassElementList`: the elements `ks[k..]` with any number of `;`
/// (the `ClassElement : ;` alternative) before, between and after them.
pub open spec fn dclass(
    a: AstV,
    ts: Stream,
    bound: int,
    ks: Seq<int>,
    k: int,
    cx: Ctx,
    i: int,
    j: int,
) -> bool
    decreases bound, 1int, ks.len() - k, j - i,
{
    let m = ed(a, ts, kid(ks, k), i);
    (k >= ks.len() && i == j) || (i < j && is_p(ts, i, ";"@) && dclass(a, ts, bound, ks, k, cx, i + 1, j))
        || (k < ks.len() && dc(a, ts, bound, ks[k], cx, i, m) && dclass(a, ts, bound, ks, k + 1, cx, m, j))
}

/// Every child in `ks` is a `StatementListItem`.
pub open spec fn all_items(a: AstV, ks: Seq<int>) -> bool {
    forall|k: int| 0 <= k < ks.len() ==> is_item_kind(kd(a, #[trigger] ks[k]))
}

/// Every child in `ks` from `from` on is of kind `x` or `y`.
pub open spec fn all_kind2(a: AstV, ks: Seq<int>, from: int, x: NodeKind, y: NodeKind) -> bool {
    forall|k: int|
        from <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == x || kd(a, ks[k]) == y
}

/// Every child in `ks` is an `AssignmentExpression` or a `SpreadElement`: the
/// items of an `ArgumentList`.
pub open spec fn all_args(a: AstV, ks: Seq<int>) -> bool {
    forall|k: int|
        0 <= k < ks.len() ==> is_assign_expr(a, #[trigger] ks[k]) || kd(a, ks[k])
            == NodeKind::SpreadElement
}

/// A `...rest` child is the last of its list.
pub open spec fn rest_only_last(a: AstV, ks: Seq<int>) -> bool {
    forall|k: int| 0 <= k + 1 < ks.len() ==> !is_rest_kind(kd(a, #[trigger] ks[k]))
}

/// An optional `Expression`: absent, or an `Expression`.
pub open spec fn opt_expr(a: AstV, c: int) -> bool {
    kd(a, c) == NodeKind::Absent || lvl(a, c) >= -1
}

/// The optional `Initializer` of node child `c` at token `m`, ending at
/// `j`: `Absent` (when not `req`d) or `= AssignmentExpression`.
pub open spec fn d_init(
    a: AstV,
    ts: Stream,
    bound: int,
    c: int,
    cx: Ctx,
    m: int,
    j: int,
    req: bool,
) -> bool
    decreases bound, 1int, 0int, 0int,
{
    (!req && kd(a, c) == NodeKind::Absent && j == m && dc(a, ts, bound, c, cx, m, m)) || (is_p(
        ts,
        m,
        "="@,
    ) && is_assign_expr(a, c) && dc(a, ts, bound, c, cx, m + 1, j))
}

} // verus!

verus! {

/// §14.7.4 `for ( ...`: the token after the initializer and what ends it:
/// the `;` of `Expression ;`, `;` and `var VariableDeclarationList ;`, or
/// nothing, for a `LexicalDeclaration`, which holds its own `;`.
pub open spec fn for_init_next(a: AstV, ts: Stream, c: int, s: int) -> int {
    if kd(a, c) == NodeKind::LexicalDeclaration {
        ed(a, ts, c, s)
    } else {
        ed(a, ts, c, s) + 1
    }
}

/// §14.7.4 `for ( ...` up to and including what follows the initializer:
/// `LexicalDeclaration` (always a real `;`: §12.10.1 rule 4), `var
/// VariableDeclarationList ;` or `Expression ;` or `;`, with `[~In]`.
pub open spec fn for_init_ok(a: AstV, ts: Stream, bound: int, c: int, cx: Ctx, s: int) -> bool
    decreases bound, 1int, 0int, 0int,
{
    let cxi = cx_in(cx, false);
    let m = ed(a, ts, c, s);
    dc(a, ts, bound, c, cxi, s, m) && (if kd(a, c) == NodeKind::LexicalDeclaration {
        is_p(ts, m - 1, ";"@)
    } else {
        is_p(ts, m, ";"@) && (kd(a, c) == NodeKind::Absent || kd(a, c)
            == NodeKind::VariableDeclarationList || (lvl(a, c) >= -1 && !(is_kw(ts, s, "let"@)
            && is_p(ts, s + 1, "["@))))
    })
}

/// The head of a `for ( ... in/of` loop, at token `s`: a `ForDeclaration`, or
/// a `LeftHandSideExpression` (not an `ObjectLiteral` or `ArrayLiteral`, which
/// are the covers of an assignment pattern) or an `AssignmentPattern`, subject to
/// the lookahead of §14.7.5 (`of`: `[lookahead ∉ { let, async of }]`, `for await`:
/// `[lookahead ≠ let]`, `in`: `[lookahead ≠ let []`).
pub open spec fn for_head_ok(a: AstV, ts: Stream, c: int, s: int, of: bool, is_await: bool) -> bool {
    kd(a, c) == NodeKind::ForDeclaration || (is_destructuring_target(a, c) && if of {
        if is_await {
            !is_kw(ts, s, "let"@)
        } else {
            !is_kw(ts, s, "let"@) && !(is_kw(ts, s, "async"@) && is_kw(ts, s + 1, "of"@))
        }
    } else {
        !(is_kw(ts, s, "let"@) && is_p(ts, s + 1, "["@))
    })
}

/// §14.12 a `CaseBlock` has at most one `DefaultClause`.
pub open spec fn at_most_one_default(a: AstV, ks: Seq<int>) -> bool {
    forall|x: int, y: int|
        1 <= x < y < ks.len() ==> !(kd(a, #[trigger] ks[x]) == NodeKind::DefaultClause && kd(
            a,
            #[trigger] ks[y],
        ) == NodeKind::DefaultClause)
}

/// A `LabelledItem` or the body of an `if`: a `Statement`, or a
/// `FunctionDeclaration` (§14.13 `LabelledItem`; Annex B.3.3).
pub open spec fn is_stmt_or_function(a: AstV, c: int) -> bool {
    is_statement_kind(kd(a, c)) || kd(a, c) == NodeKind::FunctionDeclaration
}

/// §14 statements, declarations and the roots (§16.1.1, §16.2.1): the arms of
/// [`d`] for `Script`, `Module` and the kinds of §14.
pub open spec fn d_stmt(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 3int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let k2 = kid(ks, 2);
    let k3 = kid(ks, 3);
    let cxt = cx_in(cx, true);
    match nd.kind {
        // 16.1 `Script : ScriptBody?`, `ScriptBody : StatementList[~Yield, ~Await, ~Return]`.
        NodeKind::Script => i == 0 && j == tn(ts) && all_items(a, ks) && dl(a, ts, n, ks, 0, cx, i, j),
        // 16.2 `Module : ModuleBody?`, `ModuleItemList : ModuleItem | ModuleItemList ModuleItem`.
        NodeKind::Module => i == 0 && j == tn(ts) && (forall|k: int|
            0 <= k < ks.len() ==> is_module_item_kind(kd(a, #[trigger] ks[k]))) && dl(
            a,
            ts,
            n,
            ks,
            0,
            cx,
            i,
            j,
        ),
        // 14.2 `Block : { StatementList? }`.
        NodeKind::BlockStatement => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && all_items(a, ks) && dl(a, ts, n, ks, 0, cx, i + 1, j - 1),
        // 14.3.2 `VariableStatement : var VariableDeclarationList[+In] ;`
        NodeKind::VariableStatement => {
            let m = list_next(a, ts, ks, 0, i + 1);
            is_kw(ts, i, "var"@) && ks.len() > 0 && (forall|k: int|
                0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::VariableDeclaration)
                && dsep(a, ts, n, ks, 0, cxt, i + 1, m, false) && semi(ts, m, j, false)
        },
        // 14.3.2 as the head of a `for ( var ... )`, `[?In]`.
        NodeKind::VariableDeclarationList => is_kw(ts, i, "var"@) && ks.len() > 0 && (forall|k: int|
            0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::VariableDeclaration)
            && dsep(a, ts, n, ks, 0, cx, i + 1, j, false),
        // 14.3.2 `VariableDeclaration : BindingIdentifier Initializer? | BindingPattern Initializer`.
        NodeKind::VariableDeclaration => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_binding_target_kind(kd(a, k0)) && i < m && dc(a, ts, n, k0, cx, i, m)
                && d_init(a, ts, n, k1, cx, m, j, is_binding_pattern_kind(kd(a, k0)))
        },
        // 14.3.1 `LexicalDeclaration : LetOrConst BindingList ;`
        NodeKind::LexicalDeclaration => {
            let m = list_next(a, ts, ks, 0, i + 1);
            (if nd.op == Op::Let {
                is_kw(ts, i, "let"@)
            } else {
                nd.op == Op::Const && is_kw(ts, i, "const"@)
            }) && ks.len() > 0 && (forall|k: int|
                0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::LexicalBinding)
                && dsep(a, ts, n, ks, 0, cx, i + 1, m, false) && semi(ts, m, j, false)
        },
        // 14.3.1 `LexicalBinding : BindingIdentifier Initializer? | BindingPattern Initializer`.
        NodeKind::LexicalBinding => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_binding_target_kind(kd(a, k0)) && i < m && dc(a, ts, n, k0, cx, i, m)
                && d_init(a, ts, n, k1, cx, m, j, is_binding_pattern_kind(kd(a, k0)))
        },
        // 14.4 `EmptyStatement : ;`: a real `;` (12.10.1 rule 4: never an inserted one).
        NodeKind::EmptyStatement => ks.len() == 0 && j == i + 1 && is_p(ts, i, ";"@),
        // 14.5 `ExpressionStatement : [lookahead ∉ { {, function, async [no LineTerminator
        // here] function, class, let [ }] Expression[+In] ;`
        NodeKind::ExpressionStatement => {
            let m = ed(a, ts, k0, i);
            ks.len() == 1 && !is_p(ts, i, "{"@) && !is_kw(ts, i, "function"@) && !is_kw(
                ts,
                i,
                "class"@,
            ) && !(is_kw(ts, i, "async"@) && is_kw(ts, i + 1, "function"@) && !nl(ts, i + 1))
                && !(is_kw(ts, i, "let"@) && is_p(ts, i + 1, "["@)) && lvl(a, k0) >= -1 && i < m
                && dc(a, ts, n, k0, cxt, i, m) && semi(ts, m, j, false)
        },
        // 14.6 `IfStatement : if ( Expression[+In] ) Statement else Statement | if ( Expression[+In] ) Statement`;
        // Annex B.3.3: a `FunctionDeclaration` in place of each `Statement`.
        NodeKind::IfStatement => {
            let m = ed(a, ts, k0, i + 2);
            let q = ed(a, ts, k1, m + 1);
            ks.len() == 3 && is_kw(ts, i, "if"@) && is_p(ts, i + 1, "("@) && lvl(a, k0) >= -1
                && is_stmt_or_function(a, k1) && dc(a, ts, n, k0, cxt, i + 2, m) && is_p(ts, m, ")"@)
                && dc(a, ts, n, k1, cx, m + 1, q) && ((kd(a, k2) == NodeKind::Absent && j == q && dc(
                a,
                ts,
                n,
                k2,
                cx,
                q,
                q,
            )) || (is_kw(ts, q, "else"@) && is_stmt_or_function(a, k2) && dc(
                a,
                ts,
                n,
                k2,
                cx,
                q + 1,
                j,
            )))
        },
        // 14.7.2 `do Statement while ( Expression[+In] ) ;`, with §12.10.1 rule 1, third condition.
        NodeKind::DoWhileStatement => {
            let m = ed(a, ts, k0, i + 1);
            let q = ed(a, ts, k1, m + 2);
            ks.len() == 2 && is_kw(ts, i, "do"@) && is_statement_kind(kd(a, k0)) && lvl(a, k1) >= -1
                && dc(a, ts, n, k0, cx, i + 1, m) && is_kw(ts, m, "while"@) && is_p(ts, m + 1, "("@)
                && dc(a, ts, n, k1, cxt, m + 2, q) && is_p(ts, q, ")"@) && semi(ts, q + 1, j, true)
        },
        // 14.7.3 `while ( Expression[+In] ) Statement`.
        NodeKind::WhileStatement => {
            let m = ed(a, ts, k0, i + 2);
            ks.len() == 2 && is_kw(ts, i, "while"@) && is_p(ts, i + 1, "("@) && lvl(a, k0) >= -1
                && is_statement_kind(kd(a, k1)) && dc(a, ts, n, k0, cxt, i + 2, m) && is_p(
                ts,
                m,
                ")"@,
            ) && dc(a, ts, n, k1, cx, m + 1, j)
        },
        // 14.7.4 `for ( Expression[~In]? ; Expression[+In]? ; Expression[+In]? ) Statement`,
        // `for ( var VariableDeclarationList[~In] ; ... )` and
        // `for ( LexicalDeclaration[~In] Expression[+In]? ; Expression[+In]? ) Statement`.
        NodeKind::ForStatement => {
            let p0 = for_init_next(a, ts, k0, i + 2);
            let q = ed(a, ts, k1, p0);
            let r = ed(a, ts, k2, q + 1);
            ks.len() == 4 && is_kw(ts, i, "for"@) && is_p(ts, i + 1, "("@) && is_statement_kind(
                kd(a, k3),
            ) && for_init_ok(a, ts, n, k0, cx, i + 2) && opt_expr(a, k1) && dc(
                a,
                ts,
                n,
                k1,
                cxt,
                p0,
                q,
            ) && is_p(ts, q, ";"@) && opt_expr(a, k2) && dc(a, ts, n, k2, cxt, q + 1, r) && is_p(
                ts,
                r,
                ")"@,
            ) && dc(a, ts, n, k3, cx, r + 1, j)
        },
        // 14.7.5 `for ( [lookahead ≠ let [] LeftHandSideExpression in Expression[+In] ) Statement`,
        // `for ( var ForBinding in ... )`, `for ( ForDeclaration in ... )`, and Annex B.3.5
        // `for ( var BindingIdentifier Initializer in Expression ) Statement`.
        NodeKind::ForInStatement => {
            let m = ed(a, ts, k0, i + 2);
            let q = ed(a, ts, k1, m + 1);
            ks.len() == 3 && is_kw(ts, i, "for"@) && is_p(ts, i + 1, "("@) && for_head_ok(
                a,
                ts,
                k0,
                i + 2,
                false,
                false,
            ) && lvl(a, k1) >= -1 && is_statement_kind(kd(a, k2)) && dc(
                a,
                ts,
                n,
                k0,
                cx_in(cx, false),
                i + 2,
                m,
            ) && is_kw(ts, m, "in"@) && dc(a, ts, n, k1, cxt, m + 1, q) && is_p(ts, q, ")"@) && dc(
                a,
                ts,
                n,
                k2,
                cx,
                q + 1,
                j,
            )
        },
        // 14.7.5 `for ( [lookahead ∉ { let, async of }] LeftHandSideExpression of AssignmentExpression[+In] ) Statement`,
        // `for ( var ForBinding of ... )`, `for ( ForDeclaration of ... )`, and, with
        // `[+Await]`, `for await ( ... of ... )`.
        NodeKind::ForOfStatement => {
            let s = if nd.flag {
                i + 3
            } else {
                i + 2
            };
            let m = ed(a, ts, k0, s);
            let q = ed(a, ts, k1, m + 1);
            ks.len() == 3 && is_kw(ts, i, "for"@) && (nd.flag ==> (cx.await_ && is_kw(
                ts,
                i + 1,
                "await"@,
            ))) && is_p(ts, s - 1, "("@) && for_head_ok(a, ts, k0, s, true, nd.flag)
                && first_kid_kind(a, k0) != NodeKind::VariableDeclaration && is_assign_expr(a, k1)
                && is_statement_kind(kd(a, k2)) && dc(a, ts, n, k0, cx_in(cx, false), s, m) && is_kw(
                ts,
                m,
                "of"@,
            ) && dc(a, ts, n, k1, cxt, m + 1, q) && is_p(ts, q, ")"@) && dc(a, ts, n, k2, cx, q + 1, j)
        },
        // 14.7.5 `ForDeclaration : LetOrConst ForBinding`, `for ( var ForBinding`.
        NodeKind::ForDeclaration => ks.len() == 1 && (if nd.op == Op::Var {
            is_kw(ts, i, "var"@)
        } else if nd.op == Op::Let {
            is_kw(ts, i, "let"@)
        } else {
            nd.op == Op::Const && is_kw(ts, i, "const"@)
        }) && (is_binding_target_kind(kd(a, k0)) || (nd.op == Op::Var && kd(a, k0)
            == NodeKind::VariableDeclaration)) && dc(a, ts, n, k0, cx, i + 1, j),
        // 14.8 `continue ;` and `continue [no LineTerminator here] LabelIdentifier ;`
        NodeKind::ContinueStatement => ks.len() == 1 && is_kw(ts, i, "continue"@) && (if kd(a, k0)
            == NodeKind::LabelIdentifier {
            !nl(ts, i + 1) && dc(a, ts, n, k0, cx, i + 1, i + 2) && semi(ts, i + 2, j, false)
        } else {
            kd(a, k0) == NodeKind::Absent && dc(a, ts, n, k0, cx, i + 1, i + 1) && semi(
                ts,
                i + 1,
                j,
                false,
            )
        }),
        // 14.9 `break ;` and `break [no LineTerminator here] LabelIdentifier ;`
        NodeKind::BreakStatement => ks.len() == 1 && is_kw(ts, i, "break"@) && (if kd(a, k0)
            == NodeKind::LabelIdentifier {
            !nl(ts, i + 1) && dc(a, ts, n, k0, cx, i + 1, i + 2) && semi(ts, i + 2, j, false)
        } else {
            kd(a, k0) == NodeKind::Absent && dc(a, ts, n, k0, cx, i + 1, i + 1) && semi(
                ts,
                i + 1,
                j,
                false,
            )
        }),
        // 14.10 `return ;` and `return [no LineTerminator here] Expression[+In] ;`, `[+Return]`.
        NodeKind::ReturnStatement => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 1 && cx.return_ && is_kw(ts, i, "return"@) && (if kd(a, k0)
                == NodeKind::Absent {
                dc(a, ts, n, k0, cx, i + 1, i + 1) && semi(ts, i + 1, j, false)
            } else {
                !nl(ts, i + 1) && lvl(a, k0) >= -1 && dc(a, ts, n, k0, cxt, i + 1, m) && semi(
                    ts,
                    m,
                    j,
                    false,
                )
            })
        },
        // 14.11 `with ( Expression[+In] ) Statement`
        NodeKind::WithStatement => {
            let m = ed(a, ts, k0, i + 2);
            ks.len() == 2 && is_kw(ts, i, "with"@) && is_p(ts, i + 1, "("@) && lvl(a, k0) >= -1
                && is_statement_kind(kd(a, k1)) && dc(a, ts, n, k0, cxt, i + 2, m) && is_p(
                ts,
                m,
                ")"@,
            ) && dc(a, ts, n, k1, cx, m + 1, j)
        },
        // 14.12 `switch ( Expression[+In] ) CaseBlock`, `CaseBlock : { CaseClauses? }`
        // and `{ CaseClauses? DefaultClause CaseClauses? }`: at most one `DefaultClause`.
        NodeKind::SwitchStatement => {
            let m = ed(a, ts, k0, i + 2);
            ks.len() >= 1 && is_kw(ts, i, "switch"@) && is_p(ts, i + 1, "("@) && lvl(a, k0) >= -1
                && all_kind2(a, ks, 1, NodeKind::CaseClause, NodeKind::DefaultClause)
                && at_most_one_default(a, ks) && dc(a, ts, n, k0, cxt, i + 2, m) && is_p(
                ts,
                m,
                ")"@,
            ) && is_p(ts, m + 1, "{"@) && is_p(ts, j - 1, "}"@) && m + 2 <= j - 1 && dl(
                a,
                ts,
                n,
                ks,
                1,
                cx,
                m + 2,
                j - 1,
            )
        },
        // 14.12 `CaseClause : case Expression[+In] : StatementList?`
        NodeKind::CaseClause => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() >= 1 && is_kw(ts, i, "case"@) && lvl(a, k0) >= -1 && (forall|k: int|
                1 <= k < ks.len() ==> is_item_kind(kd(a, #[trigger] ks[k]))) && dc(
                a,
                ts,
                n,
                k0,
                cxt,
                i + 1,
                m,
            ) && is_p(ts, m, ":"@) && dl(a, ts, n, ks, 1, cx, m + 1, j)
        },
        // 14.12 `DefaultClause : default : StatementList?`
        NodeKind::DefaultClause => is_kw(ts, i, "default"@) && is_p(ts, i + 1, ":"@) && all_items(
            a,
            ks,
        ) && dl(a, ts, n, ks, 0, cx, i + 2, j),
        // 14.13 `LabelledStatement : LabelIdentifier : LabelledItem`,
        // `LabelledItem : Statement | FunctionDeclaration`
        NodeKind::LabelledStatement => ks.len() == 2 && kd(a, k0) == NodeKind::LabelIdentifier
            && is_p(ts, i + 1, ":"@) && dc(a, ts, n, k0, cx, i, i + 1) && is_stmt_or_function(a, k1)
            && dc(a, ts, n, k1, cx, i + 2, j),
        // 14.14 `throw [no LineTerminator here] Expression[+In] ;`
        NodeKind::ThrowStatement => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 1 && is_kw(ts, i, "throw"@) && !nl(ts, i + 1) && lvl(a, k0) >= -1 && dc(
                a,
                ts,
                n,
                k0,
                cxt,
                i + 1,
                m,
            ) && semi(ts, m, j, false)
        },
        // 14.15 `TryStatement : try Block Catch | try Block Finally | try Block Catch Finally`
        NodeKind::TryStatement => {
            let m = ed(a, ts, k0, i + 1);
            let q = ed(a, ts, k1, m);
            ks.len() == 3 && is_kw(ts, i, "try"@) && kd(a, k0) == NodeKind::BlockStatement && (kd(
                a,
                k1,
            ) == NodeKind::Catch || kd(a, k1) == NodeKind::Absent) && (kd(a, k2)
                == NodeKind::Finally || kd(a, k2) == NodeKind::Absent) && (kd(a, k1)
                == NodeKind::Catch || kd(a, k2) == NodeKind::Finally) && dc(a, ts, n, k0, cx, i + 1, m)
                && dc(a, ts, n, k1, cx, m, q) && dc(a, ts, n, k2, cx, q, j)
        },
        // 14.15 `Catch : catch ( CatchParameter ) Block | catch Block`
        NodeKind::Catch => {
            let m = ed(a, ts, k0, i + 2);
            ks.len() == 2 && is_kw(ts, i, "catch"@) && kd(a, k1) == NodeKind::BlockStatement && (
            if kd(a, k0) == NodeKind::Absent {
                dc(a, ts, n, k0, cx, i + 1, i + 1) && dc(a, ts, n, k1, cx, i + 1, j)
            } else {
                is_binding_target_kind(kd(a, k0)) && is_p(ts, i + 1, "("@) && dc(a, ts, n, k0, cx, i + 2, m)
                    && is_p(ts, m, ")"@) && dc(a, ts, n, k1, cx, m + 1, j)
            })
        },
        // 14.15 `Finally : finally Block`
        NodeKind::Finally => ks.len() == 1 && is_kw(ts, i, "finally"@) && kd(a, k0)
            == NodeKind::BlockStatement && dc(a, ts, n, k0, cx, i + 1, j),
        // 14.16 `DebuggerStatement : debugger ;`
        NodeKind::DebuggerStatement => ks.len() == 0 && is_kw(ts, i, "debugger"@) && semi(
            ts,
            i + 1,
            j,
            false,
        ),
        _ => false,
    }
}

} // verus!

verus! {

/// §15.2, §15.5, §15.6, §15.8: the function-like productions, one function
/// for the eight kinds. `is_async` has `async` and no line terminator before
/// `function`; `is_gen` has `*` after it; `is_expr` is the expression form
/// (the name is optional, and has the function's own `[Yield]` and `[Await]`).
/// The parameters get `[Yield]` and `[Await]` as the kind says (`[~Yield,
/// ~Await]` for `FunctionDeclaration` and `FunctionExpression`, and so on), and
/// the body is `[+Return]`.
pub open spec fn d_function(
    a: AstV,
    ts: Stream,
    n: int,
    cx: Ctx,
    i: int,
    j: int,
    is_async: bool,
    is_gen: bool,
    is_expr: bool,
) -> bool
    decreases n, 1int, 0int, 0int,
{
    let ks = kids(a, n);
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let k2 = kid(ks, 2);
    let s = if is_async {
        i + 1
    } else {
        i
    };
    let g = s + 1;
    let nm = if is_gen {
        g + 1
    } else {
        g
    };
    let cxn = if is_expr {
        cx_fn(is_gen, is_async, false)
    } else {
        cx
    };
    let m = ed(a, ts, k0, nm);
    let q = ed(a, ts, k1, m);
    ks.len() == 3 && (!is_async || (is_kw(ts, i, "async"@) && !nl(ts, i + 1))) && is_kw(
        ts,
        s,
        "function"@,
    ) && (!is_gen || is_p(ts, g, "*"@)) && (
    // `export default function () {}` has `[+Default]`; an expression's name is optional.
    if kd(a, k0) == NodeKind::Absent {
        is_expr || cx.deflt
    } else {
        kd(a, k0) == NodeKind::BindingIdentifier
    }) && dc(a, ts, n, k0, cxn, nm, m) && kd(a, k1) == NodeKind::FormalParameters && dc(
        a,
        ts,
        n,
        k1,
        cx_fn(is_gen, is_async, false),
        m,
        q,
    ) && kd(a, k2) == NodeKind::FunctionBody && dc(a, ts, n, k2, cx_fn(is_gen, is_async, true), q, j)
}

/// §15.4 `MethodDefinition`, §15.5 `GeneratorMethod`, §15.8 `AsyncMethod`, §15.6
/// `AsyncGeneratorMethod`, with the `static` of a `ClassElement` (§15.7).
pub open spec fn d_method(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 1int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let k2 = kid(ks, 2);
    let p0 = if nd.flag {
        i + 1
    } else {
        i
    };
    // The index where the `ClassElementName` starts.
    let nm = match nd.op {
        Op::Method => p0,
        Op::Getter | Op::Setter | Op::GeneratorMethod | Op::AsyncMethod => p0 + 1,
        _ => p0 + 2,
    };
    let is_gen = nd.op == Op::GeneratorMethod || nd.op == Op::AsyncGeneratorMethod;
    let is_async = nd.op == Op::AsyncMethod || nd.op == Op::AsyncGeneratorMethod;
    let m = ed(a, ts, k0, nm);
    let q = ed(a, ts, k1, m);
    ks.len() == 3 && (!nd.flag || is_kw(ts, i, "static"@)) && (match nd.op {
        Op::Method => true,
        Op::Getter => is_kw(ts, p0, "get"@),
        Op::Setter => is_kw(ts, p0, "set"@),
        Op::GeneratorMethod => is_p(ts, p0, "*"@),
        Op::AsyncMethod => is_kw(ts, p0, "async"@) && !nl(ts, p0 + 1),
        Op::AsyncGeneratorMethod => is_kw(ts, p0, "async"@) && !nl(ts, p0 + 1) && is_p(
            ts,
            p0 + 1,
            "*"@,
        ),
        _ => false,
    }) && is_class_element_name_kind(kd(a, k0)) && kd(a, k1) == NodeKind::FormalParameters
        && kd(a, k2) == NodeKind::FunctionBody && (nd.op == Op::Getter ==> kids(a, k1).len() == 0)
        && (nd.op == Op::Setter ==> (kids(a, k1).len() == 1 && kd(a, kid(kids(a, k1), 0))
        == NodeKind::BindingElement)) && dc(a, ts, n, k0, cx, nm, m) && dc(
        a,
        ts,
        n,
        k1,
        cx_fn(is_gen, is_async, false),
        m,
        q,
    ) && dc(a, ts, n, k2, cx_fn(is_gen, is_async, true), q, j)
}

/// §15.7 `ClassDeclaration`, `ClassExpression`: `class BindingIdentifier?
/// ClassTail`, `ClassTail : ClassHeritage? { ClassBody? }`, `ClassHeritage :
/// extends LeftHandSideExpression`.
pub open spec fn d_class(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int, is_expr: bool) -> bool
    decreases n, 1int, 0int, 0int,
{
    let ks = kids(a, n);
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let k2 = kid(ks, 2);
    let m = ed(a, ts, k0, i + 1);
    let hs = if kd(a, k1) == NodeKind::Absent {
        m
    } else {
        m + 1
    };
    let h = ed(a, ts, k1, hs);
    ks.len() == 3 && is_kw(ts, i, "class"@) && kd(a, k2) == NodeKind::ClassBody && (if kd(a, k0)
        == NodeKind::Absent {
        is_expr || cx.deflt
    } else {
        kd(a, k0) == NodeKind::BindingIdentifier
    }) && dc(a, ts, n, k0, cx, i + 1, m) && (kd(a, k1) == NodeKind::Absent || (is_lhs_expr(a, k1)
        && is_kw(ts, m, "extends"@))) && dc(a, ts, n, k1, cx, hs, h) && dc(a, ts, n, k2, cx, h, j)
}

/// §15 the arms of [`d`] for functions, classes, parameters and bodies.
pub open spec fn d_func(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 3int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    match nd.kind {
        NodeKind::FunctionDeclaration => d_function(a, ts, n, cx, i, j, false, false, false),
        NodeKind::FunctionExpression => d_function(a, ts, n, cx, i, j, false, false, true),
        NodeKind::GeneratorDeclaration => d_function(a, ts, n, cx, i, j, false, true, false),
        NodeKind::GeneratorExpression => d_function(a, ts, n, cx, i, j, false, true, true),
        NodeKind::AsyncFunctionDeclaration => d_function(a, ts, n, cx, i, j, true, false, false),
        NodeKind::AsyncFunctionExpression => d_function(a, ts, n, cx, i, j, true, false, true),
        NodeKind::AsyncGeneratorDeclaration => d_function(a, ts, n, cx, i, j, true, true, false),
        NodeKind::AsyncGeneratorExpression => d_function(a, ts, n, cx, i, j, true, true, true),
        // 15.1 `FormalParameters : [empty] | FunctionRestParameter | FormalParameterList
        // | FormalParameterList , | FormalParameterList , FunctionRestParameter`
        NodeKind::FormalParameters => i + 1 < j && is_p(ts, i, "("@) && is_p(ts, j - 1, ")"@)
            && all_kind2(a, ks, 0, NodeKind::BindingElement, NodeKind::FunctionRestParameter)
            && rest_only_last(a, ks) && dsep(a, ts, n, ks, 0, cx, i + 1, j - 1, true),
        // 15.1 `FunctionRestParameter : BindingRestElement`
        NodeKind::FunctionRestParameter => ks.len() == 1 && is_p(ts, i, "..."@) && is_binding_target_kind(
            kd(a, k0),
        ) && dc(a, ts, n, k0, cx, i + 1, j),
        // 15.1 `FunctionBody : FunctionStatementList`, `{ ... }`
        NodeKind::FunctionBody => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && all_items(a, ks) && dl(a, ts, n, ks, 0, cx, i + 1, j - 1),
        // 15.3 `ArrowFunction : ArrowParameters[?Yield, ?Await] [no LineTerminator here] =>
        // ConciseBody[?In]`; `ConciseBody : [lookahead ≠ {] ExpressionBody[?In, ~Await] |
        // { FunctionBody[~Yield, ~Await] }`; `ArrowParameters : BindingIdentifier | ArrowFormalParameters`.
        NodeKind::ArrowFunction => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && (kd(a, k0) == NodeKind::BindingIdentifier || kd(a, k0)
                == NodeKind::FormalParameters) && i < m && dc(a, ts, n, k0, cx, i, m) && is_p(
                ts,
                m,
                "=>"@,
            ) && !nl(ts, m) && (if kd(a, k1) == NodeKind::FunctionBody {
                dc(a, ts, n, k1, cx_fn(false, false, true), m + 1, j)
            } else {
                is_assign_expr(a, k1) && !is_p(ts, m + 1, "{"@) && dc(
                    a,
                    ts,
                    n,
                    k1,
                    Ctx { yield_: false, await_: false, in_: cx.in_, return_: false, deflt: false },
                    m + 1,
                    j,
                )
            })
        },
        // 15.9 `AsyncArrowFunction : async [no LineTerminator here] AsyncArrowBindingIdentifier[?Yield]
        // [no LineTerminator here] => AsyncConciseBody[?In]`, `AsyncArrowHead : async [no
        // LineTerminator here] ArrowFormalParameters[~Yield, +Await]`.
        NodeKind::AsyncArrowFunction => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 2 && is_kw(ts, i, "async"@) && !nl(ts, i + 1) && (kd(a, k0)
                == NodeKind::BindingIdentifier || kd(a, k0) == NodeKind::FormalParameters) && i + 1
                < m && dc(a, ts, n, k0, if kd(a, k0) == NodeKind::BindingIdentifier {
                Ctx { yield_: cx.yield_, await_: true, in_: true, return_: false, deflt: false }
            } else {
                cx_fn(false, true, false)
            }, i + 1, m) && is_p(ts, m, "=>"@) && !nl(ts, m) && (if kd(a, k1)
                == NodeKind::FunctionBody {
                dc(a, ts, n, k1, cx_fn(false, true, true), m + 1, j)
            } else {
                is_assign_expr(a, k1) && !is_p(ts, m + 1, "{"@) && dc(
                    a,
                    ts,
                    n,
                    k1,
                    Ctx { yield_: false, await_: true, in_: cx.in_, return_: false, deflt: false },
                    m + 1,
                    j,
                )
            })
        },
        NodeKind::MethodDefinition => d_method(a, ts, n, cx, i, j),
        NodeKind::ClassDeclaration => d_class(a, ts, n, cx, i, j, false),
        NodeKind::ClassExpression => d_class(a, ts, n, cx, i, j, true),
        // 15.7 `ClassBody : ClassElementList`, `{ ... }`
        NodeKind::ClassBody => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@) && (forall|k: int|
            0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::MethodDefinition || kd(
                a,
                ks[k],
            ) == NodeKind::FieldDefinition || kd(a, ks[k]) == NodeKind::ClassStaticBlock)
            && dclass(a, ts, n, ks, 0, cx, i + 1, j - 1),
        // 15.7 `FieldDefinition : ClassElementName Initializer[+In, ?Yield, ?Await]?`,
        // `ClassElement : static? FieldDefinition ;`
        NodeKind::FieldDefinition => {
            let s = if nd.flag {
                i + 1
            } else {
                i
            };
            let m = ed(a, ts, k0, s);
            let q = if kd(a, k1) == NodeKind::Absent {
                m
            } else {
                ed(a, ts, k1, m + 1)
            };
            ks.len() == 2 && (!nd.flag || is_kw(ts, i, "static"@)) && is_class_element_name_kind(
                kd(a, k0),
            ) && s < m && dc(a, ts, n, k0, cx, s, m) && d_init(
                a,
                ts,
                n,
                k1,
                cx_in(cx, true),
                m,
                q,
                false,
            ) && semi(ts, q, j, false)
        },
        // 15.7 `ClassStaticBlock : static { ClassStaticBlockBody }`,
        // `ClassStaticBlockStatementList : StatementList[~Yield, +Await, ~Return]?`
        NodeKind::ClassStaticBlock => ks.len() == 1 && is_kw(ts, i, "static"@) && kd(a, k0)
            == NodeKind::FunctionBody && dc(
            a,
            ts,
            n,
            k0,
            Ctx { yield_: false, await_: true, in_: true, return_: false, deflt: false },
            i + 1,
            j,
        ),
        _ => false,
    }
}

} // verus!

verus! {

/// §13.15.5 and §14.3.3: the arms of [`d`] for binding patterns and assignment
/// patterns.
pub open spec fn d_pat(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 3int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let cxt = cx_in(cx, true);
    match nd.kind {
        // 14.3.3 `ObjectBindingPattern : { } | { BindingRestProperty } | { BindingPropertyList }
        // | { BindingPropertyList , BindingRestProperty? }`
        NodeKind::ObjectBindingPattern => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && all_kind2(a, ks, 0, NodeKind::BindingProperty, NodeKind::BindingRestProperty)
            && rest_only_last(a, ks) && dsep(a, ts, n, ks, 0, cx, i + 1, j - 1, true),
        // 14.3.3 `ArrayBindingPattern : [ Elision? BindingRestElement? ]`, `[ BindingElementList ]`, ...
        NodeKind::ArrayBindingPattern => i + 1 < j && is_p(ts, i, "["@) && is_p(ts, j - 1, "]"@)
            && (forall|k: int|
            0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::BindingElement || kd(
                a,
                ks[k],
            ) == NodeKind::Elision || kd(a, ks[k]) == NodeKind::BindingRestElement)
            && rest_only_last(a, ks) && darray(a, ts, n, ks, 0, cx, i + 1, j - 1),
        // 14.3.3 `BindingProperty : SingleNameBinding | PropertyName : BindingElement`
        NodeKind::BindingProperty => if nd.op == Op::Shorthand {
            ks.len() == 1 && kd(a, k0) == NodeKind::BindingElement && first_kid_kind(a, k0)
                == NodeKind::BindingIdentifier && dc(a, ts, n, k0, cx, i, j)
        } else {
            let m = ed(a, ts, k0, i);
            nd.op == Op::KeyValue && ks.len() == 2 && is_prop_name_kind(kd(a, k0)) && kd(a, k1)
                == NodeKind::BindingElement && i < m && dc(a, ts, n, k0, cx, i, m) && is_p(
                ts,
                m,
                ":"@,
            ) && dc(a, ts, n, k1, cx, m + 1, j)
        },
        // 14.3.3 `BindingElement : SingleNameBinding | BindingPattern Initializer?`,
        // `SingleNameBinding : BindingIdentifier Initializer[+In]?`
        NodeKind::BindingElement => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_binding_target_kind(kd(a, k0)) && i < m && dc(a, ts, n, k0, cx, i, m)
                && d_init(a, ts, n, k1, cxt, m, j, false)
        },
        // 14.3.3 `BindingRestElement : ... BindingIdentifier | ... BindingPattern`
        NodeKind::BindingRestElement => ks.len() == 1 && is_p(ts, i, "..."@)
            && is_binding_target_kind(kd(a, k0)) && dc(a, ts, n, k0, cx, i + 1, j),
        // 14.3.3 `BindingRestProperty : ... BindingIdentifier`
        NodeKind::BindingRestProperty => ks.len() == 1 && is_p(ts, i, "..."@) && kd(a, k0)
            == NodeKind::BindingIdentifier && dc(a, ts, n, k0, cx, i + 1, j),
        // 13.15.5 `ObjectAssignmentPattern : { } | { AssignmentRestProperty } |
        // { AssignmentPropertyList } | { AssignmentPropertyList , AssignmentRestProperty? }`
        NodeKind::ObjectAssignmentPattern => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && all_kind2(a, ks, 0, NodeKind::AssignmentProperty, NodeKind::AssignmentRestProperty)
            && rest_only_last(a, ks) && dsep(a, ts, n, ks, 0, cx, i + 1, j - 1, true),
        // 13.15.5 `ArrayAssignmentPattern : [ Elision? AssignmentRestElement? ]`, ...
        NodeKind::ArrayAssignmentPattern => i + 1 < j && is_p(ts, i, "["@) && is_p(ts, j - 1, "]"@)
            && (forall|k: int|
            0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::AssignmentElement || kd(
                a,
                ks[k],
            ) == NodeKind::Elision || kd(a, ks[k]) == NodeKind::AssignmentRestElement)
            && rest_only_last(a, ks) && darray(a, ts, n, ks, 0, cx, i + 1, j - 1),
        // 13.15.5 `AssignmentProperty : IdentifierReference Initializer[+In]? |
        // PropertyName : AssignmentElement`
        NodeKind::AssignmentProperty => if nd.op == Op::Shorthand {
            ks.len() == 2 && kd(a, k0) == NodeKind::IdentifierReference && dc(a, ts, n, k0, cx, i, i + 1)
                && d_init(a, ts, n, k1, cxt, i + 1, j, false)
        } else {
            let m = ed(a, ts, k0, i);
            nd.op == Op::KeyValue && ks.len() == 2 && is_prop_name_kind(kd(a, k0)) && kd(a, k1)
                == NodeKind::AssignmentElement && i < m && dc(a, ts, n, k0, cx, i, m) && is_p(
                ts,
                m,
                ":"@,
            ) && dc(a, ts, n, k1, cx, m + 1, j)
        },
        // 13.15.5 `AssignmentElement : DestructuringAssignmentTarget Initializer[+In]?`
        NodeKind::AssignmentElement => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_destructuring_target(a, k0) && i < m && dc(a, ts, n, k0, cx, i, m)
                && d_init(a, ts, n, k1, cxt, m, j, false)
        },
        // 13.15.5 `AssignmentRestElement : ... DestructuringAssignmentTarget`
        NodeKind::AssignmentRestElement => ks.len() == 1 && is_p(ts, i, "..."@)
            && is_destructuring_target(a, k0) && dc(a, ts, n, k0, cx, i + 1, j),
        // 13.15.5 `AssignmentRestProperty : ... DestructuringAssignmentTarget`
        NodeKind::AssignmentRestProperty => ks.len() == 1 && is_p(ts, i, "..."@)
            && is_destructuring_target(a, k0) && dc(a, ts, n, k0, cx, i + 1, j),
        // 13.2.4 `Elision : ,`
        NodeKind::Elision => ks.len() == 0 && j == i + 1 && is_p(ts, i, ","@),
        _ => false,
    }
}

} // verus!

verus! {

/// §13.3.9 one link of an `OptionalChain`, starting at token `i`: `?.` (when
/// `flag`) or nothing (the link continues the chain), then the access.
pub open spec fn d_chain_link(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 1int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    // The token after the `?.`, if the link has one.
    let s = if nd.flag {
        i + 1
    } else {
        i
    };
    ks.len() == 1 && (nd.flag ==> is_p(ts, i, "?."@)) && match nd.op {
        // `OptionalChain : ?. IdentifierName | OptionalChain . IdentifierName`
        Op::ChainDot => (nd.flag || is_p(ts, i, "."@)) && kd(a, k0) == NodeKind::IdentifierName
            && j == i + 2 && dc(a, ts, n, k0, cx, i + 1, j),
        // `OptionalChain : ?. PrivateIdentifier | OptionalChain . PrivateIdentifier`
        Op::ChainPrivateDot => (nd.flag || is_p(ts, i, "."@)) && kd(a, k0)
            == NodeKind::PrivateIdentifier && j == i + 2 && dc(a, ts, n, k0, cx, i + 1, j),
        // `OptionalChain : ?. [ Expression[+In] ] | OptionalChain [ Expression[+In] ]`
        Op::ChainBracket => {
            let q = ed(a, ts, k0, s + 1);
            is_p(ts, s, "["@) && lvl(a, k0) >= -1 && dc(a, ts, n, k0, cx_in(cx, true), s + 1, q)
                && is_p(ts, q, "]"@) && j == q + 1
        },
        // `OptionalChain : ?. Arguments | OptionalChain Arguments`
        Op::ChainCall => kd(a, k0) == NodeKind::Arguments && dc(a, ts, n, k0, cx, s, j),
        // `OptionalChain : ?. TemplateLiteral[+Tagged] | OptionalChain TemplateLiteral[+Tagged]`:
        // in the grammar so that §12.10 does not apply; always a Syntax Error (13.3.1.1).
        Op::ChainTemplate => kd(a, k0) == NodeKind::TemplateLiteral && dc(a, ts, n, k0, cx, s, j),
        _ => false,
    }
}

/// §13.2, §13.3: the arms of [`d`] for primary, member, call and optional chain
/// expressions.
pub open spec fn d_expr_lhs(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 2int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let cxt = cx_in(cx, true);
    match nd.kind {
        // 13.1 `IdentifierReference`, `BindingIdentifier`, `LabelIdentifier`.
        NodeKind::IdentifierReference | NodeKind::BindingIdentifier | NodeKind::LabelIdentifier => ks.len()
            == 0 && j == i + 1 && ident_tok(ts, i, cx),
        // 12.7 `IdentifierName` as a `PropertyName`, a property access or an export/import name.
        NodeKind::IdentifierName => ks.len() == 0 && j == i + 1 && is_name(ts, i),
        // 12.7 `PrivateIdentifier`.
        NodeKind::PrivateIdentifier => ks.len() == 0 && j == i + 1 && is_kind(
            ts,
            i,
            TokKind::PrivateIdentifier,
        ),
        // 13.2.1 `PrimaryExpression : this`
        NodeKind::ThisExpression => ks.len() == 0 && j == i + 1 && is_kw(ts, i, "this"@),
        // 13.2.3 `Literal : NullLiteral | BooleanLiteral | NumericLiteral | StringLiteral`
        NodeKind::NullLiteral => ks.len() == 0 && j == i + 1 && is_kw(ts, i, "null"@),
        NodeKind::BooleanLiteral => ks.len() == 0 && j == i + 1 && (is_kw(ts, i, "true"@) || is_kw(
            ts,
            i,
            "false"@,
        )),
        NodeKind::NumericLiteral => ks.len() == 0 && j == i + 1 && is_kind(
            ts,
            i,
            TokKind::NumericLiteral,
        ),
        NodeKind::StringLiteral => ks.len() == 0 && j == i + 1 && is_kind(
            ts,
            i,
            TokKind::StringLiteral,
        ),
        // 13.2.7 `RegularExpressionLiteral`
        NodeKind::RegularExpressionLiteral => ks.len() == 0 && j == i + 1 && is_kind(
            ts,
            i,
            TokKind::RegularExpressionLiteral,
        ),
        // 13.2.8 `TemplateLiteral[Yield, Await, Tagged]`; `Expression[+In]` in each substitution.
        NodeKind::TemplateLiteral => dtemplate(a, ts, n, ks, 0, cxt, i, j),
        // 13.2.8 a template component: a token of the kinds of 12.9.6.
        NodeKind::TemplateElement => ks.len() == 0 && j == i + 1 && 0 <= i < tn(ts) && (
        ts.toks[i].kind is Template),
        // 13.2.4 `ArrayLiteral : [ Elision? ] | [ ElementList ] | [ ElementList , Elision? ]`
        NodeKind::ArrayLiteral => i + 1 < j && is_p(ts, i, "["@) && is_p(ts, j - 1, "]"@)
            && (forall|k: int|
            0 <= k < ks.len() ==> is_assign_expr(a, #[trigger] ks[k]) || kd(a, ks[k])
                == NodeKind::SpreadElement || kd(a, ks[k]) == NodeKind::Elision) && darray(
            a,
            ts,
            n,
            ks,
            0,
            cxt,
            i + 1,
            j - 1,
        ),
        // 13.2.5 `ObjectLiteral : { } | { PropertyDefinitionList } | { PropertyDefinitionList , }`
        NodeKind::ObjectLiteral => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && (forall|k: int|
            0 <= k < ks.len() ==> kd(a, #[trigger] ks[k]) == NodeKind::PropertyDefinition || kd(
                a,
                ks[k],
            ) == NodeKind::CoverInitializedName || kd(a, ks[k]) == NodeKind::MethodDefinition)
            && dsep(a, ts, n, ks, 0, cxt, i + 1, j - 1, true),
        // 13.2.5 `PropertyDefinition : IdentifierReference | PropertyName : AssignmentExpression
        // | ... AssignmentExpression` (`MethodDefinition` is its own node).
        NodeKind::PropertyDefinition => match nd.op {
            Op::Shorthand => ks.len() == 1 && kd(a, k0) == NodeKind::IdentifierReference && dc(
                a,
                ts,
                n,
                k0,
                cx,
                i,
                i + 1,
            ) && j == i + 1,
            Op::KeyValue => {
                let m = ed(a, ts, k0, i);
                ks.len() == 2 && is_prop_name_kind(kd(a, k0)) && is_assign_expr(a, k1) && i < m
                    && dc(a, ts, n, k0, cx, i, m) && is_p(ts, m, ":"@) && dc(a, ts, n, k1, cxt, m + 1, j)
            },
            Op::Spread => ks.len() == 1 && is_p(ts, i, "..."@) && is_assign_expr(a, k0) && dc(
                a,
                ts,
                n,
                k0,
                cxt,
                i + 1,
                j,
            ),
            _ => false,
        },
        // 13.2.5 `CoverInitializedName : IdentifierReference Initializer[+In]`
        NodeKind::CoverInitializedName => ks.len() == 2 && kd(a, k0) == NodeKind::IdentifierReference
            && dc(a, ts, n, k0, cx, i, i + 1) && d_init(a, ts, n, k1, cxt, i + 1, j, true),
        // 13.2.5 `ComputedPropertyName : [ AssignmentExpression[+In] ]`
        NodeKind::ComputedPropertyName => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 1 && is_p(ts, i, "["@) && is_assign_expr(a, k0) && dc(a, ts, n, k0, cxt, i + 1, m)
                && is_p(ts, m, "]"@) && j == m + 1
        },
        // 13.2.9 `ParenthesizedExpression : ( Expression[+In] )`
        NodeKind::ParenthesizedExpression => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 1 && is_p(ts, i, "("@) && lvl(a, k0) >= -1 && dc(a, ts, n, k0, cxt, i + 1, m)
                && is_p(ts, m, ")"@) && j == m + 1
        },
        // 13.3.2 `MemberExpression : MemberExpression [ Expression[+In] ]`, `. IdentifierName`,
        // `. PrivateIdentifier`, and the same for `CallExpression`.
        NodeKind::MemberExpression => {
            let m = ed(a, ts, k0, i);
            let q = ed(a, ts, k1, m + 1);
            ks.len() == 2 && is_member_or_call(a, k0) && i < m && dc(a, ts, n, k0, cx, i, m) && match nd.op {
                Op::Dot => is_p(ts, m, "."@) && kd(a, k1) == NodeKind::IdentifierName && j == m + 2
                    && dc(a, ts, n, k1, cx, m + 1, j),
                Op::PrivateDot => is_p(ts, m, "."@) && kd(a, k1) == NodeKind::PrivateIdentifier && j
                    == m + 2 && dc(a, ts, n, k1, cx, m + 1, j),
                Op::Bracket => is_p(ts, m, "["@) && lvl(a, k1) >= -1 && dc(a, ts, n, k1, cxt, m + 1, q)
                    && is_p(ts, q, "]"@) && j == q + 1,
                _ => false,
            }
        },
        // 13.3.7 `SuperProperty : super [ Expression[+In] ] | super . IdentifierName`
        NodeKind::SuperProperty => {
            let q = ed(a, ts, k0, i + 2);
            ks.len() == 1 && is_kw(ts, i, "super"@) && match nd.op {
                Op::Dot => is_p(ts, i + 1, "."@) && kd(a, k0) == NodeKind::IdentifierName && j == i + 3
                    && dc(a, ts, n, k0, cx, i + 2, j),
                Op::Bracket => is_p(ts, i + 1, "["@) && lvl(a, k0) >= -1 && dc(a, ts, n, k0, cxt, i + 2, q)
                    && is_p(ts, q, "]"@) && j == q + 1,
                _ => false,
            }
        },
        // 13.3.7 `SuperCall : super Arguments`
        NodeKind::SuperCall => ks.len() == 1 && is_kw(ts, i, "super"@) && kd(a, k0)
            == NodeKind::Arguments && dc(a, ts, n, k0, cx, i + 1, j),
        // 13.3.10 `ImportCall : import ( AssignmentExpression[+In] ,? )` and
        // `import ( AssignmentExpression[+In] , AssignmentExpression[+In] ,? )`
        NodeKind::ImportCall => {
            let m = ed(a, ts, k0, i + 2);
            let q = ed(a, ts, k1, m + 1);
            ks.len() == 2 && is_kw(ts, i, "import"@) && is_p(ts, i + 1, "("@) && is_assign_expr(a, k0)
                && dc(a, ts, n, k0, cxt, i + 2, m) && (if kd(a, k1) == NodeKind::Absent {
                dc(a, ts, n, k1, cxt, m, m) && ((is_p(ts, m, ")"@) && j == m + 1) || (is_p(
                    ts,
                    m,
                    ","@,
                ) && is_p(ts, m + 1, ")"@) && j == m + 2))
            } else {
                is_assign_expr(a, k1) && is_p(ts, m, ","@) && dc(a, ts, n, k1, cxt, m + 1, q) && ((is_p(
                    ts,
                    q,
                    ")"@,
                ) && j == q + 1) || (is_p(ts, q, ","@) && is_p(ts, q + 1, ")"@) && j == q + 2))
            })
        },
        // 13.3.12 `ImportMeta : import . meta`
        NodeKind::ImportMeta => ks.len() == 0 && j == i + 3 && is_kw(ts, i, "import"@) && is_p(
            ts,
            i + 1,
            "."@,
        ) && is_kw(ts, i + 2, "meta"@),
        // 13.3.12 `NewTarget : new . target`
        NodeKind::NewTarget => ks.len() == 0 && j == i + 3 && is_kw(ts, i, "new"@) && is_p(
            ts,
            i + 1,
            "."@,
        ) && is_kw(ts, i + 2, "target"@),
        // 13.3.5 `NewExpression : new NewExpression`, `MemberExpression : new MemberExpression Arguments`
        NodeKind::NewExpression => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 2 && is_kw(ts, i, "new"@) && i + 1 < m && dc(a, ts, n, k0, cx, i + 1, m) && (
            if kd(a, k1) == NodeKind::Absent {
                (lvl(a, k0) == 16 || lvl(a, k0) == 17) && j == m && dc(a, ts, n, k1, cx, m, m)
            } else {
                lvl(a, k0) == 17 && kd(a, k1) == NodeKind::Arguments && dc(a, ts, n, k1, cx, m, j)
            })
        },
        // 13.3.6 `CallExpression : MemberExpression Arguments | CallExpression Arguments`
        NodeKind::CallExpression => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_member_or_call(a, k0) && kd(a, k1) == NodeKind::Arguments && i < m
                && dc(a, ts, n, k0, cx, i, m) && dc(a, ts, n, k1, cx, m, j)
        },
        // 13.3.8 `Arguments : ( ) | ( ArgumentList ) | ( ArgumentList , )`
        NodeKind::Arguments => i + 1 < j && is_p(ts, i, "("@) && is_p(ts, j - 1, ")"@) && all_args(
            a,
            ks,
        ) && dsep(a, ts, n, ks, 0, cxt, i + 1, j - 1, true),
        // 13.3.11 `MemberExpression : MemberExpression TemplateLiteral[?Yield, ?Await, +Tagged]`,
        // and `CallExpression TemplateLiteral`
        NodeKind::TaggedTemplate => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_member_or_call(a, k0) && kd(a, k1) == NodeKind::TemplateLiteral && i
                < m && dc(a, ts, n, k0, cx, i, m) && dc(a, ts, n, k1, cx, m, j)
        },
        // 13.3.9 `OptionalExpression : MemberExpression OptionalChain | CallExpression
        // OptionalChain | OptionalExpression OptionalChain`
        NodeKind::OptionalExpression => {
            let m = ed(a, ts, k0, i);
            ks.len() >= 2 && is_member_or_call(a, k0) && all_kind2(
                a,
                ks,
                1,
                NodeKind::OptionalChain,
                NodeKind::OptionalChain,
            ) && flag_of(a, k1) && i < m && dc(a, ts, n, k0, cx, i, m) && dl(a, ts, n, ks, 1, cx, m, j)
        },
        NodeKind::OptionalChain => d_chain_link(a, ts, n, cx, i, j),
        _ => false,
    }
}

/// §13.4 to §13.16, §15.5.1 and §15.8.1: the arms of [`d`] for the operators.
pub open spec fn d_expr(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 3int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let k2 = kid(ks, 2);
    let cxt = cx_in(cx, true);
    d_expr_lhs(a, ts, n, cx, i, j) || match nd.kind {
        // An optional symbol that is not there.
        NodeKind::Absent => ks.len() == 0 && i == j,
        // 13.4 `UpdateExpression : LeftHandSideExpression [no LineTerminator here] ++ | -- ...`,
        // `++ UnaryExpression | -- UnaryExpression`
        NodeKind::UpdateExpression => {
            let m = ed(a, ts, k0, i);
            ks.len() == 1 && (if nd.op == Op::PostfixIncrement || nd.op == Op::PostfixDecrement {
                is_lhs_expr(a, k0) && i < m && dc(a, ts, n, k0, cx, i, m) && is_op_tok(ts, m, nd.op)
                    && !nl(ts, m) && j == m + 1
            } else {
                (nd.op == Op::PrefixIncrement || nd.op == Op::PrefixDecrement) && is_op_tok(
                    ts,
                    i,
                    nd.op,
                ) && lvl(a, k0) >= 12 && dc(a, ts, n, k0, cx, i + 1, j)
            })
        },
        // 13.5 `UnaryExpression : delete | void | typeof | + | - | ~ | ! UnaryExpression`
        NodeKind::UnaryExpression => ks.len() == 1 && is_unary_op(nd.op) && is_op_tok(ts, i, nd.op)
            && lvl(a, k0) >= 12 && dc(a, ts, n, k0, cx, i + 1, j),
        // 15.8 `UnaryExpression : [+Await] AwaitExpression`, `AwaitExpression : await UnaryExpression`
        NodeKind::AwaitExpression => ks.len() == 1 && cx.await_ && is_kw(ts, i, "await"@) && lvl(
            a,
            k0,
        ) >= 12 && dc(a, ts, n, k0, cx, i + 1, j),
        // 13.6 to 13.13: the binary operators; `in` only with `[+In]` (13.10).
        NodeKind::ExponentiationExpression | NodeKind::MultiplicativeExpression
        | NodeKind::AdditiveExpression | NodeKind::ShiftExpression | NodeKind::RelationalExpression
        | NodeKind::EqualityExpression | NodeKind::BitwiseANDExpression
        | NodeKind::BitwiseXORExpression | NodeKind::BitwiseORExpression
        | NodeKind::LogicalANDExpression | NodeKind::LogicalORExpression
        | NodeKind::CoalesceExpression => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && bin_op_ok(nd.kind, nd.op) && (nd.op == Op::In ==> cx.in_)
                && binary_operands_ok(a, nd.kind, nd.op, k0, k1) && i < m && dc(a, ts, n, k0, cx, i, m)
                && is_op_tok(ts, m, nd.op) && dc(a, ts, n, k1, cx, m + 1, j)
        },
        // 13.14 `ConditionalExpression : ShortCircuitExpression ? AssignmentExpression[+In] :
        // AssignmentExpression`
        NodeKind::ConditionalExpression => {
            let m = ed(a, ts, k0, i);
            let q = ed(a, ts, k1, m + 1);
            ks.len() == 3 && (lvl(a, k0) >= 1 || kd(a, k0) == NodeKind::CoalesceExpression)
                && is_assign_expr(a, k1) && is_assign_expr(a, k2) && i < m && dc(a, ts, n, k0, cx, i, m)
                && is_p(ts, m, "?"@) && dc(a, ts, n, k1, cxt, m + 1, q) && is_p(ts, q, ":"@) && dc(
                a,
                ts,
                n,
                k2,
                cx,
                q + 1,
                j,
            )
        },
        // 13.15 `AssignmentExpression : LeftHandSideExpression = AssignmentExpression |
        // LeftHandSideExpression AssignmentOperator AssignmentExpression | ...`; for `=` the
        // target may be an `AssignmentPattern` (13.15.5).
        NodeKind::AssignmentExpression => {
            let m = ed(a, ts, k0, i);
            ks.len() == 2 && is_assign_op(nd.op) && (if nd.op == Op::Assign {
                is_destructuring_target(a, k0)
            } else {
                is_lhs_expr(a, k0)
            }) && is_assign_expr(a, k1) && i < m && dc(a, ts, n, k0, cx, i, m) && is_op_tok(
                ts,
                m,
                nd.op,
            ) && dc(a, ts, n, k1, cx, m + 1, j)
        },
        // 15.5 `YieldExpression : yield | yield [no LineTerminator here] AssignmentExpression |
        // yield [no LineTerminator here] * AssignmentExpression`, `[+Yield]`
        NodeKind::YieldExpression => ks.len() == 1 && cx.yield_ && is_kw(ts, i, "yield"@) && (
        if nd.op == Op::YieldPlain {
            if kd(a, k0) == NodeKind::Absent {
                j == i + 1 && dc(a, ts, n, k0, cx, i + 1, i + 1)
            } else {
                !nl(ts, i + 1) && is_assign_expr(a, k0) && dc(a, ts, n, k0, cx, i + 1, j)
            }
        } else {
            nd.op == Op::YieldDelegate && !nl(ts, i + 1) && is_p(ts, i + 1, "*"@) && is_assign_expr(
                a,
                k0,
            ) && dc(a, ts, n, k0, cx, i + 2, j)
        }),
        // 13.16 `Expression : AssignmentExpression | Expression , AssignmentExpression`
        NodeKind::Expression => ks.len() >= 2 && (forall|k: int|
            0 <= k < ks.len() ==> is_assign_expr(a, #[trigger] ks[k])) && dsep(
            a,
            ts,
            n,
            ks,
            0,
            cx,
            i,
            j,
            false,
        ),
        // 13.2.4, 13.3.8 `SpreadElement : ... AssignmentExpression[+In]`
        NodeKind::SpreadElement => ks.len() == 1 && is_p(ts, i, "..."@) && is_assign_expr(a, k0) && dc(
            a,
            ts,
            n,
            k0,
            cxt,
            i + 1,
            j,
        ),
        _ => false,
    }
}

} // verus!

verus! {

/// §16.2.3 `ModuleExportName : IdentifierName | StringLiteral`, and the
/// same alternatives of `AttributeKey` and `ImportSpecifier`.
pub open spec fn is_module_export_name_kind(k: NodeKind) -> bool {
    k == NodeKind::IdentifierName || k == NodeKind::StringLiteral
}

/// The optional `WithClause` child `c` starting at token `s` and ending at `r`,
/// then the `;` ending at `j`.
pub open spec fn d_with_semi(a: AstV, ts: Stream, bound: int, c: int, cx: Ctx, s: int, j: int) -> bool
    decreases bound, 1int, 0int, 0int,
{
    let r = ed(a, ts, c, s);
    (kd(a, c) == NodeKind::Absent || kd(a, c) == NodeKind::WithClause) && dc(a, ts, bound, c, cx, s, r)
        && semi(ts, r, j, false)
}

/// §16.2.2 and §16.2.3: the arms of [`d`] for imports and exports.
pub open spec fn d_module(a: AstV, ts: Stream, n: int, cx: Ctx, i: int, j: int) -> bool
    decreases n, 3int, 0int, 0int,
{
    let nd = a.nodes[n];
    let ks = nd.children;
    let k0 = kid(ks, 0);
    let k1 = kid(ks, 1);
    let k2 = kid(ks, 2);
    let cxd = Ctx { yield_: cx.yield_, await_: cx.await_, in_: cx.in_, return_: cx.return_, deflt: true };
    match nd.kind {
        // 16.2.2 `ImportDeclaration : import ImportClause FromClause WithClause? ; |
        // import ModuleSpecifier WithClause? ;`, `FromClause : from ModuleSpecifier`
        NodeKind::ImportDeclaration => {
            let m = ed(a, ts, k0, i + 1);
            ks.len() == 3 && is_kw(ts, i, "import"@) && kd(a, k1) == NodeKind::StringLiteral && (kd(
                a,
                k0,
            ) == NodeKind::Absent || kd(a, k0) == NodeKind::ImportClause) && dc(
                a,
                ts,
                n,
                k0,
                cx,
                i + 1,
                m,
            ) && (if kd(a, k0) == NodeKind::Absent {
                dc(a, ts, n, k1, cx, m, m + 1) && d_with_semi(a, ts, n, k2, cx, m + 1, j)
            } else {
                is_kw(ts, m, "from"@) && dc(a, ts, n, k1, cx, m + 1, m + 2) && d_with_semi(
                    a,
                    ts,
                    n,
                    k2,
                    cx,
                    m + 2,
                    j,
                )
            })
        },
        // 16.2.2 `ImportClause : ImportedDefaultBinding | NameSpaceImport | NamedImports |
        // ImportedDefaultBinding , NameSpaceImport | ImportedDefaultBinding , NamedImports`
        NodeKind::ImportClause => ks.len() == 2 && (kd(a, k0) == NodeKind::BindingIdentifier
            || kd(a, k0) == NodeKind::Absent) && (kd(a, k1) == NodeKind::NameSpaceImport || kd(
            a,
            k1,
        ) == NodeKind::NamedImports || kd(a, k1) == NodeKind::Absent) && (if kd(a, k1)
            == NodeKind::Absent {
            kd(a, k0) == NodeKind::BindingIdentifier && j == i + 1 && dc(a, ts, n, k0, cx, i, j)
                && dc(a, ts, n, k1, cx, j, j)
        } else if kd(a, k0) == NodeKind::Absent {
            dc(a, ts, n, k0, cx, i, i) && dc(a, ts, n, k1, cx, i, j)
        } else {
            dc(a, ts, n, k0, cx, i, i + 1) && is_p(ts, i + 1, ","@) && dc(a, ts, n, k1, cx, i + 2, j)
        }),
        // 16.2.2 `NameSpaceImport : * as ImportedBinding`
        NodeKind::NameSpaceImport => ks.len() == 1 && is_p(ts, i, "*"@) && is_kw(ts, i + 1, "as"@)
            && kd(a, k0) == NodeKind::BindingIdentifier && j == i + 3 && dc(a, ts, n, k0, cx, i + 2, j),
        // 16.2.2 `NamedImports : { } | { ImportsList } | { ImportsList , }`
        NodeKind::NamedImports => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && all_kind2(a, ks, 0, NodeKind::ImportSpecifier, NodeKind::ImportSpecifier)
            && dsep(a, ts, n, ks, 0, cx, i + 1, j - 1, true),
        // 16.2.2 `ImportSpecifier : ImportedBinding | ModuleExportName as ImportedBinding`
        NodeKind::ImportSpecifier => ks.len() == 2 && kd(a, k1) == NodeKind::BindingIdentifier && (
        if kd(a, k0) == NodeKind::Absent {
            j == i + 1 && dc(a, ts, n, k0, cx, i, i) && dc(a, ts, n, k1, cx, i, j)
        } else {
            is_module_export_name_kind(kd(a, k0)) && is_kw(ts, i + 1, "as"@) && j == i + 3 && dc(
                a,
                ts,
                n,
                k0,
                cx,
                i,
                i + 1,
            ) && dc(a, ts, n, k1, cx, i + 2, j)
        }),
        // 16.2.2 `WithClause : with { } | with { WithEntries ,? }`
        NodeKind::WithClause => i + 2 < j && is_kw(ts, i, "with"@) && is_p(ts, i + 1, "{"@) && is_p(
            ts,
            j - 1,
            "}"@,
        ) && all_kind2(a, ks, 0, NodeKind::ImportAttribute, NodeKind::ImportAttribute) && dsep(
            a,
            ts,
            n,
            ks,
            0,
            cx,
            i + 2,
            j - 1,
            true,
        ),
        // 16.2.2 `ImportAttribute : AttributeKey : StringLiteral`
        NodeKind::ImportAttribute => ks.len() == 2 && is_module_export_name_kind(kd(a, k0)) && kd(
            a,
            k1,
        ) == NodeKind::StringLiteral && is_p(ts, i + 1, ":"@) && j == i + 3 && dc(
            a,
            ts,
            n,
            k0,
            cx,
            i,
            i + 1,
        ) && dc(a, ts, n, k1, cx, i + 2, j),
        // 16.2.3 `ExportDeclaration`
        NodeKind::ExportDeclaration => is_kw(ts, i, "export"@) && match nd.op {
            // `export * FromClause WithClause? ;`
            Op::ExportAll => ks.len() == 2 && is_p(ts, i + 1, "*"@) && is_kw(ts, i + 2, "from"@)
                && kd(a, k0) == NodeKind::StringLiteral && dc(a, ts, n, k0, cx, i + 3, i + 4)
                && d_with_semi(a, ts, n, k1, cx, i + 4, j),
            // `export * as ModuleExportName FromClause WithClause? ;`
            Op::ExportAllAs => ks.len() == 3 && is_p(ts, i + 1, "*"@) && is_kw(ts, i + 2, "as"@)
                && is_module_export_name_kind(kd(a, k0)) && dc(a, ts, n, k0, cx, i + 3, i + 4)
                && is_kw(ts, i + 4, "from"@) && kd(a, k1) == NodeKind::StringLiteral && dc(
                a,
                ts,
                n,
                k1,
                cx,
                i + 5,
                i + 6,
            ) && d_with_semi(a, ts, n, k2, cx, i + 6, j),
            // `export ExportFromClause FromClause WithClause? ;` with `NamedExports`
            Op::ExportFrom => {
                let m = ed(a, ts, k0, i + 1);
                ks.len() == 3 && kd(a, k0) == NodeKind::NamedExports && kd(a, k1)
                    == NodeKind::StringLiteral && dc(a, ts, n, k0, cx, i + 1, m) && is_kw(
                    ts,
                    m,
                    "from"@,
                ) && dc(a, ts, n, k1, cx, m + 1, m + 2) && d_with_semi(a, ts, n, k2, cx, m + 2, j)
            },
            // `export NamedExports ;`
            Op::ExportNamed => {
                let m = ed(a, ts, k0, i + 1);
                ks.len() == 1 && kd(a, k0) == NodeKind::NamedExports && dc(a, ts, n, k0, cx, i + 1, m)
                    && semi(ts, m, j, false)
            },
            // `export VariableStatement[~Yield, +Await]`
            Op::ExportVar => ks.len() == 1 && kd(a, k0) == NodeKind::VariableStatement && dc(
                a,
                ts,
                n,
                k0,
                cx,
                i + 1,
                j,
            ),
            // `export Declaration[~Yield, +Await]`
            Op::ExportDecl => ks.len() == 1 && is_declaration_kind(kd(a, k0)) && dc(
                a,
                ts,
                n,
                k0,
                cx,
                i + 1,
                j,
            ),
            // `export default HoistableDeclaration[~Yield, +Await, +Default]`
            Op::ExportDefaultHoistable => ks.len() == 1 && is_kw(ts, i + 1, "default"@)
                && is_hoistable_kind(kd(a, k0)) && dc(a, ts, n, k0, cxd, i + 2, j),
            // `export default ClassDeclaration[~Yield, +Await, +Default]`
            Op::ExportDefaultClass => ks.len() == 1 && is_kw(ts, i + 1, "default"@) && kd(a, k0)
                == NodeKind::ClassDeclaration && dc(a, ts, n, k0, cxd, i + 2, j),
            // `export default [lookahead ∉ { function, async [no LineTerminator here] function,
            // class }] AssignmentExpression[+In, ~Yield, +Await] ;`
            Op::ExportDefaultExpression => {
                let m = ed(a, ts, k0, i + 2);
                ks.len() == 1 && is_kw(ts, i + 1, "default"@) && !is_kw(ts, i + 2, "function"@) && !(
                is_kw(ts, i + 2, "async"@) && is_kw(ts, i + 3, "function"@) && !nl(ts, i + 3))
                    && !is_kw(ts, i + 2, "class"@) && is_assign_expr(a, k0) && dc(
                    a,
                    ts,
                    n,
                    k0,
                    cx_in(cx, true),
                    i + 2,
                    m,
                ) && semi(ts, m, j, false)
            },
            _ => false,
        },
        // 16.2.3 `NamedExports : { } | { ExportsList } | { ExportsList , }`
        NodeKind::NamedExports => i + 1 < j && is_p(ts, i, "{"@) && is_p(ts, j - 1, "}"@)
            && all_kind2(a, ks, 0, NodeKind::ExportSpecifier, NodeKind::ExportSpecifier)
            && dsep(a, ts, n, ks, 0, cx, i + 1, j - 1, true),
        // 16.2.3 `ExportSpecifier : ModuleExportName | ModuleExportName as ModuleExportName`
        NodeKind::ExportSpecifier => ks.len() == 2 && is_module_export_name_kind(kd(a, k0)) && dc(
            a,
            ts,
            n,
            k0,
            cx,
            i,
            i + 1,
        ) && (if kd(a, k1) == NodeKind::Absent {
            j == i + 1 && dc(a, ts, n, k1, cx, i + 1, i + 1)
        } else {
            is_module_export_name_kind(kd(a, k1)) && is_kw(ts, i + 1, "as"@) && j == i + 3 && dc(
                a,
                ts,
                n,
                k1,
                cx,
                i + 2,
                j,
            )
        }),
        _ => false,
    }
}

/// The context of the goal symbol: `Script : ScriptBody?` is `[~Yield, ~Await,
/// ~Return]`; `Module : ModuleBody?` is `[~Yield, +Await, ~Return]` (§16.1, §16.2).
pub open spec fn root_ctx(g: SourceGoal) -> Ctx {
    Ctx { yield_: false, await_: g == SourceGoal::Module, in_: true, return_: false, deflt: false }
}

/// `ast` is a derivation of all of the token stream `ts` from the goal symbol
/// `g`: a well-formed arena whose root derives every token.
pub open spec fn derives_root(a: AstV, ts: Stream, g: SourceGoal) -> bool {
    ast_wf(a) && kd(a, a.root) == (if g == SourceGoal::Script {
        NodeKind::Script
    } else {
        NodeKind::Module
    }) && d(a, ts, a.root, root_ctx(g), 0, tn(ts))
}

} // verus!

verus! {

// ---------------------------------------------------------------------
// §12.10 Automatic Semicolon Insertion
// ---------------------------------------------------------------------

/// `n` gaps with nothing inserted.
pub open spec fn no_gaps(n: int) -> Seq<Ins> {
    Seq::new(n as nat, |k: int| Ins::None)
}

/// The stream `ts` (with its gap before the end) is, as it stands, a whole
/// `Script` or `Module` of the grammar: the test of §12.10.1 rule 2 ("the
/// parser is unable to parse the input token stream as a single instance of
/// the goal nonterminal"), applied to what comes before the end.
pub open spec fn complete_free(ts: Stream, g: SourceGoal) -> bool {
    exists|a: AstV| derives_root(a, ts, g)
}

/// The tokens `pt`, with the gaps `pg` before each of them (and none
/// at the end), are the beginning of some sentence of the grammar without further
/// semicolon insertion: some tokens can follow them to make a whole `Script` or
/// `Module`. "A token is not allowed by any production of the grammar"
/// (§12.10.1 rule 1) is that the tokens before it and the token itself are not
/// viable.
pub open spec fn viable_free(pt: Seq<Tok>, pg: Seq<Ins>, g: SourceGoal) -> bool {
    exists|st: Seq<Tok>, a: AstV|
        pg.len() == pt.len() && #[trigger] derives_root(
            a,
            Stream { toks: pt + st, gaps: pg + no_gaps(st.len() as int + 1) },
            g,
        )
}

/// The lexer step at `pos` with `goal` is a token that can follow the tokens `pt`
/// (with the gaps `pg` before them) in a sentence of the grammar.
pub open spec fn viable_after_lexing<L: LexerSpec>(
    src: Src,
    pos: int,
    goal: LexGoal,
    pt: Seq<Tok>,
    pg: Seq<Ins>,
    g: SourceGoal,
) -> bool {
    match L::next_token(src, pos, goal) {
        LexStep::Token(t2) => viable_free(pt.push(t2), pg.push(Ins::None), g),
        _ => false,
    }
}

/// The gap before token `k` of `ts` (`k == tn(ts)`: before the end of the
/// input) holds the `;` that §12.10.1 allows, for the source text `src`:
///
/// 1. rule 1: the `;` is `Ins::Semicolon`, the token after it (the "offending
///    token") is separated from the one before by a line terminator or is `}`,
///    and none of the tokens that the code points at that position can lex
///    to, under any goal symbol, can follow what comes before, in any
///    sentence of the grammar (the stream so far, inserted `;` included);
/// 2. rule 2: it is the gap before the end of the stream, and what comes
///    before is not a whole `Script` or `Module`;
/// 3. rule 1, third condition: it is `Ins::DoWhile`, after a `)`. The grammar of [`d_stmt`]
///    accepts this one only after a `do`-`while`.
///
/// Rule 4 (a semicolon is never inserted when it would be an empty statement or
/// one of the two `;` of a `for` header) is in [`d_stmt`]: `EmptyStatement` and
/// the `for` header accept a `;` token only. No gap holds one at the start.
pub open spec fn gap_justified<L: LexerSpec>(src: Src, ts: Stream, k: int, g: SourceGoal) -> bool {
    match ts.gaps[k] {
        Ins::None => true,
        Ins::DoWhile => 0 < k && is_p(ts, k - 1, ")"@),
        Ins::Semicolon => 0 < k && if k == tn(ts) {
            !complete_free(
                Stream { toks: ts.toks, gaps: ts.gaps.subrange(0, k).push(Ins::None) },
                g,
            )
        } else {
            (ts.toks[k].nl_before || is_p(ts, k, "}"@)) && !exists|goal: LexGoal|
                #[trigger] viable_after_lexing::<L>(
                src,
                ts.toks[k - 1].end,
                goal,
                ts.toks.subrange(0, k),
                ts.gaps.subrange(0, k),
                g,
            )
        },
    }
}

/// `ts` is the token stream of `src` for the parser: a lexing of it
/// ([`lexes_as`]), with the semicolons that §12.10 inserts, each justified
/// ([`gap_justified`]).
pub open spec fn tokens_of<L: LexerSpec>(src: Src, ts: Stream, g: SourceGoal) -> bool {
    lexes_as::<L>(src, ts.toks) && ts.gaps.len() == ts.toks.len() + 1 && (forall|k: int|
        0 <= k < ts.gaps.len() ==> #[trigger] gap_justified::<L>(src, ts, k, g))
}

/// `a` is a parse of the source text `src` as `g` by the grammar: some token
/// stream of `src` ([`tokens_of`], semicolon insertion included) is derived
/// from the goal symbol with `a` as the derivation ([`derives_root`]), and
/// the spans of `a` are inside `src`. This does not include the early errors
/// ([`early_errors_ok`]); [`is_valid_parse`] does.
pub open spec fn is_parse<L: LexerSpec>(src: Src, g: SourceGoal, a: AstV) -> bool {
    exists|ts: Stream|
        tokens_of::<L>(src, ts, g) && derives_root(a, ts, g) && spans_wf(a, src.len() as int)
}

} // verus!
