//! The parser's view of the lexer: one token at a time, with the goal symbol of
//! each token chosen by the parser (ECMA-262 §12: "the syntactic grammar
//! chooses the goal symbol"). Not proof code: the proven part of the parser is
//! [`crate::check`], which the arena the parser builds must pass.

use clazel_js_lexer::api::{Next, Value};
use clazel_js_lexer::exec::next_token;
use clazel_js_lexer::spec::{ElementKind, Goal, TemplateKind};

/// A token, with what the parser reads of it.
#[derive(Clone)]
pub struct Tok {
    /// The lexer's kind of input element.
    pub kind: ElementKind,
    /// The index of its first code point.
    pub start: usize,
    /// One past its last code point.
    pub end: usize,
    /// A line terminator precedes it.
    pub nl: bool,
    /// The end of the source text (no token).
    pub eof: bool,
    /// For a punctuator, its text; for an `IdentifierName` written without
    /// escapes, the word if it is one the parser knows (a reserved or
    /// contextual word); `""` otherwise.
    pub s: &'static str,
    /// For an `IdentifierName` or `PrivateIdentifier`, its code points with
    /// the escapes resolved.
    pub name: Vec<u32>,
    /// An `IdentifierName` or `PrivateIdentifier` with a `UnicodeEscapeSequence`.
    pub escaped: bool,
    /// A `NumericLiteral` that is a BigInt.
    pub bigint: bool,
    /// A `NumericLiteral` that is legacy octal or `NonOctalDecimalIntegerLiteral`.
    pub legacy: bool,
    /// A template component with an undefined TV.
    pub invalid_escape: bool,
}

/// The words the parser compares tokens with.
const WORDS: &[&str] = &[
    "await",
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "null",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    "let",
    "static",
    "async",
    "of",
    "get",
    "set",
    "from",
    "as",
    "target",
    "meta",
    "implements",
    "interface",
    "package",
    "private",
    "protected",
    "public",
    "eval",
    "arguments",
    "constructor",
    "prototype",
    "__proto__",
];

/// The punctuators.
const PUNCTS: &[&str] = &[
    "{", "(", ")", "[", "]", ".", "...", ";", ",", "<", ">", "<=", ">=", "==", "!=", "===", "!==",
    "+", "-", "*", "%", "**", "++", "--", "<<", ">>", ">>>", "&", "|", "^", "!", "~", "&&", "||",
    "??", "?", "?.", ":", "=", "+=", "-=", "*=", "%=", "**=", "<<=", ">>=", ">>>=", "&=", "|=",
    "^=", "&&=", "||=", "??=", "=>", "/", "/=", "}",
];

/// The interned form of `text` among `table`, `""` if not there.
fn intern(text: &[u32], table: &'static [&'static str]) -> &'static str {
    for w in table {
        if name_is(text, w) {
            return w;
        }
    }
    ""
}

/// Lexes the token at `pos` with `goal`; `None` is a lexical error.
pub fn lex(src: &[u32], pos: usize, goal: Goal, html: bool) -> Option<Tok> {
    let r = next_token(src, pos, goal, html).ok()?;
    match r {
        Next::Eof { newline_before } => Some(Tok {
            kind: ElementKind::WhiteSpace,
            start: src.len(),
            end: src.len(),
            nl: newline_before,
            eof: true,
            s: "",
            name: Vec::new(),
            escaped: false,
            bigint: false,
            legacy: false,
            invalid_escape: false,
        }),
        Next::Token(t) => {
            let el = t.element;
            let text = src.get(el.start..el.end)?;
            let mut tok = Tok {
                kind: el.kind,
                start: el.start,
                end: el.end,
                nl: t.newline_before,
                eof: false,
                s: "",
                name: Vec::new(),
                escaped: false,
                bigint: false,
                legacy: false,
                invalid_escape: false,
            };
            match el.kind {
                ElementKind::Punctuator
                | ElementKind::DivPunctuator
                | ElementKind::RightBracePunctuator => tok.s = intern(text, PUNCTS),
                ElementKind::IdentifierName => {
                    if let Value::Name {
                        code_points,
                        escaped,
                    } = el.value
                    {
                        tok.escaped = escaped;
                        if !escaped {
                            tok.s = intern(text, WORDS);
                        }
                        tok.name = code_points;
                    }
                }
                ElementKind::PrivateIdentifier => {
                    if let Value::Name {
                        code_points,
                        escaped,
                    } = el.value
                    {
                        tok.escaped = escaped;
                        tok.name = code_points;
                    }
                }
                ElementKind::NumericLiteral => {
                    if let Value::Numeric { bigint, legacy } = el.value {
                        tok.bigint = bigint;
                        tok.legacy = legacy;
                    }
                }
                ElementKind::Template(_) => {
                    if let Value::Template { cooked, .. } = el.value {
                        tok.invalid_escape = cooked.is_none();
                    }
                }
                ElementKind::StringLiteral => {
                    if let Value::String { units } = el.value {
                        tok.name = units.iter().map(|u| u32::from(*u)).collect();
                    }
                    tok.legacy = has_legacy_escape(text);
                }
                _ => {}
            }
            Some(tok)
        }
    }
}

/// The source text of a `StringLiteral` holds a `LegacyOctalEscapeSequence` or
/// a `NonOctalDecimalEscapeSequence` (§12.9.4.1): `\1` to `\9`, or `\0` followed
/// by a decimal digit.
fn has_legacy_escape(text: &[u32]) -> bool {
    let digit = |c: Option<&u32>| c.is_some_and(|c| (0x30..=0x39).contains(c));
    let mut i = 0usize;
    while let Some(c) = text.get(i) {
        if *c == 0x5C {
            let n = text.get(i.saturating_add(1));
            if n.is_some_and(|n| (0x31..=0x39).contains(n)) {
                return true;
            }
            if n == Some(&0x30) && digit(text.get(i.saturating_add(2))) {
                return true;
            }
            i = i.saturating_add(2);
        } else {
            i = i.saturating_add(1);
        }
    }
    false
}

/// The resolved name `n` is a `ReservedWord` other than `yield` and `await`.
pub fn name_is_reserved_always(n: &[u32]) -> bool {
    is_reserved_always(intern(n, WORDS))
}

/// The token as the arena check ([`crate::arena_d`]) reads it.
pub fn dtok_of(t: &Tok) -> crate::arena_d::DTok {
    use crate::spec::{TemplateKind as ST, TokKind as SK};
    let kind = match t.kind {
        ElementKind::IdentifierName => SK::IdentifierName,
        ElementKind::PrivateIdentifier => SK::PrivateIdentifier,
        ElementKind::NumericLiteral => SK::NumericLiteral,
        ElementKind::StringLiteral => SK::StringLiteral,
        ElementKind::RegularExpressionLiteral => SK::RegularExpressionLiteral,
        ElementKind::Template(TemplateKind::NoSubstitution) => SK::Template(ST::NoSubstitution),
        ElementKind::Template(TemplateKind::Head) => SK::Template(ST::Head),
        ElementKind::Template(TemplateKind::Middle) => SK::Template(ST::Middle),
        ElementKind::Template(TemplateKind::Tail) => SK::Template(ST::Tail),
        _ => SK::Punctuator,
    };
    crate::arena_d::DTok {
        kind,
        start: t.start,
        end: t.end,
        nl: t.nl,
        escaped: t.escaped,
        legacy: t.legacy,
        invalid_escape: t.invalid_escape,
        name: t.name.clone(),
    }
}

impl Tok {
    /// The token is the punctuator `p`.
    pub fn is_p(&self, p: &str) -> bool {
        !self.eof && self.s == p && !matches!(self.kind, ElementKind::IdentifierName)
    }
    /// The token is the word `w` written without escapes.
    pub fn is_w(&self, w: &str) -> bool {
        !self.eof && self.s == w && matches!(self.kind, ElementKind::IdentifierName)
    }
    /// The token is an `IdentifierName`.
    pub fn is_name(&self) -> bool {
        !self.eof && matches!(self.kind, ElementKind::IdentifierName)
    }
    /// The token is a template component of kind `k`.
    pub fn is_tpl(&self, k: TemplateKind) -> bool {
        !self.eof && self.kind == ElementKind::Template(k)
    }
}

/// The words that cannot be an `Identifier` (§12.7.2), whatever the context:
/// `ReservedWord` except `yield` and `await`.
pub fn is_reserved_always(w: &str) -> bool {
    matches!(
        w,
        "break"
            | "case"
            | "catch"
            | "class"
            | "const"
            | "continue"
            | "debugger"
            | "default"
            | "delete"
            | "do"
            | "else"
            | "enum"
            | "export"
            | "extends"
            | "false"
            | "finally"
            | "for"
            | "function"
            | "if"
            | "import"
            | "in"
            | "instanceof"
            | "new"
            | "null"
            | "return"
            | "super"
            | "switch"
            | "this"
            | "throw"
            | "true"
            | "try"
            | "typeof"
            | "var"
            | "void"
            | "while"
            | "with"
    )
}

/// The resolved name `n` is the word `w`.
pub fn name_is(n: &[u32], w: &str) -> bool {
    w.len() == n.len() && w.chars().zip(n.iter()).all(|(c, t)| u32::from(c) == *t)
}

/// The resolved name `n` is a `ReservedWord`, `yield` and `await` included.
pub fn name_is_reserved(n: &[u32]) -> bool {
    let w = intern(n, WORDS);
    is_reserved_always(w) || w == "yield" || w == "await"
}

/// The resolved name `n` is a word that is reserved in strict mode code
/// (§13.1.1 and §12.7.2's list): `implements`, `interface`, `let`, `package`,
/// `private`, `protected`, `public`, `static`, `yield`.
pub fn name_is_strict_reserved(n: &[u32]) -> bool {
    matches!(
        intern(n, WORDS),
        "implements"
            | "interface"
            | "let"
            | "package"
            | "private"
            | "protected"
            | "public"
            | "static"
            | "yield"
    )
}
