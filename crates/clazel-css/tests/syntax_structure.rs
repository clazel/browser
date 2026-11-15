//! What is inside a block, checked outside the project.
//!
//! `tests/conformance_syntax.rs` takes each rule's block from a second parse by the same
//! parser (`parse_component_values`), so it never reads what the parser built inside a
//! block, and the suite it runs, written for the 2013 draft, has no nested rules. This
//! file decodes the parser's real output (`ExecOutput`'s rows, declarations and items) into
//! trees and compares them with structures written here by hand from CSS Syntax §5.4 and
//! §5.5 at the commit the specs are pinned to (`w3c/csswg-drafts`
//! `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`, `css-syntax-3/Overview.bs`). Each case
//! says which step of which algorithm decides it. Nothing is copied from what the parser
//! gave.
//!
//! The parser is a generic processor: every rule and declaration is "valid in the current
//! context", and what a grammar would reject (a `]` in a custom property, say) is for the
//! user of the parser. WPT's pages (`tests/data/wpt-css-syntax`) were written for a
//! CSSOM, so their verdicts on validity are not the parser's; what is ported is their
//! input, with the generic result that §5 gives.
//!
//! One departure from the text is read in: "consume a block's contents" returns `rules`
//! at `<}-token>` and EOF without appending `decls`, which would lose the last
//! declarations of every block. The crate specifies that `decls` goes in first, as the
//! other branches do (`docs/ERRATA.md`, "CSS Syntax §5.5.5"); the expectations below do the
//! same.

use clazel_css::parser::exec_parse::{
    ExecParsed, parse_comma_separated_component_values, parse_component_value,
    parse_component_values, parse_declaration, parse_declaration_list, parse_rule,
    parse_stylesheet_contents,
};
use clazel_css::parser::rows::{
    ExecDeclaration, ExecDeclarationKind, ExecItem, ExecItemKind, ExecRow,
};
use clazel_css::tokenizer::exec::{ExecNumber, ExecToken, next_token};

// ------------------------------------------------------------------------------------
// The trees
// ------------------------------------------------------------------------------------

/// A component value, §5.2.
#[derive(Debug, Clone, PartialEq)]
enum Val {
    Ident(String),
    AtKeyword(String),
    Hash(String, bool),
    Str(String),
    Url(String),
    Delim(char),
    /// The number token's text as the tokenizer builds it: number part, then `e` and the
    /// exponent part if there is one.
    Number(String),
    Percentage(String),
    Dimension(String, String),
    Function(String, Vec<Val>),
    /// A simple block, by its opening character.
    Block(char, Vec<Val>),
    /// A `)`, `]` or `}` token that closes nothing.
    Close(char),
    Whitespace,
    Colon,
    Semicolon,
    Comma,
    BadUrl,
    BadString,
    Cdo,
    Cdc,
    /// The parser's arrays are not what a view of them needs.
    Malformed(String),
}

/// A declaration, §5.2.
#[derive(Debug, Clone, PartialEq)]
struct Decl {
    name: String,
    value: Vec<Val>,
    important: bool,
    /// "original text", set for a custom property.
    original_text: Option<String>,
}

/// A rule, §5.2, and the nested declarations rule of "consume a qualified rule".
#[derive(Debug, Clone, PartialEq)]
enum Rule {
    /// `block` is "consume a block"'s result, `None` for a statement at-rule.
    At {
        name: String,
        prelude: Vec<Val>,
        block: Option<Vec<Item>>,
    },
    Qualified {
        prelude: Vec<Val>,
        declarations: Vec<Decl>,
        children: Vec<Rule>,
    },
    NestedDeclarations(Vec<Decl>),
    /// The parser's arrays are not what a view of them needs.
    Malformed(String),
}

/// An item of "consume a block's contents": a rule or a list of declarations.
#[derive(Debug, Clone, PartialEq)]
enum Item {
    Rule(Rule),
    Declarations(Vec<Decl>),
}

// Short ways to write the expected trees.

fn id(s: &str) -> Val {
    Val::Ident(s.to_owned())
}
fn num(s: &str) -> Val {
    Val::Number(s.to_owned())
}
fn dim(n: &str, unit: &str) -> Val {
    Val::Dimension(n.to_owned(), unit.to_owned())
}
fn func(name: &str, inner: Vec<Val>) -> Val {
    Val::Function(name.to_owned(), inner)
}
fn curly(inner: Vec<Val>) -> Val {
    Val::Block('{', inner)
}
fn delim(c: char) -> Val {
    Val::Delim(c)
}
fn ws() -> Val {
    Val::Whitespace
}
fn decl(name: &str, value: Vec<Val>) -> Decl {
    Decl {
        name: name.to_owned(),
        value,
        important: false,
        original_text: None,
    }
}
fn important(name: &str, value: Vec<Val>) -> Decl {
    Decl {
        important: true,
        ..decl(name, value)
    }
}
fn custom(name: &str, value: Vec<Val>, original: &str) -> Decl {
    Decl {
        original_text: Some(original.to_owned()),
        ..decl(name, value)
    }
}
fn qualified(prelude: Vec<Val>, declarations: Vec<Decl>, children: Vec<Rule>) -> Rule {
    Rule::Qualified {
        prelude,
        declarations,
        children,
    }
}
fn at_block(name: &str, prelude: Vec<Val>, block: Vec<Item>) -> Rule {
    Rule::At {
        name: name.to_owned(),
        prelude,
        block: Some(block),
    }
}
fn at_statement(name: &str, prelude: Vec<Val>) -> Rule {
    Rule::At {
        name: name.to_owned(),
        prelude,
        block: None,
    }
}

// ------------------------------------------------------------------------------------
// Decoding the parser's output
// ------------------------------------------------------------------------------------

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn number_text(number: &ExecNumber) -> String {
    let mut source = string(&number.number_part);
    if !number.exponent_part.is_empty() {
        source.push('e');
        source.push_str(&string(&number.exponent_part));
    }
    source
}

struct Decoder<'a> {
    parsed: &'a ExecParsed,
}

impl Decoder<'_> {
    fn rows(&self) -> &[ExecRow] {
        &self.parsed.output.rows
    }

    /// The values of rows `lo` up to `hi`, walking back as the rows link: "Every array is
    /// in post-order", and a value's `start` is the first row inside it.
    fn values(&self, lo: usize, hi: usize) -> Vec<Val> {
        let mut out = Vec::new();
        let mut k = hi;
        while k > lo {
            let last = k.saturating_sub(1);
            out.push(self.value(last));
            // A row that does not move back would loop for ever.
            let start = self.rows().get(last).map_or(lo, |row| row.start as usize);
            assert!(start <= last, "row {last} starts at {start}");
            k = start;
        }
        out.reverse();
        out
    }

    fn value(&self, k: usize) -> Val {
        let Some(row) = self.rows().get(k) else {
            return Val::Malformed(format!("no row {k}"));
        };
        let start = row.start as usize;
        match next_token(&self.parsed.text, row.pos as usize, false).0 {
            ExecToken::Ident { value } => Val::Ident(string(&value)),
            ExecToken::AtKeyword { value } => Val::AtKeyword(string(&value)),
            ExecToken::Hash { value, is_id } => Val::Hash(string(&value), is_id),
            ExecToken::String { value } => Val::Str(string(&value)),
            ExecToken::Url { value } => Val::Url(string(&value)),
            ExecToken::Delim { value } => Val::Delim(char::from_u32(value).unwrap_or('\u{FFFD}')),
            ExecToken::Number { number } => Val::Number(number_text(&number)),
            ExecToken::Percentage { number } => Val::Percentage(number_text(&number)),
            ExecToken::Dimension { number, unit } => {
                Val::Dimension(number_text(&number), string(&unit))
            }
            ExecToken::Function { value } => Val::Function(string(&value), self.values(start, k)),
            ExecToken::OpenParen => Val::Block('(', self.values(start, k)),
            ExecToken::OpenSquare => Val::Block('[', self.values(start, k)),
            ExecToken::OpenCurly => Val::Block('{', self.values(start, k)),
            ExecToken::CloseParen => Val::Close(')'),
            ExecToken::CloseSquare => Val::Close(']'),
            ExecToken::CloseCurly => Val::Close('}'),
            ExecToken::Whitespace => Val::Whitespace,
            ExecToken::Colon => Val::Colon,
            ExecToken::Semicolon => Val::Semicolon,
            ExecToken::Comma => Val::Comma,
            ExecToken::BadUrl => Val::BadUrl,
            ExecToken::BadString => Val::BadString,
            ExecToken::Cdo => Val::Cdo,
            ExecToken::Cdc => Val::Cdc,
            ExecToken::UnicodeRange { .. } => {
                Val::Malformed("unicode range in a plain read".into())
            }
            ExecToken::Eof => Val::Malformed("EOF is not a row".into()),
        }
    }

    fn declaration(&self, d: &ExecDeclaration) -> Decl {
        assert_ne!(
            d.kind,
            ExecDeclarationKind::UnicodeRange,
            "not used by this file"
        );
        let name = match next_token(&self.parsed.text, d.name_pos as usize, false).0 {
            ExecToken::Ident { value } => string(&value),
            other => format!("<not an ident: {other:?}>"),
        };
        let original_text = (d.kind == ExecDeclarationKind::Custom).then(|| {
            string(
                self.parsed
                    .text
                    .get(d.text_start as usize..d.text_end as usize)
                    .unwrap_or_default(),
            )
        });
        Decl {
            name,
            value: self.values(d.value_lo as usize, d.value_hi as usize),
            important: d.important,
            original_text,
        }
    }

    fn declarations(&self, lo: usize, hi: usize) -> Vec<Decl> {
        (lo..hi)
            .map(|i| match self.parsed.output.declarations.get(i) {
                Some(d) => self.declaration(d),
                None => decl(&format!("<no declaration {i}>"), vec![]),
            })
            .collect()
    }

    fn items_array(&self) -> &[ExecItem] {
        &self.parsed.output.items
    }

    /// The items `lo` up to `hi`, walking back as the items link.
    fn items(&self, lo: usize, hi: usize) -> Vec<Item> {
        let mut out = Vec::new();
        let mut k = hi;
        while k > lo {
            let last = k.saturating_sub(1);
            out.push(self.item(last));
            let start = self
                .items_array()
                .get(last)
                .map_or(lo, |i| i.start as usize);
            assert!(start <= last, "item {last} starts at {start}");
            k = start;
        }
        out.reverse();
        out
    }

    fn item(&self, k: usize) -> Item {
        let Some(item) = self.items_array().get(k) else {
            return Item::Rule(Rule::Malformed(format!("no item {k}")));
        };
        let prelude = || self.values(item.lo as usize, item.hi as usize);
        let name = || match next_token(&self.parsed.text, item.pos as usize, false).0 {
            ExecToken::AtKeyword { value } => string(&value),
            other => format!("<not an at-keyword: {other:?}>"),
        };
        let block = || self.items(item.start as usize, k);
        match item.kind {
            ExecItemKind::StatementAtRule => Item::Rule(Rule::At {
                name: name(),
                prelude: prelude(),
                block: None,
            }),
            ExecItemKind::BlockAtRule => Item::Rule(Rule::At {
                name: name(),
                prelude: prelude(),
                block: Some(block()),
            }),
            ExecItemKind::QualifiedRule => Item::Rule(qualified_from(prelude(), block())),
            ExecItemKind::Declarations => {
                Item::Declarations(self.declarations(item.lo as usize, item.hi as usize))
            }
        }
    }

    fn rules(&self) -> Vec<Rule> {
        let all = self.items(0, self.items_array().len());
        all.into_iter()
            .map(|item| match item {
                Item::Rule(rule) => rule,
                Item::Declarations(_) => {
                    Rule::Malformed("a stylesheet has no list of declarations".into())
                }
            })
            .collect()
    }
}

/// §5.5.3 "consume a qualified rule", the `<{-token>` branch, after "consume a block": "If
/// the first item of child rules is a list of declarations, remove it from child rules and
/// assign it to rule's declarations. If any remaining items of child rules are lists of
/// declarations, replace them with nested declarations rules."
fn qualified_from(prelude: Vec<Val>, mut block: Vec<Item>) -> Rule {
    let declarations = match block.first() {
        Some(Item::Declarations(list)) => {
            let list = list.clone();
            block.remove(0);
            list
        }
        _ => Vec::new(),
    };
    let children = block
        .into_iter()
        .map(|item| match item {
            Item::Rule(rule) => rule,
            Item::Declarations(list) => Rule::NestedDeclarations(list),
        })
        .collect();
    Rule::Qualified {
        prelude,
        declarations,
        children,
    }
}

fn stylesheet(input: &str) -> Vec<Rule> {
    let parsed = parse_stylesheet_contents(&code_points(input));
    Decoder { parsed: &parsed }.rules()
}

fn declaration_list(input: &str) -> Vec<Decl> {
    let parsed = parse_declaration_list(&code_points(input));
    let decoder = Decoder { parsed: &parsed };
    decoder.declarations(0, parsed.output.declarations.len())
}

fn component_values(input: &str) -> Vec<Val> {
    let parsed = parse_component_values(&code_points(input));
    Decoder { parsed: &parsed }.values(0, parsed.output.rows.len())
}

// ------------------------------------------------------------------------------------
// §5.4.2 "parse a stylesheet's contents" and §5.5.3 to §5.5.6, at the top and nested
// ------------------------------------------------------------------------------------

/// CSS Syntax §5.5.3 "consume a qualified rule", `<{-token>`: "If the first two
/// non-whitespace values of rule's prelude are an ident-token whose value starts with
/// "--" followed by a colon-token, then: … If nested is false, consume a block from input,
/// and return nothing." WPT `custom-property-rule-ambiguity.html`, stylesheet1 and 2.
#[test]
fn top_level_custom_property_lookalike_is_dropped_whole() {
    let want = vec![
        qualified(vec![delim('.'), id("a"), ws()], vec![], vec![]),
        qualified(vec![delim('.'), id("b"), ws()], vec![], vec![]),
    ];
    assert_eq!(
        stylesheet(".a { }\n  --x:hover { } /* Ambiguous \"rule\" */\n  .b { }\n"),
        want
    );
    // The block is consumed as a block whatever is in it: §5.5.5 on `]` finds a declaration
    // that is not, then a rule with no `{`, which stops at the `}` ("If nested is true,
    // return nothing"), so the block gives nothing and the stylesheet goes on after `}`.
    assert_eq!(
        stylesheet(".a { }\n  --x:hover { ] } /* Ambiguous \"rule\" */\n  .b { }\n"),
        want
    );
}

/// WPT `custom-property-rule-ambiguity.html`, stylesheet3. §5.5.5 "anything else": "Mark
/// input. Consume a declaration … with nested set to true": `.a { }` has a delim first, so
/// step 1 of "consume a declaration" gives "consume the remnants of a bad declaration …
/// return nothing", the mark is restored and "consume a qualified rule" reads `.a { }`.
/// `--x:hover { } .b { }` is a declaration: step 5 reads the component values up to the
/// `<}-token>` that ends `div`'s block ("If nested is true, return values"), step 7
/// removes the whitespace at the end, and step 8 gives it an original text, the source of
/// the tokens of the value, so with `{ }` and `.b { }` in it. The declarations are
/// appended to `rules` at `<}-token>` (the erratum in the module comment), so `div`'s
/// first child is a rule, it has no declarations of its own, and the list is a nested
/// declarations rule.
#[test]
fn nested_custom_property_lookalike_is_a_declaration() {
    let value = vec![
        id("hover"),
        ws(),
        curly(vec![ws()]),
        ws(),
        delim('.'),
        id("b"),
        ws(),
        curly(vec![ws()]),
    ];
    let want = vec![qualified(
        vec![id("div"), ws()],
        vec![],
        vec![
            qualified(vec![delim('.'), id("a"), ws()], vec![], vec![]),
            Rule::NestedDeclarations(vec![custom("--x", value, "hover { }\n    .b { }")]),
        ],
    )];
    assert_eq!(
        stylesheet("div {\n    .a { }\n    --x:hover { }\n    .b { }\n  }\n"),
        want
    );
}

/// WPT `custom-property-rule-ambiguity.html`, stylesheet4. The same, with a `]` in the
/// value. The generic parser has no grammar for custom properties, so the `]` is a token
/// of the value (§5.5.6 step 5: "consume a list of component values", whose `<]-token>`
/// is "anything else": "consume a component value", which returns the token), and the
/// declaration stays whole: no `.b` rule is restarted from inside it. WPT's "invalid"
/// verdict is the grammar's, `<declaration-value>` forbidding unmatched `]`.
#[test]
fn nested_custom_property_with_a_stray_bracket_stays_one_declaration() {
    let value = vec![
        id("hover"),
        ws(),
        curly(vec![ws(), Val::Close(']'), ws()]),
        ws(),
        delim('.'),
        id("b"),
        ws(),
        curly(vec![ws()]),
    ];
    let want = vec![qualified(
        vec![id("div"), ws()],
        vec![],
        vec![
            qualified(vec![delim('.'), id("a"), ws()], vec![], vec![]),
            Rule::NestedDeclarations(vec![custom("--x", value, "hover { ] }\n    .b { }")]),
        ],
    )];
    assert_eq!(
        stylesheet("div {\n    .a { }\n    --x:hover { ] }\n    .b { }\n  }\n"),
        want
    );
}

/// §5.5.3 "consume a qualified rule", `<{-token>`: the check is for "an ident-token whose
/// value starts with "--"", so a prelude that starts `-x:` is an ordinary rule.
#[test]
fn a_single_dash_is_not_a_custom_property_name() {
    let want = vec![qualified(
        vec![id("-x"), Val::Colon, id("hover"), ws()],
        vec![],
        vec![],
    )];
    assert_eq!(stylesheet("-x:hover { }"), want);
}

/// WPT `invalid-nested-rules.html`. `.a { .b <::::invalid::::> {} & .c {} }`: §5.5.5 reads
/// `.b <::::invalid::::> {}` as a declaration (step 1 fails on the delim) and then as a
/// qualified rule, which the generic parser accepts: validity is "in the current context",
/// that is the grammar's. WPT's rule that goes missing (an "invalid rule error") is the
/// grammar's too. What the parser must do, and WPT checks, is carry on after the block:
/// `& .c {}` is the next child.
#[test]
fn nested_rules_continue_after_a_block() {
    let want = vec![qualified(
        vec![delim('.'), id("a"), ws()],
        vec![],
        vec![
            qualified(
                vec![
                    delim('.'),
                    id("b"),
                    ws(),
                    delim('<'),
                    Val::Colon,
                    Val::Colon,
                    Val::Colon,
                    Val::Colon,
                    id("invalid"),
                    Val::Colon,
                    Val::Colon,
                    Val::Colon,
                    Val::Colon,
                    delim('>'),
                    ws(),
                ],
                vec![],
                vec![],
            ),
            qualified(
                vec![delim('&'), ws(), delim('.'), id("c"), ws()],
                vec![],
                vec![],
            ),
        ],
    )];
    assert_eq!(
        stylesheet(".a {\n    .b <::::invalid::::> {}\n    & .c {}\n  }\n"),
        want
    );
}

/// WPT `at-rule-in-declaration-list.html`. §5.5.5 at-keyword: "If decls is not empty,
/// append it to rules … Consume an at-rule from input, with nested set to true. If a rule
/// was returned, append it to rules." The at-rule's block is "consume a block": here
/// empty, as `@at {}` has no items; a statement one ends at `;` (§5.5.2: `<semicolon-token>`:
/// "Discard a token … return it"). The declaration after it is in a list of its own, which
/// for a qualified rule's block is a nested declarations rule, as its first child is a rule.
#[test]
fn at_rules_inside_a_style_rule() {
    for (at_rule_text, at_rule) in [
        ("@at {}", at_block("at", vec![ws()], vec![])),
        ("@at at;", at_statement("at", vec![ws(), id("at")])),
    ] {
        let want = vec![qualified(
            vec![id("div"), ws()],
            vec![],
            vec![
                at_rule,
                Rule::NestedDeclarations(vec![decl("color", vec![id("green")])]),
            ],
        )];
        let source = format!(
            "\n      div {{\n        {at_rule_text}\n        color: green;\n      }}\n    "
        );
        assert_eq!(stylesheet(&source), want, "{source:?}");
    }
}

/// The same in an at-rule, `@page`, whose block is assigned whole (§5.5.2 `<{-token>`:
/// "Consume a block from input, and assign the result to rule's child rules"), declarations
/// and all.
#[test]
fn at_rules_inside_an_at_rule() {
    let want = vec![at_block(
        "page",
        vec![ws()],
        vec![
            Item::Rule(at_block("at", vec![ws()], vec![])),
            Item::Declarations(vec![decl("margin-top", vec![dim("20", "px")])]),
        ],
    )];
    assert_eq!(
        stylesheet("@page {\n        @at {}\n        margin-top: 20px;\n      }"),
        want
    );
    let want = vec![at_block(
        "font-face",
        vec![ws()],
        vec![
            Item::Rule(at_statement("at", vec![ws(), id("at")])),
            Item::Declarations(vec![decl("font-family", vec![id("myfont")])]),
        ],
    )];
    assert_eq!(
        stylesheet("@font-face {\n        @at at;\n        font-family: myfont;\n      }"),
        want
    );
}

/// An at-rule's block holding declarations first, then a nested at-rule with its own
/// declarations and a nested qualified rule: §5.5.5 builds `rules` as lists of
/// declarations and rules in source order, at every depth.
#[test]
fn declarations_in_nested_at_rules_and_rules() {
    let want = vec![at_block(
        "media",
        vec![ws(), id("screen"), ws()],
        vec![
            Item::Declarations(vec![decl("x", vec![id("y")])]),
            Item::Rule(at_block(
                "inner",
                vec![ws()],
                vec![Item::Declarations(vec![
                    decl("d", vec![id("e")]),
                    important("f", vec![num("1")]),
                ])],
            )),
            Item::Rule(qualified(
                vec![id("a"), ws()],
                vec![decl("color", vec![id("red")])],
                vec![],
            )),
        ],
    )];
    assert_eq!(
        stylesheet("@media screen { x: y; @inner { d: e; f: 1 !important } a { color: red } }"),
        want
    );
}

/// WPT `trailing-braces.html`. In `#target1 { color:green; color:red{}; color:red {}; }`
/// §5.5.6 step 8 (the last clause of "if decl's name is a custom property name string …
/// Otherwise, if decl's value contains a top-level simple block with an associated token of
/// `<{-token>`, and also contains any other non-whitespace-token value, return nothing")
/// makes `color:red{}` and `color:red {}` no declaration, so §5.5.5 restores the mark and
/// consumes a qualified rule, with `;` as the stop token, up to the block. The `;` after
/// each is left to §5.5.5's `<semicolon-token>`. The first declaration is flushed into
/// `rules` before the first rule ("If a rule was returned: if decls is not empty, append
/// decls to rules"), so it is the first item and becomes the rule's declarations.
#[test]
fn trailing_braces_are_rules_not_declarations() {
    let want = vec![qualified(
        vec![Val::Hash("target1".into(), true), ws()],
        vec![decl("color", vec![id("green")])],
        vec![
            qualified(vec![id("color"), Val::Colon, id("red")], vec![], vec![]),
            qualified(
                vec![id("color"), Val::Colon, id("red"), ws()],
                vec![],
                vec![],
            ),
        ],
    )];
    assert_eq!(
        stylesheet("#target1 {\n    color:green;\n    color:red{};\n    color:red {};\n  }\n"),
        want
    );
}

/// `rgb(2, 2, 2)`, as §5.5.8 "consume a function" gives it: the commas and the spaces
/// are values of the function.
fn rgb_2_2_2() -> Vec<Val> {
    vec![func(
        "rgb",
        vec![
            num("2"),
            Val::Comma,
            ws(),
            num("2"),
            Val::Comma,
            ws(),
            num("2"),
        ],
    )]
}

fn rgb_1_1_1() -> Vec<Val> {
    vec![func(
        "rgb",
        vec![
            num("1"),
            Val::Comma,
            ws(),
            num("1"),
            Val::Comma,
            ws(),
            num("1"),
        ],
    )]
}

/// The `.a` rule of `var-with-blocks.html` around one declaration line `middle`: a color,
/// the line and a background colour.
fn var_sheet(middle: &str) -> Vec<Rule> {
    stylesheet(&format!(
        "\n  .a {{\n    color: rgb(2, 2, 2);\n    {middle}\n    background-color:rgb(1, 1, 1);\n  }}\n"
    ))
}

fn a_prelude() -> Vec<Val> {
    vec![delim('.'), id("a"), ws()]
}

/// WPT `var-with-blocks.html`, standard properties. A {}-block as the whole value is a
/// declaration: §5.5.6 step 8, "a top-level {}-block is only allowed as the entire value of
/// a non-custom property". All three are in one list of declarations, which is the rule's.
#[test]
fn whole_value_blocks_are_declarations() {
    let cases: [(&str, Vec<Val>); 3] = [
        ("color:var(--x);", vec![func("var", vec![id("--x")])]),
        (
            "color:{var(--x)};",
            vec![curly(vec![func("var", vec![id("--x")])])],
        ),
        (
            "color: { var(--x) };",
            vec![curly(vec![ws(), func("var", vec![id("--x")]), ws()])],
        ),
    ];
    for (line, value) in cases {
        let want = vec![qualified(
            a_prelude(),
            vec![
                decl("color", rgb_2_2_2()),
                decl("color", value),
                decl("background-color", rgb_1_1_1()),
            ],
            vec![],
        )];
        assert_eq!(var_sheet(line), want, "{line}");
    }
}

/// WPT `var-with-blocks.html`, the invalid ones: a {}-block next to any other value is not
/// a declaration (§5.5.6 step 8), so §5.5.5 restores the mark and "consume a qualified rule"
/// reads a rule up to the block, and what is left after the block is read afresh. The
/// declarations before and after are separate lists, as a rule comes between them. What
/// is left is nothing in every case: `color:{ } var(--x);` leaves `var(--x);`, for which
/// "consume a declaration" fails at step 1 and "consume a qualified rule" with `;` as the
/// stop token returns nothing at the `;` (§5.5.3: "stop token (if passed): this is a parse
/// error. Return nothing"), which §5.5.5 then discards. `color:{ var(--x) } A;` also has
/// the block's own contents: `var(--x)` is no declaration (step 1), and a rule that reaches
/// the block's `}` is "return nothing" when nested, so the block holds nothing.
#[test]
fn blocks_beside_other_values_are_rules() {
    let var_x = func("var", vec![id("--x")]);
    let cases: Vec<(&str, Vec<Val>)> = vec![
        (
            "color:var(--x) { };",
            vec![id("color"), Val::Colon, var_x, ws()],
        ),
        ("color:{ } var(--x);", vec![id("color"), Val::Colon]),
        ("color:{ var(--x) } A;", vec![id("color"), Val::Colon]),
        (
            "color:A { var(--x) };",
            vec![id("color"), Val::Colon, id("A"), ws()],
        ),
    ];
    for (line, prelude) in cases {
        let want = vec![qualified(
            a_prelude(),
            vec![decl("color", rgb_2_2_2())],
            vec![
                qualified(prelude, vec![], vec![]),
                Rule::NestedDeclarations(vec![decl("background-color", rgb_1_1_1())]),
            ],
        )];
        assert_eq!(var_sheet(line), want, "{line}");
    }
}

/// WPT `var-with-blocks.html`, custom properties: every one is valid, with its original
/// text (§5.5.6 step 8: "If decl's name is a custom property name string, then set decl's
/// original text to the segment of the original source text string corresponding to the
/// tokens of decl's value"), whose value is trimmed (steps 6 and 7) and which starts after
/// the whitespace of step 4.
#[test]
fn custom_properties_take_blocks_anywhere() {
    let var_x = func("var", vec![id("--x")]);
    let cases: Vec<(&str, Vec<Val>, &str)> = vec![
        ("--y:var(--x);", vec![var_x.clone()], "var(--x)"),
        (
            "--y:{var(--x)};",
            vec![curly(vec![var_x.clone()])],
            "{var(--x)}",
        ),
        (
            "--y: { var(--x) };",
            vec![curly(vec![ws(), var_x.clone(), ws()])],
            "{ var(--x) }",
        ),
        (
            "--y:var(--x) { };",
            vec![var_x.clone(), ws(), curly(vec![ws()])],
            "var(--x) { }",
        ),
        (
            "--y:{ } var(--x);",
            vec![curly(vec![ws()]), ws(), var_x.clone()],
            "{ } var(--x)",
        ),
        (
            "--y:{ var(--x) } A;",
            vec![curly(vec![ws(), var_x.clone(), ws()]), ws(), id("A")],
            "{ var(--x) } A",
        ),
        (
            "--y:A { var(--x) };",
            vec![id("A"), ws(), curly(vec![ws(), var_x.clone(), ws()])],
            "A { var(--x) }",
        ),
    ];
    for (line, value, original) in cases {
        let want = vec![qualified(
            a_prelude(),
            vec![
                decl("color", rgb_2_2_2()),
                custom("--y", value, original),
                decl("background-color", rgb_1_1_1()),
            ],
            vec![],
        )];
        assert_eq!(var_sheet(line), want, "{line}");
    }
}

/// WPT `declarations-trim-whitespace.html`. §5.5.6: step 2 and 4 discard whitespace after
/// the name and after the colon; step 6: "If the last two non-whitespace-tokens in decl's
/// value are a delim-token with the value "!" followed by an ident-token with a value that
/// is an ASCII case-insensitive match for "important", remove them from decl's value and
/// set decl's important flag"; step 7 removes the whitespace left at the end; so every
/// value is `bar` and its original text `bar`, and `--foo-5` to `--foo-8` are important.
/// `--foo-9` runs to the `}`, with whitespace before it.
#[test]
fn declarations_trim_whitespace() {
    let source = "\n    #foo {\n        --foo-1:bar;\n        --foo-2: bar;\n        --foo-3:bar ;\n        --foo-4: bar ;\n        --foo-5: bar !important;\n        --foo-6: bar !important ;\n        --foo-7:bar!important;\n        --foo-8:bar!important ;\n        --foo-9:bar\n    }\n    ";
    let flags = [false, false, false, false, true, true, true, true, false];
    let declarations: Vec<Decl> = flags
        .iter()
        .enumerate()
        .map(|(i, flag)| Decl {
            name: format!("--foo-{}", i.saturating_add(1)),
            value: vec![id("bar")],
            important: *flag,
            original_text: Some("bar".to_owned()),
        })
        .collect();
    let want = vec![qualified(
        vec![Val::Hash("foo".into(), true), ws()],
        declarations,
        vec![],
    )];
    assert_eq!(stylesheet(source), want);
}

/// §5.5.6 step 8, "important" with another case, and a custom property whose value is
/// only `!important`: step 6 removes "!" and "important", leaving an empty value.
#[test]
fn important_is_case_insensitive_and_can_leave_an_empty_value() {
    assert_eq!(
        declaration_list("a: b !IMPORTANT; --c: !important; d: e ! important"),
        vec![
            important("a", vec![id("b")]),
            Decl {
                name: "--c".into(),
                value: vec![],
                important: true,
                original_text: Some(String::new()),
            },
            // `!` and `important` are not the last two non-whitespace values: whitespace
            // between them does not matter ("non-whitespace-tokens"), so this one is too.
            important("d", vec![id("e")]),
        ]
    );
}

/// §5.4.5 "parse a list of declarations", which calls "consume a declaration" with nested
/// false: a `<}-token>` in a value is "parse error. Consume a token … and append" (§5.5.7
/// "consume a list of component values"), so it stays in the value, as a close-curly
/// token; and at-rules are consumed and discarded, whether they have a block or `;`.
#[test]
fn declaration_list_keeps_stray_closers_and_drops_at_rules() {
    assert_eq!(
        declaration_list("color: green; @at {} @x y; --a:b; width: 1px !important"),
        vec![
            decl("color", vec![id("green")]),
            custom("--a", vec![id("b")], "b"),
            important("width", vec![dim("1", "px")]),
        ]
    );
    assert_eq!(
        declaration_list("a: b } c: d"),
        vec![decl(
            "a",
            vec![
                id("b"),
                ws(),
                Val::Close('}'),
                ws(),
                id("c"),
                Val::Colon,
                ws(),
                id("d"),
            ]
        )]
    );
    // Step 1 or 3 fails: "consume the remnants of a bad declaration" to the `;`, which is
    // discarded; the next declaration is read afresh.
    assert_eq!(
        declaration_list("1: x; a b; c: d"),
        vec![decl("c", vec![id("d")])]
    );
}

/// §5.5.2 "consume an at-rule", `<}-token>`: "If nested is true: … return it. Otherwise,
/// consume a token and append the result to rule's prelude". At the top level the `}` is
/// in the prelude; nested it ends the at-rule, and the block that holds it too.
#[test]
fn a_close_curly_in_an_at_rule_prelude() {
    assert_eq!(
        stylesheet("@a b } c;"),
        vec![at_statement(
            "a",
            vec![ws(), id("b"), ws(), Val::Close('}'), ws(), id("c")]
        )]
    );
    // After the block `a` has ended at the `}`, the top level reads ` c: d }` as a
    // qualified rule (§5.5.3: `<}-token>` with nested false: "consume a token and append the
    // result to rule's prelude"), which reaches EOF: "Return nothing".
    assert_eq!(
        stylesheet("a { @x b } c: d }"),
        vec![qualified(
            vec![id("a"), ws()],
            vec![],
            vec![at_statement("x", vec![ws(), id("b"), ws()])],
        )]
    );
}

/// §5.5.5, a rule with a prelude that looks like a declaration (`b:hover`), and a prelude
/// that is not one (`b c;`): "consume a declaration" fails (step 8, or step 3), the mark is
/// restored, and the rule is read with `;` as the stop token.
#[test]
fn declaration_like_preludes_inside_a_block() {
    assert_eq!(
        stylesheet("a { b:hover { c:d } }"),
        vec![qualified(
            vec![id("a"), ws()],
            vec![],
            vec![qualified(
                vec![id("b"), Val::Colon, id("hover"), ws()],
                vec![decl("c", vec![id("d")])],
                vec![],
            )],
        )]
    );
    // `b c;` is nothing (the rule reaches its stop token `;`), `d { e: f }` a rule.
    assert_eq!(
        stylesheet("a { b c; d { e: f } }"),
        vec![qualified(
            vec![id("a"), ws()],
            vec![],
            vec![qualified(
                vec![id("d"), ws()],
                vec![decl("e", vec![id("f")])],
                vec![],
            )],
        )]
    );
}

/// A custom property whose value is a block with declarations in it keeps them as tokens
/// of the value (§5.5.6 step 5), not as nested items.
#[test]
fn a_custom_property_block_holds_tokens_not_items() {
    let want = vec![qualified(
        vec![id("a"), ws()],
        vec![custom(
            "--x",
            vec![curly(vec![ws(), id("b"), Val::Colon, ws(), id("c"), ws()])],
            "{ b: c }",
        )],
        vec![],
    )];
    assert_eq!(stylesheet("a { --x: { b: c } }"), want);
    // And an unclosed block, function and declaration at the end of the input are closed
    // by EOF (§5.5.7 and §5.5.8: `<EOF-token>`: "return").
    assert_eq!(
        stylesheet("a { b: f(c, [d"),
        vec![qualified(
            vec![id("a"), ws()],
            vec![decl(
                "b",
                vec![func(
                    "f",
                    vec![id("c"), Val::Comma, ws(), Val::Block('[', vec![id("d")])]
                )]
            )],
            vec![],
        )]
    );
}

/// A stylesheet's own rules: §5.5.1: `<CDO-token>` and `<CDC-token>` are discarded, an
/// at-keyword gives an at-rule, anything else a qualified rule.
#[test]
fn stylesheet_level_items() {
    assert_eq!(
        stylesheet("<!-- @a; b {} --> @c {}"),
        vec![
            at_statement("a", vec![]),
            qualified(vec![id("b"), ws()], vec![], vec![]),
            at_block("c", vec![ws()], vec![]),
        ]
    );
}

// ------------------------------------------------------------------------------------
// §5.4 the other entry points
// ------------------------------------------------------------------------------------

/// §5.4.4 "parse a rule": discard whitespace; "If input is empty, return a syntax error";
/// an at-keyword gives "consume an at-rule", else "consume a qualified rule" with "nothing
/// or an invalid rule error" a syntax error; then "discard whitespace … If input is empty,
/// return rule. Otherwise, return a syntax error."
#[test]
fn parse_a_rule() {
    let parse = |input: &str| -> Option<Rule> {
        let (parsed, found) = parse_rule(&code_points(input));
        found.then(|| {
            Decoder { parsed: &parsed }
                .rules()
                .pop()
                .unwrap_or_else(|| Rule::Malformed("found, but no rule".into()))
        })
    };
    assert_eq!(
        parse("  @media screen { a { color: red } b {} }  "),
        Some(at_block(
            "media",
            vec![ws(), id("screen"), ws()],
            vec![
                Item::Rule(qualified(
                    vec![id("a"), ws()],
                    vec![decl("color", vec![id("red")])],
                    vec![],
                )),
                Item::Rule(qualified(vec![id("b"), ws()], vec![], vec![])),
            ],
        ))
    );
    assert_eq!(parse("@a;"), Some(at_statement("a", vec![])));
    // Empty: "return a syntax error".
    assert_eq!(parse(" "), None);
    // Something after the rule: "Otherwise, return a syntax error".
    assert_eq!(parse("a {} b {}"), None);
    // "consume a qualified rule" reaches EOF: "Return nothing".
    assert_eq!(parse("a"), None);
    // A custom-property-like prelude at the top level gives nothing (§5.5.3, nested false).
    assert_eq!(parse("--x:hover { }"), None);
}

/// §5.4.5 "parse a declaration": the same shape as "parse a rule", over "consume a
/// declaration".
#[test]
fn parse_a_declaration() {
    let parse = |input: &str| -> Option<Decl> {
        let (parsed, found) = parse_declaration(&code_points(input));
        found.then(|| {
            Decoder { parsed: &parsed }
                .declarations(0, 1)
                .pop()
                .unwrap_or_else(|| decl("<found, but no declaration>", vec![]))
        })
    };
    assert_eq!(
        parse("  color : red !IMPORTANT  "),
        Some(important("color", vec![id("red")]))
    );
    assert_eq!(
        parse("--x:  a  b  !important "),
        Some(Decl {
            name: "--x".into(),
            value: vec![id("a"), ws(), id("b")],
            important: true,
            original_text: Some("a  b".into()),
        })
    );
    assert_eq!(parse("color"), None);
    assert_eq!(parse(" "), None);
    // Step 5 stops at the `;`, so input is not empty after it: "return a syntax error".
    assert_eq!(parse("a: b; c: d"), None);
    // Step 8: a {}-block with another value, for a property that is not custom.
    assert_eq!(parse("a: {} b"), None);
    assert_eq!(parse("a: {}"), Some(decl("a", vec![curly(vec![])])));
}

/// §5.4.6 "parse a component value": one value, and nothing but whitespace around it.
#[test]
fn parse_a_component_value() {
    let parse = |input: &str| -> Option<Val> {
        let (parsed, found) = parse_component_value(&code_points(input));
        found.then(|| {
            let n = parsed.output.rows.len();
            Decoder { parsed: &parsed }.value(n.saturating_sub(1))
        })
    };
    assert_eq!(
        parse("  {a [b] }  "),
        Some(curly(vec![
            id("a"),
            ws(),
            Val::Block('[', vec![id("b")]),
            ws()
        ]))
    );
    assert_eq!(parse("a b"), None);
    assert_eq!(parse(" "), None);
}

/// §5.4.7 "parse a list of component values" with unclosed constructs: §5.5.7 to §5.5.9
/// ("`<EOF-token>`: … return"), the cases of WPT `unclosed-constructs.html` (`[foo` and
/// `:nth-child(1`, whose grammars match the block alone), and a `)` inside a `[` block,
/// which is an ordinary token there (§5.5.8: only the ending token of the block's own
/// kind ends it).
#[test]
fn unclosed_constructs_are_closed_by_eof() {
    assert_eq!(
        component_values("[foo"),
        vec![Val::Block('[', vec![id("foo")])]
    );
    assert_eq!(
        component_values(":nth-child(1"),
        vec![Val::Colon, func("nth-child", vec![num("1")])]
    );
    assert_eq!(
        component_values("f(a[b{c}d)e"),
        vec![func(
            "f",
            vec![
                id("a"),
                Val::Block(
                    '[',
                    vec![
                        id("b"),
                        curly(vec![id("c")]),
                        id("d"),
                        Val::Close(')'),
                        id("e")
                    ]
                ),
            ]
        )]
    );
    // A closer with nothing open is a token of the list (§5.5.7: `<}-token>`, nested
    // false, "Consume a token … and append").
    assert_eq!(
        component_values("a ) ] } b"),
        vec![
            id("a"),
            ws(),
            Val::Close(')'),
            ws(),
            Val::Close(']'),
            ws(),
            Val::Close('}'),
            ws(),
            id("b")
        ]
    );
}

/// §5.4.8 "parse a comma-separated list of component values": "While input is not empty:
/// consume a list of component values with `<comma-token>` as the stop token, and append the
/// result to groups. Discard a token." Read literally (and so here, and in
/// `docs/ERRATA.md`), a trailing comma ends the loop with no empty group after it. Commas
/// inside functions and blocks do not split.
#[test]
fn parse_a_comma_separated_list() {
    let groups = |input: &str| -> Vec<Vec<Val>> {
        let (parsed, ranges) = parse_comma_separated_component_values(&code_points(input));
        let decoder = Decoder { parsed: &parsed };
        ranges
            .iter()
            .map(|(lo, hi)| decoder.values(*lo as usize, *hi as usize))
            .collect()
    };
    assert_eq!(groups(""), Vec::<Vec<Val>>::new());
    assert_eq!(groups("a"), vec![vec![id("a")]]);
    assert_eq!(
        groups("a, b ,c"),
        vec![vec![id("a")], vec![ws(), id("b"), ws()], vec![id("c")]]
    );
    // The `,` after the last group is discarded, and then input is empty.
    assert_eq!(groups("a,"), vec![vec![id("a")]]);
    assert_eq!(groups(","), vec![vec![]]);
    assert_eq!(groups("a,,b"), vec![vec![id("a")], vec![], vec![id("b")]]);
    // Whitespace alone is not empty input.
    assert_eq!(groups(" "), vec![vec![ws()]]);
    // Not top-level commas.
    assert_eq!(
        groups("f(a,b), [c,d] ,{e,f}"),
        vec![
            vec![func("f", vec![id("a"), Val::Comma, id("b")])],
            vec![
                ws(),
                Val::Block('[', vec![id("c"), Val::Comma, id("d")]),
                ws()
            ],
            vec![curly(vec![id("e"), Val::Comma, id("f")])],
        ]
    );
}
