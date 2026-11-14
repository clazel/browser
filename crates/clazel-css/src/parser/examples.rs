//! Concrete sheets, evaluated on the spec, each stating what the standard's text says it
//! gives. Kept apart from the theorems so that a mutant that breaks one of them does not
//! stop Verus before it checks a kill certificate here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The rules of the sheet `string`.
pub open spec fn rules(string: Seq<u32>) -> Seq<Rule> {
    parse_a_stylesheet(Input::String { string }, None).rules
}

/// The token as a component value.
pub open spec fn token(token: Token) -> ComponentValue {
    ComponentValue::Token { token }
}

/// An ident of the one code point `c`.
pub open spec fn ident(c: u32) -> ComponentValue {
    token(Token::Ident { value: seq![c] })
}

/// A declaration with no flags.
pub open spec fn declaration(name: u32, value: Seq<ComponentValue>) -> Declaration {
    Declaration { name: seq![name], value, important: false, original_text: None }
}

/// A style rule with the one-ident prelude `c`.
pub open spec fn style_rule(
    c: u32,
    declarations: Seq<Declaration>,
    child_rules: Seq<Rule>,
) -> Rule {
    Rule::QualifiedRule { prelude: seq![ident(c)], declarations, child_rules }
}

/// The declarations of the sheet's first rule.
pub open spec fn first_rule_declarations(string: Seq<u32>) -> Seq<Declaration> {
    match rules(string)[0] {
        Rule::QualifiedRule { declarations, .. } => declarations,
        _ => Seq::empty(),
    }
}

/// The prelude of the sheet's first rule.
pub open spec fn first_rule_prelude(string: Seq<u32>) -> Seq<ComponentValue> {
    match rules(string)[0] {
        Rule::QualifiedRule { prelude, .. } => prelude,
        _ => Seq::empty(),
    }
}

/// The prelude of the first child rule of the sheet's first rule.
pub open spec fn first_child_prelude(string: Seq<u32>) -> Seq<ComponentValue> {
    match rules(string)[0] {
        Rule::QualifiedRule { child_rules, .. } => match child_rules[0] {
            Rule::QualifiedRule { prelude, .. } => prelude,
            _ => Seq::empty(),
        },
        _ => Seq::empty(),
    }
}

/// How many items the sheet's first rule's block has, if it is an at-rule with a block;
/// -1 if it is an at-rule without one, and -2 if it is not an at-rule.
pub open spec fn first_at_rule_block_len(string: Seq<u32>) -> int {
    match rules(string)[0] {
        Rule::AtRule { child_rules, .. } => match child_rules {
            Some(items) => items.len() as int,
            None => -1,
        },
        _ => -2,
    }
}

/// The prelude of the sheet's first rule, if it is an at-rule.
pub open spec fn first_at_rule_prelude(string: Seq<u32>) -> Seq<ComponentValue> {
    match rules(string)[0] {
        Rule::AtRule { prelude, .. } => prelude,
        _ => Seq::empty(),
    }
}

/// `--x: /**/a b /**/ !important `.
pub open spec fn custom_declaration() -> Seq<u32> {
    seq![
        0x2Du32, 0x2D, 0x78, 0x3A, 0x20, 0x2F, 0x2A, 0x2A, 0x2F, 0x61, 0x20, 0x62, 0x20, 0x2F,
        0x2A, 0x2A, 0x2F, 0x20, 0x21, 0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74, 0x61, 0x6E, 0x74, 0x20,
    ]
}

/// `unicode-range:U+26-2f`.
pub open spec fn unicode_declaration() -> Seq<u32> {
    unicode_range_string() + seq![0x3Au32, 0x55, 0x2B, 0x32, 0x36, 0x2D, 0x32, 0x66]
}

/// `a{b:c}`: the declaration before the closing brace stays, which is the erratum in
/// [`blocks_contents_loop`].
pub proof fn lemma_example_declaration_in_a_rule()
    ensures
        rules(seq![0x61u32, 0x7B, 0x62, 0x3A, 0x63, 0x7D]) == seq![
            style_rule(0x61, seq![declaration(0x62, seq![ident(0x63)])], Seq::empty()),
        ],
{
    assert(rules(seq![0x61u32, 0x7B, 0x62, 0x3A, 0x63, 0x7D]) == seq![
        style_rule(0x61, seq![declaration(0x62, seq![ident(0x63)])], Seq::empty()),
    ]) by (compute_only);
}

/// `a{b:c;d{}e:f}`: declarations before a nested rule are the rule's, and those after it a
/// nested declarations rule.
pub proof fn lemma_example_nested_rule()
    ensures
        rules(
            seq![0x61u32, 0x7B, 0x62, 0x3A, 0x63, 0x3B, 0x64, 0x7B, 0x7D, 0x65, 0x3A, 0x66, 0x7D],
        ) == seq![
            style_rule(
                0x61,
                seq![declaration(0x62, seq![ident(0x63)])],
                seq![
                    style_rule(0x64, Seq::empty(), Seq::empty()),
                    Rule::NestedDeclarationsRule {
                        declarations: seq![declaration(0x65, seq![ident(0x66)])],
                    },
                ],
            ),
        ],
{
    assert(rules(
        seq![0x61u32, 0x7B, 0x62, 0x3A, 0x63, 0x3B, 0x64, 0x7B, 0x7D, 0x65, 0x3A, 0x66, 0x7D],
    ) == seq![
        style_rule(
            0x61,
            seq![declaration(0x62, seq![ident(0x63)])],
            seq![
                style_rule(0x64, Seq::empty(), Seq::empty()),
                Rule::NestedDeclarationsRule {
                    declarations: seq![declaration(0x65, seq![ident(0x66)])],
                },
            ],
        ),
    ]) by (compute_only);
}

/// `a{b:c{}}`: a declaration with a `{}` block and something else is reparsed as a rule.
pub proof fn lemma_example_reparsed_as_a_rule()
    ensures
        rules(seq![0x61u32, 0x7B, 0x62, 0x3A, 0x63, 0x7B, 0x7D, 0x7D]) == seq![
            style_rule(
                0x61,
                Seq::empty(),
                seq![
                    Rule::QualifiedRule {
                        prelude: seq![ident(0x62), token(Token::Colon), ident(0x63)],
                        declarations: Seq::empty(),
                        child_rules: Seq::empty(),
                    },
                ],
            ),
        ],
{
    assert(rules(seq![0x61u32, 0x7B, 0x62, 0x3A, 0x63, 0x7B, 0x7D, 0x7D]) == seq![
        style_rule(
            0x61,
            Seq::empty(),
            seq![
                Rule::QualifiedRule {
                    prelude: seq![ident(0x62), token(Token::Colon), ident(0x63)],
                    declarations: Seq::empty(),
                    child_rules: Seq::empty(),
                },
            ],
        ),
    ]) by (compute_only);
}

/// `--x:a{}b{}` at the top level: the first rule is thrown away, block and all.
pub proof fn lemma_example_custom_property_is_no_rule()
    ensures
        rules(seq![0x2Du32, 0x2D, 0x78, 0x3A, 0x61, 0x7B, 0x7D, 0x62, 0x7B, 0x7D]) == seq![
            style_rule(0x62, Seq::empty(), Seq::empty()),
        ],
{
    assert(rules(seq![0x2Du32, 0x2D, 0x78, 0x3A, 0x61, 0x7B, 0x7D, 0x62, 0x7B, 0x7D]) == seq![
        style_rule(0x62, Seq::empty(), Seq::empty()),
    ]) by (compute_only);
}

/// `--x: /**/a b /**/ !important `: the flag is set, and the original text is the value's
/// tokens and what lies between them.
pub proof fn lemma_example_original_text()
    ensures
        parse_a_declaration(
            Input::String { string: custom_declaration() },
        ) == Some(
            Declaration {
                name: seq![0x2Du32, 0x2D, 0x78],
                value: seq![ident(0x61), token(Token::Whitespace), ident(0x62)],
                important: true,
                original_text: Some(seq![0x61u32, 0x20, 0x62]),
            },
        ),
{
    assert(parse_a_declaration(
        Input::String { string: custom_declaration() },
    ) == Some(
        Declaration {
            name: seq![0x2Du32, 0x2D, 0x78],
            value: seq![ident(0x61), token(Token::Whitespace), ident(0x62)],
            important: true,
            original_text: Some(seq![0x61u32, 0x20, 0x62]),
        },
    )) by (compute_only);
}

/// `unicode-range:U+26-2f` is one token, tokenized again with unicode ranges allowed.
pub proof fn lemma_example_unicode_range()
    ensures
        parse_a_declaration(
            Input::String { string: unicode_declaration() },
        ) == Some(
            Declaration {
                name: unicode_range_string(),
                value: seq![token(Token::UnicodeRange { start: 0x26, end: 0x2F })],
                important: false,
                original_text: None,
            },
        ),
{
    assert(parse_a_declaration(
        Input::String { string: unicode_declaration() },
    ) == Some(
        Declaration {
            name: unicode_range_string(),
            value: seq![token(Token::UnicodeRange { start: 0x26, end: 0x2F })],
            important: false,
            original_text: None,
        },
    )) by (compute_only);
}

/// `(a}]b`: a simple block ends on its mirror or EOF, not on another closing token.
pub proof fn lemma_example_block_closes_on_its_mirror()
    ensures
        parse_a_component_value(
            Input::String { string: seq![0x28u32, 0x61, 0x7D, 0x5D, 0x62] },
        ) == Some(
            ComponentValue::SimpleBlock {
                associated_token: Token::OpenParen,
                value: seq![
                    ident(0x61),
                    token(Token::CloseCurly),
                    token(Token::CloseSquare),
                    ident(0x62),
                ],
            },
        ),
{
    assert(parse_a_component_value(
        Input::String { string: seq![0x28u32, 0x61, 0x7D, 0x5D, 0x62] },
    ) == Some(
        ComponentValue::SimpleBlock {
            associated_token: Token::OpenParen,
            value: seq![
                ident(0x61),
                token(Token::CloseCurly),
                token(Token::CloseSquare),
                ident(0x62),
            ],
        },
    )) by (compute_only);
}

/// The tokens of `a,(b,c),`. A list, not a string, so that a tokenizer mutant that never
/// gets past a comma cannot stop this file being evaluated.
pub open spec fn comma_list() -> Seq<ComponentValue> {
    seq![
        ident(0x61),
        token(Token::Comma),
        token(Token::OpenParen),
        ident(0x62),
        token(Token::Comma),
        ident(0x63),
        token(Token::CloseParen),
        token(Token::Comma),
    ]
}

/// `a,(b,c),` is two groups: commas count only at the top level, and nothing follows the
/// last.
pub proof fn lemma_example_comma_list()
    ensures
        parse_a_comma_separated_list_of_component_values(Input::List { list: comma_list() }).len()
            == 2,
{
    assert(parse_a_comma_separated_list_of_component_values(
        Input::List { list: comma_list() },
    ).len() == 2) by (compute_only);
}

/// `a{@b}c{}`: a nested at-rule stops at the `}` of the block around it.
pub proof fn lemma_example_nested_at_rule()
    ensures
        rules(seq![0x61u32, 0x7B, 0x40, 0x62, 0x7D, 0x63, 0x7B, 0x7D]).len() == 2,
{
    assert(rules(seq![0x61u32, 0x7B, 0x40, 0x62, 0x7D, 0x63, 0x7B, 0x7D]).len() == 2)
        by (compute_only);
}

/// `z;a:b`: bad remnants end at the semicolon, and the next declaration is read.
pub proof fn lemma_example_remnants()
    ensures
        parse_a_list_of_declarations(
            Input::String { string: seq![0x7Au32, 0x3B, 0x61, 0x3A, 0x62] },
        ).len() == 1,
{
    assert(parse_a_list_of_declarations(
        Input::String { string: seq![0x7Au32, 0x3B, 0x61, 0x3A, 0x62] },
    ).len() == 1) by (compute_only);
}

/// `<!--a{}`: a `<CDO-token>` between rules is discarded.
pub proof fn lemma_example_cdo()
    ensures
        rules(seq![0x3Cu32, 0x21, 0x2D, 0x2D, 0x61, 0x7B, 0x7D]) == seq![
            style_rule(0x61, Seq::empty(), Seq::empty()),
        ],
{
    assert(rules(seq![0x3Cu32, 0x21, 0x2D, 0x2D, 0x61, 0x7B, 0x7D]) == seq![
        style_rule(0x61, Seq::empty(), Seq::empty()),
    ]) by (compute_only);
}

/// The value of An+B in `string`.
pub open spec fn anb(string: Seq<u32>) -> Option<(int, int)> {
    a_n_plus_b(parse_a_list_of_component_values(Input::String { string }))
}

/// One input of each clause of `<a-n-plus-b>` that §6 gives an example of, and the ones it
/// calls invalid.
pub proof fn lemma_example_a_n_plus_b()
    ensures
        anb(seq![0x6Fu32, 0x64, 0x64]) == Some((2int, 1int)),
        anb(seq![0x35u32]) == Some((0int, 5int)),
        anb(seq![0x32u32, 0x6E]) == Some((2int, 0int)),
        anb(seq![0x2Bu32, 0x6E]) == Some((1int, 0int)),
        anb(seq![0x2Du32, 0x6E, 0x2B, 0x36]) == Some((-1int, 6int)),
        anb(seq![0x33u32, 0x6E, 0x2D, 0x36]) == Some((3int, -6int)),
        anb(seq![0x33u32, 0x6E, 0x20, 0x2B, 0x20, 0x31]) == Some((3int, 1int)),
        anb(seq![0x2Bu32, 0x33, 0x6E, 0x20, 0x2D, 0x20, 0x32]) == Some((3int, -2int)),
        anb(seq![0x2Du32, 0x6E, 0x2D, 0x20, 0x31]) == Some((-1int, -1int)),
        anb(seq![0x2Du32, 0x6E, 0x2D, 0x31]) == Some((-1int, -1int)),
        anb(seq![0x6Eu32, 0x2D, 0x31]) == Some((1int, -1int)),
        anb(seq![0x33u32, 0x20, 0x6E]) == None::<(int, int)>,
        anb(seq![0x2Bu32, 0x20, 0x32, 0x6E]) == None::<(int, int)>,
        anb(seq![0x2Bu32, 0x20, 0x32]) == None::<(int, int)>,
        anb(seq![0x2Bu32, 0x20, 0x6E]) == None::<(int, int)>,
        anb(seq![0x33u32, 0x6E, 0x20, 0x2B, 0x20, 0x2D, 0x36]) == None::<(int, int)>,
{
    assert(anb(seq![0x6Fu32, 0x64, 0x64]) == Some((2int, 1int))) by (compute_only);
    assert(anb(seq![0x35u32]) == Some((0int, 5int))) by (compute_only);
    assert(anb(seq![0x32u32, 0x6E]) == Some((2int, 0int))) by (compute_only);
    assert(anb(seq![0x2Bu32, 0x6E]) == Some((1int, 0int))) by (compute_only);
    assert(anb(seq![0x2Du32, 0x6E, 0x2B, 0x36]) == Some((-1int, 6int))) by (compute_only);
    assert(anb(seq![0x33u32, 0x6E, 0x2D, 0x36]) == Some((3int, -6int))) by (compute_only);
    assert(anb(seq![0x33u32, 0x6E, 0x20, 0x2B, 0x20, 0x31]) == Some((3int, 1int)))
        by (compute_only);
    assert(anb(seq![0x2Bu32, 0x33, 0x6E, 0x20, 0x2D, 0x20, 0x32]) == Some((3int, -2int)))
        by (compute_only);
    assert(anb(seq![0x2Du32, 0x6E, 0x2D, 0x20, 0x31]) == Some((-1int, -1int))) by (compute_only);
    assert(anb(seq![0x2Du32, 0x6E, 0x2D, 0x31]) == Some((-1int, -1int))) by (compute_only);
    assert(anb(seq![0x6Eu32, 0x2D, 0x31]) == Some((1int, -1int))) by (compute_only);
    assert(anb(seq![0x33u32, 0x20, 0x6E]) == None::<(int, int)>) by (compute_only);
    assert(anb(seq![0x2Bu32, 0x20, 0x32, 0x6E]) == None::<(int, int)>) by (compute_only);
    assert(anb(seq![0x2Bu32, 0x20, 0x32]) == None::<(int, int)>) by (compute_only);
    assert(anb(seq![0x2Bu32, 0x20, 0x6E]) == None::<(int, int)>) by (compute_only);
    assert(anb(seq![0x33u32, 0x6E, 0x20, 0x2B, 0x20, 0x2D, 0x36]) == None::<(int, int)>)
        by (compute_only);
}

/// §9.1: `2n+1`, `n`, `-n-3`, and `5` when A is zero.
pub proof fn lemma_example_serialize_a_n_plus_b()
    ensures
        serialize_a_n_plus_b(2, 1) == seq![0x32u32, 0x6E, 0x2B, 0x31],
        serialize_a_n_plus_b(1, 0) == seq![0x6Eu32],
        serialize_a_n_plus_b(-1, -3) == seq![0x2Du32, 0x6E, 0x2D, 0x33],
        serialize_a_n_plus_b(0, 5) == seq![0x35u32],
{
    assert(serialize_a_n_plus_b(2, 1) == seq![0x32u32, 0x6E, 0x2B, 0x31]) by (compute_only);
    assert(serialize_a_n_plus_b(1, 0) == seq![0x6Eu32]) by (compute_only);
    assert(serialize_a_n_plus_b(-1, -3) == seq![0x2Du32, 0x6E, 0x2D, 0x33]) by (compute_only);
    assert(serialize_a_n_plus_b(0, 5) == seq![0x35u32]) by (compute_only);
}

/// §5.5.6 steps 1 to 4. `1:x;a:b`: step 1 needs an ident, so the number starts "the remnants
/// of a bad declaration", which end at the `;` and give no declaration, and the next one is
/// read. `a :b`: step 2 discards the whitespace before the colon. `a b;c:d`: step 3 needs a
/// colon, so `b;` is the remnants. `a: b`: step 4 discards the whitespace after the colon,
/// so the value is the ident alone.
pub proof fn lemma_example_declaration_steps()
    ensures
        parse_a_list_of_declarations(
            Input::String { string: seq![0x31u32, 0x3A, 0x78, 0x3B, 0x61, 0x3A, 0x62] },
        ) == seq![declaration(0x61, seq![ident(0x62)])],
        parse_a_list_of_declarations(
            Input::String { string: seq![0x61u32, 0x20, 0x3A, 0x62] },
        ) == seq![declaration(0x61, seq![ident(0x62)])],
        parse_a_list_of_declarations(
            Input::String { string: seq![0x61u32, 0x20, 0x62, 0x3B, 0x63, 0x3A, 0x64] },
        ) == seq![declaration(0x63, seq![ident(0x64)])],
        parse_a_declaration(Input::String { string: seq![0x61u32, 0x3A, 0x20, 0x62] }) == Some(
            declaration(0x61, seq![ident(0x62)]),
        ),
{
    assert(parse_a_list_of_declarations(
        Input::String { string: seq![0x31u32, 0x3A, 0x78, 0x3B, 0x61, 0x3A, 0x62] },
    ) == seq![declaration(0x61, seq![ident(0x62)])]) by (compute_only);
    assert(parse_a_list_of_declarations(
        Input::String { string: seq![0x61u32, 0x20, 0x3A, 0x62] },
    ) == seq![declaration(0x61, seq![ident(0x62)])]) by (compute_only);
    assert(parse_a_list_of_declarations(
        Input::String { string: seq![0x61u32, 0x20, 0x62, 0x3B, 0x63, 0x3A, 0x64] },
    ) == seq![declaration(0x63, seq![ident(0x64)])]) by (compute_only);
    assert(parse_a_declaration(Input::String { string: seq![0x61u32, 0x3A, 0x20, 0x62] }) == Some(
        declaration(0x61, seq![ident(0x62)]),
    )) by (compute_only);
}

/// §5.4.7 "parse a declaration": step 2 discards whitespace before it (` a:b ` is `a:b`),
/// step 6 returns a syntax error if input is not empty (`a:b;c`), and §5.5.6 step 8's
/// "custom property name string" is a name that starts with two dashes: `--x:y` has an
/// original text, `-x:y` has none.
pub proof fn lemma_example_parse_a_declaration()
    ensures
        parse_a_declaration(
            Input::String { string: seq![0x20u32, 0x20, 0x61, 0x3A, 0x62, 0x20, 0x20] },
        ) == Some(declaration(0x61, seq![ident(0x62)])),
        parse_a_declaration(
            Input::String { string: seq![0x61u32, 0x3A, 0x62, 0x3B, 0x63] },
        ) == None::<Declaration>,
        parse_a_declaration(Input::String { string: seq![0x2Du32, 0x78, 0x3A, 0x79] }) == Some(
            Declaration {
                name: seq![0x2Du32, 0x78],
                value: seq![ident(0x79)],
                important: false,
                original_text: None,
            },
        ),
        parse_a_declaration(
            Input::String { string: seq![0x2Du32, 0x2D, 0x78, 0x3A, 0x79] },
        ) == Some(
            Declaration {
                name: seq![0x2Du32, 0x2D, 0x78],
                value: seq![ident(0x79)],
                important: false,
                original_text: Some(seq![0x79u32]),
            },
        ),
{
    assert(parse_a_declaration(
        Input::String { string: seq![0x20u32, 0x20, 0x61, 0x3A, 0x62, 0x20, 0x20] },
    ) == Some(declaration(0x61, seq![ident(0x62)]))) by (compute_only);
    assert(parse_a_declaration(
        Input::String { string: seq![0x61u32, 0x3A, 0x62, 0x3B, 0x63] },
    ) == None::<Declaration>) by (compute_only);
    assert(parse_a_declaration(Input::String { string: seq![0x2Du32, 0x78, 0x3A, 0x79] }) == Some(
        Declaration {
            name: seq![0x2Du32, 0x78],
            value: seq![ident(0x79)],
            important: false,
            original_text: None,
        },
    )) by (compute_only);
    assert(parse_a_declaration(
        Input::String { string: seq![0x2Du32, 0x2D, 0x78, 0x3A, 0x79] },
    ) == Some(
        Declaration {
            name: seq![0x2Du32, 0x2D, 0x78],
            value: seq![ident(0x79)],
            important: false,
            original_text: Some(seq![0x79u32]),
        },
    )) by (compute_only);
}

/// §5.4.6 "parse a rule": ` a{} ` is the rule `a{}`, with the whitespace on both sides
/// discarded (steps 2 and 4); `a{}b` is a syntax error, since input is not empty after it
/// (step 5); and `@a;` is an at-rule (step 3's at-keyword branch).
pub proof fn lemma_example_parse_a_rule()
    ensures
        parse_a_rule(Input::String { string: seq![0x20u32, 0x61, 0x7B, 0x7D, 0x20] }) == Some(
            style_rule(0x61, Seq::empty(), Seq::empty()),
        ),
        parse_a_rule(Input::String { string: seq![0x61u32, 0x7B, 0x7D, 0x62] }) == None::<Rule>,
        parse_a_rule(Input::String { string: seq![0x40u32, 0x61, 0x3B] }) == Some(
            Rule::AtRule { name: seq![0x61u32], prelude: Seq::empty(), child_rules: None },
        ),
{
    assert(parse_a_rule(Input::String { string: seq![0x20u32, 0x61, 0x7B, 0x7D, 0x20] }) == Some(
        style_rule(0x61, Seq::empty(), Seq::empty()),
    )) by (compute_only);
    assert(parse_a_rule(Input::String { string: seq![0x61u32, 0x7B, 0x7D, 0x62] })
        == None::<Rule>) by (compute_only);
    assert(parse_a_rule(Input::String { string: seq![0x40u32, 0x61, 0x3B] }) == Some(
        Rule::AtRule { name: seq![0x61u32], prelude: Seq::empty(), child_rules: None },
    )) by (compute_only);
}

/// §5.5.10 "consume a function": `f(a)b` is the function `f(a)` and then `b`: the name is
/// the token's value, and the `)` ends the function and is not in it.
pub proof fn lemma_example_function()
    ensures
        parse_a_list_of_component_values(
            Input::String { string: seq![0x66u32, 0x28, 0x61, 0x29, 0x62] },
        ) == seq![
            ComponentValue::Function { name: seq![0x66u32], value: seq![ident(0x61)] },
            ident(0x62),
        ],
        parse_a_list_of_component_values(
            Input::String { string: seq![0x66u32, 0x28, 0x61, 0x29, 0x62] },
        )[0]->name.len() == 1,
{
    assert(parse_a_list_of_component_values(
        Input::String { string: seq![0x66u32, 0x28, 0x61, 0x29, 0x62] },
    ) == seq![
        ComponentValue::Function { name: seq![0x66u32], value: seq![ident(0x61)] },
        ident(0x62),
    ]) by (compute_only);
    assert(parse_a_list_of_component_values(
        Input::String { string: seq![0x66u32, 0x28, 0x61, 0x29, 0x62] },
    )[0]->name.len() == 1) by (compute_only);
}

/// §5.5.3 "consume a qualified rule". In `a{b c;d{}}`, `b c` is read as a rule with `;` as
/// the stop token, which "Return nothing" at the `;`, so the child is `d{}` alone. In
/// `a{b}c{}`, a `<}-token>` when nested "return nothing", so the block ends there and `c{}`
/// is a rule of its own.
pub proof fn lemma_example_qualified_rule_stops()
    ensures
        rules(seq![0x61u32, 0x7B, 0x62, 0x20, 0x63, 0x3B, 0x64, 0x7B, 0x7D, 0x7D]) == seq![
            style_rule(
                0x61,
                Seq::empty(),
                seq![style_rule(0x64, Seq::empty(), Seq::empty())],
            ),
        ],
        rules(seq![0x61u32, 0x7B, 0x62, 0x7D, 0x63, 0x7B, 0x7D]) == seq![
            style_rule(0x61, Seq::empty(), Seq::empty()),
            style_rule(0x63, Seq::empty(), Seq::empty()),
        ],
        first_child_prelude(
            seq![0x61u32, 0x7B, 0x62, 0x20, 0x63, 0x3B, 0x64, 0x7B, 0x7D, 0x7D],
        ).len() == 1,
{
    assert(rules(seq![0x61u32, 0x7B, 0x62, 0x20, 0x63, 0x3B, 0x64, 0x7B, 0x7D, 0x7D]) == seq![
        style_rule(0x61, Seq::empty(), seq![style_rule(0x64, Seq::empty(), Seq::empty())]),
    ]) by (compute_only);
    assert(rules(seq![0x61u32, 0x7B, 0x62, 0x7D, 0x63, 0x7B, 0x7D]) == seq![
        style_rule(0x61, Seq::empty(), Seq::empty()),
        style_rule(0x63, Seq::empty(), Seq::empty()),
    ]) by (compute_only);
    assert(first_child_prelude(
        seq![0x61u32, 0x7B, 0x62, 0x20, 0x63, 0x3B, 0x64, 0x7B, 0x7D, 0x7D],
    ).len() == 1) by (compute_only);
}

/// §5.5.2 "consume an at-rule". `@a;b{}`: the `;` ends the at-rule, and `b{}` is a rule.
/// `@a{b:c}`: the block is assigned to the rule's child rules, here the one list of
/// declarations. `@a b;`: the prelude is the whitespace and the ident.
pub proof fn lemma_example_at_rules()
    ensures
        rules(seq![0x40u32, 0x61, 0x3B, 0x62, 0x7B, 0x7D]) == seq![
            Rule::AtRule { name: seq![0x61u32], prelude: Seq::empty(), child_rules: None },
            style_rule(0x62, Seq::empty(), Seq::empty()),
        ],
        rules(seq![0x40u32, 0x61, 0x7B, 0x62, 0x3A, 0x63, 0x7D]) == seq![
            Rule::AtRule {
                name: seq![0x61u32],
                prelude: Seq::empty(),
                child_rules: Some(
                    seq![
                        BlockItem::Declarations {
                            declarations: seq![declaration(0x62, seq![ident(0x63)])],
                        },
                    ],
                ),
            },
        ],
        rules(seq![0x40u32, 0x61, 0x20, 0x62, 0x3B]) == seq![
            Rule::AtRule {
                name: seq![0x61u32],
                prelude: seq![token(Token::Whitespace), ident(0x62)],
                child_rules: None,
            },
        ],
        first_at_rule_block_len(seq![0x40u32, 0x61, 0x7B, 0x62, 0x3A, 0x63, 0x7D]) == 1,
        first_at_rule_prelude(seq![0x40u32, 0x61, 0x20, 0x62, 0x3B]).len() == 2,
{
    assert(rules(seq![0x40u32, 0x61, 0x3B, 0x62, 0x7B, 0x7D]) == seq![
        Rule::AtRule { name: seq![0x61u32], prelude: Seq::empty(), child_rules: None },
        style_rule(0x62, Seq::empty(), Seq::empty()),
    ]) by (compute_only);
    assert(rules(seq![0x40u32, 0x61, 0x7B, 0x62, 0x3A, 0x63, 0x7D]) == seq![
        Rule::AtRule {
            name: seq![0x61u32],
            prelude: Seq::empty(),
            child_rules: Some(
                seq![
                    BlockItem::Declarations {
                        declarations: seq![declaration(0x62, seq![ident(0x63)])],
                    },
                ],
            ),
        },
    ]) by (compute_only);
    assert(rules(seq![0x40u32, 0x61, 0x20, 0x62, 0x3B]) == seq![
        Rule::AtRule {
            name: seq![0x61u32],
            prelude: seq![token(Token::Whitespace), ident(0x62)],
            child_rules: None,
        },
    ]) by (compute_only);
    assert(first_at_rule_block_len(seq![0x40u32, 0x61, 0x7B, 0x62, 0x3A, 0x63, 0x7D]) == 1)
        by (compute_only);
    assert(first_at_rule_prelude(seq![0x40u32, 0x61, 0x20, 0x62, 0x3B]).len() == 2)
        by (compute_only);
}

/// §6.2 more of `<a-n-plus-b>`: `+n-1` is `<n-ident>` after a `+` with nothing between
/// (A is 1, B is -1), `+ n-1` is not; `n- 1` is `<ndash-ident> <signless-integer>`
/// (B is the integer's negation); `3n- 1` is `<ndash-dimension> <signless-integer>`;
/// `+n- 1` is `'+' <ndash-ident> <signless-integer>`; and `n-` has no digits, so it is
/// nothing.
pub proof fn lemma_example_a_n_plus_b_more()
    ensures
        anb(seq![0x2Bu32, 0x6E, 0x2D, 0x31]) == Some((1int, -1int)),
        anb(seq![0x2Bu32, 0x20, 0x6E, 0x2D, 0x31]) == None::<(int, int)>,
        anb(seq![0x6Eu32, 0x2D, 0x20, 0x31]) == Some((1int, -1int)),
        anb(seq![0x33u32, 0x6E, 0x2D, 0x20, 0x31]) == Some((3int, -1int)),
        anb(seq![0x2Bu32, 0x6E, 0x2D, 0x20, 0x31]) == Some((1int, -1int)),
        anb(seq![0x6Eu32, 0x2D]) == None::<(int, int)>,
{
    assert(anb(seq![0x2Bu32, 0x6E, 0x2D, 0x31]) == Some((1int, -1int))) by (compute_only);
    assert(anb(seq![0x2Bu32, 0x20, 0x6E, 0x2D, 0x31]) == None::<(int, int)>) by (compute_only);
    assert(anb(seq![0x6Eu32, 0x2D, 0x20, 0x31]) == Some((1int, -1int))) by (compute_only);
    assert(anb(seq![0x33u32, 0x6E, 0x2D, 0x20, 0x31]) == Some((3int, -1int))) by (compute_only);
    assert(anb(seq![0x2Bu32, 0x6E, 0x2D, 0x20, 0x31]) == Some((1int, -1int))) by (compute_only);
    assert(anb(seq![0x6Eu32, 0x2D]) == None::<(int, int)>) by (compute_only);
}

} // verus!
