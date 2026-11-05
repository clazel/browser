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
            Input::String {
                string: seq![
                    0x2Du32, 0x2D, 0x78, 0x3A, 0x20, 0x2F, 0x2A, 0x2A, 0x2F, 0x61, 0x20, 0x62,
                    0x20, 0x2F, 0x2A, 0x2A, 0x2F, 0x20, 0x21, 0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74,
                    0x61, 0x6E, 0x74, 0x20,
                ],
            },
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
        Input::String {
            string: seq![
                0x2Du32, 0x2D, 0x78, 0x3A, 0x20, 0x2F, 0x2A, 0x2A, 0x2F, 0x61, 0x20, 0x62, 0x20,
                0x2F, 0x2A, 0x2A, 0x2F, 0x20, 0x21, 0x69, 0x6D, 0x70, 0x6F, 0x72, 0x74, 0x61,
                0x6E, 0x74, 0x20,
            ],
        },
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
            Input::String {
                string: unicode_range_string() + seq![
                    0x3Au32, 0x55, 0x2B, 0x32, 0x36, 0x2D, 0x32, 0x66,
                ],
            },
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
        Input::String {
            string: unicode_range_string() + seq![
                0x3Au32, 0x55, 0x2B, 0x32, 0x36, 0x2D, 0x32, 0x66,
            ],
        },
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

} // verus!
