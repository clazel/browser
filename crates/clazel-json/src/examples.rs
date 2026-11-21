//! A few cases evaluated on the spec, as proven theorems. Each is its own
//! lemma so that `mutations.json` can name the one a mutant breaks, and
//! kept apart from `lemmas.rs` so that a mutant that breaks one of them
//! does not stop Verus before it checks a kill certificate there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// ECMA-404: "ws value ws" around a literal; `true`, `false` and `null`
/// are the whole of their productions.
pub proof fn lemma_example_literals()
    ensures
        json_parse(seq![0x20u32, 0x74, 0x72, 0x75, 0x65, 0x0A]) == Some(JsonValue::Bool(true)),
        json_parse(seq![0x66u32, 0x61, 0x6C, 0x73, 0x65]) == Some(JsonValue::Bool(false)),
        json_parse(seq![0x6Eu32, 0x75, 0x6C, 0x6C]) == Some(JsonValue::Null),
{
    assert(json_parse(seq![0x20u32, 0x74, 0x72, 0x75, 0x65, 0x0A]) == Some(JsonValue::Bool(true))) by (compute_only);
    assert(json_parse(seq![0x66u32, 0x61, 0x6C, 0x73, 0x65]) == Some(JsonValue::Bool(false))) by (compute_only);
    assert(json_parse(seq![0x6Eu32, 0x75, 0x6C, 0x6C]) == Some(JsonValue::Null)) by (compute_only);
}

/// `[1,"a"]` is an array of a number (kept as its source text) and a
/// string.
pub proof fn lemma_example_array()
    ensures
        json_parse(seq![0x5Bu32, 0x31, 0x2C, 0x22, 0x61, 0x22, 0x5D]) == Some(
            JsonValue::Array(seq![JsonValue::Number(seq![0x31u32]), JsonValue::String(seq![0x61u16])]),
        ),
{
    assert(json_parse(seq![0x5Bu32, 0x31, 0x2C, 0x22, 0x61, 0x22, 0x5D]) == Some(
        JsonValue::Array(seq![JsonValue::Number(seq![0x31u32]), JsonValue::String(seq![0x61u16])]),
    )) by (compute_only);
}

/// `{"a":null}` is an object with one member.
pub proof fn lemma_example_object()
    ensures
        json_parse(seq![0x7Bu32, 0x22, 0x61, 0x22, 0x3A, 0x6E, 0x75, 0x6C, 0x6C, 0x7D]) == Some(
            JsonValue::Object(seq![JsonMember { key: seq![0x61u16], value: JsonValue::Null }]),
        ),
{
    assert(json_parse(seq![0x7Bu32, 0x22, 0x61, 0x22, 0x3A, 0x6E, 0x75, 0x6C, 0x6C, 0x7D]) == Some(
        JsonValue::Object(seq![JsonMember { key: seq![0x61u16], value: JsonValue::Null }]),
    )) by (compute_only);
}

/// Numbers: `-0.5e+2` is one number; `01` is not a text (a leading zero is
/// not followed by digits), nor is `1.` or `+1`.
pub proof fn lemma_example_numbers()
    ensures
        json_parse(seq![0x2Du32, 0x30, 0x2E, 0x35, 0x65, 0x2B, 0x32]) == Some(
            JsonValue::Number(seq![0x2Du32, 0x30, 0x2E, 0x35, 0x65, 0x2B, 0x32]),
        ),
        json_parse(seq![0x30u32, 0x31]) is None,
        json_parse(seq![0x31u32, 0x2E]) is None,
        json_parse(seq![0x2Bu32, 0x31]) is None,
{
    assert(json_parse(seq![0x2Du32, 0x30, 0x2E, 0x35, 0x65, 0x2B, 0x32]) == Some(
        JsonValue::Number(seq![0x2Du32, 0x30, 0x2E, 0x35, 0x65, 0x2B, 0x32]),
    )) by (compute_only);
    assert(json_parse(seq![0x30u32, 0x31]) is None) by (compute_only);
    assert(json_parse(seq![0x31u32, 0x2E]) is None) by (compute_only);
    assert(json_parse(seq![0x2Bu32, 0x31]) is None) by (compute_only);
}

/// Strings: `"é\n\ud83d"` is U+00E9, a line feed and the lone
/// leading surrogate U+D83D; a raw U+1F600 becomes its surrogate pair; a
/// raw line feed, an unknown escape and a missing quote are errors.
pub proof fn lemma_example_strings()
    ensures
        json_parse(seq![0x22u32, 0x5C, 0x75, 0x30, 0x30, 0x65, 0x39, 0x5C, 0x6E, 0x5C, 0x75, 0x64, 0x38, 0x33, 0x64, 0x22])
            == Some(JsonValue::String(seq![0xE9u16, 0x0A, 0xD83D])),
        json_parse(seq![0x22u32, 0x1F600, 0x22]) == Some(JsonValue::String(seq![0xD83Du16, 0xDE00])),
        json_parse(seq![0x22u32, 0x0A, 0x22]) is None,
        json_parse(seq![0x22u32, 0x5C, 0x78, 0x22]) is None,
        json_parse(seq![0x22u32, 0x61]) is None,
{
    assert(json_parse(
        seq![0x22u32, 0x5C, 0x75, 0x30, 0x30, 0x65, 0x39, 0x5C, 0x6E, 0x5C, 0x75, 0x64, 0x38, 0x33, 0x64, 0x22],
    ) == Some(JsonValue::String(seq![0xE9u16, 0x0A, 0xD83D]))) by (compute_only);
    assert(json_parse(seq![0x22u32, 0x1F600, 0x22]) == Some(JsonValue::String(seq![0xD83Du16, 0xDE00])))
        by (compute_only);
    assert(json_parse(seq![0x22u32, 0x0A, 0x22]) is None) by (compute_only);
    assert(json_parse(seq![0x22u32, 0x5C, 0x78, 0x22]) is None) by (compute_only);
    assert(json_parse(seq![0x22u32, 0x61]) is None) by (compute_only);
}

/// Structure errors: a trailing comma, trailing text, an empty text.
pub proof fn lemma_example_errors()
    ensures
        json_parse(seq![0x5Bu32, 0x31, 0x2C, 0x5D]) is None,
        json_parse(seq![0x31u32, 0x20, 0x32]) is None,
        json_parse(Seq::<u32>::empty()) is None,
        json_parse(seq![0x7Bu32, 0x22, 0x61, 0x22, 0x2C, 0x7D]) is None,
{
    assert(json_parse(seq![0x5Bu32, 0x31, 0x2C, 0x5D]) is None) by (compute_only);
    assert(json_parse(seq![0x31u32, 0x20, 0x32]) is None) by (compute_only);
    assert(json_parse(Seq::<u32>::empty()) is None) by (compute_only);
    assert(json_parse(seq![0x7Bu32, 0x22, 0x61, 0x22, 0x2C, 0x7D]) is None) by (compute_only);
}

/// Nesting: `[[1]]` is two levels deep. Three levels of `[` are refused by
/// a bound of two, and the real bound is `max_depth()`; the check below
/// uses `parse_value` with two levels left.
pub proof fn lemma_example_depth()
    ensures
        parse_value(seq![0x5Bu32, 0x5B, 0x31, 0x5D, 0x5D], 0, 2) is Some,
        parse_value(seq![0x5Bu32, 0x5B, 0x5B, 0x5D, 0x5D, 0x5D], 0, 2) is None,
        parse_value(seq![0x5Bu32, 0x5B, 0x5B, 0x5D, 0x5D, 0x5D], 0, 3) is Some,
{
    assert(parse_value(seq![0x5Bu32, 0x5B, 0x31, 0x5D, 0x5D], 0, 2) is Some) by (compute_only);
    assert(parse_value(seq![0x5Bu32, 0x5B, 0x5B, 0x5D, 0x5D, 0x5D], 0, 2) is None) by (compute_only);
    assert(parse_value(seq![0x5Bu32, 0x5B, 0x5B, 0x5D, 0x5D, 0x5D], 0, 3) is Some) by (compute_only);
}

/// QuoteJSONString: `a"\` gains escapes; a line feed is `\n`, U+001F is
/// `\u001f` (lowercase hex), a lone surrogate U+D800 is `\ud800`, a
/// surrogate pair stays as it is, and `/` is not escaped.
pub proof fn lemma_example_quote()
    ensures
        quote_json_string(seq![0x61u16, 0x22, 0x5C]) == seq![0x22u16, 0x61, 0x5C, 0x22, 0x5C, 0x5C, 0x22],
        quote_json_string(seq![0x0Au16, 0x1F]) == seq![0x22u16, 0x5C, 0x6E, 0x5C, 0x75, 0x30, 0x30, 0x31, 0x66, 0x22],
        quote_json_string(seq![0xD800u16]) == seq![0x22u16, 0x5C, 0x75, 0x64, 0x38, 0x30, 0x30, 0x22],
        quote_json_string(seq![0xD83Du16, 0xDE00]) == seq![0x22u16, 0xD83D, 0xDE00, 0x22],
        quote_json_string(seq![0x2Fu16]) == seq![0x22u16, 0x2F, 0x22],
        quote_json_string(Seq::<u16>::empty()) == seq![0x22u16, 0x22],
{
    assert(quote_json_string(seq![0x61u16, 0x22, 0x5C]) == seq![0x22u16, 0x61, 0x5C, 0x22, 0x5C, 0x5C, 0x22])
        by (compute_only);
    assert(quote_json_string(seq![0x0Au16, 0x1F]) == seq![0x22u16, 0x5C, 0x6E, 0x5C, 0x75, 0x30, 0x30, 0x31, 0x66, 0x22])
        by (compute_only);
    assert(quote_json_string(seq![0xD800u16]) == seq![0x22u16, 0x5C, 0x75, 0x64, 0x38, 0x30, 0x30, 0x22])
        by (compute_only);
    assert(quote_json_string(seq![0xD83Du16, 0xDE00]) == seq![0x22u16, 0xD83D, 0xDE00, 0x22]) by (compute_only);
    assert(quote_json_string(seq![0x2Fu16]) == seq![0x22u16, 0x2F, 0x22]) by (compute_only);
    assert(quote_json_string(Seq::<u16>::empty()) == seq![0x22u16, 0x22]) by (compute_only);
}

/// Whitespace is U+0009, U+000A, U+000D and U+0020 only: form feed and
/// vertical tab are not `ws`.
pub proof fn lemma_example_whitespace()
    ensures
        json_parse(seq![0x09u32, 0x0D, 0x0A, 0x20, 0x31, 0x09]) == Some(JsonValue::Number(seq![0x31u32])),
        json_parse(seq![0x0Cu32, 0x31]) is None,
        json_parse(seq![0x0Bu32, 0x31]) is None,
        json_parse(seq![0x31u32, 0x0C]) is None,
{
    assert(json_parse(seq![0x09u32, 0x0D, 0x0A, 0x20, 0x31, 0x09]) == Some(JsonValue::Number(seq![0x31u32])))
        by (compute_only);
    assert(json_parse(seq![0x0Cu32, 0x31]) is None) by (compute_only);
    assert(json_parse(seq![0x0Bu32, 0x31]) is None) by (compute_only);
    assert(json_parse(seq![0x31u32, 0x0C]) is None) by (compute_only);
}

/// The one-character escapes: `"\b\f\n\r\t\/\\\""`.
pub proof fn lemma_example_escapes()
    ensures
        json_parse(
            seq![0x22u32, 0x5C, 0x62, 0x5C, 0x66, 0x5C, 0x6E, 0x5C, 0x72, 0x5C, 0x74, 0x5C, 0x2F, 0x5C, 0x5C, 0x5C, 0x22, 0x22],
        ) == Some(JsonValue::String(seq![0x08u16, 0x0C, 0x0A, 0x0D, 0x09, 0x2F, 0x5C, 0x22])),
{
    assert(json_parse(
        seq![0x22u32, 0x5C, 0x62, 0x5C, 0x66, 0x5C, 0x6E, 0x5C, 0x72, 0x5C, 0x74, 0x5C, 0x2F, 0x5C, 0x5C, 0x5C, 0x22, 0x22],
    ) == Some(JsonValue::String(seq![0x08u16, 0x0C, 0x0A, 0x0D, 0x09, 0x2F, 0x5C, 0x22]))) by (compute_only);
}

/// `[[1]]` is a text: two levels are within `max_depth()`.
pub proof fn lemma_example_nested_text()
    ensures
        json_parse(seq![0x5Bu32, 0x5B, 0x31, 0x5D, 0x5D]) is Some,
{
    assert(json_parse(seq![0x5Bu32, 0x5B, 0x31, 0x5D, 0x5D]) is Some) by (compute_only);
}

/// QuoteJSONString's escape table: `\b`, `\t`, `\f`, `\r`.
pub proof fn lemma_example_quote_table()
    ensures
        quote_json_string(seq![0x08u16, 0x09, 0x0C, 0x0D]) == seq![0x22u16, 0x5C, 0x62, 0x5C, 0x74, 0x5C, 0x66, 0x5C, 0x72, 0x22],
{
    assert(quote_json_string(seq![0x08u16, 0x09, 0x0C, 0x0D]) == seq![0x22u16, 0x5C, 0x62, 0x5C, 0x74, 0x5C, 0x66, 0x5C, 0x72, 0x22])
        by (compute_only);
}

} // verus!
