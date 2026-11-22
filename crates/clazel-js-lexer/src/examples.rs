//! The standard's own examples and a few small inputs, evaluated against
//! the spec: evidence that the transcription accepts what the standard says
//! it accepts, and computes the values it says it computes. Positive facts
//! only; the negative ones (that no alternative derives a range) are for
//! the conformance suite and, in the second half of 7.2, the proofs.
//!
//! This is a module of its own for the reason `clazel-percent`'s is.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::unicode::{lemma_id_continue_gap, lemma_id_start_gap};
#[cfg(verus_only)]
use super::unicode_data::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §12.7 and §12.7.1.2: `ab` is an `IdentifierName` whose
/// IdentifierCodePoints are `ab` (an escape contributes the code point it
/// names), and it has no early error.
pub proof fn example_identifier_with_escape()
    ensures
        identifier_name_cps(
            seq![0x61u32, 0x5C, 0x75, 0x30, 0x30, 0x36, 0x32],
            0,
            7,
            seq![0x61u32, 0x62],
        ),
        identifier_early_errors_ok(seq![0x61u32, 0x62]),
{
    let s = seq![0x61u32, 0x5C, 0x75, 0x30, 0x30, 0x36, 0x32];
    reveal_with_fuel(hex_digits_mv, 5);
    assert(identifier_name_cps(s, 0, 1, seq![0x61u32]));
    assert(identifier_part(s, 1, 7)) by {
        assert(hex4_digits(s, 3, 7));
        assert(unicode_escape_sequence(s, 2, 7));
    }
    assert(unicode_escape_code_point(s, 2, 7) == 0x62);
    assert(identifier_code_point(s, 1, 7) == 0x62u32);
    assert(seq![0x61u32, 0x62].drop_last() =~= seq![0x61u32]);
    assert(identifier_name_cps(s, 0, 7, seq![0x61u32, 0x62]));
    let cps = seq![0x61u32, 0x62];
    assert(identifier_early_errors_ok(cps)) by {
        assert(cps[0] == 0x61u32);
        assert(cps[1] == 0x62u32);
    }
}

/// §12.9.3: "`3in` is an error and not the two input elements `3` and
/// `in`": the code point after `3` starts an `IdentifierStart`.
pub proof fn example_numeric_literal_then_identifier()
    ensures
        numeric_literal(seq![0x33u32, 0x69, 0x6E], 0, 1),
        numeric_literal_follow_error(seq![0x33u32, 0x69, 0x6E], 1),
{
    let s = seq![0x33u32, 0x69, 0x6E];
    assert(decimal_integer_literal(s, 0, 1));
    assert(decimal_literal(s, 0, 1)) by {
        assert(decimal_integer_literal(s, 0, 1));
    }
    assert(identifier_start(s, 1, 2));
}

/// §12.9.3: numeric separators and the BigInt suffix. `0b1_0n` is a
/// `NumericLiteral`, a BigInt; `1_000` is a decimal literal.
pub proof fn example_numeric_separators()
    ensures
        numeric_literal(seq![0x30u32, 0x62, 0x31, 0x5F, 0x30, 0x6E], 0, 6),
        numeric_literal_is_bigint(seq![0x30u32, 0x62, 0x31, 0x5F, 0x30, 0x6E], 0, 6),
        numeric_literal(seq![0x31u32, 0x5F, 0x30, 0x30, 0x30], 0, 5),
{
    let s = seq![0x30u32, 0x62, 0x31, 0x5F, 0x30, 0x6E];
    assert(binary_digits(true, s, 2, 3));
    assert(binary_digits(true, s, 2, 5));
    assert(non_decimal_integer_literal(true, s, 0, 5));
    let t = seq![0x31u32, 0x5F, 0x30, 0x30, 0x30];
    assert(decimal_digits(true, t, 2, 3));
    assert(decimal_digits(true, t, 2, 4));
    assert(decimal_digits(true, t, 2, 5));
    assert(decimal_integer_literal(t, 0, 5));
    assert(decimal_literal(t, 0, 5)) by {
        assert(decimal_integer_literal(t, 0, 5));
    }
}

/// §12.9.3 with the legacy forms: `010` is a `LegacyOctalIntegerLiteral` and
/// `08` a `NonOctalDecimalIntegerLiteral`, both flagged legacy.
pub proof fn example_legacy_numeric_literals()
    ensures
        numeric_literal(seq![0x30u32, 0x31, 0x30], 0, 3),
        numeric_literal_is_legacy(seq![0x30u32, 0x31, 0x30], 0, 3),
        numeric_literal(seq![0x30u32, 0x38], 0, 2),
        numeric_literal_is_legacy(seq![0x30u32, 0x38], 0, 2),
        legacy_octal_integer_literal(seq![0x30u32, 0x31, 0x30], 0, 3),
{
    let s = seq![0x30u32, 0x31, 0x30];
    assert(legacy_octal_integer_literal(s, 0, 2));
    assert(legacy_octal_integer_literal(s, 0, 3));
    let t = seq![0x30u32, 0x38];
    assert(non_octal_decimal_integer_literal(t, 0, 2));
    assert(decimal_integer_literal(t, 0, 2));
    assert(decimal_literal(t, 0, 2)) by {
        assert(decimal_integer_literal(t, 0, 2));
    }
    assert(numeric_literal_is_legacy(t, 0, 2)) by {
        assert(non_octal_decimal_integer_literal(t, 0, 2));
    }
}


/// §12.9.4.2: `"a\n\u{1F600}\ud800"` has the string value `a`, LF, the
/// surrogate pair of U+1F600, and a lone high surrogate.
pub proof fn example_string_values()
    ensures
        string_literal_sv(
            seq![
                0x22u32, 0x61, 0x5C, 0x6E, 0x5C, 0x75, 0x7B, 0x31, 0x46, 0x36, 0x30, 0x30, 0x7D,
                0x5C, 0x75, 0x64, 0x38, 0x30, 0x30, 0x22,
            ],
            0,
            20,
            seq![0x61u16, 0x0A, 0xD83D, 0xDE00, 0xD800],
        ),
{
    let s = seq![
        0x22u32, 0x61, 0x5C, 0x6E, 0x5C, 0x75, 0x7B, 0x31, 0x46, 0x36, 0x30, 0x30, 0x7D, 0x5C,
        0x75, 0x64, 0x38, 0x30, 0x30, 0x22,
    ];
    let q = 0x22u32;
    reveal_with_fuel(hex_digits_mv, 6);
    // The characters, from the right: `\ud800` is [13, 19), `\u{1F600}` is
    // [4, 13), `\n` is [2, 4) and `a` is [1, 2).
    let v5 = seq![0xD800u16];
    assert(string_character_sv(s, 13, 19, q, v5)) by {
        assert(hex4_digits(s, 15, 19));
        assert(unicode_escape_sequence(s, 14, 19));
        assert(unicode_escape_sv(s, 14, 19) =~= v5);
        assert(template_escape_sequence_sv(s, 14, 19, v5));
        assert(escape_sequence_sv(s, 14, 19, v5));
    }
    super::lemmas::lemma_string_characters_one(s, 13, 19, q, v5);
    let pair = utf16_encode_code_point(0x1F600);
    assert(pair =~= seq![0xD83Du16, 0xDE00]);
    assert(string_character_sv(s, 4, 13, q, pair)) by {
        assert(digits(16, false, s, 7, 8));
        assert(digits(16, false, s, 7, 9));
        assert(digits(16, false, s, 7, 10));
        assert(digits(16, false, s, 7, 11));
        assert(digits(16, false, s, 7, 12));
        assert(code_point(s, 7, 12));
        assert(unicode_escape_sequence(s, 5, 13));
        assert(unicode_escape_sv(s, 5, 13) =~= pair);
        assert(template_escape_sequence_sv(s, 5, 13, pair));
        assert(escape_sequence_sv(s, 5, 13, pair));
    }
    super::lemmas::lemma_string_characters_cons(s, 4, 13, 19, q, pair, v5);
    let lf = seq![0x0Au16];
    assert(string_character_sv(s, 2, 4, q, lf)) by {
        assert(character_escape_sequence_sv(s, 3, 4, lf));
        assert(template_escape_sequence_sv(s, 3, 4, lf));
        assert(escape_sequence_sv(s, 3, 4, lf));
    }
    super::lemmas::lemma_string_characters_cons(s, 2, 4, 19, q, lf, pair + v5);
    let a = seq![0x61u16];
    assert(string_character_sv(s, 1, 2, q, a));
    super::lemmas::lemma_string_characters_cons(s, 1, 2, 19, q, a, lf + (pair + v5));
    assert(a + (lf + (pair + v5)) =~= seq![0x61u16, 0x0A, 0xD83D, 0xDE00, 0xD800]);
    assert(string_literal_sv(s, 0, 20, a + (lf + (pair + v5))));
}

/// §12.9.6: `` `a${ `` is a `TemplateHead`, with TV and TRV `a`; and
/// `` `\u{` `` (an invalid escape) has TV *undefined* and TRV `\u{`.
pub proof fn example_template_values()
    ensures
        template_part(
            seq![0x60u32, 0x61, 0x24, 0x7B],
            0,
            4,
            TemplateKind::Head,
            Some(seq![0x61u16]),
            seq![0x61u16],
        ),
        template_part(
            seq![0x60u32, 0x5C, 0x75, 0x7B, 0x60],
            0,
            5,
            TemplateKind::NoSubstitution,
            None,
            seq![0x5Cu16, 0x75, 0x7B],
        ),
{
    let s = seq![0x60u32, 0x61, 0x24, 0x7B];
    let a = seq![0x61u16];
    assert(template_character(s, 1, 2, Some(a), a));
    super::lemmas::lemma_template_characters_one(s, 1, 2, Some(a), a);
    assert(is_lit(s, 2, 4, seq!['$', '{']));
    let t = seq![0x60u32, 0x5C, 0x75, 0x7B, 0x60];
    let raw = seq![0x5Cu16, 0x75, 0x7B];
    assert(not_escape_sequence(t, 2, 4));
    reveal_with_fuel(utf16_of, 5);
    assert(utf16_of(t, 1, 4) =~= raw);
    assert(template_character(t, 1, 4, None, raw));
    super::lemmas::lemma_template_characters_one(t, 1, 4, None, raw);
}

/// §12.4: `/**/` and `/* a */` are comments; and a multi-line comment holds a
/// line terminator, which the parser sees as one.
pub proof fn example_comments()
    ensures
        comment(seq![0x2Fu32, 0x2A, 0x2A, 0x2F], 0, 4, false),
        comment(seq![0x2Fu32, 0x2A, 0x0A, 0x2A, 0x2F], 0, 5, false),
        contains_line_terminator(seq![0x2Fu32, 0x2A, 0x0A, 0x2A, 0x2F], 0, 5),
{
    let s = seq![0x2Fu32, 0x2A, 0x2A, 0x2F];
    assert(multi_line_comment(s, 0, 4));
    let t = seq![0x2Fu32, 0x2A, 0x0A, 0x2A, 0x2F];
    assert(multi_line_comment_chars(t, 2, 3));
    assert(multi_line_comment(t, 0, 5));
    assert(is_line_terminator(t[2]));
}

/// §12.3: the four `LineTerminator` code points, <LF>, <CR>, <LS> and <PS>,
/// and a code point that is not one (U+0085 NEL, which ES does not count).
pub proof fn example_line_terminators()
    ensures
        is_line_terminator(0x000Au32),
        is_line_terminator(0x000Du32),
        is_line_terminator(0x2028u32),
        is_line_terminator(0x2029u32),
        !is_line_terminator(0x0085u32),
{
}

/// §12.9.3.1 "The MV of HexDigit :: one of `a` `A` is 10", and so on: `b`
/// and `B` are 11, `9` is 9.
pub proof fn example_hex_digit_values()
    ensures
        hex_digit_value(0x62u32) == 11,
        hex_digit_value(0x42u32) == 11,
        hex_digit_value(0x39u32) == 9,
{
}

/// §12.9.5: `/[/]\//gu` is a `RegularExpressionLiteral`: a `/` inside a
/// class or escaped does not end the body.
pub proof fn example_regexp_literal()
    ensures
        regexp_literal(seq![0x2Fu32, 0x5B, 0x2F, 0x5D, 0x5C, 0x2F, 0x2F, 0x67, 0x75], 0, 9, 6),
{
    let s = seq![0x2Fu32, 0x5B, 0x2F, 0x5D, 0x5C, 0x2F, 0x2F, 0x67, 0x75];
    assert(regexp_class_chars(s, 2, 2));
    assert(regexp_class_chars(s, 2, 3)) by {
        assert(regexp_class_char(s, 2, 3));
    }
    assert(regexp_class(s, 1, 4));
    assert(regexp_first_char(s, 1, 4));
    assert(regexp_chars(s, 4, 4));
    assert(regexp_backslash_sequence(s, 4, 6));
    assert(regexp_char(s, 4, 6));
    assert(regexp_chars(s, 4, 6)) by {
        assert(regexp_chars(s, 4, 4));
    }
    assert(regexp_body(s, 1, 6));
    assert(regexp_flags(s, 7, 9)) by {
        assert(is_identifier_part_char(s[7]));
        assert(is_identifier_part_char(s[8]));
    }
}


/// §12.9.4.2 Table "String Single Character Escape Sequences": `\b` is
/// U+0008, `\t` U+0009, `\n` U+000A, `\v` U+000B, `\f` U+000C, `\r`
/// U+000D, and `\"` is `"`.
pub proof fn example_single_escapes()
    ensures
        single_escape_code_unit(0x62u32) == 0x0008u16,
        single_escape_code_unit(0x74u32) == 0x0009u16,
        single_escape_code_unit(0x6Eu32) == 0x000Au16,
        single_escape_code_unit(0x76u32) == 0x000Bu16,
        single_escape_code_unit(0x66u32) == 0x000Cu16,
        single_escape_code_unit(0x72u32) == 0x000Du16,
        single_escape_code_unit(0x22u32) == 0x0022u16,
{
}

/// §12.9.6.2: the TRV of `<CR><LF>` is the one code unit `<LF>`.
pub proof fn example_trv_crlf()
    ensures
        line_terminator_sequence_trv(seq![0x0Du32, 0x0Au32], 0, 2) =~= seq![0x000Au16],
{
}

/// §12.9.5: a `RegularExpressionNonTerminator` is a `SourceCharacter` but
/// not a `LineTerminator`: `a` is one, <LF> is not.
pub proof fn example_regexp_non_terminator()
    ensures
        is_regexp_non_terminator(0x61u32),
        !is_regexp_non_terminator(0x000Au32),
{
}

/// §12: comments, white space and line terminators are discarded by the
/// syntactic grammar; an identifier is not.
pub proof fn example_trivia()
    ensures
        is_trivia(ElementKind::WhiteSpace),
        is_trivia(ElementKind::LineTerminator),
        is_trivia(ElementKind::Comment),
        is_trivia(ElementKind::HashbangComment),
        !is_trivia(ElementKind::IdentifierName),
{
}

/// Rows of the generated `ID_Start` table that the anchors below use
/// (Unicode 18.0.0): read from the table's contents.
proof fn fact_id_start_rows()
    ensures
        id_start_at(3).last == 0xD6 && id_start_at(4).first == 0xD8 && id_start_at(4).last == 0xF6,
        id_start_at(9).last == 0x2EE && id_start_at(10).first == 0x370,
        id_start_at(249).last == 0x1FFC && id_start_at(250).first == 0x2071,
        id_start_at(282).last == 0x2DDE && id_start_at(283).first == 0x3005,
        id_start_at(296).first == 0x4E00 && id_start_at(296).last == 0xA48C,
{
    reveal(ID_START_0);
}

/// Rows of the generated `ID_Continue` table that the anchors below use.
proof fn fact_id_continue_rows()
    ensures
        id_continue_at(4).last == 0xD6 && id_continue_at(5).first == 0xD8,
        id_continue_at(11).first == 0x300 && id_continue_at(11).last == 0x374,
        id_continue_at(297).first == 0x200C && id_continue_at(297).last == 0x200D,
        id_continue_at(298).first == 0x203F,
        id_continue_at(335).last == 0x2DFF && id_continue_at(336).first == 0x3005,
{
    reveal(ID_CONTINUE_0);
}

/// §12.7 and the Unicode 18.0.0 `ID_Start` / `ID_Continue` of code points
/// above U+007F, as the generated table gives them (anchors; the table's
/// equality with `DerivedCoreProperties.txt` is not proven): U+00E9 and
/// U+65E5 are `ID_Start`; U+0300, U+200C and U+200D are `ID_Continue` and
/// not `ID_Start`; U+00D7, U+2028 and U+2E2F are neither.
pub proof fn example_unicode_id_anchors()
    ensures
        unicode_id_start(0xE9u32) && unicode_id_continue(0xE9u32),
        unicode_id_start(0x65E5u32) && unicode_id_continue(0x65E5u32),
        unicode_id_continue(0x0300u32) && !unicode_id_start(0x0300u32),
        unicode_id_continue(0x200Cu32) && !unicode_id_start(0x200Cu32),
        unicode_id_continue(0x200Du32) && !unicode_id_start(0x200Du32),
        !unicode_id_start(0x00D7u32) && !unicode_id_continue(0x00D7u32),
        !unicode_id_start(0x2028u32) && !unicode_id_continue(0x2028u32),
        !unicode_id_start(0x2E2Fu32) && !unicode_id_continue(0x2E2Fu32),
        unicode_id_start(0x61u32) && !unicode_id_start(0x5Fu32) && !unicode_id_start(0x30u32),
        unicode_id_continue(0x30u32) && unicode_id_continue(0x5Fu32) && !unicode_id_continue(
            0x24u32,
        ),
{
    fact_id_start_rows();
    fact_id_continue_rows();
    // Positive: a row holds the code point.
    assert(unicode_id_start_non_ascii(0xE9u32)) by {
        let _ = id_start_at(4);
    }
    assert(unicode_id_start_non_ascii(0x65E5u32)) by {
        let _ = id_start_at(296);
    }
    assert(unicode_id_continue_non_ascii(0xE9u32)) by {
        reveal(ID_CONTINUE_0);
        let _ = id_continue_at(5);
    }
    assert(unicode_id_continue_non_ascii(0x65E5u32)) by {
        reveal(ID_CONTINUE_0);
        let _ = id_continue_at(348);
    }
    assert(unicode_id_continue_non_ascii(0x0300u32)) by {
        let _ = id_continue_at(11);
    }
    assert(unicode_id_continue_non_ascii(0x200Cu32)) by {
        let _ = id_continue_at(297);
    }
    assert(unicode_id_continue_non_ascii(0x200Du32)) by {
        let _ = id_continue_at(297);
    }
    // Negative: the code point lies strictly between two adjacent rows.
    lemma_id_start_gap(9, 0x300u32);
    lemma_id_start_gap(249, 0x200Cu32);
    lemma_id_start_gap(249, 0x200Du32);
    lemma_id_start_gap(3, 0xD7u32);
    lemma_id_start_gap(249, 0x2028u32);
    lemma_id_start_gap(282, 0x2E2Fu32);
    lemma_id_continue_gap(4, 0xD7u32);
    lemma_id_continue_gap(297, 0x2028u32);
    lemma_id_continue_gap(335, 0x2E2Fu32);
}

} // verus!
