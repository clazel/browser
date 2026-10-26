//! The standards' own examples, evaluated by Verus against the spec: the
//! examples of ITU-T X.690 (08/2015) §8.1.3.4, §8.1.3.5, §8.2.2, §8.6.4.2,
//! §8.8, §8.9.3, §8.14.4 and §8.19.5, and those of Kaliski's Layman's Guide
//! (§5.4, §5.7 Table 3, §5.8, §5.9, §5.10, §5.6, §5.17, §6.2.6), plus the
//! `DigestInfo` prefix of RFC 8017 §9.2 (Note 1, SHA-256). Each example is
//! checked both ways: the encoder writes the printed bytes, and the decoder
//! reads them back. The non-DER alternatives the standards print beside them
//! (a long-form length that fits the short form, a TRUE that is not `0xFF`,
//! indefinite lengths, constructed strings, padding bits that are not zero)
//! are checked to be rejected.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies, even with
//! `--verify-function`. A mutant that breaks an example would otherwise
//! fail every kill certificate placed next to it, not only the one about the
//! example.
//!
//! The `{2 999 3}` example is the one in this edition (§8.19.5); the 2002
//! edition's `{2 100 3}` is added beside it, computed by hand: the first
//! subidentifier is 2 * 40 + 100 = 180 = 1 * 128 + 52, so `81 34`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Smith" (§8.9.3), "Jones" (§8.14.4) and the other strings, as octets.
pub open spec fn smith() -> Seq<u8> {
    seq![0x53u8, 0x6D, 0x69, 0x74, 0x68]
}

/// "Jones".
pub open spec fn jones() -> Seq<u8> {
    seq![0x4Au8, 0x6F, 0x6E, 0x65, 0x73]
}

/// The tag `[APPLICATION 3]`, primitive.
pub open spec fn application_3() -> Tag {
    Tag { class: Class::Application, constructed: false, number: 3 }
}

/// The tag `[APPLICATION 7]`, constructed.
pub open spec fn application_7() -> Tag {
    Tag { class: Class::Application, constructed: true, number: 7 }
}

/// The X.690 examples: the length octets, BOOLEAN, BIT STRING, NULL,
/// SEQUENCE, the tagged-type chain of §8.14.4, and the OBJECT IDENTIFIER.
pub proof fn lemma_examples_x690()
    ensures
        // 8.1.3.4: "L = 38 can be encoded as 00100110".
        encode_length(38) == seq![0x26u8],
        read_length(seq![0x26u8], 0, 1) == Some((38nat, 1nat)),
        // 8.1.3.5: "L = 201 can be encoded as: 10000001 11001001".
        encode_length(201) == seq![0x81u8, 0xC9],
        read_length(seq![0x81u8, 0xC9], 0, 2) == Some((201nat, 2nat)),
        // DER (10.1): 38 in the long form 81 26 is not the minimum.
        read_length(seq![0x81u8, 0x26], 0, 2) is None,
        // The indefinite form 80 (8.1.3.6) and the reserved FF (8.1.3.5 c).
        read_length(seq![0x80u8], 0, 1) is None,
        read_length(seq![0xFFu8], 0, 1) is None,
        // A leading zero length octet (10.1).
        read_length(seq![0x82u8, 0x00, 0xC9], 0, 3) is None,
        // 8.2.2: "If of type BOOLEAN, the value TRUE can be encoded as: 01 01 FF".
        encode_boolean(true) == seq![0x01u8, 0x01, 0xFF],
        read_boolean(seq![0x01u8, 0x01, 0xFF], 0, 3) == Some((true, 3nat)),
        encode_boolean(false) == seq![0x01u8, 0x01, 0x00],
        // 8.2.2 allows any non-zero octet for TRUE; 11.1 (DER) requires FF.
        read_boolean(seq![0x01u8, 0x01, 0x01], 0, 3) is None,
        // 8.6.4.2: the value '0A3B5F291CD'H, primitive: 03 07 04 0A3B5F291CD0.
        encode_bit_string(4, seq![0x0Au8, 0x3B, 0x5F, 0x29, 0x1C, 0xD0]) == seq![
            0x03u8, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0,
        ],
        read_bit_string(seq![0x03u8, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0], 0, 9) == Some(
            (4u8, 3nat, 9nat, 9nat),
        ),
        // 8.6.4.2: the same value as a constructor (23 80 ...) is not DER.
        read_tlv(seq![0x23u8, 0x80, 0x03, 0x03, 0x00, 0x0A, 0x3B, 0x00, 0x00], 0, 9) is None,
        // 11.2.1: unused bits that are not zero (the last octet 0xD1).
        read_bit_string(seq![0x03u8, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD1], 0, 9) is None,
        // 8.6.2.2: an unused-bits octet above 7.
        read_bit_string(seq![0x03u8, 0x02, 0x08, 0x00], 0, 4) is None,
        // 8.6.2.3: an empty bit string is `03 01 00`, with no unused bits.
        encode_bit_string(0, seq![]) == seq![0x03u8, 0x01, 0x00],
        read_bit_string(seq![0x03u8, 0x01, 0x00], 0, 3) == Some((0u8, 3nat, 3nat, 3nat)),
        read_bit_string(seq![0x03u8, 0x01, 0x01], 0, 3) is None,
        // 8.8: "05 00".
        encode_null() == seq![0x05u8, 0x00],
        read_null(seq![0x05u8, 0x00], 0, 2) == Some(2nat),
        // 8.8.2: a NULL with contents.
        read_null(seq![0x05u8, 0x01, 0x00], 0, 3) is None,
        // 8.9.3: SEQUENCE {name IA5String, ok BOOLEAN} {name "Smith", ok TRUE}:
        // 30 0A 16 05 "Smith" 01 01 FF.
        encode_sequence(encode_octets(IA5_STRING, smith()) + encode_boolean(true)) == seq![
            0x30u8, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF,
        ],
        expect_sequence(seq![0x30u8, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF], 0, 12) == Some(
            (2nat, 12nat),
        ),
        read_ia5_string(seq![0x30u8, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF], 2, 12) == Some(
            (4nat, 9nat),
        ),
        // 8.14.4, Type2 ::= [APPLICATION 3] IMPLICIT VisibleString: 43 05 "Jones".
        encode_tlv(application_3(), jones()) == seq![0x43u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73],
        read_tlv(seq![0x43u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 7) == Some(
            Tlv { tag: application_3(), cstart: 2, cend: 7 },
        ),
        // Type3 ::= [2] Type2 (explicit): A2 07 43 05 "Jones".
        encode_context(2, true, encode_tlv(application_3(), jones())) == seq![
            0xA2u8, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73,
        ],
        read_optional_explicit(seq![0xA2u8, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 9, 2) == Some(
            Some((2nat, 9nat)),
        ),
        // Type4 ::= [APPLICATION 7] IMPLICIT Type3: 67 07 43 05 "Jones".
        encode_tlv(application_7(), encode_tlv(application_3(), jones())) == seq![
            0x67u8, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73,
        ],
        // Type5 ::= [2] IMPLICIT Type2: 82 05 "Jones".
        encode_context(2, false, jones()) == seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73],
        read_optional_context(seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 7, 2) == Some(
            Some((false, 2nat, 7nat)),
        ),
        // The component is absent when the next tag is another one, and when
        // nothing is left.
        read_optional_context(seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 7, 3) == Some(None::<(bool, nat, nat)>),
        read_optional_context(seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 7, 7, 2) == Some(None::<(bool, nat, nat)>),
        // 8.19.5: {joint-iso-itu-t 999 3}: 06 03 88 37 03.
        encode_oid(seq![2nat, 999, 3]) == seq![0x06u8, 0x03, 0x88, 0x37, 0x03],
        read_oid(seq![0x06u8, 0x03, 0x88, 0x37, 0x03], 0, 5) == Some((seq![2nat, 999, 3], 5nat)),
        // The 2002 edition's {2 100 3}: first subidentifier 180 = 81 34.
        encode_oid(seq![2nat, 100, 3]) == seq![0x06u8, 0x03, 0x81, 0x34, 0x03],
        read_oid(seq![0x06u8, 0x03, 0x81, 0x34, 0x03], 0, 5) == Some((seq![2nat, 100, 3], 5nat)),
        // 8.19.2: a subidentifier padded with 80 is not the fewest octets.
        read_oid(seq![0x06u8, 0x04, 0x80, 0x81, 0x34, 0x03], 0, 6) is None,
        // A subidentifier whose last octet has bit 8 set never ends.
        read_oid(seq![0x06u8, 0x02, 0x88, 0xB7], 0, 4) is None,
{
    assert(encode_length(38) =~= seq![0x26u8]) by (compute_only);
    assert(read_length(seq![0x26u8], 0, 1) == Some((38nat, 1nat))) by (compute_only);
    assert(encode_length(201) =~= seq![0x81u8, 0xC9]) by (compute_only);
    assert(read_length(seq![0x81u8, 0xC9], 0, 2) == Some((201nat, 2nat))) by (compute_only);
    assert(read_length(seq![0x81u8, 0x26], 0, 2) is None) by (compute_only);
    assert(read_length(seq![0x80u8], 0, 1) is None) by (compute_only);
    assert(read_length(seq![0xFFu8], 0, 1) is None) by (compute_only);
    assert(read_length(seq![0x82u8, 0x00, 0xC9], 0, 3) is None) by (compute_only);
    assert(encode_boolean(true) =~= seq![0x01u8, 0x01, 0xFF]) by (compute_only);
    assert(read_boolean(seq![0x01u8, 0x01, 0xFF], 0, 3) == Some((true, 3nat))) by (compute_only);
    assert(encode_boolean(false) =~= seq![0x01u8, 0x01, 0x00]) by (compute_only);
    assert(read_boolean(seq![0x01u8, 0x01, 0x01], 0, 3) is None) by (compute_only);
    assert(encode_bit_string(4, seq![0x0Au8, 0x3B, 0x5F, 0x29, 0x1C, 0xD0]) =~= seq![
        0x03u8, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0,
    ]) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD0], 0, 9) == Some(
        (4u8, 3nat, 9nat, 9nat),
    )) by (compute_only);
    assert(read_tlv(seq![0x23u8, 0x80, 0x03, 0x03, 0x00, 0x0A, 0x3B, 0x00, 0x00], 0, 9) is None) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x07, 0x04, 0x0A, 0x3B, 0x5F, 0x29, 0x1C, 0xD1], 0, 9) is None) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x02, 0x08, 0x00], 0, 4) is None) by (compute_only);
    assert(encode_bit_string(0, seq![]) =~= seq![0x03u8, 0x01, 0x00]) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x01, 0x00], 0, 3) == Some((0u8, 3nat, 3nat, 3nat))) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x01, 0x01], 0, 3) is None) by (compute_only);
    assert(encode_null() =~= seq![0x05u8, 0x00]) by (compute_only);
    assert(read_null(seq![0x05u8, 0x00], 0, 2) == Some(2nat)) by (compute_only);
    assert(read_null(seq![0x05u8, 0x01, 0x00], 0, 3) is None) by (compute_only);
    assert(encode_sequence(encode_octets(IA5_STRING, smith()) + encode_boolean(true)) =~= seq![
        0x30u8, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF,
    ]) by (compute_only);
    assert(expect_sequence(seq![0x30u8, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF], 0, 12) == Some(
        (2nat, 12nat),
    )) by (compute_only);
    assert(read_ia5_string(seq![0x30u8, 0x0A, 0x16, 0x05, 0x53, 0x6D, 0x69, 0x74, 0x68, 0x01, 0x01, 0xFF], 2, 12) == Some(
        (4nat, 9nat),
    )) by (compute_only);
    assert(encode_tlv(application_3(), jones()) =~= seq![0x43u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]) by (compute_only);
    assert(read_tlv(seq![0x43u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 7) == Some(
        Tlv { tag: application_3(), cstart: 2, cend: 7 },
    )) by (compute_only);
    assert(encode_context(2, true, encode_tlv(application_3(), jones())) =~= seq![
        0xA2u8, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73,
    ]) by (compute_only);
    assert(read_optional_explicit(seq![0xA2u8, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 9, 2) == Some(
        Some((2nat, 9nat)),
    )) by (compute_only);
    assert(encode_tlv(application_7(), encode_tlv(application_3(), jones())) =~= seq![
        0x67u8, 0x07, 0x43, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73,
    ]) by (compute_only);
    assert(encode_context(2, false, jones()) =~= seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73]) by (compute_only);
    assert(read_optional_context(seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 7, 2) == Some(
        Some((false, 2nat, 7nat)),
    )) by (compute_only);
    assert(read_optional_context(seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 0, 7, 3) == Some(None::<(bool, nat, nat)>)) by (compute_only);
    assert(read_optional_context(seq![0x82u8, 0x05, 0x4A, 0x6F, 0x6E, 0x65, 0x73], 7, 7, 2) == Some(None::<(bool, nat, nat)>)) by (compute_only);
    assert(encode_oid(seq![2nat, 999, 3]) =~= seq![0x06u8, 0x03, 0x88, 0x37, 0x03]) by (compute_only);
    assert(read_oid(seq![0x06u8, 0x03, 0x88, 0x37, 0x03], 0, 5) == Some((seq![2nat, 999, 3], 5nat))) by (compute_only);
    assert(encode_oid(seq![2nat, 100, 3]) =~= seq![0x06u8, 0x03, 0x81, 0x34, 0x03]) by (compute_only);
    assert(read_oid(seq![0x06u8, 0x03, 0x81, 0x34, 0x03], 0, 5) == Some((seq![2nat, 100, 3], 5nat))) by (compute_only);
    assert(read_oid(seq![0x06u8, 0x04, 0x80, 0x81, 0x34, 0x03], 0, 6) is None) by (compute_only);
    assert(read_oid(seq![0x06u8, 0x02, 0x88, 0xB7], 0, 4) is None) by (compute_only);
}

/// Kaliski's examples, with the `DigestInfo` prefix of RFC 8017.
pub proof fn lemma_examples_kaliski()
    ensures
        // §5.4: the DER encoding of the BIT STRING "011011100101110111" is
        // 03 04 06 6e 5d c0 (padded with zero bits); the BER padding "e0",
        // the long form of the length and the constructed encoding are not DER.
        encode_bit_string(6, seq![0x6Eu8, 0x5D, 0xC0]) == seq![0x03u8, 0x04, 0x06, 0x6E, 0x5D, 0xC0],
        read_bit_string(seq![0x03u8, 0x04, 0x06, 0x6E, 0x5D, 0xC0], 0, 6) == Some((6u8, 3nat, 6nat, 6nat)),
        read_bit_string(seq![0x03u8, 0x04, 0x06, 0x6E, 0x5D, 0xE0], 0, 6) is None,
        read_bit_string(seq![0x03u8, 0x81, 0x04, 0x06, 0x6E, 0x5D, 0xC0], 0, 7) is None,
        read_bit_string(seq![0x23u8, 0x09, 0x03, 0x03, 0x00, 0x6E, 0x5D, 0x03, 0x02, 0x06, 0xC0], 0, 11) is None,
        // §5.7 Table 3: INTEGER 0, 127, 128, 256, -128, -129.
        encode_integer_unsigned(seq![]) == seq![0x02u8, 0x01, 0x00],
        encode_integer_unsigned(seq![0x7Fu8]) == seq![0x02u8, 0x01, 0x7F],
        encode_integer_unsigned(seq![0x80u8]) == seq![0x02u8, 0x02, 0x00, 0x80],
        encode_integer_unsigned(seq![0x01u8, 0x00]) == seq![0x02u8, 0x02, 0x01, 0x00],
        read_integer(seq![0x02u8, 0x01, 0x00], 0, 3) == Some((false, 2nat, 3nat, 3nat)),
        read_integer(seq![0x02u8, 0x01, 0x7F], 0, 3) == Some((false, 2nat, 3nat, 3nat)),
        read_integer(seq![0x02u8, 0x02, 0x00, 0x80], 0, 4) == Some((false, 3nat, 4nat, 4nat)),
        read_integer(seq![0x02u8, 0x02, 0x01, 0x00], 0, 4) == Some((false, 2nat, 4nat, 4nat)),
        read_integer(seq![0x02u8, 0x01, 0x80], 0, 3) == Some((true, 2nat, 3nat, 3nat)),
        read_integer(seq![0x02u8, 0x02, 0xFF, 0x7F], 0, 4) == Some((true, 2nat, 4nat, 4nat)),
        integer_value(seq![0x80u8]) == -128,
        integer_value(seq![0xFFu8, 0x7F]) == -129,
        integer_value(seq![0x00u8, 0x80]) == 128,
        // Redundant leading octets (8.3.2): 00 7F, 00 00, FF FF, FF 80.
        read_integer(seq![0x02u8, 0x02, 0x00, 0x7F], 0, 4) is None,
        read_integer(seq![0x02u8, 0x02, 0x00, 0x00], 0, 4) is None,
        read_integer(seq![0x02u8, 0x02, 0xFF, 0xFF], 0, 4) is None,
        read_integer(seq![0x02u8, 0x02, 0xFF, 0x80], 0, 4) is None,
        read_integer(seq![0x02u8, 0x00], 0, 2) is None,
        // §5.8: NULL is 05 00 in DER, never 05 81 00.
        read_null(seq![0x05u8, 0x81, 0x00], 0, 3) is None,
        // §5.9: {1 2 840 113549}: 06 06 2a 86 48 86 f7 0d.
        encode_oid(seq![1nat, 2, 840, 113549]) == seq![0x06u8, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D],
        read_oid(seq![0x06u8, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D], 0, 8) == Some(
            (seq![1nat, 2, 840, 113549], 8nat),
        ),
        // §5.10: the OCTET STRING 01 23 45 67 89 ab cd ef; the long length and
        // the constructed encoding are not DER.
        encode_octet_string(seq![0x01u8, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF]) == seq![
            0x04u8, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
        ],
        read_octet_string(seq![0x04u8, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF], 0, 10) == Some(
            (2nat, 10nat),
        ),
        read_octet_string(seq![0x04u8, 0x81, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF], 0, 11) is None,
        read_octet_string(
            seq![0x24u8, 0x0C, 0x04, 0x04, 0x01, 0x23, 0x45, 0x67, 0x04, 0x04, 0x89, 0xAB, 0xCD, 0xEF],
            0,
            14,
        ) is None,
        // §5.6: the IA5String "test1@rsa.com": 16 0d ...
        encode_octets(IA5_STRING, seq![0x74u8, 0x65, 0x73, 0x74, 0x31, 0x40, 0x72, 0x73, 0x61, 0x2E, 0x63, 0x6F, 0x6D]) == seq![
            0x16u8, 0x0D, 0x74, 0x65, 0x73, 0x74, 0x31, 0x40, 0x72, 0x73, 0x61, 0x2E, 0x63, 0x6F, 0x6D,
        ],
        // §5.17: the UTCTime "910506234540Z": 17 0d ...
        encode_octets(UTC_TIME, seq![0x39u8, 0x31, 0x30, 0x35, 0x30, 0x36, 0x32, 0x33, 0x34, 0x35, 0x34, 0x30, 0x5A]) == seq![
            0x17u8, 0x0D, 0x39, 0x31, 0x30, 0x35, 0x30, 0x36, 0x32, 0x33, 0x34, 0x35, 0x34, 0x30, 0x5A,
        ],
        // §6.2.6: the X.501 Name of the Guide, a SEQUENCE of three SETs of
        // SEQUENCE { OID, PrintableString }: 30 42 31 0b 30 09 ...
        encode_sequence(
            encode_set(encode_sequence(encode_oid(seq![2nat, 5, 4, 6]) + encode_octets(PRINTABLE_STRING, seq![0x55u8, 0x53])))
                + encode_set(
                encode_sequence(
                    encode_oid(seq![2nat, 5, 4, 10]) + encode_octets(
                        PRINTABLE_STRING,
                        seq![
                            0x45u8, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x20, 0x4F, 0x72, 0x67, 0x61, 0x6E, 0x69, 0x7A, 0x61, 0x74,
                            0x69, 0x6F, 0x6E,
                        ],
                    ),
                ),
            ) + encode_set(
                encode_sequence(
                    encode_oid(seq![2nat, 5, 4, 3]) + encode_octets(
                        PRINTABLE_STRING,
                        seq![0x54u8, 0x65, 0x73, 0x74, 0x20, 0x55, 0x73, 0x65, 0x72, 0x20, 0x31],
                    ),
                ),
            ),
        ) == seq![
            0x30u8, 0x42, 0x31, 0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x55, 0x53, 0x31, 0x1D, 0x30, 0x1B, 0x06,
            0x03, 0x55, 0x04, 0x0A, 0x13, 0x14, 0x45, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x20, 0x4F, 0x72, 0x67, 0x61, 0x6E, 0x69,
            0x7A, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x31, 0x14, 0x30, 0x12, 0x06, 0x03, 0x55, 0x04, 0x03, 0x13, 0x0B, 0x54, 0x65, 0x73,
            0x74, 0x20, 0x55, 0x73, 0x65, 0x72, 0x20, 0x31,
        ],
        // RFC 8017 §9.2 Note 1: the `DigestInfo` of SHA-256 is
        // 30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20 || H.
        encode_digest_info(
            seq![2nat, 16, 840, 1, 101, 3, 4, 2, 1],
            seq![
                0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
                31,
            ],
        ) == seq![
            0x30u8, 0x31, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20, 0, 1,
            2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
        ],
{
    assert(encode_bit_string(6, seq![0x6Eu8, 0x5D, 0xC0]) =~= seq![0x03u8, 0x04, 0x06, 0x6E, 0x5D, 0xC0]) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x04, 0x06, 0x6E, 0x5D, 0xC0], 0, 6) == Some((6u8, 3nat, 6nat, 6nat))) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x04, 0x06, 0x6E, 0x5D, 0xE0], 0, 6) is None) by (compute_only);
    assert(read_bit_string(seq![0x03u8, 0x81, 0x04, 0x06, 0x6E, 0x5D, 0xC0], 0, 7) is None) by (compute_only);
    assert(read_bit_string(seq![0x23u8, 0x09, 0x03, 0x03, 0x00, 0x6E, 0x5D, 0x03, 0x02, 0x06, 0xC0], 0, 11) is None) by (compute_only);
    assert(encode_integer_unsigned(seq![]) =~= seq![0x02u8, 0x01, 0x00]) by (compute_only);
    assert(encode_integer_unsigned(seq![0x7Fu8]) =~= seq![0x02u8, 0x01, 0x7F]) by (compute_only);
    assert(encode_integer_unsigned(seq![0x80u8]) =~= seq![0x02u8, 0x02, 0x00, 0x80]) by (compute_only);
    assert(encode_integer_unsigned(seq![0x01u8, 0x00]) =~= seq![0x02u8, 0x02, 0x01, 0x00]) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x01, 0x00], 0, 3) == Some((false, 2nat, 3nat, 3nat))) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x01, 0x7F], 0, 3) == Some((false, 2nat, 3nat, 3nat))) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0x00, 0x80], 0, 4) == Some((false, 3nat, 4nat, 4nat))) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0x01, 0x00], 0, 4) == Some((false, 2nat, 4nat, 4nat))) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x01, 0x80], 0, 3) == Some((true, 2nat, 3nat, 3nat))) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0xFF, 0x7F], 0, 4) == Some((true, 2nat, 4nat, 4nat))) by (compute_only);
    assert(integer_value(seq![0x80u8]) == -128) by (compute_only);
    assert(integer_value(seq![0xFFu8, 0x7F]) == -129) by (compute_only);
    assert(integer_value(seq![0x00u8, 0x80]) == 128) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0x00, 0x7F], 0, 4) is None) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0x00, 0x00], 0, 4) is None) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0xFF, 0xFF], 0, 4) is None) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x02, 0xFF, 0x80], 0, 4) is None) by (compute_only);
    assert(read_integer(seq![0x02u8, 0x00], 0, 2) is None) by (compute_only);
    assert(read_null(seq![0x05u8, 0x81, 0x00], 0, 3) is None) by (compute_only);
    assert(encode_oid(seq![1nat, 2, 840, 113549]) =~= seq![0x06u8, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D]) by (compute_only);
    assert(read_oid(seq![0x06u8, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D], 0, 8) == Some(
        (seq![1nat, 2, 840, 113549], 8nat),
    )) by (compute_only);
    assert(encode_octet_string(seq![0x01u8, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF]) =~= seq![
        0x04u8, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF,
    ]) by (compute_only);
    assert(read_octet_string(seq![0x04u8, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF], 0, 10) == Some(
        (2nat, 10nat),
    )) by (compute_only);
    assert(read_octet_string(seq![0x04u8, 0x81, 0x08, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB, 0xCD, 0xEF], 0, 11) is None) by (compute_only);
    assert(read_octet_string(
        seq![0x24u8, 0x0C, 0x04, 0x04, 0x01, 0x23, 0x45, 0x67, 0x04, 0x04, 0x89, 0xAB, 0xCD, 0xEF],
        0,
        14,
    ) is None) by (compute_only);
    assert(encode_octets(IA5_STRING, seq![0x74u8, 0x65, 0x73, 0x74, 0x31, 0x40, 0x72, 0x73, 0x61, 0x2E, 0x63, 0x6F, 0x6D]) =~= seq![
        0x16u8, 0x0D, 0x74, 0x65, 0x73, 0x74, 0x31, 0x40, 0x72, 0x73, 0x61, 0x2E, 0x63, 0x6F, 0x6D,
    ]) by (compute_only);
    assert(encode_octets(UTC_TIME, seq![0x39u8, 0x31, 0x30, 0x35, 0x30, 0x36, 0x32, 0x33, 0x34, 0x35, 0x34, 0x30, 0x5A]) =~= seq![
        0x17u8, 0x0D, 0x39, 0x31, 0x30, 0x35, 0x30, 0x36, 0x32, 0x33, 0x34, 0x35, 0x34, 0x30, 0x5A,
    ]) by (compute_only);
    assert(encode_sequence(
        encode_set(encode_sequence(encode_oid(seq![2nat, 5, 4, 6]) + encode_octets(PRINTABLE_STRING, seq![0x55u8, 0x53])))
            + encode_set(
            encode_sequence(
                encode_oid(seq![2nat, 5, 4, 10]) + encode_octets(
                    PRINTABLE_STRING,
                    seq![
                        0x45u8, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x20, 0x4F, 0x72, 0x67, 0x61, 0x6E, 0x69, 0x7A, 0x61, 0x74, 0x69,
                        0x6F, 0x6E,
                    ],
                ),
            ),
        ) + encode_set(
            encode_sequence(
                encode_oid(seq![2nat, 5, 4, 3]) + encode_octets(
                    PRINTABLE_STRING,
                    seq![0x54u8, 0x65, 0x73, 0x74, 0x20, 0x55, 0x73, 0x65, 0x72, 0x20, 0x31],
                ),
            ),
        ),
    ) =~= seq![
        0x30u8, 0x42, 0x31, 0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x55, 0x53, 0x31, 0x1D, 0x30, 0x1B, 0x06,
        0x03, 0x55, 0x04, 0x0A, 0x13, 0x14, 0x45, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x20, 0x4F, 0x72, 0x67, 0x61, 0x6E, 0x69,
        0x7A, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x31, 0x14, 0x30, 0x12, 0x06, 0x03, 0x55, 0x04, 0x03, 0x13, 0x0B, 0x54, 0x65, 0x73,
        0x74, 0x20, 0x55, 0x73, 0x65, 0x72, 0x20, 0x31,
    ]) by (compute_only);
    assert(encode_digest_info(
        seq![2nat, 16, 840, 1, 101, 3, 4, 2, 1],
        seq![
            0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
        ],
    ) =~= seq![
        0x30u8, 0x31, 0x30, 0x0D, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20, 0, 1, 2,
        3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    ]) by (compute_only);
}

} // verus!
