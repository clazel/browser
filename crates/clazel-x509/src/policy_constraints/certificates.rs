//! Known answers for the PolicyConstraints spec (RFC 5280 §4.2.1.11), and the
//! theorems that the certified mutations in `mutations.json` contradict. Each
//! DER value is written out by hand from the ASN.1 of §4.2.1.11: `80` is
//! `[0]` and `81` is `[1]`, primitive and implicit over an INTEGER.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Both fields: requireExplicitPolicy 2 and inhibitPolicyMapping 3.
pub proof fn lemma_both_fields_are_decoded()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03]) is Some,
        parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03])
            .unwrap().require_explicit_policy == Some(seq![0x02u8]),
        parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03])
            .unwrap().inhibit_policy_mapping == Some(seq![0x03u8]),
{
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03]) is Some)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03])
        .unwrap().require_explicit_policy == Some(seq![0x02u8])) by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x02, 0x81, 0x01, 0x03])
        .unwrap().inhibit_policy_mapping == Some(seq![0x03u8])) by (compute_only);
}

/// Each field alone, and both zero.
pub proof fn lemma_each_field_alone_is_decoded()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x03, 0x80, 0x01, 0x00])
            == Some(PolicyConstraints {
                require_explicit_policy: Some(seq![0x00u8]), inhibit_policy_mapping: None }),
        parse_policy_constraints(seq![0x30u8, 0x03, 0x81, 0x01, 0x05])
            == Some(PolicyConstraints {
                require_explicit_policy: None, inhibit_policy_mapping: Some(seq![0x05u8]) }),
        parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x00, 0x81, 0x01, 0x00])
            == Some(PolicyConstraints {
                require_explicit_policy: Some(seq![0x00u8]),
                inhibit_policy_mapping: Some(seq![0x00u8]) }),
{
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x80, 0x01, 0x00])
        == Some(PolicyConstraints {
            require_explicit_policy: Some(seq![0x00u8]), inhibit_policy_mapping: None }))
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x81, 0x01, 0x05])
        == Some(PolicyConstraints {
            require_explicit_policy: None, inhibit_policy_mapping: Some(seq![0x05u8]) }))
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x00, 0x81, 0x01, 0x00])
        == Some(PolicyConstraints {
            require_explicit_policy: Some(seq![0x00u8]),
            inhibit_policy_mapping: Some(seq![0x00u8]) })) by (compute_only);
}

/// RFC 5280 §4.2.1.11: an empty SEQUENCE is refused (modelling choice).
pub proof fn lemma_empty_policy_constraints_is_refused()
    ensures parse_policy_constraints(seq![0x30u8, 0x00]) is None
{
    assert(parse_policy_constraints(seq![0x30u8, 0x00]) is None) by (compute_only);
}

/// SkipCerts is INTEGER (0..MAX): a negative value is refused.
pub proof fn lemma_negative_skip_certs_is_refused()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x03, 0x80, 0x01, 0x80]) is None,
        parse_policy_constraints(seq![0x30u8, 0x03, 0x81, 0x01, 0xFF]) is None,
{
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x80, 0x01, 0x80]) is None) by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x81, 0x01, 0xFF]) is None) by (compute_only);
}

/// X.690 §8.3.2: a redundant leading 0x00 (or 0xFF) is refused; a 0x00 that
/// keeps bit 8 clear is the sign pad and is dropped from the magnitude.
pub proof fn lemma_integer_contents_are_minimal()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0x00, 0x05]) is None,
        parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0xFF, 0x80]) is None,
        parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0x00, 0x80]).unwrap()
            .require_explicit_policy == Some(seq![0x80u8]),
        parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0x00, 0x80]).unwrap()
            .require_explicit_policy.unwrap().len() == 1,
{
    assert(parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0x00, 0x05]) is None)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0xFF, 0x80]) is None)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0x00, 0x80]).unwrap()
        .require_explicit_policy == Some(seq![0x80u8])) by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x04, 0x80, 0x02, 0x00, 0x80]).unwrap()
        .require_explicit_policy.unwrap().len() == 1) by (compute_only);
}

/// The size bound: 2^32 - 1 (four magnitude octets, after the sign pad) is
/// accepted and 2^32 (five) is refused.
pub proof fn lemma_skip_certs_below_2_pow_32()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x07, 0x80, 0x05, 0x00, 0xFF, 0xFF, 0xFF, 0xFF]) is Some,
        parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x04, 0x7F, 0xFF, 0xFF, 0xFF]) is Some,
        parse_policy_constraints(seq![0x30u8, 0x07, 0x80, 0x05, 0x01, 0x00, 0x00, 0x00, 0x00]) is None,
        parse_policy_constraints(seq![0x30u8, 0x0A, 0x81, 0x08,
            0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) is None,
{
    assert(parse_policy_constraints(seq![0x30u8, 0x07, 0x80, 0x05, 0x00, 0xFF, 0xFF, 0xFF, 0xFF])
        is Some) by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x04, 0x7F, 0xFF, 0xFF, 0xFF]) is Some)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x07, 0x80, 0x05, 0x01, 0x00, 0x00, 0x00, 0x00])
        is None) by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x0A, 0x81, 0x08,
        0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) is None) by (compute_only);
}

/// X.690 §8.14.4: the fields are the primitive implicit `[0]` and `[1]`. A
/// universal INTEGER, a constructed `[0]`, and another context tag are refused.
pub proof fn lemma_wrong_tags_are_refused()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is None,
        parse_policy_constraints(seq![0x30u8, 0x05, 0xA0, 0x03, 0x02, 0x01, 0x00]) is None,
        parse_policy_constraints(seq![0x30u8, 0x03, 0x82, 0x01, 0x00]) is None,
{
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x02, 0x01, 0x00]) is None) by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x05, 0xA0, 0x03, 0x02, 0x01, 0x00]) is None)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x82, 0x01, 0x00]) is None) by (compute_only);
}

/// The ASN.1 order is `[0]` then `[1]`, each at most once.
pub proof fn lemma_fields_are_ordered_and_unique()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x06, 0x81, 0x01, 0x03, 0x80, 0x01, 0x02]) is None,
        parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x01, 0x80, 0x01, 0x02]) is None,
        parse_policy_constraints(seq![0x30u8, 0x06, 0x81, 0x01, 0x01, 0x81, 0x01, 0x02]) is None,
{
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x81, 0x01, 0x03, 0x80, 0x01, 0x02]) is None)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x80, 0x01, 0x01, 0x80, 0x01, 0x02]) is None)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x06, 0x81, 0x01, 0x01, 0x81, 0x01, 0x02]) is None)
        by (compute_only);
}

/// Nothing may follow the fields inside the SEQUENCE or the SEQUENCE itself.
pub proof fn lemma_trailing_bytes_are_refused()
    ensures
        parse_policy_constraints(seq![0x30u8, 0x05, 0x80, 0x01, 0x00, 0x05, 0x00]) is None,
        parse_policy_constraints(seq![0x30u8, 0x03, 0x80, 0x01, 0x00, 0x05, 0x00]) is None,
{
    assert(parse_policy_constraints(seq![0x30u8, 0x05, 0x80, 0x01, 0x00, 0x05, 0x00]) is None)
        by (compute_only);
    assert(parse_policy_constraints(seq![0x30u8, 0x03, 0x80, 0x01, 0x00, 0x05, 0x00]) is None)
        by (compute_only);
}

/// The OID is id-ce-policyConstraints, 2.5.29.36.
pub proof fn lemma_policy_constraints_oid()
    ensures policy_constraints_oid() =~= seq![2nat, 5nat, 29nat, 36nat]
{
}

} // verus!
