//! X.509 7.2.1's "the same value" (`requirements.rs`'s
//! `signature_algorithms_agree`) against `signature_algorithm/spec.rs`'s
//! `prepare_signature`.
//!
//! `theorem_signature_algorithms`: on `equivalence_domain`, the two
//! AlgorithmIdentifiers have one encoding exactly when `certificate/spec.rs`
//! reads them to one value. That needs DER's uniqueness in both directions,
//! so it is proven, not assumed ([`lemma_algorithm_bytes`]).
//!
//! `theorem_prepare_signature`: for one value, `prepare_signature` adds only
//! the profile's refusals.
//!
//! **Excluded, by the theorem's form: RSA with NULL on one side and absent on
//! the other.** `prepare_signature` accepts it (`signature_algorithm/spec.rs`:
//! "NULL and absent are treated as semantically equivalent"), and
//! `tests/signature_algorithm.rs` tests that on purpose. X.509 7.2.1 says "the
//! same value" and RFC 5280 §4.1.1.2 "the same algorithm identifier", and
//! RFC 4055 §5's permission to omit NULL is about one identifier, not about
//! two that differ, so **the standards' letter is with the transcription**.
//! `rustls-webpki` compares octets and refuses it, with a comment that
//! mozilla::pkix compares normalized values. The crate's reading is a stated
//! compatibility choice, not corrected here; whether to keep it is the
//! maintainer's call.
//!
//! Also outside: `classify`'s refusal of a known OID with other parameters,
//! and of unused bits in a supported signature. Those are profile rules X.509
//! leaves to the algorithm.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::signature_algorithm::spec as g;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// The one DER encoding of an AlgorithmIdentifier's value.
pub open spec fn algorithm_bytes(a: c::AlgorithmIdentifier) -> Seq<u8> {
    d::encode_sequence(
        d::encode_oid(a.oid) + match a.parameters_der {
            Some(p) => p,
            None => Seq::<u8>::empty(),
        },
    )
}

/// What `parse_algorithm_identifier` read is that encoding.
pub proof fn lemma_algorithm_canonical(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        c::parse_algorithm_identifier(b, pos, end) is Some,
    ensures
        sl(b, pos, c::parse_algorithm_identifier(b, pos, end)->Some_0.1) == algorithm_bytes(
            c::parse_algorithm_identifier(b, pos, end)->Some_0.0,
        ),
{
    let (a, next) = c::parse_algorithm_identifier(b, pos, end)->Some_0;
    let (start, finish) = d::expect_sequence(b, pos, end)->Some_0;
    clazel_der::lemmas_typed::lemma_encode_sequence_expect_sequence(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    clazel_der::lemmas_typed::lemma_encode_oid_read_oid(b, start, finish);
    let (oid, after) = d::read_oid(b, start, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
    assert(next == finish);
    let rest = match a.parameters_der {
        Some(p) => p,
        None => Seq::<u8>::empty(),
    };
    assert(rest =~= sl(b, after, finish));
    assert(sl(b, start, finish) =~= sl(b, start, after) + rest);
}

/// An element of a list of encodings reads alone.
pub proof fn lemma_element_reads(v: Seq<u8>, l: Seq<i::Tlv>, m: int)
    requires
        v.len() < two64(),
        i::parse_tlvs(v) == Some(l),
        0 <= m < l.len(),
        tag_fits(l[m]),
    ensures
        i::parse_single(l[m].encoding) == Some(l[m]),
    decreases v.len(),
{
    let u = i::parse_tlv(v)->Some_0;
    let size = u.encoding.len();
    let tail = v.subrange(size as int, v.len() as int);
    let rest = i::parse_tlvs(tail)->Some_0;
    assert(l =~= seq![u] + rest);
    if m > 0 {
        assert(l[m] == rest[m - 1]);
        lemma_element_reads(tail, rest, m - 1);
    } else {
        assert(l[0] == u);
        assert(sl(v, 0, v.len()) =~= v);
        lemma_tlv(v, 0, v.len());
        lemma_parse_tlv_not_reserved(v);
        lemma_tlv_alone(v, 0, v.len());
        let r = d::read_tlv(v, 0, v.len())->Some_0;
        assert(sl(v, 0, r.cend) == u.encoding);
    }
}

/// **The encoding is a function of the value.** An AlgorithmIdentifier's
/// octets are `algorithm_bytes` of what `certificate/spec.rs` reads from it.
pub proof fn lemma_algorithm_bytes(t: i::Tlv, x: s::AlgorithmIdentifier, a: c::AlgorithmIdentifier)
    requires
        i::parse_single(t.encoding) == Some(t),
        t.encoding.len() < two64(),
        s::decode_algorithm_identifier(t) == Some(x),
        algorithm_in_domain(x),
        algorithm_agree(a, x),
    ensures
        x.encoding == algorithm_bytes(a),
{
    let b = t.encoding;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_algorithm_back(b, 0, len, t, x);
    lemma_algorithm_canonical(b, 0, len);
    let (a2, next) = c::parse_algorithm_identifier(b, 0, len)->Some_0;
    assert(a2.oid == a.oid);
    assert(a2.parameters_der == a.parameters_der);
    assert(a2 == a);
}

/// `algorithm_agree` is a function of the transcription's value.
pub proof fn lemma_agree_unique(a1: c::AlgorithmIdentifier, a2: c::AlgorithmIdentifier, x: s::AlgorithmIdentifier)
    requires
        algorithm_agree(a1, x),
        algorithm_agree(a2, x),
    ensures
        a1 == a2,
{
}

/// **`theorem_signature_algorithms`.**
#[verifier::spinoff_prover]
pub proof fn theorem_signature_algorithms(der: Seq<u8>)
    requires
        equivalence_domain(der),
        crate_decode(der) is Some,
    ensures
        r::signature_algorithms_agree(s::decode_certificate(der)->Some_0) == (
        crate_decode(der)->Some_0.tbs.signature == crate_decode(der)->Some_0.envelope.signature_algorithm),
{
    hide(s::decode_tbs_certificate);
    hide(s::decode_algorithm_identifier);
    hide(crate_decode);
    theorem_certificate_equivalence(der);
    let a = crate_decode(der)->Some_0;
    let y = s::decode_certificate(der)->Some_0;
    lemma_certificate_opens(der, y);
    let u = i::parse_single(der)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    let b = y.to_be_signed;
    lemma_tbs_opens(l[0], b);
    let e0 = s::sequence_elements(l[0])->Some_0;
    let m = s::after_version(e0);
    let t1 = e0[(m + 1) as int];
    let t2 = l[1];
    lemma_algorithm_tag(t1);
    lemma_algorithm_tag(t2);
    lemma_contents_length(der, u);
    lemma_element_length(u.contents, l, 0);
    lemma_element_length(u.contents, l, 1);
    lemma_element_reads(u.contents, l, 1);
    lemma_tbs_sequence(l[0], b);
    lemma_element_reads(u.contents, l, 0);
    lemma_contents_length(l[0].encoding, l[0]);
    lemma_element_length(l[0].contents, e0, (m + 1) as int);
    lemma_element_reads(l[0].contents, e0, (m + 1) as int);
    lemma_algorithm_encoding(t1);
    lemma_algorithm_encoding(t2);
    lemma_algorithm_bytes(t1, b.signature, a.tbs.signature);
    lemma_algorithm_bytes(t2, y.algorithm_identifier, a.envelope.signature_algorithm);
    if r::signature_algorithms_agree(y) {
        assert(t1.encoding == t2.encoding);
        assert(t1 == t2);
        lemma_agree_unique(a.tbs.signature, a.envelope.signature_algorithm, b.signature);
    }
}

/// `encoding` is the encoding's.
pub proof fn lemma_algorithm_encoding(t: i::Tlv)
    requires
        s::decode_algorithm_identifier(t) is Some,
    ensures
        s::decode_algorithm_identifier(t)->Some_0.encoding == t.encoding,
{
}

/// **`theorem_prepare_signature`.** For one AlgorithmIdentifier in both places,
/// `prepare_signature` refuses only what the profile refuses.
pub proof fn theorem_prepare_signature(a: c::AlgorithmIdentifier, tbs: Seq<u8>, bits: Seq<u8>, unused: u8)
    ensures
        (g::prepare_signature(a, a, tbs, bits, unused) is Some) == (g::classify(a) is Some && (!(g::classify(
            a,
        )->Some_0 is Unsupported) ==> unused == 0)),
{
    assert(a.oid =~= a.oid);
}

} // verus!
