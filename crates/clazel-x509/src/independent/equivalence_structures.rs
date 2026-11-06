//! `AlgorithmIdentifier`, `SubjectPublicKeyInfo` and `Validity` of
//! `independent/structures.rs` against `certificate/spec.rs`, `spki/spec.rs`
//! and `tbs/spec.rs`. The domain is explained in `equivalence.rs`.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_time::*;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::certificate::spec as c;
#[cfg(verus_only)]
use crate::spki::spec as k;
#[cfg(verus_only)]
use crate::time::spec as t;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// One encoding at a shorter end.
// ---------------------------------------------------------------------

/// What `parse_tlv` reads from a longer slice, `parse_single` reads from just
/// the encoding.
pub proof fn lemma_tlv_alone(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
    ensures
        i::parse_tlv(sl(b, pos, end)) is Some,
        i::parse_single(sl(b, pos, d::read_tlv(b, pos, end)->Some_0.cend)) == i::parse_tlv(sl(b, pos, end)),
{
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    clazel_der::lemmas_overread::lemma_read_tlv_no_overread(b, b, pos, end, r.cend);
    lemma_tlv(b, pos, end);
    lemma_tlv(b, pos, r.cend);
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    let v = i::parse_tlv(sl(b, pos, r.cend))->Some_0;
    assert(u == v);
}

// ---------------------------------------------------------------------
// BIT STRING and OCTET STRING at a position.
// ---------------------------------------------------------------------

/// A BIT STRING at `pos`: the two agree exactly.
pub proof fn lemma_read_bit_string(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match d::read_bit_string(b, pos, end) {
            Some((unused, start, finish, next)) => {
                &&& d::read_tlv(b, pos, end) is Some
                &&& !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag)
                &&& d::read_tlv(b, pos, end)->Some_0.cend == next
                &&& pos < start <= finish <= next <= end
                &&& i::parse_tlv(sl(b, pos, end)) is Some
                &&& i::decode_bit_string(i::parse_tlv(sl(b, pos, end))->Some_0) == Some(
                    i::BitString { octets: sl(b, start, finish), unused: unused as nat },
                )
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => i::decode_bit_string(u) is None,
                None => true,
            },
        },
{
    lemma_tlv(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some(r) = d::read_tlv(b, pos, end) {
        let con = sl(b, r.cstart, r.cend);
        lemma_bit_string_contents(con);
        if !tag_is_reserved(r.tag) {
            let u = i::parse_tlv(sl(b, pos, end))->Some_0;
            lemma_has_universal_tag(b, pos, r, u, d::BIT_STRING, false);
            if d::bit_string_contents_ok(con) {
                assert(con.subrange(1, con.len() as int) =~= sl(b, r.cstart + 1, r.cend));
            }
        }
    } else {
        if let Some(u) = i::parse_tlv(sl(b, pos, end)) {
            assert(i::decode_bit_string(u) is Some ==> tag_fits(u));
        }
    }
}

/// An OCTET STRING at `pos`: the two agree exactly.
pub proof fn lemma_read_octet_string(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match d::read_octet_string(b, pos, end) {
            Some((start, finish)) => {
                &&& d::read_tlv(b, pos, end) is Some
                &&& !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag)
                &&& d::read_tlv(b, pos, end)->Some_0.cend == finish
                &&& pos < start <= finish <= end
                &&& i::parse_tlv(sl(b, pos, end)) is Some
                &&& i::decode_octet_string(i::parse_tlv(sl(b, pos, end))->Some_0) == Some(sl(b, start, finish))
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => i::decode_octet_string(u) is None,
                None => true,
            },
        },
{
    lemma_tlv(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some(r) = d::read_tlv(b, pos, end) {
        if !tag_is_reserved(r.tag) {
            let u = i::parse_tlv(sl(b, pos, end))->Some_0;
            lemma_has_universal_tag(b, pos, r, u, d::OCTET_STRING, false);
        }
    } else {
        if let Some(u) = i::parse_tlv(sl(b, pos, end)) {
            assert(i::decode_octet_string(u) is Some ==> tag_fits(u));
        }
    }
}

// ---------------------------------------------------------------------
// AlgorithmIdentifier.
// ---------------------------------------------------------------------

/// The two values of an AlgorithmIdentifier agree.
pub open spec fn algorithm_agree(a: c::AlgorithmIdentifier, x: s::AlgorithmIdentifier) -> bool {
    &&& a.oid == x.algorithm
    &&& match (a.parameters_der, x.parameters) {
        (None, None) => true,
        (Some(p), Some(q)) => p == q.encoding,
        _ => false,
    }
}

/// `parameters` that do not start with the reserved tag universal 0.
pub open spec fn parameters_plain(a: c::AlgorithmIdentifier) -> bool {
    match a.parameters_der {
        Some(p) => p.len() > 0 && p[0] != 0x00 && p[0] != 0x20,
        None => true,
    }
}

/// An AlgorithmIdentifier `certificate/spec.rs` reads (excluded: an addition,
/// a tag number over 16383 in `parameters`, a subidentifier of 2^64 or more).
pub open spec fn algorithm_in_domain(x: s::AlgorithmIdentifier) -> bool {
    &&& x.additions.len() == 0
    &&& oid_fits(x.algorithm)
    &&& match x.parameters {
        Some(q) => tag_fits(q),
        None => true,
    }
}

/// Universal 0 is exactly the first octets 0x00 and 0x20.
pub proof fn lemma_reserved_first_octet(b: Seq<u8>, pos: nat, end: nat)
    requires
        d::read_tlv(b, pos, end) is Some,
    ensures
        tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag) == (b[pos as int] == 0x00 || b[pos as int]
            == 0x20),
{
    clazel_der::lemmas::lemma_read_identifier_bounds(b, pos, end);
    let o = b[pos as int];
    let (tag, n) = d::read_identifier(b, pos, end)->Some_0;
    if o % 32 == 31 {
        // The high form is for numbers from 31.
        assert(tag.number >= 31);
    }
}

/// An AlgorithmIdentifier, from `certificate/spec.rs` to `structures.rs`.
pub proof fn lemma_algorithm_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        c::parse_algorithm_identifier(b, pos, end) is Some,
        parameters_plain(c::parse_algorithm_identifier(b, pos, end)->Some_0.0),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == c::parse_algorithm_identifier(b, pos, end)->Some_0.1,
        pos < c::parse_algorithm_identifier(b, pos, end)->Some_0.1 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        s::decode_algorithm_identifier(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        algorithm_agree(
            c::parse_algorithm_identifier(b, pos, end)->Some_0.0,
            s::decode_algorithm_identifier(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        algorithm_in_domain(s::decode_algorithm_identifier(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
{
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let (start, finish) = (r.cstart, r.cend);
    lemma_read_oid(b, start, finish);
    let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
    lemma_tlvs_empty(b, finish);
    let none = Seq::<i::Tlv>::empty();
    if after_oid == finish {
        assert(sl(b, after_oid, finish) =~= sl(b, finish, finish));
        lemma_tlvs_cons(b, start, finish, none);
        let ou = i::parse_tlv(sl(b, start, finish))->Some_0;
        let e = seq![ou] + none;
        lemma_sequence_fwd(b, pos, end, e);
        assert(e[0] == ou);
        assert(e.len() == 1);
    } else {
        let v = d::read_tlv(b, after_oid, finish)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, after_oid, finish);
        let a = c::parse_algorithm_identifier(b, pos, end)->Some_0.0;
        assert(a.parameters_der == Some(sl(b, after_oid, finish)));
        assert(sl(b, after_oid, finish)[0] == b[after_oid as int]);
        lemma_reserved_first_octet(b, after_oid, finish);
        lemma_tlvs_cons(b, after_oid, finish, none);
        lemma_tlv(b, after_oid, finish);
        let vu = i::parse_tlv(sl(b, after_oid, finish))->Some_0;
        lemma_tlvs_cons(b, start, finish, seq![vu] + none);
        let ou = i::parse_tlv(sl(b, start, finish))->Some_0;
        let e = seq![ou] + (seq![vu] + none);
        lemma_sequence_fwd(b, pos, end, e);
        assert(e[0] == ou);
        assert(e[1] == vu);
        assert(e.len() == 2);
    }
}

/// An AlgorithmIdentifier, from `structures.rs` to `certificate/spec.rs`.
pub proof fn lemma_algorithm_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, x: s::AlgorithmIdentifier)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        s::decode_algorithm_identifier(u) == Some(x),
        algorithm_in_domain(x),
    ensures
        c::parse_algorithm_identifier(b, pos, end) is Some,
        algorithm_agree(c::parse_algorithm_identifier(b, pos, end)->Some_0.0, x),
        c::parse_algorithm_identifier(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
{
    let e = s::sequence_elements(u)->Some_0;
    lemma_sequence_back(b, pos, end, u, e);
    let r = d::read_tlv(b, pos, end)->Some_0;
    let (start, finish) = (r.cstart, r.cend);
    assert(e.len() <= 2) by {
        assert(i::from_index(e, 2).len() == 0);
        if e.len() > 2 {
            assert(i::from_index(e, 2).len() == e.len() - 2);
        }
    }
    assert(tag_fits(e[0]));
    lemma_tlvs_head(b, start, finish, e);
    lemma_read_oid(b, start, finish);
    let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
    let rest = e.skip(1);
    lemma_tlvs_none_left(b, after_oid, finish, rest);
    if e.len() == 2 {
        assert(rest[0] == e[1]);
        lemma_tlvs_head(b, after_oid, finish, rest);
        let v = d::read_tlv(b, after_oid, finish)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, after_oid, finish);
        lemma_tlvs_none_left(b, v.cend, finish, rest.skip(1));
    }
}

// ---------------------------------------------------------------------
// SubjectPublicKeyInfo.
// ---------------------------------------------------------------------

/// The two values of a SubjectPublicKeyInfo agree.
pub open spec fn spki_agree(a: k::SubjectPublicKeyInfo, x: s::SubjectPublicKeyInfo) -> bool {
    &&& algorithm_agree(a.algorithm, x.algorithm)
    &&& a.subject_public_key_unused_bits as nat == x.subject_public_key.unused
    &&& a.subject_public_key_bits == x.subject_public_key.octets
}

/// **The RSA key profile** of `spki/spec.rs` (RFC 3279 §2.3.1, RFC 8017): for
/// `rsaEncryption`, NULL parameters, no unused bits and a well-formed
/// RSAPublicKey. X.509 leaves key syntax to the algorithm.
pub open spec fn rsa_profile(x: s::SubjectPublicKeyInfo) -> bool {
    k::is_rsa_encryption(x.algorithm.algorithm) ==> {
        &&& x.algorithm.parameters is Some
        &&& x.algorithm.parameters->Some_0.encoding == seq![0x05u8, 0x00u8]
        &&& x.subject_public_key.unused == 0
        &&& k::parse_rsa_public_key(x.subject_public_key.octets) is Some
    }
}

/// A SubjectPublicKeyInfo `spki/spec.rs` reads.
pub open spec fn spki_in_domain(x: s::SubjectPublicKeyInfo) -> bool {
    &&& x.additions.len() == 0
    &&& algorithm_in_domain(x.algorithm)
    &&& rsa_profile(x)
}

/// **`theorem_spki`, from `spki/spec.rs`.**
pub proof fn theorem_spki_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        k::parse_subject_public_key_info(input) is Some,
        parameters_plain(k::parse_subject_public_key_info(input)->Some_0.algorithm),
    ensures
        i::parse_single(input) is Some,
        s::decode_subject_public_key_info(i::parse_single(input)->Some_0) is Some,
        spki_agree(
            k::parse_subject_public_key_info(input)->Some_0,
            s::decode_subject_public_key_info(i::parse_single(input)->Some_0)->Some_0,
        ),
        spki_in_domain(s::decode_subject_public_key_info(i::parse_single(input)->Some_0)->Some_0),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let r = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (r.cstart, r.cend);
    let a = k::parse_subject_public_key_info(input)->Some_0;
    let (algorithm, after_algorithm) = c::parse_algorithm_identifier(b, start, finish)->Some_0;
    assert(a.algorithm == algorithm);
    lemma_algorithm_fwd(b, start, finish);
    lemma_read_bit_string(b, after_algorithm, finish);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    lemma_tlvs_cons(b, after_algorithm, finish, none);
    let ku = i::parse_tlv(sl(b, after_algorithm, finish))->Some_0;
    lemma_tlvs_cons(b, start, finish, seq![ku] + none);
    let au = i::parse_tlv(sl(b, start, finish))->Some_0;
    let e = seq![au] + (seq![ku] + none);
    lemma_sequence_fwd(b, 0, len, e);
    lemma_single(b, 0, len);
    assert(e[0] == au);
    assert(e[1] == ku);
    assert(e.len() == 2);
    let x = s::decode_subject_public_key_info(i::parse_single(input)->Some_0)->Some_0;
    if k::is_rsa_encryption(algorithm.oid) {
        assert(x.algorithm.parameters is Some);
    }
}

/// The two components of a SubjectPublicKeyInfo, as `clazel-der` reads them.
pub proof fn lemma_spki_components(b: Seq<u8>, start: nat, finish: nat, e: Seq<i::Tlv>, x: s::SubjectPublicKeyInfo)
    requires
        wf(b, start, finish),
        finish - start < two64(),
        i::parse_tlvs(sl(b, start, finish)) == Some(e),
        e.len() == 2,
        s::decode_algorithm_identifier(e[0]) == Some(x.algorithm),
        i::decode_bit_string(e[1]) == Some(x.subject_public_key),
        algorithm_in_domain(x.algorithm),
    ensures
        c::parse_algorithm_identifier(b, start, finish) is Some,
        algorithm_agree(c::parse_algorithm_identifier(b, start, finish)->Some_0.0, x.algorithm),
        ({
            let after = c::parse_algorithm_identifier(b, start, finish)->Some_0.1;
            &&& d::read_bit_string(b, after, finish) is Some
            &&& d::read_bit_string(b, after, finish)->Some_0.3 == finish
            &&& d::read_bit_string(b, after, finish)->Some_0.0 as nat == x.subject_public_key.unused
            &&& sl(
                b,
                d::read_bit_string(b, after, finish)->Some_0.1,
                d::read_bit_string(b, after, finish)->Some_0.2,
            ) == x.subject_public_key.octets
        }),
{
    assert(tag_fits(e[0]));
    assert(tag_fits(e[1]));
    lemma_tlvs_head(b, start, finish, e);
    lemma_algorithm_back(b, start, finish, e[0], x.algorithm);
    let (algorithm, after_algorithm) = c::parse_algorithm_identifier(b, start, finish)->Some_0;
    let rest = e.skip(1);
    assert(rest[0] == e[1]);
    let a0 = d::read_tlv(b, start, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
    assert(a0.cend == after_algorithm);
    lemma_tlvs_head(b, after_algorithm, finish, rest);
    lemma_read_bit_string(b, after_algorithm, finish);
    let v = d::read_tlv(b, after_algorithm, finish)->Some_0;
    lemma_tlvs_none_left(b, v.cend, finish, rest.skip(1));
}

/// **`theorem_spki`, from `structures.rs`.**
pub proof fn theorem_spki_back(input: Seq<u8>, u: i::Tlv, x: s::SubjectPublicKeyInfo)
    requires
        input.len() < two64(),
        i::parse_single(input) == Some(u),
        s::decode_subject_public_key_info(u) == Some(x),
        spki_in_domain(x),
    ensures
        k::parse_subject_public_key_info(input) is Some,
        spki_agree(k::parse_subject_public_key_info(input)->Some_0, x),
{
    hide(k::parse_rsa_public_key);
    hide(k::classify_ec_public_key);
    hide(c::parse_algorithm_identifier);
    hide(d::read_bit_string);
    hide(s::decode_algorithm_identifier);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    let e = s::sequence_elements(u)->Some_0;
    lemma_sequence_back(b, 0, len, u, e);
    let r = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (r.cstart, r.cend);
    assert(e.len() == 2) by {
        assert(i::from_index(e, 2).len() == e.len() - 2);
    }
    lemma_spki_components(b, start, finish, e, x);
    let (algorithm, after_algorithm) = c::parse_algorithm_identifier(b, start, finish)->Some_0;
    if k::is_rsa_encryption(algorithm.oid) {
        assert(k::is_rsa_encryption(x.algorithm.algorithm));
        assert(algorithm.parameters_der == Some(seq![0x05u8, 0x00u8]));
    }
}

// ---------------------------------------------------------------------
// Validity.
// ---------------------------------------------------------------------

/// A Validity `tbs/spec.rs` reads: no addition, each time in the domain, and
/// notBefore not after notAfter.
pub open spec fn validity_in_domain(v: s::Validity) -> bool {
    &&& v.additions.len() == 0
    &&& time_in_domain(v.not_before)
    &&& time_in_domain(v.not_after)
    &&& t::time_le(moment_time(time_moment(v.not_before)), moment_time(time_moment(v.not_after)))
}

/// Validity, from `tbs/spec.rs` to `structures.rs`.
pub proof fn lemma_validity_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        crate::tbs::spec::parse_validity(b, pos, end) is Some,
        crate::tbs::spec::parse_validity(b, pos, end)->Some_0.0.second != 60,
        crate::tbs::spec::parse_validity(b, pos, end)->Some_0.1.second != 60,
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == crate::tbs::spec::parse_validity(b, pos, end)->Some_0.2,
        pos < crate::tbs::spec::parse_validity(b, pos, end)->Some_0.2 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        s::decode_validity(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        validity_in_domain(s::decode_validity(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
        moment_time(time_moment(s::decode_validity(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0.not_before))
            == crate::tbs::spec::parse_validity(b, pos, end)->Some_0.0,
        moment_time(time_moment(s::decode_validity(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0.not_after))
            == crate::tbs::spec::parse_validity(b, pos, end)->Some_0.1,
{
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let (start, finish) = (r.cstart, r.cend);
    lemma_time_tlv(b, start, finish);
    let (before, after_before) = crate::tbs::spec::time_tlv(b, start, finish)->Some_0;
    lemma_time_tlv(b, after_before, finish);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    lemma_tlvs_cons(b, after_before, finish, none);
    let au = i::parse_tlv(sl(b, after_before, finish))->Some_0;
    lemma_tlvs_cons(b, start, finish, seq![au] + none);
    let bu = i::parse_tlv(sl(b, start, finish))->Some_0;
    let e = seq![bu] + (seq![au] + none);
    lemma_sequence_fwd(b, pos, end, e);
    assert(e[0] == bu);
    assert(e[1] == au);
    assert(e.len() == 2);
}

/// Validity, from `structures.rs` to `tbs/spec.rs`.
pub proof fn lemma_validity_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, v: s::Validity)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        s::decode_validity(u) == Some(v),
        validity_in_domain(v),
    ensures
        crate::tbs::spec::parse_validity(b, pos, end) is Some,
        crate::tbs::spec::parse_validity(b, pos, end)->Some_0.0 == moment_time(time_moment(v.not_before)),
        crate::tbs::spec::parse_validity(b, pos, end)->Some_0.1 == moment_time(time_moment(v.not_after)),
        crate::tbs::spec::parse_validity(b, pos, end)->Some_0.2 == pos + u.encoding.len(),
{
    let e = s::sequence_elements(u)->Some_0;
    lemma_sequence_back(b, pos, end, u, e);
    let r = d::read_tlv(b, pos, end)->Some_0;
    let (start, finish) = (r.cstart, r.cend);
    assert(e.len() == 2) by {
        assert(i::from_index(e, 2).len() == e.len() - 2);
    }
    assert(tag_fits(e[0]));
    assert(tag_fits(e[1]));
    lemma_tlvs_head(b, start, finish, e);
    lemma_time_tlv(b, start, finish);
    let a0 = d::read_tlv(b, start, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
    let rest = e.skip(1);
    assert(rest[0] == e[1]);
    lemma_tlvs_head(b, a0.cend, finish, rest);
    lemma_time_tlv(b, a0.cend, finish);
    let a1 = d::read_tlv(b, a0.cend, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, a0.cend, finish);
    lemma_tlvs_none_left(b, a1.cend, finish, rest.skip(1));
}

} // verus!
