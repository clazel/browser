//! The value decoders of `constraints/spec.rs` and
//! `policy_constraints/spec.rs` against `independent/extensions.rs`:
//! basicConstraints, keyUsage, extKeyUsage and policyConstraints. Name
//! constraints are in `equivalence_name_constraints.rs`.
//!
//! Each value has two theorems. `_fwd` starts from what the crate read and
//! `_back` from what the transcription read, and each states only its own
//! conditions.
//!
//! | Value | Crate reads, transcription refuses | Transcription reads, crate refuses |
//! |---|---|---|
//! | basicConstraints | nothing | an addition; pathLenConstraint without cA |
//! | keyUsage | nothing | an empty value; more than nine bits |
//! | extKeyUsage | nothing | a repeated purpose; a subidentifier of 2^64 or more |
//! | policyConstraints | nothing | an addition; a SkipCerts of 2^32 or more |
//!
//! The first column is empty: **`_fwd` has no condition but the length of the
//! input**, so these four decoders never accept what the transcription
//! refuses. The second column is each a real difference of source or policy:
//! - pathLenConstraint without cA: `requirements.rs` holds this as
//!   `basic_constraints_rules`, so the crate decodes what the transcription
//!   states as a rule (`equivalence_requirements.rs`).
//! - An empty keyUsage, and bits past `decipherOnly`: RFC 5280 §4.2.1.3 "at
//!   least one of the bits MUST be set to 1"; X.509 9.2.2.3's type is an open
//!   named bit list, and states neither.
//! - A repeated purpose: `constraints/spec.rs` refuses it as a stated choice.
//!   Neither X.509 9.2.2.4 nor RFC 5280 §4.2.1.12 mentions it.
//! - A SkipCerts of 2^32 or more: `policy_constraints/spec.rs`'s stated size
//!   bound. Every such value behaves as any value above the path's length.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_extensions::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::equivalence_tbs::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::constraints::spec as cs;
#[cfg(verus_only)]
use crate::policy_constraints::spec as pc;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// The arms of `decode_extension_value`.
// ---------------------------------------------------------------------

/// Two extensions of `id-ce` with different last arcs differ.
pub proof fn lemma_id_ce_differ(a: nat, b: nat)
    requires
        a != b,
    ensures
        e::id_ce(a) != e::id_ce(b),
{
    assert(e::id_ce(a)[3] == a);
    assert(e::id_ce(b)[3] == b);
}

/// The value `extensions.rs` gives a basicConstraints, if it reads one.
pub open spec fn basic_value(input: Seq<u8>) -> Option<e::BasicConstraintsSyntax> {
    match e::decode_extension_value(e::id_ce_basic_constraints(), input) {
        Some(e::ExtensionValue::BasicConstraints(v)) => Some(v),
        _ => None,
    }
}

/// The value `extensions.rs` gives a keyUsage, if it reads one.
pub open spec fn key_usage_value(input: Seq<u8>) -> Option<i::BitString> {
    match e::decode_extension_value(e::id_ce_key_usage(), input) {
        Some(e::ExtensionValue::KeyUsage(v)) => Some(v),
        _ => None,
    }
}

/// The value `extensions.rs` gives an extKeyUsage, if it reads one.
pub open spec fn ext_key_usage_value(input: Seq<u8>) -> Option<Seq<s::ObjectIdentifier>> {
    match e::decode_extension_value(e::id_ce_ext_key_usage(), input) {
        Some(e::ExtensionValue::ExtKeyUsage(v)) => Some(v),
        _ => None,
    }
}

/// The value `extensions.rs` gives a policyConstraints, if it reads one.
pub open spec fn policy_constraints_value(input: Seq<u8>) -> Option<e::PolicyConstraintsSyntax> {
    match e::decode_extension_value(e::id_ce_policy_constraints(), input) {
        Some(e::ExtensionValue::PolicyConstraints(v)) => Some(v),
        _ => None,
    }
}

/// basicConstraints is the arm `decode_extension_value` takes for its id.
pub proof fn lemma_basic_value(input: Seq<u8>)
    ensures
        basic_value(input) == match i::parse_single(input) {
            None => None,
            Some(t) => e::decode_basic_constraints(t),
        },
{
    lemma_id_ce_differ(19, 35);
    lemma_id_ce_differ(19, 14);
    lemma_id_ce_differ(19, 15);
    lemma_id_ce_differ(19, 37);
    lemma_id_ce_differ(19, 32);
    lemma_id_ce_differ(19, 17);
}

/// keyUsage is the arm `decode_extension_value` takes for its id.
pub proof fn lemma_key_usage_value(input: Seq<u8>)
    ensures
        key_usage_value(input) == match i::parse_single(input) {
            None => None,
            Some(t) => e::decode_key_usage(t),
        },
{
    lemma_id_ce_differ(15, 35);
    lemma_id_ce_differ(15, 14);
}

/// extKeyUsage is the arm `decode_extension_value` takes for its id.
pub proof fn lemma_ext_key_usage_value(input: Seq<u8>)
    ensures
        ext_key_usage_value(input) == match i::parse_single(input) {
            None => None,
            Some(t) => e::decode_ext_key_usage(t),
        },
{
    lemma_id_ce_differ(37, 35);
    lemma_id_ce_differ(37, 14);
    lemma_id_ce_differ(37, 15);
}

/// policyConstraints is the arm `decode_extension_value` takes for its id.
pub proof fn lemma_policy_constraints_value(input: Seq<u8>)
    ensures
        policy_constraints_value(input) == match i::parse_single(input) {
            None => None,
            Some(t) => e::decode_policy_constraints(t),
        },
{
    lemma_id_ce_differ(36, 35);
    lemma_id_ce_differ(36, 14);
    lemma_id_ce_differ(36, 15);
    lemma_id_ce_differ(36, 37);
    lemma_id_ce_differ(36, 32);
    lemma_id_ce_differ(36, 17);
    lemma_id_ce_differ(36, 19);
    lemma_id_ce_differ(36, 30);
}

// ---------------------------------------------------------------------
// Numbers: magnitude octets against values.
// ---------------------------------------------------------------------

/// The magnitude octets of an INTEGER's contents: without the padding octet
/// (X.690 8.3.2 b)).
pub open spec fn magnitude_of(c: Seq<u8>) -> Seq<u8> {
    if c.len() >= 2 && c[0] == 0 {
        c.skip(1)
    } else {
        c
    }
}

/// A non-negative INTEGER's value is the value of its magnitude octets.
pub proof fn lemma_magnitude_value(c: Seq<u8>)
    requires
        d::integer_contents_ok(c),
        c[0] < 128,
    ensures
        d::be_value(magnitude_of(c)) as int == d::integer_value(c),
{
    if c.len() >= 2 && c[0] == 0 {
        lemma_be_skip_zero(c);
    }
}

/// The value 2^32.
pub open spec fn two32() -> nat {
    0x1_0000_0000
}

/// **The size bound, as a value.** At most four magnitude octets is exactly a
/// value below 2^32.
pub proof fn lemma_magnitude_size(c: Seq<u8>)
    requires
        d::integer_contents_ok(c),
        c[0] < 128,
    ensures
        (magnitude_of(c).len() <= 4) == (d::integer_value(c) < two32()),
{
    let m = magnitude_of(c);
    lemma_magnitude_value(c);
    assert(d::pow256(0) == 1);
    assert(d::pow256(1) == 256);
    assert(d::pow256(2) == 65536);
    assert(d::pow256(3) == 16777216);
    assert(d::pow256(4) == 0x1_0000_0000);
    if m.len() <= 4 {
        clazel_der::lemmas::lemma_be_value_bound(m);
        clazel_der::lemmas_tlv::lemma_pow256_monotone(m.len(), 4);
    } else {
        // The first magnitude octet is not zero: a zero would have been
        // padding, and only one octet of padding is allowed.
        assert(m[0] != 0) by {
            if c.len() >= 2 && c[0] == 0 {
                assert(m[0] == c[1]);
                assert(c[1] >= 128);
            } else {
                assert(m[0] == c[0]);
            }
        }
        clazel_der::lemmas_tlv::lemma_be_value_leading_nonzero(m);
        clazel_der::lemmas_tlv::lemma_pow256_monotone(4, (m.len() - 1) as nat);
    }
}

// ---------------------------------------------------------------------
// basicConstraints.
// ---------------------------------------------------------------------

/// The two values of a basicConstraints agree. `constraints/spec.rs` keeps
/// pathLenConstraint as magnitude octets.
pub open spec fn basic_agree(a: cs::BasicConstraints, v: e::BasicConstraintsSyntax) -> bool {
    &&& a.ca == v.c_a
    &&& match (a.path_len_constraint, v.path_len_constraint) {
        (None, None) => true,
        (Some(m), Some(n)) => d::be_value(m) == n,
        _ => false,
    }
}

/// A basicConstraints `constraints/spec.rs` reads: no addition, and
/// pathLenConstraint only with cA.
pub open spec fn basic_in_domain(v: e::BasicConstraintsSyntax) -> bool {
    &&& v.additions.len() == 0
    &&& v.path_len_constraint.is_none() || v.c_a
}

/// An INTEGER at `pos`, from `read_integer`: its value is that of the
/// magnitude octets `read_integer` gives.
pub proof fn lemma_integer_magnitude(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        d::read_integer(b, pos, end) is Some,
        !d::read_integer(b, pos, end)->Some_0.0,
    ensures
        ({
            let (_, start, finish, _) = d::read_integer(b, pos, end)->Some_0;
            let r = d::read_tlv(b, pos, end)->Some_0;
            let con = sl(b, r.cstart, r.cend);
            &&& sl(b, start, finish) == magnitude_of(con)
            &&& d::be_value(sl(b, start, finish)) as int == d::integer_value(con)
            &&& con[0] < 128
        }),
{
    lemma_read_integer(b, pos, end);
    let (_, start, finish, _) = d::read_integer(b, pos, end)->Some_0;
    let r = d::read_tlv(b, pos, end)->Some_0;
    let con = sl(b, r.cstart, r.cend);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    assert(sl(b, start, finish) =~= magnitude_of(con));
    lemma_magnitude_value(con);
}

/// **`theorem_basic_constraints`, from `constraints/spec.rs`.** A value
/// `parse_basic_constraints` reads, `extensions.rs` reads to the same value.
/// No condition.
#[verifier::spinoff_prover]
pub proof fn theorem_basic_constraints_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        cs::parse_basic_constraints(input) is Some,
    ensures
        basic_value(input) is Some,
        basic_agree(cs::parse_basic_constraints(input)->Some_0, basic_value(input)->Some_0),
        basic_in_domain(basic_value(input)->Some_0),
{
    hide(basic_value);
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(d::read_boolean);
    hide(d::read_integer);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_basic_value(input);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    let a = cs::parse_basic_constraints(input)->Some_0;
    if start == finish {
        lemma_sequence_fwd(b, 0, len, none);
        lemma_single(b, 0, len);
    } else {
        let first = d::read_tlv(b, start, finish)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
        assert(first.tag == d::universal_primitive(d::BOOLEAN));
        lemma_read_boolean(b, start, finish);
        let (v, after) = d::read_boolean(b, start, finish)->Some_0;
        assert(v);
        if after == finish {
            lemma_tlv(b, start, finish);
            lemma_tlvs_cons(b, start, finish, none);
            let bu = i::parse_tlv(sl(b, start, finish))->Some_0;
            let l = seq![bu] + none;
            lemma_sequence_fwd(b, 0, len, l);
            lemma_single(b, 0, len);
            assert(l[0] == bu);
            assert(l.len() == 1);
            lemma_has_universal_tag(b, start, first, bu, d::BOOLEAN, false);
        } else {
            lemma_tlv(b, start, finish);
            lemma_tlv(b, after, finish);
            lemma_read_integer(b, after, finish);
            lemma_integer_magnitude(b, after, finish);
            lemma_tlvs_cons(b, after, finish, none);
            let iu = i::parse_tlv(sl(b, after, finish))->Some_0;
            lemma_tlvs_cons(b, start, finish, seq![iu] + none);
            let bu = i::parse_tlv(sl(b, start, finish))->Some_0;
            let l = seq![bu] + (seq![iu] + none);
            lemma_sequence_fwd(b, 0, len, l);
            lemma_single(b, 0, len);
            assert(l[0] == bu);
            assert(l[1] == iu);
            assert(l.len() == 2);
            lemma_has_universal_tag(b, start, first, bu, d::BOOLEAN, false);
            let second = d::read_tlv(b, after, finish)->Some_0;
            lemma_has_universal_tag(b, after, second, iu, d::INTEGER, false);
        }
    }
}

/// **`theorem_basic_constraints`, from `extensions.rs`.** A value
/// `extensions.rs` reads, `parse_basic_constraints` reads to the same value,
/// unless it has an addition or a pathLenConstraint without cA.
#[verifier::spinoff_prover]
pub proof fn theorem_basic_constraints_back(input: Seq<u8>, v: e::BasicConstraintsSyntax)
    requires
        input.len() < two64(),
        basic_value(input) == Some(v),
        basic_in_domain(v),
    ensures
        cs::parse_basic_constraints(input) is Some,
        basic_agree(cs::parse_basic_constraints(input)->Some_0, v),
{
    hide(basic_value);
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(d::read_boolean);
    hide(d::read_integer);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_basic_value(input);
    let u = i::parse_single(input)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    lemma_tlvs_none_left(b, start, finish, l);
    if l.len() > 0 {
        if i::tag_at(l, 0, 0, 1) {
            assert(tag_fits(l[0]));
            lemma_tlvs_head(b, start, finish, l);
            let first = d::read_tlv(b, start, finish)->Some_0;
            clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
            lemma_has_universal_tag(b, start, first, l[0], d::BOOLEAN, false);
            lemma_read_boolean(b, start, finish);
            let (val, after) = d::read_boolean(b, start, finish)->Some_0;
            let rest = l.skip(1);
            lemma_tlvs_none_left(b, after, finish, rest);
            if rest.len() > 0 {
                assert(rest[0] == l[1]);
                assert(i::tag_at(l, 1, 0, 2)) by {
                    if !i::tag_at(l, 1, 0, 2) {
                        assert(i::from_index(l, 1).len() == l.len() - 1);
                    }
                }
                assert(tag_fits(rest[0]));
                lemma_tlvs_head(b, after, finish, rest);
                lemma_read_integer(b, after, finish);
                let second = d::read_tlv(b, after, finish)->Some_0;
                clazel_der::lemmas::lemma_read_tlv_bounds(b, after, finish);
                let con = sl(b, second.cstart, second.cend);
                lemma_has_universal_tag(b, after, second, rest[0], d::INTEGER, false);
                lemma_integer_contents(con);
                lemma_integer_sign(con);
                lemma_integer_magnitude(b, after, finish);
                assert(l.len() == 2) by {
                    if l.len() > 2 {
                        assert(i::from_index(l, 2).len() == l.len() - 2);
                    }
                }
                lemma_tlvs_none_left(b, second.cend, finish, rest.skip(1));
                assert(rest.skip(1).len() == 0);
            }
        } else {
            // Without cA there is nothing else: pathLenConstraint needs it,
            // and no addition is left.
            assert(!i::tag_at(l, 0, 0, 2));
            assert(i::from_index(l, 0).len() == l.len());
        }
    }
}

// ---------------------------------------------------------------------
// keyUsage.
// ---------------------------------------------------------------------

/// The two ways of writing 2^u for a number of unused bits.
pub proof fn lemma_bit_weight(u: u8)
    requires
        u <= 7,
    ensures
        d::pow2_unused(u) == i::bit_weight(u as nat),
{
}

/// The two values of a keyUsage agree.
pub open spec fn key_usage_agree(a: cs::KeyUsage, v: i::BitString) -> bool {
    &&& a.bits == v.octets
    &&& a.bit_count + v.unused == v.octets.len() * 8
}

/// A keyUsage `constraints/spec.rs` reads: at least one bit, and none past
/// `decipherOnly`.
pub open spec fn key_usage_in_domain(v: i::BitString) -> bool {
    &&& v.octets.len() > 0
    &&& v.octets.len() * 8 <= 9 + v.unused
}

/// **`theorem_key_usage`, from `constraints/spec.rs`.** No condition.
#[verifier::spinoff_prover]
pub proof fn theorem_key_usage_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        cs::parse_key_usage(input) is Some,
    ensures
        key_usage_value(input) is Some,
        key_usage_agree(cs::parse_key_usage(input)->Some_0, key_usage_value(input)->Some_0),
        key_usage_in_domain(key_usage_value(input)->Some_0),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_key_usage_value(input);
    lemma_read_bit_string(b, 0, len);
    let (unused, start, finish, next) = d::read_bit_string(b, 0, len)->Some_0;
    lemma_single(b, 0, len);
    let u = i::parse_single(input)->Some_0;
    let r = d::read_tlv(b, 0, len)->Some_0;
    let con = sl(b, r.cstart, r.cend);
    assert(d::bit_string_contents_ok(con));
    assert(unused == con[0]);
    assert(unused <= 7);
    lemma_bit_weight(unused);
    let v = i::decode_bit_string(u)->Some_0;
    assert(finish > start) by (nonlinear_arith)
        requires
            (finish - start) * 8 - unused > 0,
            finish >= start,
            unused >= 0,
    ;
    assert(v.octets[v.octets.len() - 1] == b[finish - 1]);
}

/// **`theorem_key_usage`, from `extensions.rs`.** Unless the value is empty or
/// has a bit past `decipherOnly`.
#[verifier::spinoff_prover]
pub proof fn theorem_key_usage_back(input: Seq<u8>, v: i::BitString)
    requires
        input.len() < two64(),
        key_usage_value(input) == Some(v),
        key_usage_in_domain(v),
    ensures
        cs::parse_key_usage(input) is Some,
        key_usage_agree(cs::parse_key_usage(input)->Some_0, v),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_key_usage_value(input);
    let u = i::parse_single(input)->Some_0;
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_read_bit_string(b, 0, len);
    let (unused, start, finish, next) = d::read_bit_string(b, 0, len)->Some_0;
    assert(v.octets == sl(b, start, finish));
    assert(v.unused == unused as nat);
    assert(unused <= 7);
    lemma_bit_weight(unused);
    assert(next == len);
    assert(v.octets[v.octets.len() - 1] == b[finish - 1]);
    assert(i::no_trailing_zero_bits(v));
    assert((b[finish - 1] as nat) % d::pow2_unused(unused) == 0);
}

/// **A named bit reads the same on both sides.** `key_usage_has` of a value
/// is X.680 22's bit number of it.
pub proof fn lemma_key_usage_has(a: cs::KeyUsage, v: i::BitString, bit: cs::KeyUsageBit)
    requires
        key_usage_agree(a, v),
        v.unused <= 7,
    ensures
        cs::key_usage_has(a, bit) == i::bit_is_set(v, cs::key_usage_bit_index(bit)),
{
    let index = cs::key_usage_bit_index(bit);
    assert(index <= 8);
    assert(d::pow2_unused(0) == 1);
    assert(d::pow2_unused(1) == 2);
    assert(d::pow2_unused(2) == 4);
    assert(d::pow2_unused(3) == 8);
    assert(d::pow2_unused(4) == 16);
    assert(d::pow2_unused(5) == 32);
    assert(d::pow2_unused(6) == 64);
    assert(d::pow2_unused(7) == 128);
}

// ---------------------------------------------------------------------
// extKeyUsage.
// ---------------------------------------------------------------------

/// `oid_in` finds a member.
pub proof fn lemma_oid_in(seen: Seq<Seq<nat>>, oid: Seq<nat>, k: int)
    requires
        0 <= k <= seen.len(),
        cs::oid_in(seen, oid, k),
    ensures
        exists|m: int| k <= m < seen.len() && seen[m] == oid,
    decreases seen.len() - k,
{
    if seen[k] =~= oid {
        assert(seen[k] == oid);
    } else {
        lemma_oid_in(seen, oid, k + 1);
    }
}

/// `oid_in` of a member.
pub proof fn lemma_oid_in_member(seen: Seq<Seq<nat>>, oid: Seq<nat>, k: int, m: int)
    requires
        0 <= k <= m < seen.len(),
        seen[m] == oid,
    ensures
        cs::oid_in(seen, oid, k),
    decreases m - k,
{
    if k < m {
        lemma_oid_in_member(seen, oid, k + 1, m);
    } else {
        assert(seen[k] =~= oid);
    }
}

/// `decode_key_purpose_list` past one more element at the front.
pub proof fn lemma_key_purpose_list_shift(u: i::Tlv, l: Seq<i::Tlv>, k: nat)
    ensures
        e::decode_key_purpose_list(seq![u] + l, k + 1) == e::decode_key_purpose_list(l, k),
    decreases l.len() - k,
{
    let f = seq![u] + l;
    if k < l.len() {
        assert(f[(k + 1) as int] == l[k as int]);
        lemma_key_purpose_list_shift(u, l, k + 1);
    }
}

/// `decode_key_purpose_list` gives one value for each element.
pub proof fn lemma_key_purpose_list_len(l: Seq<i::Tlv>, k: nat)
    requires
        k <= l.len(),
        e::decode_key_purpose_list(l, k) is Some,
    ensures
        e::decode_key_purpose_list(l, k)->Some_0.len() == l.len() - k,
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_key_purpose_list_len(l, k + 1);
    }
}

/// No two purposes are one, and none is in `seen`.
pub open spec fn purposes_fresh(v: Seq<s::ObjectIdentifier>, seen: Seq<Seq<nat>>) -> bool {
    &&& forall|j: int, k: int| 0 <= j < k < v.len() ==> #[trigger] v[j] != #[trigger] v[k]
    &&& forall|m: int, k: int| 0 <= m < seen.len() && 0 <= k < v.len() ==> #[trigger] seen[m] != #[trigger] v[k]
}

/// From `constraints/spec.rs`, the purposes from `pos`.
pub proof fn lemma_eku_items_fwd(b: Seq<u8>, pos: nat, end: nat, seen: Seq<Seq<nat>>, acc: Seq<Seq<nat>>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        cs::parse_eku_items(b, pos, end, seen, acc) is Some,
    ensures
        ({
            let all = cs::parse_eku_items(b, pos, end, seen, acc)->Some_0.0;
            &&& cs::parse_eku_items(b, pos, end, seen, acc)->Some_0.1 == end
            &&& all.len() >= acc.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& {
                let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& l.len() == all.len() - acc.len()
                &&& e::decode_key_purpose_list(l, 0) is Some
                &&& {
                    let v = e::decode_key_purpose_list(l, 0)->Some_0;
                    &&& v.len() == l.len()
                    &&& forall|k: int| 0 <= k < v.len() ==> #[trigger] all[k + acc.len()] == v[k]
                    &&& forall|k: int| 0 <= k < v.len() ==> oid_fits(#[trigger] v[k])
                }
            }
        }),
    decreases end - pos,
{
    let all = cs::parse_eku_items(b, pos, end, seen, acc)->Some_0.0;
    if pos == end {
        lemma_tlvs_empty(b, pos);
    } else {
        lemma_read_oid(b, pos, end);
        let (oid, next) = d::read_oid(b, pos, end)->Some_0;
        let acc2 = acc.push(oid);
        let seen2 = seen.push(oid);
        assert(cs::parse_eku_items(b, next, end, seen2, acc2) == cs::parse_eku_items(b, pos, end, seen, acc));
        lemma_eku_items_fwd(b, next, end, seen2, acc2);
        assert(all[acc.len() as int] == acc2[acc.len() as int]);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = i::parse_tlvs(sl(b, next, end))->Some_0;
        lemma_tlvs_cons(b, pos, end, r);
        lemma_key_purpose_list_shift(u, r, 0);
        let lr = e::decode_key_purpose_list(r, 0)->Some_0;
        let v = seq![oid] + lr;
        let l = seq![u] + r;
        assert(l[0] == u);
        assert(e::decode_key_purpose_list(l, 0) == Some(v));
        assert forall|k: int| 0 <= k < v.len() implies #[trigger] all[k + acc.len()] == v[k] by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            }
        }
        assert forall|k: int| 0 <= k < v.len() implies oid_fits(#[trigger] v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// From `extensions.rs`, the purposes from `pos`.
pub proof fn lemma_eku_items_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    seen: Seq<Seq<nat>>,
    acc: Seq<Seq<nat>>,
    l: Seq<i::Tlv>,
    v: Seq<s::ObjectIdentifier>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        e::decode_key_purpose_list(l, 0) == Some(v),
        forall|k: int| 0 <= k < v.len() ==> oid_fits(#[trigger] v[k]),
        purposes_fresh(v, seen),
    ensures
        cs::parse_eku_items(b, pos, end, seen, acc) is Some,
        cs::parse_eku_items(b, pos, end, seen, acc)->Some_0.1 == end,
        cs::parse_eku_items(b, pos, end, seen, acc)->Some_0.0 == acc + v,
    decreases end - pos,
{
    lemma_tlvs_none_left(b, pos, end, l);
    if pos < end {
        let u = l[0];
        let r = l.skip(1);
        assert(l =~= seq![u] + r);
        lemma_key_purpose_list_shift(u, r, 0);
        let oid = i::decode_object_identifier(u)->Some_0;
        let lr = e::decode_key_purpose_list(r, 0)->Some_0;
        assert(v == seq![oid] + lr);
        assert(v[0] == oid);
        assert(tag_fits(u));
        lemma_tlvs_head(b, pos, end, l);
        lemma_read_oid(b, pos, end);
        let (o2, next) = d::read_oid(b, pos, end)->Some_0;
        assert(o2 == oid);
        let t = d::read_tlv(b, pos, end)->Some_0;
        assert(t.cend == next);
        assert forall|k: int| 0 <= k < lr.len() implies oid_fits(#[trigger] lr[k]) by {
            assert(v[k + 1] == lr[k]);
        }
        if cs::oid_in(seen, oid, 0) {
            lemma_oid_in(seen, oid, 0);
            let m = choose|m: int| 0 <= m < seen.len() && seen[m] == oid;
            assert(seen[m] != v[0]);
        }
        let acc2 = acc.push(oid);
        let seen2 = seen.push(oid);
        assert forall|p: int, q: int| 0 <= p < q < lr.len() implies #[trigger] lr[p] != #[trigger] lr[q] by {
            assert(v[p + 1] == lr[p]);
            assert(v[q + 1] == lr[q]);
            assert(v[p + 1] != v[q + 1]);
        }
        assert forall|m: int, q: int| 0 <= m < seen2.len() && 0 <= q < lr.len() implies #[trigger] seen2[m] != #[trigger] lr[q] by {
            assert(v[q + 1] == lr[q]);
            if m < seen.len() {
                assert(seen2[m] == seen[m]);
                assert(seen[m] != v[q + 1]);
            } else {
                assert(seen2[m] == oid);
                assert(v[0] != v[q + 1]);
            }
        }
        lemma_eku_items_back(b, next, end, seen2, acc2, r, lr);
        assert(acc2 + lr =~= acc + v);
    } else {
        assert(v.len() == 0);
        assert(acc + v =~= acc);
    }
}

/// An extKeyUsage `constraints/spec.rs` reads: each purpose once, each
/// subidentifier below 2^64.
pub open spec fn eku_in_domain(v: Seq<s::ObjectIdentifier>) -> bool {
    &&& forall|k: int| 0 <= k < v.len() ==> oid_fits(#[trigger] v[k])
    &&& forall|j: int, k: int| 0 <= j < k < v.len() ==> #[trigger] v[j] != #[trigger] v[k]
}

/// The purposes read by `parse_eku_items` are distinct.
pub proof fn lemma_eku_items_distinct(b: Seq<u8>, pos: nat, end: nat, seen: Seq<Seq<nat>>, acc: Seq<Seq<nat>>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        cs::parse_eku_items(b, pos, end, seen, acc) is Some,
        acc == seen,
        forall|j: int, k: int| 0 <= j < k < acc.len() ==> #[trigger] acc[j] != #[trigger] acc[k],
    ensures
        ({
            let all = cs::parse_eku_items(b, pos, end, seen, acc)->Some_0.0;
            forall|j: int, k: int| 0 <= j < k < all.len() ==> #[trigger] all[j] != #[trigger] all[k]
        }),
    decreases end - pos,
{
    if pos < end {
        lemma_read_oid(b, pos, end);
        let (oid, next) = d::read_oid(b, pos, end)->Some_0;
        let acc2 = acc.push(oid);
        assert forall|j: int, k: int| 0 <= j < k < acc2.len() implies #[trigger] acc2[j] != #[trigger] acc2[k] by {
            if k == acc.len() {
                assert(acc2[j] == acc[j]);
                assert(acc2[k] == oid);
                if acc[j] == oid {
                    lemma_oid_in_member(seen, oid, 0, j);
                }
            } else {
                assert(acc2[j] == acc[j]);
                assert(acc2[k] == acc[k]);
            }
        }
        assert(cs::parse_eku_items(b, next, end, acc2, acc2) == cs::parse_eku_items(b, pos, end, seen, acc));
        lemma_eku_items_distinct(b, next, end, acc2, acc2);
    }
}

/// **`theorem_ext_key_usage`, from `constraints/spec.rs`.** No condition.
#[verifier::spinoff_prover]
pub proof fn theorem_ext_key_usage_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        cs::parse_extended_key_usage(input) is Some,
    ensures
        ext_key_usage_value(input) == Some(cs::parse_extended_key_usage(input)->Some_0.purposes),
        eku_in_domain(ext_key_usage_value(input)->Some_0),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_ext_key_usage_value(input);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<Seq<nat>>::empty();
    lemma_eku_items_fwd(b, start, finish, none, none);
    lemma_eku_items_distinct(b, start, finish, none, none);
    let l = i::parse_tlvs(sl(b, start, finish))->Some_0;
    lemma_sequence_fwd(b, 0, len, l);
    lemma_single(b, 0, len);
    let all = cs::parse_extended_key_usage(input)->Some_0.purposes;
    let v = e::decode_key_purpose_list(l, 0)->Some_0;
    assert(all =~= v) by {
        assert forall|k: int| 0 <= k < v.len() implies #[trigger] all[k] == v[k] by {
            assert(all[k + none.len()] == all[k]);
        }
    }
    assert(l.len() > 0);
}

/// **`theorem_ext_key_usage`, from `extensions.rs`.** Unless a purpose repeats
/// or has a subidentifier of 2^64 or more.
#[verifier::spinoff_prover]
pub proof fn theorem_ext_key_usage_back(input: Seq<u8>, v: Seq<s::ObjectIdentifier>)
    requires
        input.len() < two64(),
        ext_key_usage_value(input) == Some(v),
        eku_in_domain(v),
    ensures
        cs::parse_extended_key_usage(input) is Some,
        cs::parse_extended_key_usage(input)->Some_0.purposes == v,
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_ext_key_usage_value(input);
    let u = i::parse_single(input)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<Seq<nat>>::empty();
    lemma_key_purpose_list_len(l, 0);
    lemma_tlvs_none_left(b, start, finish, l);
    lemma_eku_items_back(b, start, finish, none, none, l, v);
    assert(none + v =~= v);
}

// ---------------------------------------------------------------------
// policyConstraints.
// ---------------------------------------------------------------------

/// The two values of one SkipCerts agree.
pub open spec fn skip_agree(a: Option<Seq<u8>>, v: Option<nat>) -> bool {
    match (a, v) {
        (None, None) => true,
        (Some(m), Some(n)) => d::be_value(m) == n,
        _ => false,
    }
}

/// The two values of a policyConstraints agree.
pub open spec fn policy_constraints_agree(a: pc::PolicyConstraints, v: e::PolicyConstraintsSyntax) -> bool {
    &&& skip_agree(a.require_explicit_policy, v.require_explicit_policy)
    &&& skip_agree(a.inhibit_policy_mapping, v.inhibit_policy_mapping)
}

/// One SkipCerts `policy_constraints/spec.rs` reads.
pub open spec fn skip_in_domain(v: Option<nat>) -> bool {
    match v {
        None => true,
        Some(n) => n < two32(),
    }
}

/// A policyConstraints `policy_constraints/spec.rs` reads: no addition, and
/// each SkipCerts below 2^32.
pub open spec fn policy_constraints_in_domain(v: e::PolicyConstraintsSyntax) -> bool {
    &&& v.additions.len() == 0
    &&& skip_in_domain(v.require_explicit_policy)
    &&& skip_in_domain(v.inhibit_policy_mapping)
}

/// `read_identifier` is the first step of `read_tlv`.
pub proof fn lemma_tlv_identifier(b: Seq<u8>, pos: nat, end: nat)
    requires
        d::read_tlv(b, pos, end) is Some,
    ensures
        d::read_identifier(b, pos, end) is Some,
        d::read_identifier(b, pos, end)->Some_0.0 == d::read_tlv(b, pos, end)->Some_0.tag,
{
}

/// A present SkipCerts, from `policy_constraints/spec.rs`.
pub proof fn lemma_skip_certs_fwd(b: Seq<u8>, pos: nat, end: nat, number: u32)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        pc::parse_skip_certs(b, pos, end, number) is Some,
        pc::parse_skip_certs(b, pos, end, number)->Some_0 is Some,
    ensures
        ({
            let (m, next) = pc::parse_skip_certs(b, pos, end, number)->Some_0->Some_0;
            let r = d::read_tlv(b, pos, end)->Some_0;
            &&& d::read_tlv(b, pos, end) is Some
            &&& r.cend == next
            &&& pos < next <= end
            &&& !tag_is_reserved(r.tag)
            &&& i::parse_tlv(sl(b, pos, end)) is Some
            &&& {
                let u = i::parse_tlv(sl(b, pos, end))->Some_0;
                &&& u.class == i::class_context()
                &&& u.number == number
                &&& i::decode_tagged_non_negative(u) == Some(d::be_value(m))
                &&& d::be_value(m) < two32()
            }
        }),
{
    let (tag, id) = d::read_identifier(b, pos, end)->Some_0;
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    assert(r.tag == tag);
    assert(tag.class == d::Class::ContextSpecific);
    lemma_context_class(tag);
    lemma_tlv(b, pos, end);
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    let con = sl(b, r.cstart, r.cend);
    lemma_integer_contents(con);
    assert(con[0] < 128);
    lemma_magnitude_value(con);
    lemma_magnitude_size(con);
    let (m, next) = pc::parse_skip_certs(b, pos, end, number)->Some_0->Some_0;
    assert(m =~= magnitude_of(con));
}

/// A present SkipCerts, from `extensions.rs`.
pub proof fn lemma_skip_certs_back(b: Seq<u8>, pos: nat, end: nat, number: u32, u: i::Tlv)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        u.class == i::class_context(),
        u.number == number,
        tag_fits(u),
        i::decode_tagged_non_negative(u) is Some,
        i::decode_tagged_non_negative(u)->Some_0 < two32(),
    ensures
        pc::parse_skip_certs(b, pos, end, number) is Some,
        pc::parse_skip_certs(b, pos, end, number)->Some_0 is Some,
        ({
            let (m, next) = pc::parse_skip_certs(b, pos, end, number)->Some_0->Some_0;
            &&& d::be_value(m) == i::decode_tagged_non_negative(u)->Some_0
            &&& next == pos + u.encoding.len()
            &&& pos < next <= end
            &&& next == d::read_tlv(b, pos, end)->Some_0.cend
        }),
{
    lemma_tlv(b, pos, end);
    lemma_parse_tlv_not_reserved(sl(b, pos, end));
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_tlv_identifier(b, pos, end);
    lemma_context_class(r.tag);
    let con = sl(b, r.cstart, r.cend);
    assert(con == u.contents);
    lemma_integer_contents(con);
    lemma_integer_sign(con);
    lemma_magnitude_value(con);
    lemma_magnitude_size(con);
    assert(pos < end);
    let start = if con.len() >= 2 && con[0] == 0 { r.cstart + 1 } else { r.cstart };
    assert(sl(b, start, r.cend) =~= magnitude_of(con));
    assert(r.cend - start == magnitude_of(con).len());
}

/// An absent SkipCerts: another tag, or nothing left.
pub proof fn lemma_skip_certs_absent(b: Seq<u8>, pos: nat, end: nat, number: u32, l: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        l.len() > 0 ==> tag_fits(l[0]),
        !i::tag_at(l, 0, i::class_context(), number as nat),
    ensures
        pc::parse_skip_certs(b, pos, end, number) == Some(None::<(Seq<u8>, nat)>),
{
    lemma_tlvs_none_left(b, pos, end, l);
    if l.len() > 0 {
        lemma_tlvs_head(b, pos, end, l);
        let r = d::read_tlv(b, pos, end)->Some_0;
        lemma_tlv_identifier(b, pos, end);
        lemma_context_class(r.tag);
    }
}

/// **`theorem_policy_constraints`, from `policy_constraints/spec.rs`.** No
/// condition.
#[verifier::spinoff_prover]
pub proof fn theorem_policy_constraints_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        pc::parse_policy_constraints(input) is Some,
    ensures
        policy_constraints_value(input) is Some,
        policy_constraints_agree(pc::parse_policy_constraints(input)->Some_0, policy_constraints_value(input)->Some_0),
        policy_constraints_in_domain(policy_constraints_value(input)->Some_0),
{
    hide(policy_constraints_value);
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(pc::parse_skip_certs);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_policy_constraints_value(input);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    let require = pc::parse_skip_certs(b, start, finish, 0)->Some_0;
    let after = match require {
        Some((_, next)) => next,
        None => start,
    };
    let inhibit = pc::parse_skip_certs(b, after, finish, 1)->Some_0;
    if require is Some {
        lemma_skip_certs_fwd(b, start, finish, 0);
        let u1 = i::parse_tlv(sl(b, start, finish))->Some_0;
        if inhibit is Some {
            lemma_skip_certs_fwd(b, after, finish, 1);
            let u2 = i::parse_tlv(sl(b, after, finish))->Some_0;
            lemma_tlvs_cons(b, after, finish, none);
            lemma_tlvs_cons(b, start, finish, seq![u2] + none);
            let l = seq![u1] + (seq![u2] + none);
            lemma_sequence_fwd(b, 0, len, l);
            lemma_single(b, 0, len);
            assert(l[0] == u1);
            assert(l[1] == u2);
            assert(l.len() == 2);
        } else {
            lemma_tlvs_cons(b, start, finish, none);
            let l = seq![u1] + none;
            lemma_sequence_fwd(b, 0, len, l);
            lemma_single(b, 0, len);
            assert(l[0] == u1);
            assert(l.len() == 1);
        }
    } else {
        lemma_skip_certs_fwd(b, start, finish, 1);
        let u2 = i::parse_tlv(sl(b, start, finish))->Some_0;
        lemma_tlvs_cons(b, start, finish, none);
        let l = seq![u2] + none;
        lemma_sequence_fwd(b, 0, len, l);
        lemma_single(b, 0, len);
        assert(l[0] == u2);
        assert(l.len() == 1);
    }
}

/// **`theorem_policy_constraints`, from `extensions.rs`.** Unless it has an
/// addition or a SkipCerts of 2^32 or more.
#[verifier::spinoff_prover]
pub proof fn theorem_policy_constraints_back(input: Seq<u8>, v: e::PolicyConstraintsSyntax)
    requires
        input.len() < two64(),
        policy_constraints_value(input) == Some(v),
        policy_constraints_in_domain(v),
    ensures
        pc::parse_policy_constraints(input) is Some,
        policy_constraints_agree(pc::parse_policy_constraints(input)->Some_0, v),
{
    hide(policy_constraints_value);
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(pc::parse_skip_certs);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_policy_constraints_value(input);
    let u = i::parse_single(input)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    let i0: nat = if i::tag_at(l, 0, 2, 0) { 1 } else { 0 };
    let j0: nat = if i::tag_at(l, i0, 2, 1) { i0 + 1 } else { i0 };
    assert(j0 > 0);
    assert(l.len() == j0) by {
        if l.len() > j0 {
            assert(i::from_index(l, j0).len() == l.len() - j0);
        }
    }
    assert(tag_fits(l[0]));
    if i0 == 1 {
        lemma_tlvs_head(b, start, finish, l);
        lemma_skip_certs_back(b, start, finish, 0, l[0]);
        let (m1, next) = pc::parse_skip_certs(b, start, finish, 0)->Some_0->Some_0;
        let rest = l.skip(1);
        if j0 == 2 {
            assert(rest[0] == l[1]);
            assert(tag_fits(l[1]));
            lemma_tlvs_head(b, next, finish, rest);
            lemma_skip_certs_back(b, next, finish, 1, l[1]);
            let (m2, last) = pc::parse_skip_certs(b, next, finish, 1)->Some_0->Some_0;
            lemma_tlvs_none_left(b, last, finish, rest.skip(1));
        } else {
            assert(rest.len() == 0);
            lemma_tlvs_none_left(b, next, finish, rest);
            lemma_skip_certs_absent(b, next, finish, 1, rest);
        }
    } else {
        lemma_skip_certs_absent(b, start, finish, 0, l);
        lemma_tlvs_head(b, start, finish, l);
        lemma_skip_certs_back(b, start, finish, 1, l[0]);
        let (m2, last) = pc::parse_skip_certs(b, start, finish, 1)->Some_0->Some_0;
        lemma_tlvs_none_left(b, last, finish, l.skip(1));
    }
}

} // verus!
