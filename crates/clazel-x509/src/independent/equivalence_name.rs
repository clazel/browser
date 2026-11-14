//! `Name` of `independent/structures.rs` against `name/spec.rs`, with the
//! helpers for a SEQUENCE and a SET that the other files use. The domain is
//! explained in `equivalence.rs`.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::name::spec as n;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// SEQUENCE and SET.
// ---------------------------------------------------------------------

/// A SEQUENCE `clazel-der` read, as `der.rs`'s elements.
pub proof fn lemma_sequence_fwd(b: Seq<u8>, pos: nat, end: nat, e: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        d::read_tlv(b, pos, end) is Some,
        d::read_tlv(b, pos, end)->Some_0.tag == d::universal_constructed(d::SEQUENCE),
        i::parse_tlvs(sl(b, d::read_tlv(b, pos, end)->Some_0.cstart, d::read_tlv(b, pos, end)->Some_0.cend)) == Some(e),
    ensures
        i::parse_tlv(sl(b, pos, end)) is Some,
        s::sequence_elements(i::parse_tlv(sl(b, pos, end))->Some_0) == Some(e),
        tlv_view(b, pos, d::read_tlv(b, pos, end)->Some_0, i::parse_tlv(sl(b, pos, end))->Some_0),
{
    lemma_tlv(b, pos, end);
    let r = d::read_tlv(b, pos, end)->Some_0;
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    lemma_has_universal_tag(b, pos, r, u, d::SEQUENCE, true);
}

/// `der.rs`'s elements of a SEQUENCE, as `clazel-der` reads it.
pub proof fn lemma_sequence_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, e: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        s::sequence_elements(u) == Some(e),
    ensures
        d::read_tlv(b, pos, end) is Some,
        d::read_tlv(b, pos, end)->Some_0.tag == d::universal_constructed(d::SEQUENCE),
        tlv_view(b, pos, d::read_tlv(b, pos, end)->Some_0, u),
        d::expect_sequence(b, pos, end) == Some(
            (d::read_tlv(b, pos, end)->Some_0.cstart, d::read_tlv(b, pos, end)->Some_0.cend),
        ),
        i::parse_tlvs(sl(b, d::read_tlv(b, pos, end)->Some_0.cstart, d::read_tlv(b, pos, end)->Some_0.cend)) == Some(e),
        pos < d::read_tlv(b, pos, end)->Some_0.cstart,
        d::read_tlv(b, pos, end)->Some_0.cstart <= d::read_tlv(b, pos, end)->Some_0.cend,
        d::read_tlv(b, pos, end)->Some_0.cend <= end,
        d::read_tlv(b, pos, end)->Some_0.cend == pos + u.encoding.len(),
{
    lemma_tlv(b, pos, end);
    assert(tag_fits(u));
    let r = d::read_tlv(b, pos, end)->Some_0;
    lemma_has_universal_tag(b, pos, r, u, d::SEQUENCE, true);
}

// ---------------------------------------------------------------------
// The two comparisons of X.690 11.6.
// ---------------------------------------------------------------------

/// `not_after` is `der_octets_le_at`.
pub proof fn lemma_not_after(a: Seq<u8>, c: Seq<u8>, k: nat)
    ensures
        i::not_after(a, c, k) == n::der_octets_le_at(a, c, k),
    decreases (if a.len() > c.len() { a.len() } else { c.len() }) - k,
{
    let m = if a.len() > c.len() { a.len() } else { c.len() };
    if k < m {
        assert(i::padded_octet(a, k) as nat == n::padded_octet(a, k));
        assert(i::padded_octet(c, k) as nat == n::padded_octet(c, k));
        lemma_not_after(a, c, k + 1);
    }
}

/// `set_of_ordered` past one more element at the front.
pub proof fn lemma_ordered_shift(u: i::Tlv, e: Seq<i::Tlv>, k: nat)
    ensures
        i::set_of_ordered(seq![u] + e, k + 1) == i::set_of_ordered(e, k),
    decreases e.len() - k,
{
    let f = seq![u] + e;
    if k + 1 < e.len() {
        assert(f[(k + 1) as int] == e[k as int]);
        assert(f[(k + 2) as int] == e[(k + 1) as int]);
        lemma_ordered_shift(u, e, k + 1);
    }
}

/// `set_of_ordered` of one more at the front.
pub proof fn lemma_ordered_cons(u: i::Tlv, e: Seq<i::Tlv>)
    ensures
        i::set_of_ordered(seq![u] + e, 0) == ((e.len() == 0 || i::not_after(u.encoding, e[0].encoding, 0))
            && i::set_of_ordered(e, 0)),
{
    let f = seq![u] + e;
    lemma_ordered_shift(u, e, 0);
    assert(f[0] == u);
    if e.len() > 0 {
        assert(f[1] == e[0]);
    }
}

// ---------------------------------------------------------------------
// AttributeTypeAndValue.
// ---------------------------------------------------------------------

/// The two values of one attribute agree.
pub open spec fn attribute_agree(a: n::AttributeTypeAndValue, x: s::AttributeTypeAndValue) -> bool {
    &&& a.oid == x.attribute_type
    &&& a.value_der == x.value.encoding
    &&& x.value.class == d::class_bits(a.value_tag.class) as nat
    &&& x.value.constructed == a.value_tag.constructed
    &&& x.value.number == a.value_tag.number as nat
}

/// An attribute `name/spec.rs` reads (excluded: an addition, a tag number
/// over 16383, a subidentifier of 2^64 or more).
pub open spec fn attribute_in_domain(x: s::AttributeTypeAndValue) -> bool {
    &&& x.additions.len() == 0
    &&& tag_fits(x.value)
    &&& oid_fits(x.attribute_type)
}

/// One attribute, from `name/spec.rs` to `structures.rs`.
pub proof fn lemma_attribute_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        n::parse_attribute(b, pos, end) is Some,
        !tag_is_reserved(n::parse_attribute(b, pos, end)->Some_0.0.value_tag),
    ensures
        i::parse_tlv(sl(b, pos, end)) is Some,
        s::decode_attribute_type_and_value(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        attribute_agree(
            n::parse_attribute(b, pos, end)->Some_0.0,
            s::decode_attribute_type_and_value(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        attribute_in_domain(s::decode_attribute_type_and_value(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
        pos < n::parse_attribute(b, pos, end)->Some_0.1 <= end,
        n::parse_attribute(b, pos, end)->Some_0.0.der == i::parse_tlv(sl(b, pos, end))->Some_0.encoding,
        n::parse_attribute(b, pos, end)->Some_0.1 == d::read_tlv(b, pos, end)->Some_0.cend,
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
{
    let (a, next) = n::parse_attribute(b, pos, end)->Some_0;
    let t = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let (start, finish) = (t.cstart, t.cend);
    let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
    lemma_read_oid(b, start, finish);
    let v = d::read_tlv(b, after_oid, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after_oid, finish);
    lemma_tlvs_empty(b, finish);
    lemma_tlvs_cons(b, after_oid, finish, Seq::<i::Tlv>::empty());
    lemma_tlv(b, after_oid, finish);
    let vu = i::parse_tlv(sl(b, after_oid, finish))->Some_0;
    lemma_tlvs_cons(b, start, finish, seq![vu] + Seq::<i::Tlv>::empty());
    let ou = i::parse_tlv(sl(b, start, finish))->Some_0;
    let e = seq![ou] + (seq![vu] + Seq::<i::Tlv>::empty());
    lemma_sequence_fwd(b, pos, end, e);
    assert(e[0] == ou);
    assert(e[1] == vu);
    assert(e.len() == 2);
}

/// One attribute, from `structures.rs` to `name/spec.rs`.
pub proof fn lemma_attribute_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, x: s::AttributeTypeAndValue)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        s::decode_attribute_type_and_value(u) == Some(x),
        attribute_in_domain(x),
    ensures
        n::parse_attribute(b, pos, end) is Some,
        attribute_agree(n::parse_attribute(b, pos, end)->Some_0.0, x),
        n::parse_attribute(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
        n::parse_attribute(b, pos, end)->Some_0.0.der == u.encoding,
{
    let e = s::sequence_elements(u)->Some_0;
    lemma_sequence_back(b, pos, end, u, e);
    let t = d::read_tlv(b, pos, end)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    assert(e.len() == 2) by {
        assert(i::from_index(e, 2).len() == e.len() - 2);
    }
    assert(tag_fits(e[0]));
    lemma_tlvs_head(b, start, finish, e);
    lemma_read_oid(b, start, finish);
    let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
    let r = e.skip(1);
    assert(r[0] == e[1]);
    assert(x.value == e[1]);
    lemma_tlvs_head(b, after_oid, finish, r);
    let v = d::read_tlv(b, after_oid, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after_oid, finish);
    lemma_tlvs_none_left(b, v.cend, finish, r.skip(1));
    assert(v.tag.class == d::Class::Universal ==> true);
    lemma_class_all(v.tag);
}

/// Every class has its number.
pub proof fn lemma_class_all(tag: d::Tag)
    ensures
        d::class_bits(tag.class) <= 3,
{
}

// ---------------------------------------------------------------------
// One RDN's attributes.
// ---------------------------------------------------------------------

/// An attribute is a SEQUENCE.
pub proof fn lemma_attribute_tag(u: i::Tlv)
    requires
        s::decode_attribute_type_and_value(u) is Some,
    ensures
        tag_fits(u),
{
}

/// An RDN is a SET.
pub proof fn lemma_rdn_tag(u: i::Tlv)
    requires
        s::decode_relative_distinguished_name(u) is Some,
    ensures
        tag_fits(u),
{
}

/// `decode_attribute_list` past one more element at the front.
pub proof fn lemma_attribute_list_shift(u: i::Tlv, e: Seq<i::Tlv>, k: nat)
    ensures
        s::decode_attribute_list(seq![u] + e, k + 1) == s::decode_attribute_list(e, k),
    decreases e.len() - k,
{
    let f = seq![u] + e;
    if k < e.len() {
        assert(f[(k + 1) as int] == e[k as int]);
        lemma_attribute_list_shift(u, e, k + 1);
    }
}

/// From `name/spec.rs`, the attributes from `pos`.
#[verifier::spinoff_prover]
pub proof fn lemma_attributes_fwd(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    prior: Option<Seq<u8>>,
    acc: Seq<n::AttributeTypeAndValue>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        n::parse_attributes_acc(b, pos, end, prior, acc) is Some,
        forall|k: int|
            acc.len() <= k < n::parse_attributes_acc(b, pos, end, prior, acc)->Some_0.len()
                ==> !tag_is_reserved(
                #[trigger] n::parse_attributes_acc(b, pos, end, prior, acc)->Some_0[k].value_tag,
            ),
    ensures
        ({
            let all = n::parse_attributes_acc(b, pos, end, prior, acc)->Some_0;
            &&& all.len() >= acc.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& {
                let e = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& i::set_of_ordered(e, 0)
                &&& e.len() == all.len() - acc.len()
                &&& prior is Some && e.len() > 0 ==> n::der_octets_le(prior->Some_0, e[0].encoding)
                &&& s::decode_attribute_list(e, 0) is Some
                &&& {
                    let l = s::decode_attribute_list(e, 0)->Some_0;
                    &&& l.len() == e.len()
                    &&& forall|k: int|
                        0 <= k < l.len() ==> attribute_agree(#[trigger] all[k + acc.len()], l[k])
                    &&& forall|k: int| 0 <= k < l.len() ==> attribute_in_domain(#[trigger] l[k])
                }
            }
        }),
    decreases end - pos,
{
    hide(s::decode_attribute_type_and_value);
    hide(n::parse_attribute);
    let all = n::parse_attributes_acc(b, pos, end, prior, acc)->Some_0;
    if pos == end {
        lemma_tlvs_empty(b, pos);
    } else {
        let (a, next) = n::parse_attribute(b, pos, end)->Some_0;
        let acc2 = acc.push(a);
        assert(n::parse_attributes_acc(b, next, end, Some(a.der), acc2) == Some(all));
        assert(forall|k: int| acc2.len() <= k < all.len() ==> !tag_is_reserved(#[trigger] all[k].value_tag));
        lemma_attributes_fwd(b, next, end, Some(a.der), acc2);
        assert(all[acc.len() as int] == a);
        lemma_attribute_fwd(b, pos, end);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = i::parse_tlvs(sl(b, next, end))->Some_0;
        lemma_tlvs_cons(b, pos, end, r);
        let e = seq![u] + r;
        assert(e[0] == u);
        lemma_ordered_cons(u, r);
        if r.len() > 0 {
            lemma_not_after(a.der, r[0].encoding, 0);
        }
        lemma_attribute_list_shift(u, r, 0);
        let x = s::decode_attribute_type_and_value(u)->Some_0;
        let lr = s::decode_attribute_list(r, 0)->Some_0;
        let l = seq![x] + lr;
        assert(s::decode_attribute_list(e, 0) == Some(l));
        assert forall|k: int| 0 <= k < l.len() implies attribute_agree(#[trigger] all[k + acc.len()], l[k]) by {
            if k > 0 {
                assert(l[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            }
        }
        assert forall|k: int| 0 <= k < l.len() implies attribute_in_domain(#[trigger] l[k]) by {
            if k > 0 {
                assert(l[k] == lr[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// From `structures.rs`, the attributes from `pos`.
#[verifier::spinoff_prover]
pub proof fn lemma_attributes_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    prior: Option<Seq<u8>>,
    acc: Seq<n::AttributeTypeAndValue>,
    e: Seq<i::Tlv>,
    l: Seq<s::AttributeTypeAndValue>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(e),
        i::set_of_ordered(e, 0),
        s::decode_attribute_list(e, 0) == Some(l),
        forall|k: int| 0 <= k < l.len() ==> attribute_in_domain(#[trigger] l[k]),
        prior is Some && e.len() > 0 ==> n::der_octets_le(prior->Some_0, e[0].encoding),
    ensures
        n::parse_attributes_acc(b, pos, end, prior, acc) is Some,
        ({
            let all = n::parse_attributes_acc(b, pos, end, prior, acc)->Some_0;
            &&& all.len() == acc.len() + l.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& forall|k: int| 0 <= k < l.len() ==> attribute_agree(#[trigger] all[k + acc.len()], l[k])
        }),
    decreases end - pos,
{
    hide(s::decode_attribute_type_and_value);
    hide(n::parse_attribute);
    lemma_tlvs_none_left(b, pos, end, e);
    if pos < end {
        let u = e[0];
        let r = e.skip(1);
        assert(e =~= seq![u] + r);
        lemma_attribute_list_shift(u, r, 0);
        let x = s::decode_attribute_type_and_value(u)->Some_0;
        let lr = s::decode_attribute_list(r, 0)->Some_0;
        assert(l == seq![x] + lr);
        assert(l[0] == x);
        lemma_attribute_tag(u);
        lemma_tlvs_head(b, pos, end, e);
        lemma_attribute_back(b, pos, end, u, x);
        let (a, next) = n::parse_attribute(b, pos, end)->Some_0;
        let t = d::read_tlv(b, pos, end)->Some_0;
        assert(t.cend == next);
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        lemma_ordered_cons(u, r);
        if r.len() > 0 {
            lemma_not_after(a.der, r[0].encoding, 0);
        }
        assert forall|k: int| 0 <= k < lr.len() implies attribute_in_domain(#[trigger] lr[k]) by {
            assert(l[k + 1] == lr[k]);
        }
        let acc2 = acc.push(a);
        lemma_attributes_back(b, next, end, Some(a.der), acc2, r, lr);
        let all = n::parse_attributes_acc(b, pos, end, prior, acc)->Some_0;
        assert(all == n::parse_attributes_acc(b, next, end, Some(a.der), acc2)->Some_0);
        assert forall|k: int| 0 <= k < l.len() implies attribute_agree(#[trigger] all[k + acc.len()], l[k]) by {
            if k > 0 {
                assert(l[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            } else {
                assert(all[acc.len() as int] == acc2[acc.len() as int]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    } else {
        assert(l.len() == 0);
    }
}

// ---------------------------------------------------------------------
// RelativeDistinguishedName.
// ---------------------------------------------------------------------

/// The two values of one RDN agree.
pub open spec fn rdn_agree(r: n::RelativeDistinguishedName, l: s::RelativeDistinguishedName) -> bool {
    &&& r.attributes.len() == l.len()
    &&& forall|k: int| 0 <= k < l.len() ==> attribute_agree(#[trigger] r.attributes[k], l[k])
}

/// Every attribute of an RDN is one `name/spec.rs` reads.
pub open spec fn rdn_in_domain(l: s::RelativeDistinguishedName) -> bool {
    forall|k: int| 0 <= k < l.len() ==> attribute_in_domain(#[trigger] l[k])
}

/// No attribute value of an RDN has the reserved tag.
pub open spec fn rdn_tags_plain(r: n::RelativeDistinguishedName) -> bool {
    forall|k: int| 0 <= k < r.attributes.len() ==> !tag_is_reserved(#[trigger] r.attributes[k].value_tag)
}

/// One RDN, from `name/spec.rs` to `structures.rs`.
pub proof fn lemma_rdn_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        n::parse_rdn(b, pos, end) is Some,
        rdn_tags_plain(n::parse_rdn(b, pos, end)->Some_0.0),
    ensures
        i::parse_tlv(sl(b, pos, end)) is Some,
        s::decode_relative_distinguished_name(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        rdn_agree(
            n::parse_rdn(b, pos, end)->Some_0.0,
            s::decode_relative_distinguished_name(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        rdn_in_domain(s::decode_relative_distinguished_name(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
        pos < n::parse_rdn(b, pos, end)->Some_0.1 <= end,
        d::read_tlv(b, pos, end) is Some,
        n::parse_rdn(b, pos, end)->Some_0.1 == d::read_tlv(b, pos, end)->Some_0.cend,
{
    let (rdn, next) = n::parse_rdn(b, pos, end)->Some_0;
    let t = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let (start, finish) = (t.cstart, t.cend);
    let empty = Seq::<n::AttributeTypeAndValue>::empty();
    let all = n::parse_attributes_acc(b, start, finish, None, empty)->Some_0;
    assert(all == rdn.attributes);
    lemma_attributes_fwd(b, start, finish, None, empty);
    lemma_tlv(b, pos, end);
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    lemma_has_universal_tag(b, pos, t, u, d::SET, true);
    let e = i::parse_tlvs(sl(b, start, finish))->Some_0;
    let l = s::decode_attribute_list(e, 0)->Some_0;
    assert forall|k: int| 0 <= k < l.len() implies attribute_agree(#[trigger] rdn.attributes[k], l[k]) by {
        assert(all[k + empty.len()] == rdn.attributes[k]);
    }
}

/// One RDN, from `structures.rs` to `name/spec.rs`.
pub proof fn lemma_rdn_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    u: i::Tlv,
    l: s::RelativeDistinguishedName,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        s::decode_relative_distinguished_name(u) == Some(l),
        rdn_in_domain(l),
    ensures
        n::parse_rdn(b, pos, end) is Some,
        rdn_agree(n::parse_rdn(b, pos, end)->Some_0.0, l),
        n::parse_rdn(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
{
    lemma_tlv(b, pos, end);
    assert(tag_fits(u));
    let t = d::read_tlv(b, pos, end)->Some_0;
    lemma_has_universal_tag(b, pos, t, u, d::SET, true);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let (start, finish) = (t.cstart, t.cend);
    let e = i::parse_tlvs(u.contents)->Some_0;
    let empty = Seq::<n::AttributeTypeAndValue>::empty();
    lemma_attributes_back(b, start, finish, None, empty, e, l);
    let all = n::parse_attributes_acc(b, start, finish, None, empty)->Some_0;
    assert forall|k: int| 0 <= k < l.len() implies attribute_agree(#[trigger] all[k], l[k]) by {
        assert(all[k + empty.len()] == all[k]);
    }
    assert(l.len() > 0) by {
        // `decode_attribute_list` gives one value for each element.
        lemma_attribute_list_len(e, 0);
    }
}

/// `decode_attribute_list` gives one value for each element.
pub proof fn lemma_attribute_list_len(e: Seq<i::Tlv>, k: nat)
    requires
        k <= e.len(),
        s::decode_attribute_list(e, k) is Some,
    ensures
        s::decode_attribute_list(e, k)->Some_0.len() == e.len() - k,
    decreases e.len() - k,
{
    if k < e.len() {
        lemma_attribute_list_len(e, k + 1);
    }
}

// ---------------------------------------------------------------------
// RDNSequence and Name.
// ---------------------------------------------------------------------

/// `decode_rdn_list` past one more element at the front.
pub proof fn lemma_rdn_list_shift(u: i::Tlv, e: Seq<i::Tlv>, k: nat)
    ensures
        s::decode_rdn_list(seq![u] + e, k + 1) == s::decode_rdn_list(e, k),
    decreases e.len() - k,
{
    let f = seq![u] + e;
    if k < e.len() {
        assert(f[(k + 1) as int] == e[k as int]);
        lemma_rdn_list_shift(u, e, k + 1);
    }
}

/// From `name/spec.rs`, the RDNs from `pos`.
#[verifier::spinoff_prover]
pub proof fn lemma_rdns_fwd(b: Seq<u8>, pos: nat, end: nat, acc: Seq<n::RelativeDistinguishedName>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        n::parse_rdns_acc(b, pos, end, acc) is Some,
        forall|k: int|
            acc.len() <= k < n::parse_rdns_acc(b, pos, end, acc)->Some_0.len() ==> rdn_tags_plain(
                #[trigger] n::parse_rdns_acc(b, pos, end, acc)->Some_0[k],
            ),
    ensures
        ({
            let all = n::parse_rdns_acc(b, pos, end, acc)->Some_0;
            &&& all.len() >= acc.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& {
                let e = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& s::decode_rdn_list(e, 0) is Some
                &&& {
                    let l = s::decode_rdn_list(e, 0)->Some_0;
                    &&& l.len() == all.len() - acc.len()
                    &&& forall|k: int| 0 <= k < l.len() ==> rdn_agree(#[trigger] all[k + acc.len()], l[k])
                    &&& forall|k: int| 0 <= k < l.len() ==> rdn_in_domain(#[trigger] l[k])
                }
            }
        }),
    decreases end - pos,
{
    hide(s::decode_relative_distinguished_name);
    hide(n::parse_rdn);
    let all = n::parse_rdns_acc(b, pos, end, acc)->Some_0;
    if pos == end {
        lemma_tlvs_empty(b, pos);
    } else {
        let (rdn, next) = n::parse_rdn(b, pos, end)->Some_0;
        let acc2 = acc.push(rdn);
        assert(n::parse_rdns_acc(b, next, end, acc2) == Some(all));
        assert(forall|k: int| acc2.len() <= k < all.len() ==> rdn_tags_plain(#[trigger] all[k]));
        lemma_rdns_fwd(b, next, end, acc2);
        assert(all[acc.len() as int] == rdn);
        lemma_rdn_fwd(b, pos, end);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = i::parse_tlvs(sl(b, next, end))->Some_0;
        lemma_tlv(b, pos, end);
        assert(!tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag));
        lemma_tlvs_cons(b, pos, end, r);
        lemma_rdn_list_shift(u, r, 0);
        let x = s::decode_relative_distinguished_name(u)->Some_0;
        let lr = s::decode_rdn_list(r, 0)->Some_0;
        let l = seq![x] + lr;
        let e = seq![u] + r;
        assert(e[0] == u);
        assert(s::decode_rdn_list(e, 0) == Some(l));
        assert forall|k: int| 0 <= k < l.len() implies rdn_agree(#[trigger] all[k + acc.len()], l[k]) by {
            if k > 0 {
                assert(l[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            }
        }
        assert forall|k: int| 0 <= k < l.len() implies rdn_in_domain(#[trigger] l[k]) by {
            if k > 0 {
                assert(l[k] == lr[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// From `structures.rs`, the RDNs from `pos`.
#[verifier::spinoff_prover]
pub proof fn lemma_rdns_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    acc: Seq<n::RelativeDistinguishedName>,
    e: Seq<i::Tlv>,
    l: Seq<s::RelativeDistinguishedName>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(e),
        s::decode_rdn_list(e, 0) == Some(l),
        forall|k: int| 0 <= k < l.len() ==> rdn_in_domain(#[trigger] l[k]),
    ensures
        n::parse_rdns_acc(b, pos, end, acc) is Some,
        ({
            let all = n::parse_rdns_acc(b, pos, end, acc)->Some_0;
            &&& all.len() == acc.len() + l.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& forall|k: int| 0 <= k < l.len() ==> rdn_agree(#[trigger] all[k + acc.len()], l[k])
        }),
    decreases end - pos,
{
    hide(s::decode_relative_distinguished_name);
    hide(n::parse_rdn);
    lemma_tlvs_none_left(b, pos, end, e);
    if pos < end {
        let u = e[0];
        let r = e.skip(1);
        assert(e =~= seq![u] + r);
        lemma_rdn_list_shift(u, r, 0);
        let x = s::decode_relative_distinguished_name(u)->Some_0;
        let lr = s::decode_rdn_list(r, 0)->Some_0;
        assert(l == seq![x] + lr);
        assert(l[0] == x);
        lemma_rdn_tag(u);
        lemma_tlvs_head(b, pos, end, e);
        lemma_rdn_back(b, pos, end, u, x);
        let (rdn, next) = n::parse_rdn(b, pos, end)->Some_0;
        let t = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        assert(t.cend == next);
        assert forall|k: int| 0 <= k < lr.len() implies rdn_in_domain(#[trigger] lr[k]) by {
            assert(l[k + 1] == lr[k]);
        }
        let acc2 = acc.push(rdn);
        lemma_rdns_back(b, next, end, acc2, r, lr);
        let all = n::parse_rdns_acc(b, pos, end, acc)->Some_0;
        assert(all == n::parse_rdns_acc(b, next, end, acc2)->Some_0);
        assert forall|k: int| 0 <= k < l.len() implies rdn_agree(#[trigger] all[k + acc.len()], l[k]) by {
            if k > 0 {
                assert(l[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            } else {
                assert(all[acc.len() as int] == acc2[acc.len() as int]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    } else {
        assert(l.len() == 0);
    }
}

/// The two values of one Name agree.
pub open spec fn name_agree(a: n::Name, x: s::Name) -> bool {
    &&& a.rdns.len() == x.rdn_sequence.len()
    &&& forall|k: int| 0 <= k < a.rdns.len() ==> rdn_agree(#[trigger] a.rdns[k], x.rdn_sequence[k])
}

/// A Name `name/spec.rs` reads.
pub open spec fn name_in_domain(x: s::Name) -> bool {
    forall|k: int| 0 <= k < x.rdn_sequence.len() ==> rdn_in_domain(#[trigger] x.rdn_sequence[k])
}

/// No attribute value of the Name has the reserved tag.
pub open spec fn name_tags_plain(a: n::Name) -> bool {
    forall|k: int| 0 <= k < a.rdns.len() ==> rdn_tags_plain(#[trigger] a.rdns[k])
}

/// **`theorem_name`, from `name/spec.rs`.** A Name `parse_name` reads,
/// `decode_name` reads to the same value, unless an attribute value has the
/// reserved tag universal 0.
pub proof fn theorem_name_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        n::parse_name(input) is Some,
        name_tags_plain(n::parse_name(input)->Some_0),
    ensures
        i::parse_single(input) is Some,
        s::decode_name(i::parse_single(input)->Some_0) is Some,
        name_agree(n::parse_name(input)->Some_0, s::decode_name(i::parse_single(input)->Some_0)->Some_0),
        name_in_domain(s::decode_name(i::parse_single(input)->Some_0)->Some_0),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, end) = (t.cstart, t.cend);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let empty = Seq::<n::RelativeDistinguishedName>::empty();
    let a = n::parse_name(input)->Some_0;
    assert(a.rdns == n::parse_rdns_acc(b, start, end, empty)->Some_0);
    assert(forall|k: int| 0 <= k < a.rdns.len() ==> rdn_tags_plain(#[trigger] a.rdns[k]));
    lemma_rdns_fwd(b, start, end, empty);
    let e = i::parse_tlvs(sl(b, start, end))->Some_0;
    lemma_sequence_fwd(b, 0, len, e);
    lemma_single(b, 0, len);
    let l = s::decode_rdn_list(e, 0)->Some_0;
    assert forall|k: int| 0 <= k < a.rdns.len() implies rdn_agree(#[trigger] a.rdns[k], l[k]) by {
        assert(a.rdns[k + empty.len()] == a.rdns[k]);
    }
}

/// **`theorem_name`, from `structures.rs`.** A Name `decode_name` reads,
/// `parse_name` reads to the same value, unless an attribute has an addition,
/// a tag number over 16383 or a subidentifier of 2^64 or more.
pub proof fn theorem_name_back(input: Seq<u8>, u: i::Tlv, x: s::Name)
    requires
        input.len() < two64(),
        i::parse_single(input) == Some(u),
        s::decode_name(u) == Some(x),
        name_in_domain(x),
    ensures
        n::parse_name(input) is Some,
        name_agree(n::parse_name(input)->Some_0, x),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let e = s::sequence_elements(u)->Some_0;
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, e);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, end) = (t.cstart, t.cend);
    let empty = Seq::<n::RelativeDistinguishedName>::empty();
    let l = x.rdn_sequence;
    assert(forall|k: int| 0 <= k < l.len() ==> rdn_in_domain(#[trigger] l[k]));
    lemma_rdns_back(b, start, end, empty, e, l);
    let a = n::parse_name(input)->Some_0;
    assert(a.rdns == n::parse_rdns_acc(b, start, end, empty)->Some_0);
    assert forall|k: int| 0 <= k < a.rdns.len() implies rdn_agree(#[trigger] a.rdns[k], l[k]) by {
        assert(a.rdns[k + empty.len()] == a.rdns[k]);
    }
}

} // verus!
