//! `Extension` and `GeneralName` of `independent/extensions.rs` against
//! `extensions/spec.rs`. The domain is explained in `equivalence.rs`.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use super::equivalence_der::*;
#[cfg(verus_only)]
use super::equivalence_name::*;
#[cfg(verus_only)]
use super::equivalence_structures::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

// ---------------------------------------------------------------------
// Extension.
// ---------------------------------------------------------------------

/// The two values of one Extension agree. `extensions/spec.rs` keeps
/// `extnValue` unread, so the value is the octets.
pub open spec fn extension_agree(a: x::Extension, y: e::Extension) -> bool {
    &&& a.oid == y.extn_id
    &&& a.critical == y.critical
    &&& a.value == y.extn_value
}

/// An Extension `extensions/spec.rs` reads (excluded: an addition, a
/// subidentifier of 2^64 or more).
pub open spec fn extension_in_domain(y: e::Extension) -> bool {
    &&& y.additions.len() == 0
    &&& oid_fits(y.extn_id)
}

/// `extnValue` holds what `extensions.rs` reads for its `extnId`.
/// `extensions/spec.rs` leaves that to later decoders.
pub open spec fn value_decodes(a: x::Extension) -> bool {
    e::decode_extension_value(a.oid, a.value) is Some
}

/// BOOLEAN at `pos`: the two agree exactly.
pub proof fn lemma_read_boolean(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match d::read_boolean(b, pos, end) {
            Some((v, next)) => {
                &&& d::read_tlv(b, pos, end) is Some
                &&& !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag)
                &&& d::read_tlv(b, pos, end)->Some_0.cend == next
                &&& pos < next <= end
                &&& i::parse_tlv(sl(b, pos, end)) is Some
                &&& i::decode_boolean(i::parse_tlv(sl(b, pos, end))->Some_0) == Some(v)
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => i::decode_boolean(u) is None,
                None => true,
            },
        },
{
    lemma_tlv(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some(r) = d::read_tlv(b, pos, end) {
        if !tag_is_reserved(r.tag) {
            let u = i::parse_tlv(sl(b, pos, end))->Some_0;
            lemma_has_universal_tag(b, pos, r, u, d::BOOLEAN, false);
        }
    } else {
        if let Some(u) = i::parse_tlv(sl(b, pos, end)) {
            assert(i::decode_boolean(u) is Some ==> tag_fits(u));
        }
    }
}

/// One Extension, from `extensions/spec.rs` to `extensions.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_extension_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        x::parse_extension(b, pos, end) is Some,
        value_decodes(x::parse_extension(b, pos, end)->Some_0.0),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == x::parse_extension(b, pos, end)->Some_0.1,
        pos < x::parse_extension(b, pos, end)->Some_0.1 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        e::decode_extension(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        extension_agree(
            x::parse_extension(b, pos, end)->Some_0.0,
            e::decode_extension(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        extension_in_domain(e::decode_extension(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
{
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    let (start, finish) = (r.cstart, r.cend);
    lemma_read_oid(b, start, finish);
    let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
    let field = d::read_tlv(b, after_oid, finish)->Some_0;
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    if field.tag == d::universal_primitive(d::BOOLEAN) {
        lemma_read_boolean(b, after_oid, finish);
        let (v, after_critical) = d::read_boolean(b, after_oid, finish)->Some_0;
        lemma_read_octet_string(b, after_critical, finish);
        lemma_tlvs_cons(b, after_critical, finish, none);
        let vu = i::parse_tlv(sl(b, after_critical, finish))->Some_0;
        lemma_tlvs_cons(b, after_oid, finish, seq![vu] + none);
        let bu = i::parse_tlv(sl(b, after_oid, finish))->Some_0;
        lemma_tlvs_cons(b, start, finish, seq![bu] + (seq![vu] + none));
        let ou = i::parse_tlv(sl(b, start, finish))->Some_0;
        let l = seq![ou] + (seq![bu] + (seq![vu] + none));
        lemma_sequence_fwd(b, pos, end, l);
        assert(l[0] == ou);
        assert(l[1] == bu);
        assert(l[2] == vu);
        assert(l.len() == 3);
    } else {
        lemma_read_octet_string(b, after_oid, finish);
        lemma_tlvs_cons(b, after_oid, finish, none);
        let vu = i::parse_tlv(sl(b, after_oid, finish))->Some_0;
        lemma_tlvs_cons(b, start, finish, seq![vu] + none);
        let ou = i::parse_tlv(sl(b, start, finish))->Some_0;
        let l = seq![ou] + (seq![vu] + none);
        lemma_sequence_fwd(b, pos, end, l);
        assert(l[0] == ou);
        assert(l[1] == vu);
        assert(l.len() == 2);
    }
}

/// One Extension, from `extensions.rs` to `extensions/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_extension_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, y: e::Extension)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        e::decode_extension(u) == Some(y),
        extension_in_domain(y),
    ensures
        x::parse_extension(b, pos, end) is Some,
        extension_agree(x::parse_extension(b, pos, end)->Some_0.0, y),
        x::parse_extension(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
{
    let l = s::sequence_elements(u)->Some_0;
    lemma_sequence_back(b, pos, end, u, l);
    let r = d::read_tlv(b, pos, end)->Some_0;
    let (start, finish) = (r.cstart, r.cend);
    let idx: nat = if i::tag_at(l, 1, 0, 1) { 2 } else { 1 };
    assert(l.len() == idx + 1) by {
        assert(i::from_index(l, idx + 1).len() == 0);
        if l.len() > idx + 1 {
            assert(i::from_index(l, idx + 1).len() == l.len() - (idx + 1));
        }
    }
    assert(tag_fits(l[0]));
    lemma_tlvs_head(b, start, finish, l);
    lemma_read_oid(b, start, finish);
    let (oid, after_oid) = d::read_oid(b, start, finish)->Some_0;
    let rest = l.skip(1);
    assert(rest[0] == l[1]);
    assert(tag_fits(l[1]));
    lemma_tlvs_head(b, after_oid, finish, rest);
    let field = d::read_tlv(b, after_oid, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, after_oid, finish);
    lemma_has_universal_tag(b, after_oid, field, l[1], d::BOOLEAN, false);
    if idx == 2 {
        lemma_read_boolean(b, after_oid, finish);
        let last = rest.skip(1);
        assert(last[0] == l[2]);
        assert(tag_fits(l[2]));
        lemma_tlvs_head(b, field.cend, finish, last);
        lemma_read_octet_string(b, field.cend, finish);
        let v = d::read_tlv(b, field.cend, finish)->Some_0;
        lemma_tlvs_none_left(b, v.cend, finish, last.skip(1));
    } else {
        lemma_read_octet_string(b, after_oid, finish);
        lemma_tlvs_none_left(b, field.cend, finish, rest.skip(1));
    }
}

/// An Extension is a SEQUENCE.
pub proof fn lemma_extension_tag(u: i::Tlv)
    requires
        e::decode_extension(u) is Some,
    ensures
        tag_fits(u),
{
}

/// `decode_extension_list` past one more element at the front.
pub proof fn lemma_extension_list_shift(u: i::Tlv, l: Seq<i::Tlv>, k: nat)
    ensures
        e::decode_extension_list(seq![u] + l, k + 1) == e::decode_extension_list(l, k),
    decreases l.len() - k,
{
    let f = seq![u] + l;
    if k < l.len() {
        assert(f[(k + 1) as int] == l[k as int]);
        lemma_extension_list_shift(u, l, k + 1);
    }
}

/// From `extensions/spec.rs`, the extensions from `pos`.
pub proof fn lemma_extensions_fwd(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    seen: Seq<Seq<nat>>,
    acc: Seq<x::Extension>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        x::parse_extensions_acc(b, pos, end, seen, acc) is Some,
        forall|k: int|
            acc.len() <= k < x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0.len() ==> value_decodes(
                #[trigger] x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0[k],
            ),
    ensures
        ({
            let all = x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0;
            &&& x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.1 == end
            &&& all.len() >= acc.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& {
                let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& l.len() == all.len() - acc.len()
                &&& e::decode_extension_list(l, 0) is Some
                &&& {
                    let v = e::decode_extension_list(l, 0)->Some_0;
                    &&& v.len() == l.len()
                    &&& forall|k: int| 0 <= k < v.len() ==> extension_agree(#[trigger] all[k + acc.len()], v[k])
                    &&& forall|k: int| 0 <= k < v.len() ==> extension_in_domain(#[trigger] v[k])
                }
            }
        }),
    decreases end - pos,
{
    hide(e::decode_extension);
    hide(x::parse_extension);
    let all = x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0;
    if pos == end {
        lemma_tlvs_empty(b, pos);
    } else {
        let (a, next) = x::parse_extension(b, pos, end)->Some_0;
        let acc2 = acc.push(a);
        let seen2 = seen.push(a.oid);
        assert(x::parse_extensions_acc(b, next, end, seen2, acc2) == x::parse_extensions_acc(b, pos, end, seen, acc));
        assert(forall|k: int| acc2.len() <= k < all.len() ==> value_decodes(#[trigger] all[k]));
        lemma_extensions_fwd(b, next, end, seen2, acc2);
        assert(all[acc.len() as int] == a);
        lemma_extension_fwd(b, pos, end);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = i::parse_tlvs(sl(b, next, end))->Some_0;
        lemma_tlvs_cons(b, pos, end, r);
        lemma_extension_list_shift(u, r, 0);
        let y = e::decode_extension(u)->Some_0;
        let lr = e::decode_extension_list(r, 0)->Some_0;
        let v = seq![y] + lr;
        let l = seq![u] + r;
        assert(l[0] == u);
        assert(e::decode_extension_list(l, 0) == Some(v));
        assert forall|k: int| 0 <= k < v.len() implies extension_agree(#[trigger] all[k + acc.len()], v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            }
        }
        assert forall|k: int| 0 <= k < v.len() implies extension_in_domain(#[trigger] v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// `oid_seen` finds a member.
pub proof fn lemma_oid_seen(seen: Seq<Seq<nat>>, oid: Seq<nat>, k: int)
    requires
        0 <= k <= seen.len(),
        x::oid_seen(seen, oid, k),
    ensures
        exists|m: int| k <= m < seen.len() && seen[m] == oid,
    decreases seen.len() - k,
{
    if seen[k] =~= oid {
        assert(seen[k] == oid);
    } else {
        lemma_oid_seen(seen, oid, k + 1);
    }
}

/// No two extensions of the list have one `extnId`, and none has one in
/// `seen`.
pub open spec fn ids_fresh(v: Seq<e::Extension>, seen: Seq<Seq<nat>>) -> bool {
    &&& forall|j: int, k: int| 0 <= j < k < v.len() ==> #[trigger] v[j].extn_id != #[trigger] v[k].extn_id
    &&& forall|m: int, k: int| 0 <= m < seen.len() && 0 <= k < v.len() ==> #[trigger] seen[m]
        != #[trigger] v[k].extn_id
}

/// From `extensions.rs`, the extensions from `pos`.
pub proof fn lemma_extensions_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    seen: Seq<Seq<nat>>,
    acc: Seq<x::Extension>,
    l: Seq<i::Tlv>,
    v: Seq<e::Extension>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        e::decode_extension_list(l, 0) == Some(v),
        forall|k: int| 0 <= k < v.len() ==> extension_in_domain(#[trigger] v[k]),
        ids_fresh(v, seen),
    ensures
        x::parse_extensions_acc(b, pos, end, seen, acc) is Some,
        x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.1 == end,
        ({
            let all = x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0;
            &&& all.len() == acc.len() + v.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& forall|k: int| 0 <= k < v.len() ==> extension_agree(#[trigger] all[k + acc.len()], v[k])
        }),
    decreases end - pos,
{
    hide(e::decode_extension);
    hide(x::parse_extension);
    lemma_tlvs_none_left(b, pos, end, l);
    if pos < end {
        let u = l[0];
        let r = l.skip(1);
        assert(l =~= seq![u] + r);
        lemma_extension_list_shift(u, r, 0);
        let y = e::decode_extension(u)->Some_0;
        let lr = e::decode_extension_list(r, 0)->Some_0;
        assert(v == seq![y] + lr);
        assert(v[0] == y);
        lemma_extension_tag(u);
        lemma_tlvs_head(b, pos, end, l);
        lemma_extension_back(b, pos, end, u, y);
        let (a, next) = x::parse_extension(b, pos, end)->Some_0;
        let t = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        assert(t.cend == next);
        assert forall|k: int| 0 <= k < lr.len() implies extension_in_domain(#[trigger] lr[k]) by {
            assert(v[k + 1] == lr[k]);
        }
        if x::oid_seen(seen, a.oid, 0) {
            lemma_oid_seen(seen, a.oid, 0);
            let m = choose|m: int| 0 <= m < seen.len() && seen[m] == a.oid;
            assert(seen[m] != v[0].extn_id);
        }
        let acc2 = acc.push(a);
        let seen2 = seen.push(a.oid);
        assert forall|p: int, q: int| 0 <= p < q < lr.len() implies #[trigger] lr[p].extn_id != #[trigger] lr[q].extn_id by {
            assert(v[p + 1] == lr[p]);
            assert(v[q + 1] == lr[q]);
            assert(v[p + 1].extn_id != v[q + 1].extn_id);
        }
        assert forall|m: int, q: int| 0 <= m < seen2.len() && 0 <= q < lr.len() implies #[trigger] seen2[m]
            != #[trigger] lr[q].extn_id by {
            assert(v[q + 1] == lr[q]);
            if m < seen.len() {
                assert(seen2[m] == seen[m]);
                assert(seen[m] != v[q + 1].extn_id);
            } else {
                assert(seen2[m] == a.oid);
                assert(v[0].extn_id != v[q + 1].extn_id);
            }
        }
        lemma_extensions_back(b, next, end, seen2, acc2, r, lr);
        let all = x::parse_extensions_acc(b, pos, end, seen, acc)->Some_0.0;
        assert(all == x::parse_extensions_acc(b, next, end, seen2, acc2)->Some_0.0);
        assert forall|k: int| 0 <= k < v.len() implies extension_agree(#[trigger] all[k + acc.len()], v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            } else {
                assert(all[acc.len() as int] == acc2[acc.len() as int]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    } else {
        assert(v.len() == 0);
    }
}

/// The two lists of Extension agree.
pub open spec fn extensions_agree(a: Seq<x::Extension>, v: Seq<e::Extension>) -> bool {
    &&& a.len() == v.len()
    &&& forall|k: int| 0 <= k < a.len() ==> extension_agree(#[trigger] a[k], v[k])
}

/// Every Extension of the list is one `extensions/spec.rs` reads.
pub open spec fn extensions_in_domain(v: Seq<e::Extension>) -> bool {
    &&& forall|k: int| 0 <= k < v.len() ==> extension_in_domain(#[trigger] v[k])
    &&& ids_fresh(v, Seq::<Seq<nat>>::empty())
}

/// `decode_extension_list` gives one value for each element.
pub proof fn lemma_extension_list_len(l: Seq<i::Tlv>, k: nat)
    requires
        k <= l.len(),
        e::decode_extension_list(l, k) is Some,
    ensures
        e::decode_extension_list(l, k)->Some_0.len() == l.len() - k,
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_extension_list_len(l, k + 1);
    }
}

/// **`theorem_extensions`, from `extensions/spec.rs`.** Extensions
/// `parse_extensions` reads, `structures.rs` reads to the same values, unless
/// an `extnValue` is one `extensions.rs` refuses.
pub proof fn theorem_extensions_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        x::parse_extensions(input) is Some,
        forall|k: int|
            0 <= k < x::parse_extensions(input)->Some_0.len() ==> value_decodes(
                #[trigger] x::parse_extensions(input)->Some_0[k],
            ),
    ensures
        i::parse_single(input) is Some,
        s::sequence_elements(i::parse_single(input)->Some_0) is Some,
        s::sequence_elements(i::parse_single(input)->Some_0)->Some_0.len() > 0,
        e::decode_extension_list(s::sequence_elements(i::parse_single(input)->Some_0)->Some_0, 0) is Some,
        extensions_agree(
            x::parse_extensions(input)->Some_0,
            e::decode_extension_list(s::sequence_elements(i::parse_single(input)->Some_0)->Some_0, 0)->Some_0,
        ),
        forall|k: int|
            0 <= k < e::decode_extension_list(
                s::sequence_elements(i::parse_single(input)->Some_0)->Some_0,
                0,
            )->Some_0.len() ==> extension_in_domain(
                #[trigger] e::decode_extension_list(
                    s::sequence_elements(i::parse_single(input)->Some_0)->Some_0,
                    0,
                )->Some_0[k],
            ),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<Seq<nat>>::empty();
    let empty = Seq::<x::Extension>::empty();
    let all = x::parse_extensions(input)->Some_0;
    assert(x::parse_extensions_from(b, start, finish, none) == x::parse_extensions_acc(b, start, finish, none, empty));
    assert(all == x::parse_extensions_acc(b, start, finish, none, empty)->Some_0.0);
    lemma_extensions_fwd(b, start, finish, none, empty);
    let l = i::parse_tlvs(sl(b, start, finish))->Some_0;
    lemma_sequence_fwd(b, 0, len, l);
    lemma_single(b, 0, len);
    let v = e::decode_extension_list(l, 0)->Some_0;
    assert forall|k: int| 0 <= k < all.len() implies extension_agree(#[trigger] all[k], v[k]) by {
        assert(all[k + empty.len()] == all[k]);
    }
}

/// **`theorem_extensions`, from `structures.rs`.** Extensions `structures.rs`
/// reads, `parse_extensions` reads to the same values, unless one has an
/// addition or a subidentifier of 2^64 or more, or two have one `extnId`.
pub proof fn theorem_extensions_back(input: Seq<u8>, u: i::Tlv, l: Seq<i::Tlv>, v: Seq<e::Extension>)
    requires
        input.len() < two64(),
        i::parse_single(input) == Some(u),
        s::sequence_elements(u) == Some(l),
        l.len() > 0,
        e::decode_extension_list(l, 0) == Some(v),
        extensions_in_domain(v),
    ensures
        x::parse_extensions(input) is Some,
        extensions_agree(x::parse_extensions(input)->Some_0, v),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<Seq<nat>>::empty();
    let empty = Seq::<x::Extension>::empty();
    lemma_extension_list_len(l, 0);
    lemma_tlvs_none_left(b, start, finish, l);
    lemma_extensions_back(b, start, finish, none, empty, l, v);
    let all = x::parse_extensions_acc(b, start, finish, none, empty)->Some_0.0;
    assert(x::parse_extensions_from(b, start, finish, none) == x::parse_extensions_acc(b, start, finish, none, empty));
    assert(x::parse_extensions(input) == Some(all));
    assert forall|k: int| 0 <= k < all.len() implies extension_agree(#[trigger] all[k], v[k]) by {
        assert(all[k + empty.len()] == all[k]);
    }
}

// ---------------------------------------------------------------------
// GeneralName.
// ---------------------------------------------------------------------

/// `all_ia5` is `ia5_bytes`.
pub proof fn lemma_ia5(s: Seq<u8>, k: nat)
    ensures
        i::all_ia5(s, k) == x::ia5_bytes(s, k as int),
    decreases s.len() - k,
{
    if k < s.len() {
        lemma_ia5(s, k + 1);
    }
}

/// The two values of one GeneralName agree. `extensions/spec.rs` keeps every
/// form but two as its encoding.
pub open spec fn general_name_agree(a: x::GeneralName, y: e::GeneralName) -> bool {
    match a {
        x::GeneralName::DnsName(v) => y == e::GeneralName::DNSName(v),
        x::GeneralName::IpAddress(v) => y == e::GeneralName::IPAddress(v),
        x::GeneralName::Other(_, v) => {
            &&& i::parse_single(v) is Some
            &&& e::decode_general_name(i::parse_single(v)->Some_0) == Some(y)
            &&& !(y is DNSName || y is IPAddress)
        },
    }
}

/// A GeneralName `extensions/spec.rs` reads: a defined form, a dNSName that
/// is not empty and an iPAddress of 4 or 16 octets.
pub open spec fn general_name_in_domain(y: e::GeneralName) -> bool {
    match y {
        e::GeneralName::Unknown(_) => false,
        e::GeneralName::DNSName(v) => v.len() > 0,
        e::GeneralName::IPAddress(v) => v.len() == 4 || v.len() == 16,
        _ => true,
    }
}

/// A form `extensions/spec.rs` keeps unread is one `extensions.rs` reads.
pub open spec fn other_form_decodes(a: x::GeneralName) -> bool {
    match a {
        x::GeneralName::Other(_, v) => {
            &&& i::parse_single(v) is Some
            &&& e::decode_general_name(i::parse_single(v)->Some_0) is Some
        },
        _ => true,
    }
}

/// The context class of a tag.
pub proof fn lemma_context_class(tag: d::Tag)
    ensures
        (d::class_bits(tag.class) == 2) == (tag.class == d::Class::ContextSpecific),
{
}

/// One GeneralName, from `extensions/spec.rs` to `extensions.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_general_name_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        x::parse_general_name(b, pos, end) is Some,
        other_form_decodes(x::parse_general_name(b, pos, end)->Some_0.0),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == x::parse_general_name(b, pos, end)->Some_0.1,
        pos < x::parse_general_name(b, pos, end)->Some_0.1 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        e::decode_general_name(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        general_name_agree(
            x::parse_general_name(b, pos, end)->Some_0.0,
            e::decode_general_name(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        general_name_in_domain(e::decode_general_name(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
{
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_tlv(b, pos, end);
    lemma_context_class(r.tag);
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    let n = r.tag.number;
    assert(u.class == 2);
    if n == 2 || n == 7 {
        lemma_ia5(u.contents, 0);
    } else {
        lemma_tlv_alone(b, pos, end);
        let (g, next) = x::parse_general_name(b, pos, end)->Some_0;
        assert(g == x::GeneralName::Other(n, sl(b, pos, r.cend)));
    }
}

/// One GeneralName, from `extensions.rs` to `extensions/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_general_name_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, y: e::GeneralName)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        e::decode_general_name(u) == Some(y),
        general_name_in_domain(y),
    ensures
        tag_fits(u),
        x::parse_general_name(b, pos, end) is Some,
        general_name_agree(x::parse_general_name(b, pos, end)->Some_0.0, y),
        x::parse_general_name(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
{
    assert(u.class == 2 && u.number <= 8);
    lemma_tlv(b, pos, end);
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_context_class(r.tag);
    lemma_ia5(u.contents, 0);
    let n = r.tag.number;
    assert(r.tag.constructed == x::general_name_constructed(n));
    if n != 2 && n != 7 {
        lemma_parse_tlv_not_reserved(sl(b, pos, end));
        lemma_tlv_alone(b, pos, end);
    }
}

/// `decode_general_name_list` past one more element at the front.
pub proof fn lemma_general_name_list_shift(u: i::Tlv, l: Seq<i::Tlv>, k: nat)
    ensures
        e::decode_general_name_list(seq![u] + l, k + 1) == e::decode_general_name_list(l, k),
    decreases l.len() - k,
{
    let f = seq![u] + l;
    if k < l.len() {
        assert(f[(k + 1) as int] == l[k as int]);
        lemma_general_name_list_shift(u, l, k + 1);
    }
}

/// `decode_general_name_list` gives one value for each element.
pub proof fn lemma_general_name_list_len(l: Seq<i::Tlv>, k: nat)
    requires
        k <= l.len(),
        e::decode_general_name_list(l, k) is Some,
    ensures
        e::decode_general_name_list(l, k)->Some_0.len() == l.len() - k,
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_general_name_list_len(l, k + 1);
    }
}

/// From `extensions/spec.rs`, the names from `pos`.
pub proof fn lemma_general_names_fwd(b: Seq<u8>, pos: nat, end: nat, acc: Seq<x::GeneralName>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        x::parse_general_names_acc(b, pos, end, acc) is Some,
        forall|k: int|
            acc.len() <= k < x::parse_general_names_acc(b, pos, end, acc)->Some_0.0.len() ==> other_form_decodes(
                #[trigger] x::parse_general_names_acc(b, pos, end, acc)->Some_0.0[k],
            ),
    ensures
        ({
            let all = x::parse_general_names_acc(b, pos, end, acc)->Some_0.0;
            &&& x::parse_general_names_acc(b, pos, end, acc)->Some_0.1 == end
            &&& all.len() >= acc.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& {
                let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& l.len() == all.len() - acc.len()
                &&& e::decode_general_name_list(l, 0) is Some
                &&& {
                    let v = e::decode_general_name_list(l, 0)->Some_0;
                    &&& v.len() == l.len()
                    &&& forall|k: int| 0 <= k < v.len() ==> general_name_agree(#[trigger] all[k + acc.len()], v[k])
                    &&& forall|k: int| 0 <= k < v.len() ==> general_name_in_domain(#[trigger] v[k])
                }
            }
        }),
    decreases end - pos,
{
    hide(e::decode_general_name);
    hide(x::parse_general_name);
    let all = x::parse_general_names_acc(b, pos, end, acc)->Some_0.0;
    if pos == end {
        lemma_tlvs_empty(b, pos);
    } else {
        let (a, next) = x::parse_general_name(b, pos, end)->Some_0;
        let acc2 = acc.push(a);
        assert(x::parse_general_names_acc(b, next, end, acc2) == x::parse_general_names_acc(b, pos, end, acc));
        assert(forall|k: int| acc2.len() <= k < all.len() ==> other_form_decodes(#[trigger] all[k]));
        lemma_general_names_fwd(b, next, end, acc2);
        assert(all[acc.len() as int] == a);
        lemma_general_name_fwd(b, pos, end);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = i::parse_tlvs(sl(b, next, end))->Some_0;
        lemma_tlvs_cons(b, pos, end, r);
        lemma_general_name_list_shift(u, r, 0);
        let y = e::decode_general_name(u)->Some_0;
        let lr = e::decode_general_name_list(r, 0)->Some_0;
        let v = seq![y] + lr;
        let l = seq![u] + r;
        assert(l[0] == u);
        assert(e::decode_general_name_list(l, 0) == Some(v));
        assert forall|k: int| 0 <= k < v.len() implies general_name_agree(#[trigger] all[k + acc.len()], v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            }
        }
        assert forall|k: int| 0 <= k < v.len() implies general_name_in_domain(#[trigger] v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// From `extensions.rs`, the names from `pos`.
pub proof fn lemma_general_names_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    acc: Seq<x::GeneralName>,
    l: Seq<i::Tlv>,
    v: Seq<e::GeneralName>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        e::decode_general_name_list(l, 0) == Some(v),
        forall|k: int| 0 <= k < v.len() ==> general_name_in_domain(#[trigger] v[k]),
    ensures
        x::parse_general_names_acc(b, pos, end, acc) is Some,
        x::parse_general_names_acc(b, pos, end, acc)->Some_0.1 == end,
        ({
            let all = x::parse_general_names_acc(b, pos, end, acc)->Some_0.0;
            &&& all.len() == acc.len() + v.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& forall|k: int| 0 <= k < v.len() ==> general_name_agree(#[trigger] all[k + acc.len()], v[k])
        }),
    decreases end - pos,
{
    hide(e::decode_general_name);
    hide(x::parse_general_name);
    lemma_tlvs_none_left(b, pos, end, l);
    if pos < end {
        let u = l[0];
        let r = l.skip(1);
        assert(l =~= seq![u] + r);
        lemma_general_name_list_shift(u, r, 0);
        let y = e::decode_general_name(u)->Some_0;
        let lr = e::decode_general_name_list(r, 0)->Some_0;
        assert(v == seq![y] + lr);
        assert(v[0] == y);
        lemma_tlv(b, pos, end);
        assert(i::parse_tlv(sl(b, pos, end)) == Some(u));
        lemma_general_name_back(b, pos, end, u, y);
        lemma_tlvs_head(b, pos, end, l);
        let (a, next) = x::parse_general_name(b, pos, end)->Some_0;
        let t = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        assert(t.cend == next);
        assert forall|k: int| 0 <= k < lr.len() implies general_name_in_domain(#[trigger] lr[k]) by {
            assert(v[k + 1] == lr[k]);
        }
        let acc2 = acc.push(a);
        lemma_general_names_back(b, next, end, acc2, r, lr);
        let all = x::parse_general_names_acc(b, pos, end, acc)->Some_0.0;
        assert(all == x::parse_general_names_acc(b, next, end, acc2)->Some_0.0);
        assert forall|k: int| 0 <= k < v.len() implies general_name_agree(#[trigger] all[k + acc.len()], v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            } else {
                assert(all[acc.len() as int] == acc2[acc.len() as int]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    } else {
        assert(v.len() == 0);
    }
}

/// The two values of a subjectAltName agree.
pub open spec fn subject_alt_name_agree(a: x::SubjectAltName, v: Seq<e::GeneralName>) -> bool {
    &&& a.names.len() == v.len()
    &&& forall|k: int| 0 <= k < v.len() ==> general_name_agree(#[trigger] a.names[k], v[k])
}

/// The value `extensions.rs` gives a subjectAltName, if it reads one.
pub open spec fn san_value(input: Seq<u8>) -> Option<Seq<e::GeneralName>> {
    match e::decode_extension_value(e::id_ce_subject_alt_name(), input) {
        Some(e::ExtensionValue::SubjectAltName(v)) => Some(v),
        _ => None,
    }
}

/// A subjectAltName is the arm `decode_extension_value` takes for its id.
pub proof fn lemma_san_value(input: Seq<u8>)
    ensures
        san_value(input) == match i::parse_single(input) {
            None => None,
            Some(t) => match s::sequence_elements(t) {
                None => None,
                Some(l) => e::general_names_from(l),
            },
        },
{
    let id = e::id_ce_subject_alt_name();
    assert(id =~= seq![2nat, 5nat, 29nat, 17nat]);
    assert(id != e::id_ce_authority_key_identifier()) by {
        assert(e::id_ce_authority_key_identifier()[3] == 35nat);
        assert(id[3] == 17nat);
    }
    assert(id != e::id_ce_subject_key_identifier()) by {
        assert(e::id_ce_subject_key_identifier()[3] == 14nat);
        assert(id[3] == 17nat);
    }
    assert(id != e::id_ce_key_usage()) by {
        assert(e::id_ce_key_usage()[3] == 15nat);
        assert(id[3] == 17nat);
    }
    assert(id != e::id_ce_ext_key_usage()) by {
        assert(e::id_ce_ext_key_usage()[3] == 37nat);
        assert(id[3] == 17nat);
    }
    assert(id != e::id_ce_certificate_policies()) by {
        assert(e::id_ce_certificate_policies()[3] == 32nat);
        assert(id[3] == 17nat);
    }
}

/// **`theorem_subject_alt_name`, from `extensions/spec.rs`.** A value
/// `parse_subject_alt_name` reads, `extensions.rs` reads to the same names,
/// unless a form the first keeps unread is one the second refuses.
pub proof fn theorem_subject_alt_name_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        x::parse_subject_alt_name(input) is Some,
        forall|k: int|
            0 <= k < x::parse_subject_alt_name(input)->Some_0.names.len() ==> other_form_decodes(
                #[trigger] x::parse_subject_alt_name(input)->Some_0.names[k],
            ),
    ensures
        san_value(input) is Some,
        subject_alt_name_agree(x::parse_subject_alt_name(input)->Some_0, san_value(input)->Some_0),
        forall|k: int|
            0 <= k < san_value(input)->Some_0.len() ==> general_name_in_domain(
                #[trigger] san_value(input)->Some_0[k],
            ),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t.cstart, t.cend);
    let empty = Seq::<x::GeneralName>::empty();
    let a = x::parse_subject_alt_name(input)->Some_0;
    assert(x::parse_general_names_from(b, start, finish) == x::parse_general_names_acc(b, start, finish, empty));
    assert(a.names == x::parse_general_names_acc(b, start, finish, empty)->Some_0.0);
    lemma_general_names_fwd(b, start, finish, empty);
    let l = i::parse_tlvs(sl(b, start, finish))->Some_0;
    lemma_sequence_fwd(b, 0, len, l);
    lemma_single(b, 0, len);
    lemma_san_value(input);
    let v = e::decode_general_name_list(l, 0)->Some_0;
    assert(san_value(input) == Some(v));
    assert forall|k: int| 0 <= k < v.len() implies general_name_agree(#[trigger] a.names[k], v[k]) by {
        assert(a.names[k + empty.len()] == a.names[k]);
    }
}

/// **`theorem_subject_alt_name`, from `extensions.rs`.** A value `extensions.rs`
/// reads, `parse_subject_alt_name` reads to the same names, unless it holds a
/// form neither defined nor kept, an empty dNSName or an iPAddress of another
/// size.
pub proof fn theorem_subject_alt_name_back(input: Seq<u8>, v: Seq<e::GeneralName>)
    requires
        input.len() < two64(),
        san_value(input) == Some(v),
        forall|k: int| 0 <= k < v.len() ==> general_name_in_domain(#[trigger] v[k]),
    ensures
        x::parse_subject_alt_name(input) is Some,
        subject_alt_name_agree(x::parse_subject_alt_name(input)->Some_0, v),
{
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_san_value(input);
    let u = i::parse_single(input)->Some_0;
    let l = s::sequence_elements(u)->Some_0;
    assert(l.len() > 0);
    assert(tag_fits(u));
    lemma_single_back(b, 0, len, u);
    lemma_sequence_back(b, 0, len, u, l);
    let t = d::read_tlv(b, 0, len)->Some_0;
    let (start, finish) = (t.cstart, t.cend);
    let empty = Seq::<x::GeneralName>::empty();
    lemma_general_name_list_len(l, 0);
    lemma_tlvs_none_left(b, start, finish, l);
    lemma_general_names_back(b, start, finish, empty, l, v);
    let all = x::parse_general_names_acc(b, start, finish, empty)->Some_0.0;
    assert(x::parse_general_names_from(b, start, finish) == x::parse_general_names_acc(b, start, finish, empty));
    assert(x::parse_subject_alt_name(input)->Some_0.names == all);
    assert forall|k: int| 0 <= k < v.len() implies general_name_agree(#[trigger] all[k], v[k]) by {
        assert(all[k + empty.len()] == all[k]);
    }
}

} // verus!
