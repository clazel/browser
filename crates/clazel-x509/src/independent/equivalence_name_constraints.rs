//! `name_constraints/spec.rs` against `independent/extensions.rs`. The other
//! value decoders are in `equivalence_values.rs`.
//!
//! The crate reads and the transcription refuses:
//! - **An empty `NameConstraints`.** `name_constraints/spec.rs` takes both
//!   fields as OPTIONAL. X.509 9.4.2.2 says "At least one of ...
//!   shall be present", and RFC 5280 §4.2.1.10 says conforming CAs MUST NOT
//!   issue one, so **the letter is with the transcription**. The extension
//!   constrains nothing either way.
//! - **A base the crate keeps unread that the transcription refuses**
//!   ([`base_form_decodes`]): a directoryName that is not a Name, an otherName
//!   with the wrong structure, a non-IA5 URI, a registeredID that is not an
//!   OBJECT IDENTIFIER. `name_constraints::matching` parses a directoryName
//!   where it needs it and decides what the others do (see the header of
//!   `name_constraints/spec.rs`).
//!
//! The transcription reads and the crate refuses ([`subtree_in_domain`]):
//! - **`minimum` or `maximum`**: RFC 5280 §4.2.1.10 "the minimum MUST be zero,
//!   and maximum MUST be absent"; X.509 9.4.2.2 keeps them.
//! - **An addition**, in the value or in a `GeneralSubtree`.
//! - **An undefined `GeneralName`**, kept by the transcription as `Unknown`.
//! - **An iPAddress base of a size other than 8 or 32 octets**: RFC 5280
//!   §4.2.1.10. X.509 says nothing of a base's address form (`extensions.rs`,
//!   open choice).

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
use super::equivalence_values::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::name_constraints::spec as nc;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// The value `extensions.rs` gives a nameConstraints, if it reads one.
pub open spec fn name_constraints_value(input: Seq<u8>) -> Option<e::NameConstraintsSyntax> {
    match e::decode_extension_value(e::id_ce_name_constraints(), input) {
        Some(e::ExtensionValue::NameConstraints(v)) => Some(v),
        _ => None,
    }
}

/// nameConstraints is the arm `decode_extension_value` takes for its id.
pub proof fn lemma_name_constraints_value(input: Seq<u8>)
    ensures
        name_constraints_value(input) == match i::parse_single(input) {
            None => None,
            Some(t) => e::decode_name_constraints(t),
        },
{
    lemma_id_ce_differ(30, 35);
    lemma_id_ce_differ(30, 14);
    lemma_id_ce_differ(30, 15);
    lemma_id_ce_differ(30, 37);
    lemma_id_ce_differ(30, 32);
    lemma_id_ce_differ(30, 17);
    lemma_id_ce_differ(30, 19);
}

// ---------------------------------------------------------------------
// One base.
// ---------------------------------------------------------------------

/// The two values of one base agree. `name_constraints/spec.rs` keeps a
/// directoryName's contents and every other form's encoding unread.
pub open spec fn base_agree(a: nc::GeneralNameConstraint, y: e::GeneralName) -> bool {
    match a {
        nc::GeneralNameConstraint::DnsName(v) => y == e::GeneralName::DNSName(v),
        nc::GeneralNameConstraint::Rfc822Name(v) => y == e::GeneralName::Rfc822Name(v),
        nc::GeneralNameConstraint::DirectoryName(v) => {
            &&& i::parse_single(v) is Some
            &&& s::decode_name(i::parse_single(v)->Some_0) is Some
            &&& y == e::GeneralName::DirectoryName(s::decode_name(i::parse_single(v)->Some_0)->Some_0)
        },
        nc::GeneralNameConstraint::IpAddress { address, mask } => y == e::GeneralName::IPAddress(
            address + mask,
        ),
        nc::GeneralNameConstraint::Unsupported { tag: _, der } => {
            &&& i::parse_single(der) is Some
            &&& e::decode_general_name(i::parse_single(der)->Some_0) == Some(y)
            &&& !(y is DNSName || y is Rfc822Name || y is DirectoryName || y is IPAddress)
        },
    }
}

/// A base `name_constraints/spec.rs` reads: a defined form, and an iPAddress
/// of an address and a mask of one size.
pub open spec fn base_in_domain(y: e::GeneralName) -> bool {
    match y {
        e::GeneralName::Unknown(_) => false,
        e::GeneralName::IPAddress(v) => v.len() == 8 || v.len() == 32,
        _ => true,
    }
}

/// A form `name_constraints/spec.rs` keeps unread is one `extensions.rs` reads.
pub open spec fn base_form_decodes(a: nc::GeneralNameConstraint) -> bool {
    match a {
        nc::GeneralNameConstraint::DirectoryName(v) => {
            &&& i::parse_single(v) is Some
            &&& s::decode_name(i::parse_single(v)->Some_0) is Some
        },
        nc::GeneralNameConstraint::Unsupported { tag: _, der } => {
            &&& i::parse_single(der) is Some
            &&& e::decode_general_name(i::parse_single(der)->Some_0) is Some
        },
        _ => true,
    }
}

/// One base, from `name_constraints/spec.rs` to `extensions.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_base_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        nc::parse_base(b, pos, end) is Some,
        base_form_decodes(nc::parse_base(b, pos, end)->Some_0.0),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == nc::parse_base(b, pos, end)->Some_0.1,
        pos < nc::parse_base(b, pos, end)->Some_0.1 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        e::decode_general_name(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        base_agree(
            nc::parse_base(b, pos, end)->Some_0.0,
            e::decode_general_name(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        base_in_domain(e::decode_general_name(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
{
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_tlv(b, pos, end);
    lemma_context_class(r.tag);
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    let n = r.tag.number;
    let value = sl(b, r.cstart, r.cend);
    assert(u.class == 2);
    assert(u.contents == value);
    if n == 2 || n == 1 {
        lemma_ia5(u.contents, 0);
    } else if n == 7 {
        if value.len() == 8 {
            assert(value.subrange(0, 4) + value.subrange(4, 8) =~= value);
        } else {
            assert(value.subrange(0, 16) + value.subrange(16, 32) =~= value);
        }
    } else if n != 4 {
        lemma_tlv_alone(b, pos, end);
        let (g, next) = nc::parse_base(b, pos, end)->Some_0;
        assert(g == nc::GeneralNameConstraint::Unsupported { tag: n, der: sl(b, pos, r.cend) });
    }
}

/// One base, from `extensions.rs` to `name_constraints/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_base_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, y: e::GeneralName)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        e::decode_general_name(u) == Some(y),
        base_in_domain(y),
    ensures
        tag_fits(u),
        nc::parse_base(b, pos, end) is Some,
        base_agree(nc::parse_base(b, pos, end)->Some_0.0, y),
        nc::parse_base(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
{
    assert(u.class == 2 && u.number <= 8);
    lemma_tlv(b, pos, end);
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_context_class(r.tag);
    lemma_ia5(u.contents, 0);
    let n = r.tag.number;
    let value = sl(b, r.cstart, r.cend);
    assert(u.contents == value);
    assert(r.tag.constructed == x::general_name_constructed(n));
    if n == 7 {
        if value.len() == 8 {
            assert(value.subrange(0, 4) + value.subrange(4, 8) =~= value);
        } else {
            assert(value.subrange(0, 16) + value.subrange(16, 32) =~= value);
        }
    } else if n != 1 && n != 2 && n != 4 {
        lemma_parse_tlv_not_reserved(sl(b, pos, end));
        lemma_tlv_alone(b, pos, end);
    }
}

// ---------------------------------------------------------------------
// One GeneralSubtree.
// ---------------------------------------------------------------------

/// A GeneralSubtree `name_constraints/spec.rs` reads: `minimum` zero,
/// `maximum` absent, no addition.
pub open spec fn subtree_in_domain(y: e::GeneralSubtree) -> bool {
    &&& y.minimum == 0
    &&& y.maximum is None
    &&& y.additions.len() == 0
    &&& base_in_domain(y.base)
}

/// One GeneralSubtree, from `name_constraints/spec.rs` to `extensions.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_subtree_fwd(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        nc::parse_general_subtree(b, pos, end) is Some,
        base_form_decodes(nc::parse_general_subtree(b, pos, end)->Some_0.0.base),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == nc::parse_general_subtree(b, pos, end)->Some_0.1,
        pos < nc::parse_general_subtree(b, pos, end)->Some_0.1 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        e::decode_general_subtree(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        base_agree(
            nc::parse_general_subtree(b, pos, end)->Some_0.0.base,
            e::decode_general_subtree(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0.base,
        ),
        subtree_in_domain(e::decode_general_subtree(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
{
    hide(nc::parse_base);
    hide(e::decode_general_name);
    hide(base_agree);
    hide(base_in_domain);
    hide(base_form_decodes);
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_tlv(b, pos, end);
    let (start, finish) = (r.cstart, r.cend);
    lemma_base_fwd(b, start, finish);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    lemma_tlvs_cons(b, start, finish, none);
    let u1 = i::parse_tlv(sl(b, start, finish))->Some_0;
    let l = seq![u1] + none;
    lemma_sequence_fwd(b, pos, end, l);
    assert(l[0] == u1);
    assert(l.len() == 1);
}

/// One GeneralSubtree, from `extensions.rs` to `name_constraints/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_subtree_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv, y: e::GeneralSubtree)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        e::decode_general_subtree(u) == Some(y),
        subtree_in_domain(y),
    ensures
        nc::parse_general_subtree(b, pos, end) is Some,
        base_agree(nc::parse_general_subtree(b, pos, end)->Some_0.0.base, y.base),
        nc::parse_general_subtree(b, pos, end)->Some_0.1 == pos + u.encoding.len(),
{
    hide(nc::parse_base);
    hide(e::decode_general_name);
    hide(base_agree);
    hide(base_in_domain);
    let l = s::sequence_elements(u)->Some_0;
    lemma_sequence_back(b, pos, end, u, l);
    let r = d::read_tlv(b, pos, end)->Some_0;
    let (start, finish) = (r.cstart, r.cend);
    assert(l.len() == 1) by {
        assert(!i::tag_at(l, 1, 2, 0));
        assert(!i::tag_at(l, 1, 2, 1));
        if l.len() > 1 {
            assert(i::from_index(l, 1).len() == l.len() - 1);
        }
    }
    assert(e::decode_general_name(l[0]) == Some(y.base));
    assert(tag_fits(l[0])) by {
        reveal(e::decode_general_name);
        reveal(base_in_domain);
    }
    lemma_tlvs_head(b, start, finish, l);
    lemma_base_back(b, start, finish, l[0], y.base);
    let first = d::read_tlv(b, start, finish)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, start, finish);
    lemma_tlvs_none_left(b, first.cend, finish, l.skip(1));
}

/// A GeneralSubtree is a SEQUENCE.
pub proof fn lemma_subtree_tag(u: i::Tlv)
    requires
        e::decode_general_subtree(u) is Some,
    ensures
        tag_fits(u),
{
}

// ---------------------------------------------------------------------
// GeneralSubtrees.
// ---------------------------------------------------------------------

/// `decode_general_subtree_list` past one more element at the front.
pub proof fn lemma_subtree_list_shift(u: i::Tlv, l: Seq<i::Tlv>, k: nat)
    ensures
        e::decode_general_subtree_list(seq![u] + l, k + 1) == e::decode_general_subtree_list(l, k),
    decreases l.len() - k,
{
    let f = seq![u] + l;
    if k < l.len() {
        assert(f[(k + 1) as int] == l[k as int]);
        lemma_subtree_list_shift(u, l, k + 1);
    }
}

/// `decode_general_subtree_list` gives one value for each element.
pub proof fn lemma_subtree_list_len(l: Seq<i::Tlv>, k: nat)
    requires
        k <= l.len(),
        e::decode_general_subtree_list(l, k) is Some,
    ensures
        e::decode_general_subtree_list(l, k)->Some_0.len() == l.len() - k,
    decreases l.len() - k,
{
    if k < l.len() {
        lemma_subtree_list_len(l, k + 1);
    }
}

/// From `name_constraints/spec.rs`, the subtrees from `pos`.
pub proof fn lemma_subtrees_fwd(b: Seq<u8>, pos: nat, end: nat, acc: Seq<nc::GeneralSubtree>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        nc::parse_subtrees_acc(b, pos, end, acc) is Some,
        forall|k: int|
            acc.len() <= k < nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0.len() ==> base_form_decodes(
                (#[trigger] nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0[k]).base,
            ),
    ensures
        ({
            let all = nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0;
            &&& nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.1 == end
            &&& all.len() >= acc.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& i::parse_tlvs(sl(b, pos, end)) is Some
            &&& {
                let l = i::parse_tlvs(sl(b, pos, end))->Some_0;
                &&& l.len() == all.len() - acc.len()
                &&& e::decode_general_subtree_list(l, 0) is Some
                &&& {
                    let v = e::decode_general_subtree_list(l, 0)->Some_0;
                    &&& v.len() == l.len()
                    &&& forall|k: int| 0 <= k < v.len() ==> base_agree((#[trigger] all[k + acc.len()]).base, v[k].base)
                    &&& forall|k: int| 0 <= k < v.len() ==> subtree_in_domain(#[trigger] v[k])
                }
            }
        }),
    decreases end - pos,
{
    hide(e::decode_general_subtree);
    hide(nc::parse_general_subtree);
    hide(base_agree);
    hide(base_form_decodes);
    hide(subtree_in_domain);
    let all = nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0;
    if pos == end {
        lemma_tlvs_empty(b, pos);
    } else {
        let (a, next) = nc::parse_general_subtree(b, pos, end)->Some_0;
        let acc2 = acc.push(a);
        assert(nc::parse_subtrees_acc(b, next, end, acc2) == nc::parse_subtrees_acc(b, pos, end, acc));
        assert(forall|k: int| acc2.len() <= k < all.len() ==> base_form_decodes((#[trigger] all[k]).base));
        lemma_subtrees_fwd(b, next, end, acc2);
        assert(all[acc.len() as int] == acc2[acc.len() as int]);
        assert(all[acc.len() as int] == a);
        lemma_subtree_fwd(b, pos, end);
        let u = i::parse_tlv(sl(b, pos, end))->Some_0;
        let r = i::parse_tlvs(sl(b, next, end))->Some_0;
        lemma_tlvs_cons(b, pos, end, r);
        lemma_subtree_list_shift(u, r, 0);
        let y = e::decode_general_subtree(u)->Some_0;
        let lr = e::decode_general_subtree_list(r, 0)->Some_0;
        let v = seq![y] + lr;
        let l = seq![u] + r;
        assert(l[0] == u);
        assert(e::decode_general_subtree_list(l, 0) == Some(v));
        assert forall|k: int| 0 <= k < v.len() implies base_agree((#[trigger] all[k + acc.len()]).base, v[k].base) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
                assert(all[(k - 1) + acc2.len()] == all[k + acc.len()]);
            }
        }
        assert forall|k: int| 0 <= k < v.len() implies subtree_in_domain(#[trigger] v[k]) by {
            if k > 0 {
                assert(v[k] == lr[k - 1]);
            }
        }
        assert forall|k: int| 0 <= k < acc.len() implies #[trigger] all[k] == acc[k] by {
            assert(acc2[k] == acc[k]);
        }
    }
}

/// From `extensions.rs`, the subtrees from `pos`.
pub proof fn lemma_subtrees_back(
    b: Seq<u8>,
    pos: nat,
    end: nat,
    acc: Seq<nc::GeneralSubtree>,
    l: Seq<i::Tlv>,
    v: Seq<e::GeneralSubtree>,
)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        acc.len() + v.len() > 0,
        i::parse_tlvs(sl(b, pos, end)) == Some(l),
        e::decode_general_subtree_list(l, 0) == Some(v),
        forall|k: int| 0 <= k < v.len() ==> subtree_in_domain(#[trigger] v[k]),
    ensures
        nc::parse_subtrees_acc(b, pos, end, acc) is Some,
        nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.1 == end,
        ({
            let all = nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0;
            &&& all.len() == acc.len() + v.len()
            &&& forall|k: int| 0 <= k < acc.len() ==> #[trigger] all[k] == acc[k]
            &&& forall|k: int| 0 <= k < v.len() ==> base_agree((#[trigger] all[k + acc.len()]).base, v[k].base)
        }),
    decreases end - pos,
{
    hide(e::decode_general_subtree);
    hide(nc::parse_general_subtree);
    hide(base_agree);
    hide(subtree_in_domain);
    lemma_tlvs_none_left(b, pos, end, l);
    lemma_subtree_list_len(l, 0);
    if pos < end {
        let u = l[0];
        let r = l.skip(1);
        assert(l =~= seq![u] + r);
        lemma_subtree_list_shift(u, r, 0);
        let y = e::decode_general_subtree(u)->Some_0;
        let lr = e::decode_general_subtree_list(r, 0)->Some_0;
        assert(v == seq![y] + lr);
        assert(v[0] == y);
        lemma_subtree_tag(u);
        lemma_tlvs_head(b, pos, end, l);
        lemma_subtree_back(b, pos, end, u, y);
        let (a, next) = nc::parse_general_subtree(b, pos, end)->Some_0;
        let t = d::read_tlv(b, pos, end)->Some_0;
        clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
        assert(t.cend == next);
        assert forall|k: int| 0 <= k < lr.len() implies subtree_in_domain(#[trigger] lr[k]) by {
            assert(v[k + 1] == lr[k]);
        }
        let acc2 = acc.push(a);
        lemma_subtrees_back(b, next, end, acc2, r, lr);
        let all = nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0;
        assert(all == nc::parse_subtrees_acc(b, next, end, acc2)->Some_0.0);
        assert forall|k: int| 0 <= k < v.len() implies base_agree((#[trigger] all[k + acc.len()]).base, v[k].base) by {
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

/// The two lists of subtrees agree.
pub open spec fn subtrees_agree(a: Seq<nc::GeneralSubtree>, v: Seq<e::GeneralSubtree>) -> bool {
    &&& a.len() == v.len()
    &&& forall|k: int| 0 <= k < a.len() ==> base_agree((#[trigger] a[k]).base, v[k].base)
}

/// Every base of the list is one `extensions.rs` reads.
pub open spec fn subtrees_forms_decode(a: Seq<nc::GeneralSubtree>) -> bool {
    forall|k: int| 0 <= k < a.len() ==> base_form_decodes((#[trigger] a[k]).base)
}

/// Every subtree of the list is one `name_constraints/spec.rs` reads.
pub open spec fn subtrees_in_domain(v: Seq<e::GeneralSubtree>) -> bool {
    forall|k: int| 0 <= k < v.len() ==> subtree_in_domain(#[trigger] v[k])
}

/// `parse_subtrees_acc` does not return an empty list.
pub proof fn lemma_subtrees_nonempty(b: Seq<u8>, pos: nat, end: nat, acc: Seq<nc::GeneralSubtree>)
    requires
        pos <= end,
        nc::parse_subtrees_acc(b, pos, end, acc) is Some,
    ensures
        nc::parse_subtrees_acc(b, pos, end, acc)->Some_0.0.len() > 0,
    decreases end - pos,
{
    if pos != end {
        let (a, next) = nc::parse_general_subtree(b, pos, end)->Some_0;
        lemma_subtrees_nonempty(b, next, end, acc.push(a));
    }
}

/// A `[n] GeneralSubtrees` field, from `name_constraints/spec.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_subtrees_field_fwd(b: Seq<u8>, pos: nat, end: nat, number: u32)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        nc::parse_subtrees_field(b, pos, end, number) is Some,
        subtrees_forms_decode(nc::parse_subtrees_field(b, pos, end, number)->Some_0.0),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        d::read_tlv(b, pos, end)->Some_0.cend == nc::parse_subtrees_field(b, pos, end, number)->Some_0.1,
        pos < nc::parse_subtrees_field(b, pos, end, number)->Some_0.1 <= end,
        i::parse_tlv(sl(b, pos, end)) is Some,
        i::parse_tlv(sl(b, pos, end))->Some_0.class == i::class_context(),
        i::parse_tlv(sl(b, pos, end))->Some_0.number == number,
        e::decode_general_subtrees(i::parse_tlv(sl(b, pos, end))->Some_0) is Some,
        subtrees_agree(
            nc::parse_subtrees_field(b, pos, end, number)->Some_0.0,
            e::decode_general_subtrees(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0,
        ),
        subtrees_in_domain(e::decode_general_subtrees(i::parse_tlv(sl(b, pos, end))->Some_0)->Some_0),
{
    hide(nc::parse_subtrees_acc);
    hide(e::decode_general_subtree_list);
    hide(base_agree);
    hide(subtree_in_domain);
    hide(base_form_decodes);
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_tlv(b, pos, end);
    lemma_context_class(r.tag);
    let none = Seq::<nc::GeneralSubtree>::empty();
    let (all, next) = nc::parse_subtrees_acc(b, r.cstart, r.cend, none)->Some_0;
    assert(all == nc::parse_subtrees_field(b, pos, end, number)->Some_0.0);
    lemma_subtrees_nonempty(b, r.cstart, r.cend, none);
    assert forall|k: int| none.len() <= k < all.len() implies base_form_decodes(
        (#[trigger] nc::parse_subtrees_acc(b, r.cstart, r.cend, none)->Some_0.0[k]).base,
    ) by {
        assert(base_form_decodes(all[k].base));
    }
    lemma_subtrees_fwd(b, r.cstart, r.cend, none);
    let u = i::parse_tlv(sl(b, pos, end))->Some_0;
    let l = i::parse_tlvs(sl(b, r.cstart, r.cend))->Some_0;
    let v = e::decode_general_subtree_list(l, 0)->Some_0;
    assert(u.contents == sl(b, r.cstart, r.cend));
    assert(l.len() > 0);
    assert forall|k: int| 0 <= k < all.len() implies base_agree((#[trigger] all[k]).base, v[k].base) by {
        assert(all[k + none.len()] == all[k]);
    }
}

/// A `[n] GeneralSubtrees` field, from `extensions.rs`.
#[verifier::spinoff_prover]
pub proof fn lemma_subtrees_field_back(b: Seq<u8>, pos: nat, end: nat, number: u32, u: i::Tlv, v: Seq<e::GeneralSubtree>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlv(sl(b, pos, end)) == Some(u),
        u.class == i::class_context(),
        u.number == number,
        tag_fits(u),
        e::decode_general_subtrees(u) == Some(v),
        subtrees_in_domain(v),
    ensures
        nc::parse_subtrees_field(b, pos, end, number) is Some,
        subtrees_agree(nc::parse_subtrees_field(b, pos, end, number)->Some_0.0, v),
        nc::parse_subtrees_field(b, pos, end, number)->Some_0.1 == pos + u.encoding.len(),
        nc::parse_subtrees_field(b, pos, end, number)->Some_0.1 == d::read_tlv(b, pos, end)->Some_0.cend,
        pos < nc::parse_subtrees_field(b, pos, end, number)->Some_0.1 <= end,
{
    hide(nc::parse_subtrees_acc);
    hide(e::decode_general_subtree_list);
    hide(base_agree);
    hide(subtree_in_domain);
    lemma_tlv(b, pos, end);
    lemma_parse_tlv_not_reserved(sl(b, pos, end));
    let r = d::read_tlv(b, pos, end)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    lemma_context_class(r.tag);
    let l = i::parse_tlvs(u.contents)->Some_0;
    assert(u.contents == sl(b, r.cstart, r.cend));
    assert(l.len() > 0);
    lemma_subtree_list_len(l, 0);
    let none = Seq::<nc::GeneralSubtree>::empty();
    lemma_subtrees_back(b, r.cstart, r.cend, none, l, v);
    let all = nc::parse_subtrees_acc(b, r.cstart, r.cend, none)->Some_0.0;
    assert forall|k: int| 0 <= k < all.len() implies base_agree((#[trigger] all[k]).base, v[k].base) by {
        assert(all[k + none.len()] == all[k]);
    }
}

// ---------------------------------------------------------------------
// NameConstraints.
// ---------------------------------------------------------------------

/// The two values of an optional GeneralSubtrees agree.
pub open spec fn optional_subtrees_agree(a: Option<Seq<nc::GeneralSubtree>>, v: Option<Seq<e::GeneralSubtree>>) -> bool {
    match (a, v) {
        (None, None) => true,
        (Some(p), Some(q)) => subtrees_agree(p, q),
        _ => false,
    }
}

/// The two values of a nameConstraints agree.
pub open spec fn name_constraints_agree(a: nc::NameConstraints, v: e::NameConstraintsSyntax) -> bool {
    &&& optional_subtrees_agree(a.permitted_subtrees, v.permitted_subtrees)
    &&& optional_subtrees_agree(a.excluded_subtrees, v.excluded_subtrees)
}

/// Every subtree of an optional list is one `name_constraints/spec.rs` reads.
pub open spec fn optional_subtrees_in_domain(v: Option<Seq<e::GeneralSubtree>>) -> bool {
    match v {
        None => true,
        Some(q) => subtrees_in_domain(q),
    }
}

/// A nameConstraints `name_constraints/spec.rs` reads.
pub open spec fn name_constraints_in_domain(v: e::NameConstraintsSyntax) -> bool {
    &&& v.additions.len() == 0
    &&& optional_subtrees_in_domain(v.permitted_subtrees)
    &&& optional_subtrees_in_domain(v.excluded_subtrees)
}

/// Every base of an optional list is one `extensions.rs` reads.
pub open spec fn optional_forms_decode(a: Option<Seq<nc::GeneralSubtree>>) -> bool {
    match a {
        None => true,
        Some(p) => subtrees_forms_decode(p),
    }
}

/// What `name_constraints/spec.rs` reads, `extensions.rs` reads: not the empty
/// sequence, and each base one the second reads.
pub open spec fn name_constraints_decodes(a: nc::NameConstraints) -> bool {
    &&& a.permitted_subtrees is Some || a.excluded_subtrees is Some
    &&& optional_forms_decode(a.permitted_subtrees)
    &&& optional_forms_decode(a.excluded_subtrees)
}

/// **`theorem_name_constraints`, from `name_constraints/spec.rs`.** A value
/// `parse_name_constraints` reads, `extensions.rs` reads to the same value,
/// unless it is the empty sequence or a base it keeps unread is one
/// `extensions.rs` refuses.
#[verifier::spinoff_prover]
pub proof fn theorem_name_constraints_fwd(input: Seq<u8>)
    requires
        input.len() < two64(),
        nc::parse_name_constraints(input) is Some,
        name_constraints_decodes(nc::parse_name_constraints(input)->Some_0),
    ensures
        name_constraints_value(input) is Some,
        name_constraints_agree(nc::parse_name_constraints(input)->Some_0, name_constraints_value(input)->Some_0),
        name_constraints_in_domain(name_constraints_value(input)->Some_0),
{
    hide(name_constraints_value);
    hide(nc::parse_subtrees_field);
    hide(e::decode_general_subtrees);
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(subtrees_agree);
    hide(subtrees_in_domain);
    hide(subtrees_forms_decode);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_name_constraints_value(input);
    let t = d::read_tlv(b, 0, len)->Some_0;
    clazel_der::lemmas::lemma_read_tlv_bounds(b, 0, len);
    let (start, finish) = (t.cstart, t.cend);
    let none = Seq::<i::Tlv>::empty();
    lemma_tlvs_empty(b, finish);
    let field = d::read_tlv(b, start, finish)->Some_0;
    if field.tag == d::context_specific(0, true) {
        lemma_subtrees_field_fwd(b, start, finish, 0);
        let (permitted, next) = nc::parse_subtrees_field(b, start, finish, 0)->Some_0;
        let u0 = i::parse_tlv(sl(b, start, finish))->Some_0;
        if next == finish {
            lemma_tlvs_cons(b, start, finish, none);
            let l = seq![u0] + none;
            lemma_sequence_fwd(b, 0, len, l);
            lemma_single(b, 0, len);
            assert(l[0] == u0);
            assert(l.len() == 1);
        } else {
            lemma_subtrees_field_fwd(b, next, finish, 1);
            let u1 = i::parse_tlv(sl(b, next, finish))->Some_0;
            lemma_tlvs_cons(b, next, finish, none);
            lemma_tlvs_cons(b, start, finish, seq![u1] + none);
            let l = seq![u0] + (seq![u1] + none);
            lemma_sequence_fwd(b, 0, len, l);
            lemma_single(b, 0, len);
            assert(l[0] == u0);
            assert(l[1] == u1);
            assert(l.len() == 2);
        }
    } else {
        lemma_subtrees_field_fwd(b, start, finish, 1);
        let u1 = i::parse_tlv(sl(b, start, finish))->Some_0;
        lemma_tlvs_cons(b, start, finish, none);
        let l = seq![u1] + none;
        lemma_sequence_fwd(b, 0, len, l);
        lemma_single(b, 0, len);
        assert(l[0] == u1);
        assert(l.len() == 1);
    }
}

/// **`theorem_name_constraints`, from `extensions.rs`.** A value `extensions.rs`
/// reads, `parse_name_constraints` reads to the same value, unless it has an
/// addition, a `minimum`, a `maximum`, an undefined form or an iPAddress of
/// another size.
#[verifier::spinoff_prover]
pub proof fn theorem_name_constraints_back(input: Seq<u8>, v: e::NameConstraintsSyntax)
    requires
        input.len() < two64(),
        name_constraints_value(input) == Some(v),
        name_constraints_in_domain(v),
    ensures
        nc::parse_name_constraints(input) is Some,
        name_constraints_agree(nc::parse_name_constraints(input)->Some_0, v),
{
    hide(name_constraints_value);
    hide(nc::parse_subtrees_field);
    hide(e::decode_general_subtrees);
    hide(i::parse_tlv);
    hide(i::parse_tlvs);
    hide(d::read_tlv);
    hide(subtrees_agree);
    hide(subtrees_in_domain);
    let b = input;
    let len = b.len();
    assert(sl(b, 0, len) =~= b);
    lemma_name_constraints_value(input);
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
    lemma_tlvs_head(b, start, finish, l);
    let field = d::read_tlv(b, start, finish)->Some_0;
    lemma_context_class(field.tag);
    assert(start != finish) by {
        lemma_tlvs_none_left(b, start, finish, l);
    }
    assert(l[0].constructed) by {
        reveal(e::decode_general_subtrees);
    }
    if i0 == 1 {
        lemma_subtrees_field_back(b, start, finish, 0, l[0], v.permitted_subtrees->Some_0);
        let (p, next) = nc::parse_subtrees_field(b, start, finish, 0)->Some_0;
        let rest = l.skip(1);
        lemma_tlvs_none_left(b, next, finish, rest);
        if j0 == 2 {
            assert(rest[0] == l[1]);
            assert(tag_fits(l[1]));
            lemma_tlvs_head(b, next, finish, rest);
            lemma_subtrees_field_back(b, next, finish, 1, l[1], v.excluded_subtrees->Some_0);
            let (q, last) = nc::parse_subtrees_field(b, next, finish, 1)->Some_0;
            lemma_tlvs_none_left(b, last, finish, rest.skip(1));
        }
    } else {
        lemma_subtrees_field_back(b, start, finish, 1, l[0], v.excluded_subtrees->Some_0);
        let (q, last) = nc::parse_subtrees_field(b, start, finish, 1)->Some_0;
        lemma_tlvs_none_left(b, last, finish, l.skip(1));
    }
}

} // verus!
