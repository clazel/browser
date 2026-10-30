//! Facts about the name-constraint matching spec: the set laws behind its
//! representation of permitted_subtrees and excluded_subtrees, monotonicity,
//! the meaning of a subtree for each name form, and the building blocks of
//! the path theorem `thm_names_constrained` (design §3.5, piece P8).
//!
//! They are evidence that `spec.rs` says what RFC 5280 §4.2.1.10, §6.1.3 (b)
//! and (c) and §6.1.4 (g) say, not part of what an implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §6.1.4 (g): intersection and union
// ---------------------------------------------------------------------------

/// §6.1.4 (g)(1): the permitted subtrees of a concatenated state are the
/// intersection of each part's. With `s1` the state so far and `s2` one
/// certificate's set, this is "set the permitted_subtrees state variable to
/// the intersection of its previous value and the value indicated in the
/// extension field".
pub proof fn lemma_permitted_is_intersection(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    ensures
        within_permitted_subtrees(s1 + s2, name)
            == (within_permitted_subtrees(s1, name) && within_permitted_subtrees(s2, name)),
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        assert((s1 + s2).last() == s2.last());
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        lemma_permitted_is_intersection(s1, s2.drop_last(), name);
    }
}

/// §6.1.4 (g)(2): the excluded subtrees of a concatenated state are the
/// union of each part's.
pub proof fn lemma_excluded_is_union(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    ensures
        within_excluded_subtrees(s1 + s2, name)
            == (within_excluded_subtrees(s1, name) || within_excluded_subtrees(s2, name)),
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        assert((s1 + s2).last() == s2.last());
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        lemma_excluded_is_union(s1, s2.drop_last(), name);
    }
}

/// A name satisfies a concatenated state iff it satisfies each part.
pub proof fn lemma_acceptable_is_conjunction(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    ensures name_acceptable(s1 + s2, name) == (name_acceptable(s1, name) && name_acceptable(s2, name)),
{
    lemma_permitted_is_intersection(s1, s2, name);
    lemma_excluded_is_union(s1, s2, name);
}

/// The order in which constraint sets were met does not matter
/// (commutativity of the path fold).
pub proof fn lemma_state_order_independent(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    ensures name_acceptable(s1 + s2, name) == name_acceptable(s2 + s1, name),
{
    lemma_acceptable_is_conjunction(s1, s2, name);
    lemma_acceptable_is_conjunction(s2, s1, name);
}

/// How constraint sets are grouped does not matter (associativity of the
/// path fold): the state after three certificates' sets is the same however
/// it is split.
pub proof fn lemma_state_grouping_independent(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    s3: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    ensures
        name_acceptable((s1 + s2) + s3, name) == name_acceptable(s1 + (s2 + s3), name),
        name_acceptable((s1 + s2) + s3, name)
            == (name_acceptable(s1, name) && name_acceptable(s2, name) && name_acceptable(s3, name)),
{
    assert((s1 + s2) + s3 =~= s1 + (s2 + s3));
    lemma_acceptable_is_conjunction(s1 + s2, s3, name);
    lemma_acceptable_is_conjunction(s1, s2, name);
}

/// §6.1.4 (g)(1): two sets whose permitted dNSName subtrees are disjoint
/// permit no DNS name, as the RFC's "the intersection of example.com and
/// example.net is the empty set" requires. (An empty permitted set does not
/// mean "unconstrained".)
pub proof fn lemma_disjoint_permitted_permits_nothing(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    a: crate::name_constraints::spec::NameConstraints,
    b: crate::name_constraints::spec::NameConstraints,
    name: ConstrainedName,
)
    requires !permitted_by(a, name) || !permitted_by(b, name),
    ensures !within_permitted_subtrees(state.push(a).push(b), name),
{
    let s1 = state.push(a);
    let s2 = s1.push(b);
    assert(s2.drop_last() =~= s1);
    assert(s1.drop_last() =~= state);
    assert(within_permitted_subtrees(s2, name)
        == (permitted_by(b, name) && within_permitted_subtrees(s1, name)));
    assert(within_permitted_subtrees(s1, name)
        == (permitted_by(a, name) && within_permitted_subtrees(state, name)));
}

// ---------------------------------------------------------------------------
// Monotonicity
// ---------------------------------------------------------------------------

/// Adding one more constraint set to the state never makes a name
/// acceptable that was not.
pub proof fn lemma_push_never_widens(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
    name: ConstrainedName,
)
    ensures name_acceptable(state.push(value), name) ==> name_acceptable(state, name),
{
    assert(state.push(value).drop_last() =~= state);
}

/// `value` with one more excluded subtree.
pub open spec fn with_excluded_subtree(
    value: crate::name_constraints::spec::NameConstraints,
    subtree: crate::name_constraints::spec::GeneralSubtree,
) -> crate::name_constraints::spec::NameConstraints {
    crate::name_constraints::spec::NameConstraints {
        permitted_subtrees: value.permitted_subtrees,
        excluded_subtrees: Some(match value.excluded_subtrees {
            Some(items) => items.push(subtree),
            None => seq![subtree],
        }),
    }
}

/// Adding an excluded subtree to any certificate's constraints never makes
/// more names acceptable.
pub proof fn lemma_adding_excluded_subtree_never_widens(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
    subtree: crate::name_constraints::spec::GeneralSubtree,
    name: ConstrainedName,
)
    ensures
        excluded_by(value, name) ==> excluded_by(with_excluded_subtree(value, subtree), name),
        name_acceptable(state.push(with_excluded_subtree(value, subtree)), name)
            ==> name_acceptable(state.push(value), name),
{
    match value.excluded_subtrees {
        Some(items) => {
            assert(items.push(subtree).drop_last() =~= items);
        },
        None => {
            assert(seq![subtree].drop_last() =~= Seq::<crate::name_constraints::spec::GeneralSubtree>::empty());
        },
    }
    assert(state.push(value).drop_last() =~= state);
    assert(state.push(with_excluded_subtree(value, subtree)).drop_last() =~= state);
}

// ---------------------------------------------------------------------------
// A type with no permitted subtrees
// ---------------------------------------------------------------------------

/// `value` has a permitted subtree of `name`'s type.
pub open spec fn restricts_type(
    value: crate::name_constraints::spec::NameConstraints,
    name: ConstrainedName,
) -> bool {
    match value.permitted_subtrees {
        Some(items) => has_base_of_type(items, name),
        None => false,
    }
}

/// §6.1.4 (g)(1) "If permittedSubtrees does not include a particular name
/// type, the permitted_subtrees state variable is unchanged for that name
/// type": when no set has a permitted subtree of `name`'s type, `name` is
/// within permitted_subtrees, and only the excluded subtrees decide.
pub proof fn lemma_unrestricted_type_only_excluded_applies(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    requires forall|k: int| 0 <= k < state.len() ==> !restricts_type(#[trigger] state[k], name),
    ensures
        within_permitted_subtrees(state, name),
        name_acceptable(state, name) == !within_excluded_subtrees(state, name),
    decreases state.len()
{
    if state.len() > 0 {
        assert(state.last() == state[state.len() - 1]);
        assert forall|k: int| 0 <= k < state.drop_last().len() implies
            !restricts_type(#[trigger] state.drop_last()[k], name) by {
            assert(state.drop_last()[k] == state[k]);
        }
        lemma_unrestricted_type_only_excluded_applies(state.drop_last(), name);
    }
}

// ---------------------------------------------------------------------------
// One certificate: §6.1.3 (b), (c), malformed entries and the other forms
// ---------------------------------------------------------------------------

/// `names_well_formed` is the universal statement it abbreviates.
pub proof fn lemma_matched_forms_all(names: Seq<crate::extensions::spec::GeneralName>)
    ensures
        names_well_formed(names)
            == forall|i: int| 0 <= i < names.len() ==> #[trigger] entry_well_formed(names[i]),
    decreases names.len()
{
    if names.len() > 0 {
        lemma_matched_forms_all(names.drop_last());
        if names_well_formed(names) {
            assert forall|i: int| 0 <= i < names.len() implies #[trigger] entry_well_formed(names[i]) by {
                if i < names.len() - 1 {
                    assert(names.drop_last()[i] == names[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < names.len() ==> #[trigger] entry_well_formed(names[i]) {
            assert(entry_well_formed(names[names.len() - 1]));
            assert forall|i: int| 0 <= i < names.drop_last().len() implies
                #[trigger] entry_well_formed(names.drop_last()[i]) by {
                assert(names.drop_last()[i] == names[i]);
                assert(entry_well_formed(names[i]));
            }
        }
    }
}

/// (R) malformed entries: under any constraint, a malformed entry (a
/// dNSName that is no name, an rfc822Name that is no mailbox, a
/// directoryName that is no Name) fails the certificate.
pub proof fn lemma_unmatched_name_refused(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    i: int,
)
    requires state.len() > 0, 0 <= i < names.len(), !entry_well_formed(names[i]),
    ensures !certificate_names_acceptable(state, names),
{
    lemma_matched_forms_all(names);
}

/// A malformed base or an excluded directoryName: such a NameConstraints
/// value refuses the path at §6.1.4 (g), whatever the state.
pub proof fn lemma_unsupported_constraints_refused(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
)
    requires !constraints_supported(value),
    ensures prepare_name_constraints(state, Some(value)) is None,
{
}

/// The initial state accepts every list of names, whatever their forms.
pub proof fn lemma_initial_state_accepts_everything(names: Seq<crate::extensions::spec::GeneralName>)
    ensures certificate_names_acceptable(initial_state(), names),
    decreases names.len()
{
    if names.len() > 0 {
        lemma_initial_state_accepts_everything(names.drop_last());
    }
}

/// §6.1.3 (b) for a concatenated state is (b) for each part.
pub proof fn lemma_names_within_permitted_concat(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        names_within_permitted(s1 + s2, names)
            == (names_within_permitted(s1, names) && names_within_permitted(s2, names)),
    decreases names.len()
{
    if names.len() > 0 {
        if let Some(name) = constrained_name(names.last()) {
            lemma_permitted_is_intersection(s1, s2, name);
        }
        lemma_names_within_permitted_concat(s1, s2, names.drop_last());
    }
}

/// §6.1.3 (c) for a concatenated state is (c) for each part.
pub proof fn lemma_names_not_excluded_concat(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        names_not_excluded(s1 + s2, names)
            == (names_not_excluded(s1, names) && names_not_excluded(s2, names)),
    decreases names.len()
{
    if names.len() > 0 {
        if let Some(name) = constrained_name(names.last()) {
            lemma_excluded_is_union(s1, s2, name);
        }
        lemma_names_not_excluded_concat(s1, s2, names.drop_last());
    }
}

/// An uninterpreted form is constrained by a concatenated state iff it is by
/// one of the parts.
pub proof fn lemma_form_constrained_concat(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    tag: u32,
)
    ensures form_constrained(s1 + s2, tag) == (form_constrained(s1, tag) || form_constrained(s2, tag)),
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        assert((s1 + s2).last() == s2.last());
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        lemma_form_constrained_concat(s1, s2.drop_last(), tag);
    }
}

/// The other-forms check for a concatenated state is the check for each part.
pub proof fn lemma_names_of_unconstrained_forms_concat(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        names_of_unconstrained_forms(s1 + s2, names)
            == (names_of_unconstrained_forms(s1, names) && names_of_unconstrained_forms(s2, names)),
    decreases names.len()
{
    if names.len() > 0 {
        if let crate::extensions::spec::GeneralName::Other(tag, _) = names.last() {
            lemma_form_constrained_concat(s1, s2, tag);
        }
        lemma_names_of_unconstrained_forms_concat(s1, s2, names.drop_last());
    }
}

/// A certificate satisfies a concatenated state iff it satisfies each part;
/// so the certificate check, too, is independent of the order and grouping
/// of the constraint sets.
pub proof fn lemma_certificate_check_is_conjunction(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        certificate_names_acceptable(s1 + s2, names)
            == (certificate_names_acceptable(s1, names) && certificate_names_acceptable(s2, names)),
{
    lemma_names_within_permitted_concat(s1, s2, names);
    lemma_names_not_excluded_concat(s1, s2, names);
    lemma_names_of_unconstrained_forms_concat(s1, s2, names);
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    }
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    }
}

/// Adding a constraint set never makes a certificate acceptable that was
/// not.
pub proof fn lemma_certificate_check_monotone(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
    names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        certificate_names_acceptable(state.push(value), names)
            ==> certificate_names_acceptable(state, names),
{
    assert(state.push(value) =~= state + seq![value]);
    lemma_certificate_check_is_conjunction(state, seq![value], names);
}

/// A certificate that satisfies a state satisfies each constraint set in it
/// on its own: the per-certificate form of `thm_names_constrained` ("every
/// k < i with NC").
pub proof fn lemma_certificate_check_each_set(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    k: int,
)
    requires certificate_names_acceptable(state, names), 0 <= k < state.len(),
    ensures certificate_names_acceptable(seq![state[k]], names),
{
    let front = state.subrange(0, k);
    let back = state.subrange(k + 1, state.len() as int);
    assert(state =~= front + (seq![state[k]] + back));
    lemma_certificate_check_is_conjunction(front, seq![state[k]] + back, names);
    lemma_certificate_check_is_conjunction(seq![state[k]], back, names);
}

// ---------------------------------------------------------------------------
// The path: building blocks of `thm_names_constrained`
// ---------------------------------------------------------------------------

/// The state when certificate `i` is checked: the initial state with
/// §6.1.4 (g) applied for certificates `0..i`, or `None` if one of them
/// refused the path.
pub open spec fn state_before(
    path: Seq<NcCertificate>,
    i: int,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
) -> Option<Seq<crate::name_constraints::spec::NameConstraints>>
    decreases i
{
    if i <= 0 {
        Some(initial)
    } else {
        match state_before(path, i - 1, initial) {
            Some(state) => prepare_name_constraints(state, path[i - 1].name_constraints),
            None => None,
        }
    }
}

/// The NameConstraints extensions present in `path[0..i]`, in order.
pub open spec fn collected_constraints(path: Seq<NcCertificate>, i: int)
    -> Seq<crate::name_constraints::spec::NameConstraints>
    decreases i
{
    if i <= 0 {
        seq![]
    } else {
        match path[i - 1].name_constraints {
            Some(value) => collected_constraints(path, i - 1).push(value),
            None => collected_constraints(path, i - 1),
        }
    }
}

/// The state before certificate `i` is the initial state followed by every
/// constraint set met so far.
pub proof fn lemma_state_before_is_collected(
    path: Seq<NcCertificate>,
    i: int,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
)
    requires state_before(path, i, initial) is Some,
    ensures state_before(path, i, initial) == Some(initial + collected_constraints(path, i)),
    decreases i
{
    if i <= 0 {
        assert(initial + seq![] =~= initial);
    } else {
        lemma_state_before_is_collected(path, i - 1, initial);
        if let Some(value) = path[i - 1].name_constraints {
            assert((initial + collected_constraints(path, i - 1)).push(value)
                =~= initial + collected_constraints(path, i - 1).push(value));
        }
    }
}

proof fn lemma_names_constrained_from_at(
    path: Seq<NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
    j: int,
    i: int,
    state: Seq<crate::name_constraints::spec::NameConstraints>,
)
    requires
        0 <= j <= i < path.len(),
        state_before(path, j, initial) == Some(state),
        names_constrained_from(path, j, state),
    ensures
        state_before(path, i, initial) is Some,
        certificate_acceptable(state_before(path, i, initial).unwrap(), path[i]),
    decreases i - j
{
    if j < i {
        let next = prepare_name_constraints(state, path[j].name_constraints).unwrap();
        assert(state_before(path, j + 1, initial) == prepare_name_constraints(state, path[j].name_constraints));
        lemma_names_constrained_from_at(path, initial, j + 1, i, next);
    }
}

/// `thm_names_constrained`'s per-certificate fact: on an accepted path,
/// every certificate, self-issued ones included, satisfies §6.1.3 (b) and
/// (c), for its subjectAltName entries and its subject, under
/// the state built from the initial state and every earlier certificate's
/// constraints.
pub proof fn lemma_names_constrained_at(
    path: Seq<NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
    i: int,
)
    requires names_constrained(path, initial), 0 <= i < path.len(),
    ensures
        state_before(path, i, initial) == Some(initial + collected_constraints(path, i)),
        certificate_acceptable(initial + collected_constraints(path, i), path[i]),
{
    lemma_names_constrained_from_at(path, initial, 0, i, initial);
    lemma_state_before_is_collected(path, i, initial);
}

// ---------------------------------------------------------------------------
// iPAddress subtrees
// ---------------------------------------------------------------------------

/// `x AND mask`, octet by octet.
pub open spec fn apply_mask(x: Seq<u8>, mask: Seq<u8>) -> Seq<u8> {
    Seq::new(x.len(), |i: int| x[i] & mask[i])
}

proof fn lemma_ip_masked_equal_from_all(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>, i: int)
    requires address.len() == base.len(), base.len() == mask.len(), 0 <= i <= address.len(),
    ensures
        ip_masked_equal_from(address, base, mask, i)
            == forall|j: int| i <= j < address.len() ==> #[trigger] (address[j] & mask[j]) == base[j] & mask[j],
    decreases address.len() - i
{
    if i < address.len() {
        lemma_ip_masked_equal_from_all(address, base, mask, i + 1);
    }
}

/// iPAddress containment is the mask arithmetic: the address with the mask
/// applied equals the base address with the mask applied.
pub proof fn lemma_ip_within_is_masked_equality(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>)
    ensures
        ip_within(address, base, mask)
            == (address.len() == base.len() && base.len() == mask.len()
                && apply_mask(address, mask) =~= apply_mask(base, mask)),
{
    if address.len() == base.len() && base.len() == mask.len() {
        lemma_ip_masked_equal_from_all(address, base, mask, 0);
        if apply_mask(address, mask) =~= apply_mask(base, mask) {
            assert forall|j: int| 0 <= j < address.len() implies
                #[trigger] (address[j] & mask[j]) == base[j] & mask[j] by {
                assert(apply_mask(address, mask)[j] == apply_mask(base, mask)[j]);
            }
        }
    }
}

proof fn lemma_all_zero_from(mask: Seq<u8>, i: int)
    requires 0 <= i, all_zero_from(mask, i),
    ensures forall|j: int| i <= j < mask.len() ==> #[trigger] mask[j] == 0,
    decreases mask.len() - i
{
    if i < mask.len() {
        lemma_all_zero_from(mask, i + 1);
    }
}

/// The all-zero mask (0.0.0.0/0, ::/0) holds every address of its length:
/// BR §7.1.2.5.2's "iPAddress of 8 zero octets" excludes all of IPv4.
pub proof fn lemma_ip_zero_mask_holds_every_address(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>)
    requires address.len() == base.len(), base.len() == mask.len(), all_zero_from(mask, 0),
    ensures ip_within(address, base, mask),
{
    lemma_all_zero_from(mask, 0);
    lemma_ip_masked_equal_from_all(address, base, mask, 0);
    assert forall|j: int| 0 <= j < address.len() implies
        #[trigger] (address[j] & mask[j]) == base[j] & mask[j] by {
        let (x, y, m) = (address[j], base[j], mask[j]);
        assert(m == 0);
        assert(m == 0 ==> x & m == y & m) by (bit_vector);
    }
}

/// An all-ones mask (/32, /128) holds exactly the base address
/// (`rfc5280::nc::permitted-ipv6-match` with `::1/128`).
pub proof fn lemma_ip_full_mask_is_equality(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>)
    requires
        address.len() == base.len(),
        base.len() == mask.len(),
        forall|j: int| 0 <= j < mask.len() ==> #[trigger] mask[j] == 0xFF,
    ensures ip_within(address, base, mask) == (address == base),
{
    lemma_ip_masked_equal_from_all(address, base, mask, 0);
    if ip_within(address, base, mask) {
        assert forall|j: int| 0 <= j < address.len() implies address[j] == base[j] by {
            let (x, y, m) = (address[j], base[j], mask[j]);
            assert(m == 0xFF);
            assert(address[j] & mask[j] == base[j] & mask[j]);
            assert(m == 0xFF && x & m == y & m ==> x == y) by (bit_vector);
        }
        assert(address =~= base);
    }
}

/// An IPv4 address is never within an IPv6 base, nor the reverse.
pub proof fn lemma_ip_versions_never_match(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>)
    requires address.len() == 4 && base.len() == 16 || address.len() == 16 && base.len() == 4,
    ensures !ip_within(address, base, mask),
{
}

/// A non-contiguous mask is not matched (modelling choice): a base with one
/// refuses the path.
pub proof fn lemma_noncontiguous_mask_refused(
    address: Seq<u8>,
    mask: Seq<u8>,
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
)
    requires
        !mask_contiguous_from(mask, 0),
        value.excluded_subtrees == Some(seq![crate::name_constraints::spec::GeneralSubtree {
            base: crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask },
        }]),
    ensures
        !base_supported(crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask }),
        prepare_name_constraints(state, Some(value)) is None,
{
    let items = seq![crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask },
    }];
    assert(items.last() == items[0]);
}

// ---------------------------------------------------------------------------
// dNSName subtrees
// ---------------------------------------------------------------------------

/// `folded_equal_from` is the universal statement it abbreviates.
pub proof fn lemma_folded_equal_all(a: Seq<u8>, b: Seq<u8>, i: int)
    requires 0 <= i <= a.len(),
    ensures
        crate::spec::folded_equal_from(a, b, i) == (a.len() == b.len() && forall|j: int| i <= j < a.len()
            ==> #[trigger] crate::spec::ascii_fold(a[j]) == crate::spec::ascii_fold(b[j])),
    decreases a.len() - i
{
    if i < a.len() {
        lemma_folded_equal_all(a, b, i + 1);
    }
}

/// Only `.` folds to `.`: case folding never creates or removes a label
/// boundary.
pub proof fn lemma_fold_dot(x: u8)
    ensures crate::spec::ascii_fold(x) == crate::spec::ascii_fold(b'.') ==> x == b'.',
{
    assert(65u8 <= x && x <= 90u8 ==> (x | 0x20u8) >= 97u8) by (bit_vector);
}

/// `dns_within` written out: the base is empty, or the name ends with the
/// base (ignoring case), preceded by a dot when the name is longer.
pub proof fn lemma_dns_within_pointwise(name: Seq<u8>, base: Seq<u8>)
    ensures
        dns_within(name, base) == (base.len() == 0 || (name.len() >= base.len()
            && (name.len() > base.len() ==> name[name.len() - base.len() - 1] == b'.')
            && forall|j: int| 0 <= j < base.len() ==> #[trigger] crate::spec::ascii_fold(
                name[name.len() - base.len() + j]) == crate::spec::ascii_fold(base[j]))),
{
    if base.len() > 0 && name.len() == base.len() {
        lemma_folded_equal_all(name, base, 0);
        if crate::spec::folded_equal_from(name, base, 0) {
            assert forall|j: int| 0 <= j < base.len() implies #[trigger] crate::spec::ascii_fold(
                name[name.len() - base.len() + j]) == crate::spec::ascii_fold(base[j]) by {
                assert(name.len() - base.len() + j == j);
                assert(crate::spec::ascii_fold(name[j]) == crate::spec::ascii_fold(base[j]));
            }
        }
        if forall|j: int| 0 <= j < base.len() ==> #[trigger] crate::spec::ascii_fold(
            name[name.len() - base.len() + j]) == crate::spec::ascii_fold(base[j]) {
            assert forall|j: int| 0 <= j < name.len() implies #[trigger] crate::spec::ascii_fold(
                name[j]) == crate::spec::ascii_fold(base[j]) by {
                assert(name.len() - base.len() + j == j);
                assert(crate::spec::ascii_fold(name[name.len() - base.len() + j])
                    == crate::spec::ascii_fold(base[j]));
            }
        }
    } else if base.len() > 0 && name.len() > base.len() {
        let tail = name.subrange(name.len() - base.len(), name.len() as int);
        lemma_folded_equal_all(tail, base, 0);
        if crate::spec::folded_equal_from(tail, base, 0) {
            assert forall|j: int| 0 <= j < base.len() implies #[trigger] crate::spec::ascii_fold(
                name[name.len() - base.len() + j]) == crate::spec::ascii_fold(base[j]) by {
                assert(tail[j] == name[name.len() - base.len() + j]);
                assert(crate::spec::ascii_fold(tail[j]) == crate::spec::ascii_fold(base[j]));
            }
        }
        if forall|j: int| 0 <= j < base.len() ==> #[trigger] crate::spec::ascii_fold(
            name[name.len() - base.len() + j]) == crate::spec::ascii_fold(base[j]) {
            assert forall|j: int| 0 <= j < tail.len() implies
                #[trigger] crate::spec::ascii_fold(tail[j]) == crate::spec::ascii_fold(base[j]) by {
                assert(tail[j] == name[name.len() - base.len() + j]);
            }
        }
    }
}

/// `within` is reflexive for DNS names: every name is within itself.
pub proof fn lemma_dns_within_reflexive(name: Seq<u8>)
    ensures dns_within(name, name),
{
    lemma_folded_equal_all(name, name, 0);
}

/// `within` is transitive for DNS names: a name within a subtree that is
/// within another subtree is within that one.
pub proof fn lemma_dns_within_transitive(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires dns_within(a, b), dns_within(b, c),
    ensures dns_within(a, c),
{
    lemma_dns_within_pointwise(a, b);
    lemma_dns_within_pointwise(b, c);
    lemma_dns_within_pointwise(a, c);
    if c.len() > 0 {
        let (la, lb, lc) = (a.len() as int, b.len() as int, c.len() as int);
        assert(lb >= lc);
        assert(la >= lb);
        assert forall|j: int| 0 <= j < lc implies #[trigger] crate::spec::ascii_fold(a[la - lc + j])
            == crate::spec::ascii_fold(c[j]) by {
            assert(crate::spec::ascii_fold(b[lb - lc + j]) == crate::spec::ascii_fold(c[j]));
            let k = lb - lc + j;
            assert(crate::spec::ascii_fold(a[la - lb + k]) == crate::spec::ascii_fold(b[k]));
            assert(la - lb + k == la - lc + j);
        }
        if la > lc {
            if lb > lc {
                let k = lb - lc - 1;
                assert(b[k] == b'.');
                assert(crate::spec::ascii_fold(a[la - lb + k]) == crate::spec::ascii_fold(b[k]));
                lemma_fold_dot(a[la - lb + k]);
                assert(la - lb + k == la - lc - 1);
            } else {
                assert(a[la - lb - 1] == b'.');
            }
        }
    }
}

/// Clause 3 of `dns_within` is "one or more labels added": a name in
/// preferred name syntax that is within a base and longer than it is a
/// nonempty prefix, a dot, and the base (ignoring case).
pub proof fn lemma_dns_within_is_adding_labels(name: Seq<u8>, base: Seq<u8>)
    requires
        dns_within(name, base),
        base.len() > 0,
        name.len() > base.len(),
        crate::spec::dns_name_shape(name),
    ensures ({
        let k = name.len() - base.len() - 1;
        &&& 0 < k
        &&& name =~= name.subrange(0, k) + seq![b'.'] + name.subrange(k + 1, name.len() as int)
        &&& crate::spec::folded_equal_from(name.subrange(k + 1, name.len() as int), base, 0)
    }),
{
    let k = name.len() - base.len() - 1;
    if k == 0 {
        assert(name[0] == b'.');
        assert(!crate::spec::valid_name_from(name, 0));
    }
    assert(name =~= name.subrange(0, k) + seq![b'.'] + name.subrange(k + 1, name.len() as int));
}

/// Conversely, adding labels in front of a base gives a name within it:
/// `prefix . base` is within `base`.
pub proof fn lemma_dns_within_adding_labels(prefix: Seq<u8>, base: Seq<u8>)
    ensures dns_within(prefix + seq![b'.'] + base, base),
{
    let name = prefix + seq![b'.'] + base;
    lemma_dns_within_pointwise(name, base);
    assert(name[name.len() - base.len() - 1] == b'.');
    assert forall|j: int| 0 <= j < base.len() implies #[trigger] crate::spec::ascii_fold(
        name[name.len() - base.len() + j]) == crate::spec::ascii_fold(base[j]) by {
        assert(name[name.len() - base.len() + j] == base[j]);
    }
}

/// Case-insensitivity, name side: names equal up to ASCII case are within
/// the same subtrees (RFC 9549 §2.3).
pub proof fn lemma_dns_within_case_insensitive_name(n1: Seq<u8>, n2: Seq<u8>, base: Seq<u8>)
    requires n1.len() == n2.len(), crate::spec::folded_equal_from(n1, n2, 0),
    ensures dns_within(n1, base) == dns_within(n2, base),
{
    lemma_folded_equal_all(n1, n2, 0);
    lemma_dns_within_pointwise(n1, base);
    lemma_dns_within_pointwise(n2, base);
    let (l, lb) = (n1.len() as int, base.len() as int);
    if lb > 0 && l > lb {
        let k = l - lb - 1;
        lemma_fold_dot(n1[k]);
        lemma_fold_dot(n2[k]);
        assert(crate::spec::ascii_fold(n1[k]) == crate::spec::ascii_fold(n2[k]));
    }
    if lb > 0 && l >= lb {
        if forall|j: int| 0 <= j < lb ==> #[trigger] crate::spec::ascii_fold(n1[l - lb + j])
            == crate::spec::ascii_fold(base[j]) {
            assert forall|j: int| 0 <= j < lb implies #[trigger] crate::spec::ascii_fold(
                n2[n2.len() - lb + j]) == crate::spec::ascii_fold(base[j]) by {
                assert(crate::spec::ascii_fold(n1[l - lb + j]) == crate::spec::ascii_fold(base[j]));
                assert(crate::spec::ascii_fold(n1[l - lb + j]) == crate::spec::ascii_fold(n2[l - lb + j]));
            }
        }
        if forall|j: int| 0 <= j < lb ==> #[trigger] crate::spec::ascii_fold(n2[l - lb + j])
            == crate::spec::ascii_fold(base[j]) {
            assert forall|j: int| 0 <= j < lb implies #[trigger] crate::spec::ascii_fold(
                n1[n1.len() - lb + j]) == crate::spec::ascii_fold(base[j]) by {
                assert(crate::spec::ascii_fold(n2[l - lb + j]) == crate::spec::ascii_fold(base[j]));
                assert(crate::spec::ascii_fold(n1[l - lb + j]) == crate::spec::ascii_fold(n2[l - lb + j]));
            }
        }
    }
}

/// Case-insensitivity, base side: bases equal up to ASCII case stand for
/// the same subtree.
pub proof fn lemma_dns_within_case_insensitive_base(name: Seq<u8>, b1: Seq<u8>, b2: Seq<u8>)
    requires crate::spec::folded_equal_from(b1, b2, 0),
    ensures dns_within(name, b1) == dns_within(name, b2),
{
    lemma_folded_equal_all(b1, b2, 0);
    lemma_dns_within_pointwise(name, b1);
    lemma_dns_within_pointwise(name, b2);
}

// ---------------------------------------------------------------------------
// Wildcard dNSName entries
// ---------------------------------------------------------------------------

/// The permitted rule for `*.suffix` is sound: when it holds, every name
/// the wildcard stands for (any label, a dot, the suffix) is within the base.
pub proof fn lemma_wildcard_within_sound(label: Seq<u8>, suffix: Seq<u8>, base: Seq<u8>)
    requires dns_wildcard_within(suffix, base),
    ensures dns_within(label + seq![b'.'] + suffix, base),
{
    lemma_dns_within_adding_labels(label, suffix);
    lemma_dns_within_transitive(label + seq![b'.'] + suffix, suffix, base);
}

proof fn lemma_first_dot_at(name: Seq<u8>, i: int, k: int)
    requires
        0 <= i <= k < name.len(),
        name[k] == b'.',
        forall|j: int| 0 <= j < k ==> #[trigger] name[j] != b'.',
    ensures crate::spec::first_dot(name, i) == k,
    decreases k - i
{
    if i < k {
        lemma_first_dot_at(name, i + 1, k);
    }
}

/// The excluded rule for `*.suffix` is complete: if any name the wildcard
/// stands for is within the base, the rule says the wildcard meets it, so
/// an excluded subtree can never be reached through a wildcard.
pub proof fn lemma_wildcard_meets_complete(label: Seq<u8>, suffix: Seq<u8>, base: Seq<u8>)
    requires
        forall|j: int| 0 <= j < label.len() ==> #[trigger] label[j] != b'.',
        dns_within(label + seq![b'.'] + suffix, base),
    ensures dns_wildcard_meets(suffix, base),
{
    let x = label + seq![b'.'] + suffix;
    let (ll, ls, lb) = (label.len() as int, suffix.len() as int, base.len() as int);
    lemma_dns_within_pointwise(x, base);
    lemma_dns_within_pointwise(suffix, base);
    assert forall|j: int| 0 <= j < ls implies #[trigger] x[ll + 1 + j] == suffix[j] by {}
    assert(x[ll] == b'.');
    if lb > 0 {
        if lb <= ls {
            assert forall|j: int| 0 <= j < lb implies #[trigger] crate::spec::ascii_fold(
                suffix[ls - lb + j]) == crate::spec::ascii_fold(base[j]) by {
                assert(x[x.len() - lb + j] == suffix[ls - lb + j]);
            }
            if ls > lb {
                assert(x[x.len() - lb - 1] == suffix[ls - lb - 1]);
            }
        } else if lb < x.len() {
            let k = x.len() - lb - 1;
            assert(k < ll);
            assert(x[k] == label[k]);
        } else {
            assert(lb == x.len());
            assert(crate::spec::ascii_fold(x[x.len() - lb + ll]) == crate::spec::ascii_fold(base[ll]));
            assert(x.len() - lb + ll == ll);
            lemma_fold_dot(base[ll]);
            assert forall|j: int| 0 <= j < ll implies #[trigger] base[j] != b'.' by {
                assert(crate::spec::ascii_fold(x[x.len() - lb + j]) == crate::spec::ascii_fold(base[j]));
                assert(x.len() - lb + j == j);
                lemma_fold_dot(x[j]);
                assert(x[j] == label[j]);
            }
            lemma_first_dot_at(base, 0, ll);
            let rest = base.subrange(ll + 1, lb);
            lemma_folded_equal_all(rest, suffix, 0);
            assert forall|j: int| 0 <= j < rest.len() implies #[trigger] crate::spec::ascii_fold(
                rest[j]) == crate::spec::ascii_fold(suffix[j]) by {
                assert(rest[j] == base[ll + 1 + j]);
                assert(crate::spec::ascii_fold(x[x.len() - lb + (ll + 1 + j)])
                    == crate::spec::ascii_fold(base[ll + 1 + j]));
            }
        }
    }
}

/// For a DNS name, an address or a directory name, `meets` is `within`;
/// only a wildcard and a mailbox (whose local part an excluded base matches
/// ignoring case) tell them apart.
pub proof fn lemma_meets_is_within_except_wildcards(
    name: ConstrainedName,
    base: crate::name_constraints::spec::GeneralNameConstraint,
)
    requires !(name is DnsWildcard), !(name is Rfc822),
    ensures meets(name, base) == within(name, base),
{
}

// ---------------------------------------------------------------------------
// The whole certificate: subjectAltName entries and the subject field
// ---------------------------------------------------------------------------

/// An rfc822Name constraint is in force in a concatenated state iff it is in
/// one of the parts.
pub proof fn lemma_rfc822_in_force_concat(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
)
    ensures rfc822_in_force(s1 + s2) == (rfc822_in_force(s1) || rfc822_in_force(s2)),
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        assert((s1 + s2).last() == s2.last());
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        lemma_rfc822_in_force_concat(s1, s2.drop_last());
    }
}

/// The subject check for a concatenated state is the check for each part.
pub proof fn lemma_subject_check_is_conjunction(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    subject: Seq<u8>,
)
    ensures
        subject_acceptable(s1 + s2, subject)
            == (subject_acceptable(s1, subject) && subject_acceptable(s2, subject)),
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        assert((s1 + s2).len() > 0);
        if let Some(parsed) = crate::name::spec::parse_name(subject) {
            lemma_acceptable_is_conjunction(s1, s2, ConstrainedName::Directory(parsed.rdns));
            lemma_rfc822_in_force_concat(s1, s2);
        }
    }
}

/// A certificate, subject included, satisfies a concatenated state iff it
/// satisfies each part.
pub proof fn lemma_certificate_acceptable_is_conjunction(
    s1: Seq<crate::name_constraints::spec::NameConstraints>,
    s2: Seq<crate::name_constraints::spec::NameConstraints>,
    certificate: NcCertificate,
)
    ensures
        certificate_acceptable(s1 + s2, certificate)
            == (certificate_acceptable(s1, certificate) && certificate_acceptable(s2, certificate)),
{
    lemma_certificate_check_is_conjunction(s1, s2, certificate.subject_alt_names);
    lemma_subject_check_is_conjunction(s1, s2, certificate.subject);
}

/// Monotonicity for every form, the subject and the other forms included:
/// adding a constraint set never makes a certificate acceptable that was
/// not.
pub proof fn lemma_certificate_acceptable_monotone(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
    certificate: NcCertificate,
)
    ensures certificate_acceptable(state.push(value), certificate) ==> certificate_acceptable(state, certificate),
{
    assert(state.push(value) =~= state + seq![value]);
    lemma_certificate_acceptable_is_conjunction(state, seq![value], certificate);
}

/// A certificate that satisfies a state satisfies each constraint set in it
/// on its own, subject included.
pub proof fn lemma_certificate_acceptable_each_set(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    certificate: NcCertificate,
    k: int,
)
    requires certificate_acceptable(state, certificate), 0 <= k < state.len(),
    ensures certificate_acceptable(seq![state[k]], certificate),
{
    let front = state.subrange(0, k);
    let back = state.subrange(k + 1, state.len() as int);
    assert(state =~= front + (seq![state[k]] + back));
    lemma_certificate_acceptable_is_conjunction(front, seq![state[k]] + back, certificate);
    lemma_certificate_acceptable_is_conjunction(seq![state[k]], back, certificate);
}

/// Adding a constraint set never unconstrains an uninterpreted form.
pub proof fn lemma_form_constrained_monotone(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
    tag: u32,
)
    ensures form_constrained(state, tag) ==> form_constrained(state.push(value), tag),
{
    assert(state.push(value).drop_last() =~= state);
}

// ---------------------------------------------------------------------------
// Excluded beats permitted; excluded directoryName
// ---------------------------------------------------------------------------

/// §4.2.1.10 "Any name matching a restriction in the excludedSubtrees field
/// is invalid regardless of information appearing in the permittedSubtrees",
/// for every form.
pub proof fn lemma_excluded_beats_permitted(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    requires within_excluded_subtrees(state, name),
    ensures !name_acceptable(state, name),
{
}

/// A name within a base meets it, for every form: so the same base in both
/// lists refuses every name it holds.
pub proof fn lemma_within_implies_meets(
    name: ConstrainedName,
    base: crate::name_constraints::spec::GeneralNameConstraint,
)
    ensures within(name, base) ==> meets(name, base),
{
    if let (ConstrainedName::Rfc822 { local, host }, crate::name_constraints::spec::GeneralNameConstraint::Rfc822Name(b))
        = (name, base) {
        lemma_rfc822_within_implies_meets(local, host, b);
    }
}

/// (R) excluded directoryName: a NameConstraints value with a directoryName
/// base in excludedSubtrees refuses the path, whatever the state.
pub proof fn lemma_excluded_directory_name_refused(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    value: crate::name_constraints::spec::NameConstraints,
)
    requires
        value.excluded_subtrees is Some,
        has_directory_name_base(value.excluded_subtrees.unwrap()),
    ensures prepare_name_constraints(state, Some(value)) is None,
{
}

// ---------------------------------------------------------------------------
// Unconstrained forms
// ---------------------------------------------------------------------------

/// Some set in the state has a base of `name`'s type, in either list.
pub open spec fn type_constrained(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
) -> bool
    decreases state.len()
{
    state.len() > 0 && ({
        ||| match state.last().permitted_subtrees {
            Some(items) => has_base_of_type(items, name),
            None => false,
        }
        ||| match state.last().excluded_subtrees {
            Some(items) => has_base_of_type(items, name),
            None => false,
        }
        ||| type_constrained(state.drop_last(), name)
    })
}

/// A name meets only bases of its own type.
pub proof fn lemma_meets_some_needs_type(
    items: Seq<crate::name_constraints::spec::GeneralSubtree>,
    name: ConstrainedName,
)
    ensures meets_some(items, name) ==> has_base_of_type(items, name),
    decreases items.len()
{
    if items.len() > 0 {
        lemma_meets_some_needs_type(items.drop_last(), name);
    }
}

/// A name whose type no set constrains is acceptable (§4.2.1.10
/// "Restrictions apply only when the specified name form is present").
pub proof fn lemma_unconstrained_type_accepted(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
)
    requires !type_constrained(state, name),
    ensures name_acceptable(state, name),
    decreases state.len()
{
    if state.len() > 0 {
        lemma_unconstrained_type_accepted(state.drop_last(), name);
        if let Some(items) = state.last().excluded_subtrees {
            lemma_meets_some_needs_type(items, name);
        }
    }
}

/// An entry no set constrains: of a matched form whose type no set
/// constrains, or of an uninterpreted form no set constrains.
pub open spec fn entry_unconstrained(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    entry: crate::extensions::spec::GeneralName,
) -> bool {
    match constrained_name(entry) {
        Some(name) => !type_constrained(state, name),
        None => match entry {
            crate::extensions::spec::GeneralName::Other(tag, _) => !form_constrained(state, tag),
            _ => true,
        },
    }
}

/// Every entry is unconstrained.
pub open spec fn entries_unconstrained(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
) -> bool
    decreases names.len()
{
    names.len() == 0 || (entry_unconstrained(state, names.last()) && entries_unconstrained(state, names.drop_last()))
}

/// An unconstrained form is never refused except as malformed: well-formed
/// entries of forms no set constrains always pass §6.1.3 (b) and (c).
pub proof fn lemma_unconstrained_form_never_refused(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
)
    requires names_well_formed(names), entries_unconstrained(state, names),
    ensures certificate_names_acceptable(state, names),
    decreases names.len()
{
    if names.len() > 0 {
        lemma_unconstrained_form_never_refused(state, names.drop_last());
        if let Some(name) = constrained_name(names.last()) {
            lemma_unconstrained_type_accepted(state, name);
        }
    }
}

/// The other forms: an entry of an uninterpreted form that some set
/// constrains, in either list, fails the certificate.
pub proof fn lemma_constrained_other_form_refused(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    i: int,
    tag: u32,
    der: Seq<u8>,
)
    requires
        0 <= i < names.len(),
        names[i] == crate::extensions::spec::GeneralName::Other(tag, der),
        is_uninterpreted_form(tag),
        form_constrained(state, tag),
    ensures !certificate_names_acceptable(state, names),
    decreases names.len()
{
    if i < names.len() - 1 {
        assert(names.drop_last()[i] == names[i]);
        lemma_constrained_other_form_refused(state, names.drop_last(), i, tag, der);
    }
}

// ---------------------------------------------------------------------------
// rfc822Name subtrees
// ---------------------------------------------------------------------------

/// A mailbox within a base meets it: byte equality implies equality up to
/// case.
pub proof fn lemma_rfc822_within_implies_meets(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>)
    ensures rfc822_within(local, host, base) ==> rfc822_meets(local, host, base),
{
    let base_local = mailbox_local(base);
    lemma_folded_equal_all(local, base_local, 0);
}

/// A mailbox base holds itself.
pub proof fn lemma_rfc822_mailbox_reflexive(m: Seq<u8>)
    requires is_mailbox(m),
    ensures rfc822_within(mailbox_local(m), mailbox_host(m), m),
{
    lemma_folded_equal_all(mailbox_host(m), mailbox_host(m), 0);
    assert(mailbox_local(m) =~= mailbox_local(m));
}

/// A host base holds exactly the mailboxes at that host, up to case
/// (`nc-permits-email-domain-rejects-subdomain`).
pub proof fn lemma_rfc822_host_base_is_exact(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>)
    requires first_at(base, 0) >= base.len(), base.len() == 0 || base[0] != b'.',
    ensures
        rfc822_within(local, host, base) == crate::spec::folded_equal_from(host, base, 0),
        rfc822_meets(local, host, base) == rfc822_within(local, host, base),
{
}

/// A domain base `.d` holds only hosts with one or more labels added to `d`:
/// for a host in preferred name syntax, that is `dns_within` with a longer
/// name (`nc-permits-email-subdomains-rejects-apex`).
pub proof fn lemma_rfc822_domain_is_proper_subdomain(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>)
    requires
        first_at(base, 0) >= base.len(),
        base.len() > 0,
        base[0] == b'.',
        rfc822_within(local, host, base),
    ensures ({
        let domain = base.subrange(1, base.len() as int);
        &&& host.len() > domain.len()
        &&& host.len() != domain.len()
        &&& dns_within(host, domain)
    }),
{
    let domain = base.subrange(1, base.len() as int);
    let (lh, lb) = (host.len() as int, base.len() as int);
    let tail = host.subrange(lh - lb, lh);
    lemma_folded_equal_all(tail, base, 0);
    lemma_dns_within_pointwise(host, domain);
    assert(tail[0] == host[lh - lb]);
    assert(crate::spec::ascii_fold(tail[0]) == crate::spec::ascii_fold(base[0]));
    lemma_fold_dot(host[lh - lb]);
    assert(host[lh - domain.len() - 1] == b'.');
    if domain.len() > 0 {
        assert forall|j: int| 0 <= j < domain.len() implies #[trigger] crate::spec::ascii_fold(
            host[host.len() - domain.len() + j]) == crate::spec::ascii_fold(domain[j]) by {
            assert(tail[j + 1] == host[lh - lb + j + 1]);
            assert(crate::spec::ascii_fold(tail[j + 1]) == crate::spec::ascii_fold(base[j + 1]));
        }
    }
}

/// So a domain base never holds its apex: `.d` does not hold mailboxes at
/// `d`.
pub proof fn lemma_rfc822_domain_excludes_apex(local: Seq<u8>, domain: Seq<u8>)
    requires first_at(seq![b'.'] + domain, 0) >= domain.len() + 1,
    ensures !rfc822_within(local, domain, seq![b'.'] + domain),
{
    let base = seq![b'.'] + domain;
    assert(base[0] == b'.');
}

// ---------------------------------------------------------------------------
// directoryName subtrees
// ---------------------------------------------------------------------------

/// Firefox's tag relaxation is symmetric.
pub proof fn lemma_value_tags_compatible_symmetric(a: clazel_der::spec::Tag, b: clazel_der::spec::Tag)
    ensures value_tags_compatible(a, b) == value_tags_compatible(b, a),
{
}

/// And transitive: UTF8String and PrintableString form one class, every
/// other tag its own.
pub proof fn lemma_value_tags_compatible_transitive(
    a: clazel_der::spec::Tag,
    b: clazel_der::spec::Tag,
    c: clazel_der::spec::Tag,
)
    requires value_tags_compatible(a, b), value_tags_compatible(b, c),
    ensures value_tags_compatible(a, c),
{
}

/// Attribute matching is symmetric: a base and a name may trade places.
pub proof fn lemma_attribute_match_symmetric(
    x: crate::name::spec::AttributeTypeAndValue,
    y: crate::name::spec::AttributeTypeAndValue,
)
    ensures attribute_match(x, y) == attribute_match(y, x),
{
    lemma_value_tags_compatible_symmetric(x.value_tag, y.value_tag);
}

/// Attribute matching is transitive.
pub proof fn lemma_attribute_match_transitive(
    x: crate::name::spec::AttributeTypeAndValue,
    y: crate::name::spec::AttributeTypeAndValue,
    z: crate::name::spec::AttributeTypeAndValue,
)
    requires attribute_match(x, y), attribute_match(y, z),
    ensures attribute_match(x, z),
{
    lemma_value_tags_compatible_transitive(x.value_tag, y.value_tag, z.value_tag);
}

/// `attributes_match` is the pointwise statement it abbreviates.
pub proof fn lemma_attributes_match_pointwise(
    b: Seq<crate::name::spec::AttributeTypeAndValue>,
    n: Seq<crate::name::spec::AttributeTypeAndValue>,
)
    ensures
        attributes_match(b, n) == (b.len() == n.len()
            && forall|k: int| 0 <= k < b.len() ==> #[trigger] attribute_match(b[k], n[k])),
    decreases b.len()
{
    if b.len() > 0 && b.len() == n.len() {
        lemma_attributes_match_pointwise(b.drop_last(), n.drop_last());
        if attributes_match(b, n) {
            assert forall|k: int| 0 <= k < b.len() implies #[trigger] attribute_match(b[k], n[k]) by {
                if k < b.len() - 1 {
                    assert(b.drop_last()[k] == b[k]);
                    assert(n.drop_last()[k] == n[k]);
                }
            }
        }
        if forall|k: int| 0 <= k < b.len() ==> #[trigger] attribute_match(b[k], n[k]) {
            assert(attribute_match(b[b.len() - 1], n[n.len() - 1]));
            assert forall|k: int| 0 <= k < b.drop_last().len() implies
                #[trigger] attribute_match(b.drop_last()[k], n.drop_last()[k]) by {
                assert(b.drop_last()[k] == b[k]);
                assert(n.drop_last()[k] == n[k]);
                assert(attribute_match(b[k], n[k]));
            }
        }
    }
}

/// `rdns_match` is the pointwise statement it abbreviates.
pub proof fn lemma_rdns_match_pointwise(
    b: Seq<crate::name::spec::RelativeDistinguishedName>,
    n: Seq<crate::name::spec::RelativeDistinguishedName>,
)
    ensures
        rdns_match(b, n) == (b.len() == n.len()
            && forall|k: int| 0 <= k < b.len() ==> #[trigger] attributes_match(b[k].attributes, n[k].attributes)),
    decreases b.len()
{
    if b.len() > 0 && b.len() == n.len() {
        lemma_rdns_match_pointwise(b.drop_last(), n.drop_last());
        if rdns_match(b, n) {
            assert forall|k: int| 0 <= k < b.len() implies
                #[trigger] attributes_match(b[k].attributes, n[k].attributes) by {
                if k < b.len() - 1 {
                    assert(b.drop_last()[k] == b[k]);
                    assert(n.drop_last()[k] == n[k]);
                }
            }
        }
        if forall|k: int| 0 <= k < b.len() ==> #[trigger] attributes_match(b[k].attributes, n[k].attributes) {
            assert(attributes_match(b[b.len() - 1].attributes, n[n.len() - 1].attributes));
            assert forall|k: int| 0 <= k < b.drop_last().len() implies
                #[trigger] attributes_match(b.drop_last()[k].attributes, n.drop_last()[k].attributes) by {
                assert(b.drop_last()[k] == b[k]);
                assert(n.drop_last()[k] == n[k]);
                assert(attributes_match(b[k].attributes, n[k].attributes));
            }
        }
    }
}

/// Matching lists of attributes is transitive.
pub proof fn lemma_attributes_match_transitive(
    a: Seq<crate::name::spec::AttributeTypeAndValue>,
    b: Seq<crate::name::spec::AttributeTypeAndValue>,
    c: Seq<crate::name::spec::AttributeTypeAndValue>,
)
    requires attributes_match(a, b), attributes_match(b, c),
    ensures attributes_match(a, c),
{
    lemma_attributes_match_pointwise(a, b);
    lemma_attributes_match_pointwise(b, c);
    lemma_attributes_match_pointwise(a, c);
    assert forall|k: int| 0 <= k < a.len() implies #[trigger] attribute_match(a[k], c[k]) by {
        assert(attribute_match(a[k], b[k]));
        assert(attribute_match(b[k], c[k]));
        lemma_attribute_match_transitive(a[k], b[k], c[k]);
    }
}

/// Every attribute value of every RDN is one both browsers compare.
pub open spec fn rdns_comparable(rdns: Seq<crate::name::spec::RelativeDistinguishedName>) -> bool {
    forall|k: int, j: int| 0 <= k < rdns.len() && 0 <= j < rdns[k].attributes.len()
        ==> #[trigger] value_comparable(rdns[k].attributes[j])
}

/// directoryName containment is reflexive for names both browsers can
/// compare: every such name is within itself.
pub proof fn lemma_directory_within_reflexive(name: Seq<crate::name::spec::RelativeDistinguishedName>)
    requires rdns_comparable(name),
    ensures directory_within(name, name),
{
    assert(name.subrange(0, name.len() as int) =~= name);
    lemma_rdns_match_pointwise(name, name);
    assert forall|k: int| 0 <= k < name.len() implies
        #[trigger] attributes_match(name[k].attributes, name[k].attributes) by {
        let attributes = name[k].attributes;
        lemma_attributes_match_pointwise(attributes, attributes);
        assert forall|j: int| 0 <= j < attributes.len() implies
            #[trigger] attribute_match(attributes[j], attributes[j]) by {
            assert(value_comparable(name[k].attributes[j]));
            assert(attributes[j].value_der =~= attributes[j].value_der);
        }
    }
}

/// directoryName containment is transitive: a name within a subtree that is
/// within another subtree is within that one.
pub proof fn lemma_directory_within_transitive(
    a: Seq<crate::name::spec::RelativeDistinguishedName>,
    b: Seq<crate::name::spec::RelativeDistinguishedName>,
    c: Seq<crate::name::spec::RelativeDistinguishedName>,
)
    requires directory_within(a, b), directory_within(b, c),
    ensures directory_within(a, c),
{
    let ab = a.subrange(0, b.len() as int);
    let bc = b.subrange(0, c.len() as int);
    let ac = a.subrange(0, c.len() as int);
    lemma_rdns_match_pointwise(b, ab);
    lemma_rdns_match_pointwise(c, bc);
    lemma_rdns_match_pointwise(c, ac);
    assert forall|k: int| 0 <= k < c.len() implies #[trigger] attributes_match(c[k].attributes, ac[k].attributes) by {
        assert(attributes_match(c[k].attributes, bc[k].attributes));
        assert(bc[k] == b[k]);
        assert(attributes_match(b[k].attributes, ab[k].attributes));
        assert(ab[k] == a[k] && ac[k] == a[k]);
        lemma_attributes_match_transitive(c[k].attributes, b[k].attributes, a[k].attributes);
    }
}

/// An empty directoryName base holds every name.
pub proof fn lemma_directory_empty_base_holds_all(name: Seq<crate::name::spec::RelativeDistinguishedName>)
    ensures directory_within(name, seq![]),
{
    assert(name.subrange(0, 0).len() == 0);
}

} // verus!
