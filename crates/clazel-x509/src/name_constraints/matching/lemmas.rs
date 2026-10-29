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
// One certificate: §6.1.3 (b), (c) and Q12
// ---------------------------------------------------------------------------

/// `names_of_matched_forms` is the universal statement it abbreviates.
pub proof fn lemma_matched_forms_all(names: Seq<crate::extensions::spec::GeneralName>)
    ensures
        names_of_matched_forms(names)
            == forall|i: int| 0 <= i < names.len() ==> (#[trigger] constrained_name(names[i])) is Some,
    decreases names.len()
{
    if names.len() > 0 {
        lemma_matched_forms_all(names.drop_last());
        if names_of_matched_forms(names) {
            assert forall|i: int| 0 <= i < names.len() implies
                (#[trigger] constrained_name(names[i])) is Some by {
                if i < names.len() - 1 {
                    assert(names.drop_last()[i] == names[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < names.len() ==> (#[trigger] constrained_name(names[i])) is Some {
            assert(constrained_name(names[names.len() - 1]) is Some);
            assert forall|i: int| 0 <= i < names.drop_last().len() implies
                (#[trigger] constrained_name(names.drop_last()[i])) is Some by {
                assert(names.drop_last()[i] == names[i]);
                assert(constrained_name(names[i]) is Some);
            }
        }
    }
}

/// Q12, names: under any constraint, an entry of an unmatched form
/// (directoryName, rfc822Name, URI, otherName, a malformed dNSName) fails the
/// certificate.
pub proof fn lemma_unmatched_name_refused(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    i: int,
)
    requires state.len() > 0, 0 <= i < names.len(), constrained_name(names[i]) is None,
    ensures !certificate_names_acceptable(state, names),
{
    lemma_matched_forms_all(names);
}

/// Q12, constraints: an unsupported NameConstraints value refuses the path
/// at §6.1.4 (g), whatever the state.
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
        (path[i].self_issued && i < path.len() - 1)
            || certificate_names_acceptable(state_before(path, i, initial).unwrap(), path[i].subject_alt_names),
    decreases i - j
{
    if j < i {
        let next = prepare_name_constraints(state, path[j].name_constraints).unwrap();
        assert(state_before(path, j + 1, initial) == prepare_name_constraints(state, path[j].name_constraints));
        lemma_names_constrained_from_at(path, initial, j + 1, i, next);
    }
}

/// `thm_names_constrained`'s per-certificate fact: on an accepted path,
/// every certificate except a self-issued one that is not final satisfies
/// §6.1.3 (b) and (c) under the state built from the initial state and
/// every earlier certificate's constraints.
pub proof fn lemma_names_constrained_at(
    path: Seq<NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
    i: int,
)
    requires names_constrained(path, initial), 0 <= i < path.len(),
    ensures
        state_before(path, i, initial) == Some(initial + collected_constraints(path, i)),
        (path[i].self_issued && i < path.len() - 1)
            || certificate_names_acceptable(initial + collected_constraints(path, i), path[i].subject_alt_names),
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

/// For a DNS name or an address, `meets` is `within`; only a wildcard
/// tells them apart.
pub proof fn lemma_meets_is_within_except_wildcards(
    name: ConstrainedName,
    base: crate::name_constraints::spec::GeneralNameConstraint,
)
    requires !(name is DnsWildcard),
    ensures meets(name, base) == within(name, base),
{
}

} // verus!
