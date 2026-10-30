//! Public refinement contract for the executable name-constraint matcher:
//! one predicate per executable function, saying what it is proven to
//! satisfy, in terms of `spec.rs`. Each result equals the spec function it is
//! named after.
//!
//! The one place the executable code is allowed to do less than the spec is
//! the comparison bound of the path design (§1.12: at most 4,096 subjectAltName
//! entries times constraint subtrees per path, refuse beyond; `spec.rs`'s
//! header leaves it to the executable code). It is modelled **in this
//! contract only**: [`names_constrained_ensures`] says the executable result is
//! the spec's `names_constrained` *and* the path stays within the bound
//! ([`within_budget`]). So on a path within the bound the result equals the
//! spec's exactly, and a path beyond it is refused. Nothing in `spec.rs`
//! changes, and the bound can only make the executable code refuse more,
//! never accept what the spec refuses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Per-name checks
// ---------------------------------------------------------------------------

/// `dns_within`.
pub open spec fn dns_within_ensures(name: Seq<u8>, base: Seq<u8>, out: bool) -> bool {
    out == dns_within(name, base)
}

/// `dns_wildcard_within`.
pub open spec fn dns_wildcard_within_ensures(suffix: Seq<u8>, base: Seq<u8>, out: bool) -> bool {
    out == dns_wildcard_within(suffix, base)
}

/// `dns_wildcard_meets`.
pub open spec fn dns_wildcard_meets_ensures(suffix: Seq<u8>, base: Seq<u8>, out: bool) -> bool {
    out == dns_wildcard_meets(suffix, base)
}

/// `ip_within`.
pub open spec fn ip_within_ensures(address: Seq<u8>, base: Seq<u8>, mask: Seq<u8>, out: bool) -> bool {
    out == ip_within(address, base, mask)
}

/// `rfc822_within`.
pub open spec fn rfc822_within_ensures(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>, out: bool) -> bool {
    out == rfc822_within(local, host, base)
}

/// `rfc822_meets`.
pub open spec fn rfc822_meets_ensures(local: Seq<u8>, host: Seq<u8>, base: Seq<u8>, out: bool) -> bool {
    out == rfc822_meets(local, host, base)
}

/// `directory_within`.
pub open spec fn directory_within_ensures(
    name: Seq<crate::name::spec::RelativeDistinguishedName>,
    base: Seq<crate::name::spec::RelativeDistinguishedName>,
    out: bool,
) -> bool {
    out == directory_within(name, base)
}

/// `constrained_name`: the matched form of a subjectAltName entry.
pub open spec fn constrained_name_ensures(
    entry: crate::extensions::spec::GeneralName,
    out: Option<ConstrainedName>,
) -> bool {
    out == constrained_name(entry)
}

/// `within`: a name is within one subtree.
pub open spec fn within_ensures(
    name: ConstrainedName,
    base: crate::name_constraints::spec::GeneralNameConstraint,
    out: bool,
) -> bool {
    out == within(name, base)
}

/// `meets`: a name meets one subtree.
pub open spec fn meets_ensures(
    name: ConstrainedName,
    base: crate::name_constraints::spec::GeneralNameConstraint,
    out: bool,
) -> bool {
    out == meets(name, base)
}

/// `base_supported`: a subtree base is well formed.
pub open spec fn base_supported_ensures(
    base: crate::name_constraints::spec::GeneralNameConstraint,
    out: bool,
) -> bool {
    out == base_supported(base)
}

/// `constraints_supported`: a NameConstraints value this module can apply.
pub open spec fn constraints_supported_ensures(
    value: crate::name_constraints::spec::NameConstraints,
    out: bool,
) -> bool {
    out == constraints_supported(value)
}

// ---------------------------------------------------------------------------
// The state
// ---------------------------------------------------------------------------

/// `within_permitted_subtrees`: a matched name is within permitted_subtrees.
pub open spec fn within_permitted_subtrees_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
    out: bool,
) -> bool {
    out == within_permitted_subtrees(state, name)
}

/// `within_excluded_subtrees`: a matched name is within excluded_subtrees.
pub open spec fn within_excluded_subtrees_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
    out: bool,
) -> bool {
    out == within_excluded_subtrees(state, name)
}

/// `name_acceptable`.
pub open spec fn name_acceptable_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    name: ConstrainedName,
    out: bool,
) -> bool {
    out == name_acceptable(state, name)
}

/// §6.1.4 (g): `prepare_name_constraints`. `accepted` is whether the spec
/// returns `Some`; when it does, `next` is the state it returns.
pub open spec fn prepare_name_constraints_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    extension: Option<crate::name_constraints::spec::NameConstraints>,
    accepted: bool,
    next: Seq<crate::name_constraints::spec::NameConstraints>,
) -> bool {
    match prepare_name_constraints(state, extension) {
        Some(expected) => accepted && next == expected,
        None => !accepted,
    }
}

// ---------------------------------------------------------------------------
// One certificate
// ---------------------------------------------------------------------------

/// `names_well_formed`.
pub open spec fn names_well_formed_ensures(names: Seq<crate::extensions::spec::GeneralName>, out: bool) -> bool {
    out == names_well_formed(names)
}

/// `names_of_unconstrained_forms`.
pub open spec fn names_of_unconstrained_forms_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    out: bool,
) -> bool {
    out == names_of_unconstrained_forms(state, names)
}

/// `names_within_permitted`, §6.1.3 (b).
pub open spec fn names_within_permitted_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    out: bool,
) -> bool {
    out == names_within_permitted(state, names)
}

/// `names_not_excluded`, §6.1.3 (c).
pub open spec fn names_not_excluded_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    out: bool,
) -> bool {
    out == names_not_excluded(state, names)
}

/// `certificate_names_acceptable`.
pub open spec fn certificate_names_acceptable_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    names: Seq<crate::extensions::spec::GeneralName>,
    out: bool,
) -> bool {
    out == certificate_names_acceptable(state, names)
}

/// `subject_acceptable`: the subject field, given as the complete Name TLV.
pub open spec fn subject_acceptable_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    subject: Seq<u8>,
    out: bool,
) -> bool {
    out == subject_acceptable(state, subject)
}

/// `certificate_acceptable`: §6.1.3 (b) and (c) for one certificate.
pub open spec fn certificate_acceptable_ensures(
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    certificate: NcCertificate,
    out: bool,
) -> bool {
    out == certificate_acceptable(state, certificate)
}

// ---------------------------------------------------------------------------
// The comparison bound (design §1.12)
// ---------------------------------------------------------------------------

/// At most this many subjectAltName-entry by subtree comparisons per path.
pub open spec fn comparison_bound() -> nat {
    4096
}

/// The subtrees one NameConstraints value holds, in both lists.
pub open spec fn subtrees_in(value: crate::name_constraints::spec::NameConstraints) -> nat {
    (match value.permitted_subtrees { Some(items) => items.len(), None => 0 })
        + (match value.excluded_subtrees { Some(items) => items.len(), None => 0 })
}

/// The subtrees of every set in the state.
pub open spec fn subtree_count(state: Seq<crate::name_constraints::spec::NameConstraints>) -> nat
    decreases state.len()
{
    if state.len() == 0 { 0 } else { subtrees_in(state.last()) + subtree_count(state.drop_last()) }
}

/// The comparisons one certificate costs: every subjectAltName entry, and the
/// subject, against every subtree of the state.
pub open spec fn comparisons(entries: nat, subtrees: nat) -> nat {
    (entries + 1) * subtrees
}

/// Whether `spent` comparisons so far are within the bound.
pub open spec fn within_comparison_bound(spent: nat) -> bool {
    spent <= comparison_bound()
}

/// The comparisons certificate `certificate` costs under `state`.
pub open spec fn certificate_comparisons(state: Seq<crate::name_constraints::spec::NameConstraints>, certificate: NcCertificate) -> nat {
    comparisons(certificate.subject_alt_names.len(), subtree_count(state))
}

/// Every certificate of `path[i..]` stays within the bound, `spent` being
/// the comparisons of `path[..i]`, with the same state evolution as
/// `names_constrained_from`. Once a certificate's constraints are refused
/// the spec refuses the path, so what follows does not matter.
pub open spec fn within_budget_from(
    path: Seq<NcCertificate>,
    i: int,
    state: Seq<crate::name_constraints::spec::NameConstraints>,
    spent: nat,
) -> bool
    decreases path.len() - i
{
    if i < 0 || i >= path.len() {
        true
    } else {
        let certificate = path[i];
        let total = spent + certificate_comparisons(state, certificate);
        &&& within_comparison_bound(total)
        &&& i == path.len() - 1 || match prepare_name_constraints(state, certificate.name_constraints) {
            Some(next) => within_budget_from(path, i + 1, next, total),
            None => true,
        }
    }
}

/// The whole path stays within the bound.
pub open spec fn within_budget(path: Seq<NcCertificate>, initial: Seq<crate::name_constraints::spec::NameConstraints>) -> bool {
    within_budget_from(path, 0, initial, 0)
}

// ---------------------------------------------------------------------------
// The path
// ---------------------------------------------------------------------------

/// The executable path check accepts exactly the paths the spec's
/// `names_constrained` accepts that are within the comparison bound.
pub open spec fn names_constrained_ensures(
    path: Seq<NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
    out: bool,
) -> bool {
    out == (names_constrained(path, initial) && within_budget(path, initial))
}

/// On every path within the bound the executable result is the spec's, and
/// a path beyond it is refused: what [`names_constrained_ensures`] says,
/// stated both ways.
pub proof fn lemma_names_constrained_ensures_cases(
    path: Seq<NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
    out: bool,
)
    requires names_constrained_ensures(path, initial, out),
    ensures
        within_budget(path, initial) ==> out == names_constrained(path, initial),
        out ==> names_constrained(path, initial),
        !within_budget(path, initial) ==> !out,
{
}

/// `comparisons(100, 41)` is 4,141, beyond the bound: a certificate with 100
/// SAN entries under 41 subtrees is refused (limbo `pathological::nc-dos-*`
/// are of this kind).
pub proof fn lemma_over_bound_is_refused()
    ensures
        !within_comparison_bound(comparisons(100, 41)),
        within_comparison_bound(comparisons(63, 64)),
        !within_comparison_bound(comparisons(64, 64)),
{
}

/// `count` dNSName subtrees.
pub open spec fn many_subtrees(count: nat) -> Seq<crate::name_constraints::spec::GeneralSubtree> {
    Seq::new(count, |i: int| super::examples::dns_subtree(super::examples::example_com()))
}

/// `count` dNSName subjectAltName entries.
pub open spec fn many_entries(count: nat) -> Seq<crate::extensions::spec::GeneralName> {
    Seq::new(count, |i: int| super::examples::ip_entry(seq![127u8, 0, 0, 1]))
}

/// limbo's `pathological::nc-dos-*` shape: one set of 2,048 permitted and
/// 2,049 excluded subtrees.
pub open spec fn dos_state() -> Seq<crate::name_constraints::spec::NameConstraints> {
    seq![super::examples::constraints(Some(many_subtrees(2048)), Some(many_subtrees(2049)))]
}

/// A one-certificate path with `entries` iPAddress entries.
pub open spec fn one_certificate(entries: nat) -> Seq<NcCertificate> {
    seq![super::examples::certificate(many_entries(entries), None)]
}

/// `pathological::nc-dos-1` and `-2` (2,048 SAN entries) and `-3` (the
/// subject alone, no entry) are beyond the bound: each costs (entries + 1)
/// times 4,097 subtrees.
pub proof fn lemma_nc_dos_shapes_are_beyond_the_bound()
    ensures
        !within_budget(one_certificate(2048), dos_state()),
        !within_budget(one_certificate(0), dos_state()),
{
    assert(!within_budget(one_certificate(2048), dos_state())) by (compute_only);
    assert(!within_budget(one_certificate(0), dos_state())) by (compute_only);
}

/// A state of 32 permitted and 32 excluded subtrees: 64 in all.
pub open spec fn sixty_four_subtrees() -> Seq<crate::name_constraints::spec::NameConstraints> {
    seq![super::examples::constraints(Some(many_subtrees(32)), Some(many_subtrees(32)))]
}

/// The bound is exactly 4,096: 63 entries and the subject against 64
/// subtrees are within it and accepted, 64 entries are beyond it and
/// refused although the spec accepts them.
pub proof fn lemma_bound_is_exact()
    ensures
        within_budget(one_certificate(63), sixty_four_subtrees()),
        names_constrained_ensures(one_certificate(63), sixty_four_subtrees(), true),
        names_constrained(one_certificate(64), sixty_four_subtrees()),
        !within_budget(one_certificate(64), sixty_four_subtrees()),
        !names_constrained_ensures(one_certificate(64), sixty_four_subtrees(), true),
{
    assert(within_budget(one_certificate(63), sixty_four_subtrees())) by (compute_only);
    assert(names_constrained(one_certificate(63), sixty_four_subtrees())) by (compute_only);
    assert(names_constrained(one_certificate(64), sixty_four_subtrees())) by (compute_only);
    assert(!within_budget(one_certificate(64), sixty_four_subtrees())) by (compute_only);
}

/// Two certificates of 2,080 comparisons each: (31 entries + the subject)
/// against 65 subtrees. Together they are beyond the bound, though each is
/// within it.
pub proof fn lemma_bound_accumulates_over_certificates()
    ensures
        within_budget(one_certificate(31), seq![super::examples::constraints(Some(many_subtrees(65)), None)]),
        !within_budget(
            seq![
                super::examples::certificate(many_entries(31), None),
                super::examples::certificate(many_entries(31), None),
            ],
            seq![super::examples::constraints(Some(many_subtrees(65)), None)]),
{
    assert(within_budget(one_certificate(31), seq![super::examples::constraints(Some(many_subtrees(65)), None)]))
        by (compute_only);
    assert(!within_budget(
        seq![
            super::examples::certificate(many_entries(31), None),
            super::examples::certificate(many_entries(31), None),
        ],
        seq![super::examples::constraints(Some(many_subtrees(65)), None)])) by (compute_only);
}

/// Every set of the state is counted: two sets of 40 subtrees cost 80 per
/// entry, so 63 entries and the subject (5,120) are beyond the bound.
pub proof fn lemma_bound_counts_every_set()
    ensures
        !within_budget(
            one_certificate(63),
            seq![
                super::examples::constraints(Some(many_subtrees(40)), None),
                super::examples::constraints(Some(many_subtrees(40)), None),
            ]),
{
    assert(!within_budget(
        one_certificate(63),
        seq![
            super::examples::constraints(Some(many_subtrees(40)), None),
            super::examples::constraints(Some(many_subtrees(40)), None),
        ])) by (compute_only);
}

/// The bound only adds a refusal: a path the spec refuses is refused
/// within the bound too (`rfc5280::nc::permitted-self-issued`, where a
/// self-issued intermediate's name is outside the anchor's permitted
/// subtree).
pub proof fn lemma_bound_never_accepts_what_the_spec_refuses()
    ensures
        within_budget(
            seq![
                super::examples::certificate(seq![super::examples::dns_entry(super::examples::not_example_com())], None),
                super::examples::certificate(seq![super::examples::dns_entry(super::examples::example_com())], None),
            ],
            seq![super::examples::constraints(Some(seq![super::examples::dns_subtree(super::examples::example_com())]), None)]),
        !names_constrained_ensures(
            seq![
                super::examples::certificate(seq![super::examples::dns_entry(super::examples::not_example_com())], None),
                super::examples::certificate(seq![super::examples::dns_entry(super::examples::example_com())], None),
            ],
            seq![super::examples::constraints(Some(seq![super::examples::dns_subtree(super::examples::example_com())]), None)],
            true),
{
    assert(within_budget(
        seq![
            super::examples::certificate(seq![super::examples::dns_entry(super::examples::not_example_com())], None),
            super::examples::certificate(seq![super::examples::dns_entry(super::examples::example_com())], None),
        ],
        seq![super::examples::constraints(Some(seq![super::examples::dns_subtree(super::examples::example_com())]), None)]))
        by (compute_only);
    assert(!names_constrained_ensures(
        seq![
            super::examples::certificate(seq![super::examples::dns_entry(super::examples::not_example_com())], None),
            super::examples::certificate(seq![super::examples::dns_entry(super::examples::example_com())], None),
        ],
        seq![super::examples::constraints(Some(seq![super::examples::dns_subtree(super::examples::example_com())]), None)],
        true)) by (compute_only);
}

} // verus!
