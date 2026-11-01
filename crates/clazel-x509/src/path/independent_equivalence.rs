//! The independent transcription of ITU-T X.509 (10/2019) §12
//! (`independent.rs`, written by a separate agent without reading
//! `spec.rs`) **proven equal** to the RFC 5280 §6.1 transcription
//! (`spec::process`) on a stated domain: `theorem_independent_equivalence`.
//!
//! The two are compared with the same signature oracle: X.509's
//! `signature_verifies(cert, key)` is `oracle(link)`, "the algorithm is one
//! `spec.rs` supports and `link` holds of the SignedData under `key`" (an
//! unsupported algorithm cannot be verified, so folding `spec.rs`'s (R)
//! refusal into the oracle changes no verdict of `spec.rs`). X.509's inputs
//! are the browser's (`browser_inputs`): no initial name constraints, no
//! required name forms, `initial-explicit-policy` false. `spec::process` is
//! §6.1 only; `profile.rs`'s checks are not part of either side.
//!
//! The order of the path. Both process the certificate the trust anchor
//! signed first (X.509 §12.5: "starting with the public-key certificate
//! signed using the trust anchor public key"; RFC 5280 certificate 1), so
//! `path[i]` is the same certificate on both sides and no reversal is
//! needed.
//!
//! What agrees without narrowing (proven, not assumed):
//! - **pathLenConstraint.** X.509 counts, for each CA certificate, the
//!   non-self-issued certificates below it other than the end entity
//!   (`non_self_issued_count`); RFC 5280 decrements `max_path_length` for
//!   each non-self-issued intermediate. They agree: from certificate i the
//!   RFC run succeeds iff X.509's does and `max_path_length` is at least the
//!   non-self-issued intermediates from i on (`lemma_process_from`). The
//!   anchor's pathLenConstraint (RFC 5937 bullet 8; X.509 choice 8) agrees
//!   the same way.
//! - **dNSName and iPAddress "within"**, which X.509 does not define: the
//!   transcription's `dns_within` and `ip_within` are P4's for a dNSName in
//!   preferred name syntax and any address (`lemma_dns_within`,
//!   `lemma_ip_within`), and the intersection-of-sets and union readings of
//!   permitted and excluded subtrees agree (`lemma_x_permitted`,
//!   `lemma_x_excluded` against P4's denotation).
//! - **The anchor's validity and `server_distrust_after`** are not in
//!   `spec::process` either (they are `profile.rs`'s), so they do not differ.
//!
//! The domain (`equivalence_domain`, with `independent::profile_domain`).
//! Each condition excludes a real disagreement; outside it the verdicts can
//! differ, and nothing here claims they agree there.
//! 1. **No self-signed intermediate** (under `oracle(link)`). X.509 §12.5.1
//!    ignores self-signed certificates in the path, so the next certificate
//!    is verified under the key before them and the ignored one is not
//!    checked at all; RFC 5280 processes every certificate. The end entity is
//!    never ignored on either side (docs/ERRATA.md, "X.509 §12.5 ignores
//!    self-signed certificates, including the end entity").
//! 2. **No certificate appears twice** (RFC 5280 §6.1, `spec.rs`'s
//!    `certificates_distinct_from`); X.509 §12 has no such rule.
//! 3. **No requireExplicitPolicy.** `spec.rs` keeps no policy tree and so
//!    refuses when explicit_policy reaches 0 (its (R)); the transcription
//!    keeps no policy table and accepts (its restriction 1). Both are
//!    policy-free approximations that differ exactly where an explicit policy
//!    is required.
//! 4. **Nothing is revoked** (the production `revoked`; X.509 choice 15 has
//!    no revocation input).
//! 5. **Calendar-valid times**: `now` and each certificate's notBefore and
//!    notAfter. RFC 5280's `validity_contains` asks it; X.509 compares the
//!    fields. The time decoder produces only valid ones.
//! 6. **Intermediates' keyUsage, if present, has keyCertSign** (§6.1.4 (n)),
//!    and **every critical extension is one `spec.rs` recognizes** (§6.1.4
//!    (o), §6.1.5 (f)). X.509 §12 checks neither (choice 16).
//! 7. **Every NameConstraints is one P4 supports**: in the anchor and the
//!    intermediates, `constraints_supported` (a field present, well-formed
//!    bases). P4 refuses the rest (its (R) malformed bases).
//! 8. **Names under a constraint.** Once any NameConstraints is in force
//!    (`nc_before`), each certificate's subject decodes as a Name, its
//!    subjectAltName entries are well formed, its dNSNames are in preferred
//!    name syntax (**no wildcards**), and a self-issued intermediate has no
//!    subjectAltName. These are P4's (R) refusals (malformed names), the
//!    wildcard rule X.509 lacks (the transcription reads `*.example.com` as a
//!    literal name, so an excluded `bar.example.com` does not catch it, where
//!    P4 does: CVE-2025-61727), and the self-issued intermediate that X.509
//!    §12.5.1 g) (like RFC 5280 §6.1.3 (b)) skips and P4 checks (its (R),
//!    following Firefox). With no constraint in force none of this is asked,
//!    so wildcard leaves of unconstrained paths are inside the domain.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The common inputs.
// ---------------------------------------------------------------------

/// X.509's signature check, from `spec.rs`'s `link`: the algorithm is
/// supported and the signature verifies under `key`.
pub open spec fn oracle(link: super::spec::LinkFn) -> spec_fn(super::parsed::spec::PathCert, Seq<u8>) -> bool {
    |c: super::parsed::spec::PathCert, key: Seq<u8>|
        !(c.signature.class is Unsupported) && link(super::spec::signed_data(key, c))
}

/// The browser's §12.1 inputs: nothing beyond the anchor constrains names,
/// no name forms are required, and `initial-explicit-policy` is false.
pub open spec fn browser_inputs(now: crate::time::spec::CertificateTime) -> super::independent::PathInputs {
    super::independent::PathInputs {
        initial_explicit_policy: false,
        now,
        initial_permitted_subtrees: None,
        initial_excluded_subtrees: seq![],
        initial_required_name_forms: seq![],
    }
}

// ---------------------------------------------------------------------
// The domain.
// ---------------------------------------------------------------------

/// A NameConstraints is in force at `path[i]`: the anchor's, or that of a
/// certificate before it.
pub open spec fn nc_before(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
) -> bool {
    anchor.name_constraints is Some
        || exists|j: int| 0 <= j < i && (#[trigger] path[j]).name_constraints is Some
}

/// A subjectAltName entry P4 matches as X.509 does: a dNSName in preferred
/// name syntax (no wildcard), or a well-formed entry of another form.
pub open spec fn plain_entry(g: crate::extensions::spec::GeneralName) -> bool {
    match g {
        crate::extensions::spec::GeneralName::DnsName(d) => crate::spec::dns_name_shape(d),
        _ => crate::name_constraints::matching::spec::entry_well_formed(g),
    }
}

/// Domain condition 8 for one certificate.
pub open spec fn names_plain(c: super::parsed::spec::PathCert) -> bool {
    let sans = super::spec::nc_certificate(c).subject_alt_names;
    &&& crate::name::spec::parse_name(c.tbs.subject_der) is Some
    &&& forall|m: int| 0 <= m < sans.len() ==> plain_entry(#[trigger] sans[m])
}

/// A NameConstraints that P4 supports, if present (domain condition 7).
pub open spec fn nc_supported(nc: Option<crate::name_constraints::spec::NameConstraints>) -> bool {
    match nc {
        Some(v) => crate::name_constraints::matching::spec::constraints_supported(v),
        None => true,
    }
}

/// The domain conditions on `path[i]`.
pub open spec fn cert_in_equivalence_domain(
    link: super::spec::LinkFn, revoked: super::spec::RevokedFn,
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
) -> bool {
    let c = path[i];
    let intermediate = i < path.len() - 1;
    // 3, 4, 5.
    &&& c.require_explicit_policy is None
    &&& !revoked(c)
    &&& crate::time::spec::calendar_time_valid(c.tbs.not_before)
    &&& crate::time::spec::calendar_time_valid(c.tbs.not_after)
    // 1, 6, 7 for an intermediate.
    &&& intermediate ==> {
        &&& !super::independent::is_self_signed(oracle(link), c)
        &&& match c.key_usage {
            Some(usage) => crate::constraints::spec::key_usage_has(
                usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
            None => true,
        }
        &&& super::spec::intermediate_critical_supported(c.extensions, 0)
        &&& nc_supported(c.name_constraints)
    }
    // 6 for the end entity.
    &&& !intermediate ==> crate::leaf::spec::supported_critical_extensions(c.extensions, 0)
    // 8.
    &&& nc_before(anchor, path, i) ==> names_plain(c)
    &&& (nc_before(anchor, path, i) && intermediate && super::spec::self_issued(c)) ==> c.san is None
}

/// The domain of `theorem_independent_equivalence`, beyond
/// `independent::profile_domain`.
pub open spec fn equivalence_domain(
    link: super::spec::LinkFn, revoked: super::spec::RevokedFn,
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>,
    now: crate::time::spec::CertificateTime,
) -> bool {
    &&& crate::time::spec::calendar_time_valid(now)
    &&& super::spec::certificates_distinct_from(path, 0)
    &&& nc_supported(anchor.name_constraints)
    &&& forall|i: int| 0 <= i < path.len() ==> cert_in_equivalence_domain(link, revoked, anchor, path, i)
}

// ---------------------------------------------------------------------
// The name-constraint state: X.509's lists from P4's sequence.
// ---------------------------------------------------------------------

/// X.509's permitted-subtrees for P4's state: the permittedSubtrees of each
/// set that has one, in order.
pub open spec fn perm_of(st: Seq<crate::name_constraints::spec::NameConstraints>)
    -> Seq<Seq<crate::name_constraints::spec::GeneralSubtree>>
    decreases st.len()
{
    if st.len() == 0 { seq![] }
    else {
        let rest = perm_of(st.drop_last());
        match st.last().permitted_subtrees { Some(s) => rest.push(s), None => rest }
    }
}

/// X.509's excluded-subtrees for P4's state: every excludedSubtrees,
/// concatenated.
pub open spec fn excl_of(st: Seq<crate::name_constraints::spec::NameConstraints>)
    -> Seq<crate::name_constraints::spec::GeneralSubtree>
    decreases st.len()
{
    if st.len() == 0 { seq![] }
    else {
        let rest = excl_of(st.drop_last());
        match st.last().excluded_subtrees { Some(s) => rest + s, None => rest }
    }
}

/// A dNSName or iPAddress base.
pub open spec fn dns_ip_base(b: crate::name_constraints::spec::GeneralNameConstraint) -> bool {
    b is DnsName || b is IpAddress
}

/// Every base is a dNSName or an iPAddress.
pub open spec fn items_dns_ip(items: Seq<crate::name_constraints::spec::GeneralSubtree>) -> bool {
    forall|k: int| 0 <= k < items.len() ==> dns_ip_base((#[trigger] items[k]).base)
}

/// Every base of the NameConstraints is a dNSName or an iPAddress.
pub open spec fn nc_dns_ip(v: crate::name_constraints::spec::NameConstraints) -> bool {
    &&& match v.permitted_subtrees { Some(s) => items_dns_ip(s), None => true }
    &&& match v.excluded_subtrees { Some(s) => items_dns_ip(s), None => true }
}

/// Every base in the state is a dNSName or an iPAddress.
pub open spec fn state_dns_ip(st: Seq<crate::name_constraints::spec::NameConstraints>) -> bool {
    forall|j: int| 0 <= j < st.len() ==> nc_dns_ip(#[trigger] st[j])
}

/// X.509's subject name for a subjectAltName entry (`independent::san_names`).
pub open spec fn x_of(g: crate::extensions::spec::GeneralName) -> super::independent::SubjectName {
    match g {
        crate::extensions::spec::GeneralName::DnsName(d) => super::independent::SubjectName::Dns(d),
        crate::extensions::spec::GeneralName::IpAddress(a) => super::independent::SubjectName::Ip(a),
        crate::extensions::spec::GeneralName::Other(tag, _) => super::independent::SubjectName::Other(tag),
    }
}

/// X.509's §12.5.1 g) for one name.
pub open spec fn x_name_ok(x: super::independent::PathState, n: super::independent::SubjectName) -> bool {
    super::independent::within_permitted(x.permitted_subtrees, n, 0)
        && !super::independent::within_some(x.excluded_subtrees, n, 0)
}

/// One permitted set of X.509's list admits the name.
pub open spec fn x_set_ok(
    s: Seq<crate::name_constraints::spec::GeneralSubtree>, n: super::independent::SubjectName,
) -> bool {
    !super::independent::set_constrains_form(s, n, 0) || super::independent::within_some(s, n, 0)
}

/// One NameConstraints admits the name, in X.509's reading.
pub open spec fn x_nc_ok(v: crate::name_constraints::spec::NameConstraints, n: super::independent::SubjectName) -> bool {
    match v.permitted_subtrees { Some(s) => x_set_ok(s, n), None => true }
}

/// P4's §6.1.3 (b) for one subjectAltName entry.
pub open spec fn p4_entry_permitted(
    st: Seq<crate::name_constraints::spec::NameConstraints>, g: crate::extensions::spec::GeneralName,
) -> bool {
    match crate::name_constraints::matching::spec::constrained_name(g) {
        Some(cn) => crate::name_constraints::matching::spec::within_permitted_subtrees(st, cn),
        None => true,
    }
}

/// P4's §6.1.3 (c) for one subjectAltName entry.
pub open spec fn p4_entry_not_excluded(
    st: Seq<crate::name_constraints::spec::NameConstraints>, g: crate::extensions::spec::GeneralName,
) -> bool {
    match crate::name_constraints::matching::spec::constrained_name(g) {
        Some(cn) => !crate::name_constraints::matching::spec::within_excluded_subtrees(st, cn),
        None => true,
    }
}

/// P4's uninterpreted-form check for one subjectAltName entry.
pub open spec fn p4_entry_form_ok(
    st: Seq<crate::name_constraints::spec::NameConstraints>, g: crate::extensions::spec::GeneralName,
) -> bool {
    match g {
        crate::extensions::spec::GeneralName::Other(tag, _) =>
            !crate::name_constraints::matching::spec::is_uninterpreted_form(tag)
                || !crate::name_constraints::matching::spec::form_constrained(st, tag),
        _ => true,
    }
}

/// P4's checks of one subjectAltName entry.
pub open spec fn p4_entry_ok(
    st: Seq<crate::name_constraints::spec::NameConstraints>, g: crate::extensions::spec::GeneralName,
) -> bool {
    p4_entry_permitted(st, g) && p4_entry_not_excluded(st, g) && p4_entry_form_ok(st, g)
}

// ---------------------------------------------------------------------
// Small facts: times, integers, the ignored certificates, counts.
// ---------------------------------------------------------------------

/// The two orders on times are the same, and RFC 5280's validity test is
/// X.509's on calendar-valid times.
pub proof fn lemma_validity(c: super::parsed::spec::PathCert, now: crate::time::spec::CertificateTime)
    requires
        crate::time::spec::calendar_time_valid(now),
        crate::time::spec::calendar_time_valid(c.tbs.not_before),
        crate::time::spec::calendar_time_valid(c.tbs.not_after),
    ensures
        crate::time::spec::validity_contains(super::spec::validity(c), now)
            == (super::independent::time_le(c.tbs.not_before, now)
                && super::independent::time_le(now, c.tbs.not_after)),
{
}

/// `independent::magnitude` is `be_value`.
pub proof fn lemma_magnitude(octets: Seq<u8>)
    ensures super::independent::magnitude(octets) == super::parsed::spec::skip_certs_value(octets),
    decreases octets.len()
{
    if octets.len() > 0 {
        lemma_magnitude(octets.drop_last());
    }
}

/// With no self-signed certificate before the last, nothing is dropped.
pub proof fn lemma_drop_ignored(
    sig: spec_fn(super::parsed::spec::PathCert, Seq<u8>) -> bool,
    path: Seq<super::parsed::spec::PathCert>, i: int,
)
    requires
        0 <= i <= path.len(),
        forall|k: int| 0 <= k < path.len() - 1 ==> !super::independent::is_self_signed(sig, #[trigger] path[k]),
    ensures super::independent::drop_ignored(sig, path, i) == path.subrange(i, path.len() as int),
    decreases path.len() - i
{
    if i < path.len() {
        lemma_drop_ignored(sig, path, i + 1);
        assert(seq![path[i]].add(path.subrange(i + 1, path.len() as int)) =~= path.subrange(i, path.len() as int));
    } else {
        assert(path.subrange(i, path.len() as int) =~= Seq::<super::parsed::spec::PathCert>::empty());
    }
}

/// At most one certificate counted per position.
pub proof fn lemma_count_bound(path: Seq<super::parsed::spec::PathCert>, from: int, to: int)
    requires from <= to,
    ensures super::independent::non_self_issued_count(path, from, to) <= to - from,
    decreases to - from
{
    if from < to {
        lemma_count_bound(path, from + 1, to);
    }
}

/// `independent::path_in_domain` at each index.
pub proof fn lemma_path_in_domain(path: Seq<super::parsed::spec::PathCert>, i: int, k: int)
    requires 0 <= i <= k < path.len(), super::independent::path_in_domain(path, i),
    ensures super::independent::cert_in_domain(path[k]),
    decreases k - i
{
    if i < k {
        lemma_path_in_domain(path, i + 1, k);
    }
}

/// `independent::supported_subtrees` gives dNSName and iPAddress bases.
pub proof fn lemma_supported_subtrees(s: Seq<crate::name_constraints::spec::GeneralSubtree>, i: int)
    requires 0 <= i <= s.len(), super::independent::supported_subtrees(s, i),
    ensures forall|k: int| i <= k < s.len() ==> dns_ip_base((#[trigger] s[k]).base),
    decreases s.len() - i
{
    if i < s.len() {
        lemma_supported_subtrees(s, i + 1);
    }
}

/// `independent::supported_name_constraints` gives `nc_dns_ip`.
pub proof fn lemma_supported_nc(nc: Option<crate::name_constraints::spec::NameConstraints>)
    requires super::independent::supported_name_constraints(nc),
    ensures match nc { Some(v) => nc_dns_ip(v), None => true },
{
    if let Some(v) = nc {
        if let Some(s) = v.permitted_subtrees { lemma_supported_subtrees(s, 0); }
        if let Some(s) = v.excluded_subtrees { lemma_supported_subtrees(s, 0); }
    }
}

// ---------------------------------------------------------------------
// Matching one name against one base.
// ---------------------------------------------------------------------

/// The two ASCII case foldings agree.
pub proof fn lemma_fold_byte(x: u8, y: u8)
    ensures
        (super::independent::ascii_lower(x) == super::independent::ascii_lower(y))
            == (crate::spec::ascii_fold(x) == crate::spec::ascii_fold(y)),
{
    assert(0x41u8 <= x && x <= 0x5Au8 ==> (x | 0x20u8) == (x + 0x20u8) as u8) by (bit_vector);
    assert(0x41u8 <= y && y <= 0x5Au8 ==> (y | 0x20u8) == (y + 0x20u8) as u8) by (bit_vector);
}

/// `ci_equal_from` is `folded_equal_from` on equal lengths.
pub proof fn lemma_ci_folded(a: Seq<u8>, b: Seq<u8>, i: int)
    requires a.len() == b.len(), 0 <= i <= a.len(),
    ensures super::independent::ci_equal_from(a, b, i) == crate::spec::folded_equal_from(a, b, i),
    decreases a.len() - i
{
    if i < a.len() {
        lemma_fold_byte(a[i], b[i]);
        lemma_ci_folded(a, b, i + 1);
    }
}

/// X.509's `dns_within` is P4's.
pub proof fn lemma_dns_within(name: Seq<u8>, base: Seq<u8>)
    ensures
        super::independent::dns_within(name, base)
            == crate::name_constraints::matching::spec::dns_within(name, base),
{
    if base.len() > 0 && name.len() >= base.len() {
        let tail = name.subrange(name.len() - base.len(), name.len() as int);
        lemma_ci_folded(tail, base, 0);
        if name.len() == base.len() {
            assert(tail =~= name);
        }
    }
}

/// The two masked comparisons agree on equal lengths.
pub proof fn lemma_masked(a: Seq<u8>, b: Seq<u8>, mask: Seq<u8>, i: int)
    requires a.len() == b.len(), b.len() == mask.len(), 0 <= i <= a.len(),
    ensures
        super::independent::masked_equal_from(a, b, mask, i)
            == crate::name_constraints::matching::spec::ip_masked_equal_from(a, b, mask, i),
    decreases a.len() - i
{
    if i < a.len() {
        lemma_masked(a, b, mask, i + 1);
    }
}

/// X.509's `ip_within` is P4's.
pub proof fn lemma_ip_within(name: Seq<u8>, address: Seq<u8>, mask: Seq<u8>)
    ensures
        super::independent::ip_within(name, address, mask)
            == crate::name_constraints::matching::spec::ip_within(name, address, mask),
{
    if name.len() == address.len() && mask.len() == address.len() {
        lemma_masked(name, address, mask, 0);
    }
}

/// A plain dNSName or iPAddress entry: its X.509 name and its P4 name agree
/// on every base.
pub proof fn lemma_base(g: crate::extensions::spec::GeneralName, s: crate::name_constraints::spec::GeneralSubtree)
    requires
        crate::name_constraints::matching::spec::constrained_name(g) is Some,
        g is DnsName || g is IpAddress,
        g is DnsName ==> crate::spec::dns_name_shape(g->DnsName_0),
    ensures ({
        let cn = crate::name_constraints::matching::spec::constrained_name(g)->Some_0;
        &&& super::independent::subtree_has_form_of(s, x_of(g))
            == crate::name_constraints::matching::spec::same_name_type(cn, s.base)
        &&& super::independent::within_subtree(x_of(g), s)
            == crate::name_constraints::matching::spec::within(cn, s.base)
        &&& crate::name_constraints::matching::spec::meets(cn, s.base)
            == crate::name_constraints::matching::spec::within(cn, s.base)
        &&& cn is Dns || cn is Ip
    }),
{
    match g {
        crate::extensions::spec::GeneralName::DnsName(d) => {
            if let crate::name_constraints::spec::GeneralNameConstraint::DnsName(b) = s.base {
                lemma_dns_within(d, b);
            }
        },
        crate::extensions::spec::GeneralName::IpAddress(a) => {
            if let crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask } = s.base {
                lemma_ip_within(a, address, mask);
            }
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// X.509's recursions as quantifiers.
// ---------------------------------------------------------------------

/// `set_constrains_form` is "some subtree from `i` has the form".
pub proof fn lemma_x_constrains(
    set: Seq<crate::name_constraints::spec::GeneralSubtree>, n: super::independent::SubjectName, i: int,
)
    requires 0 <= i <= set.len(),
    ensures
        super::independent::set_constrains_form(set, n, i)
            == exists|k: int| i <= k < set.len() && super::independent::subtree_has_form_of(#[trigger] set[k], n),
    decreases set.len() - i
{
    if i < set.len() {
        lemma_x_constrains(set, n, i + 1);
        if super::independent::subtree_has_form_of(set[i], n) {
            assert(i <= i < set.len() && super::independent::subtree_has_form_of(set[i], n));
        }
    }
}

/// X.509's `within_some` is "some subtree from `i` holds the name".
pub proof fn lemma_x_within_some(
    set: Seq<crate::name_constraints::spec::GeneralSubtree>, n: super::independent::SubjectName, i: int,
)
    requires 0 <= i <= set.len(),
    ensures
        super::independent::within_some(set, n, i)
            == exists|k: int| i <= k < set.len() && super::independent::within_subtree(n, #[trigger] set[k]),
    decreases set.len() - i
{
    if i < set.len() {
        lemma_x_within_some(set, n, i + 1);
        if super::independent::within_subtree(n, set[i]) {
            assert(i <= i < set.len() && super::independent::within_subtree(n, set[i]));
        }
    }
}

/// `within_permitted` is "every set from `j` admits the name".
pub proof fn lemma_x_within_permitted(
    p: Seq<Seq<crate::name_constraints::spec::GeneralSubtree>>, n: super::independent::SubjectName, j: int,
)
    requires 0 <= j <= p.len(),
    ensures
        super::independent::within_permitted(p, n, j)
            == forall|k: int| j <= k < p.len() ==> x_set_ok(#[trigger] p[k], n),
    decreases p.len() - j
{
    if j < p.len() {
        lemma_x_within_permitted(p, n, j + 1);
    }
}

/// `name_space_failure` finds nothing iff every name from `k` is fine.
pub proof fn lemma_x_name_space(
    x: super::independent::PathState, names: Seq<super::independent::SubjectName>, k: int,
)
    requires 0 <= k <= names.len(),
    ensures
        (super::independent::name_space_failure(x, names, k) is None)
            == forall|m: int| k <= m < names.len() ==> x_name_ok(x, #[trigger] names[m]),
    decreases names.len() - k
{
    if k < names.len() {
        lemma_x_name_space(x, names, k + 1);
    }
}

/// `san_names` is `x_of`, entry by entry.
pub proof fn lemma_san_names(names: Seq<crate::extensions::spec::GeneralName>, i: int)
    requires 0 <= i <= names.len(),
    ensures
        super::independent::san_names(names, i).len() == names.len() - i,
        forall|k: int| 0 <= k < names.len() - i
            ==> (#[trigger] super::independent::san_names(names, i)[k]) == x_of(names[i + k]),
    decreases names.len() - i
{
    if i < names.len() {
        lemma_san_names(names, i + 1);
    }
}

/// A directory or other-form name passes X.509's checks.
pub proof fn lemma_x_other_ok(x: super::independent::PathState, n: super::independent::SubjectName)
    requires n is Directory || n is Other,
    ensures x_name_ok(x, n),
{
    lemma_x_within_permitted(x.permitted_subtrees, n, 0);
    assert forall|k: int| 0 <= k < x.permitted_subtrees.len() implies x_set_ok(#[trigger] x.permitted_subtrees[k], n) by {
        lemma_x_constrains(x.permitted_subtrees[k], n, 0);
    }
    lemma_x_within_some(x.excluded_subtrees, n, 0);
}

/// X.509's permitted check over `perm_of(st)` is "every set's".
pub proof fn lemma_x_permitted(
    st: Seq<crate::name_constraints::spec::NameConstraints>, n: super::independent::SubjectName,
)
    ensures
        super::independent::within_permitted(perm_of(st), n, 0)
            == forall|j: int| 0 <= j < st.len() ==> x_nc_ok(#[trigger] st[j], n),
    decreases st.len()
{
    let p = perm_of(st);
    lemma_x_within_permitted(p, n, 0);
    if st.len() > 0 {
        let rest = st.drop_last();
        let a = perm_of(rest);
        lemma_x_permitted(rest, n);
        lemma_x_within_permitted(a, n, 0);
        let last = st.last();
        assert(st[st.len() - 1] == last);
        // Over the state: the rest, then the last set.
        if forall|j: int| 0 <= j < st.len() ==> x_nc_ok(#[trigger] st[j], n) {
            assert forall|j: int| 0 <= j < rest.len() implies x_nc_ok(#[trigger] rest[j], n) by {
                assert(rest[j] == st[j]);
            }
        }
        if (forall|j: int| 0 <= j < rest.len() ==> x_nc_ok(#[trigger] rest[j], n)) && x_nc_ok(last, n) {
            assert forall|j: int| 0 <= j < st.len() implies x_nc_ok(#[trigger] st[j], n) by {
                if j < rest.len() { assert(rest[j] == st[j]); }
            }
        }
        // Over X.509's list: the same.
        match last.permitted_subtrees {
            Some(s) => {
                assert(p == a.push(s));
                if forall|k: int| 0 <= k < p.len() ==> x_set_ok(#[trigger] p[k], n) {
                    assert forall|k: int| 0 <= k < a.len() implies x_set_ok(#[trigger] a[k], n) by {
                        assert(p[k] == a[k]);
                    }
                    assert(p[a.len() as int] == s);
                }
                if (forall|k: int| 0 <= k < a.len() ==> x_set_ok(#[trigger] a[k], n)) && x_set_ok(s, n) {
                    assert forall|k: int| 0 <= k < p.len() implies x_set_ok(#[trigger] p[k], n) by {
                        if k < a.len() { assert(p[k] == a[k]); } else { assert(p[k] == s); }
                    }
                }
            },
            None => { assert(p == a); },
        }
    }
}

/// X.509's excluded check over `excl_of(st)` is "some set's".
pub proof fn lemma_x_excluded(
    st: Seq<crate::name_constraints::spec::NameConstraints>, n: super::independent::SubjectName,
)
    ensures
        super::independent::within_some(excl_of(st), n, 0)
            == exists|j: int| 0 <= j < st.len() && match (#[trigger] st[j]).excluded_subtrees {
                Some(s) => super::independent::within_some(s, n, 0),
                None => false,
            },
    decreases st.len()
{
    if st.len() > 0 {
        let rest = st.drop_last();
        lemma_x_excluded(rest, n);
        assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] == st[j] by {}
        let a = excl_of(rest);
        lemma_x_within_some(a, n, 0);
        match st.last().excluded_subtrees {
            Some(s) => {
                let c = a + s;
                assert(excl_of(st) == c);
                lemma_x_within_some(c, n, 0);
                lemma_x_within_some(s, n, 0);
                if super::independent::within_some(c, n, 0) {
                    let k = choose|k: int| 0 <= k < c.len() && super::independent::within_subtree(n, #[trigger] c[k]);
                    if k >= a.len() {
                        assert(super::independent::within_subtree(n, s[k - a.len()]));
                        assert(st[st.len() - 1] == st.last());
                    }
                }
                if super::independent::within_some(a, n, 0) {
                    let k = choose|k: int| 0 <= k < a.len() && super::independent::within_subtree(n, #[trigger] a[k]);
                    assert(c[k] == a[k]);
                }
                if super::independent::within_some(s, n, 0) {
                    let k = choose|k: int| 0 <= k < s.len() && super::independent::within_subtree(n, #[trigger] s[k]);
                    assert(c[k + a.len()] == s[k]);
                }
                if exists|j: int| 0 <= j < st.len() && match (#[trigger] st[j]).excluded_subtrees {
                    Some(s) => super::independent::within_some(s, n, 0),
                    None => false,
                } {
                    let j = choose|j: int| 0 <= j < st.len() && match (#[trigger] st[j]).excluded_subtrees {
                        Some(s) => super::independent::within_some(s, n, 0),
                        None => false,
                    };
                    if j < rest.len() {
                        assert(rest[j] == st[j]);
                    }
                }
            },
            None => {
                if exists|j: int| 0 <= j < st.len() && match (#[trigger] st[j]).excluded_subtrees {
                    Some(s) => super::independent::within_some(s, n, 0),
                    None => false,
                } {
                    let j = choose|j: int| 0 <= j < st.len() && match (#[trigger] st[j]).excluded_subtrees {
                        Some(s) => super::independent::within_some(s, n, 0),
                        None => false,
                    };
                    assert(j < rest.len());
                    assert(rest[j] == st[j]);
                }
            },
        }
    } else {
        assert(excl_of(st) =~= Seq::<crate::name_constraints::spec::GeneralSubtree>::empty());
    }
}

// ---------------------------------------------------------------------
// P4's recursions as quantifiers.
// ---------------------------------------------------------------------

/// `has_base_of_type` is "some base has the type".
pub proof fn lemma_p4_has_base(
    items: Seq<crate::name_constraints::spec::GeneralSubtree>,
    cn: crate::name_constraints::matching::spec::ConstrainedName,
)
    ensures
        crate::name_constraints::matching::spec::has_base_of_type(items, cn)
            == exists|k: int| 0 <= k < items.len()
                && crate::name_constraints::matching::spec::same_name_type(cn, (#[trigger] items[k]).base),
    decreases items.len()
{
    if items.len() > 0 {
        let rest = items.drop_last();
        lemma_p4_has_base(rest, cn);
        assert forall|k: int| 0 <= k < rest.len() implies #[trigger] rest[k] == items[k] by {}
        if crate::name_constraints::matching::spec::same_name_type(cn, items.last().base) {
            assert(items[items.len() - 1] == items.last());
        }
        if exists|k: int| 0 <= k < items.len()
            && crate::name_constraints::matching::spec::same_name_type(cn, (#[trigger] items[k]).base) {
            let k = choose|k: int| 0 <= k < items.len()
                && crate::name_constraints::matching::spec::same_name_type(cn, (#[trigger] items[k]).base);
            if k < rest.len() { assert(rest[k] == items[k]); }
        }
    }
}

/// P4's `within_some` is "some base holds the name".
pub proof fn lemma_p4_within_some(
    items: Seq<crate::name_constraints::spec::GeneralSubtree>,
    cn: crate::name_constraints::matching::spec::ConstrainedName,
)
    ensures
        crate::name_constraints::matching::spec::within_some(items, cn)
            == exists|k: int| 0 <= k < items.len()
                && crate::name_constraints::matching::spec::within(cn, (#[trigger] items[k]).base),
    decreases items.len()
{
    if items.len() > 0 {
        let rest = items.drop_last();
        lemma_p4_within_some(rest, cn);
        assert forall|k: int| 0 <= k < rest.len() implies #[trigger] rest[k] == items[k] by {}
        if crate::name_constraints::matching::spec::within(cn, items.last().base) {
            assert(items[items.len() - 1] == items.last());
        }
        if exists|k: int| 0 <= k < items.len()
            && crate::name_constraints::matching::spec::within(cn, (#[trigger] items[k]).base) {
            let k = choose|k: int| 0 <= k < items.len()
                && crate::name_constraints::matching::spec::within(cn, (#[trigger] items[k]).base);
            if k < rest.len() { assert(rest[k] == items[k]); }
        }
    }
}

/// P4's `meets_some` is "some base meets the name".
pub proof fn lemma_p4_meets_some(
    items: Seq<crate::name_constraints::spec::GeneralSubtree>,
    cn: crate::name_constraints::matching::spec::ConstrainedName,
)
    ensures
        crate::name_constraints::matching::spec::meets_some(items, cn)
            == exists|k: int| 0 <= k < items.len()
                && crate::name_constraints::matching::spec::meets(cn, (#[trigger] items[k]).base),
    decreases items.len()
{
    if items.len() > 0 {
        let rest = items.drop_last();
        lemma_p4_meets_some(rest, cn);
        assert forall|k: int| 0 <= k < rest.len() implies #[trigger] rest[k] == items[k] by {}
        if crate::name_constraints::matching::spec::meets(cn, items.last().base) {
            assert(items[items.len() - 1] == items.last());
        }
        if exists|k: int| 0 <= k < items.len()
            && crate::name_constraints::matching::spec::meets(cn, (#[trigger] items[k]).base) {
            let k = choose|k: int| 0 <= k < items.len()
                && crate::name_constraints::matching::spec::meets(cn, (#[trigger] items[k]).base);
            if k < rest.len() { assert(rest[k] == items[k]); }
        }
    }
}

/// P4's permitted denotation is "every set's".
pub proof fn lemma_p4_permitted(
    st: Seq<crate::name_constraints::spec::NameConstraints>,
    cn: crate::name_constraints::matching::spec::ConstrainedName,
)
    ensures
        crate::name_constraints::matching::spec::within_permitted_subtrees(st, cn)
            == forall|j: int| 0 <= j < st.len()
                ==> crate::name_constraints::matching::spec::permitted_by(#[trigger] st[j], cn),
    decreases st.len()
{
    if st.len() > 0 {
        let rest = st.drop_last();
        lemma_p4_permitted(rest, cn);
        assert(st[st.len() - 1] == st.last());
        if forall|j: int| 0 <= j < st.len() ==> crate::name_constraints::matching::spec::permitted_by(#[trigger] st[j], cn) {
            assert forall|j: int| 0 <= j < rest.len()
                implies crate::name_constraints::matching::spec::permitted_by(#[trigger] rest[j], cn) by {
                assert(rest[j] == st[j]);
            }
        }
        if crate::name_constraints::matching::spec::within_permitted_subtrees(st, cn) {
            assert forall|j: int| 0 <= j < st.len()
                implies crate::name_constraints::matching::spec::permitted_by(#[trigger] st[j], cn) by {
                if j < rest.len() { assert(rest[j] == st[j]); }
            }
        }
    }
}

/// P4's excluded denotation is "some set's".
pub proof fn lemma_p4_excluded(
    st: Seq<crate::name_constraints::spec::NameConstraints>,
    cn: crate::name_constraints::matching::spec::ConstrainedName,
)
    ensures
        crate::name_constraints::matching::spec::within_excluded_subtrees(st, cn)
            == exists|j: int| 0 <= j < st.len()
                && crate::name_constraints::matching::spec::excluded_by(#[trigger] st[j], cn),
    decreases st.len()
{
    if st.len() > 0 {
        let rest = st.drop_last();
        lemma_p4_excluded(rest, cn);
        assert forall|j: int| 0 <= j < rest.len() implies #[trigger] rest[j] == st[j] by {}
        if crate::name_constraints::matching::spec::excluded_by(st.last(), cn) {
            assert(st[st.len() - 1] == st.last());
        }
        if exists|j: int| 0 <= j < st.len()
            && crate::name_constraints::matching::spec::excluded_by(#[trigger] st[j], cn) {
            let j = choose|j: int| 0 <= j < st.len()
                && crate::name_constraints::matching::spec::excluded_by(#[trigger] st[j], cn);
            if j < rest.len() { assert(rest[j] == st[j]); }
        }
    }
}

/// No uninterpreted-form base in dNSName and iPAddress bases.
pub proof fn lemma_p4_no_form(items: Seq<crate::name_constraints::spec::GeneralSubtree>, tag: u32)
    requires items_dns_ip(items),
    ensures
        !crate::name_constraints::matching::spec::has_base_of_form(items, tag),
        !crate::name_constraints::matching::spec::has_rfc822_base(items),
    decreases items.len()
{
    if items.len() > 0 {
        let rest = items.drop_last();
        assert(items[items.len() - 1] == items.last());
        assert forall|k: int| 0 <= k < rest.len() implies dns_ip_base((#[trigger] rest[k]).base) by {
            assert(rest[k] == items[k]);
        }
        lemma_p4_no_form(rest, tag);
    }
}

/// A state of dNSName and iPAddress bases constrains no uninterpreted form
/// and no rfc822Name.
pub proof fn lemma_p4_state_no_form(st: Seq<crate::name_constraints::spec::NameConstraints>, tag: u32)
    requires state_dns_ip(st),
    ensures
        !crate::name_constraints::matching::spec::form_constrained(st, tag),
        !crate::name_constraints::matching::spec::rfc822_in_force(st),
    decreases st.len()
{
    if st.len() > 0 {
        let rest = st.drop_last();
        assert(st[st.len() - 1] == st.last());
        assert forall|j: int| 0 <= j < rest.len() implies nc_dns_ip(#[trigger] rest[j]) by {
            assert(rest[j] == st[j]);
        }
        lemma_p4_state_no_form(rest, tag);
        if let Some(s) = st.last().permitted_subtrees { lemma_p4_no_form(s, tag); }
        if let Some(s) = st.last().excluded_subtrees { lemma_p4_no_form(s, tag); }
    }
}

/// A name that is not a DNS name or an address is acceptable to a state of
/// dNSName and iPAddress bases.
pub proof fn lemma_p4_other_ok(
    st: Seq<crate::name_constraints::spec::NameConstraints>,
    cn: crate::name_constraints::matching::spec::ConstrainedName,
)
    requires state_dns_ip(st), !(cn is Dns || cn is DnsWildcard || cn is Ip),
    ensures crate::name_constraints::matching::spec::name_acceptable(st, cn),
{
    lemma_p4_permitted(st, cn);
    lemma_p4_excluded(st, cn);
    assert forall|j: int| 0 <= j < st.len()
        implies crate::name_constraints::matching::spec::permitted_by(#[trigger] st[j], cn) by {
        if let Some(items) = st[j].permitted_subtrees {
            lemma_p4_has_base(items, cn);
            assert forall|k: int| 0 <= k < items.len()
                implies !crate::name_constraints::matching::spec::same_name_type(cn, (#[trigger] items[k]).base) by {
                assert(nc_dns_ip(st[j]));
            }
        }
    }
    assert forall|j: int| 0 <= j < st.len()
        implies !crate::name_constraints::matching::spec::excluded_by(#[trigger] st[j], cn) by {
        if let Some(items) = st[j].excluded_subtrees {
            lemma_p4_meets_some(items, cn);
            assert forall|k: int| 0 <= k < items.len()
                implies !crate::name_constraints::matching::spec::meets(cn, (#[trigger] items[k]).base) by {
                assert(nc_dns_ip(st[j]));
            }
        }
    }
}

/// P4's `names_well_formed` as a quantifier.
#[verifier::spinoff_prover]
pub proof fn lemma_p4_well_formed(
    st: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        crate::name_constraints::matching::spec::names_well_formed(names)
            == forall|m: int| 0 <= m < names.len() ==> crate::name_constraints::matching::spec::entry_well_formed((#[trigger] names[m])),
    decreases names.len()
{
    if names.len() > 0 {
        let rest = names.drop_last();
        lemma_p4_well_formed(st, rest);
        assert(names[names.len() - 1] == names.last());
        if forall|m: int| 0 <= m < names.len() ==> crate::name_constraints::matching::spec::entry_well_formed((#[trigger] names[m])) {
            assert forall|m: int| 0 <= m < rest.len() implies crate::name_constraints::matching::spec::entry_well_formed((#[trigger] rest[m])) by {
                assert(rest[m] == names[m]);
            }
        }
        if crate::name_constraints::matching::spec::names_well_formed(names) {
            assert forall|m: int| 0 <= m < names.len() implies crate::name_constraints::matching::spec::entry_well_formed((#[trigger] names[m])) by {
                if m < rest.len() { assert(rest[m] == names[m]); }
            }
        }
    }
}

/// P4's `names_within_permitted` as a quantifier.
#[verifier::spinoff_prover]
pub proof fn lemma_p4_names_permitted(
    st: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        crate::name_constraints::matching::spec::names_within_permitted(st, names)
            == forall|m: int| 0 <= m < names.len() ==> p4_entry_permitted(st, (#[trigger] names[m])),
    decreases names.len()
{
    if names.len() > 0 {
        let rest = names.drop_last();
        lemma_p4_names_permitted(st, rest);
        assert(names[names.len() - 1] == names.last());
        if forall|m: int| 0 <= m < names.len() ==> p4_entry_permitted(st, (#[trigger] names[m])) {
            assert forall|m: int| 0 <= m < rest.len() implies p4_entry_permitted(st, (#[trigger] rest[m])) by {
                assert(rest[m] == names[m]);
            }
        }
        if crate::name_constraints::matching::spec::names_within_permitted(st, names) {
            assert forall|m: int| 0 <= m < names.len() implies p4_entry_permitted(st, (#[trigger] names[m])) by {
                if m < rest.len() { assert(rest[m] == names[m]); }
            }
        }
    }
}

/// P4's `names_not_excluded` as a quantifier.
#[verifier::spinoff_prover]
pub proof fn lemma_p4_names_not_excluded(
    st: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        crate::name_constraints::matching::spec::names_not_excluded(st, names)
            == forall|m: int| 0 <= m < names.len() ==> p4_entry_not_excluded(st, (#[trigger] names[m])),
    decreases names.len()
{
    if names.len() > 0 {
        let rest = names.drop_last();
        lemma_p4_names_not_excluded(st, rest);
        assert(names[names.len() - 1] == names.last());
        if forall|m: int| 0 <= m < names.len() ==> p4_entry_not_excluded(st, (#[trigger] names[m])) {
            assert forall|m: int| 0 <= m < rest.len() implies p4_entry_not_excluded(st, (#[trigger] rest[m])) by {
                assert(rest[m] == names[m]);
            }
        }
        if crate::name_constraints::matching::spec::names_not_excluded(st, names) {
            assert forall|m: int| 0 <= m < names.len() implies p4_entry_not_excluded(st, (#[trigger] names[m])) by {
                if m < rest.len() { assert(rest[m] == names[m]); }
            }
        }
    }
}

/// P4's `names_of_unconstrained_forms` as a quantifier.
#[verifier::spinoff_prover]
pub proof fn lemma_p4_names_forms(
    st: Seq<crate::name_constraints::spec::NameConstraints>, names: Seq<crate::extensions::spec::GeneralName>,
)
    ensures
        crate::name_constraints::matching::spec::names_of_unconstrained_forms(st, names)
            == forall|m: int| 0 <= m < names.len() ==> p4_entry_form_ok(st, (#[trigger] names[m])),
    decreases names.len()
{
    if names.len() > 0 {
        let rest = names.drop_last();
        lemma_p4_names_forms(st, rest);
        assert(names[names.len() - 1] == names.last());
        if forall|m: int| 0 <= m < names.len() ==> p4_entry_form_ok(st, (#[trigger] names[m])) {
            assert forall|m: int| 0 <= m < rest.len() implies p4_entry_form_ok(st, (#[trigger] rest[m])) by {
                assert(rest[m] == names[m]);
            }
        }
        if crate::name_constraints::matching::spec::names_of_unconstrained_forms(st, names) {
            assert forall|m: int| 0 <= m < names.len() implies p4_entry_form_ok(st, (#[trigger] names[m])) by {
                if m < rest.len() { assert(rest[m] == names[m]); }
            }
        }
    }
}

// ---------------------------------------------------------------------
// One certificate's names.
// ---------------------------------------------------------------------

/// One subjectAltName entry: X.509's check is P4's.
#[verifier::spinoff_prover]
pub proof fn lemma_entry(
    st: Seq<crate::name_constraints::spec::NameConstraints>, x: super::independent::PathState,
    g: crate::extensions::spec::GeneralName,
)
    requires
        state_dns_ip(st),
        x.permitted_subtrees == perm_of(st),
        x.excluded_subtrees == excl_of(st),
        st.len() > 0 ==> plain_entry(g),
    ensures x_name_ok(x, x_of(g)) == p4_entry_ok(st, g),
{
    lemma_p4_state_no_form(st, match g { crate::extensions::spec::GeneralName::Other(tag, _) => tag, _ => 0 });
    let xn = x_of(g);
    if st.len() == 0 {
        assert(perm_of(st) =~= Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty());
        assert(excl_of(st) =~= Seq::<crate::name_constraints::spec::GeneralSubtree>::empty());
        if let Some(cn) = crate::name_constraints::matching::spec::constrained_name(g) {
            lemma_p4_permitted(st, cn);
            lemma_p4_excluded(st, cn);
        }
    } else if g is Other {
        lemma_x_other_ok(x, xn);
        if let Some(cn) = crate::name_constraints::matching::spec::constrained_name(g) {
            lemma_p4_other_ok(st, cn);
        }
    } else {
        let cn = crate::name_constraints::matching::spec::constrained_name(g)->Some_0;
        lemma_x_permitted(st, xn);
        lemma_x_excluded(st, xn);
        lemma_p4_permitted(st, cn);
        lemma_p4_excluded(st, cn);
        assert forall|j: int| 0 <= j < st.len() implies ({
            &&& x_nc_ok(#[trigger] st[j], xn) == crate::name_constraints::matching::spec::permitted_by(st[j], cn)
            &&& (match st[j].excluded_subtrees {
                    Some(s) => super::independent::within_some(s, xn, 0),
                    None => false,
                }) == crate::name_constraints::matching::spec::excluded_by(st[j], cn)
        }) by {
            if let Some(s) = st[j].permitted_subtrees {
                lemma_x_constrains(s, xn, 0);
                lemma_x_within_some(s, xn, 0);
                lemma_p4_has_base(s, cn);
                lemma_p4_within_some(s, cn);
                assert forall|k: int| 0 <= k < s.len() implies ({
                    &&& super::independent::subtree_has_form_of(#[trigger] s[k], xn)
                        == crate::name_constraints::matching::spec::same_name_type(cn, s[k].base)
                    &&& super::independent::within_subtree(xn, s[k])
                        == crate::name_constraints::matching::spec::within(cn, s[k].base)
                }) by { lemma_base(g, s[k]); }
            }
            if let Some(s) = st[j].excluded_subtrees {
                lemma_x_within_some(s, xn, 0);
                lemma_p4_meets_some(s, cn);
                assert forall|k: int| 0 <= k < s.len() implies
                    super::independent::within_subtree(xn, #[trigger] s[k])
                        == crate::name_constraints::matching::spec::meets(cn, s[k].base) by {
                    lemma_base(g, s[k]);
                }
            }
        }
    }
}

/// The subject field is acceptable to P4 under the domain.
pub proof fn lemma_subject(st: Seq<crate::name_constraints::spec::NameConstraints>, c: super::parsed::spec::PathCert)
    requires state_dns_ip(st), st.len() > 0 ==> names_plain(c),
    ensures crate::name_constraints::matching::spec::subject_acceptable(st, c.tbs.subject_der),
{
    if st.len() > 0 {
        let parsed = crate::name::spec::parse_name(c.tbs.subject_der)->Some_0;
        lemma_p4_other_ok(st, crate::name_constraints::matching::spec::ConstrainedName::Directory(parsed.rdns));
        lemma_p4_state_no_form(st, 0);
    }
}

/// P4's checks of a certificate are its checks of each entry, under the domain.
#[verifier::spinoff_prover]
pub proof fn lemma_p4_certificate(st: Seq<crate::name_constraints::spec::NameConstraints>, c: super::parsed::spec::PathCert)
    requires state_dns_ip(st), st.len() > 0 ==> names_plain(c),
    ensures ({
        let sans = super::spec::nc_certificate(c).subject_alt_names;
        crate::name_constraints::matching::spec::certificate_acceptable(st, super::spec::nc_certificate(c))
            == forall|m: int| 0 <= m < sans.len() ==> p4_entry_ok(st, #[trigger] sans[m])
    }),
{
    let sans = super::spec::nc_certificate(c).subject_alt_names;
    lemma_subject(st, c);
    lemma_p4_well_formed(st, sans);
    lemma_p4_names_permitted(st, sans);
    lemma_p4_names_not_excluded(st, sans);
    lemma_p4_names_forms(st, sans);
    if st.len() > 0 {
        assert forall|m: int| 0 <= m < sans.len()
            implies crate::name_constraints::matching::spec::entry_well_formed(#[trigger] sans[m]) by {
            assert(plain_entry(sans[m]));
        }
    }
}

/// X.509's checks of a certificate's names are its checks of each entry.
pub proof fn lemma_x_certificate(x: super::independent::PathState, c: super::parsed::spec::PathCert)
    requires x.required_name_forms.len() == 0,
    ensures ({
        let sans = super::spec::nc_certificate(c).subject_alt_names;
        let names = super::independent::subject_names(c);
        &&& super::independent::every_set_satisfied(names, x.required_name_forms, 0)
        &&& (super::independent::name_space_failure(x, names, 0) is None)
            == forall|m: int| 0 <= m < sans.len() ==> x_name_ok(x, x_of(#[trigger] sans[m]))
    }),
{
    let sans = super::spec::nc_certificate(c).subject_alt_names;
    let names = super::independent::subject_names(c);
    lemma_san_names(sans, 0);
    let subj: Seq<super::independent::SubjectName> = if c.tbs.subject_der =~= seq![0x30u8, 0x00u8] { seq![] }
        else { seq![super::independent::SubjectName::Directory(c.tbs.subject_der)] };
    let x_sans = super::independent::san_names(sans, 0);
    assert(names =~= subj + x_sans);
    lemma_x_name_space(x, names, 0);
    assert forall|m: int| 0 <= m < subj.len() implies x_name_ok(x, #[trigger] subj[m]) by {
        lemma_x_other_ok(x, subj[m]);
    }
    if forall|m: int| 0 <= m < names.len() ==> x_name_ok(x, #[trigger] names[m]) {
        assert forall|m: int| 0 <= m < sans.len() implies x_name_ok(x, x_of(#[trigger] sans[m])) by {
            assert(names[subj.len() + m] == x_sans[m]);
        }
    }
    if forall|m: int| 0 <= m < sans.len() ==> x_name_ok(x, x_of(#[trigger] sans[m])) {
        assert forall|m: int| 0 <= m < names.len() implies x_name_ok(x, #[trigger] names[m]) by {
            if m >= subj.len() {
                assert(names[m] == x_sans[m - subj.len()]);
                assert(x_name_ok(x, x_of(sans[m - subj.len()])));
            } else {
                assert(names[m] == subj[m]);
            }
        }
    }
}

/// §12.5.1 g), h) for `path[i]` is P4's §6.1.3 (b), (c) under the domain.
#[verifier::spinoff_prover]
pub proof fn lemma_names(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
    st: Seq<crate::name_constraints::spec::NameConstraints>, x: super::independent::PathState,
)
    requires
        0 <= i < path.len(),
        state_dns_ip(st),
        st.len() > 0 ==> nc_before(anchor, path, i),
        nc_before(anchor, path, i) ==> names_plain(path[i]),
        (nc_before(anchor, path, i) && i < path.len() - 1 && super::spec::self_issued(path[i]))
            ==> path[i].san is None,
        x.permitted_subtrees == perm_of(st),
        x.excluded_subtrees == excl_of(st),
        x.required_name_forms.len() == 0,
    ensures
        crate::name_constraints::matching::spec::certificate_acceptable(st, super::spec::nc_certificate(path[i]))
            == ((i < path.len() - 1 && super::independent::is_self_issued(path[i])) || ({
                &&& super::independent::name_space_failure(x, super::independent::subject_names(path[i]), 0) is None
                &&& super::independent::every_set_satisfied(
                    super::independent::subject_names(path[i]), x.required_name_forms, 0)
            })),
{
    let c = path[i];
    let sans = super::spec::nc_certificate(c).subject_alt_names;
    lemma_p4_certificate(st, c);
    lemma_x_certificate(x, c);
    assert(super::spec::self_issued(c) == super::independent::is_self_issued(c));
    assert forall|m: int| 0 <= m < sans.len() implies
        x_name_ok(x, x_of(#[trigger] sans[m])) == p4_entry_ok(st, sans[m]) by {
        if st.len() > 0 { assert(plain_entry(sans[m])); }
        lemma_entry(st, x, sans[m]);
    }
    // A self-issued intermediate under a constraint has no entries.
    if i < path.len() - 1 && super::independent::is_self_issued(c) && st.len() > 0 {
        assert(sans.len() == 0);
    }
}

// ---------------------------------------------------------------------
// The procedures, certificate by certificate.
// ---------------------------------------------------------------------

/// What signed `path[i]`: the anchor's key, or the previous certificate's.
pub open spec fn key_before(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
) -> Seq<u8> {
    if i == 0 { anchor.spki_der } else { path[i - 1].tbs.subject_public_key_info_der }
}

/// The name `path[i]`'s issuer must have: the anchor's, or the previous
/// certificate's subject.
pub open spec fn name_before(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
) -> Seq<u8> {
    if i == 0 { anchor.subject_der } else { path[i - 1].tbs.subject_der }
}

/// Everything the induction carries about the two states before `path[i]`.
pub open spec fn states_agree(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
    s: super::spec::State, x: super::independent::PathState,
) -> bool {
    &&& s.working_public_key == key_before(anchor, path, i)
    &&& s.working_issuer_name == name_before(anchor, path, i)
    &&& s.explicit_policy + i >= path.len() + 1
    &&& state_dns_ip(s.subtrees)
    &&& s.subtrees.len() > 0 ==> nc_before(anchor, path, i)
    &&& x.permitted_subtrees == perm_of(s.subtrees)
    &&& x.excluded_subtrees == excl_of(s.subtrees)
    &&& x.required_name_forms.len() == 0
}

/// X.509's final processing always succeeds without a policy table.
pub proof fn lemma_final(x: super::independent::PathState)
    ensures super::independent::final_processing(x) is Success,
{
}

/// The state after a certificate's NameConstraints, in P4's form.
pub open spec fn subtrees_after(
    st: Seq<crate::name_constraints::spec::NameConstraints>, c: super::parsed::spec::PathCert,
) -> Seq<crate::name_constraints::spec::NameConstraints> {
    match c.name_constraints { Some(v) => st.push(v), None => st }
}

/// §6.1.3 for `path[i]` under the domain.
pub proof fn lemma_spec_basic(
    link: super::spec::LinkFn, revoked: super::spec::RevokedFn,
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>,
    now: crate::time::spec::CertificateTime, i: int, s: super::spec::State,
)
    requires
        0 <= i < path.len(),
        crate::time::spec::calendar_time_valid(now),
        cert_in_equivalence_domain(link, revoked, anchor, path, i),
        s.working_public_key == key_before(anchor, path, i),
        s.working_issuer_name == name_before(anchor, path, i),
        s.explicit_policy > 0,
    ensures
        (super::spec::basic_certificate_processing(link, revoked, s, path[i], now) is Ok) == ({
            &&& oracle(link)(path[i], key_before(anchor, path, i))
            &&& super::independent::time_le(path[i].tbs.not_before, now)
            &&& super::independent::time_le(now, path[i].tbs.not_after)
            &&& path[i].tbs.issuer_der =~= name_before(anchor, path, i)
            &&& crate::name_constraints::matching::spec::certificate_acceptable(
                s.subtrees, super::spec::nc_certificate(path[i]))
        }),
{
    let c = path[i];
    lemma_validity(c, now);
    assert((c.tbs.issuer_der != s.working_issuer_name) == !(c.tbs.issuer_der =~= name_before(anchor, path, i)));
}

/// §12.5.1 b) for an intermediate: cA, and the count below it.
pub proof fn lemma_x_basic_constraints(path: Seq<super::parsed::spec::PathCert>, i: int)
    requires 0 <= i < path.len() - 1, path[i].tbs.version == 2,
    ensures
        (super::independent::basic_constraints_failure(path, i) is None) == ({
            &&& match path[i].basic { Some(b) => b.ca, None => false }
            &&& match path[i].basic {
                Some(b) => match b.path_len_constraint {
                    Some(octets) => super::independent::non_self_issued_count(path, i + 1, path.len() - 1)
                        <= super::parsed::spec::skip_certs_value(octets),
                    None => true,
                },
                None => true,
            }
        }),
{
    if let Some(b) = path[i].basic {
        if let Some(octets) = b.path_len_constraint {
            lemma_magnitude(octets);
        }
    }
}

/// §6.1.4 for an intermediate under the domain.
pub proof fn lemma_spec_prep(s: super::spec::State, c: super::parsed::spec::PathCert)
    requires
        c.tbs.version == 2,
        !c.has_policy_mappings,
        c.require_explicit_policy is None,
        match c.key_usage {
            Some(usage) => crate::constraints::spec::key_usage_has(
                usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
            None => true,
        },
        super::spec::intermediate_critical_supported(c.extensions, 0),
        nc_supported(c.name_constraints),
    ensures
        (super::spec::preparation_for_next(s, c) is Ok)
            == (match c.basic { Some(b) => b.ca, None => false }
                && (super::spec::self_issued(c) || s.max_path_length > 0)),
        super::spec::preparation_for_next(s, c) is Ok ==> ({
            let next = super::spec::preparation_for_next(s, c)->Ok_0;
            &&& next.subtrees == subtrees_after(s.subtrees, c)
            &&& next.working_public_key == c.tbs.subject_public_key_info_der
            &&& next.working_issuer_name == c.tbs.subject_der
            &&& next.explicit_policy + 1 >= s.explicit_policy
            &&& next.max_path_length == super::spec::max_path_length_after_m(
                if super::spec::self_issued(c) { s.max_path_length } else { (s.max_path_length - 1) as nat }, c)
        }),
{
}

/// X.509's state after an intermediate still matches P4's.
pub proof fn lemma_x_next(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>, i: int,
    s: super::spec::State, x: super::independent::PathState,
)
    requires
        0 <= i < path.len() - 1,
        states_agree(anchor, path, i, s, x),
        super::independent::cert_in_domain(path[i]),
    ensures ({
        let c = path[i];
        let st2 = subtrees_after(s.subtrees, c);
        let x2 = super::independent::explicit_policy_indicator_processing(
            c, true, super::independent::processing_intermediate_certificate(c, x));
        &&& x2.permitted_subtrees == perm_of(st2)
        &&& x2.excluded_subtrees == excl_of(st2)
        &&& x2.required_name_forms.len() == 0
        &&& state_dns_ip(st2)
        &&& st2.len() > 0 ==> nc_before(anchor, path, i + 1)
    }),
{
    let c = path[i];
    let st2 = subtrees_after(s.subtrees, c);
    lemma_supported_nc(c.name_constraints);
    if let Some(v) = c.name_constraints {
        assert(st2.drop_last() =~= s.subtrees);
        assert(st2.last() == v);
        assert forall|j: int| 0 <= j < st2.len() implies nc_dns_ip(#[trigger] st2[j]) by {
            if j < s.subtrees.len() { assert(st2[j] == s.subtrees[j]); }
        }
        assert(0 <= i < i + 1 && path[i].name_constraints is Some);
    } else if st2.len() > 0 && anchor.name_constraints is None {
        let j = choose|j: int| 0 <= j < i && (#[trigger] path[j]).name_constraints is Some;
        assert(0 <= j < i + 1 && path[j].name_constraints is Some);
    }
}

/// From `path[i]` on, RFC 5280 succeeds iff X.509 does and
/// `max_path_length` covers the non-self-issued intermediates left.
#[verifier::spinoff_prover]
pub proof fn lemma_process_from(
    link: super::spec::LinkFn, revoked: super::spec::RevokedFn,
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>,
    now: crate::time::spec::CertificateTime, i: int,
    s: super::spec::State, x: super::independent::PathState,
)
    requires
        0 <= i < path.len(),
        super::independent::path_in_domain(path, 0),
        equivalence_domain(link, revoked, anchor, path, now),
        states_agree(anchor, path, i, s, x),
    ensures
        (super::spec::process_from(link, revoked, path, i, now, s) is Ok)
            == (super::independent::process_certificates(oracle(link), anchor, path, now, i, x) is Success
                && s.max_path_length >= super::independent::non_self_issued_count(path, i, path.len() - 1)),
    decreases path.len() - i
{
    let c = path[i];
    let n = path.len();
    let intermediate = i < n - 1;
    assert(cert_in_equivalence_domain(link, revoked, anchor, path, i));
    lemma_path_in_domain(path, 0, i);
    lemma_spec_basic(link, revoked, anchor, path, now, i, s);
    lemma_names(anchor, path, i, s.subtrees, x);
    assert(super::spec::self_issued(c) == super::independent::is_self_issued(c));
    let x1 = if intermediate { super::independent::processing_intermediate_certificate(c, x) } else { x };
    let x2 = super::independent::explicit_policy_indicator_processing(c, intermediate, x1);
    assert(super::independent::process_certificates(oracle(link), anchor, path, now, i, x)
        == match super::independent::basic_certificate_checks(
            oracle(link), path, i, key_before(anchor, path, i), name_before(anchor, path, i), now, x) {
            Some(reason) => super::independent::PathOutcome::Failure(reason),
            None => super::independent::process_certificates(oracle(link), anchor, path, now, i + 1, x2),
        });
    if !intermediate {
        lemma_final(x2);
        assert(super::independent::process_certificates(oracle(link), anchor, path, now, i + 1, x2) is Success);
        assert(super::independent::basic_constraints_failure(path, i) is None);
        assert(super::independent::non_self_issued_count(path, i, n - 1) == 0);
        assert(super::spec::wrap_up(s, c) is Ok);
    } else {
        lemma_x_basic_constraints(path, i);
        lemma_spec_prep(s, c);
        lemma_x_next(anchor, path, i, s, x);
        let d: nat = if super::independent::is_self_issued(c) { 0 } else { 1 };
        assert(super::independent::non_self_issued_count(path, i, n - 1)
            == d + super::independent::non_self_issued_count(path, i + 1, n - 1));
        let sp = super::spec::preparation_for_next(s, c);
        if sp is Ok {
            let next = sp->Ok_0;
            assert(states_agree(anchor, path, i + 1, next, x2));
            lemma_process_from(link, revoked, anchor, path, now, i + 1, next, x2);
        }
    }
}

// ---------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------

/// The state P4 starts from: the anchor's NameConstraints, if any.
pub open spec fn initial_subtrees(
    nc: Option<crate::name_constraints::spec::NameConstraints>,
) -> Seq<crate::name_constraints::spec::NameConstraints> {
    match nc { Some(v) => seq![v], None => seq![] }
}

/// X.509's initial lists are `perm_of` and `excl_of` of P4's initial state.
pub proof fn lemma_initial_lists(nc: Option<crate::name_constraints::spec::NameConstraints>)
    ensures
        Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty()
            .add(super::independent::anchor_permitted(nc)) == perm_of(initial_subtrees(nc)),
        Seq::<crate::name_constraints::spec::GeneralSubtree>::empty()
            .add(super::independent::anchor_excluded(nc)) == excl_of(initial_subtrees(nc)),
{
    let st0 = initial_subtrees(nc);
    let e = Seq::<crate::name_constraints::spec::NameConstraints>::empty();
    assert(perm_of(e) == Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty());
    assert(excl_of(e) == Seq::<crate::name_constraints::spec::GeneralSubtree>::empty());
    if let Some(v) = nc {
        assert(st0.drop_last() =~= e);
        assert(st0.last() == v);
        match v.permitted_subtrees {
            Some(s) => {
                assert(perm_of(st0) == perm_of(e).push(s));
                assert(Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty().add(seq![s])
                    =~= Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty().push(s));
            },
            None => {
                assert(perm_of(st0) == perm_of(e));
                assert(Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty().add(seq![])
                    =~= Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty());
            },
        }
        match v.excluded_subtrees {
            Some(s) => {
                assert(excl_of(st0) == excl_of(e) + s);
            },
            None => {
                assert(excl_of(st0) == excl_of(e));
                assert(Seq::<crate::name_constraints::spec::GeneralSubtree>::empty().add(seq![])
                    =~= Seq::<crate::name_constraints::spec::GeneralSubtree>::empty());
            },
        }
    } else {
        assert(st0 =~= e);
        assert(Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty().add(seq![])
            =~= Seq::<Seq<crate::name_constraints::spec::GeneralSubtree>>::empty());
        assert(Seq::<crate::name_constraints::spec::GeneralSubtree>::empty().add(seq![])
            =~= Seq::<crate::name_constraints::spec::GeneralSubtree>::empty());
    }
}

/// The two initializations agree (§6.1.2 with RFC 5937 §3.2; §12.4).
#[verifier::spinoff_prover]
pub proof fn lemma_initial(
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>,
    now: crate::time::spec::CertificateTime,
)
    requires
        path.len() > 0,
        nc_supported(anchor.name_constraints),
        super::independent::supported_name_constraints(anchor.name_constraints),
    ensures ({
        let init = super::spec::initialization(anchor, path.len());
        &&& init is Ok
        &&& states_agree(anchor, path, 0, init->Ok_0, super::independent::initialization(anchor, browser_inputs(now)))
        &&& init->Ok_0.max_path_length == match anchor.path_len { Some(p) => p, None => path.len() }
    }),
{
    let st0 = initial_subtrees(anchor.name_constraints);
    lemma_supported_nc(anchor.name_constraints);
    lemma_initial_lists(anchor.name_constraints);
    if let Some(v) = anchor.name_constraints {
        assert(Seq::<crate::name_constraints::spec::NameConstraints>::empty().push(v) =~= st0);
        assert forall|j: int| 0 <= j < st0.len() implies nc_dns_ip(#[trigger] st0[j]) by {
            assert(st0[j] == v);
        }
    }
    let init = super::spec::initialization(anchor, path.len());
    assert(init is Ok && init->Ok_0.subtrees == st0);
}

/// **The equivalence.** On the domain, X.509 §12 as transcribed accepts the
/// path iff RFC 5280 §6.1 as `spec.rs` states it does.
#[verifier::spinoff_prover]
pub proof fn theorem_independent_equivalence(
    link: super::spec::LinkFn, revoked: super::spec::RevokedFn,
    anchor: super::parsed::spec::Anchor, path: Seq<super::parsed::spec::PathCert>,
    now: crate::time::spec::CertificateTime,
)
    requires
        super::independent::profile_domain(anchor, path, browser_inputs(now)),
        equivalence_domain(link, revoked, anchor, path, now),
    ensures
        super::independent::path_is_valid(oracle(link), anchor, path, browser_inputs(now))
            == (super::spec::process(link, revoked, anchor, path, now) is Ok),
{
    let n = path.len();
    assert forall|k: int| 0 <= k < n - 1
        implies !super::independent::is_self_signed(oracle(link), #[trigger] path[k]) by {
        assert(cert_in_equivalence_domain(link, revoked, anchor, path, k));
    }
    lemma_drop_ignored(oracle(link), path, 0);
    assert(path.subrange(0, n as int) =~= path);
    if n > 0 {
        lemma_initial(anchor, path, now);
        let s0 = super::spec::initialization(anchor, n)->Ok_0;
        let x0 = super::independent::initialization(anchor, browser_inputs(now));
        lemma_process_from(link, revoked, anchor, path, now, 0, s0, x0);
        lemma_count_bound(path, 0, n - 1);
    }
}

// ---------------------------------------------------------------------
// The domain is not empty.
// ---------------------------------------------------------------------

/// The production revocation instance: nothing is revoked.
pub open spec fn never_revoked() -> super::spec::RevokedFn {
    |c: super::parsed::spec::PathCert| false
}

/// A CA certificate for `subject` issued by `issuer` (the transcription's
/// toy certificate with cA TRUE and its own DER).
pub open spec fn example_ca(issuer: u8, subject: u8) -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert {
        der: seq![issuer, subject],
        basic: Some(crate::constraints::spec::BasicConstraints { ca: true, path_len_constraint: None }),
        ..super::independent::toy_cert(issuer, subject)
    }
}

/// The end entity of the example path.
pub open spec fn example_leaf(issuer: u8, subject: u8) -> super::parsed::spec::PathCert {
    super::parsed::spec::PathCert { der: seq![issuer, subject, 0u8], ..super::independent::toy_cert(issuer, subject) }
}

/// Anchor 1, an intermediate 2, an end entity 3, inside the domain for
/// every `link`, so `theorem_independent_equivalence` is not vacuous.
#[verifier::spinoff_prover]
pub proof fn example_domain_inhabited(link: super::spec::LinkFn)
    ensures ({
        let anchor = super::independent::toy_anchor(1);
        let path = seq![example_ca(1, 2), example_leaf(2, 3)];
        let now = super::independent::t(6, 1);
        &&& super::independent::profile_domain(anchor, path, browser_inputs(now))
        &&& equivalence_domain(link, never_revoked(), anchor, path, now)
    }),
{
    let anchor = super::independent::toy_anchor(1);
    let path = seq![example_ca(1, 2), example_leaf(2, 3)];
    let now = super::independent::t(6, 1);
    assert(super::independent::path_in_domain(path, 2));
    assert(super::independent::path_in_domain(path, 1));
    assert(super::independent::supported_subtrees(Seq::<crate::name_constraints::spec::GeneralSubtree>::empty(), 0));
    assert(path[0].der.len() == 2 && path[1].der.len() == 3);
    assert(path[1].der != path[0].der);
    assert(super::spec::der_absent_from(path, path[0].der, 2));
    assert(super::spec::der_absent_from(path, path[1].der, 2));
    assert(super::spec::der_absent_from(path, path[0].der, 1));
    assert(super::spec::certificates_distinct_from(path, 2));
    assert(super::spec::certificates_distinct_from(path, 1));
    assert(super::spec::certificates_distinct_from(path, 0));
    assert(path[0].tbs.issuer_der == seq![1u8] && path[0].tbs.subject_der == seq![2u8]);
    assert(path[0].tbs.issuer_der[0] != path[0].tbs.subject_der[0]);
    assert(!super::independent::is_self_issued(path[0]));
    assert(super::spec::intermediate_critical_supported(path[0].extensions, 0));
    assert(crate::leaf::spec::supported_critical_extensions(path[1].extensions, 0));
    assert forall|i: int| 0 <= i < path.len()
        implies cert_in_equivalence_domain(link, never_revoked(), anchor, path, i) by {
        assert(!nc_before(anchor, path, i));
    }
}

} // verus!
