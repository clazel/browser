//! `matching.rs`'s `certificate_matches_host` over a whole certificate, and
//! every `MatchChoices`, against what production decides: `leaf/spec.rs`'s
//! `san_matches_reference`, inside `check_extensions`. `equivalence_matching.rs`
//! compares one presented name under `cautious_choices`; this file lifts that.
//!
//! **What each choice does.** On `equivalence_matching.rs`'s domain:
//! - `wildcard_beyond_left_most`, `partial_label_wildcard`,
//!   `wildcard_in_a_label`, `wildcard_may_be_empty` and `ignore_root_dot` **have
//!   no effect**: such a name has no `*` where they apply, and no root dot
//!   ([`theorem_domain_choices`]).
//! - `wildcards`: with it, everything the crate accepts is accepted. Without
//!   it, only names with no `*` are, so the crate is the more permissive side
//!   there ([`theorem_dns_match_under_choices`]).
//! - `wildcard_spans_labels`: the one choice that adds matches on the domain,
//!   so only one direction holds ([`theorem_spanning_is_wider`]).
//! - `cn_id`: [`theorem_cn_id_adds`] says exactly what it adds: a Common Name,
//!   when no DNS-ID, SRV-ID or URI-ID is presented. **The crate has no
//!   counterpart, by design** (RFC 9525 §6.2, `leaf/spec.rs`): so what
//!   production accepts, the transcription accepts under any `cn_id`, and the
//!   reverse fails for exactly those certificates.
//!
//! **SRV-ID and URI-ID.** `matching.rs` keeps them only as blockers of a CN-ID,
//! because matching them needs an application service type (RFC 6125 6.5). The
//! crate has neither: `only_supported_general_names` refuses a certificate with
//! any such entry, even one with a DNS-ID that matches, so production is the
//! stricter side ([`theorem_leaf_names`]). Neither side matches through them
//! ([`theorem_other_forms_never_match`]).
//!
//! **IP-ID** stays outside: RFC 6125 1.7.2 leaves IP addresses out, and
//! `matching.rs` matches none. `spec.rs`'s `ip_match` has no second transcription.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::equivalence_extensions::*;
#[cfg(verus_only)]
use super::equivalence_matching::*;
#[cfg(verus_only)]
use super::equivalence_path::*;
#[cfg(verus_only)]
use super::extensions as e;
#[cfg(verus_only)]
use super::matching::*;
#[cfg(verus_only)]
use super::requirements as r;
#[cfg(verus_only)]
use super::structures as s;
#[cfg(verus_only)]
use crate::extensions::spec as x;
#[cfg(verus_only)]
use crate::leaf::spec as lf;
#[cfg(verus_only)]
use crate::path::parsed::spec as ps;
#[cfg(verus_only)]
use crate::spec as h;
#[cfg(verus_only)]
use crate::tbs::spec as t;
#[cfg(verus_only)]
use crate::time::spec as tm;

verus! {

// ---------------------------------------------------------------------
// One label, under any choices.
// ---------------------------------------------------------------------

/// A label with no `*` matches as `same_label`, whatever the choices.
pub proof fn lemma_choices_plain_label(c: MatchChoices, a: Seq<u8>, y: Seq<u8>, beyond: bool)
    requires
        no_star(a, 0),
    ensures
        label_matches(c, a, y, beyond) == same_label(a, y),
{
    lemma_star_count_zero(a, 0);
}

/// The whole-label `*`, left-most, matches any non-empty label if wildcards
/// are taken at all.
pub proof fn lemma_choices_star_label(c: MatchChoices, a: Seq<u8>, y: Seq<u8>)
    requires
        a.len() == 1,
        a[0] == 0x2A,
    ensures
        label_matches(c, a, y, false) == (c.wildcards && y.len() > 0),
{
    assert(star_count(a, 1) == 0);
    assert(star_count(a, 0) == 1);
}

/// The labels of a name with no `*` have none.
pub proof fn lemma_labels_no_star(p: Seq<u8>, i: nat)
    requires
        i <= p.len(),
        no_star(p, i),
    ensures
        forall|k: int| 0 <= k < labels_from(p, i).len() ==> no_star(#[trigger] labels_from(p, i)[k], 0),
    decreases p.len() - i,
{
    lemma_labels_step(p, i);
    lemma_next_dot(p, i);
    let dot = next_dot(p, i);
    let head = p.subrange(i as int, dot as int);
    assert(no_star(head, 0)) by {
        assert forall|k: int| 0 <= k < head.len() implies #[trigger] head[k] != 0x2A by {
            assert(head[k] == p[i + k]);
        }
    }
    if dot < p.len() {
        assert(no_star(p, dot + 1));
        lemma_labels_no_star(p, dot + 1);
        let rest = labels_from(p, dot + 1);
        let all = labels_from(p, i);
        assert(all == seq![head] + rest);
        assert forall|k: int| 0 <= k < all.len() implies no_star(#[trigger] all[k], 0) by {
            if k > 0 {
                assert(all[k] == rest[k - 1]);
            } else {
                assert(all[k] == head);
            }
        }
    } else {
        let all = labels_from(p, i);
        assert(all == seq![head]);
        assert forall|k: int| 0 <= k < all.len() implies no_star(#[trigger] all[k], 0) by {
            assert(all[k] == head);
        }
    }
}

/// Labels with no `*` compare alike under any two choices.
pub proof fn lemma_remaining_choices(c: MatchChoices, q: MatchChoices, p: Seq<Seq<u8>>, i: nat, y: Seq<Seq<u8>>, j: nat)
    requires
        forall|k: int| i <= k < p.len() ==> no_star(#[trigger] p[k], 0),
    ensures
        remaining_labels_match(c, p, i, y, j) == remaining_labels_match(q, p, i, y, j),
    decreases p.len() - i,
{
    if i < p.len() && j < y.len() {
        assert(no_star(p[i as int], 0));
        lemma_choices_plain_label(c, p[i as int], y[j as int], true);
        lemma_choices_plain_label(q, p[i as int], y[j as int], true);
        lemma_remaining_choices(c, q, p, i + 1, y, j + 1);
    }
}

/// A shaped name does not end in a dot.
pub proof fn lemma_shape_no_root_dot(n: Seq<u8>, i: int)
    requires
        0 <= i < n.len(),
        h::valid_name_from(n, i),
    ensures
        n[n.len() - 1] != 0x2E,
    decreases n.len() - i,
{
    if n[i] == 0x2E {
        lemma_shape_no_root_dot(n, i + 1);
    } else if i + 1 < n.len() {
        lemma_shape_no_root_dot(n, i + 1);
    }
}

/// The presented names of `equivalence_matching.rs`'s domain have no root dot.
pub proof fn lemma_domain_no_root_dot(p: Seq<u8>)
    requires
        host_in_domain(p),
    ensures
        without_root_dot(p) == p,
        p.len() > 0,
{
    if h::dns_name_shape(p) {
        lemma_shape_starts(p);
        lemma_shape_no_root_dot(p, 0);
    } else {
        let suffix = p.subrange(2, p.len() as int);
        lemma_shape_starts(suffix);
        lemma_shape_no_root_dot(suffix, 0);
        assert(suffix[suffix.len() - 1] == p[p.len() - 1]);
    }
}

/// The two label lists of a name of the domain, under any choices.
#[verifier::spinoff_prover]
pub proof fn lemma_lists_choices(c: MatchChoices, p: Seq<u8>, y: Seq<u8>)
    requires
        h::dns_name_shape(y),
        host_in_domain(p),
    ensures
        (no_star(p, 0) || c.wildcards) ==> (label_lists_match(cautious_choices(), labels(p), labels(y))
            ==> label_lists_match(c, labels(p), labels(y))),
        !c.wildcard_spans_labels ==> (label_lists_match(c, labels(p), labels(y)) ==> label_lists_match(
            cautious_choices(),
            labels(p),
            labels(y),
        )),
{
    let q = cautious_choices();
    let lp = labels(p);
    let ly = labels(y);
    lemma_shape_starts(y);
    lemma_labels_len(y, 0);
    if h::dns_name_shape(p) {
        lemma_shape_starts(p);
        lemma_shape_no_star(p, 0);
        lemma_labels_len(p, 0);
        lemma_labels_no_star(p, 0);
        assert(no_star(lp[0], 0));
        lemma_choices_plain_label(c, lp[0], ly[0], false);
        lemma_choices_plain_label(q, lp[0], ly[0], false);
        lemma_remaining_choices(c, q, lp, 1, ly, 1);
        // The spanning arm needs a whole-label `*`.
        if lp[0].len() == 1 {
            assert(lp[0][0] != 0x2A);
        }
    } else {
        let suffix = p.subrange(2, p.len() as int);
        lemma_shape_starts(suffix);
        lemma_shape_no_star(suffix, 0);
        assert(no_star(p, 2)) by {
            assert forall|k: int| 2 <= k < p.len() implies #[trigger] p[k] != 0x2A by {
                assert(suffix[k - 2] == p[k]);
            }
        }
        lemma_wildcard_labels(p);
        let star = p.subrange(0, 1);
        let rest = labels_from(p, 2);
        lemma_labels_no_star(p, 2);
        assert(lp == seq![star] + rest);
        assert(lp[0] == star);
        assert forall|k: int| 1 <= k < lp.len() implies no_star(#[trigger] lp[k], 0) by {
            assert(lp[k] == rest[k - 1]);
        }
        lemma_choices_star_label(c, star, ly[0]);
        lemma_choices_star_label(q, star, ly[0]);
        lemma_remaining_choices(c, q, lp, 1, ly, 1);
        assert(!no_star(p, 0)) by {
            assert(p[0] == 0x2A);
        }
    }
}

/// `domain_name_matches` under any choices, from the label lists.
#[verifier::spinoff_prover]
pub proof fn lemma_domain_matches_lists(c: MatchChoices, p: Seq<u8>, y: Seq<u8>)
    requires
        h::dns_name_shape(y),
        host_in_domain(p),
    ensures
        domain_name_matches(c, p, y) == (reference_usable(y) && labels_non_empty(labels(p), 0)
            && label_lists_match(c, labels(p), labels(y))),
{
    lemma_domain_no_root_dot(p);
    lemma_shape_starts(y);
    lemma_shape_no_root_dot(y, 0);
}

/// **On the domain, every choice but `wildcards` and `wildcard_spans_labels`
/// has no effect.** With both settled as `cautious_choices` settles them,
/// `domain_name_matches` is `dns_match`.
pub proof fn theorem_domain_choices(c: MatchChoices, y: Seq<u8>, p: Seq<u8>)
    requires
        h::dns_name_shape(y),
        host_in_domain(p),
        c.wildcards,
        !c.wildcard_spans_labels,
    ensures
        domain_name_matches(c, p, y) == h::dns_match(y, p),
{
    lemma_domain_matches_lists(c, p, y);
    lemma_domain_matches_lists(cautious_choices(), p, y);
    lemma_lists_choices(c, p, y);
    theorem_dns_match_is_rfc_6125(y, p);
}

/// **`dns_match` under any choices, with no domain.** What the crate accepts,
/// RFC 6125 accepts under every `MatchChoices` that takes wildcards at all,
/// and under every one when the name has no `*`.
pub proof fn theorem_dns_match_under_choices(c: MatchChoices, y: Seq<u8>, p: Seq<u8>)
    requires
        c.wildcards || no_star(p, 0),
    ensures
        h::dns_match(y, p) ==> domain_name_matches(c, p, y),
{
    if h::dns_match(y, p) {
        assert(h::dns_name_shape(y));
        assert(host_in_domain(p));
        theorem_dns_match_is_rfc_6125(y, p);
        lemma_domain_matches_lists(c, p, y);
        lemma_domain_matches_lists(cautious_choices(), p, y);
        lemma_lists_choices(c, p, y);
    }
}

/// **Without spanning, on the domain, RFC 6125 accepts only what the crate
/// does**, whether it takes wildcards or not.
pub proof fn theorem_choices_imply_dns_match(c: MatchChoices, y: Seq<u8>, p: Seq<u8>)
    requires
        h::dns_name_shape(y),
        host_in_domain(p),
        !c.wildcard_spans_labels,
    ensures
        domain_name_matches(c, p, y) ==> h::dns_match(y, p),
{
    lemma_domain_matches_lists(c, p, y);
    lemma_domain_matches_lists(cautious_choices(), p, y);
    lemma_lists_choices(c, p, y);
    theorem_dns_match_is_rfc_6125(y, p);
}

/// **`wildcard_spans_labels` is the one choice that widens the domain:** only
/// this direction holds. `example_choices` shows the other fails.
pub proof fn theorem_spanning_is_wider(c: MatchChoices, y: Seq<u8>, p: Seq<u8>)
    requires
        c.wildcards,
        c.wildcard_spans_labels,
    ensures
        h::dns_match(y, p) ==> domain_name_matches(c, p, y),
{
    theorem_dns_match_under_choices(c, y, p);
}

// ---------------------------------------------------------------------
// A list of names.
// ---------------------------------------------------------------------

/// The crate's matching over a list, in the transcription's terms.
pub open spec fn names_agree(a: Seq<x::GeneralName>, w: Seq<e::GeneralName>) -> bool {
    &&& a.len() == w.len()
    &&& forall|k: int| 0 <= k < a.len() ==> general_name_agree(#[trigger] a[k], w[k])
}

/// Every DNS-ID is in the domain.
pub open spec fn dns_ids_in_domain(w: Seq<e::GeneralName>) -> bool {
    forall|k: int|
        0 <= k < w.len() ==> match #[trigger] w[k] {
            e::GeneralName::DNSName(p) => host_in_domain(p),
            _ => true,
        }
}

/// `san_matches_reference` from the crate: `some_dns_id_matches` reads the same
/// names.
pub proof fn lemma_names_fwd(c: MatchChoices, a: Seq<x::GeneralName>, w: Seq<e::GeneralName>, y: Seq<u8>, k: nat)
    requires
        names_agree(a, w),
        c.wildcards,
        k <= a.len(),
        lf::san_matches_reference(a, h::ReferenceIdentity::Dns(y), k as int),
    ensures
        some_dns_id_matches(c, w, k, y),
    decreases a.len() - k,
{
    assert(general_name_agree(a[k as int], w[k as int]));
    if lf::general_name_matches_reference(a[k as int], h::ReferenceIdentity::Dns(y)) {
        match a[k as int] {
            x::GeneralName::DnsName(p) => {
                theorem_dns_match_under_choices(c, y, p);
            },
            _ => {},
        }
    } else {
        lemma_names_fwd(c, a, w, y, k + 1);
    }
}

/// `some_dns_id_matches` from the transcription, on the domain.
pub proof fn lemma_names_back(c: MatchChoices, a: Seq<x::GeneralName>, w: Seq<e::GeneralName>, y: Seq<u8>, k: nat)
    requires
        names_agree(a, w),
        !c.wildcard_spans_labels,
        h::dns_name_shape(y),
        dns_ids_in_domain(w),
        k <= a.len(),
        some_dns_id_matches(c, w, k, y),
    ensures
        lf::san_matches_reference(a, h::ReferenceIdentity::Dns(y), k as int),
    decreases a.len() - k,
{
    assert(general_name_agree(a[k as int], w[k as int]));
    let matched = match w[k as int] {
        e::GeneralName::DNSName(p) => domain_name_matches(c, p, y),
        _ => false,
    };
    if matched {
        match w[k as int] {
            e::GeneralName::DNSName(p) => {
                theorem_choices_imply_dns_match(c, y, p);
                match a[k as int] {
                    x::GeneralName::Other(_, _) => {
                        assert(false);
                    },
                    _ => {},
                }
            },
            _ => {},
        }
    } else {
        lemma_names_back(c, a, w, y, k + 1);
    }
}

// ---------------------------------------------------------------------
// A whole certificate.
// ---------------------------------------------------------------------

/// What production decides for a DNS reference, from the subjectAltName it
/// decoded (`leaf/spec.rs`, step 1 of `check_extensions`).
pub open spec fn crate_matches_host(o: Option<x::SubjectAltName>, y: Seq<u8>) -> bool {
    match o {
        None => false,
        Some(q) => lf::san_matches_reference(q.names, h::ReferenceIdentity::Dns(y), 0),
    }
}

/// `subject_alt_names` is what the crate decoded.
pub proof fn lemma_subject_alt_names(o: Option<x::SubjectAltName>, c: s::Certificate)
    requires
        san_found_agree(o, r::extensions_of(c)),
    ensures
        match o {
            None => subject_alt_names(c).len() == 0,
            Some(q) => names_agree(q.names, subject_alt_names(c)),
        },
{
}

/// **`theorem_host_fwd`.** What production accepts for a certificate,
/// `certificate_matches_host` accepts, under every `MatchChoices` that takes
/// wildcards. No domain.
pub proof fn theorem_host_fwd(q: MatchChoices, o: Option<x::SubjectAltName>, c: s::Certificate, y: Seq<u8>)
    requires
        san_found_agree(o, r::extensions_of(c)),
        q.wildcards,
    ensures
        crate_matches_host(o, y) ==> certificate_matches_host(q, c, y),
{
    lemma_subject_alt_names(o, c);
    if crate_matches_host(o, y) {
        lemma_names_fwd(q, o->Some_0.names, subject_alt_names(c), y, 0);
    }
}

/// **`theorem_host_back`.** What `certificate_matches_host` accepts without
/// spanning and without a Common Name, on the domain, production accepts.
pub proof fn theorem_host_back(q: MatchChoices, o: Option<x::SubjectAltName>, c: s::Certificate, y: Seq<u8>)
    requires
        san_found_agree(o, r::extensions_of(c)),
        !q.wildcard_spans_labels,
        !q.cn_id,
        h::dns_name_shape(y),
        dns_ids_in_domain(subject_alt_names(c)),
    ensures
        certificate_matches_host(q, c, y) ==> crate_matches_host(o, y),
{
    lemma_subject_alt_names(o, c);
    if certificate_matches_host(q, c, y) {
        if o is None {
            assert(subject_alt_names(c).len() == 0);
            assert(!some_dns_id_matches(q, subject_alt_names(c), 0, y));
        } else {
            lemma_names_back(q, o->Some_0.names, subject_alt_names(c), y, 0);
        }
    }
}

/// **`theorem_host_equal`.** On the domain, `certificate_matches_host` under
/// `cautious_choices` is what production decides, for a whole certificate.
pub proof fn theorem_host_equal(o: Option<x::SubjectAltName>, c: s::Certificate, y: Seq<u8>)
    requires
        san_found_agree(o, r::extensions_of(c)),
        h::dns_name_shape(y),
        dns_ids_in_domain(subject_alt_names(c)),
    ensures
        certificate_matches_host(cautious_choices(), c, y) == crate_matches_host(o, y),
{
    theorem_host_fwd(cautious_choices(), o, c, y);
    theorem_host_back(cautious_choices(), o, c, y);
}

/// `choices` with the Common Name turned on or off.
pub open spec fn with_cn_id(q: MatchChoices, cn_id: bool) -> MatchChoices {
    MatchChoices { cn_id, ..q }
}

/// **`theorem_cn_id_adds`.** What `cn_id` adds to `certificate_matches_host` is
/// exactly a Common Name in a certificate with no DNS-ID, SRV-ID or URI-ID.
pub proof fn theorem_cn_id_adds(q: MatchChoices, c: s::Certificate, y: Seq<u8>)
    ensures
        certificate_matches_host(with_cn_id(q, true), c, y) == (certificate_matches_host(with_cn_id(q, false), c, y)
            || (no_blocking_identifier(subject_alt_names(c), 0) && some_cn_matches(
            with_cn_id(q, true),
            c.to_be_signed.subject.rdn_sequence,
            0,
            y,
        ))),
{
    lemma_some_dns_ignores_cn(q, subject_alt_names(c), 0, y);
}

/// `some_dns_id_matches` does not read `cn_id`.
pub proof fn lemma_some_dns_ignores_cn(q: MatchChoices, w: Seq<e::GeneralName>, k: nat, y: Seq<u8>)
    ensures
        some_dns_id_matches(with_cn_id(q, true), w, k, y) == some_dns_id_matches(with_cn_id(q, false), w, k, y),
    decreases w.len() - k,
{
    if k < w.len() {
        lemma_some_dns_ignores_cn(q, w, k + 1, y);
        match w[k as int] {
            e::GeneralName::DNSName(p) => {
                lemma_domain_ignores_cn(q, p, y);
            },
            _ => {},
        }
    }
}

/// `domain_name_matches` does not read `cn_id`.
pub proof fn lemma_domain_ignores_cn(q: MatchChoices, p: Seq<u8>, y: Seq<u8>)
    ensures
        domain_name_matches(with_cn_id(q, true), p, y) == domain_name_matches(with_cn_id(q, false), p, y),
{
    let a = with_cn_id(q, true);
    let b = with_cn_id(q, false);
    let lp = labels(if q.ignore_root_dot { without_root_dot(p) } else { p });
    let ly = labels(if q.ignore_root_dot { without_root_dot(y) } else { y });
    lemma_lists_ignore_cn(q, lp, ly);
}

/// The label lists do not read `cn_id`.
pub proof fn lemma_lists_ignore_cn(q: MatchChoices, lp: Seq<Seq<u8>>, ly: Seq<Seq<u8>>)
    ensures
        label_lists_match(with_cn_id(q, true), lp, ly) == label_lists_match(with_cn_id(q, false), lp, ly),
{
    let a = with_cn_id(q, true);
    let b = with_cn_id(q, false);
    if lp.len() > 0 && ly.len() > 0 {
        lemma_label_ignores_cn(q, lp[0], ly[0], false);
        lemma_remaining_ignores_cn(q, lp, 1, ly, 1);
        if ly.len() >= lp.len() {
            lemma_remaining_ignores_cn(q, lp, 1, ly, (ly.len() - lp.len() + 1) as nat);
        }
    }
}

/// `remaining_labels_match` does not read `cn_id`.
pub proof fn lemma_remaining_ignores_cn(q: MatchChoices, lp: Seq<Seq<u8>>, i: nat, ly: Seq<Seq<u8>>, j: nat)
    ensures
        remaining_labels_match(with_cn_id(q, true), lp, i, ly, j) == remaining_labels_match(with_cn_id(q, false), lp, i, ly, j),
    decreases lp.len() - i,
{
    if i < lp.len() && j < ly.len() {
        lemma_label_ignores_cn(q, lp[i as int], ly[j as int], true);
        lemma_remaining_ignores_cn(q, lp, i + 1, ly, j + 1);
    }
}

/// One label does not read `cn_id`.
pub proof fn lemma_label_ignores_cn(q: MatchChoices, a: Seq<u8>, y: Seq<u8>, beyond: bool)
    ensures
        label_matches(with_cn_id(q, true), a, y, beyond) == label_matches(with_cn_id(q, false), a, y, beyond),
{
}

/// **What `check_extensions` accepted, it read in one subjectAltName.**
#[verifier::spinoff_prover]
pub proof fn lemma_leaf_san(
    list: Seq<x::Extension>,
    tbs: t::TbsCertificate,
    reference: h::ReferenceIdentity,
    now: tm::CertificateTime,
    policy: lf::LeafPolicy,
    o: Option<x::SubjectAltName>,
)
    requires
        lf::check_extensions(list, tbs, reference, now, policy) is Some,
        ps::optional_subject_alt_name(list) == Some(o),
    ensures
        o is Some,
        lf::only_supported_general_names(o->Some_0.names, 0),
        lf::san_matches_reference(o->Some_0.names, reference, 0),
{
    hide(x::parse_subject_alt_name);
    hide(lf::optional_basic_constraints);
    hide(lf::optional_key_usage);
    hide(lf::optional_extended_key_usage);
    hide(crate::constraints::spec::basic_constraints_compatible);
    hide(tm::validity_contains);
}

/// `only_supported_general_names` reaches every name.
pub proof fn lemma_only_supported(a: Seq<x::GeneralName>, k: int, m: int)
    requires
        0 <= k <= m < a.len(),
        lf::only_supported_general_names(a, k),
    ensures
        a[m] is DnsName || a[m] is IpAddress,
    decreases m - k,
{
    if k < m {
        lemma_only_supported(a, k + 1, m);
    }
}

/// **`theorem_leaf_names`.** What `check_extensions` accepts holds only DNS-IDs
/// and IP-IDs: no URI-ID, no SRV-ID, no other form, and a DNS reference has
/// a DNS-ID that matches under every `MatchChoices` that takes wildcards, so a
/// Common Name is never what decides it.
pub proof fn theorem_leaf_names(
    q: MatchChoices,
    list: Seq<x::Extension>,
    tbs: t::TbsCertificate,
    y: Seq<u8>,
    now: tm::CertificateTime,
    policy: lf::LeafPolicy,
    o: Option<x::SubjectAltName>,
    c: s::Certificate,
)
    requires
        lf::check_extensions(list, tbs, h::ReferenceIdentity::Dns(y), now, policy) is Some,
        ps::optional_subject_alt_name(list) == Some(o),
        san_found_agree(o, r::extensions_of(c)),
        q.wildcards,
    ensures
        forall|k: int|
            0 <= k < subject_alt_names(c).len() ==> (#[trigger] subject_alt_names(c)[k] is DNSName
                || subject_alt_names(c)[k] is IPAddress),
        some_dns_id_matches(q, subject_alt_names(c), 0, y),
        certificate_matches_host(q, c, y),
{
    lemma_leaf_san(list, tbs, h::ReferenceIdentity::Dns(y), now, policy, o);
    lemma_subject_alt_names(o, c);
    let w = subject_alt_names(c);
    let a = o->Some_0.names;
    assert forall|k: int| 0 <= k < w.len() implies (#[trigger] w[k] is DNSName || w[k] is IPAddress) by {
        lemma_only_supported(a, 0, k);
        assert(general_name_agree(a[k], w[k]));
    }
    lemma_names_fwd(q, a, w, y, 0);
}

/// **`theorem_other_forms_never_match`.** A name list with no DNS-ID matches
/// nothing under any choices, so a URI-ID or an SRV-ID never stands for one.
pub proof fn theorem_other_forms_never_match(q: MatchChoices, w: Seq<e::GeneralName>, k: nat, y: Seq<u8>)
    requires
        forall|m: int| k <= m < w.len() ==> !(#[trigger] w[m] is DNSName),
    ensures
        !some_dns_id_matches(q, w, k, y),
    decreases w.len() - k,
{
    if k < w.len() {
        assert(!(w[k as int] is DNSName));
        theorem_other_forms_never_match(q, w, k + 1, y);
    }
}

} // verus!
