//! The theorems of the path-validation design (§3.5), **stated**: each is a
//! spec predicate that P8 is to prove holds for every input (as a lemma
//! `lemma_<name>` with `ensures <predicate>(...)`, in `path/lemmas.rs`).
//! None is proven yet, so none may be cited as evidence; they are written
//! now so that the statements are reviewed with the spec they are about.
//! Where a statement re-derives something the spec computes (the pathLen
//! count, the explicit_policy trace), it does so independently of the fold,
//! so that the theorem says something the fold's own definition does not.
//!
//! One theorem is proven here because it is only an unfolding:
//! `lemma_candidate_reduces`, which reduces every path theorem about a
//! valid candidate (`verifier::candidate_valid`) to one about its path.
//!
//! The theorems about the enumeration (`thm_anchored`'s "every element is a
//! pool element, no pool index repeats" part for the builder,
//! `lemma_candidates_complete`, `thm_first_valid`) are P9's, with the
//! enumeration, and so is the theorem that P9's search examines exactly the
//! `order` on which `verifier::verify_server_chain_ensures` judges the
//! 200,000-step build budget. The set laws of name constraints
//! (`lemma_permitted_is_intersection`, `lemma_excluded_is_union`) are P4's,
//! and `lemma_from_unix_monotone` is P1's.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A path the verifier accepts: the profile and §6.1 both succeed.
pub open spec fn accepts(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> bool {
    super::profile::path_profile(anchor, certs, reference, now) is Ok
        && process(link, revoked, anchor, certs, now) is Ok
}

// ---------------------------------------------------------------------------
// The design's theorems (§3.5)
// ---------------------------------------------------------------------------

/// `thm_links_verify`: every link of an accepted path verifies under `link`:
/// certificate 1 under the anchor's key, certificate i+1 under certificate
/// i's (§6.1.3 (a)(1), §6.1.4 (d) to (f)).
pub open spec fn thm_links_verify(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
) -> bool {
    process(link, revoked, anchor, certs, now) is Ok ==> {
        &&& link(signed_data(anchor.spki_der, certs[0]))
        &&& forall|i: int| 0 < i < certs.len() ==>
            link(#[trigger] signed_data(certs[i - 1].tbs.subject_public_key_info_der, certs[i]))
    }
}

/// `thm_anchored`, the path part: §6.1's conditions (a) "the subject of
/// certificate x is the issuer of certificate x+1" and (b) "certificate 1 is
/// issued by the trust anchor", by name (byte equality), and no certificate
/// appears twice.
pub open spec fn thm_anchored(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
) -> bool {
    process(link, revoked, anchor, certs, now) is Ok ==> {
        &&& certs[0].tbs.issuer_der == anchor.subject_der
        &&& forall|i: int| 0 < i < certs.len() ==> (#[trigger] certs[i]).tbs.issuer_der == certs[i - 1].tbs.subject_der
        &&& forall|i: int, j: int| 0 <= i < j < certs.len() ==> (#[trigger] certs[i]).der != (#[trigger] certs[j]).der
    }
}

/// `thm_cas`: every intermediate of an accepted path is a v3 CA with
/// keyCertSign, an extKeyUsage absent or with serverAuth, no policyMappings
/// and only recognized critical extensions.
pub open spec fn thm_cas(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> bool {
    accepts(link, revoked, anchor, certs, reference, now) ==>
        forall|i: int| 0 <= i < certs.len() - 1 ==> {
            let cert = #[trigger] certs[i];
            &&& cert.tbs.version == 2
            &&& match cert.basic { Some(basic) => basic.ca, None => false }
            &&& match cert.key_usage {
                Some(usage) => crate::constraints::spec::key_usage_has(
                    usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
                None => false,
            }
            &&& match cert.eku {
                Some(eku) => crate::constraints::spec::eku_allows_server_auth(eku, false),
                None => true,
            }
            &&& !cert.has_policy_mappings
            &&& intermediate_critical_supported(cert.extensions, 0)
        }
}

/// The certificates of `certs[from..to]` that are not self-issued.
pub open spec fn non_self_issued_between(certs: Seq<super::parsed::spec::PathCert>, from: int, to: int) -> nat
    decreases to - from
{
    if from >= to || from < 0 || to > certs.len() { 0 }
    else { (if self_issued(certs[from]) { 0nat } else { 1nat }) + non_self_issued_between(certs, from + 1, to) }
}

/// `thm_path_len_respected`, declaratively (design §1.7): for each
/// intermediate i with pathLenConstraint p, at most p non-self-issued
/// intermediates follow it (§4.2.1.9: "the maximum number of
/// non-self-issued intermediate certificates that may follow this
/// certificate in a valid certification path"); and for an anchor with
/// pathLenConstraint p, at most p non-self-issued intermediates in all
/// (RFC 5937 §3.2 bullet 8).
pub open spec fn thm_path_len_respected(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
) -> bool {
    process(link, revoked, anchor, certs, now) is Ok ==> {
        &&& match anchor.path_len {
            Some(p) => non_self_issued_between(certs, 0, certs.len() - 1) <= p,
            None => true,
        }
        &&& forall|i: int| 0 <= i < certs.len() - 1 ==> match (#[trigger] certs[i]).basic {
            Some(basic) => match basic.path_len_constraint {
                Some(octets) => non_self_issued_between(certs, i + 1, certs.len() - 1)
                    <= super::parsed::spec::skip_certs_value(octets),
                None => true,
            },
            None => true,
        }
    }
}

/// `thm_names_constrained`: an accepted path satisfies P4's whole-path
/// name-constraint statement from the anchor's constraints: every
/// certificate's names (self-issued ones included) within the permitted
/// subtrees and outside the excluded subtrees of every NameConstraints above
/// it, the anchor's included.
pub open spec fn thm_names_constrained(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
) -> bool {
    process(link, revoked, anchor, certs, now) is Ok ==> match super::verifier::anchor_subtrees(anchor) {
        Some(initial) => crate::name_constraints::matching::spec::names_constrained(
            super::verifier::nc_path(certs), initial),
        None => false,
    }
}

/// `thm_valid_at_now`: every certificate of an accepted path, and the
/// anchor certificate, is valid at `now`.
pub open spec fn thm_valid_at_now(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> bool {
    accepts(link, revoked, anchor, certs, reference, now) ==> {
        &&& crate::time::spec::validity_contains(
            crate::time::spec::Validity { not_before: anchor.not_before, not_after: anchor.not_after }, now)
        &&& forall|i: int| 0 <= i < certs.len() ==>
            crate::time::spec::validity_contains(validity(#[trigger] certs[i]), now)
    }
}

/// `thm_leaf_profile`: the target of an accepted path passes the leaf
/// checks, has an extKeyUsage and no nameConstraints, and the key the path
/// returns is the target's SubjectPublicKeyInfo.
pub open spec fn thm_leaf_profile(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> bool {
    accepts(link, revoked, anchor, certs, reference, now) ==> {
        let leaf = certs.last();
        &&& crate::leaf::spec::check_extensions(leaf.extensions, leaf.tbs, reference, now,
            super::profile::leaf_policy()) is Some
        &&& leaf.eku is Some
        &&& leaf.name_constraints is None
        &&& process(link, revoked, anchor, certs, now)
            == Ok::<Seq<u8>, PathError>(leaf.tbs.subject_public_key_info_der)
    }
}

/// The value of explicit_policy when §6.1.3 (f) runs on `certs[i]` (the
/// RFC's certificate i+1), re-derived step by step from §6.1.2 (d), §6.1.4
/// (h)(1) and (i)(1), independently of the fold.
pub open spec fn explicit_policy_at(certs: Seq<super::parsed::spec::PathCert>, i: int) -> nat
    decreases i
{
    if i <= 0 || i > certs.len() { certs.len() + 1 }
    else {
        let previous = certs[i - 1];
        let before = explicit_policy_at(certs, i - 1);
        let after_h = if !self_issued(previous) && before > 0 { (before - 1) as nat } else { before };
        match previous.require_explicit_policy {
            Some(r) => if r < after_h { r } else { after_h },
            None => after_h,
        }
    }
}

/// The value of explicit_policy at the end of §6.1.5 (a), (b), re-derived.
pub open spec fn explicit_policy_final(certs: Seq<super::parsed::spec::PathCert>) -> nat {
    let before = explicit_policy_at(certs, certs.len() - 1);
    let after_a = if before > 0 { (before - 1) as nat } else { before };
    if certs.last().require_explicit_policy == Some(0nat) { 0 } else { after_a }
}

/// `lemma_policy_free_sound` (design §1.2), as a statement: when §6.1
/// accepts here, the RFC's own policy conditions, §6.1.3 (f) "either
/// explicit_policy is greater than 0 or the valid_policy_tree is not equal
/// to NULL" for every certificate and §6.1.5's "(1) the value of
/// explicit_policy variable is greater than zero or (2) the valid_policy_tree
/// is not NULL", hold for **every** value of the tree. `tree_null[i]` says
/// whether the tree is NULL at certificate i+1's step (f), and
/// `tree_null[n]` at the wrap-up; nothing else in §6.1 reads the tree, so
/// these are the only places it could change the outcome.
pub open spec fn policy_free_sound(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
) -> bool {
    process(link, revoked, anchor, certs, now) is Ok ==>
        forall|tree_null: Seq<bool>| #![trigger tree_null.len()] tree_null.len() == certs.len() + 1 ==> {
            &&& forall|i: int| 0 <= i < certs.len() ==>
                (#[trigger] explicit_policy_at(certs, i) > 0 || !tree_null[i])
            &&& (explicit_policy_final(certs) > 0 || !tree_null[certs.len() as int])
        }
}

/// Every theorem above, for one path. P8's target: `forall` inputs,
/// `all_path_theorems(...)`.
pub open spec fn all_path_theorems(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> bool {
    &&& thm_links_verify(link, revoked, anchor, certs, now)
    &&& thm_anchored(link, revoked, anchor, certs, now)
    &&& thm_cas(link, revoked, anchor, certs, reference, now)
    &&& thm_path_len_respected(link, revoked, anchor, certs, now)
    &&& thm_names_constrained(link, revoked, anchor, certs, now)
    &&& thm_valid_at_now(link, revoked, anchor, certs, reference, now)
    &&& thm_leaf_profile(link, revoked, anchor, certs, reference, now)
    &&& policy_free_sound(link, revoked, anchor, certs, now)
}

// ---------------------------------------------------------------------------
// Proven: a valid candidate is an accepted path
// ---------------------------------------------------------------------------

/// A valid candidate's path is accepted, under the candidate's anchor, and
/// its key is §6.1's output. So every theorem above, once proven, holds of
/// every candidate the verifier may return.
pub proof fn lemma_candidate_reduces(
    environment: super::verifier::Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    candidate: super::verifier::Candidate, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
)
    requires super::verifier::candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
    ensures
        candidate.anchor < anchors.len(),
        accepts(environment.link, environment.revoked, anchors[candidate.anchor as int],
            super::verifier::candidate_certificates(pool, leaf, candidate), reference, now),
        super::verifier::candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now)
            == process(environment.link, environment.revoked, anchors[candidate.anchor as int],
                super::verifier::candidate_certificates(pool, leaf, candidate), now),
        super::verifier::candidate_certificates(pool, leaf, candidate).last() == leaf,
{
}

} // verus!
