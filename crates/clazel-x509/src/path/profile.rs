//! The browser profile layered on RFC 5280 §6.1 (`spec.rs`): the CA/Browser
//! Forum Baseline Requirements and what Chrome and Firefox refuse beyond the
//! RFC, for a TLS server certificate path.
//!
//! Sources, pinned:
//! - CA/Browser Forum Baseline Requirements v2.3.1, 4 October 2026,
//!   `cabforum/servercert` commit `3574ae809e5f909b58ee4c26b7bac4a3b9e78421`,
//!   `docs/BR.md`, SHA-256
//!   `ee4e4e95ba0f3fa1e11cb0dc01b2337aa26e88b8c7724c78f25e5743fc1e151e`.
//!   §7.1.2.6.1 (TLS subordinate CA extensions: keyUsage MUST), §7.1.2.7.6
//!   (subscriber extensions: extKeyUsage MUST, nameConstraints MUST NOT),
//!   §7.1.2.7.10 (subscriber EKU), §7.1.2.10.6 (CA EKU), §7.1.2.10.7 (CA key
//!   usage: keyCertSign required).
//! - RFC 5280 (pinned in `spec.rs`): §4.2.1.10 ("The name constraints
//!   extension, which MUST be used only in a CA certificate"), §4.2.1.12.
//! - NSS `certdata.txt` `CKA_NSS_SERVER_DISTRUST_AFTER`, as carried by
//!   `roots::Root::server_distrust_after` and decoded into
//!   `Anchor::server_distrust_after` (`parsed/spec.rs`).
//! - Browser behaviour: Chrome (BoringSSL `pki/`) and Firefox (NSS
//!   `lib/mozpkix/`), as the design records it (§1.4, §1.8, §4.2) and as
//!   `name_constraints/matching/spec.rs` read it on 2026-10-29. A statement
//!   about a browser that neither of those confirms is marked
//!   *unconfirmed*. The principle (Alex, 2026-10-29): accept only where both
//!   browsers accept; where they differ, follow the stricter. Each check
//!   below is a refusal the RFC does not make, marked **(R)**, with the
//!   source it follows.
//! - The path-validation design (not in the repository): §1.4, §1.7, §1.8,
//!   questions Q6, Q7 and Q9.
//!
//! Modelling choices:
//! - **This only refuses.** Every function is a conjunction of conditions on
//!   top of `spec::process`; nothing here can make a path that §6.1 refuses
//!   acceptable.
//! - **The target certificate** (`certs[n-1]`):
//!   - `leaf::spec::check_extensions` with `allow_any_extended_key_usage`
//!     false: a subjectAltName with only dNSName and iPAddress entries, one
//!     of which matches the reference identity (RFC 9525; CN is never used);
//!     keyUsage, if present, with digitalSignature (RFC 8446 §4.4.2.2); not a
//!     CA (basicConstraints cA FALSE or absent; keyCertSign only with cA);
//!     extKeyUsage, if present, with serverAuth (anyExtendedKeyUsage is not
//!     enough); valid at `now`. §6.1 allows a CA certificate as the target
//!     when its key is used for another purpose; refusing it here is
//!     `leaf/spec.rs`'s existing rule.
//!   - **(R) extKeyUsage must be present** (design Q7; BR §7.1.2.7.6
//!     "extKeyUsage MUST", §7.1.2.7.10 serverAuth MUST; limbo
//!     `webpki::eku::ee-without-eku` FAILURE). Both browsers accept a target
//!     without extKeyUsage.
//!   - **(R) nameConstraints must be absent** (RFC 5280 §4.2.1.10 "MUST be
//!     used only in a CA certificate"; BR §7.1.2.7.6 "nameConstraints MUST
//!     NOT"; limbo `rfc5280::nc::not-allowed-in-ee-noncritical` and
//!     `-critical`, both FAILURE), critical or not. A critical one is also
//!     refused by §6.1.5 (f). §6.1 never processes the target's own
//!     constraints; whether the browsers refuse it is *unconfirmed*.
//! - **Each intermediate** (`certs[0..n-1]`):
//!   - **(R) keyUsage must be present** (design Q6; BR §7.1.2.6.1 "keyUsage
//!     MUST", §7.1.2.10.7 keyCertSign required). §6.1.4 (n) checks
//!     keyCertSign only when keyUsage is present, and that check stays in
//!     `spec.rs`. Both browsers accept an intermediate without keyUsage.
//!   - **(R) extKeyUsage, if present, must contain serverAuth** (design
//!     §1.8; BR §7.1.2.10.6 "anyExtendedKeyUsage | MUST NOT"). anyExtendedKeyUsage
//!     is not accepted in its place, as in mozilla::pkix and webpki (design
//!     §1.8); Chrome's treatment of it is *unconfirmed*, and refusing is the
//!     stricter either way. Absent extKeyUsage is unrestricted, as in both
//!     browsers.
//! - **The anchor:**
//!   - **(R) The anchor certificate must be valid at `now`** (design Q9).
//!     RFC 5280 makes the anchor an input, not a certificate, and does not
//!     check it, nor does webpki. Whether Firefox and Chrome check the
//!     root's own validity is *unconfirmed* (design Q9: "Unverified: whether
//!     Chrome enforces root expiry"); refusing is the stricter either way.
//!   - **(R) `server_distrust_after`** (NSS `CKA_NSS_SERVER_DISTRUST_AFTER`;
//!     Firefox): a target whose notBefore is after the anchor's
//!     distrust-after time is refused. Equal is accepted ("after" is strict).
//!     Chrome's root store has its own distrust mechanism (*unconfirmed*
//!     whether it covers the same roots); applying NSS's is the stricter.
//!   - The anchor's role and extKeyUsage checks (design Q9) are
//!     `parsed::spec::anchor_from_root`'s, so they hold of every `Anchor`.
//! - **Order of failure:** the target first (so that identity, expiry and a
//!   CA-as-leaf are reported whatever the path; design §2.6 step 2), then
//!   the anchor, then the intermediates from certificate 1 down. Only the
//!   reported reason depends on it.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The leaf policy of this profile: anyExtendedKeyUsage is not serverAuth.
pub open spec fn leaf_policy() -> crate::leaf::spec::LeafPolicy {
    crate::leaf::spec::LeafPolicy { allow_any_extended_key_usage: false }
}

/// The target certificate's checks.
pub open spec fn leaf_profile(
    leaf: super::parsed::spec::PathCert, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> Result<(), super::spec::PathError> {
    // 1. Identity, keyUsage, role, extKeyUsage if present, and validity
    //    (`leaf::spec::check_extensions`).
    if crate::leaf::spec::check_extensions(leaf.extensions, leaf.tbs, reference, now, leaf_policy()) is None {
        Err(super::spec::PathError::Leaf)
    }
    // 2. (R) BR §7.1.2.7.6: "extKeyUsage | MUST" (design Q7).
    else if leaf.eku is None { Err(super::spec::PathError::ExtendedKeyUsage) }
    // 3. (R) RFC 5280 §4.2.1.10, BR §7.1.2.7.6: "nameConstraints | MUST NOT".
    else if leaf.name_constraints is Some { Err(super::spec::PathError::LeafNameConstraints) }
    else { Ok(()) }
}

/// One intermediate's checks.
pub open spec fn intermediate_profile(cert: super::parsed::spec::PathCert) -> Result<(), super::spec::PathError> {
    // 1. (R) BR §7.1.2.6.1: "keyUsage | MUST" (design Q6).
    if cert.key_usage is None { Err(super::spec::PathError::KeyUsage) }
    // 2. (R) BR §7.1.2.10.6, design §1.8: extKeyUsage absent, or with serverAuth.
    else if match cert.eku {
        Some(eku) => !crate::constraints::spec::eku_allows_server_auth(eku, false),
        None => false,
    } { Err(super::spec::PathError::ExtendedKeyUsage) }
    else { Ok(()) }
}

/// The intermediates' checks for `certs[i..n-1]`, certificate i+1 first.
pub open spec fn intermediates_profile_from(certs: Seq<super::parsed::spec::PathCert>, i: int)
    -> Result<(), super::spec::PathError>
    decreases certs.len() - i
{
    if i < 0 || i >= certs.len() - 1 { Ok(()) }
    else { match intermediate_profile(certs[i]) {
        Err(e) => Err(e),
        Ok(()) => intermediates_profile_from(certs, i + 1),
    }}
}

/// The anchor's checks against `now` and the target.
pub open spec fn anchor_profile(
    anchor: super::parsed::spec::Anchor, leaf: super::parsed::spec::PathCert,
    now: crate::time::spec::CertificateTime,
) -> Result<(), super::spec::PathError> {
    // 1. (R) Design Q9: the anchor certificate is valid at `now`.
    if !crate::time::spec::validity_contains(
        crate::time::spec::Validity { not_before: anchor.not_before, not_after: anchor.not_after }, now) {
        Err(super::spec::PathError::AnchorExpired)
    }
    // 2. (R) NSS CKA_NSS_SERVER_DISTRUST_AFTER: refuse a target whose
    //    notBefore is after the distrust-after time.
    else if match anchor.server_distrust_after {
        Some(after) => !crate::time::spec::time_le(leaf.tbs.not_before, after),
        None => false,
    } { Err(super::spec::PathError::Distrusted) }
    else { Ok(()) }
}

/// The profile of a whole path: target, then anchor, then intermediates.
pub open spec fn path_profile(
    anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> Result<(), super::spec::PathError> {
    if certs.len() == 0 { Err(super::spec::PathError::EmptyPath) }
    else { match leaf_profile(certs.last(), reference, now) {
        Err(e) => Err(e),
        Ok(()) => match anchor_profile(anchor, certs.last(), now) {
            Err(e) => Err(e),
            Ok(()) => intermediates_profile_from(certs, 0),
        },
    }}
}

} // verus!
