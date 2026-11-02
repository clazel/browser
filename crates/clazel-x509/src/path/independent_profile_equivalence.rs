//! The independent transcription of the CA/B Forum Baseline Requirements'
//! extKeyUsage and keyUsage rules (`independent_profile.rs`, path piece P15,
//! written by a separate agent without reading `profile.rs`) compared with
//! what this crate's verifier decides about the same two extensions, and
//! **proven equal** on a stated domain: `thm_p15_equivalence`.
//!
//! What "this crate's verifier decides" means. The transcription covers only
//! extKeyUsage and keyUsage. On our side those are read in three places, all
//! collected in [`ours_usage`] and each cited where it is restated:
//! - `profile.rs`: the target has an extKeyUsage (leaf step 2); each
//!   intermediate has a keyUsage (intermediate step 1) and an extKeyUsage
//!   absent or with serverAuth, anyExtendedKeyUsage not counting
//!   (intermediate step 2).
//! - `leaf/spec.rs` `check_extensions`, run by `profile.rs` on the target
//!   with `leaf_policy()`: a keyUsage, if present, has digitalSignature
//!   (step 2); keyCertSign only with cA, and the target is not a CA, so no
//!   keyCertSign (step 3, `basic_constraints_compatible`); an extKeyUsage, if
//!   present, has serverAuth, anyExtendedKeyUsage not counting (step 4).
//! - `spec.rs` §6.1.4 (n): an intermediate's keyUsage, if present, has
//!   keyCertSign.
//!
//! `thm_p15_ours_usage_necessary` proves every one of these holds of a path
//! `theorems::accepts` accepts, so [`ours_usage`] adds no condition the
//! verifier does not make. `thm_p15_ours_usage_sufficient` proves the
//! converse guard by guard: when [`ours_usage`] holds, each of the checks
//! above passes, so none of them refuses. That no *other* check of the
//! verifier reads keyUsage or extKeyUsage is by inspection, not proven: the
//! other guards of `check_extensions` read the critical-extension OIDs, the
//! subjectAltName, basicConstraints' cA and pathLenConstraint (the
//! pathLenConstraint clause of `basic_constraints_compatible` reads
//! keyCertSign, but a target with a pathLenConstraint is refused whatever
//! its keyUsage: without keyCertSign by that clause, with it by the cA
//! clause), and the validity; `profile.rs`'s other checks read
//! nameConstraints, the anchor's validity and `server_distrust_after`; and
//! no step of `spec::process` other than (n) reads `key_usage` or `eku`.
//!
//! The order of the path. `spec.rs` and `profile.rs` take `certs` with the
//! certificate the trust anchor signed first and the target last (RFC 5280
//! certificate 1 to n). The transcription takes the target first, "each
//! certificate issued by the next". So its path is `certs.reverse()`.
//!
//! The transcription's choice. Its entry point,
//! `tls_server_path_profile_ok`, passes `allow_unrestricted_ca_eku = true`:
//! an intermediate without extKeyUsage, or with anyExtendedKeyUsage alone,
//! is accepted (BR §7.1.2.2.3, §7.1.2.2.4). That is the function compared
//! here. With `false` an intermediate without extKeyUsage is refused, which
//! `profile.rs` accepts (as both browsers do), so the other choice would add
//! a domain condition, not remove one.
//!
//! The domain (`p15_domain`). Each condition excludes a real disagreement;
//! outside it the verdicts differ, and nothing here claims they agree there.
//! In every case but 3 and part of 5 the transcription refuses what we
//! accept: the BR are written for issuers, and `profile.rs` follows the
//! browsers ("accept only where both browsers accept"), which do not enforce
//! these rows.
//! 1. **The target's extKeyUsage lists none of codeSigning,
//!    emailProtection, timeStamping, OCSPSigning, anyExtendedKeyUsage or
//!    Precertificate Signing** beside serverAuth (BR §7.1.2.7.10 "MUST NOT";
//!    `profile.rs` requires serverAuth and does not refuse extra purposes;
//!    x509-limbo `webpki::eku::ee-anyeku` and `ee-critical-eku` sit in the
//!    same place).
//! 2. **The target's keyUsage, if present, is for an RSA or ECC key and sets
//!    none of nonRepudiation, cRLSign, encipherOnly or decipherOnly; for RSA
//!    not keyAgreement, for ECC neither keyEncipherment nor
//!    dataEncipherment** (BR §7.1.2.7.11's "N" rows; §7.1.3.1 allows only RSA
//!    and ECC keys). `check_extensions` asks only for digitalSignature and no
//!    keyCertSign. keyCertSign is not a domain condition: both refuse it.
//! 3. **The target's RSA keyUsage, if it sets keyEncipherment or
//!    dataEncipherment, also sets digitalSignature.** The BR accept an RSA
//!    subscriber with keyEncipherment or dataEncipherment alone (§7.1.2.7.11,
//!    the Note: "at least one"); `check_extensions` step 2 requires
//!    digitalSignature, which a TLS 1.3 server's CertificateVerify needs
//!    (RFC 8446 §4.4.2.2). Here we refuse what the transcription accepts.
//! 4. **An intermediate whose keyUsage sets keyCertSign also sets cRLSign
//!    and none of nonRepudiation, keyEncipherment, dataEncipherment,
//!    keyAgreement, encipherOnly or decipherOnly** (BR §7.1.2.10.7: cRLSign
//!    "Required Y", the others "Permitted N"). We need only keyCertSign
//!    (§6.1.4 (n)) and its presence (`profile.rs`, BR §7.1.2.6.1).
//! 5. **An intermediate's extKeyUsage, if present, lists none of
//!    codeSigning, emailProtection, timeStamping, OCSPSigning,
//!    anyExtendedKeyUsage or Precertificate Signing.** Beside serverAuth the
//!    BR forbid them (§7.1.2.10.6) and we accept them. anyExtendedKeyUsage
//!    *alone* is the other way round: the transcription accepts it as an
//!    unrestricted cross-certificate (§7.1.2.2.4), and `profile.rs` refuses
//!    it, following mozilla::pkix and webpki (design §1.8).
//!
//! Within the domain the two agree on: the target must have an extKeyUsage
//! with serverAuth; a target keyUsage needs digitalSignature (ECC: BR
//! "MUST"; RSA: by condition 3) and must not set keyCertSign; every
//! intermediate must have a keyUsage with keyCertSign; and an intermediate's
//! extKeyUsage is absent or lists serverAuth.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The decoded certificate of a path.
pub type PathCert = super::parsed::spec::PathCert;
/// The decoder's keyUsage bit names.
pub type KeyUsageBit = crate::constraints::spec::KeyUsageBit;

// ---------------------------------------------------------------------
// Our side: the keyUsage and extKeyUsage conditions of the verifier.
// ---------------------------------------------------------------------

/// The target's keyUsage and extKeyUsage conditions (RFC 5280 certificate n).
pub open spec fn ours_leaf_usage(leaf: PathCert) -> bool {
    // `leaf/spec.rs` check_extensions step 2: "If KeyUsage is present, TLS
    // 1.3 server auth needs digitalSignature."
    &&& match leaf.key_usage {
        Some(u) => crate::constraints::spec::key_usage_has(u, KeyUsageBit::DigitalSignature),
        None => true,
    }
    // check_extensions step 3: keyCertSign only with cA, and not a CA.
    &&& match leaf.key_usage {
        Some(u) => !crate::constraints::spec::key_usage_has(u, KeyUsageBit::KeyCertSign),
        None => true,
    }
    // `profile.rs` leaf step 2 (present) and check_extensions step 4 with
    // `profile::leaf_policy()` (serverAuth; anyExtendedKeyUsage is not enough).
    &&& match leaf.eku {
        Some(e) => crate::constraints::spec::eku_allows_server_auth(
            e, super::profile::leaf_policy().allow_any_extended_key_usage),
        None => false,
    }
}

/// One intermediate's keyUsage and extKeyUsage conditions.
pub open spec fn ours_intermediate_usage(cert: PathCert) -> bool {
    // `profile.rs` intermediate step 1 (present) and `spec.rs` §6.1.4 (n)
    // (keyCertSign).
    &&& match cert.key_usage {
        Some(u) => crate::constraints::spec::key_usage_has(u, KeyUsageBit::KeyCertSign),
        None => false,
    }
    // `profile.rs` intermediate step 2: absent, or with serverAuth.
    &&& match cert.eku {
        Some(e) => crate::constraints::spec::eku_allows_server_auth(e, false),
        None => true,
    }
}

/// The verifier's keyUsage and extKeyUsage conditions on a path, in RFC
/// 5280 order (target last).
pub open spec fn ours_usage(certs: Seq<PathCert>) -> bool {
    &&& certs.len() >= 1
    &&& ours_leaf_usage(certs.last())
    &&& forall|i: int| 0 <= i < certs.len() - 1 ==> ours_intermediate_usage(#[trigger] certs[i])
}

/// The transcription's verdict on the same path (target first).
pub open spec fn theirs(certs: Seq<PathCert>) -> bool {
    super::independent_profile::tls_server_path_profile_ok(certs.reverse())
}

// ---------------------------------------------------------------------
// The domain.
// ---------------------------------------------------------------------

/// Whether `eku` lists one of the six purposes both BR tables mark "MUST
/// NOT" (domain conditions 1 and 5).
pub open spec fn eku_lists_forbidden(eku: crate::constraints::spec::ExtendedKeyUsage) -> bool {
    let p = eku.purposes;
    ||| crate::constraints::spec::oid_in(p, seq![1nat, 3, 6, 1, 5, 5, 7, 3, 3], 0) // codeSigning
    ||| crate::constraints::spec::oid_in(p, seq![1nat, 3, 6, 1, 5, 5, 7, 3, 4], 0) // emailProtection
    ||| crate::constraints::spec::oid_in(p, seq![1nat, 3, 6, 1, 5, 5, 7, 3, 8], 0) // timeStamping
    ||| crate::constraints::spec::oid_in(p, seq![1nat, 3, 6, 1, 5, 5, 7, 3, 9], 0) // OCSPSigning
    ||| crate::constraints::spec::oid_in(p, crate::constraints::spec::any_extended_key_usage_oid(), 0)
    ||| crate::constraints::spec::oid_in(p, seq![1nat, 3, 6, 1, 4, 1, 11129, 2, 4, 4], 0) // Precertificate Signing
}

/// Whether the keyUsage asserts `bit`.
pub open spec fn ku_set(u: crate::constraints::spec::KeyUsage, bit: KeyUsageBit) -> bool {
    crate::constraints::spec::key_usage_has(u, bit)
}

/// Domain conditions 1 to 3, on the target.
pub open spec fn leaf_in_domain(leaf: PathCert) -> bool {
    // 1.
    &&& match leaf.eku { Some(e) => !eku_lists_forbidden(e), None => true }
    // 2. and 3.
    &&& match leaf.key_usage {
        None => true,
        Some(u) => {
            let kind = super::independent_profile::key_kind_of_spki(leaf.tbs.subject_public_key_info_der);
            &&& !ku_set(u, KeyUsageBit::ContentCommitment)
            &&& !ku_set(u, KeyUsageBit::CrlSign)
            &&& !ku_set(u, KeyUsageBit::EncipherOnly)
            &&& !ku_set(u, KeyUsageBit::DecipherOnly)
            &&& match kind {
                super::independent_profile::KeyKind::Rsa =>
                    !ku_set(u, KeyUsageBit::KeyAgreement)
                    && ((ku_set(u, KeyUsageBit::KeyEncipherment) || ku_set(u, KeyUsageBit::DataEncipherment))
                        ==> ku_set(u, KeyUsageBit::DigitalSignature)),
                super::independent_profile::KeyKind::Ecc =>
                    !ku_set(u, KeyUsageBit::KeyEncipherment) && !ku_set(u, KeyUsageBit::DataEncipherment),
                super::independent_profile::KeyKind::Other => false,
            }
        },
    }
}

/// Domain conditions 4 and 5, on one intermediate.
pub open spec fn intermediate_in_domain(cert: PathCert) -> bool {
    // 4.
    &&& match cert.key_usage {
        Some(u) => ku_set(u, KeyUsageBit::KeyCertSign) ==> {
            &&& ku_set(u, KeyUsageBit::CrlSign)
            &&& !ku_set(u, KeyUsageBit::ContentCommitment)
            &&& !ku_set(u, KeyUsageBit::KeyEncipherment)
            &&& !ku_set(u, KeyUsageBit::DataEncipherment)
            &&& !ku_set(u, KeyUsageBit::KeyAgreement)
            &&& !ku_set(u, KeyUsageBit::EncipherOnly)
            &&& !ku_set(u, KeyUsageBit::DecipherOnly)
        },
        None => true,
    }
    // 5.
    &&& match cert.eku { Some(e) => !eku_lists_forbidden(e), None => true }
}

/// The domain of `thm_p15_equivalence`, in RFC 5280 order.
pub open spec fn p15_domain(certs: Seq<PathCert>) -> bool {
    &&& certs.len() >= 1 ==> leaf_in_domain(certs.last())
    &&& forall|i: int| 0 <= i < certs.len() - 1 ==> intermediate_in_domain(#[trigger] certs[i])
}

/// The decoded fields of `c` are those of its extensions, as
/// `parsed::spec::parse_path_cert` builds them (`lemma_parsed_consistent`).
pub open spec fn fields_consistent(c: PathCert) -> bool {
    &&& crate::leaf::spec::optional_basic_constraints(c.extensions) == Some(c.basic)
    &&& crate::leaf::spec::optional_key_usage(c.extensions) == Some(c.key_usage)
    &&& crate::leaf::spec::optional_extended_key_usage(c.extensions) == Some(c.eku)
}

// ---------------------------------------------------------------------
// The theorems.
// ---------------------------------------------------------------------

/// `thm_p15_equivalence`: on the domain, the verifier's keyUsage and
/// extKeyUsage conditions and the transcription's verdict are the same.
pub open spec fn thm_p15_equivalence(certs: Seq<PathCert>) -> bool {
    p15_domain(certs) ==> (ours_usage(certs) == theirs(certs))
}

/// `thm_p15_ours_usage_necessary`: a path the verifier accepts meets
/// [`ours_usage`], when its target's fields are its extensions'.
pub open spec fn thm_p15_ours_usage_necessary(
    link: super::spec::LinkFn, revoked: super::spec::RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<PathCert>, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime,
) -> bool {
    (super::theorems::accepts(link, revoked, anchor, certs, reference, now)
        && certs.len() >= 1 && fields_consistent(certs.last()))
        ==> ours_usage(certs)
}

/// `thm_p15_ours_usage_sufficient`: when [`ours_usage`] holds, every check
/// listed in the module documentation passes: `profile.rs`'s intermediate
/// checks and the target's extKeyUsage presence, §6.1.4 (n), and
/// check_extensions' steps 2 and 4 and the keyCertSign half of step 3, read
/// from the target's extensions as check_extensions reads them.
pub open spec fn thm_p15_ours_usage_sufficient(certs: Seq<PathCert>) -> bool {
    (ours_usage(certs) && fields_consistent(certs.last())) ==> {
        let leaf = certs.last();
        &&& super::profile::intermediates_profile_from(certs, 0) is Ok
        &&& leaf.eku is Some
        &&& forall|i: int| 0 <= i < certs.len() - 1 ==> match (#[trigger] certs[i]).key_usage {
            Some(u) => crate::constraints::spec::key_usage_has(u, KeyUsageBit::KeyCertSign),
            None => true,
        }
        &&& match crate::leaf::spec::optional_key_usage(leaf.extensions) {
            Some(Some(u)) => crate::constraints::spec::key_usage_has(u, KeyUsageBit::DigitalSignature)
                && !crate::constraints::spec::key_usage_has(u, KeyUsageBit::KeyCertSign),
            _ => true,
        }
        &&& match crate::leaf::spec::optional_extended_key_usage(leaf.extensions) {
            Some(Some(e)) => crate::constraints::spec::eku_allows_server_auth(
                e, super::profile::leaf_policy().allow_any_extended_key_usage),
            _ => true,
        }
    }
}

/// `thm_p15_domain_inhabited`: the domain holds of a path both sides
/// accept, so `thm_p15_equivalence` is not vacuous (proven by
/// `lemma_domain_inhabited` on a two-certificate path).
pub open spec fn thm_p15_domain_inhabited() -> bool {
    exists|certs: Seq<PathCert>| p15_domain(certs) && ours_usage(certs) && theirs(certs) && certs.len() == 2
}

} // verus!
