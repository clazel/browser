//! An independent transcription of the extendedKeyUsage and keyUsage
//! requirements that the CA/Browser Forum TLS Baseline Requirements put on
//! the certificates of a TLS server path, read as a relying party's
//! acceptance check. Written without reading the existing browser profile or
//! any of the files that implement or prove it (the files that were not
//! opened are listed in the pull request that adds this one); the equivalence
//! proof against that profile is a later change by a different session.
//!
//! Sources, downloaded on 30 October 2026 and hashed with SHA-256:
//! - CA/Browser Forum, *Baseline Requirements for the Issuance and
//!   Management of Publicly-Trusted TLS Server Certificates*, **version
//!   2.3.1, 4 October 2026** (the version <https://cabforum.org/working-groups/server/baseline-requirements/documents/>
//!   lists as current). Text read from the Forum's markdown source,
//!   `docs/BR.md` at commit `3574ae809e5f909b58ee4c26b7bac4a3b9e78421` of
//!   <https://github.com/cabforum/servercert>, SHA-256
//!   `ee4e4e95ba0f3fa1e11cb0dc01b2337aa26e88b8c7724c78f25e5743fc1e151e`. The
//!   published PDF `CA-Browser-Forum-TLS-BR-2.3.1.pdf` (SHA-256
//!   `2cbcf36358e727681177ecc8bcd1b71e0567df70402adc64e3a805a6a3106600`)
//!   was downloaded too, but no PDF text extractor was available, so it was
//!   not compared with the markdown beyond the version number and date.
//!   Used: §7.1.2 (the profile list), §7.1.2.1 and §7.1.2.1.2 (root),
//!   §7.1.2.2 to §7.1.2.2.5 (cross-certified subordinate CA), §7.1.2.3.3,
//!   §7.1.2.4.2 (non-TLS and precertificate-signing CAs, to know what they
//!   are), §7.1.2.5.1 and §7.1.2.6.1 (TLS subordinate CAs), §7.1.2.7.6,
//!   §7.1.2.7.10 and §7.1.2.7.11 (subscriber), §7.1.2.10.6 and §7.1.2.10.7
//!   (common CA fields). Cited below as `BR §…`.
//! - Mozilla Root Store Policy, **version 3.1, effective 1 July 2026**,
//!   `rootstore/policy.md` of <https://github.com/mozilla/pkipolicy>, last
//!   commit `e9ea0883af380dfa5d61b1d8a991f21e743206e5` (26 June 2026),
//!   SHA-256 `0e39e12a7251b5011c86cbc83355eb63dd0b82ca33019f5ccafad6cc7ffb59db`.
//!   Used only for §5.3 and §5.3.1 (intermediate certificates), as a backup
//!   where the BR leave a question open. Cited as `Mozilla §…`.
//!
//! Direction. The BR are written for issuers ("MUST contain"). This file is
//! the relying party's reading: **a certificate the BR forbid is refused, one
//! they allow is accepted.** "MUST" and "MUST NOT" rows decide. "SHOULD",
//! "MAY", "NOT RECOMMENDED" and "RECOMMENDED" rows never refuse.
//!
//! Scope. Only extendedKeyUsage and keyUsage (and, to choose the keyUsage
//! table, the kind of the subject public key). Not here: criticality of
//! these extensions, basicConstraints, nameConstraints, certificatePolicies
//! and every other row of the BR profiles; RFC 5280 §6.1 itself.
//!
//! Modelling choices.
//! - **The path** is a `Seq<PathCert>`, leaf first, each certificate issued
//!   by the next; the last is issued by the trust anchor, which is not in
//!   the sequence. An empty sequence is refused. Position decides the
//!   profile: index 0 is the subscriber certificate (BR §7.1.2.7), every
//!   later index is a subordinate CA certificate (BR §7.1.2.2, §7.1.2.5,
//!   §7.1.2.6). Whether a certificate really is a CA (basicConstraints) is
//!   RFC 5280 §6.1's business, not modelled.
//! - **The trust anchor is exempt.** The root profile (BR §7.1.2.1.2) says
//!   extKeyUsage "MUST NOT" and keyUsage per §7.1.2.10.7, but an anchor is a
//!   trust decision of the root store, not a certificate the relying party
//!   checks against the BR, and `Anchor` has no EKU or keyUsage. Only
//!   subordinate CAs are checked.
//! - **Cross-certificates.** BR §7.1.2.2.3 lets an *unrestricted*
//!   cross-certified subordinate CA omit extKeyUsage (SHOULD) or carry
//!   anyExtendedKeyUsage alone (§7.1.2.2.4); Mozilla §5.3 exempts
//!   "cross-certificates that share a private key with a corresponding root
//!   certificate" from its EKU rules in the same way. A relying party cannot
//!   tell, from one certificate, whether it is such a cross-certificate (the
//!   test compares organization names of issuer and subject and the
//!   operators), so **an intermediate without extKeyUsage, or with
//!   anyExtendedKeyUsage as its only purpose, is accepted** when
//!   `allow_unrestricted_ca_eku` is true, and refused when it is false. The
//!   entry point [`tls_server_path_profile_ok`] passes true; the other
//!   choice is available as [`tls_server_path_profile_ok_with`], so that the
//!   consequence of the permissive reading can be examined. In every other
//!   case anyExtendedKeyUsage is refused (BR §7.1.2.10.6, §7.1.2.7.10,
//!   §7.1.2.2.4 "the only key usage present", Mozilla §5.3).
//! - **EKU chaining.** The path is for the purpose id-kp-serverAuth. A
//!   subordinate CA's extKeyUsage restricts the purposes of everything it
//!   issues (BR §7.1.2.2.3 footnote: "limiting the scope of CA
//!   Certificates, as implemented by a number of Application Software
//!   Suppliers"), so every subordinate CA must permit serverAuth: it is
//!   listed (BR §7.1.2.10.6, "MUST"), or the unrestricted forms above apply.
//!   The leaf must list it (BR §7.1.2.7.10). Nothing else is intersected: the
//!   BR do not require a leaf's other purposes (clientAuth) to be among its
//!   issuer's, and a TLS server path only asks about serverAuth.
//!   [`lemma_ca_permits_server_auth`] and [`lemma_leaf_has_server_auth`]
//!   prove that an accepted path has this property.
//! - **A subordinate CA's extKeyUsage** is accepted if it has the shape of
//!   BR §7.1.2.10.6 (serverAuth listed, no codeSigning, emailProtection,
//!   timeStamping, OCSPSigning, anyExtendedKeyUsage or precertificate
//!   signing), or an unrestricted form as above. The TLS subordinate CA
//!   profiles (§7.1.2.5.1, §7.1.2.6.1) refer to §7.1.2.10.6; the restricted
//!   cross-certificate table of §7.1.2.2.5 is the same except that it omits
//!   the OCSPSigning and precertificate-signing rows: see the entry "BR
//!   §7.1.2.2.5 omits two rows of §7.1.2.10.6" in `docs/ERRATA.md`. We
//!   apply §7.1.2.10.6 to every subordinate CA. The non-TLS and
//!   precertificate-signing CA profiles (§7.1.2.3.3, §7.1.2.4.2) forbid
//!   serverAuth, so a CA certificate of those kinds is refused by the
//!   serverAuth requirement and needs no case of its own.
//! - **"Any other value" rows are NOT RECOMMENDED**, so EKU purposes other
//!   than those the tables name are accepted (the browsers see real
//!   certificates with them). Both extKeyUsage tables name exactly the same
//!   eight purposes.
//! - **A subscriber without extKeyUsage is refused** (BR §7.1.2.7.6: the
//!   row is "MUST"). RFC 5280 would read it as "any purpose"; the BR do not.
//! - **A subordinate CA without keyUsage is refused** (BR §7.1.2.6.1,
//!   §7.1.2.5.1 and §7.1.2.2.3: keyUsage "MUST"), and a keyUsage in which
//!   keyCertSign or cRLSign is not set is refused (BR §7.1.2.10.7, "Required
//!   Y" for both). Setting any bit the table marks "Permitted N" is refused;
//!   digitalSignature is permitted and not required.
//! - **A subscriber without keyUsage is accepted** (BR §7.1.2.7.6: "SHOULD").
//!   When it has one, the table for the subject key's kind applies
//!   (BR §7.1.2.7.11). Rows marked "Permitted Y" with required "SHOULD",
//!   "MAY" or "NOT RECOMMENDED" are accepted set or clear. Rows with
//!   required "MUST" (ECC digitalSignature) are enforced. The Note under the
//!   RSA table, "At least one Key Usage MUST be set", is enforced as: one of
//!   digitalSignature, keyEncipherment or dataEncipherment is set (the other
//!   bits are forbidden anyway). See the ERRATA entry on its tension with
//!   "SHOULD".
//! - **Key kind** is read from the OID of the SubjectPublicKeyInfo's
//!   AlgorithmIdentifier as the crate's SPKI decoder parses it:
//!   rsaEncryption 1.2.840.113549.1.1.1 is RSA, id-ecPublicKey
//!   1.2.840.10045.2.1 is ECC (the BR's "ECC Public Keys" cover all
//!   curves). Any other algorithm, and an SPKI the decoder refuses, is
//!   `Other`: no table applies, so a subscriber with a keyUsage extension
//!   and such a key is refused (BR §7.1.3.1 permits only RSA and ECC keys).
//!   Without keyUsage the key kind is not read.
//! - **keyUsage bits** are read with the decoder's `key_usage_has`: a bit
//!   beyond the encoded bit count is clear.
//! - **Views.** The profile reads a certificate only through
//!   [`CertView`]: its extKeyUsage, its keyUsage and its key kind.
//!   [`view_of`] extracts it from a `PathCert`, and [`path_profile_ok`] is
//!   the same decision as [`views_profile_ok`] over the views. The
//!   examples exercise `views_profile_ok`, because a `PathCert` has many
//!   fields that play no part here.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The decoder's types, named once.
pub type ExtendedKeyUsage = crate::constraints::spec::ExtendedKeyUsage;
/// The decoder's keyUsage.
pub type KeyUsage = crate::constraints::spec::KeyUsage;
/// The decoder's keyUsage bit names.
pub type KeyUsageBit = crate::constraints::spec::KeyUsageBit;
/// The decoded certificate of a path.
pub type PathCert = crate::path::parsed::spec::PathCert;

// ---------------------------------------------------------------------
// Object identifiers (BR §7.1.2.7.10 and §7.1.2.10.6, column "OID").
// ---------------------------------------------------------------------

/// `id-kp-serverAuth`, 1.3.6.1.5.5.7.3.1.
pub open spec fn id_kp_server_auth() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 1] }

/// `id-kp-clientAuth`, 1.3.6.1.5.5.7.3.2.
pub open spec fn id_kp_client_auth() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 2] }

/// `id-kp-codeSigning`, 1.3.6.1.5.5.7.3.3.
pub open spec fn id_kp_code_signing() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 3] }

/// `id-kp-emailProtection`, 1.3.6.1.5.5.7.3.4.
pub open spec fn id_kp_email_protection() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 4] }

/// `id-kp-timeStamping`, 1.3.6.1.5.5.7.3.8.
pub open spec fn id_kp_time_stamping() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 8] }

/// `id-kp-OCSPSigning`, 1.3.6.1.5.5.7.3.9.
pub open spec fn id_kp_ocsp_signing() -> Seq<nat> { seq![1nat, 3, 6, 1, 5, 5, 7, 3, 9] }

/// `anyExtendedKeyUsage`, 2.5.29.37.0.
pub open spec fn any_extended_key_usage() -> Seq<nat> { seq![2nat, 5, 29, 37, 0] }

/// "Precertificate Signing Certificate", 1.3.6.1.4.1.11129.2.4.4.
pub open spec fn precertificate_signing() -> Seq<nat> { seq![1nat, 3, 6, 1, 4, 1, 11129, 2, 4, 4] }

/// rsaEncryption, 1.2.840.113549.1.1.1 (RFC 3279 §2.3.1).
pub open spec fn rsa_encryption() -> Seq<nat> { seq![1nat, 2, 840, 113549, 1, 1, 1] }

/// id-ecPublicKey, 1.2.840.10045.2.1 (RFC 5480 §2.1.1).
pub open spec fn id_ec_public_key() -> Seq<nat> { seq![1nat, 2, 840, 10045, 2, 1] }

// ---------------------------------------------------------------------
// What the profile reads of a certificate.
// ---------------------------------------------------------------------

/// The kind of subject public key that picks the keyUsage table of
/// BR §7.1.2.7.11.
pub enum KeyKind {
    /// "Key Usage for RSA Public Keys".
    Rsa,
    /// "Key Usage for ECC Public Keys".
    Ecc,
    /// Neither: no table applies.
    Other,
}

/// The parts of a certificate the profile reads.
pub struct CertView {
    /// extKeyUsage, if present.
    pub eku: Option<ExtendedKeyUsage>,
    /// keyUsage, if present.
    pub key_usage: Option<KeyUsage>,
    /// The kind of the subject public key.
    pub key_kind: KeyKind,
}

/// Classify a SubjectPublicKeyInfo DER by its algorithm OID (see the
/// modelling choice "Key kind").
pub open spec fn key_kind_of_spki(spki_der: Seq<u8>) -> KeyKind {
    match crate::spki::spec::parse_subject_public_key_info(spki_der) {
        None => KeyKind::Other,
        Some(spki) =>
            if spki.algorithm.oid =~= rsa_encryption() { KeyKind::Rsa }
            else if spki.algorithm.oid =~= id_ec_public_key() { KeyKind::Ecc }
            else { KeyKind::Other },
    }
}

/// The view of a path certificate.
pub open spec fn view_of(cert: PathCert) -> CertView {
    CertView {
        eku: cert.eku,
        key_usage: cert.key_usage,
        key_kind: key_kind_of_spki(cert.tbs.subject_public_key_info_der),
    }
}

// ---------------------------------------------------------------------
// extKeyUsage.
// ---------------------------------------------------------------------

/// Whether `oid` is among `purposes[i..]`.
pub open spec fn oid_listed(purposes: Seq<Seq<nat>>, oid: Seq<nat>, i: int) -> bool
    recommends 0 <= i <= purposes.len()
    decreases purposes.len() as int - i
{
    i < purposes.len() && (purposes[i] =~= oid || oid_listed(purposes, oid, i + 1))
}

/// Whether the extKeyUsage lists `oid`.
pub open spec fn eku_lists(eku: ExtendedKeyUsage, oid: Seq<nat>) -> bool {
    oid_listed(eku.purposes, oid, 0)
}

/// BR §7.1.2.7.10 "Subscriber Certificate Extended Key Usage", the table:
/// serverAuth MUST; clientAuth MAY; codeSigning, emailProtection,
/// timeStamping, OCSPSigning, anyExtendedKeyUsage and "Precertificate
/// Signing Certificate" MUST NOT; any other value NOT RECOMMENDED (accepted).
pub open spec fn subscriber_eku_table_ok(eku: ExtendedKeyUsage) -> bool {
    eku_lists(eku, id_kp_server_auth())            // serverAuth: MUST
    // clientAuth: MAY, nothing to check
    && !eku_lists(eku, id_kp_code_signing())       // codeSigning: MUST NOT
    && !eku_lists(eku, id_kp_email_protection())   // emailProtection: MUST NOT
    && !eku_lists(eku, id_kp_time_stamping())      // timeStamping: MUST NOT
    && !eku_lists(eku, id_kp_ocsp_signing())       // OCSPSigning: MUST NOT
    && !eku_lists(eku, any_extended_key_usage())   // anyExtendedKeyUsage: MUST NOT
    && !eku_lists(eku, precertificate_signing())   // Precertificate Signing: MUST NOT
    // Any other value: NOT RECOMMENDED, accepted
}

/// BR §7.1.2.7.6 extKeyUsage row ("MUST") together with §7.1.2.7.10: an
/// absent extension is refused.
pub open spec fn subscriber_eku_ok(eku: Option<ExtendedKeyUsage>) -> bool {
    match eku {
        None => false,
        Some(e) => subscriber_eku_table_ok(e),
    }
}

/// BR §7.1.2.10.6 "CA Certificate Extended Key Usage", the table. Same
/// rows and presence values as §7.1.2.7.10.
pub open spec fn ca_eku_table_ok(eku: ExtendedKeyUsage) -> bool {
    eku_lists(eku, id_kp_server_auth())            // serverAuth: MUST
    // clientAuth: MAY, nothing to check
    && !eku_lists(eku, id_kp_code_signing())       // codeSigning: MUST NOT
    && !eku_lists(eku, id_kp_email_protection())   // emailProtection: MUST NOT
    && !eku_lists(eku, id_kp_time_stamping())      // timeStamping: MUST NOT
    && !eku_lists(eku, id_kp_ocsp_signing())       // OCSPSigning: MUST NOT
    && !eku_lists(eku, any_extended_key_usage())   // anyExtendedKeyUsage: MUST NOT
    && !eku_lists(eku, precertificate_signing())   // Precertificate Signing: MUST NOT
    // Any other value: NOT RECOMMENDED, accepted
}

/// BR §7.1.2.2.4: the "unrestricted" extended key usage of an affiliated
/// cross-certified subordinate CA: anyExtendedKeyUsage, "If present, this
/// MUST be the only key usage present".
pub open spec fn unrestricted_eku(eku: ExtendedKeyUsage) -> bool {
    eku.purposes =~= seq![any_extended_key_usage()]
}

/// A subordinate CA certificate's extKeyUsage (BR §7.1.2.5.1, §7.1.2.6.1 ->
/// §7.1.2.10.6; §7.1.2.2.3 to §7.1.2.2.5 for cross-certificates). Absent is
/// BR §7.1.2.2.3's unrestricted case ("SHOULD"), so it is accepted exactly
/// when `allow_unrestricted` is.
pub open spec fn ca_eku_ok(eku: Option<ExtendedKeyUsage>, allow_unrestricted: bool) -> bool {
    match eku {
        None => allow_unrestricted,
        Some(e) => ca_eku_table_ok(e) || (allow_unrestricted && unrestricted_eku(e)),
    }
}

/// Whether the certificate's extKeyUsage permits the purpose serverAuth:
/// absent (no restriction), anyExtendedKeyUsage, or listing serverAuth. The
/// property EKU chaining asks of every subordinate CA.
pub open spec fn eku_permits_server_auth(eku: Option<ExtendedKeyUsage>) -> bool {
    match eku {
        None => true,
        Some(e) => eku_lists(e, id_kp_server_auth()) || eku_lists(e, any_extended_key_usage()),
    }
}

// ---------------------------------------------------------------------
// keyUsage.
// ---------------------------------------------------------------------

/// Whether the keyUsage asserts the named bit.
pub open spec fn ku(usage: KeyUsage, bit: KeyUsageBit) -> bool {
    crate::constraints::spec::key_usage_has(usage, bit)
}

/// BR §7.1.2.10.7 "CA Certificate Key Usage", the table (Permitted /
/// Required): digitalSignature Y / N; keyCertSign Y / Y; cRLSign Y / Y;
/// nonRepudiation, keyEncipherment, dataEncipherment, keyAgreement,
/// encipherOnly and decipherOnly N.
pub open spec fn ca_key_usage_table_ok(usage: KeyUsage) -> bool {
    // digitalSignature: permitted, not required
    !ku(usage, KeyUsageBit::ContentCommitment)  // nonRepudiation: N
    && !ku(usage, KeyUsageBit::KeyEncipherment)   // keyEncipherment: N
    && !ku(usage, KeyUsageBit::DataEncipherment)  // dataEncipherment: N
    && !ku(usage, KeyUsageBit::KeyAgreement)      // keyAgreement: N
    && ku(usage, KeyUsageBit::KeyCertSign)        // keyCertSign: permitted, required
    && ku(usage, KeyUsageBit::CrlSign)            // cRLSign: permitted, required
    && !ku(usage, KeyUsageBit::EncipherOnly)      // encipherOnly: N
    && !ku(usage, KeyUsageBit::DecipherOnly)      // decipherOnly: N
}

/// A subordinate CA certificate's keyUsage: BR §7.1.2.2.3, §7.1.2.5.1 and
/// §7.1.2.6.1 make the extension "MUST", then §7.1.2.10.7's table applies.
pub open spec fn ca_key_usage_ok(usage: Option<KeyUsage>) -> bool {
    match usage {
        None => false,
        Some(u) => ca_key_usage_table_ok(u),
    }
}

/// BR §7.1.2.7.11 "Key Usage for RSA Public Keys": digitalSignature Y /
/// SHOULD; keyEncipherment Y / MAY; dataEncipherment Y / NOT RECOMMENDED;
/// nonRepudiation, keyAgreement, keyCertSign, cRLSign, encipherOnly and
/// decipherOnly N. The Note: "At least one Key Usage MUST be set".
pub open spec fn rsa_key_usage_table_ok(usage: KeyUsage) -> bool {
    // digitalSignature, keyEncipherment, dataEncipherment: permitted, and
    // at least one set (the Note)
    (ku(usage, KeyUsageBit::DigitalSignature)
        || ku(usage, KeyUsageBit::KeyEncipherment)
        || ku(usage, KeyUsageBit::DataEncipherment))
    && !ku(usage, KeyUsageBit::ContentCommitment)  // nonRepudiation: N
    && !ku(usage, KeyUsageBit::KeyAgreement)       // keyAgreement: N
    && !ku(usage, KeyUsageBit::KeyCertSign)        // keyCertSign: N
    && !ku(usage, KeyUsageBit::CrlSign)            // cRLSign: N
    && !ku(usage, KeyUsageBit::EncipherOnly)       // encipherOnly: N
    && !ku(usage, KeyUsageBit::DecipherOnly)       // decipherOnly: N
}

/// BR §7.1.2.7.11 "Key Usage for ECC Public Keys": digitalSignature Y /
/// MUST; keyAgreement Y / NOT RECOMMENDED; nonRepudiation, keyEncipherment,
/// dataEncipherment, keyCertSign, cRLSign, encipherOnly and decipherOnly N.
pub open spec fn ecc_key_usage_table_ok(usage: KeyUsage) -> bool {
    ku(usage, KeyUsageBit::DigitalSignature)       // digitalSignature: MUST
    && !ku(usage, KeyUsageBit::ContentCommitment)  // nonRepudiation: N
    && !ku(usage, KeyUsageBit::KeyEncipherment)    // keyEncipherment: N
    && !ku(usage, KeyUsageBit::DataEncipherment)   // dataEncipherment: N
    // keyAgreement: permitted, NOT RECOMMENDED
    && !ku(usage, KeyUsageBit::KeyCertSign)        // keyCertSign: N
    && !ku(usage, KeyUsageBit::CrlSign)            // cRLSign: N
    && !ku(usage, KeyUsageBit::EncipherOnly)       // encipherOnly: N
    && !ku(usage, KeyUsageBit::DecipherOnly)       // decipherOnly: N
}

/// A subscriber certificate's keyUsage: BR §7.1.2.7.6 makes the extension
/// "SHOULD" (absent is accepted); when present, the table for the key's
/// kind of BR §7.1.2.7.11 applies, and a key of no known kind has none.
pub open spec fn subscriber_key_usage_ok(usage: Option<KeyUsage>, kind: KeyKind) -> bool {
    match usage {
        None => true,
        Some(u) => match kind {
            KeyKind::Rsa => rsa_key_usage_table_ok(u),
            KeyKind::Ecc => ecc_key_usage_table_ok(u),
            KeyKind::Other => false,
        },
    }
}

// ---------------------------------------------------------------------
// The path.
// ---------------------------------------------------------------------

/// The subscriber certificate (BR §7.1.2.7): extKeyUsage and keyUsage.
pub open spec fn subscriber_ok(view: CertView) -> bool {
    subscriber_eku_ok(view.eku) && subscriber_key_usage_ok(view.key_usage, view.key_kind)
}

/// A subordinate CA certificate (BR §7.1.2.2, §7.1.2.5, §7.1.2.6):
/// extKeyUsage and keyUsage.
pub open spec fn subordinate_ca_ok(view: CertView, allow_unrestricted: bool) -> bool {
    ca_eku_ok(view.eku, allow_unrestricted) && ca_key_usage_ok(view.key_usage)
}

/// Every view from `i` on is an acceptable subordinate CA certificate.
pub open spec fn subordinate_cas_ok(views: Seq<CertView>, i: int, allow_unrestricted: bool) -> bool
    recommends 0 <= i <= views.len()
    decreases views.len() as int - i
{
    if i >= views.len() { true }
    else { subordinate_ca_ok(views[i], allow_unrestricted) && subordinate_cas_ok(views, i + 1, allow_unrestricted) }
}

/// The profile over views: a non-empty path whose first view is an
/// acceptable subscriber certificate and whose others are acceptable
/// subordinate CA certificates.
pub open spec fn views_profile_ok(views: Seq<CertView>, allow_unrestricted: bool) -> bool {
    views.len() >= 1
    && subscriber_ok(views[0])
    && subordinate_cas_ok(views, 1, allow_unrestricted)
}

/// The views of a path.
pub open spec fn views_of(path: Seq<PathCert>) -> Seq<CertView> {
    Seq::new(path.len(), |i: int| view_of(path[i]))
}

/// The profile over a path of certificates, leaf first, the trust anchor
/// not included (see the modelling choices).
pub open spec fn path_profile_ok(path: Seq<PathCert>, allow_unrestricted: bool) -> bool {
    views_profile_ok(views_of(path), allow_unrestricted)
}

/// The entry point: the EKU and keyUsage requirements of the BR for a TLS
/// server path, with unrestricted cross-certificate EKUs accepted.
pub open spec fn tls_server_path_profile_ok(path: Seq<PathCert>) -> bool {
    path_profile_ok(path, true)
}

/// The same with the choice made by the caller: whether an intermediate may
/// lack extKeyUsage or carry anyExtendedKeyUsage alone.
pub open spec fn tls_server_path_profile_ok_with(path: Seq<PathCert>, allow_unrestricted_ca_eku: bool) -> bool {
    path_profile_ok(path, allow_unrestricted_ca_eku)
}

// ---------------------------------------------------------------------
// Properties of the transcription.
// ---------------------------------------------------------------------

/// EKU chaining (BR §7.1.2.10.6): in an accepted path, every subordinate CA
/// permits serverAuth.
pub proof fn lemma_ca_permits_server_auth(views: Seq<CertView>, i: int, allow_unrestricted: bool)
    requires
        0 <= i <= views.len(),
        subordinate_cas_ok(views, i, allow_unrestricted),
    ensures
        forall|j: int| i <= j < views.len() ==> #[trigger] eku_permits_server_auth(views[j].eku),
    decreases views.len() as int - i
{
    if i < views.len() {
        lemma_ca_permits_server_auth(views, i + 1, allow_unrestricted);
        let e = views[i].eku;
        match e {
            None => {}
            Some(eku) => {
                // ca_eku_table_ok lists serverAuth; the unrestricted form is
                // [anyExtendedKeyUsage] alone, which lists itself.
                if unrestricted_eku(eku) {
                    assert(eku.purposes[0] =~= any_extended_key_usage());
                    assert(oid_listed(eku.purposes, any_extended_key_usage(), 0));
                }
            }
        }
    }
}

/// BR §7.1.2.7.10: an accepted path's leaf lists serverAuth.
pub proof fn lemma_leaf_has_server_auth(views: Seq<CertView>, allow_unrestricted: bool)
    requires views_profile_ok(views, allow_unrestricted),
    ensures
        views[0].eku is Some,
        eku_lists(views[0].eku->Some_0, id_kp_server_auth()),
{
}

/// BR §7.1.2.10.7: an accepted path's subordinate CAs all assert keyCertSign.
pub proof fn lemma_ca_key_cert_sign(views: Seq<CertView>, i: int, allow_unrestricted: bool)
    requires
        0 <= i <= views.len(),
        subordinate_cas_ok(views, i, allow_unrestricted),
    ensures
        forall|j: int| i <= j < views.len() ==>
            (#[trigger] views[j].key_usage is Some
                && ku(views[j].key_usage->Some_0, KeyUsageBit::KeyCertSign)),
    decreases views.len() as int - i
{
    if i < views.len() {
        lemma_ca_key_cert_sign(views, i + 1, allow_unrestricted);
    }
}

// ---------------------------------------------------------------------
// Sanity examples, proved by evaluation. A KeyUsage's `bits` are the DER
// BIT STRING data octets, bit 0 the most significant bit of octet 0
// (RFC 5280 §4.2.1.3); `bit_count` is the number of named bits kept.
// ---------------------------------------------------------------------

/// digitalSignature only (0x80).
pub open spec fn ku_digital_signature() -> KeyUsage { KeyUsage { bits: seq![0x80u8], bit_count: 1 } }

/// digitalSignature and keyEncipherment (0xa0).
pub open spec fn ku_ds_ke() -> KeyUsage { KeyUsage { bits: seq![0xa0u8], bit_count: 3 } }

/// keyCertSign and cRLSign (0x06).
pub open spec fn ku_ca() -> KeyUsage { KeyUsage { bits: seq![0x06u8], bit_count: 7 } }

/// digitalSignature, keyCertSign and cRLSign (0x86).
pub open spec fn ku_ca_ds() -> KeyUsage { KeyUsage { bits: seq![0x86u8], bit_count: 7 } }

/// cRLSign only (0x02).
pub open spec fn ku_crl_only() -> KeyUsage { KeyUsage { bits: seq![0x02u8], bit_count: 7 } }

/// keyCertSign only (0x04).
pub open spec fn ku_cert_sign_only() -> KeyUsage { KeyUsage { bits: seq![0x04u8], bit_count: 6 } }

/// digitalSignature and keyCertSign and cRLSign and keyAgreement (0x8e).
pub open spec fn ku_ca_with_key_agreement() -> KeyUsage { KeyUsage { bits: seq![0x8eu8], bit_count: 7 } }

/// digitalSignature and keyAgreement (0x88).
pub open spec fn ku_ds_agreement() -> KeyUsage { KeyUsage { bits: seq![0x88u8], bit_count: 5 } }

/// keyEncipherment only (0x20).
pub open spec fn ku_ke_only() -> KeyUsage { KeyUsage { bits: seq![0x20u8], bit_count: 3 } }

/// keyAgreement only (0x08).
pub open spec fn ku_agreement_only() -> KeyUsage { KeyUsage { bits: seq![0x08u8], bit_count: 5 } }

/// An extKeyUsage with the given purposes.
pub open spec fn eku_of(purposes: Seq<Seq<nat>>) -> ExtendedKeyUsage { ExtendedKeyUsage { purposes } }

/// A subscriber certificate with an ECC key, digitalSignature and serverAuth.
pub open spec fn good_leaf() -> CertView {
    CertView {
        eku: Some(eku_of(seq![id_kp_server_auth(), id_kp_client_auth()])),
        key_usage: Some(ku_digital_signature()),
        key_kind: KeyKind::Ecc,
    }
}

/// A subordinate CA with serverAuth and keyCertSign, cRLSign.
pub open spec fn good_ca() -> CertView {
    CertView {
        eku: Some(eku_of(seq![id_kp_server_auth()])),
        key_usage: Some(ku_ca()),
        key_kind: KeyKind::Rsa,
    }
}

proof fn examples_accept() {
    // A leaf and one intermediate.
    assert(views_profile_ok(seq![good_leaf(), good_ca()], true)) by (compute_only);
    assert(views_profile_ok(seq![good_leaf(), good_ca()], false)) by (compute_only);
    // A leaf alone (issued by the anchor).
    assert(views_profile_ok(seq![good_leaf()], true)) by (compute_only);
    // Two intermediates.
    assert(views_profile_ok(seq![good_leaf(), good_ca(), good_ca()], false)) by (compute_only);
    // The CA may also assert digitalSignature.
    assert(subordinate_ca_ok(CertView { key_usage: Some(ku_ca_ds()), ..good_ca() }, false)) by (compute_only);
    // An RSA leaf with digitalSignature and keyEncipherment, or keyEncipherment alone.
    assert(subscriber_ok(CertView { key_kind: KeyKind::Rsa, key_usage: Some(ku_ds_ke()), ..good_leaf() }))
        by (compute_only);
    assert(subscriber_ok(CertView { key_kind: KeyKind::Rsa, key_usage: Some(ku_ke_only()), ..good_leaf() }))
        by (compute_only);
    // An ECC leaf may assert keyAgreement (NOT RECOMMENDED, not forbidden).
    assert(subscriber_ok(CertView { key_usage: Some(ku_ds_agreement()), ..good_leaf() })) by (compute_only);
    // A leaf without keyUsage ("SHOULD").
    assert(subscriber_ok(CertView { key_usage: None, ..good_leaf() })) by (compute_only);
    // An EKU value the tables do not name is accepted ("Any other value": NOT RECOMMENDED).
    assert(subscriber_ok(CertView {
        eku: Some(eku_of(seq![id_kp_server_auth(), seq![1nat, 3, 6, 1, 4, 1, 311, 10, 3, 3]])),
        ..good_leaf()
    })) by (compute_only);
    // The unrestricted cross-certificate forms: no EKU, or anyExtendedKeyUsage alone.
    assert(views_profile_ok(seq![good_leaf(), CertView { eku: None, ..good_ca() }], true)) by (compute_only);
    assert(views_profile_ok(
        seq![good_leaf(), CertView { eku: Some(eku_of(seq![any_extended_key_usage()])), ..good_ca() }],
        true,
    )) by (compute_only);
}

proof fn examples_reject() {
    // The empty path.
    assert(!views_profile_ok(seq![], true)) by (compute_only);
    // An intermediate without keyCertSign (cRLSign only), or without cRLSign.
    assert(!views_profile_ok(seq![good_leaf(), CertView { key_usage: Some(ku_crl_only()), ..good_ca() }], true))
        by (compute_only);
    assert(!views_profile_ok(seq![good_leaf(), CertView { key_usage: Some(ku_cert_sign_only()), ..good_ca() }], true))
        by (compute_only);
    // An intermediate with no keyUsage, or a forbidden bit (keyAgreement).
    assert(!views_profile_ok(seq![good_leaf(), CertView { key_usage: None, ..good_ca() }], true)) by (compute_only);
    assert(!views_profile_ok(
        seq![good_leaf(), CertView { key_usage: Some(ku_ca_with_key_agreement()), ..good_ca() }], true,
    )) by (compute_only);
    // A leaf without serverAuth (clientAuth only), or without extKeyUsage.
    assert(!views_profile_ok(
        seq![CertView { eku: Some(eku_of(seq![id_kp_client_auth()])), ..good_leaf() }, good_ca()], true,
    )) by (compute_only);
    assert(!views_profile_ok(seq![CertView { eku: None, ..good_leaf() }, good_ca()], true)) by (compute_only);
    // An intermediate whose EKU excludes serverAuth (clientAuth only; emailProtection only).
    assert(!views_profile_ok(
        seq![good_leaf(), CertView { eku: Some(eku_of(seq![id_kp_client_auth()])), ..good_ca() }], true,
    )) by (compute_only);
    assert(!views_profile_ok(
        seq![good_leaf(), CertView { eku: Some(eku_of(seq![id_kp_email_protection()])), ..good_ca() }], true,
    )) by (compute_only);
    // serverAuth together with a forbidden purpose, on the intermediate and on the leaf.
    assert(!views_profile_ok(
        seq![good_leaf(), CertView {
            eku: Some(eku_of(seq![id_kp_server_auth(), id_kp_code_signing()])), ..good_ca() }], true,
    )) by (compute_only);
    assert(!subscriber_ok(CertView {
        eku: Some(eku_of(seq![id_kp_server_auth(), id_kp_ocsp_signing()])), ..good_leaf() })) by (compute_only);
    // anyExtendedKeyUsage on a leaf, alone or with serverAuth.
    assert(!subscriber_ok(CertView { eku: Some(eku_of(seq![any_extended_key_usage()])), ..good_leaf() }))
        by (compute_only);
    assert(!subscriber_ok(CertView {
        eku: Some(eku_of(seq![id_kp_server_auth(), any_extended_key_usage()])), ..good_leaf() })) by (compute_only);
    // anyExtendedKeyUsage beside serverAuth on an intermediate.
    assert(!subordinate_ca_ok(CertView {
        eku: Some(eku_of(seq![id_kp_server_auth(), any_extended_key_usage()])), ..good_ca() }, true)) by (compute_only);
    // The unrestricted forms are refused when not allowed.
    assert(!views_profile_ok(seq![good_leaf(), CertView { eku: None, ..good_ca() }], false)) by (compute_only);
    assert(!views_profile_ok(
        seq![good_leaf(), CertView { eku: Some(eku_of(seq![any_extended_key_usage()])), ..good_ca() }], false,
    )) by (compute_only);
    // A bad certificate anywhere in the path: the second intermediate.
    assert(!views_profile_ok(
        seq![good_leaf(), good_ca(), CertView { key_usage: Some(ku_crl_only()), ..good_ca() }], true,
    )) by (compute_only);
    // keyUsage of a leaf: keyCertSign set (RSA and ECC), ECC without digitalSignature,
    // RSA with keyAgreement only, a key of no known kind.
    assert(!subscriber_ok(CertView { key_usage: Some(ku_ca()), ..good_leaf() })) by (compute_only);
    assert(!subscriber_ok(CertView { key_kind: KeyKind::Rsa, key_usage: Some(ku_ca_ds()), ..good_leaf() }))
        by (compute_only);
    assert(!subscriber_ok(CertView { key_usage: Some(ku_agreement_only()), ..good_leaf() })) by (compute_only);
    assert(!subscriber_ok(CertView { key_kind: KeyKind::Ecc, key_usage: Some(ku_ke_only()), ..good_leaf() }))
        by (compute_only);
    assert(!subscriber_ok(CertView { key_kind: KeyKind::Rsa, key_usage: Some(ku_agreement_only()), ..good_leaf() }))
        by (compute_only);
    assert(!subscriber_ok(CertView { key_kind: KeyKind::Other, ..good_leaf() })) by (compute_only);
}

} // verus!
