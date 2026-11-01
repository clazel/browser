//! An independent transcription of the certification path processing
//! procedure of ITU-T X.509 (10/2019), clause 12 ("Certification path
//! processing procedure"), over the crate's decoded path types
//! ([`PathCert`](crate::path::parsed::spec::PathCert) and
//! [`Anchor`](crate::path::parsed::spec::Anchor)).
//!
//! Written without reading any other specification of path validation in
//! this repository: none of `path/spec.rs`, `profile.rs`, `contract.rs`,
//! `lemmas.rs`, `theorems.rs`, `exec.rs`, `examples.rs`, `verifier.rs`,
//! `mutation_certificates.rs`, `path/search/`, `mutations.json`,
//! `clazel-crypto`'s `chain/` or `.claude/plans/` was opened, and RFC 5280
//! was not consulted. The equivalence proof against the RFC 5280 §6.1 spec
//! is a later change, by a different session. This file proves nothing
//! beyond its sanity examples.
//!
//! Source, read in full for the clauses cited:
//! - Recommendation ITU-T X.509 (10/2019) | ISO/IEC 9594-8:2020,
//!   <https://www.itu.int/rec/T-REC-X.509-201910-I/en> (PDF fetched from
//!   `https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-X.509-201910-I!!PDF-E&type=items`
//!   on 30 October 2026; 236 pages, 3 581 573 bytes), SHA-256
//!   `1f4ea2939ecc31a3433c499084d485e770f9b8dcee55a0ba9fe4c27128822e8c`.
//!   Transcribed: §12.1 to §12.5.4 (document pages 63 to 67). Read for
//!   what they say about the procedure's terms: §3.5.68, §3.5.69, §3.5.73
//!   (definitions), §9.1.5 (self-issued certificates), §9.4.2.1 (basic
//!   constraints), §9.4.2.2 (name constraints), §9.4.2.3 (policy
//!   constraints). Steps are cited as `§12.5.2 step 1)` or `§12.5.1 b)`,
//!   with the clause's own labels.
//!
//! What the order of the path is. §12.5: "Each public-key certificate is then
//! processed in turn, starting with the public-key certificate signed using
//! the trust anchor public key. The last public-key certificate is
//! considered to be the end-entity public-key certificate". So `path[0]` is
//! the certificate the trust anchor signed, `path[n-1]` is the end entity,
//! and `path[j]` is verified under the key of `path[j-1]`.
//!
//! Modelling choices (the first group is what the equivalence is expected to
//! cover; the rest are choices of form):
//!
//! Restrictions of the domain, given to this author as the shared interface
//! (not independent; [`profile_domain`] is their conjunction, and outside it
//! the result below is X.509's only where the notes say so):
//! 1. certificatePolicies has no effect: §12.5.1 c) to f) and the policy
//!    table are not applied. The table keeps the zeroth row `any-policy` that
//!    §12.4 step 1) wrote, so at the end the authorities-constrained set and
//!    the user-constrained set are both `any-policy` (§12.5.4 steps 1) and 2))
//!    and step 3) cannot fail. (Read literally, §12.5.1 c) would null the
//!    table for a certificate without the extension; that is a policy
//!    effect, which this domain leaves out.)
//! 2. `initial-explicit-policy` is false. The input exists
//!    ([`PathInputs::initial_explicit_policy`]) and §12.5.3 is transcribed
//!    in full, so that the `explicit-policy-indicator` output is computed;
//!    only [`profile_domain`] requires it false.
//! 3. No policyMappings: `PathCert::has_policy_mappings` is not read by any
//!    step; [`profile_domain`] requires it false. §12.5.2 steps 3) to 5)
//!    act only on the policy table, so they have no body here.
//! 4. NameConstraints with the supported forms only, `minimum` 0 and no
//!    `maximum`: the decoder type
//!    [`GeneralSubtree`](crate::name_constraints::spec::GeneralSubtree)
//!    has no minimum or maximum field (they are its DEFAULT 0 and absent).
//!    A subtree whose base is not a dNSName or an iPAddress is of a name form
//!    that no name examined below has, so it neither constrains nor excludes
//!    anything; [`supported_name_constraints`] is the domain condition that
//!    rules those out, and outside it the result is not X.509's (which would
//!    need the other forms' matching, e.g. §9.4.2.2's directoryName rule).
//! 5. v3 certificates only: [`profile_domain`] requires `tbs.version == 2`.
//!    §12.5.1 b) is transcribed as written ("For an intermediate version 3 CA
//!    certificate"), so a version 1 or 2 intermediate is not checked for
//!    basicConstraints.
//!
//! Forms of the standard that differ from this file's, with the argument
//! that the meaning is unchanged:
//! 6. The inputs are a record ([`PathInputs`]) and two arguments: the
//!    path (§12.1 a)) and the trust anchor (§12.1 b)). Signature
//!    verification is a parameter `signature_verifies(cert, key)`: "the
//!    signature of `cert` verifies under the SubjectPublicKeyInfo DER
//!    `key`". §12.5.1 a) "check that the signature verifies" is
//!    `signature_verifies(cert, key of its issuer)`. Alternative digital
//!    signatures (§12.5.1 a), first sentence) are not modelled.
//! 7. The inputs §12.1 c) (initial-policy-set), e) (initial-policy-
//!    mapping-inhibit) and f) (initial-inhibit-policy) are not in
//!    [`PathInputs`]: the first is `any-policy` (a restriction 1 consequence)
//!    and the others only steer policy mapping and anyPolicy matching on the
//!    table. Likewise `PathCert` carries neither `inhibitPolicyMapping` nor
//!    `inhibitAnyPolicy`, and the state variables §12.3 g), h) and the two
//!    pending indicators of i) for them could only change the table, so they
//!    are not in [`PathState`]. The outputs §12.2 c), d), f) are the policy
//!    sets and mapping details, which restriction 1 fixes, and §12.2 g), h)
//!    are about trust brokers and authorizers, not the procedure.
//!    Output a) and b) are [`PathOutcome`]; e) is its
//!    `explicit_policy_indicator`.
//! 8. §12.1 b): trust anchor information, per §3.5.73, is "at least the
//!    distinguished name of the trust anchor, associated public key, ... and
//!    any constraints on its use, including a validity period". [`Anchor`]
//!    gives the name, the key, name constraints and a pathLenConstraint. §12
//!    does not say how the constraints on the anchor's use enter the
//!    procedure, so this file takes the evident reading: the anchor's
//!    permitted and excluded subtrees are intersected and united with the
//!    initial sets of §12.1 h) and i) in §12.4 steps 2) and 3), and the
//!    anchor's pathLenConstraint is checked as §12.5.1 b) checks a CA
//!    certificate that comes before `path[0]` (the non-self-issued
//!    intermediate certificates of the path must number at most
//!    `path_len`; [`anchor_path_length_ok`]). **The anchor's validity period
//!    is not checked**: §12.5.1 a) says "dates are valid" of the
//!    public-key certificates of the path, and §12.1 b) asks of the anchor
//!    only a public key. Its `server_distrust_after` is not an X.509 notion.
//! 9. Names are compared as DER: "the subject and issuer names chain
//!    correctly" (§12.5.1 a)) and "the issuer and the subject are the same
//!    CA" (§3.5.68) are `issuer_der == subject_der` on the complete Name TLV.
//!    X.501 name matching (case and whitespace folding) is not modelled.
//! 10. A certificate is **self-issued** if its issuer and subject are equal
//!    (§9.1.5: "recognized by the fact that the issuer and subject names
//!    present in them are identical") and **self-signed** if it is
//!    self-issued and its signature verifies under its own public key
//!    (§3.5.69). In-path certificates are what §9.1.5's categories b) and
//!    c) cannot be told apart for: both are self-issued, not self-signed,
//!    and §12.5's "intermediate self-issued" rules treat them alike. A
//!    self-issued certificate at the end of the path is an end-entity
//!    certificate (category b)).
//! 11. "Self-signed certificates, if encountered in the path, are ignored"
//!    (§12.5.1, §12.5.2, §9.1.5): such a certificate is removed from the
//!    path before anything else ([`drop_ignored`]), so the next certificate
//!    is checked against the previous certificate that was kept, and
//!    counts, state and `path_depth` do not see it. **The last certificate
//!    is never ignored**: see ERRATA.md, "X.509 §12.5 ignores self-signed
//!    certificates, including the end entity". An empty path is a failure
//!    (§12.1 a): "a set of public-key certificates comprising a
//!    certification path"; §12.5: "the last ... is the end-entity").
//! 12. `pathLenConstraint` (§12.5.1 b)) has no counter state in clause 12:
//!    "check that the current certification path does not violate that
//!    constraint (ignoring intermediate self-issued certificates)". It is
//!    read with §9.4.2.1: the constraint of a CA certificate is "the maximum
//!    number of CA certificates that may follow this CA certificate", and
//!    it "controls the number of non-self-issued CA certificates between the
//!    CA certificate containing the constraint and the end-entity". So for
//!    `path[i]` that number is the count of non-self-issued certificates of
//!    `path[i+1 .. n-1]` (the end entity is not a CA certificate), and it
//!    must be at most the constraint ([`non_self_issued_count`]).
//! 13. Sets of subtrees. `permitted-subtrees` (§12.3 b)) is represented by
//!    the list of the sets that were intersected into it, the empty list
//!    meaning `unbounded`; a name satisfies it iff it satisfies every set in
//!    the list. A set constrains a name form iff it has a subtree of that
//!    form (§9.4.2.2: "If this extension is present but a name form is not
//!    included in the extension, then no constraints are imposed on that
//!    name form"; §12.1 h): "for which initial permitted subtrees are
//!    defined"). This is the intersection of the per-form sets: for a form
//!    one set leaves unconstrained, the intersection is the other's. The
//!    `excluded-subtrees` (§12.3 c)) are the concatenation of the sets
//!    united into it.
//! 14. The names examined by §12.5.1 g) and h) are the subject component, as
//!    a directoryName unless it is the empty Name `SEQUENCE {}`, and the
//!    entries of subjectAltName (§12.1 h): "Subject names are those name
//!    values appearing in the subject component or the subjectAltName
//!    extension"; §9.4.2.2: "names in non-critical subject alternative name
//!    extensions shall be processed"). Whether a name is **within** a
//!    subtree is not defined by X.509 for dNSName or iPAddress (§9.4.2.2
//!    defines it for directoryName only, and §9.4.2.2 says only forms "that
//!    have a well-defined hierarchical structure may be used"). The rules
//!    here are the Internet conventions, recorded as a choice of this file
//!    and kept in one place ([`dns_within`], [`ip_within`]): a dNSName is
//!    within a base if the base is empty or the name is the base or ends in
//!    "." followed by the base (ASCII case-insensitively); an iPAddress is
//!    within an (address, mask) base if the lengths of name, address and mask
//!    agree and the name and address agree under the mask.
//! 15. §12.5.1 a) "and that the public-key certificate has not been revoked"
//!    is not modelled: §12.1 lists no revocation information among the
//!    inputs, so the procedure has nothing to decide it with. "Check that
//!    dates are valid" is `notBefore <= now <= notAfter` (a closed interval,
//!    comparing the calendar fields lexicographically).
//! 16. Not part of clause 12, so not transcribed: keyUsage, extKeyUsage,
//!    handling of unrecognized critical extensions (§9.4.2.1 asks a
//!    relying party to support basicConstraints, and the decoders refuse
//!    malformed ones) and whether the end-entity certificate suits the use.
//! 17. A diagnostic code (§12.2 b)) is [`FailureReason`]; the first failing
//!    check, in the order of §12.5.1 a) to h), is the one reported. The
//!    choice of reason does not change whether the path is valid.
//! 18. The "set" of name forms of §12.1 j) is a `Seq<NameForm>`, the "set
//!    of sets" a `Seq` of them; membership is by search, not by `Set`.
//! 19. §12.5.2's "intermediate CA certificate" is every certificate of the
//!    (kept) path but the last; §12.5.3 applies to all of them, the last
//!    included. The steps of §12.5.1 are applied in the clause's order
//!    first to a certificate, then §12.5.2 (intermediates), then §12.5.3,
//!    before the next. A name constraint recorded by §12.5.2 therefore
//!    applies to the certificates after the one that carries it, not to it.
//! 20. The loop "Each public-key certificate is then processed in turn" is a
//!    recursion on the index of the certificate; "terminate returning a
//!    failure indication" is the early `Failure` and no certificate after it
//!    is looked at. [`PathState`] is the §12.3 variable list.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §12.1 Path processing inputs, §12.2 outputs, §12.3 variables.
// ---------------------------------------------------------------------

/// A name form (§12.1 j): a "name form" of the subject names of a
/// certificate): the form of a name that §12.5.1 h) looks for.
pub enum NameForm {
    /// The subject component, a distinguished name.
    DirectoryName,
    /// A dNSName of subjectAltName.
    DnsName,
    /// An iPAddress of subjectAltName.
    IpAddress,
    /// Any other GeneralName choice of subjectAltName, by tag.
    Other(u32),
}

/// A subject name of a certificate (§12.1 h): "those name values appearing
/// in the subject component or the subjectAltName extension").
pub enum SubjectName {
    /// The subject component.
    Directory(Seq<u8>),
    /// A dNSName.
    Dns(Seq<u8>),
    /// An iPAddress.
    Ip(Seq<u8>),
    /// Another GeneralName choice, by tag; no constraint examined here
    /// applies to it.
    Other(u32),
}

/// The inputs of §12.1 other than the path (a)) and the trust anchor
/// information (b)); see modelling choice 7 for c), e) and f).
pub struct PathInputs {
    /// §12.1 d) initial-explicit-policy.
    pub initial_explicit_policy: bool,
    /// §12.1 g) the current date/time.
    pub now: crate::time::spec::CertificateTime,
    /// §12.1 h) initial-permitted-subtrees-set; `None` is `unbounded`.
    pub initial_permitted_subtrees: Option<Seq<crate::name_constraints::spec::GeneralSubtree>>,
    /// §12.1 i) initial-excluded-subtrees-set; the empty sequence is the
    /// empty set.
    pub initial_excluded_subtrees: Seq<crate::name_constraints::spec::GeneralSubtree>,
    /// §12.1 j) initial-required-name-forms; the empty sequence is the empty
    /// set (no specific name forms required).
    pub initial_required_name_forms: Seq<Seq<NameForm>>,
}

/// Why a path was rejected (§12.2 b)).
pub enum FailureReason {
    /// There is no end-entity certificate (§12.1 a), §12.5).
    EmptyPath,
    /// §12.5.1 a): "check that the signature verifies".
    SignatureDoesNotVerify,
    /// §12.5.1 a): "Check that dates are valid": now is before notBefore.
    NotYetValid,
    /// §12.5.1 a): "Check that dates are valid": now is after notAfter.
    Expired,
    /// §12.5.1 a): "the public-key certificate subject and public-key
    /// certificate issuer names chain correctly".
    NamesDoNotChain,
    /// §12.5.1 b): "check that basicConstraints is present and that the cA
    /// component ... is TRUE".
    NotACaCertificate,
    /// §12.5.1 b): the pathLenConstraint is violated.
    PathLengthViolated,
    /// §12.5.1 g): a subject name is not "within the name-space given by the
    /// value of permitted-subtrees".
    SubjectNameNotPermitted,
    /// §12.5.1 g): a subject name is "within the name-space given by the
    /// value of excluded-subtrees".
    SubjectNameExcluded,
    /// §12.5.1 h): no subject name of one of the name forms of a set of
    /// required-name-forms.
    RequiredNameFormMissing,
    /// §12.5.4 step 3): "check that neither the authorities-constrained-
    /// policy-set nor the user-constrained-policy-set is empty".
    EmptyPolicySet,
}

/// The outputs of §12.2 that the restrictions leave (a), b) and e)).
pub enum PathOutcome {
    /// §12.2 a), b): failure, with a diagnostic code.
    Failure(FailureReason),
    /// §12.2 a), e): success, with the explicit-policy-indicator.
    Success {
        /// §12.2 e) explicit-policy-indicator.
        explicit_policy_indicator: bool,
    },
}

/// The §12.3 variables that restriction 1 and modelling choice 7 leave.
/// The authorities-constrained-policy-set table (a)) is constant, see
/// [`final_processing`].
pub struct PathState {
    /// §12.3 b) permitted-subtrees, as the list of the sets intersected into
    /// it (choice 13); empty is `unbounded`.
    pub permitted_subtrees: Seq<Seq<crate::name_constraints::spec::GeneralSubtree>>,
    /// §12.3 c) excluded-subtrees, as the concatenation of the sets united.
    pub excluded_subtrees: Seq<crate::name_constraints::spec::GeneralSubtree>,
    /// §12.3 d) required-name-forms.
    pub required_name_forms: Seq<Seq<NameForm>>,
    /// §12.3 e) explicit-policy-indicator.
    pub explicit_policy_indicator: bool,
    /// §12.3 f) path depth.
    pub path_depth: nat,
    /// §12.3 i) explicit-policy-pending.
    pub explicit_policy_pending: bool,
    /// §12.3 i) the skip-certificates value of explicit-policy-pending.
    pub explicit_policy_skip_certificates: nat,
}

/// The authorities-constrained and user-constrained policy sets of
/// §12.5.4, which restriction 1 leaves only two values.
pub enum PolicySet {
    /// The special value any-policy.
    AnyPolicy,
    /// The empty or null set.
    Empty,
}

// ---------------------------------------------------------------------
// The domain of the restrictions.
// ---------------------------------------------------------------------

/// Whether every subtree of the set is of a supported form (choice 4).
pub open spec fn supported_subtrees(set: Seq<crate::name_constraints::spec::GeneralSubtree>, i: int) -> bool
    recommends 0 <= i <= set.len()
    decreases set.len() as int - i
{
    if i >= set.len() { true }
    else {
        (match set[i].base {
            crate::name_constraints::spec::GeneralNameConstraint::DnsName(_) => true,
            crate::name_constraints::spec::GeneralNameConstraint::IpAddress { .. } => true,
            _ => false,
        }) && supported_subtrees(set, i + 1)
    }
}

/// Choice 4: every subtree of the extension is a dNSName or an iPAddress.
pub open spec fn supported_name_constraints(
    nc: Option<crate::name_constraints::spec::NameConstraints>,
) -> bool {
    match nc {
        None => true,
        Some(c) =>
            (match c.permitted_subtrees { None => true, Some(s) => supported_subtrees(s, 0) })
            && (match c.excluded_subtrees { None => true, Some(s) => supported_subtrees(s, 0) }),
    }
}

/// Restrictions 1 to 5 on one certificate.
pub open spec fn cert_in_domain(c: crate::path::parsed::spec::PathCert) -> bool {
    c.tbs.version == 2 && !c.has_policy_mappings && supported_name_constraints(c.name_constraints)
}

/// Restrictions 1 to 5 on a whole path.
pub open spec fn path_in_domain(path: Seq<crate::path::parsed::spec::PathCert>, i: int) -> bool
    recommends 0 <= i <= path.len()
    decreases path.len() as int - i
{
    if i >= path.len() { true }
    else { cert_in_domain(path[i]) && path_in_domain(path, i + 1) }
}

/// The inputs to which the restrictions confine the equivalence: v3
/// certificates, no policyMappings, supported name constraint forms (also
/// in the anchor and in the initial sets), and `initial-explicit-policy`
/// false.
pub open spec fn profile_domain(
    anchor: crate::path::parsed::spec::Anchor,
    path: Seq<crate::path::parsed::spec::PathCert>,
    inputs: PathInputs,
) -> bool {
    !inputs.initial_explicit_policy
        && path_in_domain(path, 0)
        && supported_name_constraints(anchor.name_constraints)
        && (match inputs.initial_permitted_subtrees { None => true, Some(s) => supported_subtrees(s, 0) })
        && supported_subtrees(inputs.initial_excluded_subtrees, 0)
}

// ---------------------------------------------------------------------
// Vocabulary of the procedure: self-issued, self-signed, dates, names.
// ---------------------------------------------------------------------

/// §3.5.68, §9.1.5: "the issuer and subject names present in them are
/// identical" (choice 9).
pub open spec fn is_self_issued(c: crate::path::parsed::spec::PathCert) -> bool {
    c.tbs.issuer_der =~= c.tbs.subject_der
}

/// §3.5.69: self-issued, and "the private key used ... to sign the CA
/// certificate corresponds to the public key that is certified within" it:
/// its signature verifies under its own key (choice 10).
pub open spec fn is_self_signed(
    signature_verifies: spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool,
    c: crate::path::parsed::spec::PathCert,
) -> bool {
    is_self_issued(c) && signature_verifies(c, c.tbs.subject_public_key_info_der)
}

/// `a <= b` on calendar fields, most significant first (choice 15).
pub open spec fn time_le(a: crate::time::spec::CertificateTime, b: crate::time::spec::CertificateTime) -> bool {
    a.year < b.year
        || (a.year == b.year && (a.month < b.month
        || (a.month == b.month && (a.day < b.day
        || (a.day == b.day && (a.hour < b.hour
        || (a.hour == b.hour && (a.minute < b.minute
        || (a.minute == b.minute && a.second <= b.second)))))))))
}

/// The form of a subject name.
pub open spec fn name_form(n: SubjectName) -> NameForm {
    match n {
        SubjectName::Directory(_) => NameForm::DirectoryName,
        SubjectName::Dns(_) => NameForm::DnsName,
        SubjectName::Ip(_) => NameForm::IpAddress,
        SubjectName::Other(tag) => NameForm::Other(tag),
    }
}

/// The subjectAltName entries as subject names (choice 14).
pub open spec fn san_names(names: Seq<crate::extensions::spec::GeneralName>, i: int) -> Seq<SubjectName>
    recommends 0 <= i <= names.len()
    decreases names.len() as int - i
{
    if i >= names.len() { seq![] }
    else {
        let rest = san_names(names, i + 1);
        match names[i] {
            crate::extensions::spec::GeneralName::DnsName(d) => seq![SubjectName::Dns(d)].add(rest),
            crate::extensions::spec::GeneralName::IpAddress(a) => seq![SubjectName::Ip(a)].add(rest),
            crate::extensions::spec::GeneralName::Other(tag, _) => seq![SubjectName::Other(tag)].add(rest),
        }
    }
}

/// The subject names of a certificate (§12.1 h), choice 14): the subject
/// component unless it is empty, then the subjectAltName entries.
pub open spec fn subject_names(c: crate::path::parsed::spec::PathCert) -> Seq<SubjectName> {
    let subject: Seq<SubjectName> = if c.tbs.subject_der =~= seq![0x30u8, 0x00u8] { seq![] }
        else { seq![SubjectName::Directory(c.tbs.subject_der)] };
    match c.san {
        None => subject,
        Some(san) => subject.add(san_names(san.names, 0)),
    }
}

/// The value of a big-endian unsigned integer (the canonical magnitude
/// octets of `BasicConstraints::path_len_constraint`).
pub open spec fn magnitude(octets: Seq<u8>) -> nat
    decreases octets.len(),
{
    if octets.len() == 0 { 0 }
    else { magnitude(octets.drop_last()) * 256 + octets.last() as nat }
}

// ---------------------------------------------------------------------
// Name spaces (choices 13 and 14).
// ---------------------------------------------------------------------

/// ASCII lowercase of one octet.
pub open spec fn ascii_lower(b: u8) -> u8 {
    if 0x41u8 <= b && b <= 0x5Au8 { (b + 32) as u8 } else { b }
}

/// `a` and `b` agree ASCII case-insensitively from index `i`, being of the
/// same length.
pub open spec fn ci_equal_from(a: Seq<u8>, b: Seq<u8>, i: int) -> bool
    recommends a.len() == b.len(), 0 <= i <= a.len()
    decreases a.len() as int - i
{
    if i >= a.len() || i >= b.len() { true }
    else { ascii_lower(a[i]) == ascii_lower(b[i]) && ci_equal_from(a, b, i + 1) }
}

/// Choice 14: a dNSName is within a dNSName base.
pub open spec fn dns_within(name: Seq<u8>, base: Seq<u8>) -> bool {
    base.len() == 0
        || (name.len() >= base.len()
            && ci_equal_from(name.subrange(name.len() - base.len(), name.len() as int), base, 0)
            && (name.len() == base.len() || name[name.len() - base.len() - 1] == 0x2Eu8))
}

/// `a` and `b` agree under `mask` from index `i`.
pub open spec fn masked_equal_from(a: Seq<u8>, b: Seq<u8>, mask: Seq<u8>, i: int) -> bool
    recommends a.len() == b.len(), b.len() == mask.len(), 0 <= i <= a.len()
    decreases a.len() as int - i
{
    if i >= a.len() || i >= b.len() || i >= mask.len() { true }
    else { (a[i] & mask[i]) == (b[i] & mask[i]) && masked_equal_from(a, b, mask, i + 1) }
}

/// Choice 14: an iPAddress is within an (address, mask) base.
pub open spec fn ip_within(name: Seq<u8>, address: Seq<u8>, mask: Seq<u8>) -> bool {
    name.len() == address.len() && mask.len() == address.len()
        && masked_equal_from(name, address, mask, 0)
}

/// Whether the subtree is of the form of the name.
pub open spec fn subtree_has_form_of(s: crate::name_constraints::spec::GeneralSubtree, n: SubjectName) -> bool {
    match (s.base, n) {
        (crate::name_constraints::spec::GeneralNameConstraint::DnsName(_), SubjectName::Dns(_)) => true,
        (crate::name_constraints::spec::GeneralNameConstraint::IpAddress { .. }, SubjectName::Ip(_)) => true,
        _ => false,
    }
}

/// Whether the name is within the subtree (false when the forms differ).
pub open spec fn within_subtree(n: SubjectName, s: crate::name_constraints::spec::GeneralSubtree) -> bool {
    match (n, s.base) {
        (SubjectName::Dns(name), crate::name_constraints::spec::GeneralNameConstraint::DnsName(base)) =>
            dns_within(name, base),
        (SubjectName::Ip(name), crate::name_constraints::spec::GeneralNameConstraint::IpAddress { address, mask }) =>
            ip_within(name, address, mask),
        _ => false,
    }
}

/// Whether the set has a subtree of the name's form: the set "constrains"
/// that form (choice 13).
pub open spec fn set_constrains_form(
    set: Seq<crate::name_constraints::spec::GeneralSubtree>, n: SubjectName, i: int,
) -> bool
    recommends 0 <= i <= set.len()
    decreases set.len() as int - i
{
    if i >= set.len() { false }
    else { subtree_has_form_of(set[i], n) || set_constrains_form(set, n, i + 1) }
}

/// Whether the name is within some subtree of the set.
pub open spec fn within_some(
    set: Seq<crate::name_constraints::spec::GeneralSubtree>, n: SubjectName, i: int,
) -> bool
    recommends 0 <= i <= set.len()
    decreases set.len() as int - i
{
    if i >= set.len() { false }
    else { within_subtree(n, set[i]) || within_some(set, n, i + 1) }
}

/// The name satisfies every set of the list of permitted sets (choice 13).
pub open spec fn within_permitted(
    permitted: Seq<Seq<crate::name_constraints::spec::GeneralSubtree>>, n: SubjectName, j: int,
) -> bool
    recommends 0 <= j <= permitted.len()
    decreases permitted.len() as int - j
{
    if j >= permitted.len() { true }
    else {
        (!set_constrains_form(permitted[j], n, 0) || within_some(permitted[j], n, 0))
            && within_permitted(permitted, n, j + 1)
    }
}

/// §12.5.1 g) over the subject names from index `k`: the first name that is
/// not within permitted-subtrees or is within excluded-subtrees.
pub open spec fn name_space_failure(state: PathState, names: Seq<SubjectName>, k: int) -> Option<FailureReason>
    recommends 0 <= k <= names.len()
    decreases names.len() as int - k
{
    if k >= names.len() { None }
    else if !within_permitted(state.permitted_subtrees, names[k], 0) {
        Some(FailureReason::SubjectNameNotPermitted)
    } else if within_some(state.excluded_subtrees, names[k], 0) {
        Some(FailureReason::SubjectNameExcluded)
    } else {
        name_space_failure(state, names, k + 1)
    }
}

/// Whether a name form is in a set of name forms.
pub open spec fn form_in(set: Seq<NameForm>, f: NameForm, i: int) -> bool
    recommends 0 <= i <= set.len()
    decreases set.len() as int - i
{
    if i >= set.len() { false } else { set[i] == f || form_in(set, f, i + 1) }
}

/// Whether some name from index `k` has a form in the set.
pub open spec fn some_name_in(names: Seq<SubjectName>, set: Seq<NameForm>, k: int) -> bool
    recommends 0 <= k <= names.len()
    decreases names.len() as int - k
{
    if k >= names.len() { false }
    else { form_in(set, name_form(names[k]), 0) || some_name_in(names, set, k + 1) }
}

/// §12.5.1 h): "for each set of name forms in required-name-forms check that
/// there is a subject name ... of one of the name forms in the set".
pub open spec fn every_set_satisfied(
    names: Seq<SubjectName>, required: Seq<Seq<NameForm>>, j: int,
) -> bool
    recommends 0 <= j <= required.len()
    decreases required.len() as int - j
{
    if j >= required.len() { true }
    else { some_name_in(names, required[j], 0) && every_set_satisfied(names, required, j + 1) }
}

// ---------------------------------------------------------------------
// The path: ignored certificates, and the pathLenConstraint count.
// ---------------------------------------------------------------------

/// Choice 11: the path without its self-signed certificates other than the
/// last, from index `i`.
pub open spec fn drop_ignored(
    signature_verifies: spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool,
    path: Seq<crate::path::parsed::spec::PathCert>,
    i: int,
) -> Seq<crate::path::parsed::spec::PathCert>
    recommends 0 <= i <= path.len()
    decreases path.len() as int - i
{
    if i >= path.len() { seq![] }
    else if i + 1 < path.len() && is_self_signed(signature_verifies, path[i]) {
        drop_ignored(signature_verifies, path, i + 1)
    } else {
        seq![path[i]].add(drop_ignored(signature_verifies, path, i + 1))
    }
}

/// Choice 12: the number of non-self-issued certificates of `path[from ..
/// to]`.
pub open spec fn non_self_issued_count(
    path: Seq<crate::path::parsed::spec::PathCert>, from: int, to: int,
) -> nat
    recommends 0 <= from, to <= path.len()
    decreases to - from
{
    if from >= to { 0 }
    else {
        (if is_self_issued(path[from]) { 0nat } else { 1nat }) + non_self_issued_count(path, from + 1, to)
    }
}

/// §12.5.1 b), applied to the trust anchor information (choice 8): the
/// non-self-issued intermediate certificates of the path are at most the
/// anchor's pathLenConstraint, if it has one.
pub open spec fn anchor_path_length_ok(
    anchor: crate::path::parsed::spec::Anchor, path: Seq<crate::path::parsed::spec::PathCert>,
) -> bool {
    match anchor.path_len {
        None => true,
        Some(limit) => non_self_issued_count(path, 0, path.len() - 1) <= limit,
    }
}

// ---------------------------------------------------------------------
// §12.4 Initialization step.
// ---------------------------------------------------------------------

/// The permitted sets of the anchor's constraints (§3.5.73, choice 8).
pub open spec fn anchor_permitted(
    nc: Option<crate::name_constraints::spec::NameConstraints>,
) -> Seq<Seq<crate::name_constraints::spec::GeneralSubtree>> {
    match nc {
        Some(c) => match c.permitted_subtrees { Some(s) => seq![s], None => seq![] },
        None => seq![],
    }
}

/// The excluded subtrees of the anchor's constraints.
pub open spec fn anchor_excluded(
    nc: Option<crate::name_constraints::spec::NameConstraints>,
) -> Seq<crate::name_constraints::spec::GeneralSubtree> {
    match nc {
        Some(c) => match c.excluded_subtrees { Some(s) => s, None => seq![] },
        None => seq![],
    }
}

/// §12.4: the initialization step.
pub open spec fn initialization(anchor: crate::path::parsed::spec::Anchor, inputs: PathInputs) -> PathState {
    PathState {
        // 1) "Write any-policy in the zeroth and first columns of the zeroth
        //    row of the authorities-constrained-policy-set table." Constant
        //    here (restriction 1), see `final_processing`.
        // 2) "Initialize the permitted-subtrees variable to the initial-
        //    permitted-subtrees-set value." With the anchor's own (choice 8).
        permitted_subtrees: (match inputs.initial_permitted_subtrees {
            Some(s) => seq![s],
            None => seq![],
        }).add(anchor_permitted(anchor.name_constraints)),
        // 3) "Initialize the excluded-subtrees variable to the initial-
        //    excluded-subtrees-set value."
        excluded_subtrees: inputs.initial_excluded_subtrees.add(anchor_excluded(anchor.name_constraints)),
        // 4) "Initialize the required-name-forms variable to the initial-
        //    required-name-forms value."
        required_name_forms: inputs.initial_required_name_forms,
        // 5) "Initialize the explicit-policy-indicator to the initial-
        //    explicit-policy value."
        explicit_policy_indicator: inputs.initial_explicit_policy,
        // 6) "Initialize path-depth to one."
        path_depth: 1,
        // 7), 8) policy-mapping-inhibit-indicator and inhibit-any-policy-
        //    indicator: not modelled (choice 7).
        // 9) "Initialize the three pending-constraints indicators to unset."
        //    Only explicit-policy-pending is modelled (choice 7).
        explicit_policy_pending: false,
        explicit_policy_skip_certificates: 0,
    }
}

// ---------------------------------------------------------------------
// §12.5.1 Basic public-key certificate checks.
// ---------------------------------------------------------------------

/// §12.5.1 b): "For an intermediate version 3 CA certificate, check that
/// basicConstraints is present and that the cA component ... is TRUE. If the
/// pathLenConstraint component is present, check that the current
/// certification path does not violate that constraint (ignoring
/// intermediate self-issued certificates)." `i` is the certificate's index in
/// `path`.
pub open spec fn basic_constraints_failure(
    path: Seq<crate::path::parsed::spec::PathCert>, i: int,
) -> Option<FailureReason>
    recommends 0 <= i < path.len()
{
    let c = path[i];
    let intermediate = i + 1 < path.len();
    if !(intermediate && c.tbs.version == 2) { None }
    else {
        match c.basic {
            None => Some(FailureReason::NotACaCertificate),
            Some(b) => if !b.ca { Some(FailureReason::NotACaCertificate) }
                else {
                    match b.path_len_constraint {
                        None => None,
                        Some(octets) =>
                            // Choice 12: the certificates that follow, but the end entity.
                            if non_self_issued_count(path, i + 1, path.len() - 1) <= magnitude(octets) { None }
                            else { Some(FailureReason::PathLengthViolated) },
                    }
                },
        }
    }
}

/// §12.5.1 a)..h) for `path[i]`, in the clause's order, with the state before
/// this certificate is processed. `key` and `issuer_name` are the key and
/// name of what signed it: the trust anchor for the first certificate,
/// otherwise the previous certificate.
pub open spec fn basic_certificate_checks(
    signature_verifies: spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool,
    path: Seq<crate::path::parsed::spec::PathCert>,
    i: int,
    key: Seq<u8>,
    issuer_name: Seq<u8>,
    now: crate::time::spec::CertificateTime,
    state: PathState,
) -> Option<FailureReason>
    recommends 0 <= i < path.len()
{
    let c = path[i];
    let intermediate = i + 1 < path.len();
    let self_issued_intermediate = intermediate && is_self_issued(c);
    // a) "check that the signature verifies."
    if !signature_verifies(c, key) { Some(FailureReason::SignatureDoesNotVerify) }
    // a) "Check that dates are valid,"
    else if !time_le(c.tbs.not_before, now) { Some(FailureReason::NotYetValid) }
    else if !time_le(now, c.tbs.not_after) { Some(FailureReason::Expired) }
    // a) "that the ... subject and ... issuer names chain correctly,"
    else if !(c.tbs.issuer_der =~= issuer_name) { Some(FailureReason::NamesDoNotChain) }
    // a) "and that the public-key certificate has not been revoked": choice 15.
    else if basic_constraints_failure(path, i) is Some {
        // b)
        basic_constraints_failure(path, i)
    }
    // c), d), e), f): the policies extension has no effect (restriction 1).
    // g) "If the public-key certificate is not an intermediate self-issued
    //    certificate, check that the subject name is within the name-space
    //    given by the value of permitted-subtrees and is not within the
    //    name-space given by the value of excluded-subtrees."
    else if !self_issued_intermediate && name_space_failure(state, subject_names(c), 0) is Some {
        name_space_failure(state, subject_names(c), 0)
    }
    // h) "If the public-key certificate is not an intermediate self-issued
    //    certificate, and if required-name-forms is not an empty set, for
    //    each set of name forms in required-name-forms check that there is a
    //    subject name in the public-key certificate of one of the name forms
    //    in the set."
    else if !self_issued_intermediate && !every_set_satisfied(subject_names(c), state.required_name_forms, 0) {
        Some(FailureReason::RequiredNameFormMissing)
    } else { None }
}

// ---------------------------------------------------------------------
// §12.5.2 Processing intermediate certificates.
// ---------------------------------------------------------------------

/// §12.5.2: the constraint recording actions for an intermediate CA
/// certificate.
pub open spec fn processing_intermediate_certificate(
    c: crate::path::parsed::spec::PathCert, state: PathState,
) -> PathState {
    PathState {
        // 1) "If the nameConstraints extension with a permittedSubtrees
        //    component is present in the certificate, set the permitted-
        //    subtrees state variable to the intersection of its previous
        //    value and the value indicated in the certificate extension."
        permitted_subtrees: match c.name_constraints {
            Some(nc) => match nc.permitted_subtrees {
                Some(s) => state.permitted_subtrees.push(s),
                None => state.permitted_subtrees,
            },
            None => state.permitted_subtrees,
        },
        // 2) "If the nameConstraints extension with an excludedSubtrees
        //    component is present in the certificate, set the excluded-
        //    subtrees state variable to the union of its previous value and
        //    the value indicated in the certificate extension."
        excluded_subtrees: match c.name_constraints {
            Some(nc) => match nc.excluded_subtrees {
                Some(s) => state.excluded_subtrees.add(s),
                None => state.excluded_subtrees,
            },
            None => state.excluded_subtrees,
        },
        // 3), 4), 5), 6): policy mappings, inhibit-policy-mapping and
        // inhibit-any-policy act only on the table and on the indicators
        // that are not modelled (choice 7).
        // 7) "Increment [path-depth]."
        path_depth: state.path_depth + 1,
        required_name_forms: state.required_name_forms,
        explicit_policy_indicator: state.explicit_policy_indicator,
        explicit_policy_pending: state.explicit_policy_pending,
        explicit_policy_skip_certificates: state.explicit_policy_skip_certificates,
    }
}

// ---------------------------------------------------------------------
// §12.5.3 Explicit policy indicator processing.
// ---------------------------------------------------------------------

/// The lesser of two naturals.
pub open spec fn lesser(a: nat, b: nat) -> nat {
    if a <= b { a } else { b }
}

/// §12.5.3: for all certificates. `intermediate` says whether `c` is an
/// intermediate CA certificate (not the last of the path).
pub open spec fn explicit_policy_indicator_processing(
    c: crate::path::parsed::spec::PathCert, intermediate: bool, state: PathState,
) -> PathState {
    // 1) "If explicit-policy-indicator is not set:"
    if state.explicit_policy_indicator { state }
    else {
        // "– if the explicit-policy-pending indicator is set and the
        //  certificate is not a self-issued intermediate CA certificate,
        //  decrement the corresponding skip-certificates value and, if this
        //  value becomes zero, set explicit-policy-indicator."
        let decremented = state.explicit_policy_pending && !(intermediate && is_self_issued(c));
        let skip: nat = if decremented && state.explicit_policy_skip_certificates > 0 {
            (state.explicit_policy_skip_certificates - 1) as nat
        } else { state.explicit_policy_skip_certificates };
        let after_pending = PathState {
            explicit_policy_indicator: decremented && skip == 0,
            explicit_policy_skip_certificates: skip,
            ..state
        };
        // "– If the requireExplicitPolicy component of the policyConstraints
        //  extension is present in the certificate, perform the following.
        //  For a SkipCerts value of 0, set the explicit-policy-indicator.
        //  For any other SkipCerts value, set the explicit-policy-pending
        //  indicator, and set the corresponding skip-certificates value to
        //  the lesser of the SkipCerts value and the previous skip-
        //  certificates value (if the explicit-policy-pending indicator was
        //  already set)."
        match c.require_explicit_policy {
            None => after_pending,
            Some(skip_certs) =>
                if skip_certs == 0 {
                    PathState { explicit_policy_indicator: true, ..after_pending }
                } else {
                    PathState {
                        explicit_policy_pending: true,
                        explicit_policy_skip_certificates: if after_pending.explicit_policy_pending {
                            lesser(skip_certs, after_pending.explicit_policy_skip_certificates)
                        } else { skip_certs },
                        ..after_pending
                    }
                },
        }
        // "– If the requireExplicitPolicy component ... is present, and the
        //  certification path includes a certificate issued by a nominated
        //  CA, it is necessary for all certificates in the path to contain,
        //  in the certificate policies extension, an acceptable policy
        //  identifier." This explains the indicator; the check is §12.5.4
        //  step 3).
    }
}

// ---------------------------------------------------------------------
// §12.5.4 Final processing.
// ---------------------------------------------------------------------

/// The intersection of two policy sets.
pub open spec fn policy_set_intersection(a: PolicySet, b: PolicySet) -> PolicySet {
    match (a, b) {
        (PolicySet::AnyPolicy, PolicySet::AnyPolicy) => PolicySet::AnyPolicy,
        _ => PolicySet::Empty,
    }
}

/// §12.5.4: final processing, once all certificates are processed.
pub open spec fn final_processing(state: PathState) -> PathOutcome {
    // 1) "Determine the authorities-constrained-policy-set from the
    //    authorities-constrained-policy-set table. ... If the authorities-
    //    constrained-policy-set[0, path-depth] is any-policy, then the
    //    authorities-constrained-policy-set is any-policy." The table is
    //    still its zeroth row (restriction 1).
    let authorities_constrained_policy_set = PolicySet::AnyPolicy;
    // 2) "Calculate the user-constrained-policy-set by forming the
    //    intersection of the authorities-constrained-policy-set and the
    //    initial-policy-set." The initial-policy-set is any-policy (choice 7).
    let user_constrained_policy_set =
        policy_set_intersection(authorities_constrained_policy_set, PolicySet::AnyPolicy);
    // 3) "If the explicit-policy-indicator is set, check that neither the
    //    authorities-constrained-policy-set nor the user-constrained-policy-
    //    set is empty."
    if state.explicit_policy_indicator
        && (authorities_constrained_policy_set == PolicySet::Empty
            || user_constrained_policy_set == PolicySet::Empty) {
        PathOutcome::Failure(FailureReason::EmptyPolicySet)
    } else {
        // "If none of the above checks were to fail on the end certificate,
        //  then the procedure shall terminate, returning a success
        //  indication together with the explicit-policy-indicator, ..."
        PathOutcome::Success { explicit_policy_indicator: state.explicit_policy_indicator }
    }
}

// ---------------------------------------------------------------------
// §12.5 Public-key certificate processing: the loop.
// ---------------------------------------------------------------------

/// §12.5: process `path[i ..]` ("in turn, starting with the public-key
/// certificate signed using the trust anchor public key") from the state
/// after `path[.. i]`.
pub open spec fn process_certificates(
    signature_verifies: spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool,
    anchor: crate::path::parsed::spec::Anchor,
    path: Seq<crate::path::parsed::spec::PathCert>,
    now: crate::time::spec::CertificateTime,
    i: int,
    state: PathState,
) -> PathOutcome
    recommends 0 <= i <= path.len()
    decreases path.len() as int - i
{
    if i >= path.len() {
        // §12.5.4 "Once all certificates in the path have been processed".
        final_processing(state)
    } else {
        let c = path[i];
        let intermediate = i + 1 < path.len();
        // What signed `path[i]`: the trust anchor for the first certificate.
        let key = if i == 0 { anchor.spki_der } else { path[i - 1].tbs.subject_public_key_info_der };
        let issuer_name = if i == 0 { anchor.subject_der } else { path[i - 1].tbs.subject_der };
        // §12.5.1 Basic public-key certificate checks.
        match basic_certificate_checks(signature_verifies, path, i, key, issuer_name, now, state) {
            Some(reason) => PathOutcome::Failure(reason),
            None => {
                // §12.5.2 Processing intermediate certificates (not the last).
                let after_intermediate = if intermediate { processing_intermediate_certificate(c, state) } else { state };
                // §12.5.3 Explicit policy indicator processing (all certificates).
                let after_explicit = explicit_policy_indicator_processing(c, intermediate, after_intermediate);
                process_certificates(signature_verifies, anchor, path, now, i + 1, after_explicit)
            },
        }
    }
}

/// The certification path processing procedure of §12: from the inputs
/// (§12.1) to the outcome (§12.2). `path_in` is `path[0]` the certificate
/// signed with the trust anchor's key, to the end-entity certificate last.
pub open spec fn certification_path_processing(
    signature_verifies: spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool,
    anchor: crate::path::parsed::spec::Anchor,
    path_in: Seq<crate::path::parsed::spec::PathCert>,
    inputs: PathInputs,
) -> PathOutcome {
    // §12.5.1, §12.5.2 "Self-signed certificates, if encountered in the path,
    // are ignored." (choice 11)
    let path = drop_ignored(signature_verifies, path_in, 0);
    if path.len() == 0 { PathOutcome::Failure(FailureReason::EmptyPath) }
    // §12.5.1 b) of the trust anchor information (choice 8).
    else if !anchor_path_length_ok(anchor, path) { PathOutcome::Failure(FailureReason::PathLengthViolated) }
    else {
        // §12.4 Initialization step, then §12.5 each certificate in turn.
        process_certificates(signature_verifies, anchor, path, inputs.now, 0, initialization(anchor, inputs))
    }
}

/// Whether the path is valid (§12.2 a)).
pub open spec fn path_is_valid(
    signature_verifies: spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool,
    anchor: crate::path::parsed::spec::Anchor,
    path: Seq<crate::path::parsed::spec::PathCert>,
    inputs: PathInputs,
) -> bool {
    certification_path_processing(signature_verifies, anchor, path, inputs) is Success
}

// ---------------------------------------------------------------------
// Sanity checks on tiny paths chosen by this author (not taken from any
// other file of the repository). A name is one octet; the key of a
// certificate is its subject's name octet doubled, and a "signature" is the
// key it names, so that `signature_verifies` is a comparison.
// ---------------------------------------------------------------------

/// A time in 2026.
pub open spec fn t(month: u8, day: u8) -> crate::time::spec::CertificateTime {
    crate::time::spec::CertificateTime { year: 2026, month, day, hour: 0, minute: 0, second: 0 }
}

/// The "signature" model of the checks: `cert` verifies under `key` iff its
/// signature bits are `key`.
pub open spec fn toy_signature(c: crate::path::parsed::spec::PathCert, key: Seq<u8>) -> bool {
    c.signature.signature_bits =~= key
}

/// A trust anchor named `[name]` whose key is `[name, name]`.
pub open spec fn toy_anchor(name: u8) -> crate::path::parsed::spec::Anchor {
    crate::path::parsed::spec::Anchor {
        subject_der: seq![name],
        spki_der: seq![name, name],
        name_constraints: None,
        path_len: None,
        not_before: t(1, 1),
        not_after: t(1, 2),
        server_distrust_after: None,
    }
}

/// A v3 certificate for `subject` (key `[subject, subject]`) issued by
/// `issuer` (whose key signs it), valid from 1 March to 1 September 2026,
/// without extensions.
pub open spec fn toy_cert(issuer: u8, subject: u8) -> crate::path::parsed::spec::PathCert {
    let algorithm = crate::certificate::spec::AlgorithmIdentifier { oid: seq![], parameters_der: None };
    crate::path::parsed::spec::PathCert {
        der: seq![],
        envelope: crate::certificate::spec::CertificateEnvelope {
            tbs_certificate_der: seq![],
            signature_algorithm: algorithm,
            signature_unused_bits: 0,
            signature_bits: seq![issuer, issuer],
        },
        tbs: crate::tbs::spec::TbsCertificate {
            version: 2,
            serial_number_der: seq![],
            signature: algorithm,
            issuer_der: seq![issuer],
            not_before: t(3, 1),
            not_after: t(9, 1),
            subject_der: seq![subject],
            subject_public_key_info_der: seq![subject, subject],
            issuer_unique_id_der: None,
            subject_unique_id_der: None,
            extensions_der: None,
            extensions_sequence_der: None,
            tbs_certificate_der: seq![],
        },
        extensions: seq![],
        basic: None,
        key_usage: None,
        eku: None,
        name_constraints: None,
        san: None,
        require_explicit_policy: None,
        has_policy_mappings: false,
        signature: crate::signature_algorithm::spec::PreparedSignature {
            tbs_algorithm: algorithm,
            outer_algorithm: algorithm,
            class: crate::signature_algorithm::spec::AlgorithmClass::Unsupported,
            tbs_der: seq![],
            signature_bits: seq![issuer, issuer],
            signature_unused_bits: 0,
        },
    }
}

/// `toy_cert` that is a CA, with an optional pathLenConstraint (the octets
/// of the magnitude).
pub open spec fn toy_ca(issuer: u8, subject: u8, path_len: Option<Seq<u8>>) -> crate::path::parsed::spec::PathCert {
    crate::path::parsed::spec::PathCert {
        basic: Some(crate::constraints::spec::BasicConstraints { ca: true, path_len_constraint: path_len }),
        ..toy_cert(issuer, subject)
    }
}

/// `toy_cert` with a subjectAltName of one dNSName.
pub open spec fn toy_ee(issuer: u8, subject: u8, dns: Seq<u8>) -> crate::path::parsed::spec::PathCert {
    crate::path::parsed::spec::PathCert {
        san: Some(crate::extensions::spec::SubjectAltName {
            names: seq![crate::extensions::spec::GeneralName::DnsName(dns)],
        }),
        ..toy_cert(issuer, subject)
    }
}

/// A set of one dNSName subtree.
pub open spec fn dns_subtrees(base: Seq<u8>) -> Seq<crate::name_constraints::spec::GeneralSubtree> {
    seq![crate::name_constraints::spec::GeneralSubtree {
        base: crate::name_constraints::spec::GeneralNameConstraint::DnsName(base),
    }]
}

/// Inputs on 15 June 2026 with nothing initial.
pub open spec fn toy_inputs() -> PathInputs {
    PathInputs {
        initial_explicit_policy: false,
        now: t(6, 15),
        initial_permitted_subtrees: None,
        initial_excluded_subtrees: seq![],
        initial_required_name_forms: seq![],
    }
}

/// The accepting path `A -> B (CA) -> C (end entity www.example.com)`.
pub open spec fn toy_path() -> Seq<crate::path::parsed::spec::PathCert> {
    seq![toy_ca(0xA, 0xB, None), toy_ee(0xB, 0xC, seq![0x77u8, 0x77, 0x77, 0x2E, 0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x63, 0x6F, 0x6D])]
}

/// Name matching: the dNSName and iPAddress rules of choice 14.
proof fn name_matching()
    ensures
        // www.example.com is within example.com and within WWW.EXAMPLE.COM,
        dns_within(seq![0x77u8, 0x2E, 0x61, 0x2E, 0x62], seq![0x61u8, 0x2E, 0x62]),
        dns_within(seq![0x57u8, 0x2E, 0x41, 0x2E, 0x42], seq![0x61u8, 0x2E, 0x62]),
        // a.b is within itself and within the empty base,
        dns_within(seq![0x61u8, 0x2E, 0x62], seq![0x61u8, 0x2E, 0x62]),
        dns_within(seq![0x61u8, 0x2E, 0x62], seq![]),
        // but xa.b is not within a.b (no dot), nor b within a.b,
        !dns_within(seq![0x78u8, 0x61, 0x2E, 0x62], seq![0x61u8, 0x2E, 0x62]),
        !dns_within(seq![0x62u8], seq![0x61u8, 0x2E, 0x62]),
        // 10.1.2.3 is within 10.1.0.0/16, 10.2.2.3 is not, nor is an IPv6 name.
        ip_within(seq![10u8, 1, 2, 3], seq![10u8, 1, 0, 0], seq![255u8, 255, 0, 0]),
        !ip_within(seq![10u8, 2, 2, 3], seq![10u8, 1, 0, 0], seq![255u8, 255, 0, 0]),
        !ip_within(seq![10u8, 1, 2, 3, 0, 0], seq![10u8, 1, 0, 0], seq![255u8, 255, 0, 0]),
{
    assert(dns_within(seq![0x77u8, 0x2E, 0x61, 0x2E, 0x62], seq![0x61u8, 0x2E, 0x62])) by (compute);
    assert(dns_within(seq![0x57u8, 0x2E, 0x41, 0x2E, 0x42], seq![0x61u8, 0x2E, 0x62])) by (compute);
    assert(dns_within(seq![0x61u8, 0x2E, 0x62], seq![0x61u8, 0x2E, 0x62])) by (compute);
    assert(dns_within(seq![0x61u8, 0x2E, 0x62], seq![])) by (compute);
    assert(!dns_within(seq![0x78u8, 0x61, 0x2E, 0x62], seq![0x61u8, 0x2E, 0x62])) by (compute);
    assert(!dns_within(seq![0x62u8], seq![0x61u8, 0x2E, 0x62])) by (compute);
    assert(ip_within(seq![10u8, 1, 2, 3], seq![10u8, 1, 0, 0], seq![255u8, 255, 0, 0])) by (compute);
    assert(!ip_within(seq![10u8, 2, 2, 3], seq![10u8, 1, 0, 0], seq![255u8, 255, 0, 0])) by (compute);
    assert(!ip_within(seq![10u8, 1, 2, 3, 0, 0], seq![10u8, 1, 0, 0], seq![255u8, 255, 0, 0])) by (compute);
}

/// `c` with another public key (its subject's), keeping its name.
pub open spec fn toy_rekey(c: crate::path::parsed::spec::PathCert, key: Seq<u8>) -> crate::path::parsed::spec::PathCert {
    crate::path::parsed::spec::PathCert {
        tbs: crate::tbs::spec::TbsCertificate { subject_public_key_info_der: key, ..c.tbs },
        ..c
    }
}

/// `c` signed by `key`.
pub open spec fn toy_signed_by(c: crate::path::parsed::spec::PathCert, key: Seq<u8>) -> crate::path::parsed::spec::PathCert {
    crate::path::parsed::spec::PathCert {
        signature: crate::signature_algorithm::spec::PreparedSignature { signature_bits: key, ..c.signature },
        ..c
    }
}

/// `c` with a nameConstraints extension.
pub open spec fn toy_constrained(
    c: crate::path::parsed::spec::PathCert,
    permitted: Option<Seq<crate::name_constraints::spec::GeneralSubtree>>,
    excluded: Option<Seq<crate::name_constraints::spec::GeneralSubtree>>,
) -> crate::path::parsed::spec::PathCert {
    crate::path::parsed::spec::PathCert {
        name_constraints: Some(crate::name_constraints::spec::NameConstraints {
            permitted_subtrees: permitted,
            excluded_subtrees: excluded,
        }),
        ..c
    }
}

/// `c` with requireExplicitPolicy `skip`.
pub open spec fn toy_require_explicit(c: crate::path::parsed::spec::PathCert, skip: nat) -> crate::path::parsed::spec::PathCert {
    crate::path::parsed::spec::PathCert { require_explicit_policy: Some(skip), ..c }
}

/// The signature oracle of the checks.
pub open spec fn toy_sig() -> spec_fn(crate::path::parsed::spec::PathCert, Seq<u8>) -> bool {
    |c: crate::path::parsed::spec::PathCert, key: Seq<u8>| toy_signature(c, key)
}

/// "example.com".
pub open spec fn example_com() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x63, 0x6F, 0x6D]
}

/// "example.org".
pub open spec fn example_org() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x6F, 0x72, 0x67]
}

/// Success with an explicit-policy-indicator (a struct literal does not parse
/// after `==` in an `ensures`).
pub open spec fn success(explicit_policy_indicator: bool) -> PathOutcome {
    PathOutcome::Success { explicit_policy_indicator }
}

/// A tiny path that is accepted (A -> B -> C).
proof fn accepting_path()
    ensures
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(), toy_inputs())
            == success(false),
        path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(), toy_inputs()),
        profile_domain(toy_anchor(0xA), toy_path(), toy_inputs()),
{
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(), toy_inputs())
        == success(false)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(), toy_inputs())) by (compute);
    assert(profile_domain(toy_anchor(0xA), toy_path(), toy_inputs())) by (compute);
}

/// §12.5.1 a): expired, not yet valid, the wrong key, names that do not chain.
proof fn basic_check_rejections()
    ensures
        // now is after notAfter (1 September) / before notBefore (1 March).
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { now: t(10, 1), ..toy_inputs() })
            == PathOutcome::Failure(FailureReason::Expired),
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { now: t(2, 1), ..toy_inputs() })
            == PathOutcome::Failure(FailureReason::NotYetValid),
        // The dates are a closed interval.
        path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(), PathInputs { now: t(9, 1), ..toy_inputs() }),
        path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(), PathInputs { now: t(3, 1), ..toy_inputs() }),
        // A path from a different anchor: the first signature does not verify.
        certification_path_processing(toy_sig(), toy_anchor(0xD), toy_path(), toy_inputs())
            == PathOutcome::Failure(FailureReason::SignatureDoesNotVerify),
        // The right key but the wrong issuer name.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_signed_by(toy_ca(0xD, 0xB, None), seq![0xAu8, 0xA]), toy_path()[1]], toy_inputs())
            == PathOutcome::Failure(FailureReason::NamesDoNotChain),
        // No certificate.
        certification_path_processing(toy_sig(), toy_anchor(0xA), seq![], toy_inputs())
            == PathOutcome::Failure(FailureReason::EmptyPath),
{
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { now: t(10, 1), ..toy_inputs() }) == PathOutcome::Failure(FailureReason::Expired)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { now: t(2, 1), ..toy_inputs() }) == PathOutcome::Failure(FailureReason::NotYetValid)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(), PathInputs { now: t(9, 1), ..toy_inputs() })) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(), PathInputs { now: t(3, 1), ..toy_inputs() })) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xD), toy_path(), toy_inputs())
        == PathOutcome::Failure(FailureReason::SignatureDoesNotVerify)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_signed_by(toy_ca(0xD, 0xB, None), seq![0xAu8, 0xA]), toy_path()[1]], toy_inputs())
        == PathOutcome::Failure(FailureReason::NamesDoNotChain)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), seq![], toy_inputs())
        == PathOutcome::Failure(FailureReason::EmptyPath)) by (compute);
}

/// §12.5.1 b): the intermediate certificate must have basicConstraints with
/// cA TRUE (a version 3 one).
proof fn ca_flag_rejections()
    ensures
        // No basicConstraints.
        certification_path_processing(toy_sig(), toy_anchor(0xA), seq![toy_cert(0xA, 0xB), toy_path()[1]], toy_inputs())
            == PathOutcome::Failure(FailureReason::NotACaCertificate),
        // cA FALSE.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![crate::path::parsed::spec::PathCert {
                basic: Some(crate::constraints::spec::BasicConstraints { ca: false, path_len_constraint: None }),
                ..toy_cert(0xA, 0xB)
            }, toy_path()[1]], toy_inputs())
            == PathOutcome::Failure(FailureReason::NotACaCertificate),
        // The end entity is not an intermediate: no basicConstraints needed.
        path_is_valid(toy_sig(), toy_anchor(0xA), seq![toy_ee(0xA, 0xC, example_com())], toy_inputs()),
{
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), seq![toy_cert(0xA, 0xB), toy_path()[1]], toy_inputs())
        == PathOutcome::Failure(FailureReason::NotACaCertificate)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![crate::path::parsed::spec::PathCert {
            basic: Some(crate::constraints::spec::BasicConstraints { ca: false, path_len_constraint: None }),
            ..toy_cert(0xA, 0xB)
        }, toy_path()[1]], toy_inputs())
        == PathOutcome::Failure(FailureReason::NotACaCertificate)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA), seq![toy_ee(0xA, 0xC, example_com())], toy_inputs())) by (compute);
}

/// §12.5.1 b): pathLenConstraint, with self-issued intermediate certificates
/// not counted, and the trust anchor's own constraint.
proof fn path_length_checks()
    ensures
        // A (anchor) -> B (CA, pathLen 0) -> D (CA) -> C (end entity): D follows B.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_ca(0xA, 0xB, Some(seq![0u8])), toy_ca(0xB, 0xD, None), toy_ee(0xD, 0xC, example_com())],
            toy_inputs())
            == PathOutcome::Failure(FailureReason::PathLengthViolated),
        // The same with pathLen 1.
        path_is_valid(toy_sig(), toy_anchor(0xA),
            seq![toy_ca(0xA, 0xB, Some(seq![1u8])), toy_ca(0xB, 0xD, None), toy_ee(0xD, 0xC, example_com())],
            toy_inputs()),
        // B (pathLen 0) -> B' (self-issued, another key) -> C: B' does not count.
        path_is_valid(toy_sig(), toy_anchor(0xA),
            seq![toy_ca(0xA, 0xB, Some(seq![0u8])),
                 toy_rekey(toy_ca(0xB, 0xB, None), seq![0xBBu8, 0xBB]),
                 toy_signed_by(toy_ee(0xB, 0xC, example_com()), seq![0xBBu8, 0xBB])],
            toy_inputs()),
        // The anchor's pathLenConstraint 0 allows no intermediate certificate...
        certification_path_processing(toy_sig(),
            crate::path::parsed::spec::Anchor { path_len: Some(0), ..toy_anchor(0xA) },
            toy_path(), toy_inputs())
            == PathOutcome::Failure(FailureReason::PathLengthViolated),
        // ... and 1 allows one.
        path_is_valid(toy_sig(), crate::path::parsed::spec::Anchor { path_len: Some(1), ..toy_anchor(0xA) },
            toy_path(), toy_inputs()),
{
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_ca(0xA, 0xB, Some(seq![0u8])), toy_ca(0xB, 0xD, None), toy_ee(0xD, 0xC, example_com())],
        toy_inputs()) == PathOutcome::Failure(FailureReason::PathLengthViolated)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA),
        seq![toy_ca(0xA, 0xB, Some(seq![1u8])), toy_ca(0xB, 0xD, None), toy_ee(0xD, 0xC, example_com())],
        toy_inputs())) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA),
        seq![toy_ca(0xA, 0xB, Some(seq![0u8])),
             toy_rekey(toy_ca(0xB, 0xB, None), seq![0xBBu8, 0xBB]),
             toy_signed_by(toy_ee(0xB, 0xC, example_com()), seq![0xBBu8, 0xBB])],
        toy_inputs())) by (compute);
    assert(certification_path_processing(toy_sig(),
        crate::path::parsed::spec::Anchor { path_len: Some(0), ..toy_anchor(0xA) },
        toy_path(), toy_inputs()) == PathOutcome::Failure(FailureReason::PathLengthViolated)) by (compute);
    assert(path_is_valid(toy_sig(), crate::path::parsed::spec::Anchor { path_len: Some(1), ..toy_anchor(0xA) },
        toy_path(), toy_inputs())) by (compute);
}

/// §12.5.1 g) and §12.5.2 steps 1) and 2): permitted and excluded dNSName
/// subtrees, on the certificates after the one that carries them.
proof fn name_constraint_checks()
    ensures
        // B excludes example.com: C's www.example.com is within it.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_constrained(toy_ca(0xA, 0xB, None), None, Some(dns_subtrees(example_com()))), toy_path()[1]],
            toy_inputs())
            == PathOutcome::Failure(FailureReason::SubjectNameExcluded),
        // B excludes example.org: it is not.
        path_is_valid(toy_sig(), toy_anchor(0xA),
            seq![toy_constrained(toy_ca(0xA, 0xB, None), None, Some(dns_subtrees(example_org()))), toy_path()[1]],
            toy_inputs()),
        // B permits only example.org: www.example.com is not permitted.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_org())), None), toy_path()[1]],
            toy_inputs())
            == PathOutcome::Failure(FailureReason::SubjectNameNotPermitted),
        // B permits example.com.
        path_is_valid(toy_sig(), toy_anchor(0xA),
            seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_com())), None), toy_path()[1]],
            toy_inputs()),
        // The exclusion takes precedence over a permission.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_com())),
                Some(dns_subtrees(example_com()))), toy_path()[1]],
            toy_inputs())
            == PathOutcome::Failure(FailureReason::SubjectNameExcluded),
        // B's own constraints do not apply to B: its dNSName example.com is
        // not within the example.org it permits.
        path_is_valid(toy_sig(), toy_anchor(0xA),
            seq![crate::path::parsed::spec::PathCert {
                    san: toy_ee(0xA, 0xB, example_com()).san,
                    ..toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_org())), None)
                 },
                 toy_ca(0xB, 0xD, None), toy_ee(0xD, 0xC, example_org())],
            toy_inputs()),
        // An initial excluded subtree (§12.1 i)) acts from the first certificate.
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { initial_excluded_subtrees: dns_subtrees(example_com()), ..toy_inputs() })
            == PathOutcome::Failure(FailureReason::SubjectNameExcluded),
        // Permitted subtrees of two CAs are intersected: example.com then
        // example.org permit nothing of either.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_com())), None),
                 toy_constrained(toy_ca(0xB, 0xD, None), Some(dns_subtrees(example_org())), None),
                 toy_ee(0xD, 0xC, example_com())],
            toy_inputs())
            == PathOutcome::Failure(FailureReason::SubjectNameNotPermitted),
{
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_constrained(toy_ca(0xA, 0xB, None), None, Some(dns_subtrees(example_com()))), toy_path()[1]],
        toy_inputs()) == PathOutcome::Failure(FailureReason::SubjectNameExcluded)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA),
        seq![toy_constrained(toy_ca(0xA, 0xB, None), None, Some(dns_subtrees(example_org()))), toy_path()[1]],
        toy_inputs())) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_org())), None), toy_path()[1]],
        toy_inputs()) == PathOutcome::Failure(FailureReason::SubjectNameNotPermitted)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA),
        seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_com())), None), toy_path()[1]],
        toy_inputs())) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_com())),
            Some(dns_subtrees(example_com()))), toy_path()[1]],
        toy_inputs()) == PathOutcome::Failure(FailureReason::SubjectNameExcluded)) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA),
        seq![crate::path::parsed::spec::PathCert {
                san: toy_ee(0xA, 0xB, example_com()).san,
                ..toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_org())), None)
             },
             toy_ca(0xB, 0xD, None), toy_ee(0xD, 0xC, example_org())],
        toy_inputs())) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { initial_excluded_subtrees: dns_subtrees(example_com()), ..toy_inputs() })
        == PathOutcome::Failure(FailureReason::SubjectNameExcluded)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_constrained(toy_ca(0xA, 0xB, None), Some(dns_subtrees(example_com())), None),
             toy_constrained(toy_ca(0xB, 0xD, None), Some(dns_subtrees(example_org())), None),
             toy_ee(0xD, 0xC, example_com())],
        toy_inputs()) == PathOutcome::Failure(FailureReason::SubjectNameNotPermitted)) by (compute);
}

/// §12.5.1 h): required name forms.
proof fn required_name_form_checks()
    ensures
        // Both certificates have a subject (a directoryName); only C has a
        // dNSName; neither has an iPAddress. Every certificate that is not a
        // self-issued intermediate is checked, B included.
        path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { initial_required_name_forms: seq![seq![NameForm::DirectoryName]], ..toy_inputs() }),
        path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs {
                initial_required_name_forms: seq![seq![NameForm::IpAddress, NameForm::DirectoryName]],
                ..toy_inputs()
            }),
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { initial_required_name_forms: seq![seq![NameForm::DnsName]], ..toy_inputs() })
            == PathOutcome::Failure(FailureReason::RequiredNameFormMissing),
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { initial_required_name_forms: seq![seq![NameForm::IpAddress]], ..toy_inputs() })
            == PathOutcome::Failure(FailureReason::RequiredNameFormMissing),
{
    assert(path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { initial_required_name_forms: seq![seq![NameForm::DirectoryName]], ..toy_inputs() })) by (compute);
    assert(path_is_valid(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs {
            initial_required_name_forms: seq![seq![NameForm::IpAddress, NameForm::DirectoryName]],
            ..toy_inputs()
        })) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { initial_required_name_forms: seq![seq![NameForm::DnsName]], ..toy_inputs() })
        == PathOutcome::Failure(FailureReason::RequiredNameFormMissing)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { initial_required_name_forms: seq![seq![NameForm::IpAddress]], ..toy_inputs() })
        == PathOutcome::Failure(FailureReason::RequiredNameFormMissing)) by (compute);
}

/// §12.5.1, §12.5.2, §9.1.5: self-signed certificates are ignored, except
/// at the end.
proof fn self_signed_checks()
    ensures
        // A self-signed copy of the anchor's certificate at the start is ignored.
        path_is_valid(toy_sig(), toy_anchor(0xA),
            seq![toy_ca(0xA, 0xA, None), toy_path()[0], toy_path()[1]], toy_inputs()),
        // A self-signed certificate that the anchor did not sign, as the whole
        // path, is the end entity, which is not ignored: its signature fails.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_ca(0xD, 0xD, None)], toy_inputs())
            == PathOutcome::Failure(FailureReason::SignatureDoesNotVerify),
{
    assert(path_is_valid(toy_sig(), toy_anchor(0xA),
        seq![toy_ca(0xA, 0xA, None), toy_path()[0], toy_path()[1]], toy_inputs())) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), seq![toy_ca(0xD, 0xD, None)], toy_inputs())
        == PathOutcome::Failure(FailureReason::SignatureDoesNotVerify)) by (compute);
}

/// §12.5.3: the explicit-policy-indicator, with SkipCerts counted in
/// non-self-issued certificates.
proof fn explicit_policy_checks()
    ensures
        // initial-explicit-policy is passed through.
        certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
            PathInputs { initial_explicit_policy: true, ..toy_inputs() })
            == success(true),
        // requireExplicitPolicy 0 on B sets it at B.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 0), toy_path()[1]], toy_inputs())
            == success(true),
        // requireExplicitPolicy 1 on B: pending at B, set at C.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 1), toy_path()[1]], toy_inputs())
            == success(true),
        // requireExplicitPolicy 2 on B: the path ends first.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 2), toy_path()[1]], toy_inputs())
            == success(false),
        // requireExplicitPolicy 1 on B, then a self-issued intermediate B'
        // (not counted), then C: set at C.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 1),
                 toy_rekey(toy_ca(0xB, 0xB, None), seq![0xBBu8, 0xBB]),
                 toy_signed_by(toy_ee(0xB, 0xC, example_com()), seq![0xBBu8, 0xBB])], toy_inputs())
            == success(true),
        // requireExplicitPolicy 2 on B, then a self-issued B', then D, then C:
        // B' does not count, so D is the first skipped and C the second: set at C.
        certification_path_processing(toy_sig(), toy_anchor(0xA),
            seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 2),
                 toy_rekey(toy_ca(0xB, 0xB, None), seq![0xBBu8, 0xBB]),
                 toy_signed_by(toy_ca(0xB, 0xD, None), seq![0xBBu8, 0xBB]),
                 toy_ee(0xD, 0xC, example_com())], toy_inputs())
            == success(true),
{
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA), toy_path(),
        PathInputs { initial_explicit_policy: true, ..toy_inputs() })
        == success(true)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 0), toy_path()[1]], toy_inputs())
        == success(true)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 1), toy_path()[1]], toy_inputs())
        == success(true)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 2), toy_path()[1]], toy_inputs())
        == success(false)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 1),
             toy_rekey(toy_ca(0xB, 0xB, None), seq![0xBBu8, 0xBB]),
             toy_signed_by(toy_ee(0xB, 0xC, example_com()), seq![0xBBu8, 0xBB])], toy_inputs())
        == success(true)) by (compute);
    assert(certification_path_processing(toy_sig(), toy_anchor(0xA),
        seq![toy_require_explicit(toy_ca(0xA, 0xB, None), 2),
             toy_rekey(toy_ca(0xB, 0xB, None), seq![0xBBu8, 0xBB]),
             toy_signed_by(toy_ca(0xB, 0xD, None), seq![0xBBu8, 0xBB]),
             toy_ee(0xD, 0xC, example_com())], toy_inputs())
        == success(true)) by (compute);
}

} // verus!
