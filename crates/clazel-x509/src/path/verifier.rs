//! The verdict on a presented TLS server chain: RFC 5280 §6.1 (`spec.rs`)
//! and the browser profile (`profile.rs`) on one candidate path, the bounds
//! of the design's §1.12, and the contract the top-level verifier meets
//! (design §2.6, §3.5).
//!
//! Sources: as `spec.rs` and `profile.rs`; RFC 8446 §4.4.2 ("The sender's
//! certificate MUST come in the first CertificateEntry in the list. Each
//! following certificate SHOULD directly certify the one immediately
//! preceding it" and "clients SHOULD be prepared to handle potentially
//! extraneous certificates and arbitrary orderings from any TLS version"),
//! <https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2>; RFC 4158 (path
//! building, guidance only).
//!
//! What is here and what is not:
//! - **One candidate path** is an anchor index and a sequence of pool
//!   indices (`Candidate`, design §2.6). `candidate_verdict` is the whole
//!   verdict on it: well-formedness, `profile::path_profile`, `spec::process`
//!   and the name-constraint comparison bound.
//! - **The chain** is accepted when *some* candidate is valid
//!   (`some_candidate_valid`). Which candidate the verifier returns, the
//!   bounded depth-first search that finds it (design §2.6: anchors first,
//!   then pool certificates in message order) and the theorems about that
//!   search are P9's (`build.rs`, `chain.rs`). `verify_server_chain_ensures`
//!   is the contract P9's executable verifier must meet: an `Ok` is a valid
//!   candidate; `BuildBudgetExhausted` means the search's first 200,000
//!   candidate-issuer steps held no valid path; any other error means no
//!   candidate is valid.
//!
//! Modelling choices:
//! - **The reference identity is typed** (design Q2, decided 2026-10-29): a
//!   `crate::spec::ReferenceIdentity`, DNS or IP, as the URL layer produces
//!   it. IP references match only iPAddress subjectAltName entries and DNS
//!   references only dNSName entries (`crate::spec::service_identity_match`).
//!   No host bytes are re-parsed here.
//! - **The clock** is Unix seconds (`now: u64`, as `clazel-tls`'s
//!   `ChainValidation` passes it), converted by
//!   `time::spec::from_unix_seconds`; a time past the year 9999 refuses
//!   (`Malformed`).
//! - **The presented chain** is the TLS Certificate message's certificates
//!   in order, `presented[0]` the server's own (RFC 8446 §4.4.2). The others
//!   are a pool, used in any order (design Q3). **(I)** A pool certificate
//!   that `parse_path_cert` refuses is dropped from the pool rather than
//!   refusing the chain (design §2.6 step 3); a path simply cannot use it.
//!   A first certificate that does not parse refuses (`Malformed`).
//! - **Trust anchors** are a parameter, `anchors`; the production value is
//!   every `roots::ROOTS` entry for which `parsed::spec::anchor_from_root` is
//!   `Some`.
//! - **Revocation and signatures** are the parameters of `spec.rs`, in
//!   `Environment`. **(I)** Certificate Transparency is not checked (design
//!   Q4: Phase 8).
//! - **Bounds** (design §1.12, Q13, decided 2026-10-29 by Alex: "Drop the
//!   cap. Follow one of the other browser's approaches"; Firefox's is
//!   followed). The source is mozilla::pkix `lib/mozpkix/lib/pkixbuild.cpp`
//!   (NSS `master`, read 2026-10-29):
//!   - **No cap on the certificates supplied (=).** Neither browser caps
//!     the number of certificates a server sends; the search's work is
//!     bounded by the budget below instead. (A Certificate message is in any
//!     case at most 2^24 - 1 bytes, RFC 8446 §4.)
//!   - **Depth (=).** At most `max_intermediates` intermediates in a
//!     candidate, 6 in production: `BuildForward`'s "static const unsigned
//!     int MAX_SUBCA_COUNT = 6;" and "if (subCACount >= MAX_SUBCA_COUNT) {
//!     return Result::ERROR_UNKNOWN_ISSUER; }", which runs for every CA
//!     certificate that is not a trust anchor (after the trust-anchor
//!     return, before `FindIssuer`) and has no exception for self-issued
//!     ones. So self-issued intermediates count here too. A longer candidate
//!     is not a candidate (limbo's `max_chain_depth` sets the parameter per
//!     test case; it does not count self-issued certificates, a listed
//!     difference of the harness).
//!   - **Work budget.** At most `build_budget()` = 200,000 candidate-issuer
//!     steps: `BuildCertChain`'s "unsigned int buildForwardCallBudget =
//!     200000;", checked in `PathBuildingStep::Check` ("if
//!     (buildForwardCallBudget == 0)", recording `ERROR_UNKNOWN_ISSUER` and
//!     stopping) and decremented ("buildForwardCallBudget--;") once per
//!     potential issuer that passes the subject-name, loop, name-constraint
//!     and TLS-feature checks, before the recursive `BuildForward` and
//!     before `VerifySignedData`. Here a step (`IssuerStep`) is one
//!     name-chained, loop-free candidate issuer (an anchor or a pool
//!     certificate) examined by the search, and the error is
//!     `BuildBudgetExhausted`. **(R)** A step is counted on names alone, so
//!     a candidate issuer whose name constraints Firefox would refuse before
//!     counting is counted here: for the same order, this exhausts no later.
//!     The order is design §2.6's (anchors in table order, then pool
//!     certificates in message order, depth first), not Firefox's trust
//!     domain's `FindIssuer` order, so which chains exhaust differs in detail.
//!     **(=)** Firefox counts trust-anchor candidates as steps (they reach
//!     `Check` as potential issuers), and so does this.
//!   - **Why the budget is a parameterised predicate.** Whether the budget
//!     runs out depends on the search's order and on where it stops (at the
//!     first valid candidate), which is P9's enumeration. So
//!     `verify_server_chain_ensures` takes that order as `order`, the
//!     sequence of steps the search examines, and constrains it only by
//!     `search_order_well_formed` (every step name-chained, none twice).
//!     P9 defines the order and proves its executable search examines exactly
//!     it. Even before P9, exhaustion means more than 200,000 distinct
//!     name-chained steps exist and the first 200,000 completed none valid.
//!   - **Name constraints.** At most 4,096 name-constraint comparisons per
//!     path, counted as P5's contract counts them (`within_budget`, below)
//!     (`TooManyNameComparisons`). Both browsers bound name-constraint work
//!     (design §1.12); this is P5's bound, kept.
//!
//! For P16, the intended `clazel-tls` join (not changed here). `auth::spec`'s
//! `ChainValidation` becomes
//! `spec_fn(crate::spec::ReferenceIdentity, u64, Seq<u8>) -> Result<Seq<u8>, CertificateError>`:
//! the typed reference identity, the clock and the Certificate message body.
//! Its instance (in `clazel-crypto`, design §3.1) parses the body's
//! CertificateEntry list with `clazel_tls::spec`, takes each entry's
//! `cert_data` in order as `presented`, and returns the `Ok` value's
//! `leaf_spki` of a verifier meeting `verify_server_chain_ensures` with the
//! production anchors, `max_intermediates` 6, P11's `link` and `revoked` =
//! nothing. `auth::spec::Config.host` and `hello::client_spec::Config` carry
//! the typed host. The intended mapping of errors to the `CertificateError`
//! alerts: `Expired` and `AnchorExpired` to `Expired` (45);
//! `UnsupportedAlgorithm` to `Unsupported` (43); `UnknownIssuer`,
//! `BadSignature`, `NameChaining`, `Distrusted`, `Revoked` and
//! `BuildBudgetExhausted` (Firefox: `ERROR_UNKNOWN_ISSUER`) to `UnknownCa`
//! (48); every other error to
//! `BadCertificate` (42).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Parameters and results
// ---------------------------------------------------------------------------

/// The verifier's parameters that are not data from the peer.
pub struct Environment {
    /// §6.1.3 (a)(1): link signature verification (P11's instance).
    pub link: super::spec::LinkFn,
    /// §6.1.3 (a)(3): revocation (production: nothing is revoked).
    pub revoked: super::spec::RevokedFn,
    /// Design §1.12: the most intermediates a candidate may have (6).
    pub max_intermediates: nat,
}

/// A candidate path (design §2.6): `anchors[anchor]`, then the pool
/// certificates `path[0]`, ..., `path[len-1]` (the anchor's child first),
/// then the presented leaf.
pub struct Candidate {
    /// Index into the anchors.
    pub anchor: nat,
    /// Indices into the pool (`presented[1..]`), the anchor's child first.
    pub path: Seq<nat>,
}

/// An accepted chain (design §2.6).
pub struct Validated {
    /// Index of the anchor the path reaches.
    pub anchor: nat,
    /// The pool indices of the intermediates, the anchor's child first.
    pub path: Seq<nat>,
    /// The target's complete SubjectPublicKeyInfo DER (§6.1.6's
    /// working_public_key), the key `ChainValidation` returns.
    pub leaf_spki: Seq<u8>,
}

// ---------------------------------------------------------------------------
// Bounds (design §1.12)
// ---------------------------------------------------------------------------

/// The production `max_intermediates`: mozilla::pkix `MAX_SUBCA_COUNT`.
pub open spec fn default_max_intermediates() -> nat { 6 }

/// At most this many candidate-issuer steps are examined: mozilla::pkix
/// `buildForwardCallBudget`.
pub open spec fn build_budget() -> nat { 200000 }

/// At most this many subjectAltName-entry by subtree comparisons per path.
/// The definitions down to `within_budget` are those of P5's contract
/// (`name_constraints/matching/contract.rs` on PR #40, not yet on this
/// branch), restated so the bound is part of the spec; once #40 is merged
/// they should be replaced by P5's, which are the same text.
pub open spec fn comparison_bound() -> nat { 4096 }

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

/// Every certificate of `path[i..]` stays within the bound, `spent` being the
/// comparisons of `path[..i]`, with the state evolution of P4's
/// `names_constrained_from`.
pub open spec fn within_budget_from(
    path: Seq<crate::name_constraints::matching::spec::NcCertificate>, i: int,
    state: Seq<crate::name_constraints::spec::NameConstraints>, spent: nat,
) -> bool
    decreases path.len() - i
{
    if i < 0 || i >= path.len() { true }
    else {
        let certificate = path[i];
        let total = spent + comparisons(certificate.subject_alt_names.len(), subtree_count(state));
        &&& total <= comparison_bound()
        &&& i == path.len() - 1 || match crate::name_constraints::matching::spec::prepare_name_constraints(
            state, certificate.name_constraints) {
            Some(next) => within_budget_from(path, i + 1, next, total),
            None => true,
        }
    }
}

/// The whole path within the bound, from `initial`.
pub open spec fn within_budget(
    path: Seq<crate::name_constraints::matching::spec::NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
) -> bool {
    within_budget_from(path, 0, initial, 0)
}

/// What P4 reads from each certificate of a path, in order.
pub open spec fn nc_path(certs: Seq<super::parsed::spec::PathCert>)
    -> Seq<crate::name_constraints::matching::spec::NcCertificate>
    decreases certs.len()
{
    if certs.len() == 0 { seq![] }
    else { nc_path(certs.drop_last()).push(super::spec::nc_certificate(certs.last())) }
}

/// The name-constraint state the anchor starts a path with (RFC 5937 §3.2
/// bullets 2 and 3), or `None` when it is unsupported (`spec::initialization`
/// then refuses).
pub open spec fn anchor_subtrees(anchor: super::parsed::spec::Anchor)
    -> Option<Seq<crate::name_constraints::spec::NameConstraints>>
{
    crate::name_constraints::matching::spec::prepare_name_constraints(
        crate::name_constraints::matching::spec::initial_state(), anchor.name_constraints)
}

/// A path within the comparison bound (vacuous when the anchor's constraints
/// are unsupported, which `spec::process` refuses anyway).
pub open spec fn path_within_budget(anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>) -> bool {
    match anchor_subtrees(anchor) {
        Some(initial) => within_budget(nc_path(certs), initial),
        None => true,
    }
}

// ---------------------------------------------------------------------------
// One candidate
// ---------------------------------------------------------------------------

/// `index` is not among `path[from..]`.
pub open spec fn index_absent_from(path: Seq<nat>, index: nat, from: int) -> bool
    decreases path.len() - from
{
    if from < 0 || from >= path.len() { true }
    else { path[from] != index && index_absent_from(path, index, from + 1) }
}

/// No index of `path[from..]` repeats.
pub open spec fn indices_distinct_from(path: Seq<nat>, from: int) -> bool
    decreases path.len() - from
{
    if from < 0 || from >= path.len() { true }
    else { index_absent_from(path, path[from], from + 1) && indices_distinct_from(path, from + 1) }
}

/// Every index of `path[from..]` names a pool certificate that parsed.
pub open spec fn indices_usable_from(pool: Seq<Option<super::parsed::spec::PathCert>>, path: Seq<nat>, from: int) -> bool
    decreases path.len() - from
{
    if from < 0 || from >= path.len() { true }
    else { path[from] < pool.len() && pool[path[from] as int] is Some && indices_usable_from(pool, path, from + 1) }
}

/// A candidate names an anchor, at most `max_intermediates` usable pool
/// certificates, and none twice (design §2.6).
pub open spec fn candidate_well_formed(
    anchors: Seq<super::parsed::spec::Anchor>, pool: Seq<Option<super::parsed::spec::PathCert>>,
    candidate: Candidate, max_intermediates: nat,
) -> bool {
    &&& candidate.anchor < anchors.len()
    &&& candidate.path.len() <= max_intermediates
    &&& indices_usable_from(pool, candidate.path, 0)
    &&& indices_distinct_from(candidate.path, 0)
}

/// The intermediates a candidate names, the anchor's child first.
pub open spec fn intermediates_of(pool: Seq<Option<super::parsed::spec::PathCert>>, path: Seq<nat>)
    -> Seq<super::parsed::spec::PathCert>
    decreases path.len()
{
    if path.len() == 0 { seq![] }
    else {
        let index = path.last();
        let cert = if index < pool.len() { match pool[index as int] { Some(c) => c, None => arbitrary() } }
            else { arbitrary() };
        intermediates_of(pool, path.drop_last()).push(cert)
    }
}

/// §6.1.1 (a): the prospective path of a candidate, certificate 1 first and
/// the leaf last.
pub open spec fn candidate_certificates(
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert, candidate: Candidate,
) -> Seq<super::parsed::spec::PathCert> {
    intermediates_of(pool, candidate.path).push(leaf)
}

/// The verdict on one candidate: well-formed, then the profile, then §6.1,
/// then the comparison bound. `Ok` carries the target's key.
pub open spec fn candidate_verdict(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    candidate: Candidate, reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> Result<Seq<u8>, super::spec::PathError> {
    if !candidate_well_formed(anchors, pool, candidate, environment.max_intermediates) {
        // A path longer than the bound, or through an unusable certificate,
        // is not a candidate.
        if candidate.path.len() > environment.max_intermediates { Err(super::spec::PathError::TooManyIntermediates) }
        else { Err(super::spec::PathError::UnknownIssuer) }
    } else {
        let anchor = anchors[candidate.anchor as int];
        let certs = candidate_certificates(pool, leaf, candidate);
        match super::profile::path_profile(anchor, certs, reference, now) {
            Err(e) => Err(e),
            Ok(()) => match super::spec::process(environment.link, environment.revoked, anchor, certs, now) {
                Err(e) => Err(e),
                Ok(key) => if !path_within_budget(anchor, certs) { Err(super::spec::PathError::TooManyNameComparisons) }
                    else { Ok(key) },
            },
        }
    }
}

/// A candidate on which the verdict is `Ok`.
pub open spec fn candidate_valid(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    candidate: Candidate, reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> bool {
    candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now) is Ok
}

// ---------------------------------------------------------------------------
// The presented chain
// ---------------------------------------------------------------------------

/// The pool: every presented certificate after the first, parsed; `None`
/// where it does not parse (dropped, (I)).
pub open spec fn parsed_pool(presented: Seq<Seq<u8>>) -> Seq<Option<super::parsed::spec::PathCert>>
    decreases presented.len()
{
    if presented.len() <= 1 { seq![] }
    else { parsed_pool(presented.drop_last()).push(super::parsed::spec::parse_path_cert(presented.last())) }
}

/// What the verdict starts from: the leaf, the pool and the time.
pub struct ChainInputs {
    /// `presented[0]`, parsed.
    pub leaf: super::parsed::spec::PathCert,
    /// `presented[1..]`, parsed.
    pub pool: Seq<Option<super::parsed::spec::PathCert>>,
    /// `now`, as a certificate time.
    pub now: crate::time::spec::CertificateTime,
}

/// The inputs, or the error that refuses the chain before any path is tried.
pub open spec fn chain_inputs(presented: Seq<Seq<u8>>, now: u64) -> Result<ChainInputs, super::spec::PathError> {
    // 1. RFC 8446 §4.4.2: the server's own certificate comes first. (No cap
    //    on how many follow: design §1.12, as Firefox.)
    if presented.len() == 0 { Err(super::spec::PathError::Malformed) }
    else { match (super::parsed::spec::parse_path_cert(presented[0]), crate::time::spec::from_unix_seconds(now as nat)) {
        // 2. The leaf parses, and the time is one a certificate can name.
        (Some(leaf), Some(time)) => Ok(ChainInputs { leaf, pool: parsed_pool(presented), now: time }),
        _ => Err(super::spec::PathError::Malformed),
    }}
}

/// The chain is acceptable: some candidate path is valid.
pub open spec fn some_candidate_valid(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64,
) -> bool {
    match chain_inputs(presented, now) {
        Err(_) => false,
        Ok(inputs) => exists|candidate: Candidate|
            candidate_valid(environment, anchors, inputs.pool, inputs.leaf, candidate, reference, inputs.now),
    }
}

// ---------------------------------------------------------------------------
// The search budget (design §1.12; mozilla::pkix buildForwardCallBudget)
// ---------------------------------------------------------------------------

/// A candidate issuer the search examines: an anchor or a pool certificate.
pub enum Issuer {
    /// `anchors[i]`.
    Anchor(nat),
    /// `pool[j]`.
    Pool(nat),
}

/// One step of the search: the issuer examined for the top of `path` (the
/// leaf when `path` is empty, else `pool[path[0]]`), `path` being the pool
/// indices chosen so far, the anchor's child first (as in `Candidate`).
pub struct IssuerStep {
    /// The partial path whose top certificate's issuer is sought.
    pub path: Seq<nat>,
    /// The candidate issuer examined.
    pub issuer: Issuer,
}

/// The issuer name the search looks for above `path`.
pub open spec fn sought_issuer(
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert, path: Seq<nat>,
) -> Seq<u8> {
    if path.len() == 0 { leaf.tbs.issuer_der }
    else if path[0] < pool.len() { match pool[path[0] as int] { Some(c) => c.tbs.issuer_der, None => leaf.tbs.issuer_der } }
    else { leaf.tbs.issuer_der }
}

/// A step Firefox would count (after its name and loop checks): the issuer
/// exists and its subject is the sought name; a pool issuer is usable, not
/// already on the path, and the path stays within `max_intermediates`.
pub open spec fn step_name_chained(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert, step: IssuerStep,
) -> bool {
    &&& step.path.len() <= environment.max_intermediates
    &&& indices_usable_from(pool, step.path, 0)
    &&& indices_distinct_from(step.path, 0)
    &&& match step.issuer {
        Issuer::Anchor(a) => a < anchors.len()
            && anchors[a as int].subject_der == sought_issuer(pool, leaf, step.path),
        Issuer::Pool(j) => j < pool.len() && step.path.len() < environment.max_intermediates
            && index_absent_from(step.path, j, 0)
            && match pool[j as int] {
                Some(c) => c.tbs.subject_der == sought_issuer(pool, leaf, step.path),
                None => false,
            },
    }
}

/// `step` is not among `order[from..]`.
pub open spec fn step_absent_from(order: Seq<IssuerStep>, step: IssuerStep, from: int) -> bool
    decreases order.len() - from
{
    if from < 0 || from >= order.len() { true }
    else { order[from] != step && step_absent_from(order, step, from + 1) }
}

/// `order` is a sequence of distinct name-chained steps, for `order[from..]`.
pub open spec fn search_order_well_formed_from(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    order: Seq<IssuerStep>, from: int,
) -> bool
    decreases order.len() - from
{
    if from < 0 || from >= order.len() { true }
    else {
        &&& step_name_chained(environment, anchors, pool, leaf, order[from])
        &&& step_absent_from(order, order[from], from + 1)
        &&& search_order_well_formed_from(environment, anchors, pool, leaf, order, from + 1)
    }
}

/// The candidate an anchor step completes; a pool step completes none.
pub open spec fn step_candidate(step: IssuerStep) -> Option<Candidate> {
    match step.issuer {
        Issuer::Anchor(a) => Some(Candidate { anchor: a, path: step.path }),
        Issuer::Pool(_) => None,
    }
}

/// No step of `order[from..to]` completes a valid candidate.
pub open spec fn no_valid_step_between(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    order: Seq<IssuerStep>, from: int, to: int,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> bool
    decreases to - from
{
    if from < 0 || from >= to || from >= order.len() { true }
    else {
        &&& match step_candidate(order[from]) {
            Some(candidate) => !candidate_valid(environment, anchors, pool, leaf, candidate, reference, now),
            None => true,
        }
        &&& no_valid_step_between(environment, anchors, pool, leaf, order, from + 1, to, reference, now)
    }
}

/// The budget `budget` runs out on `order`: the search would examine more
/// than `budget` steps, and none of the first `budget` completes a valid
/// candidate ("if (buildForwardCallBudget == 0)" is reached on step
/// `budget` + 1).
pub open spec fn budget_exhausted_at(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    order: Seq<IssuerStep>, budget: nat,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> bool {
    order.len() > budget
        && no_valid_step_between(environment, anchors, pool, leaf, order, 0, budget as int, reference, now)
}

/// The production budget runs out on `order`, for the presented chain.
pub open spec fn budget_exhausted(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    order: Seq<IssuerStep>, reference: crate::spec::ReferenceIdentity, now: u64,
) -> bool {
    match chain_inputs(presented, now) {
        Err(_) => false,
        Ok(inputs) => {
            &&& search_order_well_formed_from(environment, anchors, inputs.pool, inputs.leaf, order, 0)
            &&& budget_exhausted_at(environment, anchors, inputs.pool, inputs.leaf, order, build_budget(), reference, inputs.now)
        },
    }
}

/// The top-level verifier's contract (design §2.6, §3.5), for P9's
/// executable `verify_server_chain`. `order` is the sequence of steps P9's
/// search examines on these inputs (see the header: the budget depends on
/// it, so it is a parameter here and P9's definition fixes it).
/// - `Ok(v)`: the chain's inputs are acceptable, and the candidate
///   `(v.anchor, v.path)` is valid with `v.leaf_spki` its key (soundness);
/// - `Err(BuildBudgetExhausted)`: `order` is well formed and the budget runs
///   out on it;
/// - any other `Err`: no candidate is valid (completeness, within the depth).
pub open spec fn verify_server_chain_ensures(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64, order: Seq<IssuerStep>,
    out: Result<Validated, super::spec::PathError>,
) -> bool {
    match out {
        Ok(v) => match chain_inputs(presented, now) {
            Err(_) => false,
            Ok(inputs) => candidate_verdict(environment, anchors, inputs.pool, inputs.leaf,
                Candidate { anchor: v.anchor, path: v.path }, reference, inputs.now) == Ok::<Seq<u8>, super::spec::PathError>(v.leaf_spki),
        },
        Err(super::spec::PathError::BuildBudgetExhausted) =>
            budget_exhausted(environment, anchors, presented, order, reference, now),
        Err(_) => !some_candidate_valid(environment, anchors, presented, reference, now),
    }
}

} // verus!
