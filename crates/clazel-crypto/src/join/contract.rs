//! Contracts for the executable join ([`super::exec`]), in terms of
//! [`super::spec`], and the composition theorems (design §3.5, "after the
//! join"), **stated** here and proven in [`super::lemmas`].
//!
//! - `new_ensures`: the verifier's anchors are exactly
//!   `spec::anchors_from_roots` of the rows it was given.
//! - `validate_ensures`: the executable validator returns exactly
//!   `spec::validate`.
//! - `chain_verified`: what an accepted chain means. The body is a
//!   Certificate; P9's `verify_server_chain` accepted its certificates for
//!   the host's reference identity and the clock, choosing the candidate
//!   `(v.anchor, v.path)`, whose verdict is the returned key; that path is
//!   accepted by RFC 5280 §6.1 and the profile under the production
//!   environment, so every P7/P8 path theorem (`all_path_theorems`) holds of
//!   it; and every link on it is one of P11's accepted signature forms
//!   (`chain::lemmas::verified_link`) on the exact TBS octets.
//! - `thm_validate_sound`: every key the join returns is `chain_verified`.
//! - `thm_handshake_chain_verified`: over every finite trace of the
//!   `clazel-tls` authentication machine with the production verification
//!   functions, a state that has checked a chain holds a key that is
//!   `chain_verified` for the state's own host and clock and some
//!   Certificate body. This composes `clazel-tls`'s
//!   `auth::contract::thm_chain_justified_trace` with `thm_validate_sound`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `exec::ChainVerifier::new`: its anchors are the table's.
pub open spec fn new_ensures(roots: Seq<RootEntry>, anchors: Seq<clazel_x509::path::parsed::spec::Anchor>) -> bool {
    anchors == anchors_from_roots(roots)
}

/// `exec::ChainVerifier::validate`: exactly `spec::validate`.
pub open spec fn validate_ensures(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>,
    host: clazel_tls::host::spec::Host, now: u64, body: Seq<u8>,
    out: Result<Seq<u8>, clazel_tls::auth::spec::CertificateError>,
) -> bool {
    out == validate(anchors, host, now, body)
}

/// The candidate a validated chain names.
pub open spec fn chosen(validated: clazel_x509::path::verifier::Validated) -> clazel_x509::path::verifier::Candidate {
    clazel_x509::path::verifier::Candidate { anchor: validated.anchor, path: validated.path }
}

/// Every link of `certs` under `anchor` is one of P11's accepted forms:
/// certificate 1 under the anchor's key, certificate i+1 under certificate i's.
pub open spec fn links_verified(anchor: clazel_x509::path::parsed::spec::Anchor,
    certs: Seq<clazel_x509::path::parsed::spec::PathCert>) -> bool
{
    &&& certs.len() > 0
    &&& crate::chain::lemmas::verified_link(anchor.spki_der, certs[0])
    &&& forall|i: int| 0 < i < certs.len() ==>
        #[trigger] crate::chain::lemmas::verified_link(certs[i - 1].tbs.subject_public_key_info_der, certs[i])
}

/// What it means that `body`'s chain was accepted for `host` at `now`,
/// with `key` the leaf's SubjectPublicKeyInfo (module header).
pub open spec fn chain_verified(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>,
    host: clazel_tls::host::spec::Host, now: u64, body: Seq<u8>, key: Seq<u8>,
) -> bool {
    match clazel_tls::spec::read_certificate(body) {
        None => false,
        Some(certificate) => {
            let presented = presented(certificate.entries);
            let reference = reference_identity(host);
            match (clazel_x509::path::search::spec::verify_server_chain(production_environment(), anchors, presented, reference, now),
                clazel_x509::path::verifier::chain_inputs(presented, now)) {
                (Ok(validated), Ok(inputs)) => {
                    let candidate = chosen(validated);
                    let anchor = anchors[candidate.anchor as int];
                    let certs = clazel_x509::path::verifier::candidate_certificates(inputs.pool, inputs.leaf, candidate);
                    &&& validated.leaf_spki == key
                    // RFC 8446 §4.4.2: the leaf is the sender's certificate.
                    &&& presented.len() > 0
                    &&& clazel_x509::path::parsed::spec::parse_path_cert(presented[0]) == Some(inputs.leaf)
                    &&& certs.last() == inputs.leaf
                    // P9: the search's choice is a valid candidate with this key.
                    &&& candidate.anchor < anchors.len()
                    &&& clazel_x509::path::verifier::candidate_verdict(production_environment(), anchors,
                            inputs.pool, inputs.leaf, candidate, reference, inputs.now)
                        == Ok::<Seq<u8>, clazel_x509::path::spec::PathError>(key)
                    // P7/P8: §6.1 and the profile accept the path, so every path theorem holds of it.
                    &&& clazel_x509::path::theorems::accepts(crate::chain::spec::production_link(), not_revoked(),
                            anchor, certs, reference, inputs.now)
                    &&& clazel_x509::path::theorems::all_path_theorems(crate::chain::spec::production_link(), not_revoked(),
                            anchor, certs, reference, inputs.now)
                    // P11: every link is an accepted signature form on the exact TBS octets.
                    &&& links_verified(anchor, certs)
                },
                _ => false,
            }
        },
    }
}

/// Every key the join returns is `chain_verified`.
pub open spec fn thm_validate_sound(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>,
    host: clazel_tls::host::spec::Host, now: u64, body: Seq<u8>,
) -> bool {
    match validate(anchors, host, now, body) {
        Ok(key) => chain_verified(anchors, host, now, body, key),
        Err(_) => true,
    }
}

/// Over every finite input trace from a well-formed, justified state (a
/// started machine is one, `clazel_tls::auth::lemmas::lemma_start_justified`),
/// with the production verification functions over `anchors`: once a chain
/// is checked, the key the machine verifies CertificateVerify with is
/// `chain_verified` for the machine's own host and clock.
pub open spec fn thm_handshake_chain_verified(c: clazel_tls::schedule::spec::Crypto,
    anchors: Seq<clazel_x509::path::parsed::spec::Anchor>, s: clazel_tls::auth::spec::State,
    inputs: Seq<clazel_tls::auth::spec::Input>,
) -> bool {
    let v = verification(anchors);
    (clazel_tls::auth::spec::wf(s) && clazel_tls::auth::contract::chain_justified(v, s)) ==> {
        let t = clazel_tls::auth::spec::run(c, v, s, inputs);
        t.chain_checked ==> exists|body: Seq<u8>| #[trigger] chain_verified(anchors, t.config.host, t.config.now, body, t.key)
    }
}

} // verus!
