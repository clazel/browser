//! The composition theorems of [`super::contract`], proven: the join's
//! soundness (`lemma_thm_validate_sound`) from P9's
//! `lemma_meets_verifier_contract`, P8's `lemma_candidate_reduces` and
//! `lemma_all_path_theorems`, and P11's `lemma_candidate_links_verify`; and
//! the handshake theorem (`lemma_thm_handshake_chain_verified`) from
//! `clazel-tls`'s `lemma_thm_chain_justified_trace`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`super::contract::thm_validate_sound`] holds for every input.
pub proof fn lemma_thm_validate_sound(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>,
    host: clazel_tls::host::spec::Host, now: u64, body: Seq<u8>)
    ensures super::contract::thm_validate_sound(anchors, host, now, body),
{
    // The definitions below are used only through the lemmas about them.
    hide(clazel_tls::spec::read_certificate);
    hide(clazel_x509::path::parsed::spec::parse_path_cert);
    hide(clazel_x509::time::spec::from_unix_seconds);
    hide(clazel_x509::path::verifier::candidate_verdict);
    hide(clazel_x509::path::spec::process);
    hide(clazel_x509::path::profile::path_profile);
    hide(clazel_x509::path::search::spec::verify_server_chain);
    hide(clazel_x509::path::search::spec::steps_from);
    hide(clazel_x509::path::theorems::all_path_theorems);
    hide(clazel_x509::path::theorems::accepts);
    match clazel_tls::spec::read_certificate(body) {
        None => {},
        Some(certificate) => {
            let environment = production_environment();
            let presented = presented(certificate.entries);
            let reference = reference_identity(host);
            clazel_x509::path::search::lemmas::lemma_meets_verifier_contract(environment, anchors, presented, reference, now);
            match clazel_x509::path::search::spec::verify_server_chain(environment, anchors, presented, reference, now) {
                Err(_) => {},
                Ok(validated) => {
                    let inputs = clazel_x509::path::verifier::chain_inputs(presented, now)->Ok_0;
                    let candidate = super::contract::chosen(validated);
                    assert(clazel_x509::path::verifier::candidate_valid(environment, anchors, inputs.pool, inputs.leaf,
                        candidate, reference, inputs.now));
                    clazel_x509::path::theorems::lemma_candidate_reduces(environment, anchors, inputs.pool, inputs.leaf,
                        candidate, reference, inputs.now);
                    let anchor = anchors[candidate.anchor as int];
                    let certs = clazel_x509::path::verifier::candidate_certificates(inputs.pool, inputs.leaf, candidate);
                    clazel_x509::path::lemmas::lemma_all_path_theorems(crate::chain::spec::production_link(), not_revoked(),
                        anchor, certs, reference, inputs.now);
                    crate::chain::lemmas::lemma_candidate_links_verify(environment, anchors, inputs.pool, inputs.leaf,
                        candidate, reference, inputs.now);
                    assert(certs.len() > 0);
                    assert(super::contract::links_verified(anchor, certs));
                },
            }
        },
    }
}

/// [`super::contract::thm_handshake_chain_verified`] holds for every trace.
pub proof fn lemma_thm_handshake_chain_verified(c: clazel_tls::schedule::spec::Crypto,
    anchors: Seq<clazel_x509::path::parsed::spec::Anchor>, s: clazel_tls::auth::spec::State,
    inputs: Seq<clazel_tls::auth::spec::Input>)
    ensures super::contract::thm_handshake_chain_verified(c, anchors, s, inputs),
{
    let v = verification(anchors);
    clazel_tls::auth::lemmas::lemma_thm_chain_justified_trace(c, v, s, inputs);
    if clazel_tls::auth::spec::wf(s) && clazel_tls::auth::contract::chain_justified(v, s) {
        let t = clazel_tls::auth::spec::run(c, v, s, inputs);
        if t.chain_checked {
            let body = choose|body: Seq<u8>| #[trigger] (v.chain)(t.config.host, t.config.now, body)
                == Ok::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(t.key);
            assert(validate(anchors, t.config.host, t.config.now, body) == Ok::<Seq<u8>, clazel_tls::auth::spec::CertificateError>(t.key));
            lemma_thm_validate_sound(anchors, t.config.host, t.config.now, body);
            assert(super::contract::chain_verified(anchors, t.config.host, t.config.now, body, t.key));
        }
    }
}

} // verus!
