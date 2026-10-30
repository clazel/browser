//! Concrete authentication mutation witnesses. The input-sensitive primitive
//! functions and validator are protocol fixtures, not production cryptography/X.509.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// First octet, with a total empty-input case for the fixture functions.
pub open spec fn first(s: Seq<u8>) -> u8 { if s.len() == 0 { 0 } else { s[0] } }
/// Input-sensitive, SHA-256-sized fixture outputs; no cryptographic claim.
pub open spec fn crypto() -> crate::schedule::spec::Crypto {
    crate::schedule::spec::Crypto {
        hash: |m: Seq<u8>| Seq::new(32, |i: int| (m.len() % 251) as u8),
        extract: |salt: Seq<u8>, ikm: Seq<u8>| Seq::new(32, |i: int| first(salt) ^ first(ikm)),
        expand: |secret: Seq<u8>, info: Seq<u8>, n: nat| Seq::new(n, |i: int|
            first(secret) ^ (if info.len() > 9 { info[9] } else { 0u8 })),
        hmac: |key: Seq<u8>, message: Seq<u8>| Seq::new(32, |i: int| first(key) ^ first(message)),
    }
}
/// One structurally valid, nonempty TLS Certificate; the DER is opaque to this fixture.
pub open spec fn certificate() -> Seq<u8> { seq![0u8, 0u8, 0u8, 6u8, 0u8, 0u8, 1u8, 170u8, 0u8, 0u8] }
/// certificate() whose entry carries status_request (a CertificateStatus with
/// a one-octet OCSP response), which initial() never offered.
pub open spec fn certificate_with_status_request() -> Seq<u8> {
    seq![0u8, 0u8, 0u8, 15u8, 0u8, 0u8, 1u8, 170u8, 0u8, 9u8,
        0u8, 5u8, 0u8, 5u8, 1u8, 0u8, 0u8, 1u8, 48u8]
}
/// Server CertificateVerify body with scheme ECDSA-P256-SHA256 and a fixture signature.
pub open spec fn cv() -> Seq<u8> { seq![4u8, 3u8, 0u8, 1u8, 9u8] }
/// Chain/name/time and server CertificateVerify fixture checks.
pub open spec fn verifier() -> Verification {
    Verification {
        chain: |host: crate::host::spec::Host, now: u64, body: Seq<u8>|
            if host == crate::host::spec::Host::Dns(seq![104u8]) && now == 7 && body == certificate() { Ok(seq![17u8]) }
            else { Err(CertificateError::BadCertificate) },
        signature: |key: Seq<u8>, scheme: u16, input: Seq<u8>, signature: Seq<u8>|
            key == seq![17u8] && scheme == 0x0403 && signature == seq![9u8]
                && input == crate::transcript::spec::certificate_verify_input(true, Seq::new(32, |i: int| 30u8)),
    }
}
/// Constructor context: an abstract negotiated CH/SH prefix and actual offers.
pub open spec fn initial() -> State {
    State {
        config: Config { host: crate::host::spec::Host::Dns(seq![104u8]), now: 7,
            server_secret: Seq::new(32, |i: int| 49u8), client_secret: Seq::new(32, |i: int| 66u8),
            signatures: seq![0x0403u16], extensions: seq![0u16, 10u16, 13u16, 43u16, 51u16] },
        transcript: crate::transcript::spec::State { messages: seq![1u8, 0u8, 0u8, 1u8, 1u8, 2u8, 0u8, 0u8, 1u8, 2u8],
            phase: crate::transcript::spec::Phase::Handshake, retried: false },
        phase: Phase::EncryptedExtensions, key: Seq::empty(), requested: false,
        chain_checked: false, signature_checked: false, finished_checked: false,
        client_sent: false, application_hash: Seq::empty(),
    }
}
/// State after the server's empty EncryptedExtensions.
pub open spec fn after_extensions() -> State { receive(crypto(), verifier(), initial(), 8, seq![0u8, 0u8]).0 }
/// State after the fixture certificate was validated for the target host/time.
pub open spec fn after_certificate() -> State { receive(crypto(), verifier(), after_extensions(), 11, certificate()).0 }
/// State after the server CertificateVerify was checked over the proper prefix.
pub open spec fn after_signature() -> State { receive(crypto(), verifier(), after_certificate(), 15, cv()).0 }
/// Valid server Finished and the resulting client flight.
pub open spec fn accepted() -> (State, Action) {
    receive(crypto(), verifier(), after_signature(), 20, Seq::new(32, |i: int| 112u8))
}
/// A chain validator rejecting the peer's chain with its precise expiry alert.
pub open spec fn rejected_chain() -> Action {
    let v = Verification { chain: |host: crate::host::spec::Host, now: u64, body: Seq<u8>| Err(CertificateError::Expired),
        signature: |key: Seq<u8>, scheme: u16, input: Seq<u8>, signature: Seq<u8>| true };
    receive(crypto(), v, after_extensions(), 11, certificate()).1
}
/// A signature verifier rejecting the peer signature.
pub open spec fn rejected_signature() -> Action {
    let v = Verification { chain: verifier().chain,
        signature: |key: Seq<u8>, scheme: u16, input: Seq<u8>, signature: Seq<u8>| false };
    receive(crypto(), v, after_certificate(), 15, cv()).1
}

/// A host outside host_ok (an empty name) refuses the start (internal_error).
pub proof fn lemma_start_refuses_bad_host()
    ensures start(Config { host: crate::host::spec::Host::Dns(seq![]), ..initial().config }, initial().transcript) is Err,
{
    assert(start(Config { host: crate::host::spec::Host::Dns(seq![]), ..initial().config }, initial().transcript) is Err) by (compute_only);
}

/// Concrete authentication requirement: early_data.
pub proof fn lemma_early_data()
    ensures step(crypto(), verifier(), initial(), Input::Application(seq![1u8])).1 == Action::Fail(10u8),
{
    assert(step(crypto(), verifier(), initial(), Input::Application(seq![1u8])).1 == Action::Fail(10u8)) by (compute_only);
}

/// Concrete authentication requirement: early_ack.
pub proof fn lemma_early_ack()
    ensures step(crypto(), verifier(), initial(), Input::SentFinished).1 == Action::Fail(80u8),
{
    assert(step(crypto(), verifier(), initial(), Input::SentFinished).1 == Action::Fail(80u8)) by (compute_only);
}

/// Concrete authentication requirement: bad_chain.
pub proof fn lemma_bad_chain()
    ensures rejected_chain() == Action::Fail(45u8),
{
    assert(rejected_chain() == Action::Fail(45u8)) by (compute_only);
}

/// Concrete authentication requirement: bad_signature.
pub proof fn lemma_bad_signature()
    ensures rejected_signature() == Action::Fail(51u8),
{
    assert(rejected_signature() == Action::Fail(51u8)) by (compute_only);
}

/// Concrete authentication requirement: bad_finished.
pub proof fn lemma_bad_finished()
    ensures receive(crypto(), verifier(), after_signature(), 20, Seq::new(32, |i: int| 0u8)).1 == Action::Fail(51u8),
{
    assert(receive(crypto(), verifier(), after_signature(), 20, Seq::new(32, |i: int| 0u8)).1 == Action::Fail(51u8)) by (compute_only);
}

/// Concrete authentication requirement: client_flight.
pub proof fn lemma_client_flight()
    ensures accepted().1 == Action::Send(seq![20u8, 0u8, 0u8, 32u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8]),
{
    assert(accepted().1 == Action::Send(seq![20u8, 0u8, 0u8, 32u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8, 111u8])) by (compute_only);
}

/// Concrete authentication requirement: send_phase.
pub proof fn lemma_send_phase()
    ensures accepted().0.phase == Phase::SendFinished,
{
    assert(accepted().0.phase == Phase::SendFinished) by (compute_only);
}

/// Concrete authentication requirement: checkpoint.
pub proof fn lemma_checkpoint()
    ensures accepted().0.application_hash == Seq::new(32, |i: int| 75u8),
{
    assert(accepted().0.application_hash == Seq::new(32, |i: int| 75u8)) by (compute_only);
}

/// Concrete authentication requirement: no_ack.
pub proof fn lemma_no_ack()
    ensures step(crypto(), verifier(), accepted().0, Input::Application(seq![1u8])).1 == Action::Fail(10u8),
{
    assert(step(crypto(), verifier(), accepted().0, Input::Application(seq![1u8])).1 == Action::Fail(10u8)) by (compute_only);
}

/// Concrete authentication requirement: unoffered_signature.
pub proof fn lemma_unoffered_signature()
    ensures receive(crypto(), verifier(), after_certificate(), 15, seq![8u8, 7u8, 0u8, 1u8, 9u8]).1 == Action::Fail(47u8),
{
    assert(receive(crypto(), verifier(), after_certificate(), 15, seq![8u8, 7u8, 0u8, 1u8, 9u8]).1 == Action::Fail(47u8)) by (compute_only);
}

/// Concrete authentication requirement: failed_absorbs.
pub proof fn lemma_failed_absorbs()
    ensures step(crypto(), verifier(), State { phase: Phase::Failed, ..initial() }, Input::Application(seq![1u8])).1 == Action::None,
{
    assert(step(crypto(), verifier(), State { phase: Phase::Failed, ..initial() }, Input::Application(seq![1u8])).1 == Action::None) by (compute_only);
}

/// Concrete authentication requirement: closed_absorbs.
pub proof fn lemma_closed_absorbs()
    ensures step(crypto(), verifier(), State { phase: Phase::Closed, ..initial() }, Input::Application(seq![1u8])).1 == Action::None,
{
    assert(step(crypto(), verifier(), State { phase: Phase::Closed, ..initial() }, Input::Application(seq![1u8])).1 == Action::None) by (compute_only);
}


/// RFC 8446 §4.4.2: an unoffered Certificate entry extension is refused.
pub proof fn lemma_unoffered_certificate_extension()
    ensures receive(crypto(), verifier(), after_extensions(), 11, certificate_with_status_request()).1 == Action::Fail(110u8),
{
    assert(receive(crypto(), verifier(), after_extensions(), 11, certificate_with_status_request()).1 == Action::Fail(110u8)) by (compute_only);
}

} // verus!
