//! Adversarial checks of the transcript accumulator's RFC 8446 Hello ordering.
//! These exercise transcript bookkeeping only; `Phase` is not authentication.

use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::transcript::exec::Transcript;
use clazel_tls::transcript::spec::{Error, Kind, Phase};

struct FixedHash;

impl Crypto for FixedHash {
    fn hash(&self, _messages: &[u8]) -> Vec<u8> {
        vec![0xa5; 32]
    }

    // These operations are required by the shared Crypto interface but are
    // not called by transcript tests; empty outputs are inert test stubs.
    fn extract(&self, _salt: &[u8], _ikm: &[u8]) -> Vec<u8> {
        Vec::new()
    }

    fn expand(&self, _secret: &[u8], _info: &[u8], _length: u16) -> Vec<u8> {
        Vec::new()
    }

    fn hmac(&self, _key: &[u8], _message: &[u8]) -> Vec<u8> {
        Vec::new()
    }
}

fn initial() -> Result<Transcript, String> {
    Transcript::new(&[0x11]).map_err(|error| format!("construction failed: {error:?}"))
}

fn assert_rejected_unchanged(transcript: &mut Transcript, kind: Kind) {
    let before_messages = transcript.messages().to_vec();
    let before_phase = transcript.phase();
    let before_retried = transcript.retried();
    let result = transcript.push(&FixedHash, kind, &[0x22]);
    assert_eq!(result, Err(Error::UnexpectedMessage));
    assert_eq!(transcript.messages(), before_messages);
    assert_eq!(transcript.phase(), before_phase);
    assert_eq!(transcript.retried(), before_retried);
}

#[test]
fn unsolicited_or_duplicated_hello_messages_are_rejected() -> Result<(), String> {
    // RFC 8446 §4.1.4 permits a ClientHello only initially, or as the
    // response to a HelloRetryRequest; §4.4.1 hashes the initial ClientHello.
    let mut transcript = initial()?;
    assert_eq!(transcript.phase(), Phase::FirstServerHello);
    assert_rejected_unchanged(&mut transcript, Kind::ClientHello);

    transcript
        .push(&FixedHash, Kind::ServerHello, &[0x33])
        .map_err(|error| format!("ServerHello rejected: {error:?}"))?;
    assert_eq!(transcript.phase(), Phase::Handshake);
    assert_rejected_unchanged(&mut transcript, Kind::ServerHello);
    Ok(())
}

#[test]
fn retry_exchange_requires_exactly_one_second_client_hello() -> Result<(), String> {
    // RFC 8446 §4.1.4 allows one HelloRetryRequest, followed by the
    // client's second ClientHello and the server's final ServerHello.
    let mut transcript = initial()?;
    transcript
        .push(&FixedHash, Kind::HelloRetryRequest, &[0x33])
        .map_err(|error| format!("HelloRetryRequest rejected: {error:?}"))?;
    assert_eq!(transcript.phase(), Phase::SecondClientHello);
    assert!(transcript.retried());
    transcript
        .push(&FixedHash, Kind::ClientHello, &[0x44])
        .map_err(|error| format!("second ClientHello rejected: {error:?}"))?;
    assert_eq!(transcript.phase(), Phase::SecondServerHello);
    assert_rejected_unchanged(&mut transcript, Kind::ClientHello);
    transcript
        .push(&FixedHash, Kind::ServerHello, &[0x55])
        .map_err(|error| format!("final ServerHello rejected: {error:?}"))?;
    assert_eq!(transcript.phase(), Phase::Handshake);
    assert_rejected_unchanged(&mut transcript, Kind::ClientHello);
    Ok(())
}

#[test]
fn retry_exchange_rejects_skipped_key_exchange_messages_without_state_change() -> Result<(), String>
{
    // RFC 8446 §4.1.4 requires an updated ClientHello after HRR; §4.4.1's
    // transcript rewrite does not permit the server to skip that message.
    let mut transcript = initial()?;
    transcript
        .push(&FixedHash, Kind::HelloRetryRequest, &[0x33])
        .map_err(|error| format!("HelloRetryRequest rejected: {error:?}"))?;
    assert_eq!(transcript.phase(), Phase::SecondClientHello);
    assert_rejected_unchanged(&mut transcript, Kind::ServerHello);

    transcript
        .push(&FixedHash, Kind::ClientHello, &[0x44])
        .map_err(|error| format!("second ClientHello rejected: {error:?}"))?;
    assert_eq!(transcript.phase(), Phase::SecondServerHello);
    for kind in [Kind::Certificate, Kind::CertificateVerify, Kind::Finished] {
        assert_rejected_unchanged(&mut transcript, kind);
    }
    Ok(())
}
