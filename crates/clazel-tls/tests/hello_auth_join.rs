//! Tests for the explicit Hello-to-key-agreement-to-authentication handoff.
//!
//! The provider below is deterministic and input-sensitive, but is only a
//! protocol test double. It is neither X25519, real HKDF/HMAC, nor X.509 or
//! signature verification.

use std::cell::RefCell;

use clazel_tls::auth::exec::{Action, Auth, Input};
use clazel_tls::auth::spec::{CertificateError, Phase as AuthPhase};
use clazel_tls::auth::verify::Verifier;
use clazel_tls::encode;
use clazel_tls::hello::client::{Config, Established, Hello, Outcome};
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::schedule::exec::finished;
use clazel_tls::spec::{DECRYPT_ERROR, ILLEGAL_PARAMETER, INTERNAL_ERROR};
use clazel_tls::transcript::exec::certificate_verify_input;
use clazel_tls::types::{Certificate, CertificateEntry, CertificateVerify, Extension};
use sha2::{Digest, Sha256};

const HOST: &[u8] = b"join.example.test";
const PRIVATE: [u8; 32] = [0x41; 32];
const PUBLIC: [u8; 32] = [0x52; 32];
const PEER: [u8; 32] = [0x63; 32];
const SHARED: [u8; 32] = [0x74; 32];
const ZERO: [u8; 32] = [0; 32];
const LEAF_KEY: &[u8] = b"mock certificate key";
const SIGNATURE: &[u8] = b"mock signature";

/// Deterministic non-cryptographic protocol test double, not real HKDF/HMAC.
struct TestCrypto;

impl Crypto for TestCrypto {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let mut input = b"join extract".to_vec();
        input.extend_from_slice(salt);
        input.extend_from_slice(ikm);
        Sha256::digest(input).to_vec()
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut input = b"join expand".to_vec();
        input.extend_from_slice(secret);
        input.extend_from_slice(info);
        let block = Sha256::digest(input);
        let mut output = Vec::with_capacity(usize::from(length));
        while output.len() < usize::from(length) {
            output.extend_from_slice(&block);
        }
        output.truncate(usize::from(length));
        output
    }

    fn hmac(&self, key: &[u8], message: &[u8]) -> Vec<u8> {
        let mut input = b"join hmac".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(message);
        Sha256::digest(input).to_vec()
    }
}

#[derive(Default)]
struct Calls {
    public: Vec<Vec<u8>>,
    shared: Vec<(Vec<u8>, Vec<u8>)>,
}

/// Deterministic key-exchange stub records exact inputs and returns configured outputs.
struct MockExchange {
    public_output: Vec<u8>,
    shared_output: Option<Vec<u8>>,
    calls: RefCell<Calls>,
}

impl MockExchange {
    fn accepting(shared_output: Option<Vec<u8>>) -> Self {
        Self {
            public_output: PUBLIC.to_vec(),
            shared_output,
            calls: RefCell::new(Calls::default()),
        }
    }
}

impl KeyExchange for MockExchange {
    fn public_key(&self, private_key: &[u8]) -> Vec<u8> {
        self.calls.borrow_mut().public.push(private_key.to_vec());
        self.public_output.clone()
    }

    fn shared_secret(&self, private_key: &[u8], peer_key: &[u8]) -> Option<Vec<u8>> {
        self.calls
            .borrow_mut()
            .shared
            .push((private_key.to_vec(), peer_key.to_vec()));
        self.shared_output.clone()
    }
}

#[derive(Default)]
struct VerificationCalls {
    chain: Vec<(Vec<u8>, u64, Vec<u8>)>,
    signature: Vec<SignatureCall>,
}

type SignatureCall = (Vec<u8>, u16, Vec<u8>, Vec<u8>);

struct MockVerifier {
    signature_valid: bool,
    calls: RefCell<VerificationCalls>,
}

impl MockVerifier {
    fn accepting() -> Self {
        Self {
            signature_valid: true,
            calls: RefCell::new(VerificationCalls::default()),
        }
    }
}

impl Verifier for MockVerifier {
    fn chain(
        &self,
        host: &[u8],
        now: u64,
        certificate_body: &[u8],
    ) -> Result<Vec<u8>, CertificateError> {
        self.calls
            .borrow_mut()
            .chain
            .push((host.to_vec(), now, certificate_body.to_vec()));
        Ok(LEAF_KEY.to_vec())
    }

    fn signature(&self, key: &[u8], scheme: u16, input: &[u8], signature: &[u8]) -> bool {
        self.calls.borrow_mut().signature.push((
            key.to_vec(),
            scheme,
            input.to_vec(),
            signature.to_vec(),
        ));
        self.signature_valid
    }

    fn finished_equal(&self, received: &[u8], expected: &[u8]) -> bool {
        received == expected
    }
}

fn config() -> Config {
    Config {
        host: HOST.to_vec(),
        now: 1_800_000_000,
        random: vec![0x11; 32],
        session_id: Vec::new(),
        public_key: PUBLIC.to_vec(),
        send_sni: true,
    }
}

fn server_hello() -> Vec<u8> {
    server_hello_with_peer(&PEER)
}

fn server_hello_with_peer(peer: &[u8; 32]) -> Vec<u8> {
    let version = [3, 4];
    let mut key_data = vec![0, 29, 0, 32];
    key_data.extend_from_slice(peer);
    let mut extensions = Vec::new();
    extensions.extend_from_slice(&43u16.to_be_bytes());
    extensions.extend_from_slice(
        &u16::try_from(version.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    extensions.extend_from_slice(&version);
    extensions.extend_from_slice(&51u16.to_be_bytes());
    extensions.extend_from_slice(
        &u16::try_from(key_data.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    extensions.extend_from_slice(&key_data);
    let mut body = vec![3, 3];
    body.extend_from_slice(&[0x33; 32]);
    body.push(0); // echoed legacy_session_id
    body.extend_from_slice(&0x1303u16.to_be_bytes());
    body.push(0); // legacy_compression_method
    body.extend_from_slice(
        &u16::try_from(extensions.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    body.extend_from_slice(&extensions);
    body
}

fn established(crypto: &TestCrypto) -> Result<Established, String> {
    let (hello, _) = Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    match hello
        .receive(crypto, &server_hello())
        .map_err(|alert| format!("ServerHello alert {alert}"))?
    {
        Outcome::Established(value) => Ok(value),
        Outcome::Retry(_, _) => Err("unexpected retry in fixture".to_owned()),
    }
}

fn expand_label(crypto: &TestCrypto, secret: &[u8], label: &[u8], context: &[u8]) -> Vec<u8> {
    let full_label_len = 6usize.saturating_add(label.len());
    let mut info = Vec::new();
    info.extend_from_slice(&32u16.to_be_bytes());
    info.push(u8::try_from(full_label_len).unwrap_or(u8::MAX));
    info.extend_from_slice(b"tls13 ");
    info.extend_from_slice(label);
    info.push(u8::try_from(context.len()).unwrap_or(u8::MAX));
    info.extend_from_slice(context);
    crypto.expand(secret, &info, 32)
}

fn expected_master(crypto: &TestCrypto, shared: &[u8]) -> Vec<u8> {
    let zeros = [0; 32];
    let early = crypto.extract(&zeros, &zeros);
    let empty_hash = crypto.hash(&[]);
    let derived_early = expand_label(crypto, &early, b"derived", &empty_hash);
    let handshake = crypto.extract(&derived_early, shared);
    let derived_handshake = expand_label(crypto, &handshake, b"derived", &empty_hash);
    crypto.extract(&derived_handshake, &zeros)
}

fn derive_secret(crypto: &TestCrypto, secret: &[u8], label: &[u8], messages: &[u8]) -> Vec<u8> {
    let context = crypto.hash(messages);
    expand_label(crypto, secret, label, &context)
}

fn expected_handshake_traffic(
    crypto: &TestCrypto,
    shared: &[u8],
    transcript_messages: &[u8],
) -> (Vec<u8>, Vec<u8>) {
    let zeros = [0; 32];
    let early = crypto.extract(&zeros, &zeros);
    let derived_early = expand_label(crypto, &early, b"derived", &crypto.hash(&[]));
    let handshake = crypto.extract(&derived_early, shared);
    (
        derive_secret(crypto, &handshake, b"s hs traffic", transcript_messages),
        derive_secret(crypto, &handshake, b"c hs traffic", transcript_messages),
    )
}

fn certificate_body() -> Vec<u8> {
    let certificate = Certificate {
        context: &[],
        entries: vec![CertificateEntry {
            cert_data: b"opaque test certificate",
            extensions: Vec::new(),
        }],
    };
    let mut body = Vec::new();
    encode::write_certificate(&mut body, &certificate);
    body
}

fn cv_body() -> Vec<u8> {
    let verify = CertificateVerify {
        algorithm: 0x0804,
        signature: SIGNATURE,
    };
    let mut body = Vec::new();
    encode::write_certificate_verify(&mut body, &verify);
    body
}

fn handshake_message(kind: u8, body: &[u8]) -> Vec<u8> {
    let mut message = Vec::new();
    encode::write_handshake(&mut message, kind, body);
    message
}

fn encrypted_extensions_body() -> Vec<u8> {
    let mut body = Vec::new();
    encode::write_encrypted_extensions(&mut body, &[] as &[Extension<'_>]);
    body
}

fn progress_to_certificate_verify(
    auth: &mut Auth,
    crypto: &TestCrypto,
    verifier: &MockVerifier,
) -> Result<(Vec<u8>, Vec<u8>), String> {
    let ee = encrypted_extensions_body();
    assert_eq!(
        auth.step(crypto, verifier, Input::Handshake(8, &ee)),
        Action::None
    );
    let certificate = certificate_body();
    assert_eq!(
        auth.step(crypto, verifier, Input::Handshake(11, &certificate)),
        Action::None
    );
    let prefix = auth.messages().to_vec();
    let expected_cv_input = certificate_verify_input(true, &crypto.hash(&prefix));
    let cv = cv_body();
    assert_eq!(
        auth.step(crypto, verifier, Input::Handshake(15, &cv)),
        Action::None
    );
    assert_eq!(
        verifier.calls.borrow().chain,
        vec![(HOST.to_vec(), 1_800_000_000, certificate.clone())]
    );
    assert_eq!(
        verifier.calls.borrow().signature,
        vec![(
            LEAF_KEY.to_vec(),
            0x0804,
            expected_cv_input,
            SIGNATURE.to_vec()
        )]
    );
    Ok((certificate, cv))
}

#[test]
fn rejects_wrong_private_key_length_before_provider_calls() -> Result<(), String> {
    let crypto = TestCrypto;
    let exchange = MockExchange::accepting(Some(SHARED.to_vec()));
    let result = established(&crypto)?.into_auth(&crypto, &exchange, &[0x41; 31]);
    assert!(matches!(result, Err(INTERNAL_ERROR)));
    let calls = exchange.calls.borrow();
    assert!(calls.public.is_empty());
    assert!(calls.shared.is_empty());
    Ok(())
}

#[test]
fn rejects_private_key_not_bound_to_client_share_before_agreement() -> Result<(), String> {
    let crypto = TestCrypto;
    let exchange = MockExchange {
        public_output: vec![0x99; 32],
        shared_output: Some(SHARED.to_vec()),
        calls: RefCell::new(Calls::default()),
    };
    let result = established(&crypto)?.into_auth(&crypto, &exchange, &PRIVATE);
    assert!(matches!(result, Err(INTERNAL_ERROR)));
    let calls = exchange.calls.borrow();
    assert_eq!(calls.public, vec![PRIVATE.to_vec()]);
    assert!(calls.shared.is_empty());
    Ok(())
}

#[test]
fn rejects_provider_failure_and_all_zero_derived_secret() -> Result<(), String> {
    let crypto = TestCrypto;
    let rejected = MockExchange::accepting(None);
    assert!(matches!(
        established(&crypto)?.into_auth(&crypto, &rejected, &PRIVATE),
        Err(ILLEGAL_PARAMETER)
    ));
    assert_eq!(
        rejected.calls.borrow().shared,
        vec![(PRIVATE.to_vec(), PEER.to_vec())]
    );

    let zero_secret = MockExchange::accepting(Some(ZERO.to_vec()));
    assert!(matches!(
        established(&crypto)?.into_auth(&crypto, &zero_secret, &PRIVATE),
        Err(ILLEGAL_PARAMETER)
    ));
    assert_eq!(
        zero_secret.calls.borrow().shared,
        vec![(PRIVATE.to_vec(), PEER.to_vec())]
    );
    Ok(())
}

#[test]
fn accepts_zero_raw_peer_when_provider_returns_nonzero_shared_secret() -> Result<(), String> {
    let crypto = TestCrypto;
    let body = server_hello_with_peer(&ZERO);
    let (hello, _) = Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let established = match hello
        .receive(&crypto, &body)
        .map_err(|alert| format!("zero raw peer rejected before provider: {alert}"))?
    {
        Outcome::Established(value) => value,
        Outcome::Retry(_, _) => return Err("unexpected retry in fixture".to_owned()),
    };
    let exchange = MockExchange::accepting(Some(SHARED.to_vec()));
    let (auth, master) = established
        .into_auth(&crypto, &exchange, &PRIVATE)
        .map_err(|alert| format!("join rejected test provider secret: {alert}"))?;
    assert_eq!(auth.phase(), AuthPhase::EncryptedExtensions);
    assert_eq!(master, expected_master(&crypto, &SHARED));
    assert_eq!(exchange.calls.borrow().public, vec![PRIVATE.to_vec()]);
    assert_eq!(
        exchange.calls.borrow().shared,
        vec![(PRIVATE.to_vec(), ZERO.to_vec())]
    );
    Ok(())
}

#[test]
fn binds_exact_private_and_peer_inputs_and_derives_secrets_from_peer_result() -> Result<(), String>
{
    let crypto = TestCrypto;
    let exchange = MockExchange::accepting(Some(SHARED.to_vec()));
    let (auth, master) = established(&crypto)?
        .into_auth(&crypto, &exchange, &PRIVATE)
        .map_err(|alert| format!("join alert {alert}"))?;
    assert_eq!(auth.phase(), AuthPhase::EncryptedExtensions);
    assert_eq!(master, expected_master(&crypto, &SHARED));
    assert_ne!(master, expected_master(&crypto, &PEER));
    let calls = exchange.calls.borrow();
    assert_eq!(calls.public, vec![PRIVATE.to_vec()]);
    assert_eq!(calls.shared, vec![(PRIVATE.to_vec(), PEER.to_vec())]);
    Ok(())
}

struct AuthFlight {
    auth: Auth,
    verifier: MockVerifier,
    transcript: Vec<u8>,
    certificate: Vec<u8>,
    server_secret: Vec<u8>,
    client_secret: Vec<u8>,
}

fn auth_through_cv(crypto: &TestCrypto, exchange: &MockExchange) -> Result<AuthFlight, String> {
    let server_body = server_hello();
    let (hello, client_hello_flight) =
        Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let established = match hello
        .receive(crypto, &server_body)
        .map_err(|alert| format!("ServerHello alert {alert}"))?
    {
        Outcome::Established(value) => value,
        Outcome::Retry(_, _) => return Err("unexpected retry in fixture".to_owned()),
    };
    let mut prefix = client_hello_flight;
    prefix.extend_from_slice(&handshake_message(2, &server_body));
    let (server_secret, client_secret) = expected_handshake_traffic(crypto, &SHARED, &prefix);
    let (mut auth, _) = established
        .into_auth(crypto, exchange, &PRIVATE)
        .map_err(|alert| format!("join alert {alert}"))?;
    assert_eq!(auth.phase(), AuthPhase::EncryptedExtensions);
    let verifier = MockVerifier::accepting();
    let (certificate, cv) = progress_to_certificate_verify(&mut auth, crypto, &verifier)?;
    let through_cv = auth.messages().to_vec();
    let mut expected = prefix;
    expected.extend_from_slice(&handshake_message(8, &encrypted_extensions_body()));
    expected.extend_from_slice(&handshake_message(11, &certificate));
    expected.extend_from_slice(&handshake_message(15, &cv));
    assert_eq!(through_cv, expected);
    Ok(AuthFlight {
        auth,
        verifier,
        transcript: through_cv,
        certificate,
        server_secret,
        client_secret,
    })
}

#[test]
fn joined_secrets_drive_mock_authentication_and_finished_transcript() -> Result<(), String> {
    let crypto = TestCrypto;
    let exchange = MockExchange::accepting(Some(SHARED.to_vec()));

    let failed = auth_through_cv(&crypto, &exchange)?;
    let mut failed_auth = failed.auth;
    let server_finished = finished(&crypto, &failed.server_secret, &failed.transcript);
    let mut wrong_finished = server_finished.clone();
    if let Some(first) = wrong_finished.first_mut() {
        *first ^= 1;
    }
    assert_eq!(
        failed_auth.step(
            &crypto,
            &failed.verifier,
            Input::Handshake(20, &wrong_finished)
        ),
        Action::Fail(DECRYPT_ERROR)
    );
    assert_eq!(failed_auth.phase(), AuthPhase::Failed);

    let success = auth_through_cv(&crypto, &exchange)?;
    let mut auth = success.auth;
    let server_finished = finished(&crypto, &success.server_secret, &success.transcript);
    let mut through_server_finished = success.transcript;
    through_server_finished.extend_from_slice(&handshake_message(20, &server_finished));
    let expected_client_finished =
        finished(&crypto, &success.client_secret, &through_server_finished);
    assert_ne!(
        expected_client_finished,
        finished(&crypto, &success.server_secret, &through_server_finished),
        "test provider must distinguish client and server traffic labels"
    );
    assert_eq!(
        auth.step(
            &crypto,
            &success.verifier,
            Input::Handshake(20, &server_finished)
        ),
        Action::Send(handshake_message(20, &expected_client_finished))
    );
    let mut expected_messages = through_server_finished;
    expected_messages.extend_from_slice(&handshake_message(20, &expected_client_finished));
    assert_eq!(auth.messages(), expected_messages);
    assert_eq!(auth.phase(), AuthPhase::SendFinished);
    assert_eq!(
        success.verifier.calls.borrow().chain,
        vec![(HOST.to_vec(), 1_800_000_000, success.certificate)]
    );
    Ok(())
}
