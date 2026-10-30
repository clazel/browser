//! Behavioral tests for the initial TLS authentication gate.
//!
//! The deterministic provider and verifier below are protocol-test doubles,
//! not real cryptography, HKDF/HMAC, or X.509 validation.

use std::cell::RefCell;

use clazel_tls::auth::exec::{Action, Auth, Config, Input};
use clazel_tls::auth::spec::{CertificateError, Phase};
use clazel_tls::auth::verify::Verifier;
use clazel_tls::encode::{
    write_certificate, write_certificate_request, write_certificate_verify,
    write_encrypted_extensions, write_handshake,
};
use clazel_tls::host::exec::Host;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::schedule::exec::finished;
use clazel_tls::spec::{
    DECODE_ERROR, DECRYPT_ERROR, ILLEGAL_PARAMETER, INTERNAL_ERROR, MISSING_EXTENSION,
    UNEXPECTED_MESSAGE, UNSUPPORTED_EXTENSION,
};
use clazel_tls::transcript::exec::Transcript;
use clazel_tls::transcript::spec::Kind;
use clazel_tls::types::{
    Certificate, CertificateEntry, CertificateRequest, CertificateVerify, Extension, HsMsg,
};
use sha2::{Digest, Sha256};

const HOST: &[u8] = b"example.test";
const NOW: u64 = 1_800_000_000;
const SERVER_SECRET: [u8; 32] = [0x31; 32];
const CLIENT_SECRET: [u8; 32] = [0x42; 32];
const LEAF_KEY: &[u8] = b"mock leaf public key";
const SIGNATURE_SCHEME: u16 = 0x0804;
const SIGNATURE: &[u8] = b"mock signature";

/// Input-sensitive deterministic protocol test double, not real
/// cryptography or an HKDF/HMAC implementation.
struct TestCrypto;

impl Crypto for TestCrypto {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let mut input = b"test extract".to_vec();
        input.extend_from_slice(salt);
        input.extend_from_slice(ikm);
        Sha256::digest(input).to_vec()
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut input = b"test expand".to_vec();
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
        let mut input = b"test hmac".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(message);
        Sha256::digest(input).to_vec()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SignatureCall {
    key: Vec<u8>,
    scheme: u16,
    input: Vec<u8>,
    signature: Vec<u8>,
}

#[derive(Default)]
struct Calls {
    chains: Vec<(Host, u64, Vec<u8>)>,
    signatures: Vec<SignatureCall>,
}

struct MockVerifier {
    chain_result: Result<Vec<u8>, CertificateError>,
    signature_valid: bool,
    calls: RefCell<Calls>,
}

impl MockVerifier {
    fn accepts_chain() -> Self {
        Self {
            chain_result: Ok(LEAF_KEY.to_vec()),
            signature_valid: true,
            calls: RefCell::new(Calls::default()),
        }
    }
}

impl Verifier for MockVerifier {
    fn chain(
        &self,
        host: &Host,
        now: u64,
        certificate_body: &[u8],
    ) -> Result<Vec<u8>, CertificateError> {
        self.calls
            .borrow_mut()
            .chains
            .push((host.clone(), now, certificate_body.to_vec()));
        self.chain_result.clone()
    }

    fn signature(&self, key: &[u8], scheme: u16, input: &[u8], signature: &[u8]) -> bool {
        self.calls.borrow_mut().signatures.push(SignatureCall {
            key: key.to_vec(),
            scheme,
            input: input.to_vec(),
            signature: signature.to_vec(),
        });
        self.signature_valid
    }

    fn finished_equal(&self, received: &[u8], expected: &[u8]) -> bool {
        received == expected
    }
}

fn config() -> Config {
    Config {
        host: Host::Dns(HOST.to_vec()),
        now: NOW,
        server_secret: SERVER_SECRET.to_vec(),
        client_secret: CLIENT_SECRET.to_vec(),
        signatures: vec![SIGNATURE_SCHEME],
        extensions: vec![0, 13],
    }
}

fn start(crypto: &TestCrypto) -> Result<Auth, String> {
    let mut transcript =
        Transcript::new(b"client hello").map_err(|error| format!("transcript start: {error:?}"))?;
    transcript
        .push(crypto, Kind::ServerHello, b"server hello")
        .map_err(|error| format!("transcript ServerHello: {error:?}"))?;
    Auth::start(config(), transcript).map_err(|alert| format!("auth start alert {alert}"))
}

fn handshake(typ: u8, body: &[u8]) -> Vec<u8> {
    let mut encoded = Vec::new();
    write_handshake(&mut encoded, typ, body);
    encoded
}

fn hello_transcript() -> Vec<u8> {
    let mut messages = handshake(1, b"client hello");
    messages.extend_from_slice(&handshake(2, b"server hello"));
    messages
}

fn encrypted_extensions(extensions: &[Extension<'_>]) -> Vec<u8> {
    let mut body = Vec::new();
    write_encrypted_extensions(&mut body, extensions);
    body
}

fn certificate_body(context: &[u8], certificate: &[u8]) -> Vec<u8> {
    let value = Certificate {
        context,
        entries: vec![CertificateEntry {
            cert_data: certificate,
            extensions: Vec::new(),
        }],
    };
    let mut body = Vec::new();
    write_certificate(&mut body, &value);
    body
}

fn certificate_request_body(context: &[u8], extensions: &[Extension<'_>]) -> Vec<u8> {
    let value = CertificateRequest {
        context,
        extensions: extensions.to_vec(),
    };
    let mut body = Vec::new();
    write_certificate_request(&mut body, &value);
    body
}

fn certificate_verify_body(scheme: u16, signature: &[u8]) -> Vec<u8> {
    let value = CertificateVerify {
        algorithm: scheme,
        signature,
    };
    let mut body = Vec::new();
    write_certificate_verify(&mut body, &value);
    body
}

fn through_certificate(request: Option<&[u8]>, certificate: &[u8]) -> Vec<u8> {
    let mut messages = hello_transcript();
    messages.extend_from_slice(&handshake(8, &encrypted_extensions(&[])));
    if let Some(request) = request {
        messages.extend_from_slice(&handshake(13, request));
    }
    messages.extend_from_slice(&handshake(11, certificate));
    messages
}

fn through_certificate_verify(request: Option<&[u8]>, certificate: &[u8]) -> Vec<u8> {
    let mut messages = through_certificate(request, certificate);
    let cv = certificate_verify_body(SIGNATURE_SCHEME, SIGNATURE);
    messages.extend_from_slice(&handshake(15, &cv));
    messages
}

fn receive(
    auth: &mut Auth,
    crypto: &TestCrypto,
    verifier: &MockVerifier,
    typ: u8,
    body: &[u8],
) -> Action {
    auth.step(crypto, verifier, Input::Handshake(typ, body))
}

fn progress_to_certificate(
    auth: &mut Auth,
    crypto: &TestCrypto,
    verifier: &MockVerifier,
    request: Option<&[u8]>,
) -> Result<(), String> {
    assert_eq!(
        receive(auth, crypto, verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    if let Some(body) = request {
        assert_eq!(receive(auth, crypto, verifier, 13, body), Action::None);
    }
    Ok(())
}

fn progress_to_finished(
    auth: &mut Auth,
    crypto: &TestCrypto,
    verifier: &MockVerifier,
    request: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    progress_to_certificate(auth, crypto, verifier, request)?;
    let cert = certificate_body(&[], b"opaque certificate bytes");
    assert_eq!(receive(auth, crypto, verifier, 11, &cert), Action::None);
    let mut expected_prefix = through_certificate(request, &cert);
    assert_eq!(auth.messages(), expected_prefix);
    let signature_input = clazel_tls::transcript::exec::certificate_verify_input(
        true,
        &crypto.hash(&expected_prefix),
    );
    let cv = certificate_verify_body(SIGNATURE_SCHEME, SIGNATURE);
    assert_eq!(receive(auth, crypto, verifier, 15, &cv), Action::None);
    expected_prefix.extend_from_slice(&handshake(15, &cv));
    assert_eq!(auth.messages(), expected_prefix);
    assert_eq!(
        verifier.calls.borrow().signatures.last(),
        Some(&SignatureCall {
            key: LEAF_KEY.to_vec(),
            scheme: SIGNATURE_SCHEME,
            input: signature_input,
            signature: SIGNATURE.to_vec(),
        })
    );
    Ok(cert)
}

fn request_body(context: &[u8]) -> Vec<u8> {
    certificate_request_body(
        context,
        &[Extension {
            etype: 13,
            data: &[0x00, 0x02, 0x08, 0x04],
        }],
    )
}

fn complete_server_authentication(
    auth: &mut Auth,
    crypto: &TestCrypto,
    verifier: &MockVerifier,
    request: Option<&[u8]>,
) -> Result<(Vec<u8>, Vec<u8>), String> {
    let certificate = progress_to_finished(auth, crypto, verifier, request)?;
    let before_server_finished = through_certificate_verify(request, &certificate);
    assert_eq!(auth.messages(), before_server_finished);
    let received = finished(crypto, &SERVER_SECRET, &before_server_finished);
    assert_ne!(
        received,
        finished(crypto, &CLIENT_SECRET, &before_server_finished),
        "provider fixture must distinguish server and client secrets"
    );
    let truncated_prefix = before_server_finished
        .get(4..)
        .ok_or("expected nonempty Hello transcript")?;
    assert_ne!(
        received,
        finished(crypto, &SERVER_SECRET, truncated_prefix),
        "provider fixture must distinguish transcript prefixes"
    );
    let mut server_transcript = before_server_finished;
    server_transcript.extend_from_slice(&handshake(20, &received));
    let app_hash = crypto.hash(&server_transcript);
    let mut client_finished_prefix = server_transcript.clone();
    if request.is_some() {
        client_finished_prefix.extend_from_slice(&handshake(11, &[0, 0, 0, 0]));
    }
    let own_finished = finished(crypto, &CLIENT_SECRET, &client_finished_prefix);
    assert_ne!(
        own_finished,
        finished(crypto, &SERVER_SECRET, &client_finished_prefix),
        "provider fixture must distinguish client and server secrets"
    );
    let mut expected_flight = Vec::new();
    if request.is_some() {
        expected_flight.extend_from_slice(&handshake(11, &[0, 0, 0, 0]));
    }
    expected_flight.extend_from_slice(&handshake(20, &own_finished));
    assert_eq!(
        receive(auth, crypto, verifier, 20, &received),
        Action::Send(expected_flight.clone())
    );
    assert_eq!(auth.phase(), Phase::SendFinished);
    assert_eq!(auth.application_hash(), app_hash);
    let mut expected_messages = server_transcript;
    expected_messages.extend_from_slice(&expected_flight);
    assert_eq!(auth.messages(), expected_messages);
    Ok((certificate, expected_flight))
}

#[test]
fn no_client_certificate_path_gates_application_until_send_ack() -> Result<(), String> {
    let crypto = TestCrypto;
    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    let (certificate, flight) =
        complete_server_authentication(&mut auth, &crypto, &verifier, None)?;
    assert_eq!(flight.get(..4), Some(&[20, 0, 0, 32][..]));
    let calls = verifier.calls.borrow();
    assert_eq!(
        calls.chains,
        vec![(Host::Dns(HOST.to_vec()), NOW, certificate)]
    );
    assert_eq!(calls.signatures.len(), 1);
    drop(calls);

    assert_eq!(
        auth.step(&crypto, &verifier, Input::Application(b"before ack")),
        Action::Fail(UNEXPECTED_MESSAGE)
    );
    assert_eq!(auth.phase(), Phase::Failed);
    assert_eq!(
        auth.step(&crypto, &verifier, Input::SentFinished),
        Action::None
    );
    assert_eq!(
        auth.step(&crypto, &verifier, Input::Application(b"after failure")),
        Action::None
    );

    let mut auth = start(&crypto)?;
    let (_, expected_flight) = complete_server_authentication(&mut auth, &crypto, &verifier, None)?;
    assert_eq!(
        auth.step(&crypto, &verifier, Input::SentFinished),
        Action::Ready
    );
    assert_eq!(auth.phase(), Phase::Ready);
    assert_eq!(
        auth.step(&crypto, &verifier, Input::Application(b"payload")),
        Action::Deliver(b"payload".to_vec())
    );
    assert_eq!(auth.messages().last(), expected_flight.last());
    Ok(())
}

#[test]
fn requested_empty_client_certificate_is_sent_before_client_finished() -> Result<(), String> {
    let crypto = TestCrypto;
    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    let request = request_body(&[]);
    let (_, flight) =
        complete_server_authentication(&mut auth, &crypto, &verifier, Some(&request))?;
    assert_eq!(flight.get(..8), Some(&[11, 0, 0, 4, 0, 0, 0, 0][..]));
    assert_eq!(flight.get(8..12), Some(&[20, 0, 0, 32][..]));
    assert_eq!(
        auth.step(&crypto, &verifier, Input::SentFinished),
        Action::Ready
    );
    Ok(())
}

#[test]
fn typed_chain_failures_and_empty_chain_preserve_expected_alerts() -> Result<(), String> {
    let crypto = TestCrypto;
    for (error, alert) in [
        (CertificateError::BadCertificate, 42),
        (CertificateError::UnknownCa, 48),
        (CertificateError::Expired, 45),
        (CertificateError::Unsupported, 43),
    ] {
        let verifier = MockVerifier {
            chain_result: Err(error),
            signature_valid: true,
            calls: RefCell::new(Calls::default()),
        };
        let mut auth = start(&crypto)?;
        assert_eq!(
            receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
            Action::None
        );
        let cert = certificate_body(&[], b"opaque certificate bytes");
        let before = auth.messages().to_vec();
        assert_eq!(
            receive(&mut auth, &crypto, &verifier, 11, &cert),
            Action::Fail(alert)
        );
        assert_eq!(auth.messages(), before);
        assert_eq!(auth.phase(), Phase::Failed);
        assert_eq!(
            auth.step(&crypto, &verifier, Input::Application(b"after failure")),
            Action::None
        );
        assert_eq!(
            verifier.calls.borrow().chains,
            vec![(Host::Dns(HOST.to_vec()), NOW, cert)]
        );
    }

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    let empty = certificate_body(&[], &[]);
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 11, &empty),
        Action::Fail(DECODE_ERROR)
    );
    assert!(verifier.calls.borrow().chains.is_empty());
    Ok(())
}

#[test]
fn unoffered_certificate_entry_extensions_are_refused_before_chain_validation() -> Result<(), String>
{
    // RFC 8446 §4.4.2: Certificate entry extensions must answer ClientHello
    // offers; config() offers server_name and signature_algorithms only.
    let crypto = TestCrypto;
    let status_request: &[u8] = &[1, 0, 0, 1, 0x30];
    let sct_list: &[u8] = &[0, 3, 0, 1, 0x30];
    let unknown: &[u8] = b"opaque";
    for (etype, data, on_leaf) in [
        (5, status_request, true),
        (18, sct_list, true),
        (0x9999, unknown, true),
        (5, status_request, false),
    ] {
        let verifier = MockVerifier::accepts_chain();
        let mut auth = start(&crypto)?;
        progress_to_certificate(&mut auth, &crypto, &verifier, None)?;
        let with_extension = CertificateEntry {
            cert_data: b"opaque certificate bytes",
            extensions: vec![Extension { etype, data }],
        };
        let plain = CertificateEntry {
            cert_data: b"opaque intermediate bytes",
            extensions: Vec::new(),
        };
        let entries = if on_leaf {
            vec![with_extension, plain]
        } else {
            vec![plain, with_extension]
        };
        let mut cert = Vec::new();
        write_certificate(
            &mut cert,
            &Certificate {
                context: &[],
                entries,
            },
        );
        let before = auth.messages().to_vec();
        assert_eq!(
            receive(&mut auth, &crypto, &verifier, 11, &cert),
            Action::Fail(UNSUPPORTED_EXTENSION),
            "extension {etype:#06x} on the {} entry",
            if on_leaf { "leaf" } else { "second" }
        );
        assert_eq!(auth.messages(), before);
        assert_eq!(auth.phase(), Phase::Failed);
        assert!(verifier.calls.borrow().chains.is_empty());
    }
    Ok(())
}

#[test]
fn certificate_verify_checks_captured_identity_and_fails_closed() -> Result<(), String> {
    let crypto = TestCrypto;
    let verifier = MockVerifier {
        chain_result: Ok(LEAF_KEY.to_vec()),
        signature_valid: false,
        calls: RefCell::new(Calls::default()),
    };
    let mut auth = start(&crypto)?;
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    let cert = certificate_body(&[], b"opaque certificate bytes");
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 11, &cert),
        Action::None
    );
    assert_eq!(
        verifier.calls.borrow().chains,
        vec![(Host::Dns(HOST.to_vec()), NOW, cert.clone())]
    );
    let expected_prefix = through_certificate(None, &cert);
    assert_eq!(auth.messages(), expected_prefix);
    let expected_input = clazel_tls::transcript::exec::certificate_verify_input(
        true,
        &crypto.hash(&expected_prefix),
    );
    assert_eq!(
        receive(
            &mut auth,
            &crypto,
            &verifier,
            15,
            &certificate_verify_body(SIGNATURE_SCHEME, SIGNATURE)
        ),
        Action::Fail(DECRYPT_ERROR)
    );
    let signature_call = verifier
        .calls
        .borrow()
        .signatures
        .last()
        .cloned()
        .ok_or("signature verifier not called")?;
    assert_eq!(signature_call.key, LEAF_KEY);
    assert_eq!(signature_call.scheme, SIGNATURE_SCHEME);
    assert_eq!(signature_call.signature, SIGNATURE);
    assert_eq!(signature_call.input, expected_input);
    assert_eq!(auth.phase(), Phase::Failed);
    assert_eq!(
        auth.step(&crypto, &verifier, Input::Application(b"x")),
        Action::None
    );
    Ok(())
}

#[test]
fn malformed_and_incorrect_server_finished_fail_with_distinct_alerts() -> Result<(), String> {
    let crypto = TestCrypto;
    let verifier = MockVerifier::accepts_chain();
    let mut malformed = start(&crypto)?;
    progress_to_finished(&mut malformed, &crypto, &verifier, None)?;
    assert_eq!(
        receive(&mut malformed, &crypto, &verifier, 20, &[0; 31]),
        Action::Fail(DECODE_ERROR)
    );

    let verifier = MockVerifier::accepts_chain();
    let mut incorrect = start(&crypto)?;
    let certificate = progress_to_finished(&mut incorrect, &crypto, &verifier, None)?;
    let transcript = through_certificate_verify(None, &certificate);
    assert_eq!(incorrect.messages(), transcript);
    let mut wrong = finished(&crypto, &SERVER_SECRET, &transcript);
    if let Some(first) = wrong.first_mut() {
        *first ^= 1;
    }
    assert_eq!(
        receive(&mut incorrect, &crypto, &verifier, 20, &wrong),
        Action::Fail(DECRYPT_ERROR)
    );
    assert_eq!(incorrect.phase(), Phase::Failed);
    assert_eq!(
        incorrect.step(&crypto, &verifier, Input::Application(b"x")),
        Action::None
    );
    Ok(())
}

#[test]
fn malformed_requests_unoffered_extensions_and_signature_schemes_are_rejected() -> Result<(), String>
{
    let crypto = TestCrypto;
    let verifier = MockVerifier::accepts_chain();

    let mut nonempty_context = start(&crypto)?;
    assert_eq!(
        receive(
            &mut nonempty_context,
            &crypto,
            &verifier,
            8,
            &encrypted_extensions(&[])
        ),
        Action::None
    );
    let request = request_body(b"not empty");
    let parsed_request = clazel_tls::handshake::read_certificate_request(&request)
        .ok_or_else(|| "generic CertificateRequest parser rejected a valid context".to_owned())?;
    assert_eq!(parsed_request.context, b"not empty");
    assert_eq!(
        receive(&mut nonempty_context, &crypto, &verifier, 13, &request),
        Action::Fail(ILLEGAL_PARAMETER)
    );

    let mut missing_sig_algs = start(&crypto)?;
    assert_eq!(
        receive(
            &mut missing_sig_algs,
            &crypto,
            &verifier,
            8,
            &encrypted_extensions(&[])
        ),
        Action::None
    );
    let request = certificate_request_body(
        &[],
        &[Extension {
            etype: 47,
            data: &[0, 0],
        }],
    );
    assert_eq!(
        receive(&mut missing_sig_algs, &crypto, &verifier, 13, &request),
        Action::Fail(MISSING_EXTENSION)
    );

    let mut unoffered_ee = start(&crypto)?;
    let response = [Extension {
        etype: 10,
        data: &[0, 2, 0, 29],
    }];
    assert_eq!(
        receive(
            &mut unoffered_ee,
            &crypto,
            &verifier,
            8,
            &encrypted_extensions(&response)
        ),
        Action::Fail(UNSUPPORTED_EXTENSION)
    );

    for scheme in [0x0403, 0x0201] {
        let verifier = MockVerifier::accepts_chain();
        let mut auth = start(&crypto)?;
        assert_eq!(
            receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
            Action::None
        );
        assert_eq!(
            receive(
                &mut auth,
                &crypto,
                &verifier,
                11,
                &certificate_body(&[], b"cert")
            ),
            Action::None
        );
        assert_eq!(
            receive(
                &mut auth,
                &crypto,
                &verifier,
                15,
                &certificate_verify_body(scheme, SIGNATURE)
            ),
            Action::Fail(ILLEGAL_PARAMETER)
        );
        assert!(verifier.calls.borrow().signatures.is_empty());
    }
    Ok(())
}

#[test]
fn generic_certificate_parser_preserves_context_but_initial_server_auth_rejects_it()
-> Result<(), String> {
    let crypto = TestCrypto;
    let verifier = MockVerifier::accepts_chain();
    let body = certificate_body(b"client-context", b"certificate-bytes");

    match clazel_tls::handshake::parse_handshake_body(11, &body, 32) {
        Ok(HsMsg::Certificate(certificate)) => {
            assert_eq!(certificate.context, b"client-context");
        }
        other => {
            return Err(format!(
                "generic parser did not retain certificate context: {other:?}"
            ));
        }
    }

    let mut auth = start(&crypto)?;
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 11, &body),
        Action::Fail(ILLEGAL_PARAMETER)
    );
    Ok(())
}

#[test]
fn out_of_order_messages_premature_application_and_wrong_ack_are_terminal() -> Result<(), String> {
    let crypto = TestCrypto;
    let verifier = MockVerifier::accepts_chain();
    let mut skipped_ee = start(&crypto)?;
    assert_eq!(
        receive(
            &mut skipped_ee,
            &crypto,
            &verifier,
            11,
            &certificate_body(&[], b"cert")
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );
    assert_eq!(skipped_ee.phase(), Phase::Failed);

    let mut duplicate_ee = start(&crypto)?;
    let ee = encrypted_extensions(&[]);
    assert_eq!(
        receive(&mut duplicate_ee, &crypto, &verifier, 8, &ee),
        Action::None
    );
    assert_eq!(
        receive(&mut duplicate_ee, &crypto, &verifier, 8, &ee),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let mut finished_skips_certificate = start(&crypto)?;
    assert_eq!(
        receive(&mut finished_skips_certificate, &crypto, &verifier, 8, &ee),
        Action::None
    );
    assert_eq!(
        receive(
            &mut finished_skips_certificate,
            &crypto,
            &verifier,
            20,
            &[0; 32]
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let mut finished_skips_signature = start(&crypto)?;
    assert_eq!(
        receive(&mut finished_skips_signature, &crypto, &verifier, 8, &ee),
        Action::None
    );
    assert_eq!(
        receive(
            &mut finished_skips_signature,
            &crypto,
            &verifier,
            11,
            &certificate_body(&[], b"cert")
        ),
        Action::None
    );
    assert_eq!(
        receive(
            &mut finished_skips_signature,
            &crypto,
            &verifier,
            20,
            &[0; 32]
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let mut premature = start(&crypto)?;
    assert_eq!(
        premature.step(&crypto, &verifier, Input::Application(b"early")),
        Action::Fail(UNEXPECTED_MESSAGE)
    );
    assert_eq!(premature.phase(), Phase::Failed);
    assert_eq!(
        premature.step(&crypto, &verifier, Input::Application(b"later")),
        Action::None
    );

    let mut wrong_ack = start(&crypto)?;
    assert_eq!(
        wrong_ack.step(&crypto, &verifier, Input::SentFinished),
        Action::Fail(INTERNAL_ERROR)
    );
    assert_eq!(wrong_ack.phase(), Phase::Failed);

    let mut closed = start(&crypto)?;
    assert_eq!(
        closed.step(&crypto, &verifier, Input::Closed),
        Action::Close
    );
    assert_eq!(closed.phase(), Phase::Closed);
    assert_eq!(
        closed.step(&crypto, &verifier, Input::Application(b"after close")),
        Action::None
    );
    Ok(())
}

#[test]
fn premature_application_is_never_delivered_before_send_ack() -> Result<(), String> {
    let crypto = TestCrypto;

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    assert_eq!(
        auth.step(&crypto, &verifier, Input::Application(b"before EE")),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    assert_eq!(
        auth.step(
            &crypto,
            &verifier,
            Input::Application(b"before Certificate")
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 13, &request_body(&[])),
        Action::None
    );
    assert_eq!(
        auth.step(
            &crypto,
            &verifier,
            Input::Application(b"before requested Certificate")
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    assert_eq!(
        receive(&mut auth, &crypto, &verifier, 8, &encrypted_extensions(&[])),
        Action::None
    );
    assert_eq!(
        receive(
            &mut auth,
            &crypto,
            &verifier,
            11,
            &certificate_body(&[], b"cert")
        ),
        Action::None
    );
    assert_eq!(
        auth.step(
            &crypto,
            &verifier,
            Input::Application(b"before CertificateVerify")
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    progress_to_finished(&mut auth, &crypto, &verifier, None)?;
    assert_eq!(
        auth.step(
            &crypto,
            &verifier,
            Input::Application(b"before server Finished")
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );

    let verifier = MockVerifier::accepts_chain();
    let mut auth = start(&crypto)?;
    complete_server_authentication(&mut auth, &crypto, &verifier, None)?;
    assert_eq!(
        auth.step(
            &crypto,
            &verifier,
            Input::Application(b"before SentFinished")
        ),
        Action::Fail(UNEXPECTED_MESSAGE)
    );
    assert_eq!(
        auth.step(
            &crypto,
            &verifier,
            Input::Application(b"after terminal failure")
        ),
        Action::None
    );
    Ok(())
}

#[test]
fn the_typed_host_reaches_the_validator_unchanged() -> Result<(), String> {
    let crypto = TestCrypto;
    for host in [
        Host::Ip(vec![192, 0, 2, 10]),
        Host::Ip(vec![
            0x20, 0x01, 0x0d, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
        ]),
        Host::Dns(b"example.test".to_vec()),
    ] {
        let verifier = MockVerifier::accepts_chain();
        let mut transcript = Transcript::new(b"client hello")
            .map_err(|error| format!("transcript start: {error:?}"))?;
        transcript
            .push(&crypto, Kind::ServerHello, b"server hello")
            .map_err(|error| format!("transcript ServerHello: {error:?}"))?;
        let mut auth = Auth::start(
            Config {
                host: host.clone(),
                ..config()
            },
            transcript,
        )
        .map_err(|alert| format!("auth start alert {alert}"))?;
        progress_to_certificate(&mut auth, &crypto, &verifier, None)?;
        let cert = certificate_body(&[], b"opaque certificate bytes");
        assert_eq!(
            receive(&mut auth, &crypto, &verifier, 11, &cert),
            Action::None
        );
        assert_eq!(verifier.calls.borrow().chains, vec![(host, NOW, cert)]);
    }
    Ok(())
}

#[test]
fn hosts_outside_the_bounds_are_refused_at_start() -> Result<(), String> {
    let crypto = TestCrypto;
    for host in [
        Host::Dns(Vec::new()),
        Host::Dns(vec![b'h'; 254]),
        Host::Dns(b"example.test.".to_vec()),
        Host::Ip(Vec::new()),
        Host::Ip(vec![1; 5]),
        Host::Ip(vec![1; 17]),
    ] {
        let mut transcript = Transcript::new(b"client hello")
            .map_err(|error| format!("transcript start: {error:?}"))?;
        transcript
            .push(&crypto, Kind::ServerHello, b"server hello")
            .map_err(|error| format!("transcript ServerHello: {error:?}"))?;
        assert!(matches!(
            Auth::start(Config { host, ..config() }, transcript),
            Err(INTERNAL_ERROR)
        ));
    }
    Ok(())
}
