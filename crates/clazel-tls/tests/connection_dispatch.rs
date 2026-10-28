//! Initial protected TLS connection dispatch integration tests.
//!
//! The crypto, AEAD, key exchange and verifier below are deterministic protocol
//! test doubles. They are not production cryptography, X.509 validation, or
//! signature verification.

use std::cell::RefCell;
use std::rc::Rc;

use clazel_tls::auth::spec::CertificateError;
use clazel_tls::auth::verify::Verifier;
use clazel_tls::connection::exec::{Action, Connection, Mode};
use clazel_tls::encode;
use clazel_tls::hello::client::{Config, Hello, Outcome};
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::record::Aead;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::schedule::exec::finished;
use clazel_tls::traffic::exec::{Decryptor, Encryptor};
use clazel_tls::traffic::provider::{Factory, KeyedAead};
use clazel_tls::types::{
    Certificate, CertificateEntry, CertificateVerify, Extension, NewSessionTicket,
};
use sha2::{Digest, Sha256};

const HOST: &[u8] = b"dispatch.example.test";
const NOW: u64 = 1_800_000_000;
const PRIVATE: [u8; 32] = [0x41; 32];
const PUBLIC: [u8; 32] = [0x52; 32];
const PEER: [u8; 32] = [0x63; 32];
const SHARED: [u8; 32] = [0x74; 32];
const LEAF_KEY: &[u8] = b"mock leaf key";

/// Input-sensitive, deterministic protocol test double; not real HKDF/HMAC.
struct TestCrypto;

impl Crypto for TestCrypto {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let mut input = b"dispatch extract".to_vec();
        input.extend_from_slice(salt);
        input.extend_from_slice(ikm);
        Sha256::digest(input).to_vec()
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut input = b"dispatch expand".to_vec();
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
        let mut input = b"dispatch hmac".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(message);
        Sha256::digest(input).to_vec()
    }
}

#[derive(Default)]
struct Trace {
    made_keys: Vec<Vec<u8>>,
}

#[derive(Clone)]
struct ToyFactory(Rc<RefCell<Trace>>);

impl ToyFactory {
    fn new() -> Self {
        Self(Rc::new(RefCell::new(Trace::default())))
    }
}

struct ToyCipher {
    key: Vec<u8>,
}

impl Factory for ToyFactory {
    type Cipher = ToyCipher;

    fn make(&self, key: &[u8]) -> Self::Cipher {
        self.0.borrow_mut().made_keys.push(key.to_vec());
        ToyCipher { key: key.to_vec() }
    }
}

impl Aead for ToyCipher {
    fn tag_len(&self) -> usize {
        16
    }

    fn nonce_len(&self) -> usize {
        12
    }

    fn seal(&self, nonce: &[u8], ad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let mut output = plaintext.to_vec();
        output.extend_from_slice(&tag(&self.key, nonce, ad, plaintext));
        output
    }

    fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> Option<Vec<u8>> {
        if ciphertext.len() < 16 {
            return None;
        }
        let split = ciphertext.len().saturating_sub(16);
        let (plaintext, received) = ciphertext.split_at(split);
        if received != tag(&self.key, nonce, ad, plaintext) {
            return None;
        }
        Some(plaintext.to_vec())
    }
}

impl KeyedAead for ToyCipher {}

fn tag(key: &[u8], nonce: &[u8], ad: &[u8], plaintext: &[u8]) -> [u8; 16] {
    let mut input = b"test-only dispatch tag".to_vec();
    input.extend_from_slice(key);
    input.extend_from_slice(nonce);
    input.extend_from_slice(ad);
    input.extend_from_slice(plaintext);
    let digest = Sha256::digest(input);
    let mut output = [0; 16];
    if let Some(bytes) = digest.get(..16) {
        output.copy_from_slice(bytes);
    }
    output
}

struct MockExchange;

impl KeyExchange for MockExchange {
    fn public_key(&self, _private_key: &[u8]) -> Vec<u8> {
        PUBLIC.to_vec()
    }

    fn shared_secret(&self, _private_key: &[u8], _peer_key: &[u8]) -> Option<Vec<u8>> {
        Some(SHARED.to_vec())
    }
}

struct MockVerifier;

impl Verifier for MockVerifier {
    fn chain(
        &self,
        host: &[u8],
        now: u64,
        certificate_body: &[u8],
    ) -> Result<Vec<u8>, CertificateError> {
        if host == HOST && now == NOW && !certificate_body.is_empty() {
            Ok(LEAF_KEY.to_vec())
        } else {
            Err(CertificateError::BadCertificate)
        }
    }

    fn signature(&self, key: &[u8], _scheme: u16, _input: &[u8], _signature: &[u8]) -> bool {
        key == LEAF_KEY
    }

    fn finished_equal(&self, received: &[u8], expected: &[u8]) -> bool {
        received == expected
    }
}

fn config() -> Config {
    Config {
        host: HOST.to_vec(),
        now: NOW,
        random: vec![0x11; 32],
        session_id: Vec::new(),
        public_key: PUBLIC.to_vec(),
        send_sni: true,
    }
}

fn server_hello() -> Vec<u8> {
    let version = [3, 4];
    let mut key_share = vec![0, 29, 0, 32];
    key_share.extend_from_slice(&PEER);
    let mut extensions = Vec::new();
    extensions.extend_from_slice(&43u16.to_be_bytes());
    extensions.extend_from_slice(&2u16.to_be_bytes());
    extensions.extend_from_slice(&version);
    extensions.extend_from_slice(&51u16.to_be_bytes());
    extensions.extend_from_slice(
        &u16::try_from(key_share.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    extensions.extend_from_slice(&key_share);
    let mut body = vec![3, 3];
    body.extend_from_slice(&[0x33; 32]);
    body.push(0);
    body.extend_from_slice(&0x1303u16.to_be_bytes());
    body.push(0);
    body.extend_from_slice(
        &u16::try_from(extensions.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    body.extend_from_slice(&extensions);
    body
}

fn handshake(typ: u8, body: &[u8]) -> Vec<u8> {
    let mut output = Vec::new();
    encode::write_handshake(&mut output, typ, body);
    output
}

fn certificate_body() -> Vec<u8> {
    let cert = Certificate {
        context: &[],
        entries: vec![CertificateEntry {
            cert_data: b"mock certificate",
            extensions: Vec::new(),
        }],
    };
    let mut output = Vec::new();
    encode::write_certificate(&mut output, &cert);
    output
}

fn encrypted_extensions() -> Vec<u8> {
    let mut output = Vec::new();
    encode::write_encrypted_extensions(&mut output, &[] as &[Extension<'_>]);
    output
}

fn ticket_body(lifetime: u32, extensions: Vec<Extension<'_>>) -> Vec<u8> {
    let ticket = NewSessionTicket {
        ticket_lifetime: lifetime,
        ticket_age_add: 0x1234_5678,
        ticket_nonce: &[0x01],
        ticket: b"opaque ticket",
        extensions,
    };
    let mut output = Vec::new();
    encode::write_new_session_ticket(&mut output, &ticket);
    output
}

fn certificate_verify() -> Vec<u8> {
    let cv = CertificateVerify {
        algorithm: 0x0804,
        signature: b"mock sig",
    };
    let mut output = Vec::new();
    encode::write_certificate_verify(&mut output, &cv);
    output
}

fn reference_expand_label(
    crypto: &TestCrypto,
    secret: &[u8],
    label: &[u8],
    context: &[u8],
) -> Vec<u8> {
    let mut info = Vec::new();
    info.extend_from_slice(&32u16.to_be_bytes());
    info.push(u8::try_from(6usize.saturating_add(label.len())).unwrap_or(u8::MAX));
    info.extend_from_slice(b"tls13 ");
    info.extend_from_slice(label);
    info.push(u8::try_from(context.len()).unwrap_or(u8::MAX));
    info.extend_from_slice(context);
    crypto.expand(secret, &info, 32)
}

fn handshake_secrets(crypto: &TestCrypto, transcript: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let zero = [0; 32];
    let early = crypto.extract(&zero, &zero);
    let derived = reference_expand_label(crypto, &early, b"derived", &crypto.hash(&[]));
    let handshake = crypto.extract(&derived, &SHARED);
    let transcript_hash = crypto.hash(transcript);
    let client = reference_expand_label(crypto, &handshake, b"c hs traffic", &transcript_hash);
    let server = reference_expand_label(crypto, &handshake, b"s hs traffic", &transcript_hash);
    let derived_handshake =
        reference_expand_label(crypto, &handshake, b"derived", &crypto.hash(&[]));
    let master = crypto.extract(&derived_handshake, &zero);
    (client, server, master)
}

struct Fixture {
    connection: Connection<TestCrypto, ToyFactory, MockVerifier>,
    crypto: TestCrypto,
    factory: ToyFactory,
    client_secret: Vec<u8>,
    server_secret: Vec<u8>,
    master: Vec<u8>,
    transcript: Vec<u8>,
    server_plaintext: Vec<u8>,
    server_records: Vec<Vec<u8>>,
}

fn fixture() -> Result<Fixture, String> {
    let crypto = TestCrypto;
    let factory = ToyFactory::new();
    let exchange = MockExchange;
    let body = server_hello();
    let (hello, client_hello) =
        Hello::start(config()).map_err(|e| format!("Hello start alert {e}"))?;
    let established = match hello
        .receive(&crypto, &body)
        .map_err(|e| format!("ServerHello alert {e}"))?
    {
        Outcome::Established(value) => value,
        Outcome::Retry(_, _) => return Err("unexpected retry".to_owned()),
    };
    let mut transcript = client_hello;
    transcript.extend_from_slice(&handshake(2, &body));
    let (client_secret, server_secret, master) = handshake_secrets(&crypto, &transcript);
    let expected_client_secret = client_secret.clone();
    let expected_server_secret = server_secret.clone();
    let keys = established
        .into_record_auth(&crypto, &exchange, &factory, &PRIVATE)
        .map_err(|e| format!("key handoff alert {e}"))?;
    let connection = Connection::new(keys, TestCrypto, factory.clone(), MockVerifier);

    let cert = certificate_body();
    let cv = certificate_verify();
    let mut prefix = transcript;
    prefix.extend_from_slice(&handshake(8, &encrypted_extensions()));
    prefix.extend_from_slice(&handshake(11, &cert));
    let cv_input =
        clazel_tls::transcript::exec::certificate_verify_input(true, &crypto.hash(&prefix));
    let _ = cv_input;
    prefix.extend_from_slice(&handshake(15, &cv));
    let verify_data = finished(&crypto, &server_secret, &prefix);
    let mut flight = prefix;
    flight.extend_from_slice(&handshake(20, &verify_data));
    let mut encryptor = Encryptor::new(&crypto, &factory, &server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    let mut records = Vec::new();
    for message in [
        handshake(8, &encrypted_extensions()),
        handshake(11, &cert),
        handshake(15, &cv),
        handshake(20, &verify_data),
    ] {
        let record = encryptor
            .seal(22, &message, 0)
            .map_err(|e| format!("record seal alert {e}"))?;
        records.push(record);
    }
    Ok(Fixture {
        connection,
        crypto,
        factory,
        client_secret: expected_client_secret,
        server_secret: expected_server_secret,
        master,
        transcript: flight.clone(),
        server_plaintext: flight,
        server_records: records,
    })
}

fn ready_fixture() -> Result<Fixture, String> {
    let mut fixture = fixture()?;
    let mut client_flight = Action::None;
    for record in &fixture.server_records {
        let (consumed, action) = fixture.connection.feed(record);
        assert_eq!(consumed, record.len());
        client_flight = action;
    }
    let wire = match client_flight {
        Action::Send(wire) => wire,
        other => return Err(format!("expected client flight, got {other:?}")),
    };
    assert_eq!(
        fixture.connection.acknowledge_client_flight(&wire),
        Action::Ready
    );
    Ok(fixture)
}

fn updated_traffic_secret(crypto: &TestCrypto, secret: &[u8]) -> Vec<u8> {
    reference_expand_label(crypto, secret, b"traffic upd", &[])
}

fn application_secrets(fixture: &Fixture) -> (Vec<u8>, Vec<u8>) {
    let transcript_hash = fixture.crypto.hash(&fixture.transcript);
    (
        reference_expand_label(
            &fixture.crypto,
            &fixture.master,
            b"c ap traffic",
            &transcript_hash,
        ),
        reference_expand_label(
            &fixture.crypto,
            &fixture.master,
            b"s ap traffic",
            &transcript_hash,
        ),
    )
}

#[test]
fn fragmented_server_flight_gates_client_finished_and_application_keys() -> Result<(), String> {
    let mut fixture = fixture()?;
    let first_record = fixture
        .server_records
        .first()
        .ok_or("missing first server record")?;
    let split = first_record.len().saturating_sub(7);
    let (used, first) = fixture
        .connection
        .feed(first_record.get(..split).ok_or("short record")?);
    assert_eq!(used, split);
    assert_eq!(first, Action::None);
    assert_eq!(fixture.connection.mode(), Mode::Handshake);

    let tail = first_record.get(split..).ok_or("missing record suffix")?;
    let (used, first_done) = fixture.connection.feed(tail);
    assert_eq!(used, tail.len());
    assert_eq!(first_done, Action::None);
    let mut send = Action::None;
    for record in fixture.server_records.iter().skip(1) {
        let (used, action) = fixture.connection.feed(record);
        assert_eq!(used, record.len());
        send = action;
    }
    let wire = match send {
        Action::Send(bytes) => bytes,
        other => return Err(format!("expected client flight, got {other:?}")),
    };
    assert_eq!(fixture.connection.mode(), Mode::AwaitClientFlight);
    assert_eq!(fixture.connection.feed(&[23, 3, 3, 0, 17, 0]).0, 0);

    let mut client_decryptor =
        Decryptor::new(&fixture.crypto, &fixture.factory, &fixture.client_secret)
            .map_err(|e| format!("client test epoch alert {e}"))?;
    let client_plaintext = match client_decryptor.open(&wire) {
        clazel_tls::traffic::exec::Read::Record(22, bytes, consumed) if consumed == wire.len() => {
            bytes
        }
        other => return Err(format!("unexpected client flight decode {other:?}")),
    };
    assert_eq!(client_plaintext.first(), Some(&20));
    let expected_client_finished =
        finished(&fixture.crypto, &fixture.client_secret, &fixture.transcript);
    assert_eq!(client_plaintext, handshake(20, &expected_client_finished));
    assert_eq!(
        fixture.connection.acknowledge_client_flight(&wire),
        Action::Ready
    );
    assert_eq!(fixture.connection.mode(), Mode::Ready);

    let app_hash = fixture.crypto.hash(&fixture.transcript);
    let client_app_secret =
        reference_expand_label(&fixture.crypto, &fixture.master, b"c ap traffic", &app_hash);
    let server_app_secret =
        reference_expand_label(&fixture.crypto, &fixture.master, b"s ap traffic", &app_hash);
    assert_ne!(client_app_secret, server_app_secret);
    let installed = fixture.factory.0.borrow();
    let client_hs_key =
        reference_expand_label(&fixture.crypto, &fixture.client_secret, b"key", &[]);
    let server_hs_key =
        reference_expand_label(&fixture.crypto, &fixture.server_secret, b"key", &[]);
    let client_app_key = reference_expand_label(&fixture.crypto, &client_app_secret, b"key", &[]);
    let server_app_key = reference_expand_label(&fixture.crypto, &server_app_secret, b"key", &[]);
    assert_eq!(installed.made_keys.first(), Some(&client_hs_key));
    assert_eq!(installed.made_keys.get(1), Some(&server_hs_key));
    assert_eq!(
        installed
            .made_keys
            .get(installed.made_keys.len().saturating_sub(2)..),
        Some(&[client_app_key, server_app_key][..])
    );
    drop(installed);
    let mut app_sender = Encryptor::new(&fixture.crypto, &fixture.factory, &server_app_secret)
        .map_err(|e| format!("application test epoch alert {e}"))?;
    let app_record = app_sender
        .seal(23, b"payload", 0)
        .map_err(|e| format!("app seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&app_record),
        (app_record.len(), Action::Deliver(b"payload".to_vec()))
    );
    let client_record = match fixture.connection.send_application(b"client payload", 0) {
        Action::Send(wire) => wire,
        other => {
            return Err(format!(
                "expected protected application send, got {other:?}"
            ));
        }
    };
    let mut client_app_reader =
        Decryptor::new(&fixture.crypto, &fixture.factory, &client_app_secret)
            .map_err(|e| format!("client application test epoch alert {e}"))?;
    assert!(matches!(
        client_app_reader.open(&client_record),
        clazel_tls::traffic::exec::Read::Record(23, bytes, consumed)
            if bytes == b"client payload" && consumed == client_record.len()
    ));
    let close_notify = app_sender
        .seal(21, &[1, 0], 0)
        .map_err(|e| format!("close-notify seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&close_notify),
        (close_notify.len(), Action::PeerClosed)
    );
    assert_eq!(fixture.connection.mode(), Mode::Ready);
    assert_eq!(fixture.connection.feed(&[0xff, 0xff]), (2, Action::None));
    assert_eq!(fixture.connection.eof(), Action::PeerClosed);

    let after_peer_close = match fixture
        .connection
        .send_application(b"write side remains open", 0)
    {
        Action::Send(wire) => wire,
        other => {
            return Err(format!(
                "expected send after peer half-close, got {other:?}"
            ));
        }
    };
    assert!(matches!(
        client_app_reader.open(&after_peer_close),
        clazel_tls::traffic::exec::Read::Record(23, bytes, consumed)
            if bytes == b"write side remains open" && consumed == after_peer_close.len()
    ));
    let local_close = match fixture.connection.close_write() {
        Action::Send(wire) => wire,
        other => {
            return Err(format!(
                "expected protected local close_notify, got {other:?}"
            ));
        }
    };
    assert!(matches!(
        client_app_reader.open(&local_close),
        clazel_tls::traffic::exec::Read::Record(21, bytes, consumed)
            if bytes == [1, 0] && consumed == local_close.len()
    ));
    assert_eq!(
        fixture.connection.acknowledge_close_notify(&local_close),
        Action::Close
    );
    assert_eq!(fixture.connection.mode(), Mode::Closed);
    Ok(())
}

#[test]
fn wrong_finished_and_bad_mac_fail_closed() -> Result<(), String> {
    let mut bad_finished = fixture()?;
    // The ciphertext's authenticated plaintext is built under the right key,
    // but carries a wrong Finished; Auth must terminate before a client send.
    for record in bad_finished.server_records.iter().take(3) {
        let (consumed, action) = bad_finished.connection.feed(record);
        assert_eq!(consumed, record.len());
        assert_eq!(action, Action::None);
    }
    let prefix_end = bad_finished.server_plaintext.len().saturating_sub(36);
    let before_finished = bad_finished
        .server_plaintext
        .get(..prefix_end)
        .ok_or("missing Finished message")?;
    let mut wrong_finished_body = finished(
        &bad_finished.crypto,
        &bad_finished.server_secret,
        before_finished,
    );
    if let Some(first) = wrong_finished_body.first_mut() {
        *first ^= 1;
    }
    let wrong_finished_message = handshake(20, &wrong_finished_body);
    let mut wrong_sealer = Encryptor::new(
        &bad_finished.crypto,
        &bad_finished.factory,
        &bad_finished.server_secret,
    )
    .map_err(|e| format!("server epoch alert {e}"))?;
    for message in [
        handshake(8, &encrypted_extensions()),
        handshake(11, &certificate_body()),
        handshake(15, &certificate_verify()),
    ] {
        let _ = wrong_sealer
            .seal(22, &message, 0)
            .map_err(|e| format!("record seal alert {e}"))?;
    }
    let wrong = wrong_sealer
        .seal(22, &wrong_finished_message, 0)
        .map_err(|e| format!("record seal alert {e}"))?;
    let (_, result) = bad_finished.connection.feed(&wrong);
    assert_eq!(result, Action::Fail(clazel_tls::spec::DECRYPT_ERROR));
    assert_eq!(bad_finished.connection.mode(), Mode::Failed);
    assert_eq!(bad_finished.connection.feed(&wrong), (0, Action::None));

    let mut bad_mac = fixture()?;
    let mut corrupt = bad_mac
        .server_records
        .first()
        .cloned()
        .ok_or("missing first record")?;
    if let Some(last) = corrupt.last_mut() {
        *last ^= 1;
    }
    let (_, result) = bad_mac.connection.feed(&corrupt);
    assert_eq!(result, Action::Fail(clazel_tls::spec::BAD_RECORD_MAC));
    assert_eq!(bad_mac.connection.mode(), Mode::Failed);
    assert_eq!(bad_mac.connection.feed(&corrupt), (0, Action::None));
    Ok(())
}

#[test]
fn finished_must_end_at_record_boundary_and_compatibility_ccs_is_dropped() -> Result<(), String> {
    let mut trailing_fixture = fixture()?;
    let mut trailing_message = trailing_fixture.server_plaintext.clone();
    trailing_message.extend_from_slice(&handshake(8, &encrypted_extensions()));
    let mut server_sealer = Encryptor::new(
        &trailing_fixture.crypto,
        &trailing_fixture.factory,
        &trailing_fixture.server_secret,
    )
    .map_err(|e| format!("server epoch alert {e}"))?;
    let trailing_record = server_sealer
        .seal(22, &trailing_message, 0)
        .map_err(|e| format!("record seal alert {e}"))?;
    let (used, result) = trailing_fixture.connection.feed(&trailing_record);
    assert_eq!(used, trailing_record.len());
    assert_eq!(result, Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE));

    let ccs = [20, 3, 3, 0, 1, 1];
    // An in-window compatibility CCS is ignored before the next protected record.
    let mut fresh = fixture()?;
    let (ccs_used, ignored) = fresh.connection.feed(&ccs);
    assert_eq!(ccs_used, ccs.len());
    assert_eq!(ignored, Action::Ignored);
    let mut coalesced = Vec::new();
    for record in &fresh.server_records {
        coalesced.extend_from_slice(record);
    }
    let mut remaining = coalesced.as_slice();
    let mut send = Action::None;
    while !remaining.is_empty() {
        let (consumed, action) = fresh.connection.feed(remaining);
        assert!(consumed > 0);
        assert!(consumed <= remaining.len());
        remaining = remaining.get(consumed..).ok_or("bad consumed boundary")?;
        send = action;
    }
    assert!(matches!(send, Action::Send(_)));

    let mut after_finished = fixture()?;
    let mut client_flight = Action::None;
    for record in &after_finished.server_records {
        let (_, action) = after_finished.connection.feed(record);
        client_flight = action;
    }
    assert!(matches!(client_flight, Action::Send(_)));
    let client_wire = match client_flight {
        Action::Send(bytes) => bytes,
        other => return Err(format!("expected client flight before CCS, got {other:?}")),
    };
    assert_eq!(
        after_finished
            .connection
            .acknowledge_client_flight(&client_wire),
        Action::Ready
    );
    assert_eq!(
        after_finished.connection.feed(&ccs).1,
        Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
    );
    Ok(())
}

#[test]
fn application_record_before_server_finished_is_terminal() -> Result<(), String> {
    let mut fixture = fixture()?;
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &fixture.server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    let premature = server
        .seal(23, b"too early", 0)
        .map_err(|e| format!("record seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&premature),
        (
            premature.len(),
            Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
        )
    );
    assert_eq!(fixture.connection.mode(), Mode::Failed);
    assert_eq!(fixture.connection.feed(&premature), (0, Action::None));
    Ok(())
}

#[test]
fn local_key_update_waits_for_exact_send_ack_and_rotates_only_client_epoch() -> Result<(), String> {
    let mut failed_fixture = ready_fixture()?;
    let (old_client_secret, _) = application_secrets(&failed_fixture);
    let wire = match failed_fixture.connection.request_key_update(true) {
        Action::Send(wire) => wire,
        other => return Err(format!("expected KeyUpdate send, got {other:?}")),
    };
    let mut old_client_reader = Decryptor::new(
        &failed_fixture.crypto,
        &failed_fixture.factory,
        &old_client_secret,
    )
    .map_err(|e| format!("old client epoch alert {e}"))?;
    assert!(matches!(old_client_reader.open(&wire),
        clazel_tls::traffic::exec::Read::Record(22, bytes, consumed)
            if bytes == handshake(24, &[1]) && consumed == wire.len()));
    assert_eq!(
        failed_fixture.connection.send_application(b"blocked", 0),
        Action::None
    );

    let mut wrong_ack = wire.clone();
    if let Some(last) = wrong_ack.last_mut() {
        *last ^= 1;
    }
    assert_eq!(
        failed_fixture.connection.acknowledge_key_update(&wrong_ack),
        Action::Fail(clazel_tls::spec::INTERNAL_ERROR)
    );
    assert_eq!(failed_fixture.connection.mode(), Mode::Failed);

    let mut fixture = ready_fixture()?;
    let (old_client_secret, _) = application_secrets(&fixture);
    let updated_client_secret = updated_traffic_secret(&fixture.crypto, &old_client_secret);
    let wire = match fixture.connection.request_key_update(true) {
        Action::Send(wire) => wire,
        other => return Err(format!("expected KeyUpdate send, got {other:?}")),
    };
    assert_eq!(
        fixture.connection.acknowledge_key_update(&wire),
        Action::None
    );
    let app_wire = match fixture.connection.send_application(b"after update", 0) {
        Action::Send(wire) => wire,
        other => return Err(format!("expected application send, got {other:?}")),
    };
    let mut peer_reader = Decryptor::new(&fixture.crypto, &fixture.factory, &updated_client_secret)
        .map_err(|e| format!("updated client epoch alert {e}"))?;
    assert!(matches!(peer_reader.open(&app_wire),
        clazel_tls::traffic::exec::Read::Record(23, bytes, consumed)
            if bytes == b"after update" && consumed == app_wire.len()));
    Ok(())
}

#[test]
fn peer_key_update_rotates_receive_epoch_and_sends_unrequested_response() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let (old_client_secret, old_server_secret) = application_secrets(&fixture);
    let updated_client_secret = updated_traffic_secret(&fixture.crypto, &old_client_secret);
    let updated_server_secret = updated_traffic_secret(&fixture.crypto, &old_server_secret);
    let mut old_server_sender =
        Encryptor::new(&fixture.crypto, &fixture.factory, &old_server_secret)
            .map_err(|e| format!("old server epoch alert {e}"))?;
    let request = old_server_sender
        .seal(22, &handshake(24, &[1]), 0)
        .map_err(|e| format!("KeyUpdate seal alert {e}"))?;
    let (consumed, response) = fixture.connection.feed(&request);
    assert_eq!(consumed, request.len());
    let response = match response {
        Action::Send(wire) => wire,
        other => return Err(format!("expected mandatory response, got {other:?}")),
    };
    assert_eq!(
        fixture.connection.send_application(b"blocked", 0),
        Action::None
    );

    let mut old_client_reader =
        Decryptor::new(&fixture.crypto, &fixture.factory, &old_client_secret)
            .map_err(|e| format!("old client epoch alert {e}"))?;
    assert!(matches!(old_client_reader.open(&response),
        clazel_tls::traffic::exec::Read::Record(22, bytes, consumed)
            if bytes == handshake(24, &[0]) && consumed == response.len()));
    assert_eq!(
        fixture.connection.acknowledge_key_update(&response),
        Action::None
    );

    let app_wire = match fixture.connection.send_application(b"client new epoch", 0) {
        Action::Send(wire) => wire,
        other => return Err(format!("expected application send, got {other:?}")),
    };
    let mut updated_client_reader =
        Decryptor::new(&fixture.crypto, &fixture.factory, &updated_client_secret)
            .map_err(|e| format!("updated client epoch alert {e}"))?;
    assert!(matches!(updated_client_reader.open(&app_wire),
        clazel_tls::traffic::exec::Read::Record(23, bytes, consumed)
            if bytes == b"client new epoch" && consumed == app_wire.len()));

    let mut updated_server_sender =
        Encryptor::new(&fixture.crypto, &fixture.factory, &updated_server_secret)
            .map_err(|e| format!("updated server epoch alert {e}"))?;
    let peer_app = updated_server_sender
        .seal(23, b"server new epoch", 0)
        .map_err(|e| format!("updated server app seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&peer_app),
        (
            peer_app.len(),
            Action::Deliver(b"server new epoch".to_vec())
        )
    );
    Ok(())
}

#[test]
fn peer_key_update_after_local_close_notify_rotates_receive_epoch_and_sends_nothing(
) -> Result<(), String> {
    // RFC 8446 §6.1 and §4.6.3: nothing is written after our close_notify,
    // whether it is still awaiting its send acknowledgement or already sent.
    for acknowledge_first in [false, true] {
        let mut fixture = ready_fixture()?;
        let (_, old_server_secret) = application_secrets(&fixture);
        let updated_server_secret = updated_traffic_secret(&fixture.crypto, &old_server_secret);
        let close = match fixture.connection.close_write() {
            Action::Send(wire) => wire,
            other => return Err(format!("expected protected close_notify, got {other:?}")),
        };
        if acknowledge_first {
            assert_eq!(
                fixture.connection.acknowledge_close_notify(&close),
                Action::WriteClosed
            );
        }

        let mut old_server_sender =
            Encryptor::new(&fixture.crypto, &fixture.factory, &old_server_secret)
                .map_err(|e| format!("old server epoch alert {e}"))?;
        let request = old_server_sender
            .seal(22, &handshake(24, &[1]), 0)
            .map_err(|e| format!("KeyUpdate seal alert {e}"))?;
        assert_eq!(
            fixture.connection.feed(&request),
            (request.len(), Action::None),
            "acknowledge_first = {acknowledge_first}"
        );
        assert_eq!(fixture.connection.mode(), Mode::Ready);
        assert_eq!(fixture.connection.request_key_update(false), Action::None);

        if !acknowledge_first {
            assert_eq!(
                fixture.connection.acknowledge_close_notify(&close),
                Action::WriteClosed
            );
        }

        let mut updated_server_sender =
            Encryptor::new(&fixture.crypto, &fixture.factory, &updated_server_secret)
                .map_err(|e| format!("updated server epoch alert {e}"))?;
        let peer_app = updated_server_sender
            .seal(23, b"server new epoch", 0)
            .map_err(|e| format!("updated server app seal alert {e}"))?;
        assert_eq!(
            fixture.connection.feed(&peer_app),
            (
                peer_app.len(),
                Action::Deliver(b"server new epoch".to_vec())
            )
        );
    }
    Ok(())
}

#[test]
fn fragmented_key_update_with_trailing_message_is_rejected() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let (_, server_secret) = application_secrets(&fixture);
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    let update = handshake(24, &[0]);
    let first = update.get(..2).ok_or("short KeyUpdate")?;
    let tail = update.get(2..).ok_or("missing KeyUpdate suffix")?;
    let first_record = server
        .seal(22, first, 0)
        .map_err(|e| format!("first fragment seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&first_record),
        (first_record.len(), Action::None)
    );

    let mut second_fragment = tail.to_vec();
    second_fragment.extend_from_slice(&handshake(24, &[0]));
    let second_record = server
        .seal(22, &second_fragment, 0)
        .map_err(|e| format!("second fragment seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&second_record),
        (
            second_record.len(),
            Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
        )
    );
    assert_eq!(fixture.connection.mode(), Mode::Failed);
    assert_eq!(fixture.connection.feed(&second_record), (0, Action::None));
    Ok(())
}

#[test]
fn valid_new_session_tickets_are_discarded_without_resumption_state() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let (_, server_secret) = application_secrets(&fixture);
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;

    // With no PSK mode, this profile never caches or derives a resumption PSK.
    // Zero and over-seven-day lifetimes are discarded along with usable tickets.
    for lifetime in [0, 604_800, 604_801] {
        let message = handshake(4, &ticket_body(lifetime, Vec::new()));
        let record = server
            .seal(22, &message, 0)
            .map_err(|e| format!("ticket seal alert {e}"))?;
        assert_eq!(
            fixture.connection.feed(&record),
            (record.len(), Action::None)
        );
        assert_eq!(fixture.connection.mode(), Mode::Ready);
    }

    let app = server
        .seal(23, b"ticket did not replace application state", 0)
        .map_err(|e| format!("server app seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&app),
        (
            app.len(),
            Action::Deliver(b"ticket did not replace application state".to_vec())
        )
    );
    Ok(())
}

/// RFC 8446 §5.1: a compatibility CCS between the fragments of one handshake
/// message interleaves another record type and is fatal unexpected_message.
#[test]
fn compatibility_ccs_between_handshake_fragments_is_refused() -> Result<(), String> {
    let mut fixture = fixture()?;
    let encrypted_extensions = handshake(8, &encrypted_extensions());
    let split = encrypted_extensions.len().saturating_div(2);
    let prefix = encrypted_extensions.get(..split).ok_or("short EE prefix")?;
    let suffix = encrypted_extensions
        .get(split..)
        .ok_or("missing EE suffix")?;
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &fixture.server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;

    let prefix_record = server
        .seal(22, prefix, 0)
        .map_err(|e| format!("prefix seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&prefix_record),
        (prefix_record.len(), Action::None)
    );
    let ccs = [20, 3, 3, 0, 1, 1];
    assert_eq!(fixture.connection.feed(&ccs), (ccs.len(), Action::Fail(10)));
    // The failure is terminal: the rest of the message is not accepted.
    let suffix_record = server
        .seal(22, suffix, 0)
        .map_err(|e| format!("suffix seal alert {e}"))?;
    assert_eq!(fixture.connection.feed(&suffix_record).1, Action::None);
    Ok(())
}

/// A compatibility CCS between two whole handshake messages is still dropped.
#[test]
fn compatibility_ccs_between_whole_handshake_messages_is_dropped() -> Result<(), String> {
    let mut fixture = fixture()?;
    let encrypted_extensions = handshake(8, &encrypted_extensions());
    let certificate = handshake(11, &certificate_body());
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &fixture.server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    let ee_record = server
        .seal(22, &encrypted_extensions, 0)
        .map_err(|e| format!("EE seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&ee_record),
        (ee_record.len(), Action::None)
    );
    let ccs = [20, 3, 3, 0, 1, 1];
    assert_eq!(fixture.connection.feed(&ccs), (ccs.len(), Action::Ignored));
    let certificate_record = server
        .seal(22, &certificate, 0)
        .map_err(|e| format!("certificate seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&certificate_record),
        (certificate_record.len(), Action::None)
    );
    Ok(())
}

#[test]
fn invalid_or_protected_ccs_and_other_record_interleaving_fail() -> Result<(), String> {
    let mut invalid_fixture = fixture()?;
    let invalid_ccs = [20, 3, 3, 0, 1, 2];
    assert_eq!(
        invalid_fixture.connection.feed(&invalid_ccs),
        (
            invalid_ccs.len(),
            Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
        )
    );

    let mut interleaved_fixture = fixture()?;
    let mut server = Encryptor::new(
        &interleaved_fixture.crypto,
        &interleaved_fixture.factory,
        &interleaved_fixture.server_secret,
    )
    .map_err(|e| format!("interleaved server epoch alert {e}"))?;
    let prefix = handshake(8, &encrypted_extensions());
    let prefix = prefix.get(..3).ok_or("short handshake prefix")?;
    let partial_record = server
        .seal(22, prefix, 0)
        .map_err(|e| format!("partial handshake seal alert {e}"))?;
    assert_eq!(
        interleaved_fixture.connection.feed(&partial_record),
        (partial_record.len(), Action::None)
    );
    let app_record = server
        .seal(23, b"interleaved application record", 0)
        .map_err(|e| format!("interleaved app seal alert {e}"))?;
    assert_eq!(
        interleaved_fixture.connection.feed(&app_record),
        (
            app_record.len(),
            Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
        )
    );

    let mut protected_fixture = ready_fixture()?;
    let (_, server_secret) = application_secrets(&protected_fixture);
    let key = clazel_tls::schedule::exec::write_key(&protected_fixture.crypto, &server_secret);
    let iv = clazel_tls::schedule::exec::write_iv(&protected_fixture.crypto, &server_secret);
    let cipher = ToyCipher { key };
    let protected_ccs = clazel_tls::record::encrypt_record(&cipher, &iv, 0, 20, &[1], 0);
    assert_eq!(
        protected_fixture.connection.feed(&protected_ccs),
        (
            protected_ccs.len(),
            Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
        )
    );
    Ok(())
}

#[test]
fn user_canceled_is_nonfatal_and_eof_without_close_notify_is_truncation() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let (_, server_secret) = application_secrets(&fixture);
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    for level in [1, 2] {
        let alert = server
            .seal(21, &[level, 90], 0)
            .map_err(|e| format!("user-canceled seal alert {e}"))?;
        assert_eq!(
            fixture.connection.feed(&alert),
            (alert.len(), Action::Cancelled)
        );
        assert_eq!(fixture.connection.mode(), Mode::Ready);
    }
    let app = server
        .seal(23, b"user_canceled did not close the write direction", 0)
        .map_err(|e| format!("app seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&app),
        (
            app.len(),
            Action::Deliver(b"user_canceled did not close the write direction".to_vec())
        )
    );
    assert_eq!(
        fixture.connection.eof(),
        Action::Fail(clazel_tls::spec::INTERNAL_ERROR)
    );
    assert_eq!(fixture.connection.mode(), Mode::Failed);
    Ok(())
}

#[test]
fn peer_close_notify_preserves_an_unacknowledged_local_key_update() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let (old_client_secret, old_server_secret) = application_secrets(&fixture);
    let next_client_secret = updated_traffic_secret(&fixture.crypto, &old_client_secret);
    let key_update = match fixture.connection.request_key_update(false) {
        Action::Send(wire) => wire,
        other => return Err(format!("expected pending KeyUpdate, got {other:?}")),
    };
    assert_eq!(
        fixture
            .connection
            .send_application(b"blocked until update ack", 0),
        Action::None
    );

    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &old_server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    let close = server
        .seal(21, &[1, 0], 0)
        .map_err(|e| format!("close-notify seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&close),
        (close.len(), Action::PeerClosed)
    );
    assert_eq!(fixture.connection.mode(), Mode::Ready);

    assert_eq!(
        fixture.connection.acknowledge_key_update(&key_update),
        Action::None
    );
    let app = match fixture
        .connection
        .send_application(b"write survives peer close", 0)
    {
        Action::Send(wire) => wire,
        other => return Err(format!("expected send after KeyUpdate ack, got {other:?}")),
    };
    let mut peer = Decryptor::new(&fixture.crypto, &fixture.factory, &next_client_secret)
        .map_err(|e| format!("peer epoch alert {e}"))?;
    assert!(matches!(
        peer.open(&app),
        clazel_tls::traffic::exec::Read::Record(23, bytes, consumed)
            if bytes == b"write survives peer close" && consumed == app.len()
    ));

    let local_close = match fixture.connection.close_write() {
        Action::Send(wire) => wire,
        other => {
            return Err(format!(
                "expected local close after KeyUpdate, got {other:?}"
            ));
        }
    };
    assert_eq!(
        fixture.connection.acknowledge_close_notify(&local_close),
        Action::Close
    );
    assert_eq!(fixture.connection.mode(), Mode::Closed);
    Ok(())
}

#[test]
fn close_notify_write_requires_exact_send_acknowledgement() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let wire = match fixture.connection.close_write() {
        Action::Send(wire) => wire,
        other => return Err(format!("expected protected close_notify, got {other:?}")),
    };
    let mut wrong = wire.clone();
    if let Some(last) = wrong.last_mut() {
        *last ^= 1;
    }
    assert_eq!(
        fixture.connection.acknowledge_close_notify(&wrong),
        Action::Fail(clazel_tls::spec::INTERNAL_ERROR)
    );
    assert_eq!(fixture.connection.mode(), Mode::Failed);
    Ok(())
}

#[test]
fn fragmented_ticket_is_discarded_but_coalesced_or_duplicate_messages_fail() -> Result<(), String> {
    let mut fixture = ready_fixture()?;
    let (_, server_secret) = application_secrets(&fixture);
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;
    let ticket = handshake(4, &ticket_body(3600, Vec::new()));
    let split = ticket.len().saturating_div(2);
    let prefix = ticket.get(..split).ok_or("short ticket")?;
    let suffix = ticket.get(split..).ok_or("missing ticket suffix")?;
    let prefix_record = server
        .seal(22, prefix, 0)
        .map_err(|e| format!("ticket prefix seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&prefix_record),
        (prefix_record.len(), Action::None)
    );
    let suffix_record = server
        .seal(22, suffix, 0)
        .map_err(|e| format!("ticket suffix seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&suffix_record),
        (suffix_record.len(), Action::None)
    );

    let mut coalesced = ticket.clone();
    coalesced.extend_from_slice(&handshake(24, &[0]));
    let coalesced_record = server
        .seal(22, &coalesced, 0)
        .map_err(|e| format!("coalesced post-handshake seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&coalesced_record),
        (
            coalesced_record.len(),
            Action::Fail(clazel_tls::spec::UNEXPECTED_MESSAGE)
        )
    );
    assert_eq!(fixture.connection.mode(), Mode::Failed);

    let mut duplicate_fixture = ready_fixture()?;
    let (_, duplicate_server_secret) = application_secrets(&duplicate_fixture);
    let mut duplicate_server = Encryptor::new(
        &duplicate_fixture.crypto,
        &duplicate_fixture.factory,
        &duplicate_server_secret,
    )
    .map_err(|e| format!("duplicate server epoch alert {e}"))?;
    let early_data = [0, 0, 0, 1];
    let duplicate_extensions = vec![
        Extension {
            etype: 42,
            data: &early_data,
        },
        Extension {
            etype: 42,
            data: &early_data,
        },
    ];
    let duplicate_ticket = handshake(4, &ticket_body(3600, duplicate_extensions));
    let duplicate_record = duplicate_server
        .seal(22, &duplicate_ticket, 0)
        .map_err(|e| format!("duplicate ticket seal alert {e}"))?;
    assert_eq!(
        duplicate_fixture.connection.feed(&duplicate_record),
        (
            duplicate_record.len(),
            Action::Fail(clazel_tls::spec::ILLEGAL_PARAMETER)
        )
    );
    Ok(())
}

#[test]
fn empty_ticket_is_decode_error_and_unknown_ticket_extensions_are_discarded() -> Result<(), String>
{
    let mut fixture = ready_fixture()?;
    let (_, server_secret) = application_secrets(&fixture);
    let mut server = Encryptor::new(&fixture.crypto, &fixture.factory, &server_secret)
        .map_err(|e| format!("server epoch alert {e}"))?;

    let empty_ticket_body = [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0];
    let malformed = handshake(4, &empty_ticket_body);
    let malformed_record = server
        .seal(22, &malformed, 0)
        .map_err(|e| format!("malformed ticket seal alert {e}"))?;
    assert_eq!(
        fixture.connection.feed(&malformed_record),
        (
            malformed_record.len(),
            Action::Fail(clazel_tls::spec::DECODE_ERROR)
        )
    );

    let mut unknown_fixture = ready_fixture()?;
    let (_, unknown_server_secret) = application_secrets(&unknown_fixture);
    let mut unknown_server = Encryptor::new(
        &unknown_fixture.crypto,
        &unknown_fixture.factory,
        &unknown_server_secret,
    )
    .map_err(|e| format!("unknown-extension server epoch alert {e}"))?;
    let unknown_extension = Extension {
        etype: 0xFE42,
        data: b"opaque",
    };
    let unknown_ticket = handshake(4, &ticket_body(3600, vec![unknown_extension]));
    let unknown_record = unknown_server
        .seal(22, &unknown_ticket, 0)
        .map_err(|e| format!("unknown-extension ticket seal alert {e}"))?;
    assert_eq!(
        unknown_fixture.connection.feed(&unknown_record),
        (unknown_record.len(), Action::None)
    );
    Ok(())
}
