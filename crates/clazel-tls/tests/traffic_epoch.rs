//! Adversarial tests for separate protected TLS traffic-key epochs.
//!
//! The cipher below is a deterministic protocol test double, not ChaCha20-Poly1305
//! or a cryptographic implementation. It records exact key/nonce/AD inputs.

use std::cell::RefCell;
use std::rc::Rc;

use clazel_tls::auth::exec::Input;
use clazel_tls::auth::spec::Phase as AuthPhase;
use clazel_tls::encode;
use clazel_tls::hello::client::{Config, Hello, Outcome};
use clazel_tls::hello::key_exchange::KeyExchange;
use clazel_tls::reassemble::{Event, Reassembler};
use clazel_tls::record::Aead;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::spec::{
    BAD_RECORD_MAC, DECODE_ERROR, INTERNAL_ERROR, RECORD_OVERFLOW, UNEXPECTED_MESSAGE,
};
use clazel_tls::traffic::exec::{Decryptor, Encryptor, Read};
use clazel_tls::traffic::provider::{Factory, KeyedAead};
use clazel_tls::types::Extension;
use sha2::{Digest, Sha256};

const SECRET: [u8; 32] = [0x31; 32];
const HOST: &[u8] = b"traffic.example.test";
const PRIVATE: [u8; 32] = [0x41; 32];
const PUBLIC: [u8; 32] = [0x52; 32];
const PEER: [u8; 32] = [0x63; 32];
const SHARED: [u8; 32] = [0x74; 32];

/// Input-sensitive but deliberately non-cryptographic SHA-256-based test double.
struct TestCrypto;

impl Crypto for TestCrypto {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let mut input = b"traffic extract".to_vec();
        input.extend_from_slice(salt);
        input.extend_from_slice(ikm);
        Sha256::digest(input).to_vec()
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut input = b"traffic expand".to_vec();
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
        let mut input = b"traffic hmac".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(message);
        Sha256::digest(input).to_vec()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AeadCall {
    key: Vec<u8>,
    nonce: Vec<u8>,
    ad: Vec<u8>,
}

#[derive(Default)]
struct Trace {
    made_keys: Vec<Vec<u8>>,
    seals: Vec<AeadCall>,
    opens: Vec<AeadCall>,
}

#[derive(Clone)]
struct ToyFactory {
    trace: Rc<RefCell<Trace>>,
}

impl ToyFactory {
    fn new() -> Self {
        Self {
            trace: Rc::new(RefCell::new(Trace::default())),
        }
    }
}

struct ToyCipher {
    key: Vec<u8>,
    trace: Rc<RefCell<Trace>>,
}

impl Factory for ToyFactory {
    type Cipher = ToyCipher;

    fn make(&self, key: &[u8]) -> Self::Cipher {
        self.trace.borrow_mut().made_keys.push(key.to_vec());
        ToyCipher {
            key: key.to_vec(),
            trace: Rc::clone(&self.trace),
        }
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
        self.trace.borrow_mut().seals.push(AeadCall {
            key: self.key.clone(),
            nonce: nonce.to_vec(),
            ad: ad.to_vec(),
        });
        let mut ciphertext = plaintext.to_vec();
        let tag = toy_tag(&self.key, nonce, ad, &ciphertext);
        ciphertext.extend_from_slice(&tag);
        ciphertext
    }

    fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> Option<Vec<u8>> {
        self.trace.borrow_mut().opens.push(AeadCall {
            key: self.key.clone(),
            nonce: nonce.to_vec(),
            ad: ad.to_vec(),
        });
        if ciphertext.len() < 16 {
            return None;
        }
        let split = ciphertext.len().saturating_sub(16);
        let (plaintext, received_tag) = ciphertext.split_at(split);
        let expected_tag = toy_tag(&self.key, nonce, ad, plaintext);
        if received_tag != expected_tag {
            return None;
        }
        Some(plaintext.to_vec())
    }
}

impl KeyedAead for ToyCipher {}

fn toy_tag(key: &[u8], nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> [u8; 16] {
    let mut input = b"test-only toy tag".to_vec();
    input.extend_from_slice(key);
    input.extend_from_slice(nonce);
    input.extend_from_slice(ad);
    input.extend_from_slice(ciphertext);
    let digest = Sha256::digest(input);
    let mut tag = [0u8; 16];
    tag.copy_from_slice(digest.get(..16).unwrap_or(&[0; 16]));
    tag
}

fn reference_expand_label(
    crypto: &TestCrypto,
    secret: &[u8],
    label: &[u8],
    length: u16,
) -> Vec<u8> {
    reference_expand_label_context(crypto, secret, label, &[], length)
}

fn reference_expand_label_context(
    crypto: &TestCrypto,
    secret: &[u8],
    label: &[u8],
    context: &[u8],
    length: u16,
) -> Vec<u8> {
    let mut info = Vec::new();
    info.extend_from_slice(&length.to_be_bytes());
    let full_label_length = 6usize.saturating_add(label.len());
    info.push(u8::try_from(full_label_length).unwrap_or(u8::MAX));
    info.extend_from_slice(b"tls13 ");
    info.extend_from_slice(label);
    info.push(u8::try_from(context.len()).unwrap_or(u8::MAX));
    info.extend_from_slice(context);
    crypto.expand(secret, &info, length)
}

fn expected_handshake_secrets(
    crypto: &TestCrypto,
    transcript: &[u8],
    shared: &[u8],
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let zeros = [0; 32];
    let early = crypto.extract(&zeros, &zeros);
    let derived_early =
        reference_expand_label_context(crypto, &early, b"derived", &crypto.hash(&[]), 32);
    let handshake = crypto.extract(&derived_early, shared);
    let transcript_hash = crypto.hash(transcript);
    let client =
        reference_expand_label_context(crypto, &handshake, b"c hs traffic", &transcript_hash, 32);
    let server =
        reference_expand_label_context(crypto, &handshake, b"s hs traffic", &transcript_hash, 32);
    let derived_handshake =
        reference_expand_label_context(crypto, &handshake, b"derived", &crypto.hash(&[]), 32);
    let master = crypto.extract(&derived_handshake, &zeros);
    (client, server, master)
}

fn expected_key_iv(crypto: &TestCrypto) -> (Vec<u8>, Vec<u8>) {
    (
        reference_expand_label(crypto, &SECRET, b"key", 32),
        reference_expand_label(crypto, &SECRET, b"iv", 12),
    )
}

fn reference_nonce(iv: &[u8], sequence: u64) -> Vec<u8> {
    let mut nonce = iv.to_vec();
    let sequence_bytes = sequence.to_be_bytes();
    for (target, source) in nonce
        .iter_mut()
        .rev()
        .take(8)
        .zip(sequence_bytes.iter().rev())
    {
        *target ^= *source;
    }
    nonce
}

fn ccs_record() -> Vec<u8> {
    vec![20, 3, 3, 0, 1, 1]
}

fn record_with_inner(crypto: &TestCrypto, inner: &[u8]) -> Vec<u8> {
    let (key, iv) = expected_key_iv(crypto);
    let nonce = reference_nonce(&iv, 0);
    let encrypted_len = inner.len().saturating_add(16);
    let mut header = vec![23, 3, 3];
    header.extend_from_slice(
        &u16::try_from(encrypted_len)
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    let mut wire = header.clone();
    let mut encrypted = inner.to_vec();
    encrypted.extend_from_slice(&toy_tag(&key, &nonce, &header, inner));
    wire.extend_from_slice(&encrypted);
    wire
}

struct MockExchange {
    public_result: Vec<u8>,
    shared_result: Option<Vec<u8>>,
}

impl KeyExchange for MockExchange {
    fn public_key(&self, _private_key: &[u8]) -> Vec<u8> {
        self.public_result.clone()
    }

    fn shared_secret(&self, _private_key: &[u8], _peer_key: &[u8]) -> Option<Vec<u8>> {
        self.shared_result.clone()
    }
}

fn hello_config() -> Config {
    Config {
        host: HOST.to_vec(),
        now: 1_800_000_000,
        random: vec![0x11; 32],
        session_id: vec![0x12; 8],
        public_key: PUBLIC.to_vec(),
        send_sni: true,
    }
}

fn handshake_message(kind: u8, body: &[u8]) -> Vec<u8> {
    let mut message = Vec::new();
    encode::write_handshake(&mut message, kind, body);
    message
}

fn server_hello_body() -> Vec<u8> {
    let version = [3, 4];
    let mut key_data = vec![0, 29, 0, 32];
    key_data.extend_from_slice(&PEER);
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
    body.push(8);
    body.extend_from_slice(&[0x12; 8]);
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

fn hello_fixture(
    crypto: &TestCrypto,
) -> Result<(clazel_tls::hello::client::Established, Vec<u8>), String> {
    let (hello, client_hello) =
        Hello::start(hello_config()).map_err(|alert| format!("ClientHello start alert {alert}"))?;
    let server_body = server_hello_body();
    match hello
        .receive(crypto, &server_body)
        .map_err(|alert| format!("ServerHello alert {alert}"))?
    {
        Outcome::Established(value) => Ok((value, client_hello)),
        Outcome::Retry(_, _) => Err("unexpected HelloRetryRequest in fixture".to_owned()),
    }
}

#[test]
fn derives_key_and_iv_and_uses_nonce_sequence_and_header_ad() -> Result<(), String> {
    let crypto = TestCrypto;
    let factory = ToyFactory::new();
    let (key, iv) = expected_key_iv(&crypto);
    let mut sender = Encryptor::new(&crypto, &factory, &SECRET)
        .map_err(|alert| format!("sender construction alert {alert}"))?;
    assert_eq!(factory.trace.borrow().made_keys, vec![key.clone()]);
    assert_eq!(sender.next_sequence(), Some(0));

    let first = sender
        .seal(23, b"payload", 2)
        .map_err(|alert| format!("first seal alert {alert}"))?;
    let second = sender
        .seal(23, b"second", 0)
        .map_err(|alert| format!("second seal alert {alert}"))?;
    assert_eq!(sender.next_sequence(), Some(2));
    let calls = &factory.trace.borrow().seals;
    assert_eq!(calls.len(), 2);
    let first_call = calls.first().ok_or("missing first AEAD call")?;
    let second_call = calls.get(1).ok_or("missing second AEAD call")?;
    assert_eq!(first_call.key, key);
    assert_eq!(first_call.nonce, reference_nonce(&iv, 0));
    assert_eq!(first_call.ad, first.get(..5).unwrap_or(&[]));
    assert_eq!(second_call.nonce, reference_nonce(&iv, 1));
    assert_eq!(second_call.ad, second.get(..5).unwrap_or(&[]));
    assert_eq!(first_call.ad.first(), Some(&23));
    assert_eq!(first_call.ad.get(1..3), Some(&[3, 3][..]));

    let receiver_factory = ToyFactory::new();
    let mut receiver = Decryptor::new(&crypto, &receiver_factory, &SECRET)
        .map_err(|alert| format!("receiver construction alert {alert}"))?;
    assert_eq!(
        receiver_factory.trace.borrow().made_keys,
        vec![reference_expand_label(&crypto, &SECRET, b"key", 32)]
    );
    let mut joined = first.clone();
    joined.extend_from_slice(&second);
    let (first_type, first_content, consumed) = match receiver.open(&joined) {
        Read::Record(typ, content, consumed) => (typ, content, consumed),
        other => return Err(format!("first record not returned: {other:?}")),
    };
    assert_eq!(
        (first_type, first_content.as_slice()),
        (23, b"payload".as_slice())
    );
    assert_eq!(consumed, first.len());
    assert_eq!(receiver.next_sequence(), Some(1));
    assert_eq!(
        receiver.open(joined.get(consumed..).unwrap_or(&[])),
        Read::Record(23, b"second".to_vec(), second.len())
    );
    assert_eq!(receiver.next_sequence(), Some(2));
    let opens = &receiver_factory.trace.borrow().opens;
    assert_eq!(opens.len(), 2);
    let first_open = opens.first().ok_or("missing first AEAD open")?;
    let second_open = opens.get(1).ok_or("missing second AEAD open")?;
    assert_eq!(first_open.nonce, reference_nonce(&iv, 0));
    assert_eq!(first_open.ad, first.get(..5).unwrap_or(&[]));
    assert_eq!(second_open.nonce, reference_nonce(&iv, 1));
    Ok(())
}

#[test]
fn incomplete_input_does_not_call_aead_or_advance_counter() -> Result<(), String> {
    let crypto = TestCrypto;
    let sender_factory = ToyFactory::new();
    let mut sender = Encryptor::new(&crypto, &sender_factory, &SECRET)
        .map_err(|alert| format!("sender construction alert {alert}"))?;
    let wire = sender
        .seal(23, b"fragment", 0)
        .map_err(|alert| format!("seal alert {alert}"))?;

    let factory = ToyFactory::new();
    let mut receiver = Decryptor::new(&crypto, &factory, &SECRET)
        .map_err(|alert| format!("receiver construction alert {alert}"))?;
    assert_eq!(receiver.open(&[]), Read::NeedMore);
    assert_eq!(receiver.open(wire.get(..4).unwrap_or(&[])), Read::NeedMore);
    let short_body_end = wire.len().saturating_sub(1);
    assert_eq!(
        receiver.open(wire.get(..short_body_end).unwrap_or(&[])),
        Read::NeedMore
    );
    assert_eq!(receiver.next_sequence(), Some(0));
    assert!(factory.trace.borrow().opens.is_empty());
    assert_eq!(
        receiver.open(&wire),
        Read::Record(23, b"fragment".to_vec(), wire.len())
    );
    assert_eq!(receiver.next_sequence(), Some(1));
    assert_eq!(factory.trace.borrow().opens.len(), 1);
    Ok(())
}

#[test]
fn invalid_installs_sends_and_padding_fail_without_crypto_calls() -> Result<(), String> {
    let crypto = TestCrypto;
    let factory = ToyFactory::new();
    assert!(matches!(
        Encryptor::new(&crypto, &factory, &[1; 31]),
        Err(INTERNAL_ERROR)
    ));
    assert!(matches!(
        Decryptor::new(&crypto, &factory, &[1; 31]),
        Err(INTERNAL_ERROR)
    ));
    assert!(factory.trace.borrow().made_keys.is_empty());

    for (typ, content, padding, alert) in [
        (24, &b"x"[..], 0, UNEXPECTED_MESSAGE),
        (22, &b""[..], 0, UNEXPECTED_MESSAGE),
        (21, &b""[..], 0, UNEXPECTED_MESSAGE),
        (23, &[0x78; 16384][..], 240, RECORD_OVERFLOW),
    ] {
        let local = ToyFactory::new();
        let mut sender = Encryptor::new(&crypto, &local, &SECRET)
            .map_err(|error| format!("sender construction alert {error}"))?;
        assert!(matches!(sender.seal(typ, content, padding), Err(value) if value == alert));
        assert_eq!(sender.next_sequence(), Some(0));
        assert!(local.trace.borrow().seals.is_empty());
        assert!(matches!(sender.seal(23, b"later", 0), Err(INTERNAL_ERROR)));
        assert_eq!(sender.next_sequence(), Some(0));
        assert!(local.trace.borrow().seals.is_empty());
    }

    let local = ToyFactory::new();
    let mut sender = Encryptor::new(&crypto, &local, &SECRET)
        .map_err(|alert| format!("sender construction alert {alert}"))?;
    assert!(sender.seal(23, &vec![0x5a; 16385], 0).is_err());
    assert!(local.trace.borrow().seals.is_empty());
    let maximum_factory = ToyFactory::new();
    let mut maximum_sender = Encryptor::new(&crypto, &maximum_factory, &SECRET)
        .map_err(|alert| format!("maximum sender construction alert {alert}"))?;
    let maximum_padding = 16640usize.saturating_sub(16384 + 1 + 16);
    let output = maximum_sender
        .seal(23, &vec![0x5a; 16384], maximum_padding)
        .map_err(|alert| format!("maximum valid record rejected: {alert}"))?;
    assert_eq!(output.len(), 16645);
    assert_eq!(maximum_factory.trace.borrow().seals.len(), 1);
    Ok(())
}

#[test]
fn tamper_reorder_ccs_and_malformed_inner_plaintext_are_terminal() -> Result<(), String> {
    let crypto = TestCrypto;
    let sender_factory = ToyFactory::new();
    let mut sender = Encryptor::new(&crypto, &sender_factory, &SECRET)
        .map_err(|alert| format!("sender construction alert {alert}"))?;
    let first = sender
        .seal(23, b"first", 0)
        .map_err(|alert| format!("first seal alert {alert}"))?;
    let second = sender
        .seal(23, b"second", 0)
        .map_err(|alert| format!("second seal alert {alert}"))?;

    let tamper_factory = ToyFactory::new();
    let mut tamper_receiver = Decryptor::new(&crypto, &tamper_factory, &SECRET)
        .map_err(|alert| format!("decryptor construction alert {alert}"))?;
    let mut corrupt = first.clone();
    if let Some(last) = corrupt.last_mut() {
        *last ^= 1;
    }
    assert_eq!(tamper_receiver.open(&corrupt), Read::Fail(BAD_RECORD_MAC));
    assert_eq!(tamper_receiver.open(&first), Read::Fail(INTERNAL_ERROR));
    assert_eq!(tamper_receiver.next_sequence(), Some(0));
    assert_eq!(tamper_factory.trace.borrow().opens.len(), 1);

    let reorder_factory = ToyFactory::new();
    let mut reorder_receiver = Decryptor::new(&crypto, &reorder_factory, &SECRET)
        .map_err(|alert| format!("decryptor construction alert {alert}"))?;
    assert_eq!(reorder_receiver.open(&second), Read::Fail(BAD_RECORD_MAC));
    assert_eq!(reorder_receiver.open(&first), Read::Fail(INTERNAL_ERROR));
    assert_eq!(reorder_factory.trace.borrow().opens.len(), 1);

    let ccs_factory = ToyFactory::new();
    let mut ccs_receiver = Decryptor::new(&crypto, &ccs_factory, &SECRET)
        .map_err(|alert| format!("decryptor construction alert {alert}"))?;
    assert_eq!(
        ccs_receiver.open(&ccs_record()),
        Read::Fail(UNEXPECTED_MESSAGE)
    );
    assert!(ccs_factory.trace.borrow().opens.is_empty());
    assert_eq!(ccs_receiver.open(&first), Read::Fail(INTERNAL_ERROR));

    let framing_factory = ToyFactory::new();
    let mut framing_receiver = Decryptor::new(&crypto, &framing_factory, &SECRET)
        .map_err(|alert| format!("decryptor construction alert {alert}"))?;
    let mut bad_version = first.clone();
    if let Some(version_byte) = bad_version.get_mut(2) {
        *version_byte = 2;
    }
    assert_eq!(
        framing_receiver.open(&bad_version),
        Read::Fail(DECODE_ERROR)
    );
    assert_eq!(framing_factory.trace.borrow().opens.len(), 0);
    assert_eq!(framing_receiver.open(&first), Read::Fail(INTERNAL_ERROR));

    let overflow_factory = ToyFactory::new();
    let mut overflow_receiver = Decryptor::new(&crypto, &overflow_factory, &SECRET)
        .map_err(|alert| format!("decryptor construction alert {alert}"))?;
    assert_eq!(
        overflow_receiver.open(&[23, 3, 3, 0x41, 1]),
        Read::Fail(RECORD_OVERFLOW)
    );
    assert!(overflow_factory.trace.borrow().opens.is_empty());

    let malformed_factory = ToyFactory::new();
    let mut malformed_receiver = Decryptor::new(&crypto, &malformed_factory, &SECRET)
        .map_err(|alert| format!("decryptor construction alert {alert}"))?;
    let malformed = record_with_inner(&crypto, &[0, 0]);
    assert_eq!(
        malformed_receiver.open(&malformed),
        Read::Fail(UNEXPECTED_MESSAGE)
    );
    assert_eq!(malformed_receiver.open(&first), Read::Fail(INTERNAL_ERROR));
    assert_eq!(malformed_factory.trace.borrow().opens.len(), 1);
    Ok(())
}

#[test]
fn empty_application_content_is_valid() -> Result<(), String> {
    let crypto = TestCrypto;
    let factory = ToyFactory::new();
    let mut sender = Encryptor::new(&crypto, &factory, &SECRET)
        .map_err(|alert| format!("sender construction alert {alert}"))?;
    let wire = sender
        .seal(23, &[], 0)
        .map_err(|alert| format!("empty application record rejected: {alert}"))?;
    let receiver_factory = ToyFactory::new();
    let mut receiver = Decryptor::new(&crypto, &receiver_factory, &SECRET)
        .map_err(|alert| format!("receiver construction alert {alert}"))?;
    assert_eq!(
        receiver.open(&wire),
        Read::Record(23, Vec::new(), wire.len())
    );
    Ok(())
}

#[test]
fn hello_record_auth_handoff_installs_directional_keys_and_processes_ee() -> Result<(), String> {
    let crypto = TestCrypto;
    let exchange = MockExchange {
        public_result: PUBLIC.to_vec(),
        shared_result: Some(SHARED.to_vec()),
    };
    let (established, client_hello_flight) = hello_fixture(&crypto)?;
    let server_body = server_hello_body();
    let mut prefix = client_hello_flight;
    prefix.extend_from_slice(&handshake_message(2, &server_body));
    let (client_secret, server_secret, expected_master) =
        expected_handshake_secrets(&crypto, &prefix, &SHARED);

    let handoff_factory = ToyFactory::new();
    let handoff = established
        .into_record_auth(&crypto, &exchange, &handoff_factory, &PRIVATE)
        .map_err(|alert| format!("record-auth handoff alert {alert}"))?;
    assert_eq!(
        handoff_factory.trace.borrow().made_keys,
        vec![
            reference_expand_label(&crypto, &client_secret, b"key", 32),
            reference_expand_label(&crypto, &server_secret, b"key", 32),
        ]
    );
    let (mut auth, mut sender, mut receiver, master) = handoff.into_parts();
    assert_eq!(master, expected_master);
    assert_eq!(auth.phase(), AuthPhase::EncryptedExtensions);
    assert_eq!(auth.messages(), prefix);
    assert_eq!(sender.next_sequence(), Some(0));
    assert_eq!(receiver.next_sequence(), Some(0));

    let mut ee_body = Vec::new();
    encode::write_encrypted_extensions(&mut ee_body, &[] as &[Extension<'_>]);
    let ee_message = handshake_message(8, &ee_body);
    let server_factory = ToyFactory::new();
    let mut server_sender = Encryptor::new(&crypto, &server_factory, &server_secret)
        .map_err(|alert| format!("server writer construction alert {alert}"))?;
    let server_wire = server_sender
        .seal(22, &ee_message, 0)
        .map_err(|alert| format!("server EncryptedExtensions seal alert {alert}"))?;
    let (content_type, plaintext, consumed) = match receiver.open(&server_wire) {
        Read::Record(typ, bytes, consumed) => (typ, bytes, consumed),
        other => return Err(format!("bundle receiver rejected EE record: {other:?}")),
    };
    assert_eq!(content_type, 22);
    assert_eq!(consumed, server_wire.len());
    assert_eq!(receiver.next_sequence(), Some(1));
    let mut reassembler = Reassembler::new();
    match reassembler.feed_record(content_type, &plaintext) {
        Ok(Event::Messages(messages)) => assert_eq!(messages, vec![ee_message]),
        other => return Err(format!("EE record did not reassemble: {other:?}")),
    }
    assert_eq!(
        auth.step(&crypto, &NoopVerifier, Input::Handshake(8, &ee_body)),
        clazel_tls::auth::exec::Action::None
    );
    assert_eq!(auth.phase(), AuthPhase::CertificateOrRequest);

    let client_finished = handshake_message(20, &[0x5a; 32]);
    let client_wire = sender
        .seal(22, &client_finished, 0)
        .map_err(|alert| format!("bundle sender seal alert {alert}"))?;
    assert_eq!(sender.next_sequence(), Some(1));
    let peer_factory = ToyFactory::new();
    let mut peer_receiver = Decryptor::new(&crypto, &peer_factory, &client_secret)
        .map_err(|alert| format!("peer reader construction alert {alert}"))?;
    assert_eq!(
        peer_factory.trace.borrow().made_keys,
        vec![reference_expand_label(&crypto, &client_secret, b"key", 32)]
    );
    assert_eq!(
        peer_receiver.open(&client_wire),
        Read::Record(22, client_finished, client_wire.len())
    );
    Ok(())
}

struct NoopVerifier;

impl clazel_tls::auth::verify::Verifier for NoopVerifier {
    fn chain(
        &self,
        _host: &[u8],
        _now: u64,
        _certificate_body: &[u8],
    ) -> Result<Vec<u8>, clazel_tls::auth::spec::CertificateError> {
        Err(clazel_tls::auth::spec::CertificateError::UnknownCa)
    }

    fn signature(&self, _key: &[u8], _scheme: u16, _input: &[u8], _signature: &[u8]) -> bool {
        false
    }

    fn finished_equal(&self, received: &[u8], expected: &[u8]) -> bool {
        received == expected
    }
}

#[test]
fn failed_key_exchange_never_installs_record_keys() -> Result<(), String> {
    let crypto = TestCrypto;
    let factory = ToyFactory::new();

    let (established, _) = hello_fixture(&crypto)?;
    let valid_exchange = MockExchange {
        public_result: PUBLIC.to_vec(),
        shared_result: Some(SHARED.to_vec()),
    };
    assert!(matches!(
        established.into_record_auth(&crypto, &valid_exchange, &factory, &[0x41; 31]),
        Err(INTERNAL_ERROR)
    ));
    assert!(factory.trace.borrow().made_keys.is_empty());

    let (established, _) = hello_fixture(&crypto)?;
    let mismatched_exchange = MockExchange {
        public_result: vec![0x99; 32],
        shared_result: Some(SHARED.to_vec()),
    };
    assert!(matches!(
        established.into_record_auth(&crypto, &mismatched_exchange, &factory, &PRIVATE),
        Err(INTERNAL_ERROR)
    ));
    assert!(factory.trace.borrow().made_keys.is_empty());

    let (established, _) = hello_fixture(&crypto)?;
    let rejected_exchange = MockExchange {
        public_result: PUBLIC.to_vec(),
        shared_result: None,
    };
    assert!(matches!(
        established.into_record_auth(&crypto, &rejected_exchange, &factory, &PRIVATE),
        Err(clazel_tls::spec::ILLEGAL_PARAMETER)
    ));
    assert!(factory.trace.borrow().made_keys.is_empty());
    Ok(())
}
