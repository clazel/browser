//! Adversarial tests for separate protected TLS traffic-key epochs.
//!
//! The cipher below is a deterministic protocol test double, not ChaCha20-Poly1305
//! or a cryptographic implementation. It records exact key/nonce/AD inputs.

use std::cell::RefCell;
use std::rc::Rc;

use clazel_tls::record::Aead;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::spec::{
    BAD_RECORD_MAC, DECODE_ERROR, INTERNAL_ERROR, RECORD_OVERFLOW, UNEXPECTED_MESSAGE,
};
use clazel_tls::traffic::exec::{Decryptor, Encryptor, Read};
use clazel_tls::traffic::provider::{Factory, KeyedAead};
use sha2::{Digest, Sha256};

const SECRET: [u8; 32] = [0x31; 32];

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
    let mut info = Vec::new();
    info.extend_from_slice(&length.to_be_bytes());
    let full_label_length = 6usize.saturating_add(label.len());
    info.push(u8::try_from(full_label_length).unwrap_or(u8::MAX));
    info.extend_from_slice(b"tls13 ");
    info.extend_from_slice(label);
    info.push(0); // empty HKDF-Label context
    crypto.expand(secret, &info, length)
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
