//! The post-handshake transducer (`connection::post_handshake_exec`) against an
//! independent model of the server: RFC 8446 §4.6 NewSessionTicket and
//! KeyUpdate, §5 records and sequence numbers, §6 alerts, §7.2 and §7.3 traffic
//! secret updates.
//!
//! The key schedule is the reference HKDF-SHA256 provider (RFC 5869, RFC 2104)
//! over RustCrypto SHA-256. The AEAD is a deterministic test double with a real
//! keystream and a real tag over key, nonce, additional data and ciphertext; it
//! is NOT ChaCha20-Poly1305 and not cryptography. The test builds the server's
//! records itself (nonce, additional data, inner plaintext) from the keys that
//! `schedule::exec` derives, so the transducer's record layer is checked against
//! an implementation that does not share its code. RFC 8448 supplies the handshake
//! messages (its records are AES-128-GCM and cannot be used).
//!
//! Nothing here positions a sequence counter near 2^64 - 1 (no API allows it);
//! the wrap rule is stated and witnessed in the Verus spec, not run.

mod post_handshake_vectors;

use clazel_tls::connection::post_handshake_exec::{Action, Input, PostHandshake};
use clazel_tls::record::Aead;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::schedule::exec::{update_secret, write_iv, write_key};
use clazel_tls::spec::{
    BAD_RECORD_MAC, CLOSE_NOTIFY, DECODE_ERROR, ILLEGAL_PARAMETER, INTERNAL_ERROR, RECORD_OVERFLOW,
    UNEXPECTED_MESSAGE,
};
use clazel_tls::traffic::provider::{Factory, KeyedAead};
use sha2::{Digest, Sha256};

const CLIENT_SECRET_0: [u8; 32] = [0x11; 32];
const SERVER_SECRET_0: [u8; 32] = [0x22; 32];

const CT_ALERT: u8 = 21;
const CT_HANDSHAKE: u8 = 22;
const CT_APPLICATION_DATA: u8 = 23;

/// RFC 5869 / RFC 2104 reference provider (as in `conformance_key_schedule.rs`).
#[derive(Clone)]
struct Reference;

impl Crypto for Reference {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        self.hmac(salt, ikm)
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut out = Vec::new();
        let mut previous = Vec::new();
        for counter in 1..=u8::MAX {
            if out.len() >= usize::from(length) {
                break;
            }
            let mut message = previous;
            message.extend_from_slice(info);
            message.push(counter);
            previous = self.hmac(secret, &message);
            out.extend_from_slice(&previous);
        }
        out.truncate(usize::from(length));
        out
    }

    fn hmac(&self, key: &[u8], message: &[u8]) -> Vec<u8> {
        let mut padded = if key.len() > 64 {
            self.hash(key)
        } else {
            key.to_vec()
        };
        padded.resize(64, 0);
        let inner_pad: Vec<u8> = padded.iter().map(|b| b ^ 0x36).collect();
        let outer_pad: Vec<u8> = padded.iter().map(|b| b ^ 0x5c).collect();
        let mut inner = Sha256::new();
        inner.update(inner_pad);
        inner.update(message);
        let mut outer = Sha256::new();
        outer.update(outer_pad);
        outer.update(inner.finalize());
        outer.finalize().to_vec()
    }
}

/// Deterministic test double: XOR with a SHA-256 keystream, then a 16-byte tag.
fn keystream(key: &[u8], nonce: &[u8], length: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut block: u32 = 0;
    while out.len() < length {
        let mut input = b"test-only keystream".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(nonce);
        input.extend_from_slice(&block.to_be_bytes());
        out.extend_from_slice(&Sha256::digest(input));
        block = block.saturating_add(1);
    }
    out.truncate(length);
    out
}

fn tag(key: &[u8], nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> Vec<u8> {
    let mut input = b"test-only tag".to_vec();
    input.extend_from_slice(key);
    input.extend_from_slice(nonce);
    input.extend_from_slice(ad);
    input.extend_from_slice(ciphertext);
    Sha256::digest(input).iter().take(16).copied().collect()
}

fn aead_seal(key: &[u8], nonce: &[u8], ad: &[u8], plaintext: &[u8]) -> Vec<u8> {
    let stream = keystream(key, nonce, plaintext.len());
    let mut out: Vec<u8> = plaintext.iter().zip(stream).map(|(p, k)| p ^ k).collect();
    let t = tag(key, nonce, ad, &out);
    out.extend_from_slice(&t);
    out
}

fn aead_open(key: &[u8], nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> Option<Vec<u8>> {
    let split = ciphertext.len().checked_sub(16)?;
    let (body, received) = ciphertext.split_at(split);
    if received != tag(key, nonce, ad, body).as_slice() {
        return None;
    }
    let stream = keystream(key, nonce, body.len());
    Some(body.iter().zip(stream).map(|(c, k)| c ^ k).collect())
}

#[derive(Clone)]
struct ToyFactory;

struct ToyCipher {
    key: Vec<u8>,
}

impl Factory for ToyFactory {
    type Cipher = ToyCipher;

    fn make(&self, key: &[u8]) -> Self::Cipher {
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
        aead_seal(&self.key, nonce, ad, plaintext)
    }

    fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> Option<Vec<u8>> {
        aead_open(&self.key, nonce, ad, ciphertext)
    }
}

impl KeyedAead for ToyCipher {}

fn hex(s: &str) -> Vec<u8> {
    s.split_whitespace()
        .map(|b| u8::from_str_radix(b, 16).unwrap_or(0))
        .collect()
}

/// RFC 8446 §5.3: the nonce is the IV XOR the 64-bit sequence number, left-padded.
fn nonce(iv: &[u8], seq: u64) -> Vec<u8> {
    let mut n = iv.to_vec();
    let bytes = seq.to_be_bytes();
    let offset = n.len().saturating_sub(8);
    for (slot, b) in n.iter_mut().skip(offset).zip(bytes) {
        *slot ^= b;
    }
    n
}

/// RFC 8446 §5.2: one TLSCiphertext with `pad` zero bytes of padding.
fn protect(secret: &[u8], seq: u64, typ: u8, content: &[u8], pad: usize) -> Vec<u8> {
    let key = write_key(&Reference, secret);
    let iv = write_iv(&Reference, secret);
    let mut inner = content.to_vec();
    inner.push(typ);
    inner.resize(inner.len().saturating_add(pad), 0);
    let length = u16::try_from(inner.len().saturating_add(16)).unwrap_or(u16::MAX);
    let mut ad = vec![CT_APPLICATION_DATA, 3, 3];
    ad.extend_from_slice(&length.to_be_bytes());
    let mut record = ad.clone();
    record.extend_from_slice(&aead_seal(&key, &nonce(&iv, seq), &ad, &inner));
    record
}

/// Open a TLSCiphertext and drop the padding; `None` if it does not authenticate.
fn unprotect(secret: &[u8], seq: u64, record: &[u8]) -> Option<(u8, Vec<u8>)> {
    let key = write_key(&Reference, secret);
    let iv = write_iv(&Reference, secret);
    let (ad, body) = record.split_at(5);
    let mut inner = aead_open(&key, &nonce(&iv, seq), ad, body)?;
    while inner.last() == Some(&0) {
        inner.pop();
    }
    let typ = inner.pop()?;
    Some((typ, inner))
}

fn key_update_message(request: u8) -> Vec<u8> {
    vec![24, 0, 0, 1, request]
}

/// A client under test and the server's model of both directions.
struct Harness {
    client: PostHandshake<Reference, ToyFactory>,
    server_secret: Vec<u8>,
    server_seq: u64,
    client_secret: Vec<u8>,
    client_seq: u64,
}

impl Harness {
    fn new() -> Result<Self, String> {
        let client = PostHandshake::new(Reference, ToyFactory, &CLIENT_SECRET_0, &SERVER_SECRET_0)
            .map_err(|a| format!("new failed with alert {a}"))?;
        Ok(Self {
            client,
            server_secret: SERVER_SECRET_0.to_vec(),
            server_seq: 0,
            client_secret: CLIENT_SECRET_0.to_vec(),
            client_seq: 0,
        })
    }

    /// The server sends a record under its current keys.
    fn server_record(&mut self, typ: u8, content: &[u8]) -> Vec<u8> {
        let record = protect(&self.server_secret, self.server_seq, typ, content, 0);
        self.server_seq = self.server_seq.saturating_add(1);
        record
    }

    /// The server updates its own write keys (after sending a KeyUpdate).
    fn server_rotates(&mut self) {
        self.server_secret = update_secret(&Reference, &self.server_secret);
        self.server_seq = 0;
    }

    /// The server reads one record the client sent, under the client's keys it knows.
    fn server_reads(&mut self, record: &[u8]) -> Option<(u8, Vec<u8>)> {
        let opened = unprotect(&self.client_secret, self.client_seq, record);
        if opened.is_some() {
            self.client_seq = self.client_seq.saturating_add(1);
        }
        opened
    }

    /// The server learns the client updated its write keys.
    fn client_rotated(&mut self) {
        self.client_secret = update_secret(&Reference, &self.client_secret);
        self.client_seq = 0;
    }

    /// Feed bytes record by record, as a transport would; collect the actions.
    fn feed(&mut self, bytes: &[u8]) -> Vec<Action> {
        let mut all = Vec::new();
        let mut rest = bytes;
        while !rest.is_empty() {
            let (consumed, actions) = self.client.step(Input::Bytes(rest));
            all.extend(actions);
            if consumed == 0 {
                break;
            }
            rest = rest.get(consumed..).unwrap_or(&[]);
        }
        all
    }
}

fn sends(actions: &[Action]) -> Vec<&Vec<u8>> {
    actions
        .iter()
        .filter_map(|a| {
            if let Action::Send(w) = a {
                Some(w)
            } else {
                None
            }
        })
        .collect()
}

fn delivered(actions: &[Action]) -> Vec<u8> {
    actions
        .iter()
        .filter_map(|a| {
            if let Action::Deliver(d) = a {
                Some(d.clone())
            } else {
                None
            }
        })
        .flatten()
        .collect()
}

#[test]
fn application_data_is_delivered_in_order_across_coalescing_and_fragmentation() -> Result<(), String>
{
    let mut h = Harness::new()?;
    let first = h.server_record(CT_APPLICATION_DATA, b"hello ");
    let second = protect(
        &h.server_secret,
        h.server_seq,
        CT_APPLICATION_DATA,
        b"world",
        40,
    );
    h.server_seq = h.server_seq.saturating_add(1);
    let mut joined = first.clone();
    joined.extend_from_slice(&second);
    // Coalesced: step consumes exactly one record each time.
    let (consumed, actions) = h.client.step(Input::Bytes(&joined));
    assert_eq!(consumed, first.len());
    assert_eq!(actions, vec![Action::Deliver(b"hello ".to_vec())]);
    let rest = joined.get(consumed..).ok_or("short")?;
    let (consumed, actions) = h.client.step(Input::Bytes(rest));
    assert_eq!(consumed, second.len());
    assert_eq!(actions, vec![Action::Deliver(b"world".to_vec())]);
    // Fragmented: every proper prefix of a record is "need more": nothing consumed.
    let third = h.server_record(CT_APPLICATION_DATA, b"!");
    for cut in 0..third.len() {
        let prefix = third.get(..cut).ok_or("short")?;
        let (consumed, actions) = h.client.step(Input::Bytes(prefix));
        assert_eq!((consumed, actions), (0, vec![]), "prefix of {cut} bytes");
    }
    let (consumed, actions) = h.client.step(Input::Bytes(&third));
    assert_eq!(
        (consumed, actions),
        (third.len(), vec![Action::Deliver(b"!".to_vec())])
    );
    Ok(())
}

#[test]
fn empty_application_record_delivers_nothing() -> Result<(), String> {
    let mut h = Harness::new()?;
    let record = h.server_record(CT_APPLICATION_DATA, b"");
    let (consumed, actions) = h.client.step(Input::Bytes(&record));
    assert_eq!((consumed, actions), (record.len(), vec![]));
    assert!(h.client.is_open());
    Ok(())
}

#[test]
fn new_session_ticket_is_parsed_then_ignored() -> Result<(), String> {
    let mut h = Harness::new()?;
    let ticket = hex(post_handshake_vectors::NEW_SESSION_TICKET);
    let record = h.server_record(CT_HANDSHAKE, &ticket);
    let (consumed, actions) = h.client.step(Input::Bytes(&record));
    assert_eq!((consumed, actions), (record.len(), vec![]));
    // Two tickets in one record, then data: still open, data still delivered.
    let mut two = ticket.clone();
    two.extend_from_slice(&ticket);
    let record = h.server_record(CT_HANDSHAKE, &two);
    assert_eq!(h.feed(&record), vec![]);
    let data = h.server_record(CT_APPLICATION_DATA, b"after tickets");
    assert_eq!(
        h.feed(&data),
        vec![Action::Deliver(b"after tickets".to_vec())]
    );
    // A ticket fragmented over two records is reassembled, then ignored.
    let (a, b) = ticket.split_at(50);
    let r1 = h.server_record(CT_HANDSHAKE, a);
    let r2 = h.server_record(CT_HANDSHAKE, b);
    assert_eq!(h.feed(&r1), vec![]);
    assert_eq!(h.feed(&r2), vec![]);
    assert!(h.client.is_open());
    Ok(())
}

#[test]
fn malformed_new_session_ticket_is_a_decode_error() -> Result<(), String> {
    let mut h = Harness::new()?;
    // Type 4 with a one-byte body: not a NewSessionTicket.
    let record = h.server_record(CT_HANDSHAKE, &[4, 0, 0, 1, 0]);
    let actions = h.feed(&record);
    assert_eq!(actions.last(), Some(&Action::Fail(DECODE_ERROR)));
    check_fatal_alert(&mut h, &actions, DECODE_ERROR)
}

/// The failure sent a protected fatal alert the server can read, then `Fail`.
fn check_fatal_alert(h: &mut Harness, actions: &[Action], alert: u8) -> Result<(), String> {
    assert_eq!(actions.last(), Some(&Action::Fail(alert)));
    let wires = sends(actions);
    assert_eq!(wires.len(), 1, "one alert record");
    let record = wires.first().ok_or("no alert")?;
    assert_eq!(h.server_reads(record), Some((CT_ALERT, vec![2, alert])));
    assert!(!h.client.is_open());
    Ok(())
}

#[test]
fn key_update_not_requested_moves_the_read_keys_only() -> Result<(), String> {
    let mut h = Harness::new()?;
    let before = h.server_record(CT_APPLICATION_DATA, b"one");
    assert_eq!(h.feed(&before), vec![Action::Deliver(b"one".to_vec())]);
    let update = h.server_record(CT_HANDSHAKE, &key_update_message(0));
    assert_eq!(h.feed(&update), vec![], "no reply to update_not_requested");
    h.server_rotates();
    // The next record is under the new keys at sequence number 0.
    assert_eq!(h.server_seq, 0);
    let after = h.server_record(CT_APPLICATION_DATA, b"two");
    assert_eq!(h.feed(&after), vec![Action::Deliver(b"two".to_vec())]);
    // The client's write keys did not move: its next record is at sequence 1 of the first epoch.
    let sent = h.client.send_application(b"reply");
    let wire = sends(&sent)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no send")?;
    assert_eq!(
        h.server_reads(&wire),
        Some((CT_APPLICATION_DATA, b"reply".to_vec()))
    );
    assert_eq!(h.client_seq, 1);
    Ok(())
}

#[test]
fn old_read_keys_do_not_open_records_after_a_key_update() -> Result<(), String> {
    let mut h = Harness::new()?;
    let update = h.server_record(CT_HANDSHAKE, &key_update_message(0));
    assert_eq!(h.feed(&update), vec![]);
    // A record under the OLD keys (sequence 1 of the old epoch) must be refused.
    let stale = h.server_record(CT_APPLICATION_DATA, b"stale");
    let actions = h.feed(&stale);
    check_fatal_alert(&mut h, &actions, BAD_RECORD_MAC)
}

#[test]
fn key_update_requested_is_answered_under_the_old_keys_then_the_write_keys_move()
-> Result<(), String> {
    let mut h = Harness::new()?;
    // Spend some client sequence numbers first so a reset is visible.
    for i in 0..3u8 {
        let sent = h.client.send_application(&[i]);
        let wire = sends(&sent)
            .first()
            .map(|w| (*w).clone())
            .ok_or("no send")?;
        assert_eq!(h.server_reads(&wire), Some((CT_APPLICATION_DATA, vec![i])));
    }
    assert_eq!(h.client_seq, 3);
    let update = h.server_record(CT_HANDSHAKE, &key_update_message(1));
    let actions = h.feed(&update);
    assert_eq!(actions.len(), 1);
    let reply = sends(&actions)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no reply")?;
    // The reply is KeyUpdate(update_not_requested) under the OLD client keys, sequence 3.
    assert_eq!(
        h.server_reads(&reply),
        Some((CT_HANDSHAKE, key_update_message(0)))
    );
    h.client_rotated();
    // The next client record is under the new keys at sequence 0.
    let sent = h.client.send_application(b"fresh");
    let wire = sends(&sent)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no send")?;
    assert_eq!(
        h.server_reads(&wire),
        Some((CT_APPLICATION_DATA, b"fresh".to_vec()))
    );
    assert_eq!(h.client_seq, 1);
    // The read side moved too, independently.
    h.server_rotates();
    let data = h.server_record(CT_APPLICATION_DATA, b"server fresh");
    assert_eq!(
        h.feed(&data),
        vec![Action::Deliver(b"server fresh".to_vec())]
    );
    Ok(())
}

#[test]
fn client_initiated_key_update_with_and_without_a_request() -> Result<(), String> {
    for (request_peer, byte) in [(false, 0u8), (true, 1u8)] {
        let mut h = Harness::new()?;
        let sent = h.client.update_keys(request_peer);
        assert_eq!(sent.len(), 1);
        let wire = sends(&sent)
            .first()
            .map(|w| (*w).clone())
            .ok_or("no send")?;
        assert_eq!(
            h.server_reads(&wire),
            Some((CT_HANDSHAKE, key_update_message(byte)))
        );
        h.client_rotated();
        let sent = h.client.send_application(b"x");
        let wire = sends(&sent)
            .first()
            .map(|w| (*w).clone())
            .ok_or("no send")?;
        assert_eq!(
            h.server_reads(&wire),
            Some((CT_APPLICATION_DATA, b"x".to_vec()))
        );
        assert_eq!(h.client_seq, 1, "write sequence number reset by the update");
        // The read keys did not move.
        let data = h.server_record(CT_APPLICATION_DATA, b"still old read keys");
        assert_eq!(
            h.feed(&data),
            vec![Action::Deliver(b"still old read keys".to_vec())]
        );
    }
    Ok(())
}

#[test]
fn several_key_updates_in_a_row() -> Result<(), String> {
    let mut h = Harness::new()?;
    for round in 0..4u8 {
        let update = h.server_record(CT_HANDSHAKE, &key_update_message(round % 2));
        let actions = h.feed(&update);
        if round % 2 == 1 {
            let reply = sends(&actions)
                .first()
                .map(|w| (*w).clone())
                .ok_or("no reply")?;
            assert_eq!(
                h.server_reads(&reply),
                Some((CT_HANDSHAKE, key_update_message(0)))
            );
            h.client_rotated();
        } else {
            assert_eq!(actions, vec![]);
        }
        h.server_rotates();
        let data = h.server_record(CT_APPLICATION_DATA, &[round]);
        assert_eq!(h.feed(&data), vec![Action::Deliver(vec![round])]);
    }
    Ok(())
}

#[test]
fn invalid_request_update_is_illegal_parameter() -> Result<(), String> {
    for bad in [2u8, 3, 255] {
        let mut h = Harness::new()?;
        let record = h.server_record(CT_HANDSHAKE, &key_update_message(bad));
        let actions = h.feed(&record);
        check_fatal_alert(&mut h, &actions, ILLEGAL_PARAMETER)?;
    }
    Ok(())
}

#[test]
fn key_update_must_end_its_record_and_leave_no_partial_message() -> Result<(), String> {
    let ticket = hex(post_handshake_vectors::NEW_SESSION_TICKET);
    // A KeyUpdate followed by a ticket in the same record: messages after a key change.
    let mut h = Harness::new()?;
    let mut body = key_update_message(0);
    body.extend_from_slice(&ticket);
    let record = h.server_record(CT_HANDSHAKE, &body);
    let actions = h.feed(&record);
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    // A KeyUpdate followed by the start of another message: it would span the key change.
    let mut h = Harness::new()?;
    let mut body = key_update_message(0);
    body.extend_from_slice(&[4, 0]);
    let record = h.server_record(CT_HANDSHAKE, &body);
    let actions = h.feed(&record);
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    // A KeyUpdate fragmented over two records is reassembled; it then ends a record at a boundary.
    let mut h = Harness::new()?;
    let first = h.server_record(CT_HANDSHAKE, &[24, 0]);
    assert_eq!(h.feed(&first), vec![]);
    let second = h.server_record(CT_HANDSHAKE, &[0, 1, 0]);
    assert_eq!(h.feed(&second), vec![]);
    h.server_rotates();
    let data = h.server_record(CT_APPLICATION_DATA, b"new keys");
    assert_eq!(h.feed(&data), vec![Action::Deliver(b"new keys".to_vec())]);
    // A fragmented ticket left unfinished, then KeyUpdate bytes: they are read as more of the
    // ticket, so nothing rotates, and a following data record interleaves.
    let mut h = Harness::new()?;
    let first = h.server_record(CT_HANDSHAKE, ticket.get(..10).ok_or("short")?);
    assert_eq!(h.feed(&first), vec![]);
    let record = h.server_record(CT_HANDSHAKE, &key_update_message(0));
    assert_eq!(h.feed(&record), vec![]);
    let data = h.server_record(CT_APPLICATION_DATA, b"x");
    let actions = h.feed(&data);
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    Ok(())
}

#[test]
fn other_handshake_messages_after_the_handshake_are_unexpected_message() -> Result<(), String> {
    let kinds = [
        ("ClientHello", post_handshake_vectors::CLIENT_HELLO),
        ("ServerHello", post_handshake_vectors::SERVER_HELLO),
        (
            "EncryptedExtensions",
            post_handshake_vectors::ENCRYPTED_EXTENSIONS,
        ),
        ("Certificate", post_handshake_vectors::CERTIFICATE),
        ("Finished", post_handshake_vectors::SERVER_FINISHED),
        ("EndOfEarlyData", post_handshake_vectors::END_OF_EARLY_DATA),
    ];
    for (name, vector) in kinds {
        let mut h = Harness::new()?;
        let record = h.server_record(CT_HANDSHAKE, &hex(vector));
        let actions = h.feed(&record);
        assert_eq!(
            actions.last(),
            Some(&Action::Fail(UNEXPECTED_MESSAGE)),
            "{name}"
        );
        check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    }
    // The type decides before the body is read: a bogus body of a forbidden type, and an unknown type.
    for message in [
        vec![1u8, 0, 0, 0],
        vec![13, 0, 0, 1, 0],
        vec![99, 0, 0, 0],
        vec![0, 0, 0, 0],
    ] {
        let mut h = Harness::new()?;
        let record = h.server_record(CT_HANDSHAKE, &message);
        let actions = h.feed(&record);
        check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    }
    Ok(())
}

#[test]
fn change_cipher_spec_after_the_handshake_is_unexpected_message() -> Result<(), String> {
    // Unprotected, as middlebox compatibility mode sends it before the handshake ends.
    let mut h = Harness::new()?;
    let (consumed, actions) = h.client.step(Input::Bytes(&[20, 3, 3, 0, 1, 1]));
    assert_eq!(consumed, 6);
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    // Protected: inner content type 20.
    let mut h = Harness::new()?;
    let record = h.server_record(20, &[1]);
    let actions = h.feed(&record);
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)
}

#[test]
fn close_notify_is_answered_and_ends_delivery() -> Result<(), String> {
    let mut h = Harness::new()?;
    let data = h.server_record(CT_APPLICATION_DATA, b"last");
    let alert = h.server_record(CT_ALERT, &[1, CLOSE_NOTIFY]);
    let late = h.server_record(CT_APPLICATION_DATA, b"too late");
    assert_eq!(h.feed(&data), vec![Action::Deliver(b"last".to_vec())]);
    let (consumed, actions) = h.client.step(Input::Bytes(&alert));
    assert_eq!(consumed, alert.len());
    assert_eq!(actions.len(), 2);
    assert_eq!(actions.last(), Some(&Action::Close));
    let reply = sends(&actions)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no close_notify")?;
    assert_eq!(
        h.server_reads(&reply),
        Some((CT_ALERT, vec![1, CLOSE_NOTIFY]))
    );
    assert!(!h.client.is_open());
    // Data after the closure alert is ignored (§6.1): consumed, nothing delivered.
    let (consumed, actions) = h.client.step(Input::Bytes(&late));
    assert_eq!((consumed, actions), (late.len(), vec![]));
    // Neither sending nor closing does anything now; the transport closing is not an error.
    assert_eq!(h.client.send_application(b"x"), vec![]);
    assert_eq!(h.client.update_keys(true), vec![]);
    assert_eq!(h.client.close(), vec![]);
    assert_eq!(h.client.step(Input::Closed), (0, vec![]));
    Ok(())
}

#[test]
fn every_other_alert_is_fatal_and_is_not_answered() -> Result<(), String> {
    // handshake_failure, user_canceled, an unknown description, and close_notify at level fatal
    // is still close_notify (TLS 1.3 ignores the level), so it is not in this list.
    for (level, description) in [(2u8, 40u8), (1, 90), (1, 40), (2, 200), (1, 0xff)] {
        let mut h = Harness::new()?;
        let alert = h.server_record(CT_ALERT, &[level, description]);
        let (consumed, actions) = h.client.step(Input::Bytes(&alert));
        assert_eq!(consumed, alert.len());
        assert_eq!(
            actions,
            vec![Action::Fail(description)],
            "level {level} description {description}"
        );
        assert!(!h.client.is_open());
        let data = h.server_record(CT_APPLICATION_DATA, b"after");
        let (consumed, actions) = h.client.step(Input::Bytes(&data));
        assert_eq!((consumed, actions), (data.len(), vec![]));
    }
    Ok(())
}

#[test]
fn malformed_alert_records_fail() -> Result<(), String> {
    for body in [vec![1u8], vec![1, 0, 0]] {
        let mut h = Harness::new()?;
        let record = h.server_record(CT_ALERT, &body);
        let actions = h.feed(&record);
        check_fatal_alert(&mut h, &actions, DECODE_ERROR)?;
    }
    Ok(())
}

#[test]
fn a_handshake_message_may_not_be_interleaved_with_other_records() -> Result<(), String> {
    let ticket = hex(post_handshake_vectors::NEW_SESSION_TICKET);
    let (a, _) = ticket.split_at(30);
    for interleaved in [CT_APPLICATION_DATA, CT_ALERT] {
        let mut h = Harness::new()?;
        let first = h.server_record(CT_HANDSHAKE, a);
        assert_eq!(h.feed(&first), vec![]);
        let content: &[u8] = if interleaved == CT_ALERT {
            &[1, CLOSE_NOTIFY]
        } else {
            b"data"
        };
        let record = h.server_record(interleaved, content);
        let actions = h.feed(&record);
        check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)?;
    }
    Ok(())
}

#[test]
fn tampered_truncated_and_reordered_records_are_bad_record_mac() -> Result<(), String> {
    let mut h = Harness::new()?;
    let mut record = h.server_record(CT_APPLICATION_DATA, b"data");
    let last = record.len().saturating_sub(1);
    if let Some(b) = record.get_mut(last) {
        *b ^= 1;
    }
    let actions = h.feed(&record);
    assert!(delivered(&actions).is_empty());
    check_fatal_alert(&mut h, &actions, BAD_RECORD_MAC)?;
    // Reordered: the second record is read at sequence number 0.
    let mut h = Harness::new()?;
    let _first = h.server_record(CT_APPLICATION_DATA, b"one");
    let second = h.server_record(CT_APPLICATION_DATA, b"two");
    let actions = h.feed(&second);
    check_fatal_alert(&mut h, &actions, BAD_RECORD_MAC)?;
    // Replayed.
    let mut h = Harness::new()?;
    let first = h.server_record(CT_APPLICATION_DATA, b"one");
    assert_eq!(h.feed(&first), vec![Action::Deliver(b"one".to_vec())]);
    let actions = h.feed(&first);
    check_fatal_alert(&mut h, &actions, BAD_RECORD_MAC)
}

#[test]
fn oversized_and_malformed_records_fail_before_decryption() -> Result<(), String> {
    // Length 2^14 + 257 exceeds a TLSCiphertext.
    let mut h = Harness::new()?;
    let (consumed, actions) = h.client.step(Input::Bytes(&[23, 3, 3, 0x41, 0x01]));
    assert_eq!(consumed, 5);
    check_fatal_alert(&mut h, &actions, RECORD_OVERFLOW)?;
    // A wrong legacy_record_version.
    let mut h = Harness::new()?;
    let (_, actions) = h.client.step(Input::Bytes(&[23, 3, 1, 0, 20]));
    check_fatal_alert(&mut h, &actions, DECODE_ERROR)?;
    // An unexpected outer type once protected (a plaintext alert).
    let mut h = Harness::new()?;
    let (_, actions) = h.client.step(Input::Bytes(&[21, 3, 3, 0, 2, 1, 0]));
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)
}

#[test]
fn a_record_of_only_zeros_is_unexpected_message() -> Result<(), String> {
    let mut h = Harness::new()?;
    let key = write_key(&Reference, &SERVER_SECRET_0);
    let iv = write_iv(&Reference, &SERVER_SECRET_0);
    let ad = [CT_APPLICATION_DATA, 3, 3, 0, 20];
    let mut record = ad.to_vec();
    record.extend_from_slice(&aead_seal(&key, &nonce(&iv, 0), &ad, &[0, 0, 0, 0]));
    let actions = h.feed(&record);
    check_fatal_alert(&mut h, &actions, UNEXPECTED_MESSAGE)
}

#[test]
fn the_transport_closing_before_close_notify_is_a_failure_with_no_alert() -> Result<(), String> {
    let mut h = Harness::new()?;
    let (consumed, actions) = h.client.step(Input::Closed);
    assert_eq!((consumed, actions), (0, vec![Action::Fail(INTERNAL_ERROR)]));
    assert!(!h.client.is_open());
    Ok(())
}

#[test]
fn the_client_can_close_and_nothing_is_delivered_afterwards() -> Result<(), String> {
    let mut h = Harness::new()?;
    let sent = h.client.send_application(b"request");
    let wire = sends(&sent)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no send")?;
    assert_eq!(
        h.server_reads(&wire),
        Some((CT_APPLICATION_DATA, b"request".to_vec()))
    );
    let closing = h.client.close();
    assert_eq!(closing.len(), 2);
    assert_eq!(closing.last(), Some(&Action::Close));
    let wire = sends(&closing)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no close_notify")?;
    assert_eq!(
        h.server_reads(&wire),
        Some((CT_ALERT, vec![1, CLOSE_NOTIFY]))
    );
    // The server's reply is ignored; so is anything else.
    let reply = h.server_record(CT_ALERT, &[1, CLOSE_NOTIFY]);
    assert_eq!(h.client.step(Input::Bytes(&reply)), (reply.len(), vec![]));
    Ok(())
}

#[test]
fn application_data_longer_than_a_record_fails_with_record_overflow() -> Result<(), String> {
    let mut h = Harness::new()?;
    let ok = vec![7u8; 16384];
    let sent = h.client.send_application(&ok);
    let wire = sends(&sent)
        .first()
        .map(|w| (*w).clone())
        .ok_or("no send")?;
    assert_eq!(h.server_reads(&wire), Some((CT_APPLICATION_DATA, ok)));
    let sent = h.client.send_application(&vec![7u8; 16385]);
    assert_eq!(sent, vec![Action::Fail(RECORD_OVERFLOW)]);
    assert!(!h.client.is_open());
    Ok(())
}

#[test]
fn a_new_transducer_refuses_a_secret_of_the_wrong_length() {
    assert!(PostHandshake::new(Reference, ToyFactory, &[1; 31], &SERVER_SECRET_0).is_err());
    assert!(PostHandshake::new(Reference, ToyFactory, &CLIENT_SECRET_0, &[1; 33]).is_err());
}

#[test]
fn client_records_carry_increasing_sequence_numbers_under_one_key() -> Result<(), String> {
    let mut h = Harness::new()?;
    let mut previous: Option<Vec<u8>> = None;
    for i in 0..5u8 {
        let sent = h.client.send_application(&[i]);
        let wire = sends(&sent)
            .first()
            .map(|w| (*w).clone())
            .ok_or("no send")?;
        // The same plaintext at a different sequence number is a different record.
        assert_ne!(previous.as_ref(), Some(&wire));
        assert_eq!(h.server_reads(&wire), Some((CT_APPLICATION_DATA, vec![i])));
        previous = Some(wire);
    }
    assert_eq!(h.client_seq, 5);
    Ok(())
}
