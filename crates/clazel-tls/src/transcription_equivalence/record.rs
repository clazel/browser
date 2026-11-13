//! RFC 8446 §5.1 to §5.4 and §7.3: record protection in `spec.rs` and
//! `traffic/spec.rs` proven equal to the clean-room transcription's
//! `record.rs` and `connection::receive_ciphertext`, for every input:
//! [`theorem_record_protection_equivalence`].
//!
//! What is compared, each for all inputs:
//! - §3.3 numbers and §5.1's TLSPlaintext encoding ([`lemma_read_uint`],
//!   [`lemma_write_plaintext`]);
//! - §5.2's TLSInnerPlaintext, written and scanned ([`lemma_inner_write`],
//!   [`lemma_inner_scan`]);
//! - §5.3's per-record nonce ([`lemma_nonce`]) and §5.2's additional data
//!   ([`lemma_additional_data`]);
//! - §7.3's traffic keys at the start of an epoch ([`lemma_epoch_start`]);
//! - §5.2's protection of one record by an epoch (`traffic::spec::send`
//!   against `record::protect_record`), for every send the crate accepts;
//! - §5.2 and §5.4's deprotection of one whole TLSCiphertext by an epoch
//!   (`traffic::spec::receive` against `connection::receive_ciphertext`):
//!   both fail with the same alert, or both yield the same content type and
//!   content with the sequence number advanced.
//!
//! How the two are related ([`epoch_agrees`]): the crate's epoch and the
//! transcription's `TrafficState` hold the same key and IV; the crate's next
//! sequence number `Some(n)` is the transcription's `n`, and the crate's
//! exhausted `None` is a transcription number past 2^64 - 1. The crate's
//! `Seal`/`Open` are the transcription's `aead_encrypt`/`aead_decrypt` with
//! the epoch's key, and its tag length is the transcription's
//! `aead_expansion()`, 16.
//!
//! Domain, and why (each a finding, listed in the PR):
//! - **A failed epoch.** The crate keeps a per-epoch `failed` flag; the
//!   transcription ends the whole connection on the first error, so it has
//!   no failed epoch to read from. The theorem is for a live epoch.
//! - **Sender-side checks.** `traffic::spec::send_error` refuses an inner
//!   type other than alert, handshake or application data, empty alert or
//!   handshake content, and more than 2^14 + 1 inner bytes. The
//!   transcription's sender never builds such a record, so there is nothing
//!   to compare; the theorem covers every send the crate accepts.
//! - **The record header** (type, `legacy_record_version`, length) is read
//!   before the epoch sees the record, by the dispatcher on one side and
//!   `receive_record` on the other; that comparison, and the two sides'
//!   disagreement on `legacy_record_version`, belong to the connection.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's epoch and the transcription's traffic state hold the same
/// key, IV and sequence number.
pub open spec fn epoch_agrees(s: crate::traffic::spec::State, t: crate::transcription::record::TrafficState) -> bool {
    s.key == t.key && s.iv == t.iv
        && match s.next {
            Some(n) => t.sequence_number == n as nat,
            None => t.sequence_number > crate::transcription::record::max_sequence_number(),
        }
}

/// `wire` starts with one whole TLSCiphertext, as the crate reads it.
pub open spec fn is_protected_record(wire: Seq<u8>) -> bool {
    crate::spec::read_record(wire, true) matches crate::spec::Read::Done(crate::spec::Frame::Protected(_, _), _)
}

/// The crate's keyed seal is the transcription's AEAD-Encrypt under `key`.
pub open spec fn seal_agrees(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    p: crate::transcription::primitives::Primitives, key: Seq<u8>) -> bool
{
    forall|n: Seq<u8>, ad: Seq<u8>, pt: Seq<u8>| #[trigger] seal(n, ad, pt) == (p.aead_encrypt)(key, n, ad, pt)
}

/// The crate's keyed open is the transcription's AEAD-Decrypt under `key`.
pub open spec fn open_agrees(open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    p: crate::transcription::primitives::Primitives, key: Seq<u8>) -> bool
{
    forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] open(n, ad, ct) == (p.aead_decrypt)(key, n, ad, ct)
}

/// A crate result and a transcription result of receiving one record agree:
/// the same alert on failure, or the same content handed on, with the read
/// sequence number advanced, on success.
pub open spec fn receive_agrees(p: crate::transcription::primitives::Primitives,
    connection: crate::transcription::connection::Connection, traffic: crate::transcription::record::TrafficState,
    read: crate::traffic::spec::Read, outcome: crate::transcription::connection::Receive) -> bool
{
    match read {
        crate::traffic::spec::Read::Fail(alert) => match outcome {
            crate::transcription::connection::Receive::Abort(e) =>
                crate::transcription::alerts::required_alert(e) == alert as nat,
            _ => false,
        },
        crate::traffic::spec::Read::Record(t, content, _) =>
            outcome == crate::transcription::connection::receive_protected_content(p,
                crate::transcription::connection::Connection {
                    receive: crate::transcription::connection::Protection::Protected(
                        crate::transcription::record::TrafficState {
                            sequence_number: traffic.sequence_number + 1, ..traffic }),
                    ..connection
                }, t as nat, content),
        crate::traffic::spec::Read::NeedMore => false,
    }
}

// ---------------------------------------------------------------------------
// §3.3 numbers.
// ---------------------------------------------------------------------------

/// `encode_uint` has `width` bytes.
pub proof fn lemma_encode_uint_len(value: nat, width: nat)
    ensures crate::transcription::presentation::encode_uint(value, width).len() == width,
    decreases width,
{
    if width > 0 {
        lemma_encode_uint_len(value / 256, (width - 1) as nat);
    }
}

/// §3.3: the transcription's reader of the first `width` bytes is the
/// crate's value of those bytes.
pub proof fn lemma_read_uint(bytes: Seq<u8>, width: nat)
    requires bytes.len() >= width,
    ensures crate::transcription::presentation::read_uint(bytes, width) == crate::spec::be_value(bytes.take(width as int)),
    decreases width,
{
    if width > 0 {
        lemma_read_uint(bytes, (width - 1) as nat);
        assert(bytes.take(width as int).drop_last() =~= bytes.take(width - 1));
    }
}

/// §5.1: the TLSPlaintext encoders agree.
pub proof fn lemma_write_plaintext(t: u8, version: u16, fragment: Seq<u8>)
    ensures
        crate::spec::write_plaintext(t, version, fragment)
            == crate::transcription::record::write_tls_plaintext(t as nat, version as nat, fragment),
        crate::spec::write_record_header(t, version, fragment.len())
            == crate::transcription::record::write_record_header(t as nat, version as nat, fragment.len()),
{
    lemma_header(t, version, fragment.len());
}

/// §5.1: the record header encoders agree.
pub proof fn lemma_header(t: u8, version: u16, length: nat)
    ensures
        crate::spec::write_record_header(t, version, length)
            == crate::transcription::record::write_record_header(t as nat, version as nat, length),
{
    super::schedule::lemma_be_bytes(t as nat, 1);
    super::schedule::lemma_be_bytes(version as nat, 2);
    super::schedule::lemma_be_bytes(length, 2);
    assert(crate::transcription::presentation::encode_uint((t as nat) / 256, 0) =~= Seq::<u8>::empty());
    assert(crate::transcription::presentation::uint8(t as nat) =~= seq![t]);
}

// ---------------------------------------------------------------------------
// §5.2, §5.4 TLSInnerPlaintext.
// ---------------------------------------------------------------------------

/// §5.2: the encoders of TLSInnerPlaintext agree.
pub proof fn lemma_inner_write(content: Seq<u8>, t: u8, padding: nat)
    ensures
        crate::spec::write_inner_plaintext(content, t, padding)
            == crate::transcription::record::write_inner_plaintext(content, t as nat, padding),
{
    super::transcript::lemma_repeat(0, padding);
    assert(crate::transcription::presentation::encode_uint((t as nat) / 256, 0) =~= Seq::<u8>::empty());
    assert(crate::transcription::presentation::uint8(t as nat) =~= seq![t]);
    assert(crate::spec::write_inner_plaintext(content, t, padding)
        =~= crate::transcription::record::write_inner_plaintext(content, t as nat, padding));
}

/// §5.4: the two scans from the end find the same content and type.
pub proof fn lemma_inner_scan(cleartext: Seq<u8>)
    ensures
        match crate::spec::split_inner_plaintext(cleartext) {
            None => crate::transcription::record::read_inner_plaintext(cleartext) is None,
            Some((content, t)) => crate::transcription::record::read_inner_plaintext(cleartext) == Some((content, t as nat)),
        },
    decreases cleartext.len(),
{
    if cleartext.len() > 0 {
        assert(cleartext.subrange(0, cleartext.len() - 1) =~= cleartext.drop_last());
        lemma_inner_scan(cleartext.drop_last());
    }
}

// ---------------------------------------------------------------------------
// §5.3 nonce and §5.2 additional data.
// ---------------------------------------------------------------------------

/// Byte-wise XOR of two sequences of one length.
pub proof fn lemma_xor(a: Seq<u8>, b: Seq<u8>)
    requires a.len() == b.len(),
    ensures
        crate::transcription::record::xor_bytes(a, b).len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] crate::transcription::record::xor_bytes(a, b)[i] == a[i] ^ b[i],
    decreases a.len(),
{
    if a.len() > 0 {
        let a1 = a.subrange(1, a.len() as int);
        let b1 = b.subrange(1, b.len() as int);
        lemma_xor(a1, b1);
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] crate::transcription::record::xor_bytes(a, b)[i] == a[i] ^ b[i] by {
            if i > 0 {
                assert(crate::transcription::record::xor_bytes(a, b)[i] == crate::transcription::record::xor_bytes(a1, b1)[i - 1]);
            }
        }
    }
}

/// §5.3: the per-record nonces agree, for every IV and sequence number.
pub proof fn lemma_nonce(iv: Seq<u8>, n: u64)
    ensures crate::spec::per_record_nonce(iv, n) == crate::transcription::record::per_record_nonce(iv, n as nat),
{
    let padded = crate::spec::be_bytes(n as nat, iv.len());
    super::schedule::lemma_be_bytes(n as nat, iv.len());
    crate::lemmas_pl::lemma_be_bytes_len(n as nat, iv.len());
    lemma_xor(padded, iv);
    let ours = crate::spec::per_record_nonce(iv, n);
    let theirs = crate::transcription::record::per_record_nonce(iv, n as nat);
    assert forall|i: int| 0 <= i < iv.len() implies ours[i] == theirs[i] by {
        let x = iv[i];
        let y = padded[i];
        assert(x ^ y == y ^ x) by (bit_vector);
    }
    assert(ours =~= theirs);
}

/// §5.2: the additional data of a TLSCiphertext is its header bytes, the
/// version as received.
pub proof fn lemma_additional_data(wire: Seq<u8>)
    requires wire.len() >= 5, wire[0] == 23,
    ensures
        wire.take(5) == crate::transcription::record::additional_data(
            crate::transcription::record::ct_application_data(),
            crate::transcription::record::read_record_header(wire)->Some_0.legacy_record_version,
            crate::transcription::record::read_record_header(wire)->Some_0.length),
{
    let v = wire.subrange(1, 3);
    let l = wire.subrange(3, 5);
    lemma_read_uint(v, 2);
    lemma_read_uint(l, 2);
    assert(v.take(2) =~= v);
    assert(l.take(2) =~= l);
    crate::lemmas_pl::lemma_be_bytes_of_be_value(v);
    crate::lemmas_pl::lemma_be_bytes_of_be_value(l);
    super::schedule::lemma_be_bytes(crate::spec::be_value(v), 2);
    super::schedule::lemma_be_bytes(crate::spec::be_value(l), 2);
    super::schedule::lemma_be_bytes(23, 1);
    assert(crate::transcription::presentation::encode_uint(23, 1) =~= seq![23u8]) by (compute_only);
    assert(wire.take(5) =~= seq![wire[0]] + v + l);
}

// ---------------------------------------------------------------------------
// §7.3 epoch start.
// ---------------------------------------------------------------------------

/// §7.3: an epoch started from a 32-byte secret agrees with the
/// transcription's traffic state of the same secret.
pub proof fn lemma_epoch_start(c: crate::schedule::spec::Crypto, p: crate::transcription::primitives::Primitives, secret: Seq<u8>)
    requires super::schedule::crypto_agrees(c, p), secret.len() == 32,
    ensures
        crate::traffic::spec::start(c, secret) is Ok,
        epoch_agrees(crate::traffic::spec::start(c, secret)->Ok_0, crate::transcription::record::traffic_state(p, secret)),
        !(crate::traffic::spec::start(c, secret)->Ok_0).failed,
{
    super::schedule::theorem_schedule_equivalence(c, p);
    assert(crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Key, seq![], 32)
        == crate::transcription::key_schedule::write_key(p, secret));
    assert(crate::schedule::spec::expand_label(c, secret, crate::schedule::spec::Label::Iv, seq![], 12)
        == crate::transcription::key_schedule::write_iv(p, secret));
}

// ---------------------------------------------------------------------------
// §5.2 protection and deprotection by one epoch.
// ---------------------------------------------------------------------------

/// §5.2: every record the crate's epoch accepts to send is the
/// transcription's protected record of the same content, and the sequence
/// numbers move on together.
pub proof fn lemma_protect(p: crate::transcription::primitives::Primitives,
    seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    s: crate::traffic::spec::State, t: crate::transcription::record::TrafficState, typ: u8, content: Seq<u8>)
    requires
        epoch_agrees(s, t),
        seal_agrees(seal, p, t.key),
        crate::traffic::spec::send(seal, s, typ, content, 0).1 is Ok,
    ensures
        crate::traffic::spec::send(seal, s, typ, content, 0).1->Ok_0
            == crate::transcription::record::protect_record(p, t, typ as nat, content),
        epoch_agrees(crate::traffic::spec::send(seal, s, typ, content, 0).0,
            crate::transcription::record::TrafficState { sequence_number: t.sequence_number + 1, ..t }),
{
    let n = s.next->Some_0;
    let inner = crate::spec::write_inner_plaintext(content, typ, 0);
    lemma_inner_write(content, typ, 0);
    lemma_nonce(s.iv, n);
    let length = inner.len() + 16;
    lemma_header(23, 0x0303, length);
    assert(crate::spec::additional_data(length) == crate::spec::write_record_header(23, 0x0303, length));
}

/// §5.2, §5.3, §5.4: one whole TLSCiphertext read by a live epoch. The two
/// sides fail with the same alert, or hand on the same type and content with
/// the read sequence number advanced.
pub proof fn lemma_deprotect(p: crate::transcription::primitives::Primitives,
    open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    s: crate::traffic::spec::State, connection: crate::transcription::connection::Connection,
    t: crate::transcription::record::TrafficState, wire: Seq<u8>)
    requires
        epoch_agrees(s, t),
        open_agrees(open, p, t.key),
        !s.failed,
        is_protected_record(wire),
    ensures
        receive_agrees(p, connection, t, crate::traffic::spec::receive(open, s, wire).1,
            crate::transcription::connection::receive_ciphertext(p, connection, t,
                crate::transcription::record::read_record_header(wire)->Some_0.legacy_record_version,
                wire.subrange(5, wire.len() as int).take(
                    crate::transcription::record::read_record_header(wire)->Some_0.length as int))),
{
    let header = crate::transcription::record::read_record_header(wire)->Some_0;
    let (h, encrypted) = match crate::spec::read_record(wire, true) {
        crate::spec::Read::Done(crate::spec::Frame::Protected(h, e), _) => (h, e),
        _ => (seq![], seq![]),
    };
    let len = crate::spec::be_value(wire.subrange(3, 5));
    lemma_read_uint(wire.subrange(3, 5), 2);
    assert(wire.subrange(3, 5).take(2) =~= wire.subrange(3, 5));
    assert(header.length == len);
    assert(encrypted =~= wire.subrange(5, wire.len() as int).take(len as int));
    assert(h == wire.take(5));
    lemma_additional_data(wire);
    assert(encrypted.len() == len);
    let outcome = crate::transcription::connection::receive_ciphertext(p, connection, t,
        header.legacy_record_version, encrypted);
    match s.next {
        None => {
            assert(outcome == crate::transcription::connection::Receive::Abort(
                crate::transcription::alerts::ClientError::SequenceNumberWrap));
        },
        Some(n) => {
            lemma_nonce(s.iv, n);
            let nonce = crate::spec::per_record_nonce(s.iv, n);
            match open(nonce, h, encrypted) {
                None => {},
                Some(cleartext) => {
                    lemma_inner_scan(cleartext);
                    if cleartext.len() <= crate::spec::MAX_PLAINTEXT + 1 {
                        match crate::spec::split_inner_plaintext(cleartext) {
                            None => {},
                            Some((content, typ)) => {
                                crate::lemmas_record::lemma_split_inner_canonical(cleartext);
                                let after = crate::transcription::connection::Connection {
                                    receive: crate::transcription::connection::Protection::Protected(
                                        crate::transcription::record::TrafficState {
                                            sequence_number: t.sequence_number + 1, ..t }),
                                    ..connection
                                };
                                assert(outcome == crate::transcription::connection::receive_protected_content(p, after, typ as nat, content));
                                if content.len() == 0 && typ == 21 {
                                    // Zero-length alert: interleaved or empty, unexpected_message either way.
                                    assert(after.handshake_fragments == connection.handshake_fragments);
                                }
                            },
                        }
                    }
                },
            }
        },
    }
}

/// RFC 8446 §5.2 to §5.4 and §7.3, for every epoch, secret, content and
/// whole TLSCiphertext: the crate's record protection is the transcription's.
pub proof fn theorem_record_protection_equivalence(c: crate::schedule::spec::Crypto,
    p: crate::transcription::primitives::Primitives)
    requires super::schedule::crypto_agrees(c, p),
    ensures
        // §5.3.
        forall|iv: Seq<u8>, n: u64| #[trigger] crate::spec::per_record_nonce(iv, n)
            == crate::transcription::record::per_record_nonce(iv, n as nat),
        // §5.2, §5.4.
        forall|content: Seq<u8>, t: u8, padding: nat| #[trigger] crate::spec::write_inner_plaintext(content, t, padding)
            == crate::transcription::record::write_inner_plaintext(content, t as nat, padding),
        forall|cleartext: Seq<u8>| match #[trigger] crate::spec::split_inner_plaintext(cleartext) {
            None => crate::transcription::record::read_inner_plaintext(cleartext) is None,
            Some((content, t)) => crate::transcription::record::read_inner_plaintext(cleartext) == Some((content, t as nat)),
        },
        // §5.1.
        forall|t: u8, version: u16, fragment: Seq<u8>| #[trigger] crate::spec::write_plaintext(t, version, fragment)
            == crate::transcription::record::write_tls_plaintext(t as nat, version as nat, fragment),
        // §7.3.
        forall|secret: Seq<u8>| secret.len() == 32 ==> {
            &&& #[trigger] crate::traffic::spec::start(c, secret) is Ok
            &&& epoch_agrees(crate::traffic::spec::start(c, secret)->Ok_0, crate::transcription::record::traffic_state(p, secret))
        },
        // §5.2 protection.
        forall|seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>, s: crate::traffic::spec::State,
            t: crate::transcription::record::TrafficState, typ: u8, content: Seq<u8>|
            #[trigger] epoch_agrees(s, t) && seal_agrees(seal, p, t.key)
                && (#[trigger] crate::traffic::spec::send(seal, s, typ, content, 0)).1 is Ok ==> {
                &&& crate::traffic::spec::send(seal, s, typ, content, 0).1->Ok_0
                    == crate::transcription::record::protect_record(p, t, typ as nat, content)
                &&& epoch_agrees(crate::traffic::spec::send(seal, s, typ, content, 0).0,
                    crate::transcription::record::TrafficState { sequence_number: t.sequence_number + 1, ..t })
            },
        // §5.2, §5.4 deprotection.
        forall|open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, s: crate::traffic::spec::State,
            connection: crate::transcription::connection::Connection, t: crate::transcription::record::TrafficState, wire: Seq<u8>|
            epoch_agrees(s, t) && open_agrees(open, p, t.key) && !s.failed
                && is_protected_record(wire) ==>
                receive_agrees(p, connection, t, (#[trigger] crate::traffic::spec::receive(open, s, wire)).1,
                    #[trigger] crate::transcription::connection::receive_ciphertext(p, connection, t,
                        crate::transcription::record::read_record_header(wire)->Some_0.legacy_record_version,
                        wire.subrange(5, wire.len() as int).take(
                            crate::transcription::record::read_record_header(wire)->Some_0.length as int))),
{
    assert forall|iv: Seq<u8>, n: u64| #[trigger] crate::spec::per_record_nonce(iv, n)
        == crate::transcription::record::per_record_nonce(iv, n as nat) by { lemma_nonce(iv, n); }
    assert forall|content: Seq<u8>, t: u8, padding: nat| #[trigger] crate::spec::write_inner_plaintext(content, t, padding)
        == crate::transcription::record::write_inner_plaintext(content, t as nat, padding) by { lemma_inner_write(content, t, padding); }
    assert forall|cleartext: Seq<u8>| match #[trigger] crate::spec::split_inner_plaintext(cleartext) {
        None => crate::transcription::record::read_inner_plaintext(cleartext) is None,
        Some((content, t)) => crate::transcription::record::read_inner_plaintext(cleartext) == Some((content, t as nat)),
    } by { lemma_inner_scan(cleartext); }
    assert forall|t: u8, version: u16, fragment: Seq<u8>| #[trigger] crate::spec::write_plaintext(t, version, fragment)
        == crate::transcription::record::write_tls_plaintext(t as nat, version as nat, fragment) by {
        lemma_write_plaintext(t, version, fragment);
    }
    assert forall|secret: Seq<u8>| secret.len() == 32 implies {
        &&& #[trigger] crate::traffic::spec::start(c, secret) is Ok
        &&& epoch_agrees(crate::traffic::spec::start(c, secret)->Ok_0, crate::transcription::record::traffic_state(p, secret))
    } by { lemma_epoch_start(c, p, secret); }
    assert forall|seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>, s: crate::traffic::spec::State,
        t: crate::transcription::record::TrafficState, typ: u8, content: Seq<u8>|
        #[trigger] epoch_agrees(s, t) && seal_agrees(seal, p, t.key)
            && (#[trigger] crate::traffic::spec::send(seal, s, typ, content, 0)).1 is Ok implies {
            &&& crate::traffic::spec::send(seal, s, typ, content, 0).1->Ok_0
                == crate::transcription::record::protect_record(p, t, typ as nat, content)
            &&& epoch_agrees(crate::traffic::spec::send(seal, s, typ, content, 0).0,
                crate::transcription::record::TrafficState { sequence_number: t.sequence_number + 1, ..t })
        } by { lemma_protect(p, seal, s, t, typ, content); }
    assert forall|open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, s: crate::traffic::spec::State,
        connection: crate::transcription::connection::Connection, t: crate::transcription::record::TrafficState, wire: Seq<u8>|
        epoch_agrees(s, t) && open_agrees(open, p, t.key) && !s.failed
            && is_protected_record(wire) implies
            receive_agrees(p, connection, t, (#[trigger] crate::traffic::spec::receive(open, s, wire)).1,
                #[trigger] crate::transcription::connection::receive_ciphertext(p, connection, t,
                    crate::transcription::record::read_record_header(wire)->Some_0.legacy_record_version,
                    wire.subrange(5, wire.len() as int).take(
                        crate::transcription::record::read_record_header(wire)->Some_0.length as int)))
    by { lemma_deprotect(p, open, s, connection, t, wire); }
}

} // verus!
