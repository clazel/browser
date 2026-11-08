//! RFC 8446 §4.4.1 and §4.4.3: `transcript::spec` proven equal to the
//! clean-room transcription's transcript (`authentication::transcript_hash`
//! over a list of raw messages and the retry flag), for every input:
//! [`theorem_transcript_equivalence`].
//!
//! How the two are compared:
//! - **State.** The crate keeps the bytes it will hash, with §4.4.1's
//!   synthetic `message_hash` already in place of ClientHello1; the
//!   transcription keeps the raw messages and a flag and builds the bytes when
//!   it hashes. [`represents`] says a crate state stands for a list and a
//!   flag: its bytes are [`hashed_bytes`] of them, its flag is theirs, and in
//!   `FirstServerHello` the list is ClientHello1 alone.
//! - **Hash.length.** The transcription writes the synthetic header as
//!   `00 00 Hash.length` with Hash.length the constant 32; the crate writes
//!   `uint24` of the hash output's actual length (`write_handshake(254, ..)`).
//!   They agree when the hash's outputs are 32 bytes, which both sides state
//!   of SHA-256 in their headers. That is this theorem's one hypothesis on the
//!   hash ([`hash_is_32`]), not a disagreement.
//! - **What only one side checks.** The crate refuses a body above 2^18 bytes
//!   and a transcript above 4 MiB (`TooLarge`), resource policies its header
//!   names; the RFC has neither, and the transcription accepts both. The
//!   crate also refuses a message out of the Hello order (`UnexpectedMessage`),
//!   which the transcription checks in its state machine, not in its
//!   transcript. So the theorem covers every *accepted* step; what a refusal
//!   leads to is compared where the state machines are.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Both sides model SHA-256: every output is Hash.length = 32 bytes.
pub open spec fn hash_is_32(hash: spec_fn(Seq<u8>) -> Seq<u8>) -> bool {
    forall|x: Seq<u8>| #[trigger] hash(x).len() == 32
}

/// §4.4.1: the bytes the transcription's `transcript_hash` hashes.
pub open spec fn hashed_bytes(p: crate::transcription::primitives::Primitives, messages: Seq<Seq<u8>>, retried: bool) -> Seq<u8> {
    if retried && messages.len() > 0 {
        crate::transcription::authentication::synthetic_message_hash(p, messages[0])
            + crate::transcription::presentation::concatenate(messages.subrange(1, messages.len() as int))
    } else {
        crate::transcription::presentation::concatenate(messages)
    }
}

/// The crate's transcript state `s` stands for the transcription's list of
/// raw `messages` with flag `retried`.
pub open spec fn represents(p: crate::transcription::primitives::Primitives, s: crate::transcript::spec::State,
    messages: Seq<Seq<u8>>, retried: bool) -> bool
{
    s.messages == hashed_bytes(p, messages, retried)
        && s.retried == retried
        && messages.len() >= 1
        && (s.phase == crate::transcript::spec::Phase::FirstServerHello ==> messages.len() == 1 && !retried)
}

/// §4: the two encoders of a handshake message agree for every type byte.
pub proof fn lemma_write_handshake(t: u8, body: Seq<u8>)
    ensures crate::spec::write_handshake(t, body) == crate::transcription::key_exchange::write_handshake(t as nat, body),
{
    super::schedule::lemma_be_bytes(body.len(), 3);
    super::schedule::lemma_be_bytes(t as nat, 1);
    let one = crate::transcription::presentation::encode_uint(t as nat, 1);
    assert(crate::transcription::presentation::encode_uint((t as nat) / 256, 0) =~= Seq::<u8>::empty());
    assert(one =~= seq![t]);
}

/// `concatenate` of a list with one more message.
pub proof fn lemma_concatenate_push(messages: Seq<Seq<u8>>, m: Seq<u8>)
    ensures
        crate::transcription::presentation::concatenate(messages.push(m))
            == crate::transcription::presentation::concatenate(messages) + m,
    decreases messages.len(),
{
    if messages.len() == 0 {
        assert(messages.push(m).subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
        assert(crate::transcription::presentation::concatenate(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
        assert(crate::transcription::presentation::concatenate(messages.push(m)) =~= m);
    } else {
        let tail = messages.subrange(1, messages.len() as int);
        assert(messages.push(m).subrange(1, messages.push(m).len() as int) =~= tail.push(m));
        lemma_concatenate_push(tail, m);
        assert(crate::transcription::presentation::concatenate(messages.push(m))
            =~= crate::transcription::presentation::concatenate(messages) + m);
    }
}

/// `concatenate` of one message.
pub proof fn lemma_concatenate_one(m: Seq<u8>)
    ensures crate::transcription::presentation::concatenate(seq![m]) == m,
{
    lemma_concatenate_push(Seq::<Seq<u8>>::empty(), m);
    assert(Seq::<Seq<u8>>::empty().push(m) =~= seq![m]);
    assert(crate::transcription::presentation::concatenate(Seq::<Seq<u8>>::empty()) =~= Seq::<u8>::empty());
    assert(Seq::<u8>::empty() + m =~= m);
}

/// One accepted step keeps the representation.
pub proof fn lemma_step(p: crate::transcription::primitives::Primitives, s: crate::transcript::spec::State,
    messages: Seq<Seq<u8>>, retried: bool, kind: crate::transcript::spec::Kind, body: Seq<u8>)
    requires
        hash_is_32(p.hash),
        represents(p, s, messages, retried),
        crate::transcript::spec::step(p.hash, s, kind, body) is Ok,
    ensures
        represents(p, crate::transcript::spec::step(p.hash, s, kind, body)->Ok_0,
            messages.push(crate::spec::write_handshake(crate::transcript::spec::wire_type(kind), body)),
            retried || kind == crate::transcript::spec::Kind::HelloRetryRequest),
{
    let after = crate::transcript::spec::step(p.hash, s, kind, body)->Ok_0;
    let m = crate::spec::write_handshake(crate::transcript::spec::wire_type(kind), body);
    let next = messages.push(m);
    let r2 = retried || kind == crate::transcript::spec::Kind::HelloRetryRequest;
    assert(after.phase != crate::transcript::spec::Phase::FirstServerHello);
    if kind == crate::transcript::spec::Kind::HelloRetryRequest {
        // Only from FirstServerHello, where the list is ClientHello1 alone.
        assert(s.phase == crate::transcript::spec::Phase::FirstServerHello);
        assert(messages.len() == 1 && !retried);
        lemma_concatenate_one(messages[0]);
        assert(messages =~= seq![messages[0]]);
        assert(s.messages == messages[0]);
        let h = (p.hash)(messages[0]);
        assert(h.len() == 32);
        super::schedule::lemma_be_bytes(32, 3);
        assert(crate::spec::write_u24(32) =~= seq![0u8, 0u8, 32u8]) by (compute_only);
        assert(crate::spec::write_handshake(254, h)
            =~= crate::transcription::authentication::synthetic_message_hash(p, messages[0]));
        assert(next.subrange(1, next.len() as int) =~= seq![m]);
        lemma_concatenate_one(m);
        assert(after.messages =~= hashed_bytes(p, next, r2));
    } else if retried {
        lemma_concatenate_push(messages.subrange(1, messages.len() as int), m);
        assert(next.subrange(1, next.len() as int) =~= messages.subrange(1, messages.len() as int).push(m));
        assert(after.messages =~= hashed_bytes(p, next, r2));
    } else {
        lemma_concatenate_push(messages, m);
        assert(after.messages =~= hashed_bytes(p, next, r2));
    }
}

/// RFC 8446 §4.4.1 and §4.4.3, for every ClientHello, state, message and
/// hash of 32-byte outputs:
/// - `start` stands for the one-message list `[ClientHello]`, encoded the
///   same way on both sides;
/// - every accepted `step` stands for that list with the message appended,
///   and the retry flag raised exactly by a HelloRetryRequest (§4.4.1's
///   synthetic message included);
/// - the crate's hash of its bytes is the transcription's `transcript_hash`
///   of the list it stands for;
/// - §4.4.3's content covered by the server's signature is the same bytes.
pub proof fn theorem_transcript_equivalence(p: crate::transcription::primitives::Primitives)
    requires hash_is_32(p.hash),
    ensures
        forall|client_hello: Seq<u8>| #[trigger] crate::transcript::spec::start(client_hello) is Ok ==>
            represents(p, crate::transcript::spec::start(client_hello)->Ok_0,
                seq![crate::transcription::key_exchange::write_handshake(
                    crate::transcription::key_exchange::ht_client_hello(), client_hello)], false),
        forall|s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool,
            kind: crate::transcript::spec::Kind, body: Seq<u8>|
            #[trigger] represents(p, s, messages, retried) && #[trigger] crate::transcript::spec::step(p.hash, s, kind, body) is Ok ==>
                represents(p, crate::transcript::spec::step(p.hash, s, kind, body)->Ok_0,
                    messages.push(crate::transcription::key_exchange::write_handshake(
                        crate::transcript::spec::wire_type(kind) as nat, body)),
                    retried || kind == crate::transcript::spec::Kind::HelloRetryRequest),
        forall|s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool|
            #[trigger] represents(p, s, messages, retried) ==>
                (p.hash)(s.messages) == crate::transcription::authentication::transcript_hash(p, messages, retried),
        forall|transcript_hash: Seq<u8>|
            #[trigger] crate::transcript::spec::certificate_verify_input(true, transcript_hash)
                == crate::transcription::authentication::certificate_verify_content(
                    crate::transcription::authentication::server_certificate_verify_context(), transcript_hash),
        forall|transcript_hash: Seq<u8>|
            #[trigger] crate::transcript::spec::certificate_verify_input(false, transcript_hash)
                == crate::transcription::authentication::certificate_verify_content(
                    crate::transcription::authentication::client_certificate_verify_context(), transcript_hash),
{
    assert forall|client_hello: Seq<u8>| #[trigger] crate::transcript::spec::start(client_hello) is Ok implies
        represents(p, crate::transcript::spec::start(client_hello)->Ok_0,
            seq![crate::transcription::key_exchange::write_handshake(
                crate::transcription::key_exchange::ht_client_hello(), client_hello)], false)
    by {
        lemma_write_handshake(1, client_hello);
        lemma_concatenate_one(crate::spec::write_handshake(1, client_hello));
    }
    assert forall|s: crate::transcript::spec::State, messages: Seq<Seq<u8>>, retried: bool,
        kind: crate::transcript::spec::Kind, body: Seq<u8>|
        #[trigger] represents(p, s, messages, retried) && #[trigger] crate::transcript::spec::step(p.hash, s, kind, body) is Ok implies
            represents(p, crate::transcript::spec::step(p.hash, s, kind, body)->Ok_0,
                messages.push(crate::transcription::key_exchange::write_handshake(
                    crate::transcript::spec::wire_type(kind) as nat, body)),
                retried || kind == crate::transcript::spec::Kind::HelloRetryRequest)
    by {
        lemma_write_handshake(crate::transcript::spec::wire_type(kind), body);
        lemma_step(p, s, messages, retried, kind, body);
    }
    let rep = crate::transcript::spec::context(true);
    let rep_c = crate::transcript::spec::context(false);
    assert(rep =~= crate::transcription::authentication::server_certificate_verify_context());
    assert(rep_c =~= crate::transcription::authentication::client_certificate_verify_context());
    assert(Seq::new(64, |i: int| 32u8) =~= crate::transcription::presentation::repeat_byte(0x20, 64)) by {
        lemma_repeat(0x20, 64);
    }
    assert forall|transcript_hash: Seq<u8>|
        #[trigger] crate::transcript::spec::certificate_verify_input(true, transcript_hash)
            == crate::transcription::authentication::certificate_verify_content(
                crate::transcription::authentication::server_certificate_verify_context(), transcript_hash)
    by {}
    assert forall|transcript_hash: Seq<u8>|
        #[trigger] crate::transcript::spec::certificate_verify_input(false, transcript_hash)
            == crate::transcription::authentication::certificate_verify_content(
                crate::transcription::authentication::client_certificate_verify_context(), transcript_hash)
    by {}
}

/// `repeat_byte` is the constant sequence.
pub proof fn lemma_repeat(byte: u8, count: nat)
    ensures crate::transcription::presentation::repeat_byte(byte, count) =~= Seq::new(count, |i: int| byte),
    decreases count,
{
    if count > 0 {
        lemma_repeat(byte, (count - 1) as nat);
        assert(crate::transcription::presentation::repeat_byte(byte, count)
            =~= Seq::new((count - 1) as nat, |i: int| byte).push(byte));
    }
}

} // verus!
