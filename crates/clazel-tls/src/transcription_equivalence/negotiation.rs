//! RFC 8446 §4.1.2–§4.1.4 and §4.4.1: the negotiation controller of
//! `hello/client_spec.rs` (`start`, then `receive` on each server Hello
//! body) step for step against the clean-room transcription's
//! `start_handshake` and its WAIT_SH `receive_handshake_message`:
//! [`theorem_negotiation_equivalence`].
//!
//! The two states are tied by [`negotiation_agrees`]: the transcription is
//! in WAIT_SH; its first ClientHello is the crate's, and the one it sent
//! last is the crate's first or, after a retry, the crate's ClientHello2;
//! its retry record is the profile's exactly when the crate has retried
//! (the hello theorem's hypothesis [`super::hello::retry_is_profile`]);
//! the crate's transcript bytes stand for its list of raw messages
//! ([`super::transcript::represents`]); and its X25519 private key is the
//! one whose public value the crate offers. `start` establishes it, and a
//! crate retry keeps it, so the hello theorem's two hypotheses
//! ([`super::hello::sent_is_profile`], [`super::hello::retry_is_profile`])
//! hold in every state the crate's controller reaches: this discharges
//! `retry_is_profile` for the controller.
//!
//! On each body: when the crate rejects, the transcription aborts, and the
//! crate's alert is that of a failure in the transcription's list; when
//! the crate retries, the transcription accepts the HelloRetryRequest,
//! sends the crate's ClientHello2 (in a record of version 0x0303), and the
//! relation holds again; when the crate establishes, the transcription
//! accepts the same ServerHello (`accept_server_hello`), the X25519 share
//! is the one the crate hands on, and the crate's transcript stands for
//! the transcription's.
//!
//! Domain (the crate's resource policies, as in the transcript theorem):
//! the body has at most `MAX_BODY` octets. Two more policies of the crate
//! can refuse a body the transcription accepts, with `internal_error`: its
//! transcript cap (4 MiB, `TooLarge`) and its cookie cap (`MAX_COOKIE`,
//! a cookie of more than 4096 octets). [`receive_agrees`] says those are
//! the only other refusals: an `internal_error` where the transcription
//! has no failure.
//!
//! Not covered here: `bootstrap_spec`'s record layer around this
//! controller (the acknowledgement gate, the CCS, fragments and alerts);
//! that is the framing and driver part of #139.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The two writers of a ClientHello.
// ---------------------------------------------------------------------------

/// §3.4: the two writers of a list of `uint16` agree.
pub proof fn lemma_write_u16s(vs: Seq<u16>)
    ensures
        crate::spec::write_u16s(vs) == crate::transcription::presentation::write_uint16_list(super::extensions::nats(vs)),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_write_u16s(vs.skip(1));
        let n = super::extensions::nats(vs);
        assert(n.subrange(1, n.len() as int) =~= super::extensions::nats(vs.skip(1)));
        super::schedule::lemma_be_bytes(vs[0] as nat, 2);
    }
}

/// §4.2: the two writers of the contents of an extension block agree.
pub proof fn lemma_write_extension_list(es: Seq<crate::spec::Ext>)
    ensures
        crate::spec::write_list(es, |e: crate::spec::Ext| crate::spec::write_ext(e))
            == crate::transcription::extensions::write_extension_list(super::messages::exts_view(es)),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_write_extension_list(es.skip(1));
        let v = super::messages::exts_view(es);
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        super::schedule::lemma_be_bytes(es[0].etype as nat, 2);
        super::schedule::lemma_write_vec(es[0].data, 65535);
        let rest = crate::spec::write_list(es.skip(1), |e: crate::spec::Ext| crate::spec::write_ext(e));
        assert(crate::spec::write_ext(es[0]) + rest
            =~= crate::transcription::presentation::uint16(v[0].extension_type)
                + crate::transcription::presentation::write_vector(v[0].extension_data, 0xffff) + rest);
    }
}

/// §4.1.2: the crate's ClientHello message (its handshake encoding of the
/// body) is the transcription's `write_client_hello` of the same hello.
pub proof fn lemma_write_client_hello(ch: crate::spec::ClientHello)
    ensures
        crate::spec::write_handshake(1, crate::spec::write_client_hello(ch))
            == crate::transcription::key_exchange::write_client_hello(super::client::ch_view(ch)),
{
    let body = crate::spec::write_client_hello(ch);
    super::transcript::lemma_write_handshake(1, body);
    super::schedule::lemma_be_bytes(ch.legacy_version as nat, 2);
    super::schedule::lemma_write_vec(ch.session_id, 32);
    lemma_write_u16s(ch.cipher_suites);
    super::schedule::lemma_write_vec(crate::spec::write_u16s(ch.cipher_suites), 65534);
    super::schedule::lemma_write_vec(ch.compression, 255);
    lemma_write_extension_list(ch.extensions);
    super::schedule::lemma_write_vec(
        crate::spec::write_list(ch.extensions, |e: crate::spec::Ext| crate::spec::write_ext(e)), 65535);
    let v = super::client::ch_view(ch);
    let t = crate::transcription::presentation::uint16(v.legacy_version)
        + v.random
        + crate::transcription::presentation::write_vector(v.legacy_session_id, 32)
        + crate::transcription::presentation::write_vector(
            crate::transcription::presentation::write_uint16_list(v.cipher_suites), 0xfffe)
        + crate::transcription::presentation::write_vector(v.legacy_compression_methods, 0xff)
        + crate::transcription::extensions::write_extensions(v.extensions);
    assert(body =~= t);
}

// ---------------------------------------------------------------------------
// The relation and the steps.
// ---------------------------------------------------------------------------

/// The crate's negotiation controller and the transcription's handshake
/// stand for the same negotiation (see the module documentation).
pub open spec fn negotiation_agrees(p: crate::transcription::primitives::Primitives,
    s: crate::hello::client_spec::State, hs: crate::transcription::state_machine::ClientHandshake) -> bool
{
    let c = s.config;
    let first = super::client::ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
    &&& hs.state == crate::transcription::state_machine::ClientState::WaitSh
    &&& hs.first_hello == first
    &&& super::hello::retry_is_profile(s.transcript.retried, hs.retry)
    &&& !s.transcript.retried ==> hs.hello == first
    &&& s.transcript.retried ==> exists|cookie: Seq<u8>| cookie.len() > 0
            && hs.hello == super::client::ch_view(#[trigger] crate::hello::client_spec::client_hello(c, cookie))
    &&& super::transcript::represents(p, s.transcript, hs.transcript, s.transcript.retried)
    &&& (p.x25519)(hs.x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key
}

/// The crate's `receive` and the transcription's WAIT_SH step on one body
/// agree (see the module documentation).
pub open spec fn receive_agrees(p: crate::transcription::primitives::Primitives,
    s: crate::hello::client_spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>) -> bool
{
    let raw = crate::transcription::key_exchange::write_handshake(2, body);
    let step = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
    let f = super::hello::hello_failures(hs.hello, hs.retry, body);
    match crate::hello::spec::validate(s.config.session_id, s.transcript.retried, body) {
        Err(alert) => {
            &&& crate::hello::client_spec::receive(p.hash, s, body) == Err::<crate::hello::client_spec::Outcome, u8>(alert)
            &&& super::auth_flight::alert_in(alert, f)
            &&& f.len() > 0 && step == crate::transcription::state_machine::HandshakeStep::Abort(f[0])
        },
        Ok(_) => match crate::hello::client_spec::receive(p.hash, s, body) {
            // Only the crate's transcript cap refuses here.
            Err(alert) => alert == 80 && f.len() == 0,
            Ok(crate::hello::client_spec::Outcome::Retry(next, flight)) => match step {
                crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, receive_key_changes } => {
                    &&& negotiation_agrees(p, next, handshake)
                    &&& actions == seq![crate::transcription::state_machine::Action::SendHandshake(flight,
                        crate::transcription::state_machine::other_record_version())]
                    &&& !receive_key_changes
                },
                _ => false,
            },
            Ok(crate::hello::client_spec::Outcome::Established(config, transcript, key)) =>
                match crate::transcription::key_exchange::read_server_hello(body) {
                    None => false,
                    Some(h) => {
                        &&& config == s.config
                        &&& !crate::transcription::key_exchange::is_hello_retry_request(h)
                        &&& f.len() == 0
                        &&& step == crate::transcription::state_machine::accept_server_hello(p, hs, h, raw)
                        &&& crate::transcription::extensions::read_key_share_server_hello(
                            crate::transcription::extensions::find_extension(h.extensions, 51)->0)
                            == Some(crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: key })
                        &&& super::transcript::represents(p, transcript, hs.transcript.push(raw), s.transcript.retried)
                    },
                },
        },
    }
}

/// `start`: the crate's first state agrees with the transcription's
/// `start_handshake` of the crate's ClientHello, and the flight it sends is
/// the transcription's encoding of that ClientHello.
pub open spec fn start_agrees(p: crate::transcription::primitives::Primitives, c: crate::hello::client_spec::Config,
    x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>) -> bool
{
    let first = super::client::ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
    match crate::hello::client_spec::start(c) {
        Ok((s, flight)) => {
            &&& negotiation_agrees(p, s, crate::transcription::state_machine::start_handshake(first, x25519_private_key, retry_private_key))
            &&& flight == crate::transcription::key_exchange::write_client_hello(first)
        },
        Err(_) => true,
    }
}

/// [`start_agrees`], for one configuration and key.
pub proof fn lemma_start(p: crate::transcription::primitives::Primitives, c: crate::hello::client_spec::Config,
    x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>)
    requires
        (p.x25519)(x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key,
    ensures start_agrees(p, c, x25519_private_key, retry_private_key),
{
    let ch = crate::hello::client_spec::client_hello(c, Seq::empty());
    let first = super::client::ch_view(ch);
    lemma_write_client_hello(ch);
    let b = crate::hello::client_spec::body(c, Seq::empty());
    super::transcript::lemma_write_handshake(1, b);
    super::transcript::lemma_concatenate_one(crate::spec::write_handshake(1, b));
    let hs = crate::transcription::state_machine::start_handshake(first, x25519_private_key, retry_private_key);
    assert(hs.transcript =~= seq![crate::transcription::key_exchange::write_handshake(1, b)]);
}

/// A crate transcript step on a body of at most `MAX_BODY` octets, in a
/// phase that takes it, refuses only for the 4 MiB cap.
pub proof fn lemma_step_refusal(hash: spec_fn(Seq<u8>) -> Seq<u8>, t: crate::transcript::spec::State,
    kind: crate::transcript::spec::Kind, body: Seq<u8>)
    requires
        body.len() <= crate::transcript::spec::MAX_BODY,
        crate::transcript::spec::next_phase(t.phase, kind) is Some,
    ensures
        crate::transcript::spec::step(hash, t, kind, body) is Err
            ==> crate::transcript::spec::step(hash, t, kind, body) == Err::<crate::transcript::spec::State, crate::transcript::spec::Error>(crate::transcript::spec::Error::TooLarge),
{
}

/// [`receive_agrees`], for one state and body.
#[verifier::rlimit(200)]
pub proof fn lemma_receive(p: crate::transcription::primitives::Primitives, s: crate::hello::client_spec::State,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        crate::hello::client_spec::wf(s),
        negotiation_agrees(p, s, hs),
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures receive_agrees(p, s, hs, body),
{
    let c = s.config;
    let retried = s.transcript.retried;
    let raw = crate::transcription::key_exchange::write_handshake(2, body);
    // The hello theorem's two hypotheses hold here.
    let cookie0: Seq<u8> = if retried {
        choose|cookie: Seq<u8>| cookie.len() > 0
            && hs.hello == super::client::ch_view(#[trigger] crate::hello::client_spec::client_hello(c, cookie))
    } else {
        Seq::empty()
    };
    assert(hs.hello == super::client::ch_view(crate::hello::client_spec::client_hello(c, cookie0)));
    let offers = crate::hello::join_spec::extension_types(c, cookie0.len() != 0);
    super::client::lemma_sent_is_profile(c, cookie0);
    super::hello::lemma_validate(hs.hello, hs.retry, offers, c.session_id, retried, body);
    super::hello::lemma_receive(p, hs, body);
    super::hello::lemma_read_server_hello(body);
    let f = super::hello::hello_failures(hs.hello, hs.retry, body);
    super::transcript::lemma_write_handshake(2, body);
    match crate::hello::spec::validate(c.session_id, retried, body) {
        Err(alert) => {
            if f.len() == 0 {
                assert(!super::auth_flight::alert_in(alert, f));
            }
        },
        Ok(crate::hello::spec::Selection::Retry(cookie)) => {
            // A retry: the crate had not retried (else `SecondHelloRetryRequest`).
            let h = crate::transcription::key_exchange::read_server_hello(body)->Some_0;
            assert(crate::transcription::key_exchange::read_server_hello_any_version(body) == Some(h));
            if retried {
                assert(f == crate::transcription::alerts::fails_if(true, crate::transcription::alerts::ClientError::SecondHelloRetryRequest)
                    + crate::transcription::key_exchange::hello_retry_request_failures(hs.hello, h));
                assert(false);
            }
            assert(s.transcript.phase == crate::transcript::spec::Phase::FirstServerHello);
            super::client::lemma_retry(c, body, (p.x25519)(hs.x25519_private_key, crate::transcription::primitives::x25519_basepoint()));
            let hrr = crate::transcription::key_exchange::hello_retry_request_failures(hs.hello, h);
            let second = super::client::ch_view(crate::hello::client_spec::client_hello(c, cookie));
            assert(crate::transcription::extensions::find_extension(h.extensions, 51) is None) by {
                super::client::lemma_retry_accepted(hs.hello, c.session_id, offers, h);
            }
            assert(f == crate::transcription::alerts::fails_if(false, crate::transcription::alerts::ClientError::SecondHelloRetryRequest) + hrr);
            let step = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
            assert(step == crate::transcription::state_machine::accept_hello_retry_request(p, hs, h, raw));
            // The crate's two transcript steps.
            let hash = p.hash;
            let k_hrr = crate::transcript::spec::Kind::HelloRetryRequest;
            let k_ch = crate::transcript::spec::Kind::ClientHello;
            let b2 = crate::hello::client_spec::body(c, cookie);
            lemma_step_refusal(hash, s.transcript, k_hrr, body);
            match crate::transcript::spec::step(hash, s.transcript, k_hrr, body) {
                Err(_) => {},
                Ok(t1) => {
                    super::transcript::lemma_step(p, s.transcript, hs.transcript, false, k_hrr, body);
                    assert(t1.phase == crate::transcript::spec::Phase::SecondClientHello);
                    assert(b2.len() <= crate::transcript::spec::MAX_BODY || crate::transcript::spec::step(hash, t1, k_ch, b2) is Err);
                    if b2.len() <= crate::transcript::spec::MAX_BODY {
                        lemma_step_refusal(hash, t1, k_ch, b2);
                    }
                    match crate::transcript::spec::step(hash, t1, k_ch, b2) {
                        Err(_) => {},
                        Ok(t2) => {
                            super::transcript::lemma_step(p, t1, hs.transcript.push(raw), true, k_ch, b2);
                            super::transcript::lemma_write_handshake(1, b2);
                            lemma_write_client_hello(crate::hello::client_spec::client_hello(c, cookie));
                            let next = crate::hello::client_spec::State { config: c, transcript: t2 };
                            let hs2 = match step {
                                crate::transcription::state_machine::HandshakeStep::Proceed { handshake, .. } => handshake,
                                _ => hs,
                            };
                            assert(hs2.hello == second);
                            assert(hs2.transcript == hs.transcript.push(raw).push(crate::transcription::key_exchange::write_client_hello(second)));
                            assert(cookie.len() > 0 && hs2.hello == super::client::ch_view(crate::hello::client_spec::client_hello(c, cookie)));
                            assert(negotiation_agrees(p, next, hs2));
                        },
                    }
                },
            }
        },
        Ok(crate::hello::spec::Selection::Share(key)) => {
            let h = crate::transcription::key_exchange::read_server_hello(body)->Some_0;
            let k_sh = crate::transcript::spec::Kind::ServerHello;
            assert(crate::transcript::spec::next_phase(s.transcript.phase, k_sh) is Some);
            lemma_step_refusal(p.hash, s.transcript, k_sh, body);
            match crate::transcript::spec::step(p.hash, s.transcript, k_sh, body) {
                Err(_) => {},
                Ok(t) => {
                    super::transcript::lemma_step(p, s.transcript, hs.transcript, retried, k_sh, body);
                },
            }
        },
    }
}

/// **The negotiation theorem.** For every configuration the crate starts
/// with, and every private key whose public value it offers, the crate's
/// first state agrees with the transcription's `start_handshake` of the
/// crate's ClientHello, and sends it; and from every pair of agreeing
/// states, on every body, the crate's `receive` and the transcription's
/// WAIT_SH step agree ([`receive_agrees`]), a retry leading again to
/// agreeing states. Hypothesis: the hash's outputs are 32 bytes
/// ([`super::transcript::hash_is_32`]), and the crate hashes with the
/// transcription's hash.
pub proof fn theorem_negotiation_equivalence(p: crate::transcription::primitives::Primitives)
    requires super::transcript::hash_is_32(p.hash),
    ensures
        forall|c: crate::hello::client_spec::Config, x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>|
            crate::hello::client_spec::start(c) is Ok
                && (p.x25519)(x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key
            ==> #[trigger] start_agrees(p, c, x25519_private_key, retry_private_key),
        forall|s: crate::hello::client_spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            crate::hello::client_spec::wf(s) && #[trigger] negotiation_agrees(p, s, hs)
                && body.len() <= crate::transcript::spec::MAX_BODY
            ==> #[trigger] receive_agrees(p, s, hs, body),
{
    assert forall|c: crate::hello::client_spec::Config, x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>|
        crate::hello::client_spec::start(c) is Ok
            && (p.x25519)(x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key
        implies #[trigger] start_agrees(p, c, x25519_private_key, retry_private_key) by {
        lemma_start(p, c, x25519_private_key, retry_private_key);
    }
    assert forall|s: crate::hello::client_spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        crate::hello::client_spec::wf(s) && #[trigger] negotiation_agrees(p, s, hs)
            && body.len() <= crate::transcript::spec::MAX_BODY
        implies #[trigger] receive_agrees(p, s, hs, body) by {
        lemma_receive(p, s, hs, body);
    }
}

} // verus!
