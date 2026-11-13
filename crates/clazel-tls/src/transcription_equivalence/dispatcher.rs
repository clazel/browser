//! RFC 8446 §4.3, §4.4, §5, §6, §7.3 and Appendix D.4: the client from the
//! accepted ServerHello to CONNECTED, `connection/dispatcher_spec.rs`
//! (`feed`'s record step `receive_record`, and `acknowledge`) started from
//! `traffic/handshake_spec.rs`'s handoff, against the clean-room
//! transcription's record layer (`connection::receive_stream`,
//! `receive_record`, `receive_ciphertext`, `process_handshake_bytes`,
//! `apply_actions`, `alert_record`, `close_write`) around A.1's states
//! WAIT_EE to WAIT_FINISHED (`state_machine::receive_handshake_message`),
//! with D.4's change_cipher_spec (`middlebox::client_receive_stream`):
//! [`theorem_dispatcher_equivalence`]. It sits between
//! [`super::bootstrap`] (before the ServerHello) and
//! [`super::post_handshake`] (after CONNECTED), and composes with the
//! second: acknowledging the client's flight gives the state where
//! `post_handshake::post_agrees` holds ([`ack_agrees`]).
//!
//! The two states are tied by [`dispatcher_agrees`]: the authentication
//! states agree (`auth::auth_agrees`, so the crate's phase is A.1's state);
//! the server handshake epoch is the transcription's `receive`; the client
//! handshake epoch is unused and the transcription's `send` not engaged; the
//! reassembly buffer is `handshake_fragments`; the master secret is the
//! transcription's; nothing is closed or owed; and D.4's dummy record is
//! owed exactly when the transcription, in compatibility mode, has not
//! written it. [`lemma_start`] establishes it from the handoff.
//!
//! What is compared, from agreeing states and for all inputs: one whole
//! record (five header bytes and exactly `length` more), the crate's
//! `receive_record` (`feed` on every record its framer completes,
//! [`lemma_feed_complete`]) against `client_receive_stream`
//! ([`record_agrees`]): the header (§5, §5.1), the compatibility
//! change_cipher_spec (dropped at a message boundary, refused inside a
//! fragmented message, on both sides), deprotection (§5.2 to §5.4, through
//! [`super::record`]), alerts (§6, §6.1), application data (refused before
//! CONNECTED), and the handshake messages of the record, one by one
//! ([`lemma_messages`], through [`super::auth`] and [`super::auth_flight`]),
//! to the server Finished, the client's flight with D.4's dummy record, and
//! its acknowledgement.
//!
//! Rejections, as #139 compares them: the crate rejects exactly when the
//! transcription does, and its alert is that of some failure in the
//! transcription's list for the message it aborts on ([`fails_as`],
//! [`message_fails`]); no order is chosen where the RFC ranks none. The
//! crate's alert record is the transcription's `alert_record` of the crate's
//! alert (the fatal alert under the client handshake key, A.1's note).
//!
//! Hypotheses (true of what both sides model; not axioms): [`hypotheses`]
//! (the crate's `Crypto`, AEAD and signature check are the transcription's
//! primitives; hash, HMAC and HKDF-Expand outputs have their lengths) and,
//! for the start, `keys::x25519_agrees`.
//!
//! Domain conditions (kept, stated, until the driver theorem):
//! - the crate's 16 KiB key cap ([`validator_agrees`]); its other caps
//!   (2^18 handshake message, 4 MiB transcript) are cases of
//!   [`fail_agrees`] instead, so every record is compared;
//! - offers are the client's profile (`auth::spec::profile_extensions`);
//! - the certificate validators agree (`auth_flight::chain_agrees`);
//! - for the start, [`accepts_server_hello`]: what the bootstrap theorem's
//!   `Established` case gives, plus the ClientHello's signature schemes and
//!   the fields A.1 sets only from WAIT_EE on being unset (not yet
//!   discharged from `negotiation_agrees`: the driver theorem's).
//!
//! Where the two differ, each stated as a definition:
//! - [`wrong_type`] (the multi-fault item): a message of a type the state
//!   does not expect; the crate may name its parser's fault.
//! - [`finished_first`]: a Finished that is not the record's last message
//!   at a boundary; the crate refuses the record before authenticating any
//!   of its messages.
//! - `post_handshake::two_faults`: an unknown record type longer than
//!   2^14.
//! - the 2^18 handshake-message cap (`internal_error`), in [`fail_agrees`].
//! - [`transcript_cap`]: the crate's 4 MiB transcript cap refuses, with
//!   `internal_error`, a message the transcription accepts (only when the
//!   transcript, the message and the client's 48-octet flight would pass
//!   4 MiB: `auth::transcript_capped`). Short of that, the crate proceeds
//!   exactly as the record-level comparison says, with no condition.
//! - [`coalesced`]: the crate's flight is one record; the transcription
//!   writes the empty Certificate and the Finished in two. The same bytes
//!   with no CertificateRequest.
//! - the peer's close_notify during its flight ([`outcome_agrees`]): the
//!   crate closes at once, sending exactly the transcription's
//!   `close_write` record; the transcription only stops reading.
//!
//! The framer's timing on a partial record, and `feed` over a stream in any
//! chunks, are [`super::framing`]'s ([`super::framing::theorem_disp_stream`]).
//!
//! Not covered: transport end of file (the crate's `die`; `connection.rs` leaves
//! transport closure out of scope); `acknowledge` of bytes other than the
//! flight (a local `internal_error`; the transcription has no transport);
//! `feed` outside the `Handshake` mode (it does nothing).

#[cfg(verus_only)]
use crate::connection::dispatcher_spec::{Action, Ciphers, Mode, State};
#[cfg(verus_only)]
use crate::transcription::alerts::ClientError;
#[cfg(verus_only)]
use crate::transcription::connection::{Connection, Progress, Protection, Receive};
#[cfg(verus_only)]
use crate::transcription::middlebox::{ClientConnection, ClientReceive};
#[cfg(verus_only)]
use crate::transcription::primitives::Primitives;
#[cfg(verus_only)]
use crate::transcription::state_machine::{ClientHandshake, ClientState, HandshakeStep};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Hypotheses on the primitives, and the domain.
// ---------------------------------------------------------------------------

/// The dispatcher's key-explicit AEAD (`dispatcher_spec::Ciphers`, the
/// factory's functions: `cipher_models`) is the transcription's AEAD-Encrypt
/// and AEAD-Decrypt, for every key.
pub open spec fn ciphers_agree(f: Ciphers, p: Primitives) -> bool {
    &&& forall|k: Seq<u8>, n: Seq<u8>, ad: Seq<u8>, x: Seq<u8>|
        #[trigger] (f.seal)(k, n, ad, x) == (p.aead_encrypt)(k, n, ad, x)
    &&& forall|k: Seq<u8>, n: Seq<u8>, ad: Seq<u8>, x: Seq<u8>|
        #[trigger] (f.open)(k, n, ad, x) == (p.aead_decrypt)(k, n, ad, x)
}

/// Every hypothesis of the theorem: the two sides' primitives are the same
/// functions (hash, HKDF, HMAC, AEAD, the signature check with no separate
/// key-compatibility check), and the hash, HMAC and HKDF-Expand outputs have
/// the lengths both sides model (SHA-256: 32 octets; RFC 5869 §2.3).
pub open spec fn hypotheses(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives) -> bool
{
    &&& super::schedule::crypto_agrees(c, p)
    &&& ciphers_agree(f, p)
    &&& super::transcript::hash_is_32(p.hash)
    &&& super::auth::hmac_is_32(p.hmac)
    &&& super::auth::verification_agrees(v, p)
    &&& super::post_handshake::expand_is_sized(p)
}

/// The domain on the certificate validators (as in
/// [`super::auth_flight`]): the two agree on every Certificate body
/// (`chain_agrees`, X.509 being a parameter on both sides), and the crate's
/// 16 KiB key cap never fires.
pub open spec fn validator_agrees(v: crate::auth::spec::Verification, p: Primitives,
    config: crate::auth::spec::Config) -> bool
{
    &&& super::auth_flight::chain_agrees(v, p, config.host, config.now)
    &&& forall|body: Seq<u8>| #[trigger] (v.chain)(config.host, config.now, body) matches Ok(key)
        ==> key.len() <= crate::auth::spec::MAX_KEY
}

/// The factory's functions as the dispatcher keeps them agree when the
/// factory does ([`super::post_handshake::cipher_agrees`]).
pub proof fn lemma_cipher_models(factory: crate::traffic::spec::Cipher, s: State, p: Primitives)
    requires super::post_handshake::cipher_agrees(factory, p),
    ensures ciphers_agree(crate::connection::dispatcher_spec::cipher_models(factory, s), p),
{
}

/// The dispatcher's keyed seal and open of an epoch are the transcription's
/// AEAD under the same key.
pub proof fn lemma_seal(f: Ciphers, p: Primitives, e: crate::traffic::spec::State)
    requires ciphers_agree(f, p),
    ensures
        super::record::seal_agrees(crate::connection::dispatcher_spec::seal_with(f, e), p, e.key),
        super::record::open_agrees(crate::connection::dispatcher_spec::open_with(f, e), p, e.key),
{
    let seal = crate::connection::dispatcher_spec::seal_with(f, e);
    let open = crate::connection::dispatcher_spec::open_with(f, e);
    assert forall|n: Seq<u8>, ad: Seq<u8>, pt: Seq<u8>| #[trigger] seal(n, ad, pt) == (p.aead_encrypt)(e.key, n, ad, pt) by {
        assert((f.seal)(e.key, n, ad, pt) == (p.aead_encrypt)(e.key, n, ad, pt));
    }
    assert forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] open(n, ad, ct) == (p.aead_decrypt)(e.key, n, ad, ct) by {
        assert((f.open)(e.key, n, ad, ct) == (p.aead_decrypt)(e.key, n, ad, ct));
    }
}

// ---------------------------------------------------------------------------
// One handshake message of the server's flight.
// ---------------------------------------------------------------------------

/// A.1: the message type the transcription's state expects.
pub open spec fn expected(state: ClientState, t: u8) -> bool {
    ||| state == ClientState::WaitEe && t == 8
    ||| state == ClientState::WaitCertCr && (t == 13 || t == 11)
    ||| state == ClientState::WaitCert && t == 11
    ||| state == ClientState::WaitCv && t == 15
    ||| state == ClientState::WaitFinished && t == 20
}

/// The transcription's failure list of a message of the expected type
/// (`encrypted_extensions_failures`, `certificate_request_failures`,
/// `certificate_failures`); empty for CertificateVerify and Finished,
/// whose alerts are compared as equal.
pub open spec fn message_failures(hs: ClientHandshake, m: Seq<u8>) -> Seq<ClientError> {
    let t = m[0];
    let body = m.skip(4);
    if hs.state == ClientState::WaitEe && t == 8 {
        super::auth_flight::ee_failures(hs, body)
    } else if hs.state == ClientState::WaitCertCr && t == 13 {
        super::auth_flight::cr_failures(body)
    } else if (hs.state == ClientState::WaitCertCr || hs.state == ClientState::WaitCert) && t == 11 {
        match crate::transcription::authentication::read_certificate(body) {
            Some(c) => crate::transcription::authentication::certificate_failures(hs.hello, c),
            None => seq![],
        }
    } else {
        seq![]
    }
}

/// **A stated difference (the multi-fault item): a message of a type the
/// state does not expect.** Both reject. The transcription says
/// `unexpected_message` first (A.1 and §4: "Protocol messages MUST be sent
/// in the order defined"); the crate parses the body first
/// (`auth::spec::receive`), so a body that is also malformed is refused
/// with its parser's alert, and a well-formed one with
/// `unexpected_message`. The RFC ranks neither fault.
pub open spec fn wrong_type(t: u8, body: Seq<u8>, alert: u8) -> bool {
    ||| alert == crate::spec::UNEXPECTED_MESSAGE
    ||| crate::spec::parse_handshake_body(t, body, 32) matches crate::spec::Res::Err(k) && alert == crate::spec::alert_of(k)
}

/// The crate's rejection of message `m` with `alert` and the
/// transcription's abort with `e` agree: for the expected type, `alert` is
/// that of some failure in the transcription's list (`e` first, then
/// [`message_failures`]: no order is chosen where the RFC ranks none); for
/// another type, [`wrong_type`].
pub open spec fn message_fails(hs: ClientHandshake, m: Seq<u8>, e: ClientError, alert: u8) -> bool {
    if expected(hs.state, m[0]) {
        super::auth_flight::alert_in(alert, seq![e] + message_failures(hs, m))
    } else {
        wrong_type(m[0], m.skip(4), alert)
    }
}

/// What A.1's steps before CONNECTED keep: the handshake secrets, the
/// ClientHello and retry record, and the CertificateRequest context.
pub open spec fn kept(hs: ClientHandshake, h2: ClientHandshake) -> bool {
    &&& h2.client_handshake_traffic_secret == hs.client_handshake_traffic_secret
    &&& h2.server_handshake_traffic_secret == hs.server_handshake_traffic_secret
    &&& h2.handshake_secret == hs.handshake_secret
    &&& h2.retry == hs.retry
    &&& h2.hello == hs.hello
}

/// The client's flight after the server Finished, as the transcription
/// records it: the last messages of its transcript (the empty Certificate if
/// one was requested, §4.4.2, and the Finished).
pub open spec fn client_flight(hs: ClientHandshake) -> Seq<Seq<u8>> {
    let n = hs.transcript.len();
    if hs.certificate_request_context is Some {
        hs.transcript.subrange(n - 2, n as int)
    } else {
        hs.transcript.subrange(n - 1, n as int)
    }
}

/// §4.4.4, A.1 "Recv Finished": the transcription's step on a server
/// Finished that the crate accepts, with the flight the crate sends: CONNECTED,
/// the client's flight (the crate's `flight` is its messages, in order),
/// A.1's actions in order, and the hash the crate keeps for the application
/// secrets.
pub open spec fn finished_agrees(p: Primitives, hs: ClientHandshake, m: Seq<u8>, after: crate::auth::spec::State,
    flight: Seq<u8>, t: HandshakeStep) -> bool
{
    let retried = hs.retry is Some;
    let master = crate::transcription::key_schedule::master_secret(p, hs.handshake_secret);
    let through = hs.transcript.push(m);
    match t {
        HandshakeStep::Proceed { handshake, actions, receive_key_changes } => {
            let msgs = client_flight(handshake);
            &&& receive_key_changes
            &&& handshake.state == ClientState::Connected
            &&& kept(hs, handshake)
            &&& handshake.certificate_request_context == hs.certificate_request_context
            &&& (msgs.len() == 1 || msgs.len() == 2)
            &&& (msgs.len() == 2) == (hs.certificate_request_context is Some)
            &&& forall|i: int| 0 <= i < msgs.len() ==> #[trigger] msgs[i].len() <= crate::spec::MAX_PLAINTEXT
            &&& flight == crate::transcription::presentation::concatenate(msgs)
            &&& 0 < flight.len() <= crate::spec::MAX_PLAINTEXT
            &&& actions == seq![crate::transcription::state_machine::Action::SetSendSecret(hs.client_handshake_traffic_secret)]
                + crate::transcription::state_machine::send_each(msgs.subrange(0, msgs.len() - 1))
                + seq![
                    crate::transcription::state_machine::Action::SendHandshake(msgs.last(), 0x0303),
                    crate::transcription::state_machine::Action::SetSendSecret(
                        crate::transcription::key_schedule::client_application_traffic_secret_0(p, master, through, retried)),
                    crate::transcription::state_machine::Action::SetReceiveSecret(
                        crate::transcription::key_schedule::server_application_traffic_secret_0(p, master, through, retried)),
                ]
            &&& after.application_hash == crate::transcription::authentication::transcript_hash(p, through, retried)
            &&& after.phase == crate::auth::spec::Phase::SendFinished
            &&& super::transcript::represents(p, crate::transcript::spec::State {
                    messages: super::transcript::hashed_bytes(p, through, retried),
                    phase: crate::transcript::spec::Phase::Handshake, retried }, through, retried)
        },
        _ => false,
    }
}

/// The crate's authentication step on one whole message `m` and the
/// transcription's A.1 step on it agree: both reject (as
/// [`message_fails`]); or both go on with no action, the states still
/// related and the crate's transcript longer by the message; or the server
/// Finished is accepted and the crate's flight is the transcription's
/// ([`finished_agrees`]).
pub open spec fn message_agrees(p: Primitives, a: crate::auth::spec::State, hs: ClientHandshake, m: Seq<u8>,
    r: (crate::auth::spec::State, crate::auth::spec::Action), t: HandshakeStep) -> bool
{
    match r.1 {
        crate::auth::spec::Action::Fail(alert) => t is Abort && message_fails(hs, m, t->Abort_0, alert),
        crate::auth::spec::Action::None => {
            &&& t is Proceed
            &&& t->actions.len() == 0
            &&& !t->receive_key_changes
            &&& super::auth::auth_agrees(p, r.0, t->handshake)
            &&& kept(hs, t->handshake)
            &&& t->handshake.state != ClientState::Connected
            &&& r.0.config == a.config
            &&& r.0.transcript.messages.len() == a.transcript.messages.len() + m.len()
        },
        crate::auth::spec::Action::Send(flight) => {
            &&& m[0] == crate::spec::HS_FINISHED
            &&& a.phase == crate::auth::spec::Phase::Finished
            &&& hs.state == ClientState::WaitFinished
            &&& r.0.config == a.config
            &&& finished_agrees(p, hs, m, r.0, flight, t)
        },
        _ => false,
    }
}

/// `alert_in` of the first failure.
pub proof fn lemma_in_first(alert: u8, e: ClientError, rest: Seq<ClientError>)
    requires crate::transcription::alerts::required_alert(e) == alert as nat,
    ensures super::auth_flight::alert_in(alert, seq![e] + rest),
{
    assert((seq![e] + rest)[0] == e);
}

/// No failure of the transcription requires a closure alert.
pub proof fn lemma_required_not_closure(e: ClientError)
    ensures
        crate::transcription::alerts::required_alert(e) != 0,
        crate::transcription::alerts::required_alert(e) != 90,
        crate::transcription::alerts::required_alert(e) < 256,
{
}

/// An alert in a failure list is not a closure alert.
pub proof fn lemma_in_not_closure(alert: u8, l: Seq<ClientError>)
    requires super::auth_flight::alert_in(alert, l),
    ensures alert != 0 && alert != 90,
{
    let i = choose|i: int| 0 <= i < l.len() && #[trigger] crate::transcription::alerts::required_alert(l[i]) == alert as nat;
    lemma_required_not_closure(l[i]);
}

/// The crate's authentication step keeps its configuration.
pub proof fn lemma_step_config(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    a: crate::auth::spec::State, t: u8, body: Seq<u8>)
    ensures crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(t, body)).0.config == a.config,
{
    hide(crate::spec::parse_handshake_body);
    match crate::spec::parse_handshake_body(t, body, 32) {
        crate::spec::Res::Err(_) => {},
        crate::spec::Res::Ok(m) => {
            lemma_dispatch_config(c, v, a, body, m);
        },
    }
}

/// The crate's `dispatch` keeps the configuration.
pub proof fn lemma_dispatch_config(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    a: crate::auth::spec::State, body: Seq<u8>, m: crate::spec::HsMsg)
    ensures crate::auth::spec::dispatch(c, v, a, body, m).0.config == a.config,
{
    hide(crate::auth::spec::accept_finished);
    hide(crate::auth::spec::on_certificate);
    hide(crate::auth::spec::on_request);
    hide(crate::auth::spec::on_verify);
    hide(crate::auth::spec::on_extensions);
    match m {
        crate::spec::HsMsg::EncryptedExtensions(es) => { reveal(crate::auth::spec::on_extensions); },
        crate::spec::HsMsg::CertificateRequest(r) => { reveal(crate::auth::spec::on_request); },
        crate::spec::HsMsg::Certificate(cert) => { reveal(crate::auth::spec::on_certificate); },
        crate::spec::HsMsg::CertificateVerify(cv) => { reveal(crate::auth::spec::on_verify); },
        crate::spec::HsMsg::Finished(vd) => {
            if a.phase == crate::auth::spec::Phase::Finished && vd.len() == 32 {
                lemma_accept_finished_config(c, a, vd);
            }
        },
        _ => {},
    }
}

/// §4.4.4: the crate's `accept_finished` keeps the configuration.
pub proof fn lemma_accept_finished_config(c: crate::schedule::spec::Crypto, a: crate::auth::spec::State, vd: Seq<u8>)
    ensures crate::auth::spec::accept_finished(c, a, vd).0.config == a.config,
{
    hide(crate::transcript::spec::step);
    hide(crate::schedule::spec::finished);
    hide(crate::spec::write_handshake);
}

/// §4.4.4: the flight the crate's `accept_finished` sends is the empty
/// Certificate (when requested) and its Finished: 36 or 44 octets, and its
/// phase is then `SendFinished`.
pub proof fn lemma_crate_flight(c: crate::schedule::spec::Crypto, p: Primitives, a: crate::auth::spec::State, vd: Seq<u8>)
    requires
        super::schedule::crypto_agrees(c, p),
        super::auth::hmac_is_32(p.hmac),
        crate::auth::spec::accept_finished(c, a, vd).1 is Send,
    ensures
        0 < crate::auth::spec::accept_finished(c, a, vd).1->Send_0.len() <= 44,
        crate::auth::spec::accept_finished(c, a, vd).0.phase == crate::auth::spec::Phase::SendFinished,
{
    hide(crate::transcript::spec::step);
    let r = crate::auth::spec::accept_finished(c, a, vd);
    let own = crate::schedule::spec::finished(c, a.config.client_secret, r.0.transcript.messages);
    super::auth::lemma_raw(20, own);
    super::auth::lemma_raw(11, crate::auth::spec::empty_certificate());
    assert(own.len() == 32);
}

/// §4.4.1: one more message in the transcription's list adds its bytes to
/// what the transcript hash covers.
pub proof fn lemma_hashed_push(p: Primitives, messages: Seq<Seq<u8>>, m: Seq<u8>, retried: bool)
    requires messages.len() >= 1,
    ensures
        super::transcript::hashed_bytes(p, messages.push(m), retried)
            == super::transcript::hashed_bytes(p, messages, retried) + m,
{
    if retried {
        let tail = messages.subrange(1, messages.len() as int);
        assert(messages.push(m).subrange(1, messages.push(m).len() as int) =~= tail.push(m));
        super::transcript::lemma_concatenate_push(tail, m);
        assert(messages.push(m)[0] == messages[0]);
        let s = crate::transcription::authentication::synthetic_message_hash(p, messages[0]);
        assert(s + (crate::transcription::presentation::concatenate(tail) + m)
            =~= (s + crate::transcription::presentation::concatenate(tail)) + m);
    } else {
        super::transcript::lemma_concatenate_push(messages, m);
    }
}

/// `concatenate` of one or two messages.
pub proof fn lemma_concatenate_two(x: Seq<u8>, y: Seq<u8>)
    ensures
        crate::transcription::presentation::concatenate(seq![x]) == x,
        crate::transcription::presentation::concatenate(seq![x, y]) == x + y,
{
    super::transcript::lemma_concatenate_one(x);
    super::transcript::lemma_concatenate_one(y);
    assert(seq![x, y].subrange(1, 2) =~= seq![y]);
}

/// The crate's authentication step and the transcription's A.1 step agree on
/// every whole message ([`message_agrees`]), from related states, within the
/// crate's resource policy.
#[verifier::rlimit(80)]
pub proof fn lemma_message(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, p: Primitives,
    a: crate::auth::spec::State, hs: ClientHandshake, m: Seq<u8>)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        super::auth::hmac_is_32(p.hmac),
        super::auth::verification_agrees(v, p),
        super::auth::auth_agrees(p, a, hs),
        validator_agrees(v, p, a.config),
        crate::auth::spec::profile_extensions(a.config.extensions),
        m.len() >= 4,
        m.len() == 4 + crate::spec::be_value(m.subrange(1, 4)),
        m.skip(4).len() <= crate::transcript::spec::MAX_BODY,
    ensures
        message_agrees(p, a, hs, m, crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(m[0], m.skip(4))),
            crate::transcription::state_machine::receive_handshake_message(p, hs, m))
        || super::auth::transcript_capped(a, m.skip(4),
            crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(m[0], m.skip(4))),
            crate::transcription::state_machine::receive_handshake_message(p, hs, m)),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(super::auth::auth_agrees);
    hide(crate::spec::parse_handshake_body);
    let t = m[0];
    let body = m.skip(4);
    super::bootstrap::lemma_message(m);
    lemma_step_config(c, v, a, t, body);
    assert(super::auth::phase_is(a.phase, hs.state)) by { reveal(super::auth::auth_agrees); }
    lemma_t_step(p, hs, m);
    let r = crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(t, body));
    let ts = crate::transcription::state_machine::receive_handshake_message(p, hs, m);
    if !expected(hs.state, t) {
        lemma_crate_wrong_type(c, v, a, hs, t, body);
    } else if hs.state == ClientState::WaitFinished {
        assert(t == 20);
        super::auth::lemma_finished(c, v, p, a, hs, body);
        match r.1 {
            crate::auth::spec::Action::Fail(alert) => {
                if ts is Abort {
                    lemma_in_first(alert, ts->Abort_0, message_failures(hs, m));
                }
            },
            crate::auth::spec::Action::Send(flight) => {
                lemma_finished_send(c, v, p, a, hs, m);
            },
            _ => {},
        }
    } else {
        lemma_message_flight(c, v, p, a, hs, m);
    }
}

/// [`lemma_message`] for EncryptedExtensions, CertificateRequest,
/// Certificate and CertificateVerify of the expected type.
#[verifier::rlimit(80)]
pub proof fn lemma_message_flight(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, p: Primitives,
    a: crate::auth::spec::State, hs: ClientHandshake, m: Seq<u8>)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        super::auth::hmac_is_32(p.hmac),
        super::auth::verification_agrees(v, p),
        super::auth::auth_agrees(p, a, hs),
        validator_agrees(v, p, a.config),
        crate::auth::spec::profile_extensions(a.config.extensions),
        m.len() >= 4,
        m == crate::transcription::key_exchange::write_handshake(m[0] as nat, m.skip(4)),
        m.skip(4).len() <= crate::transcript::spec::MAX_BODY,
        expected(hs.state, m[0]),
        hs.state != ClientState::WaitFinished,
    ensures
        message_agrees(p, a, hs, m, crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(m[0], m.skip(4))),
            crate::transcription::state_machine::receive_handshake_message(p, hs, m))
        || super::auth::transcript_capped(a, m.skip(4),
            crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(m[0], m.skip(4))),
            crate::transcription::state_machine::receive_handshake_message(p, hs, m)),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(super::auth::auth_agrees);
    hide(crate::spec::parse_handshake_body);
    let t = m[0];
    let body = m.skip(4);
    lemma_step_config(c, v, a, t, body);
    assert(super::auth::phase_is(a.phase, hs.state)) by { reveal(super::auth::auth_agrees); }
    lemma_t_step(p, hs, m);
    let r = crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(t, body));
    let ts = crate::transcription::state_machine::receive_handshake_message(p, hs, m);
    let retried = hs.retry is Some;
    if hs.state == ClientState::WaitEe {
        super::auth_flight::lemma_ee(c, v, p, a, hs, body);
    } else if hs.state == ClientState::WaitCertCr && t == 13 {
        super::auth_flight::lemma_cr(c, v, p, a, hs, body);
    } else if hs.state == ClientState::WaitCertCr || hs.state == ClientState::WaitCert {
        assert((v.chain)(a.config.host, a.config.now, body) matches Ok(key) ==> key.len() <= crate::auth::spec::MAX_KEY);
        super::auth_flight::lemma_certificate(c, v, p, a, hs, body);
    } else if hs.state == ClientState::WaitCv {
        super::auth::lemma_certificate_verify(c, v, p, a, hs, body);
        match r.1 {
            crate::auth::spec::Action::Fail(alert) => {
                if ts is Abort {
                    lemma_in_first(alert, ts->Abort_0, message_failures(hs, m));
                }
            },
            _ => {},
        }
    }
    // EncryptedExtensions, CertificateRequest, Certificate, CertificateVerify.
    match r.1 {
        crate::auth::spec::Action::None => {
            let h2 = ts->handshake;
            reveal(super::auth::auth_agrees);
            assert(super::transcript::represents(p, a.transcript, hs.transcript, retried));
            assert(super::transcript::represents(p, r.0.transcript, h2.transcript, retried));
            lemma_hashed_push(p, hs.transcript, m, retried);
        },
        _ => {},
    }
}

/// The server Finished's case of [`lemma_message`]: the crate's flight
/// and the transcription's step agree as [`finished_agrees`] says.
#[verifier::rlimit(80)]
pub proof fn lemma_finished_send(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, p: Primitives,
    a: crate::auth::spec::State, hs: ClientHandshake, m: Seq<u8>)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        super::auth::hmac_is_32(p.hmac),
        super::auth::auth_agrees(p, a, hs),
        hs.state == ClientState::WaitFinished,
        m.len() >= 4,
        m[0] == 20,
        m == crate::transcription::key_exchange::write_handshake(20, m.skip(4)),
        m.skip(4).len() <= crate::transcript::spec::MAX_BODY,
        crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(20, m.skip(4))).1 is Send,
    ensures
        finished_agrees(p, hs, m, crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(20, m.skip(4))).0,
            crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(20, m.skip(4))).1->Send_0,
            crate::transcription::state_machine::receive_handshake_message(p, hs, m)),
{
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::auth::spec::step);
    hide(crate::auth::spec::accept_finished);
    hide(crate::transcription::key_schedule::client_application_traffic_secret_0);
    hide(crate::transcription::key_schedule::server_application_traffic_secret_0);
    hide(crate::transcription::key_schedule::master_secret);
    hide(crate::transcription::authentication::transcript_hash);
    hide(super::transcript::hashed_bytes);
    hide(crate::transcription::state_machine::send_each);
    hide(crate::transcription::presentation::concatenate);
    hide(super::auth::auth_agrees);
    let body = m.skip(4);
    let r = crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(20, body));
    let flight = r.1->Send_0;
    let ts = crate::transcription::state_machine::receive_handshake_message(p, hs, m);
    assert(super::auth::phase_is(a.phase, hs.state)) by { reveal(super::auth::auth_agrees); }
    assert(a.phase == crate::auth::spec::Phase::Finished);
    super::auth::lemma_finished(c, v, p, a, hs, body);
    assert(body.len() <= crate::transcript::spec::MAX_BODY);
    assert(r == (if body.len() != 32 { crate::auth::spec::fail(a, 50) } else { crate::auth::spec::accept_finished(c, a, body) })) by {
        super::auth::lemma_crate_finished(c, v, a, body);
    }
    assert(body.len() == 32);
    assert(r == crate::auth::spec::accept_finished(c, a, body));
    lemma_crate_flight(c, p, a, body);
    lemma_t_step(p, hs, m);
    let h2 = ts->handshake;
    let n0 = hs.transcript.len();
    let n = h2.transcript.len();
    let msgs = client_flight(h2);
    assert(ts is Proceed);
    assert(n == n0 + 2 + (if hs.certificate_request_context is Some { 1int } else { 0int }));
    assert(h2.certificate_request_context == hs.certificate_request_context);
    assert(msgs =~= h2.transcript.subrange(n0 as int + 1, n as int));
    assert(msgs.subrange(0, msgs.len() - 1) =~= h2.transcript.subrange(n0 as int + 1, n - 1));
    assert(msgs.last() == h2.transcript.last());
    assert(flight == crate::transcription::presentation::concatenate(msgs));
    if msgs.len() == 1 {
        assert(msgs =~= seq![msgs[0]]);
        lemma_concatenate_two(msgs[0], msgs[0]);
        assert(msgs[0] == flight);
    } else {
        assert(msgs =~= seq![msgs[0], msgs[1]]);
        lemma_concatenate_two(msgs[0], msgs[1]);
        assert(msgs[0] + msgs[1] == flight);
        assert(msgs[0].len() + msgs[1].len() == flight.len());
    }
    let through = hs.transcript.push(m);
    let tr = crate::transcript::spec::State {
        messages: super::transcript::hashed_bytes(p, through, hs.retry is Some),
        phase: crate::transcript::spec::Phase::Handshake, retried: hs.retry is Some };
    assert(super::transcript::represents(p, tr, through, hs.retry is Some));
    let retried = hs.retry is Some;
    let master = crate::transcription::key_schedule::master_secret(p, hs.handshake_secret);
    assert(kept(hs, h2));
    assert((msgs.len() == 1 || msgs.len() == 2));
    assert((msgs.len() == 2) == (hs.certificate_request_context is Some));
    assert(flight == crate::transcription::presentation::concatenate(msgs));
    assert(0 < flight.len() <= crate::spec::MAX_PLAINTEXT);
    assert(forall|i: int| 0 <= i < msgs.len() ==> #[trigger] msgs[i].len() <= crate::spec::MAX_PLAINTEXT);
    assert(ts->actions == seq![crate::transcription::state_machine::Action::SetSendSecret(hs.client_handshake_traffic_secret)]
                + crate::transcription::state_machine::send_each(msgs.subrange(0, msgs.len() - 1))
                + seq![
                    crate::transcription::state_machine::Action::SendHandshake(msgs.last(), 0x0303),
                    crate::transcription::state_machine::Action::SetSendSecret(
                        crate::transcription::key_schedule::client_application_traffic_secret_0(p, master, through, retried)),
                    crate::transcription::state_machine::Action::SetReceiveSecret(
                        crate::transcription::key_schedule::server_application_traffic_secret_0(p, master, through, retried)),
                ]);
    assert(r.0.application_hash == crate::transcription::authentication::transcript_hash(p, through, retried));
    assert(r.0.phase == crate::auth::spec::Phase::SendFinished);
}

/// The crate's step on a message of a type its phase does not expect:
/// refused, with `unexpected_message` or its parser's alert.
#[verifier::rlimit(50)]
pub proof fn lemma_crate_wrong_type(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    a: crate::auth::spec::State, hs: ClientHandshake, t: u8, body: Seq<u8>)
    requires
        super::auth::phase_is(a.phase, hs.state),
        !expected(hs.state, t),
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures
        crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(t, body)).1 is Fail,
        wrong_type(t, body, crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(t, body)).1->Fail_0),
{
    hide(crate::spec::parse_handshake_body);
    hide(crate::auth::spec::accept_finished);
    hide(crate::auth::spec::on_certificate);
    hide(crate::auth::spec::on_request);
    hide(crate::auth::spec::on_verify);
    hide(crate::auth::spec::on_extensions);
    super::auth_flight::lemma_crate_receive(c, v, a, t, body);
    lemma_parse_variant(t, body);
    match crate::spec::parse_handshake_body(t, body, 32) {
        crate::spec::Res::Err(k) => {},
        crate::spec::Res::Ok(msg) => {
            match msg {
                crate::spec::HsMsg::EncryptedExtensions(es) => { reveal(crate::auth::spec::on_extensions); },
                crate::spec::HsMsg::CertificateRequest(r) => { reveal(crate::auth::spec::on_request); },
                crate::spec::HsMsg::Certificate(cert) => { reveal(crate::auth::spec::on_certificate); },
                crate::spec::HsMsg::CertificateVerify(cv) => { reveal(crate::auth::spec::on_verify); },
                _ => {},
            }
        },
    }
}

/// The crate parser's result is of the variant its type byte names.
pub proof fn lemma_parse_variant(t: u8, body: Seq<u8>)
    ensures
        crate::spec::parse_handshake_body(t, body, 32) matches crate::spec::Res::Ok(m) ==> {
            &&& (m is EncryptedExtensions ==> t == 8)
            &&& (m is CertificateRequest ==> t == 13)
            &&& (m is Certificate ==> t == 11)
            &&& (m is CertificateVerify ==> t == 15)
            &&& (m is Finished ==> t == 20)
        },
{
}

/// The transcription's step on one message in WAIT_EE to WAIT_FINISHED:
/// a type out of order is `out_of_order`; otherwise what it keeps.
pub proof fn lemma_t_step(p: Primitives, hs: ClientHandshake, m: Seq<u8>)
    requires
        hs.state == ClientState::WaitEe || hs.state == ClientState::WaitCertCr || hs.state == ClientState::WaitCert
            || hs.state == ClientState::WaitCv || hs.state == ClientState::WaitFinished,
        m.len() >= 4,
    ensures ({
        let t = crate::transcription::state_machine::receive_handshake_message(p, hs, m);
        &&& !expected(hs.state, m[0]) ==> t == crate::transcription::state_machine::out_of_order(m[0] as nat)
        &&& !expected(hs.state, m[0]) ==> t is Abort
            && crate::transcription::alerts::required_alert(t->Abort_0) == 10
        &&& (t is Proceed && !(hs.state == ClientState::WaitFinished && m[0] == 20)) ==> {
            &&& t->handshake.transcript == hs.transcript.push(m)
            &&& kept(hs, t->handshake)
            &&& t->handshake.state != ClientState::Connected
            &&& in_flight(t->handshake.state)
            &&& t->actions.len() == 0
            &&& !t->receive_key_changes
        }
        &&& (t is Proceed && hs.state == ClientState::WaitFinished && m[0] == 20) ==> {
            &&& t->receive_key_changes
            &&& kept(hs, t->handshake)
            &&& t->handshake.certificate_request_context == hs.certificate_request_context
            &&& t->handshake.transcript.len() == hs.transcript.len() + 2
                + (if hs.certificate_request_context is Some { 1int } else { 0int })
        }
    }),
{
}

// ---------------------------------------------------------------------------
// The relation.
// ---------------------------------------------------------------------------

/// A.1's states of the server's flight, WAIT_EE to WAIT_FINISHED.
pub open spec fn in_flight(state: ClientState) -> bool {
    state == ClientState::WaitEe || state == ClientState::WaitCertCr || state == ClientState::WaitCert
        || state == ClientState::WaitCv || state == ClientState::WaitFinished
}

/// The crate's client handshake epoch is unused: it is the transcription's
/// traffic state of `client_handshake_traffic_secret` at sequence number 0
/// (A.1 sets "K_send = handshake" only on Finished, and the alert of A.1's
/// note uses that key fresh: `connection::protection_for_alert`).
pub open spec fn sender_fresh(p: Primitives, s: State, c: Connection) -> bool {
    &&& s.handshake_sender is Some
    &&& super::record::epoch_agrees(s.handshake_sender->Some_0,
        crate::transcription::record::traffic_state(p, c.handshake.client_handshake_traffic_secret))
    &&& !s.handshake_sender->Some_0.failed
}

/// The crate's server handshake epoch is the transcription's `receive`.
pub open spec fn receiver_agrees(s: State, c: Connection) -> bool {
    &&& s.handshake_receiver is Some
    &&& c.receive is Protected
    &&& super::record::epoch_agrees(s.handshake_receiver->Some_0, c.receive->Protected_0)
    &&& !s.handshake_receiver->Some_0.failed
}

/// The dispatcher in its `Handshake` mode and the transcription's client
/// in WAIT_EE to WAIT_FINISHED stand for the same connection, except perhaps
/// for the bytes of an unfinished handshake message: the authentication
/// states agree ([`super::auth::auth_agrees`], which ties the phase to A.1's
/// state); the domain on the validators and offers holds; the server
/// handshake epoch is the transcription's `receive`; the client handshake
/// epoch is unused ([`sender_fresh`]) and the transcription's `send` is not
/// engaged; nothing is closed or owed; the crate's master secret is the
/// transcription's of its Handshake Secret; the framer holds no partial
/// record; and the dummy change_cipher_spec is still owed exactly when the
/// transcription, in compatibility mode, has not written it (Appendix D.4).
pub open spec fn agrees_but_buffer(p: Primitives, v: crate::auth::spec::Verification, s: State, cl: ClientConnection) -> bool {
    let c = cl.connection;
    &&& s.mode == Mode::Handshake
    &&& s.framing.len() == 0
    &&& s.auth is Some
    &&& super::auth::auth_agrees(p, s.auth->Some_0, c.handshake)
    &&& validator_agrees(v, p, s.auth->Some_0.config)
    &&& crate::auth::spec::profile_extensions(s.auth->Some_0.config.extensions)
    &&& receiver_agrees(s, c)
    &&& sender_fresh(p, s, c)
    &&& c.send == Protection::Unprotected
    &&& !c.read_closed
    &&& !c.key_update_owed
    &&& s.master == crate::transcription::key_schedule::master_secret(p, c.handshake.handshake_secret)
    &&& s.ccs_pending == (cl.compatibility_mode && !cl.change_cipher_spec_sent)
}

/// **The state relation**: [`agrees_but_buffer`], and the crate's
/// reassembly buffer is the transcription's `handshake_fragments`.
pub open spec fn dispatcher_agrees(p: Primitives, v: crate::auth::spec::Verification, s: State, cl: ClientConnection) -> bool {
    agrees_but_buffer(p, v, s, cl) && cl.connection.handshake_fragments == s.reassembly.buf
}

// ---------------------------------------------------------------------------
// Alerts.
// ---------------------------------------------------------------------------

/// §6, §6.2, A.1's note: the crate's fatal alert in the server's flight is
/// the transcription's `alert_record` of the same description: the fatal
/// alert under the client handshake key, at sequence number 0; then every
/// key is dropped.
pub proof fn lemma_fatal(f: Ciphers, p: Primitives, s: State, y: Connection, alert: u8)
    requires
        ciphers_agree(f, p),
        s.mode == Mode::Handshake,
        sender_fresh(p, s, y),
        in_flight(y.handshake.state),
        alert != 0,
        alert != 90,
    ensures
        crate::connection::dispatcher_spec::fatal(f, s, alert)
            == (Action::Fail(alert, Some(crate::transcription::connection::alert_record(p, y, alert as nat))),
                crate::connection::dispatcher_spec::failed()),
{
    let tx = s.handshake_sender->Some_0;
    let t0 = crate::transcription::record::traffic_state(p, y.handshake.client_handshake_traffic_secret);
    lemma_seal(f, p, tx);
    let content = crate::connection::dispatcher_spec::fatal_alert(alert);
    assert(crate::transcription::alerts::write_alert(alert as nat) =~= content);
    super::record::lemma_protect(p, crate::connection::dispatcher_spec::seal_with(f, tx), tx, t0, 21, content);
}

/// §6.1: the crate's close_notify in the server's flight is the
/// transcription's `close_write` record; then every key is dropped.
pub proof fn lemma_closing(f: Ciphers, p: Primitives, s: State, y: Connection)
    requires
        ciphers_agree(f, p),
        s.mode == Mode::Handshake,
        sender_fresh(p, s, y),
        in_flight(y.handshake.state),
    ensures
        crate::connection::dispatcher_spec::closing(f, s)
            == (Action::Close(Some(crate::transcription::connection::close_write(p, y))),
                crate::connection::dispatcher_spec::closed()),
{
    let tx = s.handshake_sender->Some_0;
    let t0 = crate::transcription::record::traffic_state(p, y.handshake.client_handshake_traffic_secret);
    lemma_seal(f, p, tx);
    let content = crate::connection::dispatcher_spec::close_notify_alert();
    assert(crate::transcription::alerts::write_alert(0) =~= content);
    super::record::lemma_protect(p, crate::connection::dispatcher_spec::seal_with(f, tx), tx, t0, 21, content);
}

/// The transcription's alert record is the same in every state of the
/// server's flight with the same client handshake secret.
pub proof fn lemma_alert_record_kept(p: Primitives, y1: Connection, y2: Connection, alert: nat)
    requires
        in_flight(y1.handshake.state),
        in_flight(y2.handshake.state),
        y1.handshake.client_handshake_traffic_secret == y2.handshake.client_handshake_traffic_secret,
    ensures
        crate::transcription::connection::alert_record(p, y1, alert)
            == crate::transcription::connection::alert_record(p, y2, alert),
{
}

// ---------------------------------------------------------------------------
// The client's flight.
// ---------------------------------------------------------------------------

/// The transcription's records of the client's flight: each message in a
/// record of its own (its sender's choice: no coalescing), under the client
/// handshake key at sequence numbers 0, 1, ...
pub open spec fn protect_each(p: Primitives, t: crate::transcription::record::TrafficState, msgs: Seq<Seq<u8>>)
    -> Seq<Seq<u8>>
    decreases msgs.len(),
{
    if msgs.len() == 0 {
        seq![]
    } else {
        seq![crate::transcription::record::protect_record(p, t, 22, msgs[0])]
            + protect_each(p, crate::transcription::record::TrafficState { sequence_number: t.sequence_number + 1, ..t },
                msgs.skip(1))
    }
}

/// **A stated difference: coalescing.** The crate seals its whole flight
/// in one record (§5.1: "Handshake messages MAY be coalesced into a single
/// TLSPlaintext record"); the transcription writes each message in a record
/// of its own ([`protect_each`]). With no CertificateRequest the flight is
/// one message and the two are the same record ([`lemma_one_message`]).
pub open spec fn coalesced(p: Primitives, chts: Seq<u8>, msgs: Seq<Seq<u8>>) -> Seq<u8> {
    crate::transcription::record::protect_record(p, crate::transcription::record::traffic_state(p, chts), 22,
        crate::transcription::presentation::concatenate(msgs))
}

/// A.1's actions on the server Finished, for the client's flight `msgs`.
pub open spec fn flight_actions(chts: Seq<u8>, msgs: Seq<Seq<u8>>, cas: Seq<u8>, sas: Seq<u8>)
    -> Seq<crate::transcription::state_machine::Action>
{
    seq![crate::transcription::state_machine::Action::SetSendSecret(chts)]
        + crate::transcription::state_machine::send_each(msgs.subrange(0, msgs.len() - 1))
        + seq![
            crate::transcription::state_machine::Action::SendHandshake(msgs.last(), 0x0303),
            crate::transcription::state_machine::Action::SetSendSecret(cas),
            crate::transcription::state_machine::Action::SetReceiveSecret(sas),
        ]
}

/// The transcription's `fragment_blocks` of at most 2^14 octets.
pub proof fn lemma_one_block(m: Seq<u8>)
    requires m.len() <= crate::spec::MAX_PLAINTEXT,
    ensures crate::transcription::record::fragment_blocks(m) == seq![m],
{
}

/// The transcription's `apply_actions` of one handshake message sent under
/// a live key, then the rest.
pub proof fn lemma_apply_send(p: Primitives, y: Connection, m: Seq<u8>,
    rest: Seq<crate::transcription::state_machine::Action>)
    requires
        y.send is Protected,
        m.len() <= crate::spec::MAX_PLAINTEXT,
    ensures ({
        let t = y.send->Protected_0;
        let y1 = Connection { send: Protection::Protected(crate::transcription::record::TrafficState {
            sequence_number: t.sequence_number + 1, ..t }), ..y };
        let (last, more) = crate::transcription::connection::apply_actions(p, y1, rest);
        crate::transcription::connection::apply_actions(p, y,
            seq![crate::transcription::state_machine::Action::SendHandshake(m, 0x0303)] + rest)
            == (last, seq![crate::transcription::record::protect_record(p, t, 22, m)] + more)
    }),
{
    let a = seq![crate::transcription::state_machine::Action::SendHandshake(m, 0x0303)] + rest;
    assert(a[0] == crate::transcription::state_machine::Action::SendHandshake(m, 0x0303));
    assert(a.subrange(1, a.len() as int) =~= rest);
    lemma_one_block(m);
    super::post_handshake::lemma_send_block(p, y.send->Protected_0, 22, m);
}

/// The transcription's `apply_actions` of A.1's actions on the server
/// Finished: each message of the flight in its own record under the client
/// handshake key, then both directions under the application keys.
#[verifier::rlimit(40)]
pub proof fn lemma_apply_flight(p: Primitives, y: Connection, chts: Seq<u8>, msgs: Seq<Seq<u8>>, cas: Seq<u8>, sas: Seq<u8>)
    requires
        msgs.len() == 1 || msgs.len() == 2,
        forall|i: int| 0 <= i < msgs.len() ==> #[trigger] msgs[i].len() <= crate::spec::MAX_PLAINTEXT,
    ensures
        crate::transcription::connection::apply_actions(p, y, flight_actions(chts, msgs, cas, sas))
            == (Connection {
                send: Protection::Protected(crate::transcription::record::traffic_state(p, cas)),
                receive: Protection::Protected(crate::transcription::record::traffic_state(p, sas)),
                ..y
            }, protect_each(p, crate::transcription::record::traffic_state(p, chts), msgs)),
{
    let t0 = crate::transcription::record::traffic_state(p, chts);
    let t1 = crate::transcription::record::TrafficState { sequence_number: 1, ..t0 };
    let t2 = crate::transcription::record::TrafficState { sequence_number: 2, ..t0 };
    let tail = seq![
        crate::transcription::state_machine::Action::SetSendSecret(cas),
        crate::transcription::state_machine::Action::SetReceiveSecret(sas),
    ];
    let fin = crate::transcription::state_machine::Action::SendHandshake(msgs.last(), 0x0303);
    let y0 = Connection { send: Protection::Protected(t0), ..y };
    let done = Connection {
        send: Protection::Protected(crate::transcription::record::traffic_state(p, cas)),
        receive: Protection::Protected(crate::transcription::record::traffic_state(p, sas)),
        ..y
    };
    let e = Seq::<crate::transcription::state_machine::Action>::empty();
    assert forall|z: Connection| z == (Connection { send: z.send, ..y }) implies
        #[trigger] crate::transcription::connection::apply_actions(p, z, tail) == (done, Seq::<Seq<u8>>::empty()) by {
        let s1 = seq![crate::transcription::state_machine::Action::SetReceiveSecret(sas)];
        assert(tail.subrange(1, 2) =~= s1);
        assert(s1.subrange(1, 1) =~= e);
        assert(tail[0] == crate::transcription::state_machine::Action::SetSendSecret(cas));
        assert(s1[0] == crate::transcription::state_machine::Action::SetReceiveSecret(sas));
        let z1 = Connection { send: Protection::Protected(crate::transcription::record::traffic_state(p, cas)), ..z };
        let z2 = Connection { receive: Protection::Protected(crate::transcription::record::traffic_state(p, sas)), ..z1 };
        assert(z2 == done);
        assert(crate::transcription::connection::apply_actions(p, z2, e) == (done, Seq::<Seq<u8>>::empty()));
        assert(crate::transcription::connection::apply_actions(p, z1, s1) == crate::transcription::connection::apply_actions(p, z2, e));
        assert(crate::transcription::connection::apply_actions(p, z, tail) == crate::transcription::connection::apply_actions(p, z1, s1));
    }
    let actions = flight_actions(chts, msgs, cas, sas);
    assert(actions[0] == crate::transcription::state_machine::Action::SetSendSecret(chts));
    if msgs.len() == 1 {
        assert(msgs.subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
        assert(crate::transcription::state_machine::send_each(Seq::<Seq<u8>>::empty()) == e);
        assert(actions.subrange(1, actions.len() as int) =~= seq![fin] + tail);
        lemma_apply_send(p, y0, msgs[0], tail);
        assert(msgs.last() == msgs[0]);
        let y1 = Connection { send: Protection::Protected(t1), ..y };
        assert(crate::transcription::connection::apply_actions(p, y1, tail) == (done, Seq::<Seq<u8>>::empty()));
        assert(msgs.skip(1) =~= Seq::<Seq<u8>>::empty());
        assert(protect_each(p, t1, Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
        assert(seq![crate::transcription::record::protect_record(p, t0, 22, msgs[0])] + Seq::<Seq<u8>>::empty()
            =~= seq![crate::transcription::record::protect_record(p, t0, 22, msgs[0])]);
    } else {
        let cert = crate::transcription::state_machine::Action::SendHandshake(msgs[0], 0x0303);
        assert(msgs.subrange(0, 1) =~= seq![msgs[0]]);
        assert(seq![msgs[0]].subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
        assert(crate::transcription::state_machine::send_each(seq![msgs[0]].subrange(1, 1)) == e);
        assert(crate::transcription::state_machine::send_each(seq![msgs[0]]) == seq![cert] + e);
        assert(seq![cert] + e =~= seq![cert]);
        assert(actions.subrange(1, actions.len() as int) =~= seq![cert] + (seq![fin] + tail));
        lemma_apply_send(p, y0, msgs[0], seq![fin] + tail);
        let y1 = Connection { send: Protection::Protected(t1), ..y };
        lemma_apply_send(p, y1, msgs[1], tail);
        assert(msgs.last() == msgs[1]);
        let y2 = Connection { send: Protection::Protected(t2), ..y };
        assert(crate::transcription::connection::apply_actions(p, y2, tail) == (done, Seq::<Seq<u8>>::empty()));
        assert(msgs.skip(1) =~= seq![msgs[1]]);
        assert(seq![msgs[1]].skip(1) =~= Seq::<Seq<u8>>::empty());
        assert(protect_each(p, t2, Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
        assert(protect_each(p, t1, seq![msgs[1]]) =~= seq![crate::transcription::record::protect_record(p, t1, 22, msgs[1])]);
        assert(protect_each(p, t0, msgs) =~= seq![crate::transcription::record::protect_record(p, t0, 22, msgs[0]),
            crate::transcription::record::protect_record(p, t1, 22, msgs[1])]);
    }
}

/// With no CertificateRequest, the crate's record of its flight is the
/// transcription's one record.
pub proof fn lemma_one_message(p: Primitives, chts: Seq<u8>, msgs: Seq<Seq<u8>>)
    requires msgs.len() == 1,
    ensures
        protect_each(p, crate::transcription::record::traffic_state(p, chts), msgs) == seq![coalesced(p, chts, msgs)],
{
    let t0 = crate::transcription::record::traffic_state(p, chts);
    assert(msgs =~= seq![msgs[0]]);
    lemma_concatenate_two(msgs[0], msgs[0]);
    assert(msgs.skip(1) =~= Seq::<Seq<u8>>::empty());
    let t1 = crate::transcription::record::TrafficState { sequence_number: t0.sequence_number + 1, ..t0 };
    assert(protect_each(p, t1, Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
    assert(seq![crate::transcription::record::protect_record(p, t0, 22, msgs[0])] + Seq::<Seq<u8>>::empty()
        =~= seq![crate::transcription::record::protect_record(p, t0, 22, msgs[0])]);
}

// ---------------------------------------------------------------------------
// The acknowledgement, and the step to CONNECTED.
// ---------------------------------------------------------------------------

/// §7.1, §7.3: acknowledging exactly the flight the crate asked to send
/// gives `Ready` with the application traffic secrets, and they are the
/// transcription's: its connection is the one A.1's last actions leave
/// ([`super::post_handshake::established`]), so the post-handshake
/// machine's `start` from them agrees with it
/// ([`super::post_handshake::post_agrees`]): the two theorems compose.
pub open spec fn ack_agrees(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, conn: Connection) -> bool
{
    let (a, s2) = crate::connection::dispatcher_spec::acknowledge(c, v, f, s, s.pending_flight);
    let app = crate::connection::post_handshake_spec::start(c, s2.client_application_secret, s2.server_application_secret);
    &&& a == Action::Ready
    &&& s2.mode == Mode::Ready
    &&& s2.client_application_secret.len() == 32
    &&& s2.server_application_secret.len() == 32
    &&& super::post_handshake::established(p, conn, s2.client_application_secret, s2.server_application_secret)
    &&& app is Ok
    &&& super::post_handshake::post_agrees(app->Ok_0, conn)
}

/// [`ack_agrees`], from the crate's state awaiting its flight and the
/// transcription's connection after the server Finished.
pub proof fn lemma_ack(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, conn: Connection, through: Seq<Seq<u8>>, retried: bool)
    requires
        hypotheses(c, v, f, p),
        s.mode == Mode::AwaitClientFlight,
        s.auth is Some,
        s.auth->Some_0.phase == crate::auth::spec::Phase::SendFinished,
        s.auth->Some_0.application_hash == crate::transcription::authentication::transcript_hash(p, through, retried),
        through.len() >= 1,
        conn.handshake.state == ClientState::Connected,
        conn.send == Protection::Protected(crate::transcription::record::traffic_state(p,
            crate::transcription::key_schedule::client_application_traffic_secret_0(p, s.master, through, retried))),
        conn.receive == Protection::Protected(crate::transcription::record::traffic_state(p,
            crate::transcription::key_schedule::server_application_traffic_secret_0(p, s.master, through, retried))),
        conn.handshake_fragments.len() == 0,
        !conn.read_closed,
        !conn.key_update_owed,
    ensures ack_agrees(c, v, f, p, s, conn),
{
    let a = s.auth->Some_0;
    let tr = crate::transcript::spec::State {
        messages: super::transcript::hashed_bytes(p, through, retried),
        phase: crate::transcript::spec::Phase::Handshake, retried };
    assert(super::transcript::represents(p, tr, through, retried));
    super::auth::lemma_hash_represents(p, tr, through, retried);
    super::keys::lemma_derive_on_transcript(c, p, s.master, crate::schedule::spec::Label::ClientApplication, tr, through, retried);
    super::keys::lemma_derive_on_transcript(c, p, s.master, crate::schedule::spec::Label::ServerApplication, tr, through, retried);
    let (act, s2) = crate::connection::dispatcher_spec::acknowledge(c, v, f, s, s.pending_flight);
    let cas = crate::schedule::spec::expand_label(c, s.master, crate::schedule::spec::Label::ClientApplication, a.application_hash, 32);
    let sas = crate::schedule::spec::expand_label(c, s.master, crate::schedule::spec::Label::ServerApplication, a.application_hash, 32);
    assert(s2.client_application_secret == cas);
    assert(s2.server_application_secret == sas);
    assert(cas == crate::transcription::key_schedule::client_application_traffic_secret_0(p, s.master, through, retried));
    assert(sas == crate::transcription::key_schedule::server_application_traffic_secret_0(p, s.master, through, retried));
    assert(cas.len() == 32);
    assert(sas.len() == 32);
    super::post_handshake::lemma_start(c, p, cas, sas, conn);
}

// ---------------------------------------------------------------------------
// The handshake messages of one record.
// ---------------------------------------------------------------------------

/// The transcription's processing of the handshake bytes `bf` aborts, and
/// `alert` is that of the failure it aborts on as [`message_fails`] compares
/// them, or §5.1's alignment failure (`unexpected_message`).
pub open spec fn fails_as(p: Primitives, hs: ClientHandshake, bf: Seq<u8>, alert: u8) -> bool
    decreases bf.len(),
{
    match crate::transcription::key_exchange::read_handshake_header(bf) {
        None => false,
        Some(h) => if bf.len() < 4 + h.length {
            false
        } else {
            let raw = bf.subrange(0, (4 + h.length) as int);
            let rest = bf.subrange((4 + h.length) as int, bf.len() as int);
            match crate::transcription::state_machine::receive_handshake_message(p, hs, raw) {
                HandshakeStep::Abort(e) => message_fails(hs, raw, e, alert),
                HandshakeStep::Proceed { handshake, receive_key_changes, .. } =>
                    if receive_key_changes && rest.len() != 0 {
                        alert == crate::spec::UNEXPECTED_MESSAGE
                    } else {
                        fails_as(p, handshake, rest, alert)
                    },
            }
        },
    }
}

/// **A stated difference: the crate's transcript cap** (4 MiB,
/// `transcript::spec::MAX_TRANSCRIPT`, `internal_error`). Along the
/// transcription's processing of the handshake bytes `bf`, it reaches a
/// message it accepts while the crate's transcript (the bytes the
/// transcription's list stands for, `transcript::hashed_bytes`) with that
/// message and the 48 octets of the client's own flight would pass 4 MiB.
/// The crate may refuse such a message with `internal_error`
/// (`auth::transcript_capped`), where the transcription has no failure:
/// §4's `uint24 length` allows it, and the cap is the crate's resource
/// policy (§6.2 `internal_error`: "unrelated to the peer or the
/// correctness of the protocol").
pub open spec fn transcript_cap(p: Primitives, hs: ClientHandshake, bf: Seq<u8>) -> bool
    decreases bf.len(),
{
    match crate::transcription::key_exchange::read_handshake_header(bf) {
        None => false,
        Some(h) => if bf.len() < 4 + h.length {
            false
        } else {
            let raw = bf.subrange(0, (4 + h.length) as int);
            let rest = bf.subrange((4 + h.length) as int, bf.len() as int);
            match crate::transcription::state_machine::receive_handshake_message(p, hs, raw) {
                HandshakeStep::Abort(_) => false,
                HandshakeStep::Proceed { handshake, receive_key_changes, .. } =>
                    super::transcript::hashed_bytes(p, hs.transcript, hs.retry is Some).len() + raw.len() + 48
                        > crate::transcript::spec::MAX_TRANSCRIPT
                    || (!(receive_key_changes && rest.len() != 0) && transcript_cap(p, handshake, rest)),
            }
        },
    }
}

/// [`transcript_cap`] on its first whole message.
pub proof fn lemma_cap_first(p: Primitives, hs: ClientHandshake, bf: Seq<u8>, n: nat)
    requires
        4 <= n <= bf.len(),
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length == n,
    ensures ({
        let raw = bf.subrange(0, n as int);
        let rest = bf.subrange(n as int, bf.len() as int);
        transcript_cap(p, hs, bf) == match crate::transcription::state_machine::receive_handshake_message(p, hs, raw) {
            HandshakeStep::Abort(_) => false,
            HandshakeStep::Proceed { handshake, receive_key_changes, .. } =>
                super::transcript::hashed_bytes(p, hs.transcript, hs.retry is Some).len() + raw.len() + 48
                    > crate::transcript::spec::MAX_TRANSCRIPT
                || (!(receive_key_changes && rest.len() != 0) && transcript_cap(p, handshake, rest)),
        }
    }),
{
}

/// What the crate sends on the server Finished and the transcription's
/// records agree: the transcription is in CONNECTED with the client's
/// flight as the last messages of its transcript; its records are each
/// message under the client handshake key ([`protect_each`]); the crate's
/// bytes are D.4's dummy change_cipher_spec, if the transcription writes it
/// before these records (`middlebox::before_second_flight`), and then the
/// flight [`coalesced`] in one record, which with no CertificateRequest is
/// exactly the transcription's batch; the crate awaits that acknowledgement
/// with the dummy record no longer owed; and acknowledging it agrees
/// ([`ack_agrees`]).
pub open spec fn sent_agrees(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, cl: ClientConnection, pr: Progress, wire: Seq<u8>, s2: State) -> bool
{
    let conn = pr.connection;
    let hs2 = conn.handshake;
    let msgs = client_flight(hs2);
    let chts = hs2.client_handshake_traffic_secret;
    &&& hs2.state == ClientState::Connected
    &&& pr.application_data.len() == 0
    &&& pr.records_to_send == protect_each(p, crate::transcription::record::traffic_state(p, chts), msgs)
    &&& wire == super::ccs::flatten(crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
        cl.change_cipher_spec_sent, seq![coalesced(p, chts, msgs)]).0)
    &&& (msgs.len() == 1 ==> wire == super::ccs::flatten(crate::transcription::middlebox::before_second_flight(
        cl.compatibility_mode, cl.change_cipher_spec_sent, pr.records_to_send).0))
    &&& s2.mode == Mode::AwaitClientFlight
    &&& s2.pending_flight == wire
    &&& !s2.ccs_pending
    &&& ack_agrees(c, v, f, p, s2, conn)
}

/// The crate's processing of the complete messages of a record
/// (`run_messages`) and the transcription's (`process_handshake_bytes` of
/// the same bytes `bf`) agree: both go on, the states agreeing and nothing
/// sent; or both reject, the transcription with a failure of which the
/// crate's alert is one ([`fails_as`]), the crate sending the
/// transcription's `alert_record` of its alert; or the crate sends its
/// flight and the transcription its records ([`sent_agrees`]).
pub open spec fn messages_agree(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>, r: (Action, State), t: Receive) -> bool
{
    match r.0 {
        Action::None => match t {
            Receive::Continue(pr) => {
                &&& pr.application_data.len() == 0
                &&& pr.records_to_send.len() == 0
                &&& dispatcher_agrees(p, v, r.1, ClientConnection { connection: pr.connection, ..cl })
            },
            _ => false,
        },
        Action::Fail(alert, w) => {
            &&& r.1 == crate::connection::dispatcher_spec::failed()
            &&& alert != 0 && alert != 90
            &&& w == Some(crate::transcription::connection::alert_record(p, cl.connection, alert as nat))
            &&& ((t is Abort && fails_as(p, cl.connection.handshake, bf, alert))
                || (alert == crate::spec::INTERNAL_ERROR && transcript_cap(p, cl.connection.handshake, bf)))
        },
        Action::Send(wire) => match t {
            Receive::Continue(pr) => sent_agrees(c, v, f, p, cl, pr, wire, r.1),
            _ => false,
        },
        _ => false,
    }
}

/// The transcription's `process_handshake_bytes` on its first whole
/// message: A.1's step, §5.1's alignment check on a key change, the actions,
/// then the rest of the buffer.
pub proof fn lemma_t_first(p: Primitives, y: Connection, bf: Seq<u8>, n: nat)
    requires
        4 <= n <= bf.len(),
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length == n,
    ensures ({
        let raw = bf.subrange(0, n as int);
        let rest = bf.subrange(n as int, bf.len() as int);
        crate::transcription::connection::process_handshake_bytes(p, y, bf)
            == match crate::transcription::state_machine::receive_handshake_message(p, y.handshake, raw) {
                HandshakeStep::Abort(e) => Receive::Abort(e),
                HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                    if receive_key_changes && rest.len() != 0 {
                        Receive::Abort(ClientError::KeyChangeNotAligned)
                    } else {
                        let (after, sent) = crate::transcription::connection::apply_actions(p,
                            Connection { handshake, ..y }, actions);
                        super::bootstrap::after_records(sent,
                            crate::transcription::connection::process_handshake_bytes(p, after, rest))
                    },
            }
    }),
{
}

/// [`fails_as`] on its first whole message.
pub proof fn lemma_fails_first(p: Primitives, hs: ClientHandshake, bf: Seq<u8>, n: nat, alert: u8)
    requires
        4 <= n <= bf.len(),
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length == n,
    ensures ({
        let raw = bf.subrange(0, n as int);
        let rest = bf.subrange(n as int, bf.len() as int);
        fails_as(p, hs, bf, alert) == match crate::transcription::state_machine::receive_handshake_message(p, hs, raw) {
            HandshakeStep::Abort(e) => message_fails(hs, raw, e, alert),
            HandshakeStep::Proceed { handshake, receive_key_changes, .. } =>
                if receive_key_changes && rest.len() != 0 {
                    alert == crate::spec::UNEXPECTED_MESSAGE
                } else {
                    fails_as(p, handshake, rest, alert)
                },
        }
    }),
{
}

/// A message's rejection never names a closure alert.
pub proof fn lemma_message_fails_alert(hs: ClientHandshake, m: Seq<u8>, e: ClientError, alert: u8)
    requires message_fails(hs, m, e, alert),
    ensures alert != 0 && alert != 90,
{
    if expected(hs.state, m[0]) {
        lemma_in_not_closure(alert, seq![e] + message_failures(hs, m));
    } else {
        match crate::spec::parse_handshake_body(m[0], m.skip(4), 32) {
            crate::spec::Res::Err(k) => { super::post_handshake::lemma_alert_of(k); },
            _ => {},
        }
    }
}

/// The crate's `run_messages` on its first message.
pub proof fn lemma_run_first(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    s: State, ms: Seq<Seq<u8>>)
    requires ms.len() > 0,
    ensures
        crate::connection::dispatcher_spec::run_messages(c, v, f, s, ms) == ({
            let (action, after) = crate::connection::dispatcher_spec::process_one(c, v, f, s, ms[0]);
            match action {
                Action::None => crate::connection::dispatcher_spec::run_messages(c, v, f, after, ms.skip(1)),
                _ => (action, after),
            }
        }),
{
}

/// §4.4.4, §5.1: a Finished that is not misplaced is the record's last
/// message, at a message boundary.
pub proof fn lemma_in_place(ms: Seq<Seq<u8>>, boundary: bool)
    requires
        ms.len() > 0,
        !crate::connection::dispatcher_spec::finished_out_of_place(ms, boundary),
    ensures
        !crate::connection::dispatcher_spec::finished_out_of_place(ms.skip(1), boundary),
        ms[0].len() > 0 && ms[0][0] == 20 ==> ms.len() == 1 && boundary,
{
}

/// The server Finished, the last message of its record at a message
/// boundary, accepted: the crate's flight and the transcription's records
/// agree ([`sent_agrees`]).
#[verifier::rlimit(80)]
pub proof fn lemma_send_case(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>)
    requires
        hypotheses(c, v, f, p),
        agrees_but_buffer(p, v, s, cl),
        s.reassembly.buf.len() == 0,
        bf.len() >= 4,
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length == bf.len(),
        crate::auth::spec::step(c, v, s.auth->Some_0, crate::auth::spec::Input::Handshake(bf[0], bf.skip(4))).1 is Send,
        message_agrees(p, s.auth->Some_0, cl.connection.handshake, bf,
            crate::auth::spec::step(c, v, s.auth->Some_0, crate::auth::spec::Input::Handshake(bf[0], bf.skip(4))),
            crate::transcription::state_machine::receive_handshake_message(p, cl.connection.handshake, bf)),
    ensures
        messages_agree(c, v, f, p, s, cl, bf, crate::connection::dispatcher_spec::run_messages(c, v, f, s, seq![bf]),
            crate::transcription::connection::process_handshake_bytes(p, cl.connection, bf)),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::transcription::connection::apply_actions);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(crate::transcription::key_schedule::client_application_traffic_secret_0);
    hide(crate::transcription::key_schedule::server_application_traffic_secret_0);
    hide(crate::transcription::key_schedule::master_secret);
    hide(crate::transcription::presentation::concatenate);
    hide(crate::transcription::record::protect_record);
    let y = cl.connection;
    let hs = y.handshake;
    let a = s.auth->Some_0;
    let rs = crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(bf[0], bf.skip(4)));
    let flight = rs.1->Send_0;
    let ts = crate::transcription::state_machine::receive_handshake_message(p, hs, bf);
    let h2 = ts->handshake;
    let msgs = client_flight(h2);
    let retried = hs.retry is Some;
    let master = crate::transcription::key_schedule::master_secret(p, hs.handshake_secret);
    let through = hs.transcript.push(bf);
    let cas = crate::transcription::key_schedule::client_application_traffic_secret_0(p, master, through, retried);
    let sas = crate::transcription::key_schedule::server_application_traffic_secret_0(p, master, through, retried);
    let chts = hs.client_handshake_traffic_secret;
    // The transcription: A.1's actions, then nothing left in the record.
    lemma_t_first(p, y, bf, bf.len());
    assert(bf.subrange(0, bf.len() as int) =~= bf);
    let rest = bf.subrange(bf.len() as int, bf.len() as int);
    assert(rest =~= Seq::<u8>::empty());
    assert(ts->actions == flight_actions(chts, msgs, cas, sas));
    let y2 = Connection { handshake: h2, ..y };
    lemma_apply_flight(p, y2, chts, msgs, cas, sas);
    let after = Connection {
        send: Protection::Protected(crate::transcription::record::traffic_state(p, cas)),
        receive: Protection::Protected(crate::transcription::record::traffic_state(p, sas)),
        ..y2
    };
    reveal(crate::transcription::connection::process_handshake_bytes);
    super::post_handshake::lemma_t_incomplete(p, after, rest);
    let conn = Connection { handshake_fragments: rest, ..after };
    let t0 = crate::transcription::record::traffic_state(p, chts);
    let sent = protect_each(p, t0, msgs);
    assert(sent + Seq::<Seq<u8>>::empty() =~= sent);
    let pr = Progress { connection: conn, application_data: seq![], records_to_send: sent };
    assert(crate::transcription::connection::process_handshake_bytes(p, y, bf) == Receive::Continue(pr));
    // The crate: its flight, sealed under the unused client handshake epoch.
    lemma_run_first(c, v, f, s, seq![bf]);
    assert(seq![bf][0] == bf);
    let stepped = State { auth: Some(rs.0), ..s };
    assert(crate::connection::dispatcher_spec::process_one(c, v, f, s, bf)
        == crate::connection::dispatcher_spec::send_flight(f, stepped, flight));
    let tx = s.handshake_sender->Some_0;
    lemma_seal(f, p, tx);
    assert(tx.next == Some(0u64));
    super::record::lemma_protect(p, crate::connection::dispatcher_spec::seal_with(f, tx), tx, t0, 22, flight);
    let rec = crate::transcription::record::protect_record(p, t0, 22, flight);
    assert(rec == coalesced(p, chts, msgs));
    super::ccs::lemma_ccs_bytes();
    let dummy = crate::transcription::middlebox::dummy_change_cipher_spec_record();
    super::ccs::lemma_flatten(dummy, rec);
    assert(seq![dummy] + seq![rec] =~= seq![dummy, rec]);
    if msgs.len() == 1 {
        lemma_one_message(p, chts, msgs);
    }
    let (act, s2) = crate::connection::dispatcher_spec::send_flight(f, stepped, flight);
    assert(s2.auth == Some(rs.0));
    assert(s2.master == s.master);
    lemma_ack(c, v, f, p, s2, conn, through, retried);
    let wire = act->Send_0;
    assert(conn.handshake == h2);
    assert(h2.state == ClientState::Connected);
    assert(pr.records_to_send == protect_each(p, crate::transcription::record::traffic_state(p, h2.client_handshake_traffic_secret), msgs));
    assert(wire == (if s.ccs_pending { crate::connection::dispatcher_spec::compatibility_ccs_record() + rec } else { rec }));
    super::ccs::lemma_flatten(rec, rec);
    if cl.compatibility_mode && !cl.change_cipher_spec_sent {
        assert(crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
            cl.change_cipher_spec_sent, seq![rec]).0 == seq![dummy] + seq![rec]);
    } else {
        assert(crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
            cl.change_cipher_spec_sent, seq![rec]).0 == seq![rec]);
    }
    assert(wire == super::ccs::flatten(crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
        cl.change_cipher_spec_sent, seq![coalesced(p, chts, msgs)]).0));
    assert(msgs.len() == 1 ==> wire == super::ccs::flatten(crate::transcription::middlebox::before_second_flight(
        cl.compatibility_mode, cl.change_cipher_spec_sent, pr.records_to_send).0));
    assert(s2.mode == Mode::AwaitClientFlight);
    assert(s2.pending_flight == wire);
    assert(!s2.ccs_pending);
    assert(sent_agrees(c, v, f, p, cl, pr, act->Send_0, s2));
}

/// The step of [`lemma_messages`] past a message both sides accept with no
/// action: what holds for the rest of the buffer holds for the buffer.
#[verifier::rlimit(40)]
pub proof fn lemma_messages_more(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>, n: nat, s2: State, h2: ClientHandshake,
    r: (Action, State), t: Receive)
    requires
        4 <= n <= bf.len(),
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length == n,
        crate::transcription::state_machine::receive_handshake_message(p, cl.connection.handshake, bf.subrange(0, n as int))
            is Proceed,
        crate::transcription::state_machine::receive_handshake_message(p, cl.connection.handshake, bf.subrange(0, n as int))->handshake
            == h2,
        !crate::transcription::state_machine::receive_handshake_message(p, cl.connection.handshake, bf.subrange(0, n as int))
            ->receive_key_changes,
        in_flight(cl.connection.handshake.state),
        in_flight(h2.state),
        h2.client_handshake_traffic_secret == cl.connection.handshake.client_handshake_traffic_secret,
        messages_agree(c, v, f, p, s2, ClientConnection { connection: Connection { handshake: h2, ..cl.connection }, ..cl },
            bf.subrange(n as int, bf.len() as int), r, t),
    ensures
        messages_agree(c, v, f, p, s, cl, bf, r, super::bootstrap::after_records(Seq::<Seq<u8>>::empty(), t)),
{
    let y = cl.connection;
    let y2 = Connection { handshake: h2, ..y };
    let cl2 = ClientConnection { connection: y2, ..cl };
    let rest = bf.subrange(n as int, bf.len() as int);
    lemma_fails_first(p, y.handshake, bf, n, match r.0 { Action::Fail(a, _) => a, _ => 0u8 });
    lemma_cap_first(p, y.handshake, bf, n);
    match t {
        Receive::Continue(pr) => {
            assert(Seq::<Seq<u8>>::empty() + pr.records_to_send =~= pr.records_to_send);
            assert(super::bootstrap::after_records(Seq::<Seq<u8>>::empty(), t) == t);
            assert forall|cn: Connection| ClientConnection { connection: cn, ..cl2 } == ClientConnection { connection: cn, ..cl } by {}
        },
        _ => {},
    }
    match r.0 {
        Action::Fail(alert, w) => {
            lemma_alert_record_kept(p, y, y2, alert as nat);
        },
        _ => {},
    }
}

/// §4, §5.1, A.1: the crate's `run_messages` on the complete messages of a
/// buffer and the transcription's `process_handshake_bytes` of it agree
/// ([`messages_agree`]), the crate's reassembly state being the bytes after
/// them, and no Finished out of place.
#[verifier::rlimit(80)]
pub proof fn lemma_messages(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>)
    requires
        hypotheses(c, v, f, p),
        agrees_but_buffer(p, v, s, cl),
        crate::spec::extract_messages(bf) is Ok,
        s.reassembly.buf == crate::spec::extract_messages(bf)->Ok_0.1,
        !crate::connection::dispatcher_spec::finished_out_of_place(crate::spec::extract_messages(bf)->Ok_0.0,
            s.reassembly.buf.len() == 0),
    ensures
        messages_agree(c, v, f, p, s, cl, bf,
            crate::connection::dispatcher_spec::run_messages(c, v, f, s, crate::spec::extract_messages(bf)->Ok_0.0),
            crate::transcription::connection::process_handshake_bytes(p, cl.connection, bf)),
    decreases bf.len(),
{
    hide(crate::connection::dispatcher_spec::run_messages);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(messages_agree);
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::extract_messages);
    hide(fails_as);
    hide(transcript_cap);
    hide(crate::connection::dispatcher_spec::finished_out_of_place);
    let y = cl.connection;
    let (ms, r) = crate::spec::extract_messages(bf)->Ok_0;
    super::bootstrap::lemma_extract(bf);
    if ms.len() == 0 {
        assert(ms =~= Seq::<Seq<u8>>::empty());
        reveal(crate::connection::dispatcher_spec::run_messages);
        reveal(crate::transcription::connection::process_handshake_bytes);
        super::post_handshake::lemma_t_incomplete(p, y, bf);
        reveal(messages_agree);
        let y2 = Connection { handshake_fragments: bf, ..y };
        assert(agrees_but_buffer(p, v, s, ClientConnection { connection: y2, ..cl }));
    } else {
        super::post_handshake::lemma_extract_more(bf);
        let n = super::bootstrap::first_length(bf);
        let m = ms[0];
        let rest = bf.subrange(n as int, bf.len() as int);
        assert(rest =~= bf.skip(n as int));
        let a = s.auth->Some_0;
        let hs = y.handshake;
        assert(m.subrange(1, 4) =~= bf.subrange(1, 4));
        assert(m.skip(4).len() == n - 4);
        lemma_message(c, v, p, a, hs, m);
        lemma_cap_first(p, hs, bf, n);
        lemma_t_first(p, y, bf, n);
        lemma_run_first(c, v, f, s, ms);
        lemma_in_place(ms, r.len() == 0);
        let rs = crate::auth::spec::step(c, v, a, crate::auth::spec::Input::Handshake(m[0], m.skip(4)));
        let ts = crate::transcription::state_machine::receive_handshake_message(p, hs, m);
        let stepped = State { auth: Some(rs.0), ..s };
        assert(super::auth::phase_is(a.phase, hs.state));
        match rs.1 {
            crate::auth::spec::Action::Fail(alert) => {
                if ts is Abort {
                    lemma_message_fails_alert(hs, m, ts->Abort_0, alert);
                } else {
                    assert(super::auth::transcript_capped(a, m.skip(4), rs, ts));
                    assert(a.transcript.messages == super::transcript::hashed_bytes(p, hs.transcript, hs.retry is Some));
                    assert(transcript_cap(p, hs, bf));
                }
                lemma_fatal(f, p, stepped, y, alert);
                lemma_fails_first(p, hs, bf, n, alert);
                reveal(messages_agree);
            },
            crate::auth::spec::Action::None => {
                let h2 = ts->handshake;
                let y2 = Connection { handshake: h2, ..y };
                let cl2 = ClientConnection { connection: y2, ..cl };
                super::post_handshake::lemma_apply_none(p, y2);
                assert(Connection { handshake: h2, ..y } == y2);
                assert(super::auth::phase_is(rs.0.phase, h2.state));
                assert(agrees_but_buffer(p, v, stepped, cl2));
                assert(crate::spec::extract_messages(rest) == crate::spec::Res::Ok((ms.skip(1), r)));
                lemma_messages(c, v, f, p, stepped, cl2, rest);
                let rr = crate::connection::dispatcher_spec::run_messages(c, v, f, stepped, ms.skip(1));
                let tt = crate::transcription::connection::process_handshake_bytes(p, y2, rest);
                lemma_messages_more(c, v, f, p, s, cl, bf, n, stepped, h2, rr, tt);
            },
            crate::auth::spec::Action::Send(flight) => {
                assert(ms.len() == 1 && r.len() == 0);
                assert(bf.len() == n);
                assert(m =~= bf);
                assert(ms =~= seq![bf]);
                lemma_send_case(c, v, f, p, s, cl, bf);
            },
            _ => {},
        }
    }
}

// ---------------------------------------------------------------------------
// One record.
// ---------------------------------------------------------------------------

/// **A stated difference: a Finished out of place.** The crate refuses a
/// record whose messages include a Finished that is not the record's last
/// message at a message boundary with `unexpected_message`, before any of
/// its messages reaches authentication (`dispatcher_spec::process_messages`:
/// §5.1, "Handshake messages MUST NOT span key changes", and the key changes
/// after the server Finished). The transcription processes the messages in
/// order and aborts at the first that fails, at the latest at that Finished
/// (§5.1's alignment check, `KeyChangeNotAligned`): both reject
/// ([`lemma_finished_aborts`]), and when an earlier message also fails the
/// two name different faults. The RFC ranks neither.
pub open spec fn finished_first(bf: Seq<u8>) -> bool {
    crate::spec::extract_messages(bf) matches crate::spec::Res::Ok((ms, r))
        && crate::connection::dispatcher_spec::finished_out_of_place(ms, r.len() == 0)
}

/// The handshake bytes a record completes: the crate's reassembly buffer
/// and the record's decrypted content, when the record is a handshake
/// record under the server handshake key.
pub open spec fn handshake_bytes(f: Ciphers, s: State, b: Seq<u8>) -> Option<Seq<u8>> {
    let rx = s.handshake_receiver->Some_0;
    match crate::traffic::spec::receive(crate::connection::dispatcher_spec::open_with(f, rx), rx, b).1 {
        crate::traffic::spec::Read::Record(typ, x, _) => if typ == 22 { Some(s.reassembly.buf + x) } else { None },
        _ => None,
    }
}

/// When the crate fails with `alert` on record `b`: the transcription aborts
/// with that alert; or both reject and a stated difference holds
/// ([`super::post_handshake::two_faults`], [`finished_first`]); or the
/// crate's alert is that of a failure of the message the transcription
/// aborts on ([`fails_as`], the membership comparison); or the crate's 2^18
/// handshake-message cap fired (`internal_error`; §4's `uint24 length`
/// allows the message and the transcription has no cap); or its 4 MiB
/// transcript cap refused a message the transcription accepts
/// ([`transcript_cap`], `internal_error` too).
pub open spec fn fail_agrees(f: Ciphers, p: Primitives, s: State, y: Connection, b: Seq<u8>, t: Receive, alert: u8) -> bool {
    ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == alert as nat
    ||| t is Abort && super::post_handshake::two_faults(b)
    ||| t is Abort && (handshake_bytes(f, s, b) matches Some(bf)
        && (fails_as(p, y.handshake, bf, alert) || finished_first(bf)))
    ||| alert == crate::spec::INTERNAL_ERROR && (handshake_bytes(f, s, b) matches Some(bf)
        && crate::spec::extract_messages(bf) is Err)
    ||| alert == crate::spec::INTERNAL_ERROR && (handshake_bytes(f, s, b) matches Some(bf)
        && transcript_cap(p, y.handshake, bf))
}

/// What the crate does with a record (`a`, `s2`) and what the
/// transcription does (`t`) agree:
/// - the crate goes on with no effect (nothing to do, a dropped
///   change_cipher_spec, a user_canceled): so does the transcription, with
///   nothing sent or delivered, and the states agree;
/// - the crate sends its flight: [`sent_agrees`];
/// - the crate fails: every key is dropped, its alert record is the
///   transcription's `alert_record` of its alert, and `failed` (the
///   transcription aborts as [`fail_agrees`] says);
/// - the peer's error alert: `PeerError` with the same description;
/// - **a stated difference, the peer's close_notify during its flight**
///   (§6.1): the transcription stops reading (`read_closed`) and keeps its
///   write side, its own close_notify being the separate `close_write`, so
///   its handshake can no longer complete; the crate closes at once,
///   sending exactly that `close_write` record, and drops every key.
pub open spec fn outcome_agrees(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, a: Action, s2: State, t: Receive, failed: bool) -> bool
{
    let y = cl.connection;
    match a {
        Action::None | Action::Ignored | Action::Cancelled => match t {
            Receive::Continue(pr) => {
                &&& pr.application_data.len() == 0
                &&& pr.records_to_send.len() == 0
                &&& dispatcher_agrees(p, v, s2, ClientConnection { connection: pr.connection, ..cl })
            },
            _ => false,
        },
        Action::Send(wire) => match t {
            Receive::Continue(pr) => sent_agrees(c, v, f, p, cl, pr, wire, s2),
            _ => false,
        },
        Action::Fail(alert, w) => {
            &&& s2 == crate::connection::dispatcher_spec::failed()
            &&& alert != 0 && alert != 90
            &&& w == Some(crate::transcription::connection::alert_record(p, y, alert as nat))
            &&& failed
        },
        Action::PeerAlert(d) => {
            &&& s2 == crate::connection::dispatcher_spec::failed()
            &&& t == Receive::PeerError(d as nat)
        },
        Action::Close(w) => {
            &&& s2 == crate::connection::dispatcher_spec::closed()
            &&& w == Some(crate::transcription::connection::close_write(p, y))
            &&& t is Continue
            &&& t->Continue_0.connection.read_closed
            &&& t->Continue_0.connection.handshake == y.handshake
            &&& t->Continue_0.application_data.len() == 0
            &&& t->Continue_0.records_to_send.len() == 0
        },
        Action::Ready => false,
    }
}

/// `connection::receive_stream`'s result as `middlebox::client_receive_stream`
/// gives it: D.4's dummy record before the client's second flight.
pub open spec fn lifted(cl: ClientConnection, t: Receive) -> ClientReceive {
    match t {
        Receive::Abort(e) => ClientReceive::Abort(e),
        Receive::PeerError(d) => ClientReceive::PeerError(d),
        Receive::Continue(progress) => {
            let (records, sent) = crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
                cl.change_cipher_spec_sent, progress.records_to_send);
            ClientReceive::Continue { client: ClientConnection { connection: progress.connection,
                change_cipher_spec_sent: sent, ..cl }, application_data: progress.application_data,
                records_to_send: records }
        },
    }
}

/// The crate's step on one whole record `b` (`dispatcher_spec::receive_record`,
/// which `feed` runs on every record its framer completes:
/// [`lemma_feed_complete`]) and the transcription's
/// `middlebox::client_receive_stream` of it agree: the transcription's result
/// is its `one_record` with D.4's dummy record ([`lifted`]), and
/// [`outcome_agrees`] with [`fail_agrees`] for a failure.
pub open spec fn record_agrees(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>) -> bool
{
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s, b);
    let t = super::bootstrap::one_record(p, cl.connection, b);
    &&& crate::transcription::middlebox::client_receive_stream(p, cl, b).0 == lifted(cl, t)
    &&& outcome_agrees(c, v, f, p, s, cl, a, s2, t, match a {
        Action::Fail(alert, _) => fail_agrees(f, p, s, cl.connection, b, t, alert),
        _ => true,
    })
}

/// The transcription aborts on handshake bytes holding a Finished out of
/// place (the second half of [`finished_first`]).
#[verifier::rlimit(40)]
pub proof fn lemma_finished_aborts(p: Primitives, y: Connection, bf: Seq<u8>)
    requires
        in_flight(y.handshake.state),
        crate::spec::extract_messages(bf) is Ok,
        crate::connection::dispatcher_spec::finished_out_of_place(crate::spec::extract_messages(bf)->Ok_0.0,
            crate::spec::extract_messages(bf)->Ok_0.1.len() == 0),
    ensures crate::transcription::connection::process_handshake_bytes(p, y, bf) is Abort,
    decreases bf.len(),
{
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::extract_messages);
    let (ms, r) = crate::spec::extract_messages(bf)->Ok_0;
    super::bootstrap::lemma_extract(bf);
    if ms.len() > 0 {
        super::post_handshake::lemma_extract_more(bf);
        let n = super::bootstrap::first_length(bf);
        let m = ms[0];
        let rest = bf.subrange(n as int, bf.len() as int);
        assert(rest =~= bf.skip(n as int));
        lemma_t_first(p, y, bf, n);
        lemma_t_step(p, y.handshake, m);
        let ts = crate::transcription::state_machine::receive_handshake_message(p, y.handshake, m);
        if ts is Proceed {
            if y.handshake.state == ClientState::WaitFinished && m[0] == 20 {
                if rest.len() == 0 {
                    assert(bf.len() == n);
                    assert(ms.len() == 1 && r.len() == 0);
                    assert(ms.skip(1) =~= Seq::<Seq<u8>>::empty());
                    assert(!crate::connection::dispatcher_spec::finished_out_of_place(ms.skip(1), true));
                    assert(!crate::connection::dispatcher_spec::finished_out_of_place(ms, true));
                }
            } else {
                assert(m[0] != 20);
                assert(ts->actions =~= Seq::<crate::transcription::state_machine::Action>::empty());
                assert(!ts->receive_key_changes);
                assert(!crate::connection::dispatcher_spec::finished_out_of_place(seq![m].take(0), r.len() == 0));
                assert(crate::connection::dispatcher_spec::finished_out_of_place(ms.skip(1), r.len() == 0));
                let y2 = Connection { handshake: ts->handshake, ..y };
                super::post_handshake::lemma_apply_none(p, y2);
                assert(crate::spec::extract_messages(rest) == crate::spec::Res::Ok((ms.skip(1), r)));
                lemma_finished_aborts(p, y2, rest);
            }
        }
    } else {
        assert(ms =~= Seq::<Seq<u8>>::empty());
    }
}

/// §5, §5.1, §5.2: the header of one whole record, read by the crate's
/// protected framer and by the transcription in WAIT_EE to WAIT_FINISHED.
/// A change_cipher_spec of the single byte 0x01 is dropped at a message
/// boundary and refused inside a fragmented message (§5, §5.1; Appendix
/// D.4); a TLSCiphertext goes on to `receive_ciphertext`; every other record
/// is refused on both sides, with the same alert or as
/// [`super::post_handshake::two_faults`].
pub proof fn lemma_frame(p: Primitives, c: Connection, b: Seq<u8>)
    requires
        super::bootstrap::whole_record(b),
        c.receive is Protected,
        in_flight(c.handshake.state),
        !c.read_closed,
    ensures ({
        let t = super::bootstrap::one_record(p, c, b);
        match crate::spec::read_record(b, true) {
            crate::spec::Read::Fail(k) => t is Abort
                && (crate::transcription::alerts::required_alert(t->Abort_0) == crate::spec::alert_of(k) as nat
                    || super::post_handshake::two_faults(b)),
            crate::spec::Read::Done(crate::spec::Frame::Ccs, rest) => t == if c.handshake_fragments.len() != 0 {
                Receive::Abort(ClientError::InterleavedRecord)
            } else {
                Receive::Continue(Progress { connection: c, application_data: seq![], records_to_send: seq![] })
            },
            crate::spec::Read::Done(crate::spec::Frame::Protected(h, e), rest) => {
                &&& b[0] == crate::spec::CT_APPLICATION_DATA
                &&& rest.len() == 0
                &&& super::record::is_protected_record(b)
                &&& t == crate::transcription::connection::receive_ciphertext(p, c, c.receive->Protected_0,
                    crate::transcription::record::read_record_header(b)->Some_0.legacy_record_version,
                    b.subrange(5, b.len() as int).take(
                        crate::transcription::record::read_record_header(b)->Some_0.length as int))
            },
            crate::spec::Read::Done(_, _) => false,
            crate::spec::Read::NeedMore => false,
        }
    }),
{
    super::bootstrap::lemma_header(b);
    let len = super::bootstrap::length(b);
    assert(b.subrange(5, b.len() as int).take(len as int) =~= super::bootstrap::fragment(b));
    assert(b.subrange(5, (5 + len) as int) =~= super::bootstrap::fragment(b));
    if b[0] == 20 && len <= crate::spec::MAX_PLAINTEXT {
        if super::bootstrap::fragment(b) == seq![1u8] {
            assert(super::bootstrap::fragment(b) =~= seq![0x01u8]);
        }
    }
}

/// [`outcome_agrees`] carries over from the states after the record's
/// deprotection (the read sequence numbers moved on) to the states before.
pub proof fn lemma_outcome_transfer(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, s1: State, y1: Connection, a: Action, s2: State, t: Receive,
    failed: bool)
    requires
        y1.handshake == cl.connection.handshake,
        in_flight(cl.connection.handshake.state),
        outcome_agrees(c, v, f, p, s1, ClientConnection { connection: y1, ..cl }, a, s2, t, failed),
    ensures
        outcome_agrees(c, v, f, p, s, cl, a, s2, t, failed),
{
    let cl1 = ClientConnection { connection: y1, ..cl };
    assert forall|cn: Connection| ClientConnection { connection: cn, ..cl1 } == ClientConnection { connection: cn, ..cl } by {}
    match a {
        Action::Fail(alert, w) => { lemma_alert_record_kept(p, y1, cl.connection, alert as nat); },
        Action::Close(w) => { lemma_alert_record_kept(p, y1, cl.connection, 0); },
        _ => {},
    }
}

/// §5.1, §5.4, §6, A.1: the content of a record under the server handshake
/// key, the crate's `receive_plaintext` against the transcription's
/// `receive_protected_content`, for every type and content the crate's
/// inner-plaintext check lets through.
#[verifier::rlimit(80)]
pub proof fn lemma_content(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, typ: u8, x: Seq<u8>)
    requires
        hypotheses(c, v, f, p),
        dispatcher_agrees(p, v, s, cl),
        typ == 21 || typ == 22 || typ == 23,
        x.len() <= crate::spec::MAX_PLAINTEXT,
        typ != 23 ==> x.len() > 0,
    ensures ({
        let (a, s2) = crate::connection::dispatcher_spec::receive_plaintext(c, v, f, s, typ, x);
        let t = crate::transcription::connection::receive_protected_content(p, cl.connection, typ as nat, x);
        let bf = s.reassembly.buf + x;
        outcome_agrees(c, v, f, p, s, cl, a, s2, t, {
            ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == a->Fail_0 as nat
            ||| typ == 22 && t is Abort && (fails_as(p, cl.connection.handshake, bf, a->Fail_0) || finished_first(bf))
            ||| typ == 22 && a->Fail_0 == crate::spec::INTERNAL_ERROR && crate::spec::extract_messages(bf) is Err
            ||| typ == 22 && a->Fail_0 == crate::spec::INTERNAL_ERROR && transcript_cap(p, cl.connection.handshake, bf)
        })
    }),
{
    hide(crate::connection::dispatcher_spec::run_messages);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(messages_agree);
    hide(fails_as);
    let y = cl.connection;
    assert(super::auth::phase_is(s.auth->Some_0.phase, y.handshake.state));
    assert(ClientConnection { connection: y, ..cl } == cl);
    if typ == 23 {
        lemma_fatal(f, p, s, y, 10);
    } else if typ == 21 {
        if s.reassembly.buf.len() > 0 {
            lemma_fatal(f, p, s, y, 10);
        } else if x.len() != 2 {
            lemma_fatal(f, p, s, y, 50);
        } else {
            let d = x[1];
            if d == 0 {
                lemma_closing(f, p, s, y);
            } else if d == 90 {
            } else {
            }
        }
    } else {
        let bf = s.reassembly.buf + x;
        super::bootstrap::lemma_extract(bf);
        match crate::spec::extract_messages(bf) {
            crate::spec::Res::Err(e) => {
                lemma_fatal(f, p, s, y, 80);
            },
            crate::spec::Res::Ok((ms, r)) => {
                let s3 = State { reassembly: crate::spec::Reasm { buf: r }, ..s };
                if crate::connection::dispatcher_spec::finished_out_of_place(ms, r.len() == 0) {
                    lemma_fatal(f, p, s3, y, 10);
                    lemma_finished_aborts(p, y, bf);
                } else {
                    assert(agrees_but_buffer(p, v, s3, cl));
                    lemma_messages(c, v, f, p, s3, cl, bf);
                    reveal(messages_agree);
                }
            },
        }
    }
}

/// §5, §5.1 to §5.4, §6, A.1: one whole record in the server's flight: the
/// crate's `receive_record` against the transcription's `receive_stream`
/// (with D.4's wrapper, `client_receive_stream`).
#[verifier::rlimit(80)]
pub proof fn lemma_receive(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>)
    requires
        hypotheses(c, v, f, p),
        dispatcher_agrees(p, v, s, cl),
        super::bootstrap::whole_record(b),
    ensures record_agrees(c, v, f, p, s, cl, b),
{
    hide(crate::connection::dispatcher_spec::receive_plaintext);
    hide(crate::transcription::connection::receive_protected_content);
    hide(crate::transcription::connection::receive_stream);
    hide(outcome_agrees);
    hide(dispatcher_agrees);
    let y = cl.connection;
    assert(super::auth::phase_is(s.auth->Some_0.phase, y.handshake.state)) by { reveal(dispatcher_agrees); }
    assert(receiver_agrees(s, y) && sender_fresh(p, s, y) && !y.read_closed && s.mode == Mode::Handshake
        && s.auth is Some) by { reveal(dispatcher_agrees); }
    super::bootstrap::lemma_stream_one(p, y, b);
    lemma_frame(p, y, b);
    let rx = s.handshake_receiver->Some_0;
    let tr = y.receive->Protected_0;
    lemma_seal(f, p, rx);
    let t = super::bootstrap::one_record(p, y, b);
    match crate::spec::read_record(b, true) {
        crate::spec::Read::Fail(k) => {
            super::post_handshake::lemma_alert_of(k);
            lemma_fatal(f, p, s, y, crate::spec::alert_of(k));
            reveal(outcome_agrees);
            assert(crate::transcription::middlebox::client_receive_stream(p, cl, b).0 == lifted(cl, t));
            assert(record_agrees(c, v, f, p, s, cl, b));
        },
        crate::spec::Read::Done(crate::spec::Frame::Ccs, rest) => {
            reveal(outcome_agrees);
            reveal(dispatcher_agrees);
            if s.reassembly.buf.len() > 0 {
                lemma_fatal(f, p, s, y, 10);
            } else {
                assert(ClientConnection { connection: y, ..cl } == cl);
            }
            assert(record_agrees(c, v, f, p, s, cl, b));
        },
        crate::spec::Read::Done(crate::spec::Frame::Protected(h, e), rest) => {
            super::record::lemma_deprotect(p, crate::connection::dispatcher_spec::open_with(f, rx), rx, y, tr, b);
            let read = crate::traffic::spec::receive(crate::connection::dispatcher_spec::open_with(f, rx), rx, b);
            let opened = State { handshake_receiver: Some(read.0), ..s };
            match read.1 {
                crate::traffic::spec::Read::Fail(a) => {
                    lemma_required_not_closure(t->Abort_0);
                    lemma_fatal(f, p, opened, y, a);
                    reveal(outcome_agrees);
                    assert(record_agrees(c, v, f, p, s, cl, b));
                },
                crate::traffic::spec::Read::Record(typ, x, used) => {
                    let n = rx.next->Some_0;
                    let open = crate::connection::dispatcher_spec::open_with(f, rx);
                    let inner = open(crate::spec::per_record_nonce(rx.iv, n), h, e)->Some_0;
                    super::post_handshake::lemma_inner_ok(inner);
                    super::post_handshake::lemma_advance(rx, tr);
                    let y1 = Connection {
                        receive: Protection::Protected(crate::transcription::record::TrafficState {
                            sequence_number: tr.sequence_number + 1, ..tr }),
                        ..y
                    };
                    let cl1 = ClientConnection { connection: y1, ..cl };
                    assert(dispatcher_agrees(p, v, opened, cl1)) by { reveal(dispatcher_agrees); }
                    lemma_content(c, v, f, p, opened, cl1, typ, x);
                    let (a2, s2) = crate::connection::dispatcher_spec::receive_plaintext(c, v, f, opened, typ, x);
                    let t1 = crate::transcription::connection::receive_protected_content(p, y1, typ as nat, x);
                    assert(t == t1);
                    assert(opened.reassembly == s.reassembly);
                    let failed = (t1 is Abort && crate::transcription::alerts::required_alert(t1->Abort_0) == a2->Fail_0 as nat)
                        || (typ == 22 && t1 is Abort && (fails_as(p, y1.handshake, opened.reassembly.buf + x, a2->Fail_0)
                            || finished_first(opened.reassembly.buf + x)))
                        || (typ == 22 && a2->Fail_0 == crate::spec::INTERNAL_ERROR
                            && crate::spec::extract_messages(opened.reassembly.buf + x) is Err)
                        || (typ == 22 && a2->Fail_0 == crate::spec::INTERNAL_ERROR
                            && transcript_cap(p, y1.handshake, opened.reassembly.buf + x));
                    lemma_outcome_transfer(c, v, f, p, s, cl, opened, y1, a2, s2, t, failed);
                    assert(crate::connection::dispatcher_spec::receive_record(c, v, f, s, b) == (a2, s2));
                    assert(handshake_bytes(f, s, b) == if typ == 22 { Some(s.reassembly.buf + x) } else { None::<Seq<u8>> });
                    assert(a2 is Fail ==> (failed ==> fail_agrees(f, p, s, y, b, t, a2->Fail_0)));
                    assert(record_agrees(c, v, f, p, s, cl, b)) by { reveal(outcome_agrees); }
                },
                crate::traffic::spec::Read::NeedMore => {},
            }
        },
        crate::spec::Read::Done(_, _) => {},
        crate::spec::Read::NeedMore => {},
    }
}

/// `feed` on bytes that complete a record is [`record_agrees`]'s
/// `receive_record` of exactly that record (with the framer emptied), after
/// consuming the bytes the framer took. When the framer completes a record
/// is `framing_spec`'s (not compared here: the crate decides on a record's
/// type and length as soon as its header has arrived).
pub proof fn lemma_feed_complete(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification, f: Ciphers,
    s: State, input: Seq<u8>)
    requires
        s.mode == Mode::Handshake,
        crate::connection::framing_spec::feed(s.framing, input).status == crate::connection::framing_spec::Status::Complete,
    ensures ({
        let framed = crate::connection::framing_spec::feed(s.framing, input);
        let (action, after) = crate::connection::dispatcher_spec::receive_record(c, v, f,
            State { framing: seq![], ..s }, framed.buffer);
        crate::connection::dispatcher_spec::feed(c, v, f, s, input) == (framed.consumed, action, after)
    }),
{
}

// ---------------------------------------------------------------------------
// The start: the handoff after the ServerHello.
// ---------------------------------------------------------------------------

/// What the transcription holds when it accepts the ServerHello that the
/// crate hands on with `peer_key` and `transcript` (as
/// [`super::negotiation::receive_agrees`]'s `Established` case and
/// [`super::bootstrap::buffer_agrees`] give them): A.1's step on `raw` is
/// `accept_server_hello` of the parsed `sh`, whose key_share is the X25519
/// share `peer_key`; the crate's transcript stands for the transcription's
/// list with `raw`; the crate's private key is the transcription's; the
/// ClientHello offered the crate's signature schemes and extension types
/// (`join_spec::extension_types`, which `auth::spec::Config` keeps); and
/// the fields A.1 sets only from WAIT_EE on (the server's key, a
/// CertificateRequest context) are not yet set.
pub open spec fn accepts_server_hello(p: Primitives, c0: Connection, sh: crate::transcription::key_exchange::ServerHello,
    raw: Seq<u8>, config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State,
    peer_key: Seq<u8>, private_key: Seq<u8>) -> bool
{
    let hs0 = c0.handshake;
    &&& hs0.state == ClientState::WaitSh
    &&& crate::transcription::state_machine::receive_handshake_message(p, hs0, raw)
        == crate::transcription::state_machine::accept_server_hello(p, hs0, sh, raw)
    &&& crate::transcription::extensions::find_extension(sh.extensions, 51) is Some
    &&& crate::transcription::extensions::read_key_share_server_hello(
        crate::transcription::extensions::find_extension(sh.extensions, 51)->0)
        == Some(crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: peer_key })
    &&& super::transcript::represents(p, transcript, hs0.transcript.push(raw), hs0.retry is Some)
    &&& private_key == hs0.x25519_private_key
    &&& crate::transcription::key_exchange::offered_signature_schemes(hs0.hello) == super::auth::offered_schemes()
    &&& super::extensions::nats(crate::hello::join_spec::extension_types(config, transcript.retried))
        == crate::transcription::extensions::extension_types(hs0.hello.extensions)
    &&& hs0.server_public_key.len() == 0
    &&& hs0.certificate_request_context is None
    &&& c0.send == Protection::Unprotected
    &&& !c0.read_closed
    &&& !c0.key_update_owed
}

/// The start: from the crate's handoff (`handshake_spec::start`, then
/// `dispatcher_spec::start` with D.4's `needs_ccs`) and the transcription's
/// connection after it accepts the same ServerHello and applies A.1's "K_recv
/// = handshake" (`bootstrap::after_message`), with the dummy record still
/// owed exactly when the transcription has not written it: the states agree
/// ([`dispatcher_agrees`]).
#[verifier::rlimit(60)]
pub proof fn lemma_start(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    v: crate::auth::spec::Verification, f: Ciphers, p: Primitives, cl: ClientConnection, c0: Connection,
    sh: crate::transcription::key_exchange::ServerHello, raw: Seq<u8>, config: crate::hello::client_spec::Config,
    transcript: crate::transcript::spec::State, peer_key: Seq<u8>, private_key: Seq<u8>)
    requires
        hypotheses(c, v, f, p),
        super::keys::x25519_agrees(k, p),
        accepts_server_hello(p, c0, sh, raw, config, transcript, peer_key, private_key),
        super::auth_flight::chain_agrees(v, p, config.host, config.now),
        forall|body: Seq<u8>| #[trigger] (v.chain)(config.host, config.now, body) matches Ok(key)
            ==> key.len() <= crate::auth::spec::MAX_KEY,
        crate::traffic::handshake_spec::start(c, k, config, transcript, peer_key, private_key) is Ok,
        super::bootstrap::after_message(p, c0, raw) is Continue,
        cl.connection == super::bootstrap::after_message(p, c0, raw)->Continue_0.connection,
        crate::traffic::handshake_spec::needs_ccs(config, transcript)
            == (cl.compatibility_mode && !cl.change_cipher_spec_sent),
    ensures
        dispatcher_agrees(p, v, crate::connection::dispatcher_spec::start(
            crate::traffic::handshake_spec::start(c, k, config, transcript, peer_key, private_key)->Ok_0,
            crate::traffic::handshake_spec::needs_ccs(config, transcript)), cl),
{
    let hs0 = c0.handshake;
    let retried = hs0.retry is Some;
    let msgs = hs0.transcript.push(raw);
    let h = crate::traffic::handshake_spec::start(c, k, config, transcript, peer_key, private_key)->Ok_0;
    let (auth_config, master) = crate::hello::join_spec::derive(c, k, config, transcript, peer_key, private_key)->Ok_0;
    assert(crate::hello::join_spec::derive(c, k, config, transcript, peer_key, private_key) is Ok);
    assert(private_key.len() == 32 && (k.public_key)(private_key) == config.public_key);
    super::keys::theorem_handshake_keys_equivalence(c, k, p);
    assert(super::transcript::represents(p, transcript, msgs, retried));
    let shared = (p.x25519)(private_key, peer_key);
    let handshake = crate::transcription::key_schedule::handshake_secret(p,
        crate::transcription::key_schedule::early_secret(p, crate::transcription::primitives::zero_value()), shared);
    assert(!crate::transcription::presentation::all_zero(shared));
    assert(auth_config.server_secret == crate::transcription::key_schedule::server_handshake_traffic_secret(p, handshake, msgs, retried));
    assert(auth_config.client_secret == crate::transcription::key_schedule::client_handshake_traffic_secret(p, handshake, msgs, retried));
    assert(master == crate::transcription::key_schedule::master_secret(p, handshake));
    // The transcription's step.
    let step = crate::transcription::state_machine::accept_server_hello(p, hs0, sh, raw);
    assert(step is Proceed);
    let hs1 = step->handshake;
    assert(hs1.state == ClientState::WaitEe);
    assert(hs1.transcript == msgs);
    assert(hs1.handshake_secret == handshake);
    assert(hs1.client_handshake_traffic_secret == auth_config.client_secret);
    assert(hs1.server_handshake_traffic_secret == auth_config.server_secret);
    let shts = auth_config.server_secret;
    let a1 = seq![crate::transcription::state_machine::Action::SetReceiveSecret(shts)];
    assert(step->actions == a1);
    let y1 = Connection { handshake: hs1, ..c0 };
    let y2 = Connection { receive: Protection::Protected(crate::transcription::record::traffic_state(p, shts)), ..y1 };
    assert(a1.subrange(1, 1) =~= Seq::<crate::transcription::state_machine::Action>::empty());
    assert(crate::transcription::connection::apply_actions(p, y2, Seq::empty()) == (y2, Seq::<Seq<u8>>::empty()));
    assert(crate::transcription::connection::apply_actions(p, y1, a1) == (y2, Seq::<Seq<u8>>::empty()));
    // The crate's start.
    super::record::lemma_epoch_start(c, p, auth_config.client_secret);
    super::record::lemma_epoch_start(c, p, auth_config.server_secret);
    let s = crate::connection::dispatcher_spec::start(h, crate::traffic::handshake_spec::needs_ccs(config, transcript));
    let a = s.auth->Some_0;
    assert(a.config == auth_config);
    assert(a.transcript == transcript);
    assert(super::transcript::represents(p, a.transcript, hs1.transcript, hs1.retry is Some));
    assert(a.transcript.phase == crate::transcript::spec::Phase::Handshake);
    assert(a.key == hs1.server_public_key);
    assert(a.config.server_secret == hs1.server_handshake_traffic_secret);
    assert(a.config.client_secret == hs1.client_handshake_traffic_secret);
    assert(a.config.signatures == crate::hello::client_spec::signatures());
    assert(crate::transcription::key_exchange::offered_signature_schemes(hs1.hello) == super::auth::offered_schemes());
    assert(super::extensions::nats(a.config.extensions) == crate::transcription::extensions::extension_types(hs1.hello.extensions));
    assert(a.requested <==> hs1.certificate_request_context is Some);
    assert(super::auth::phase_is(a.phase, hs1.state));
    assert(super::auth::auth_agrees(p, a, hs1));
    assert(s.reassembly.buf =~= cl.connection.handshake_fragments);
}

/// The theorem's start, the conditions above packaged: every crate state
/// the handoff starts agrees with the transcription's connection after the
/// same ServerHello.
pub open spec fn start_agrees(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    v: crate::auth::spec::Verification, p: Primitives, cl: ClientConnection, c0: Connection,
    sh: crate::transcription::key_exchange::ServerHello, raw: Seq<u8>, config: crate::hello::client_spec::Config,
    transcript: crate::transcript::spec::State, peer_key: Seq<u8>, private_key: Seq<u8>) -> bool
{
    (accepts_server_hello(p, c0, sh, raw, config, transcript, peer_key, private_key)
        && super::auth_flight::chain_agrees(v, p, config.host, config.now)
        && (forall|body: Seq<u8>| #[trigger] (v.chain)(config.host, config.now, body) matches Ok(key)
            ==> key.len() <= crate::auth::spec::MAX_KEY)
        && crate::traffic::handshake_spec::start(c, k, config, transcript, peer_key, private_key) is Ok
        && super::bootstrap::after_message(p, c0, raw) is Continue
        && cl.connection == super::bootstrap::after_message(p, c0, raw)->Continue_0.connection
        && crate::traffic::handshake_spec::needs_ccs(config, transcript)
            == (cl.compatibility_mode && !cl.change_cipher_spec_sent))
    ==> dispatcher_agrees(p, v, crate::connection::dispatcher_spec::start(
        crate::traffic::handshake_spec::start(c, k, config, transcript, peer_key, private_key)->Ok_0,
        crate::traffic::handshake_spec::needs_ccs(config, transcript)), cl)
}

// ---------------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------------

/// [`start_agrees`], for every handoff.
pub proof fn lemma_start_agrees(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    v: crate::auth::spec::Verification, f: Ciphers, p: Primitives, cl: ClientConnection, c0: Connection,
    sh: crate::transcription::key_exchange::ServerHello, raw: Seq<u8>, config: crate::hello::client_spec::Config,
    transcript: crate::transcript::spec::State, peer_key: Seq<u8>, private_key: Seq<u8>)
    requires
        hypotheses(c, v, f, p),
        super::keys::x25519_agrees(k, p),
    ensures start_agrees(c, k, v, p, cl, c0, sh, raw, config, transcript, peer_key, private_key),
{
    if accepts_server_hello(p, c0, sh, raw, config, transcript, peer_key, private_key)
        && super::auth_flight::chain_agrees(v, p, config.host, config.now)
        && (forall|body: Seq<u8>| #[trigger] (v.chain)(config.host, config.now, body) matches Ok(key)
            ==> key.len() <= crate::auth::spec::MAX_KEY)
        && crate::traffic::handshake_spec::start(c, k, config, transcript, peer_key, private_key) is Ok
        && super::bootstrap::after_message(p, c0, raw) is Continue
        && cl.connection == super::bootstrap::after_message(p, c0, raw)->Continue_0.connection
        && crate::traffic::handshake_spec::needs_ccs(config, transcript)
            == (cl.compatibility_mode && !cl.change_cipher_spec_sent)
    {
        lemma_start(c, k, v, f, p, cl, c0, sh, raw, config, transcript, peer_key, private_key);
    }
}

/// **The dispatcher theorem.** RFC 8446 §4.3, §4.4, §5, §5.1 to §5.4, §6,
/// §6.1, §7.1, §7.3 and Appendix D.4, under [`hypotheses`] (the two sides'
/// primitives are the same functions, with the lengths both model) and
/// X25519 agreeing (`keys::x25519_agrees`):
/// - **the start** ([`start_agrees`]): the crate's handoff
///   (`handshake_spec::start`, `dispatcher_spec::start` with `needs_ccs`)
///   agrees ([`dispatcher_agrees`]) with the transcription's connection after
///   it accepts the same ServerHello ([`accepts_server_hello`]), when the
///   validators agree and the dummy change_cipher_spec is owed exactly when
///   the transcription has not written it;
/// - **every whole record** from agreeing states: the crate's
///   `receive_record` (which `feed` runs on each record its framer
///   completes) and the transcription's `client_receive_stream` agree
///   ([`record_agrees`]): the crate rejects exactly when the transcription
///   does (its alert that of some failure in the transcription's list,
///   [`fail_agrees`], its alert record the transcription's `alert_record`),
///   with the stated differences [`wrong_type`], [`finished_first`],
///   `post_handshake::two_faults`, the 2^18 cap and [`transcript_cap`]; the peer's error alert
///   is `PeerError` on both sides; a close_notify is the stated difference
///   of [`outcome_agrees`]; a compatibility change_cipher_spec is dropped at
///   a message boundary and refused inside a fragmented message on both
///   sides; otherwise both go on in agreeing states, or, on the server
///   Finished, the crate's flight is D.4's dummy record when owed and the
///   transcription's records [`coalesced`] into one, the same bytes with no
///   CertificateRequest, and acknowledging exactly it reaches `Ready` with
///   the transcription's application secrets, where the post-handshake
///   theorem's `post_agrees` holds ([`ack_agrees`], [`sent_agrees`]);
/// - `feed` on a completed record is that record's step
///   ([`lemma_feed_complete`]), and the transcription reads a stream one
///   whole record at a time (`post_handshake::lemma_stream_prefix`).
pub proof fn theorem_dispatcher_equivalence(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    v: crate::auth::spec::Verification, f: Ciphers, p: Primitives)
    requires
        hypotheses(c, v, f, p),
        super::keys::x25519_agrees(k, p),
    ensures
        forall|cl: ClientConnection, c0: Connection, sh: crate::transcription::key_exchange::ServerHello, raw: Seq<u8>,
            config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State, peer_key: Seq<u8>,
            private_key: Seq<u8>|
            #[trigger] start_agrees(c, k, v, p, cl, c0, sh, raw, config, transcript, peer_key, private_key),
        forall|s: State, cl: ClientConnection, b: Seq<u8>|
            #[trigger] dispatcher_agrees(p, v, s, cl) && #[trigger] super::bootstrap::whole_record(b)
                ==> record_agrees(c, v, f, p, s, cl, b),
        forall|s: State, input: Seq<u8>|
            s.mode == Mode::Handshake && (#[trigger] crate::connection::framing_spec::feed(s.framing, input)).status
                == crate::connection::framing_spec::Status::Complete ==> {
                let framed = crate::connection::framing_spec::feed(s.framing, input);
                let (action, after) = crate::connection::dispatcher_spec::receive_record(c, v, f,
                    State { framing: seq![], ..s }, framed.buffer);
                crate::connection::dispatcher_spec::feed(c, v, f, s, input) == (framed.consumed, action, after)
            },
        forall|conn: Connection, b: Seq<u8>, rest: Seq<u8>| #[trigger] super::bootstrap::whole_record(b) ==>
            (#[trigger] crate::transcription::connection::receive_stream(p, conn, b + rest)).0
                == super::post_handshake::joined(crate::transcription::connection::receive_stream(p, conn, b).0,
                    |c2: Connection| crate::transcription::connection::receive_stream(p, c2, rest).0),
{
    assert forall|cl: ClientConnection, c0: Connection, sh: crate::transcription::key_exchange::ServerHello, raw: Seq<u8>,
        config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State, peer_key: Seq<u8>,
        private_key: Seq<u8>|
        #[trigger] start_agrees(c, k, v, p, cl, c0, sh, raw, config, transcript, peer_key, private_key) by {
        lemma_start_agrees(c, k, v, f, p, cl, c0, sh, raw, config, transcript, peer_key, private_key);
    }
    assert forall|s: State, cl: ClientConnection, b: Seq<u8>|
        #[trigger] dispatcher_agrees(p, v, s, cl) && #[trigger] super::bootstrap::whole_record(b)
            implies record_agrees(c, v, f, p, s, cl, b) by {
        lemma_receive(c, v, f, p, s, cl, b);
    }
    assert forall|s: State, input: Seq<u8>|
        s.mode == Mode::Handshake && (#[trigger] crate::connection::framing_spec::feed(s.framing, input)).status
            == crate::connection::framing_spec::Status::Complete implies {
            let framed = crate::connection::framing_spec::feed(s.framing, input);
            let (action, after) = crate::connection::dispatcher_spec::receive_record(c, v, f,
                State { framing: seq![], ..s }, framed.buffer);
            crate::connection::dispatcher_spec::feed(c, v, f, s, input) == (framed.consumed, action, after)
        } by {
        lemma_feed_complete(c, v, f, s, input);
    }
    assert forall|conn: Connection, b: Seq<u8>, rest: Seq<u8>| #[trigger] super::bootstrap::whole_record(b) implies
        (#[trigger] crate::transcription::connection::receive_stream(p, conn, b + rest)).0
            == super::post_handshake::joined(crate::transcription::connection::receive_stream(p, conn, b).0,
                |c2: Connection| crate::transcription::connection::receive_stream(p, c2, rest).0) by {
        super::post_handshake::lemma_stream_prefix(p, conn, b, rest);
    }
}

} // verus!
