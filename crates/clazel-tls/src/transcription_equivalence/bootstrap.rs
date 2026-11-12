//! RFC 8446 §4.1.2–§4.1.4, §5, §5.1, §6 and Appendix D.4: the record layer
//! of `hello/bootstrap_spec.rs` around the negotiation controller (the
//! acknowledgement gate, change_cipher_spec records, handshake fragments and
//! alerts, and the CCS before ClientHello2) against the clean-room
//! transcription's `middlebox::start_client` and
//! `middlebox::client_receive_stream`: [`theorem_bootstrap_equivalence`].
//!
//! The two states are tied by [`bootstrap_agrees`]: the crate waits for the
//! server's Hello (`AwaitServerHello`) and its controller agrees with the
//! transcription's handshake ([`super::negotiation::negotiation_agrees`]);
//! no record protection on either side; the crate's reassembly buffer is the
//! transcription's `handshake_fragments`; the read side is open; the
//! compatibility mode is the crate's (a non-empty session ID); and the
//! transcription has written its dummy change_cipher_spec exactly when the
//! crate has (after a retry, in the mode: [`super::ccs::sent_before`]).
//!
//! What is compared is one whole record (`whole_record`: five header bytes
//! and exactly `length` more), the crate's `bootstrap_lemmas::record_step`
//! (which `bootstrap_lemmas::lemma_feed_complete` proves is `feed` on every
//! record its framer completes) against the transcription's
//! `client_receive_stream` of the same bytes ([`record_agrees`]). The framer
//! itself (when each side decides on a partial record) is `framing_spec`'s
//! part of #139.
//!
//! The acknowledgement gate is the crate's interface to its transport (a send
//! must be acknowledged with exactly its bytes before input is read); the
//! transcription has no transport, and writes its records as a list. So
//! [`start_agrees`] and [`buffer_agrees`] say: the bytes the crate asks
//! to send are the transcription's records, and acknowledging exactly them
//! leads to agreeing states. After a HelloRetryRequest, the messages that
//! follow it in its record (§5.1 lets them be coalesced) are what the crate
//! processes on that acknowledgement, and the transcription in the same
//! step: [`buffer_agrees`] compares the two, again from agreeing states. So
//! when one of them fails, the crate has already asked to send ClientHello2,
//! while the transcription's abort writes no ClientHello2; both reject, with
//! the same alerts.
//!
//! Where the two differ (each a case of [`fail_agrees`]):
//! - **Two faults in one record** ([`two_faults`]): both reject; the crate
//!   names the other fault. A record of an unknown type longer than 2^14
//!   (the crate checks the type first, `unexpected_message`; the
//!   transcription the length first, `record_overflow`), and an alert record
//!   of a length other than 0 or 2 inside a fragmented handshake message (the
//!   crate `decode_error`, the transcription `unexpected_message`).
//! - **The crate's resource caps** ([`cap`]): a handshake message above
//!   2^18 octets, and the transcript and cookie caps of the negotiation
//!   theorem, refused with `internal_error`.
//! - (Resolved: bytes after a handshake message in the same record. The
//!   crate refused them before looking at the first message; it now handles
//!   them as §5.1 and the transcription do, see `bootstrap_spec`.)
//! - A ServerHello the crate accepts here, whose X25519 shared secret is all
//!   zero: the transcription aborts in the same step (`accept_server_hello`),
//!   the crate in `join_spec::derive`, after this layer
//!   ([`buffer_agrees`]'s `Established` case states the transcription's
//!   step exactly). With bytes after that ServerHello the two name
//!   different faults: the crate the bytes (`unexpected_message`), the
//!   transcription the secret ([`buffer_fail_agrees`]).
//!
//! Not covered: the transport's end of file (the crate's `eof`: no
//! transcription counterpart, as `connection.rs` leaves transport closure
//! out of scope).

#[cfg(verus_only)]
use crate::hello::bootstrap_spec::{Action, Mode, State};
#[cfg(verus_only)]
use crate::transcription::alerts::ClientError;
#[cfg(verus_only)]
use crate::transcription::connection::{Connection, Progress, Protection, Receive};
#[cfg(verus_only)]
use crate::transcription::middlebox::{ClientConnection, ClientReceive};
#[cfg(verus_only)]
use crate::transcription::primitives::Primitives;
#[cfg(verus_only)]
use crate::transcription::state_machine::HandshakeStep;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// One record.
// ---------------------------------------------------------------------------

/// Five header bytes and exactly the `length` bytes after them.
pub open spec fn whole_record(b: Seq<u8>) -> bool {
    b.len() >= 5 && b.len() == 5 + crate::spec::be_value(b.subrange(3, 5))
}

/// The record's `length` field.
pub open spec fn length(b: Seq<u8>) -> nat {
    crate::spec::be_value(b.subrange(3, 5))
}

/// The record's fragment.
pub open spec fn fragment(b: Seq<u8>) -> Seq<u8> {
    b.subrange(5, b.len() as int)
}

/// The transcription's handling of one whole record (§5: its length, then
/// `receive_record`), with the read side open.
pub open spec fn one_record(p: Primitives, c: Connection, b: Seq<u8>) -> Receive {
    let header = crate::transcription::record::read_record_header(b)->Some_0;
    match crate::transcription::connection::record_length_failure(c, header) {
        Some(error) => Receive::Abort(error),
        None => crate::transcription::connection::receive_record(p, c, header, fragment(b)),
    }
}

/// [`one_record`] is what `receive_stream` does with a whole record.
pub proof fn lemma_stream_one(p: Primitives, c: Connection, b: Seq<u8>)
    requires whole_record(b), !c.read_closed,
    ensures crate::transcription::connection::receive_stream(p, c, b).0 == one_record(p, c, b),
{
    super::record::lemma_read_uint(b.subrange(3, 5), 2);
    assert(b.subrange(3, 5).take(2) =~= b.subrange(3, 5));
    let header = crate::transcription::record::read_record_header(b)->Some_0;
    assert(header.length == length(b));
    let rest = b.subrange((5 + header.length) as int, b.len() as int);
    assert(rest =~= Seq::<u8>::empty());
    match crate::transcription::connection::record_length_failure(c, header) {
        Some(_) => {},
        None => {
            match crate::transcription::connection::receive_record(p, c, header, fragment(b)) {
                Receive::Continue(first) => {
                    let (outcome, _) = crate::transcription::connection::receive_stream(p, first.connection, rest);
                    assert(outcome == Receive::Continue(Progress { connection: first.connection,
                        application_data: seq![], records_to_send: seq![] }));
                    assert(first.application_data + Seq::<u8>::empty() =~= first.application_data);
                    assert(first.records_to_send + Seq::<Seq<u8>>::empty() =~= first.records_to_send);
                },
                _ => {},
            }
        },
    }
}

/// §4: the crate's `extract_messages` and the transcription's reading of a
/// handshake header take the same first message off a buffer.
pub proof fn lemma_extract(buf: Seq<u8>)
    ensures
        match crate::spec::extract_messages(buf) {
            crate::spec::Res::Err(e) => e == crate::spec::ErrKind::HandshakeTooLarge,
            crate::spec::Res::Ok((ms, rest)) => if ms.len() == 0 {
                &&& rest == buf
                &&& buf.len() < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY
                &&& match crate::transcription::key_exchange::read_handshake_header(buf) {
                    None => true,
                    Some(h) => buf.len() < 4 + h.length,
                }
            } else {
                let n = 4 + crate::spec::be_value(buf.subrange(1, 4));
                &&& buf.len() >= n
                &&& n <= crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY
                &&& crate::transcription::key_exchange::read_handshake_header(buf) is Some
                &&& 4 + crate::transcription::key_exchange::read_handshake_header(buf)->Some_0.length == n
                &&& ms[0] == buf.subrange(0, n as int)
                &&& (ms.len() == 1 && rest.len() == 0) == (buf.len() == n)
            },
        },
    decreases buf.len(),
{
    super::messages::lemma_read_handshake_header(buf);
    if buf.len() >= crate::spec::HANDSHAKE_HEADER {
        let len = crate::spec::be_value(buf.subrange(1, 4));
        if len <= crate::spec::MAX_HANDSHAKE_BODY && buf.len() >= crate::spec::HANDSHAKE_HEADER + len {
            let tail = buf.skip((crate::spec::HANDSHAKE_HEADER + len) as int);
            lemma_extract(tail);
            assert(buf.take((crate::spec::HANDSHAKE_HEADER + len) as int) =~= buf.subrange(0, (4 + len) as int));
            if buf.len() == 4 + len {
                assert(tail =~= Seq::<u8>::empty());
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The relation and the cases.
// ---------------------------------------------------------------------------

/// The crate's bootstrap, waiting for the server's Hello, and the
/// transcription's client stand for the same connection, except perhaps for
/// the bytes of an unfinished handshake message (see the module
/// documentation).
pub open spec fn agrees_but_buffer(p: Primitives, s: State, cl: ClientConnection) -> bool {
    let c = cl.connection;
    &&& s.mode == Mode::AwaitServerHello
    &&& crate::hello::bootstrap_spec::wf(s)
    &&& super::negotiation::negotiation_agrees(p, s.hello->Some_0, c.handshake)
    &&& c.receive == Protection::Unprotected
    &&& c.send == Protection::Unprotected
    &&& !c.read_closed
    &&& !c.key_update_owed
    &&& cl.compatibility_mode == s.compatibility
    &&& cl.change_cipher_spec_sent == (s.hello->Some_0.transcript.retried && s.compatibility)
}

/// [`agrees_but_buffer`], and the crate's reassembly buffer is the
/// transcription's `handshake_fragments`.
pub open spec fn bootstrap_agrees(p: Primitives, s: State, cl: ClientConnection) -> bool {
    agrees_but_buffer(p, s, cl) && cl.connection.handshake_fragments == s.reassembly.buf
}

/// The bytes of the handshake message(s) a handshake record completes:
/// the reassembly buffer and the fragment.
pub open spec fn buffer(s: State, b: Seq<u8>) -> Seq<u8> {
    s.reassembly.buf + fragment(b)
}

/// A handshake record of at most 2^14 octets with a non-empty fragment.
pub open spec fn handshake_record(b: Seq<u8>) -> bool {
    b[0] == crate::spec::CT_HANDSHAKE && 0 < length(b) <= crate::spec::MAX_PLAINTEXT
}

/// Two faults in one record, where each side names a different one (see
/// the module documentation).
pub open spec fn two_faults(c: Connection, b: Seq<u8>) -> bool {
    ||| b[0] != crate::spec::CT_CHANGE_CIPHER_SPEC && b[0] != crate::spec::CT_ALERT
            && b[0] != crate::spec::CT_HANDSHAKE && length(b) > crate::spec::MAX_PLAINTEXT
    ||| b[0] == crate::spec::CT_ALERT && length(b) != 0 && length(b) != 2
            && length(b) <= crate::spec::MAX_PLAINTEXT && c.handshake_fragments.len() > 0
}

/// The crate's resource cap on a handshake message: above
/// `MAX_HANDSHAKE_BODY` octets (the transcript and cookie caps are in
/// [`buffer_fail_agrees`]).
pub open spec fn cap(p: Primitives, s: State, c: Connection, b: Seq<u8>) -> bool {
    handshake_record(b) && crate::spec::extract_messages(buffer(s, b))
        == crate::spec::Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(crate::spec::ErrKind::HandshakeTooLarge)
}

/// When the crate fails with `alert` on a record that is not handshake
/// messages: the transcription aborts with that alert, or one of the named
/// differences holds.
pub open spec fn fail_agrees(p: Primitives, s: State, c: Connection, b: Seq<u8>, t: Receive, alert: u8) -> bool {
    ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == alert as nat
    ||| t is Abort && two_faults(c, b)
    ||| alert == crate::spec::INTERNAL_ERROR && cap(p, s, c, b)
}

/// The length of the first handshake message of `bf`, header included.
pub open spec fn first_length(bf: Seq<u8>) -> nat {
    4 + crate::spec::be_value(bf.subrange(1, 4))
}

/// The body of the first handshake message of `bf`.
pub open spec fn first_body(bf: Seq<u8>) -> Seq<u8> {
    bf.subrange(4, first_length(bf) as int)
}

/// The crate's handling of the bytes `bf` of handshake messages: the
/// complete ones (`bootstrap_spec::receive_messages`), with the bytes of an
/// unfinished one as the reassembly state.
pub open spec fn buffer_step(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, bf: Seq<u8>) -> (State, Action) {
    match crate::spec::extract_messages(bf) {
        crate::spec::Res::Ok((ms, rest)) => crate::hello::bootstrap_spec::receive_messages(hash,
            State { reassembly: crate::spec::Reasm { buf: rest }, ..s }, ms),
        crate::spec::Res::Err(e) => (crate::hello::bootstrap_lemmas::terminal(s, Mode::Failed, s.reassembly),
            Action::Fail(crate::spec::alert_of(e))),
    }
}

/// `records` written before what `t` writes, as `process_handshake_bytes`
/// joins one message's records to the next ones'.
pub open spec fn after_records(records: Seq<Seq<u8>>, t: Receive) -> Receive {
    match t {
        Receive::Continue(progress) =>
            Receive::Continue(Progress { records_to_send: records + progress.records_to_send, ..progress }),
        other => other,
    }
}

/// When the crate fails with `alert` on the handshake messages `bf`, and
/// the transcription's processing of them gives `t`: the transcription
/// aborts with that alert; or the first message is a ServerHello whose
/// failures (the transcription's list) include the crate's alert, and the
/// transcription aborts with the first; or the crate's transcript or cookie
/// cap refused a ServerHello with no failure (`internal_error`); or the
/// server's ServerHello has an all-zero X25519 shared secret and bytes follow
/// it: the transcription aborts on the secret, the crate on the bytes (it
/// computes the secret after this layer, in `join_spec::derive`).
pub open spec fn buffer_fail_agrees(p: Primitives, s: State, c: Connection, bf: Seq<u8>, t: Receive, alert: u8) -> bool {
    let f = super::hello::hello_failures(c.handshake.hello, c.handshake.retry, first_body(bf));
    ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == alert as nat
    ||| bf[0] == crate::spec::HS_SERVER_HELLO && super::auth_flight::alert_in(alert, f) && f.len() > 0
            && t == Receive::Abort(f[0])
    ||| alert == crate::spec::INTERNAL_ERROR && bf[0] == crate::spec::HS_SERVER_HELLO
            && crate::hello::spec::validate(s.hello->Some_0.config.session_id, s.hello->Some_0.transcript.retried,
                first_body(bf)) is Ok
            && f.len() == 0
    ||| alert == crate::spec::UNEXPECTED_MESSAGE && bf.len() > first_length(bf)
            && t == Receive::Abort(ClientError::SharedSecretAllZero)
}

/// The transcription after one whole handshake message `raw` that ends the
/// buffer: its step, its actions, and an empty buffer.
pub open spec fn after_message(p: Primitives, c: Connection, raw: Seq<u8>) -> Receive {
    match crate::transcription::state_machine::receive_handshake_message(p, c.handshake, raw) {
        HandshakeStep::Abort(e) => Receive::Abort(e),
        HandshakeStep::Proceed { handshake, actions, .. } => {
            let (after, sent) = crate::transcription::connection::apply_actions(p, Connection { handshake, ..c }, actions);
            Receive::Continue(Progress { connection: Connection { handshake_fragments: seq![], ..after },
                application_data: seq![], records_to_send: sent })
        },
    }
}

/// The crate's handling of the handshake messages `bf` ([`buffer_step`])
/// and the transcription's (`process_handshake_bytes`) agree, from states
/// that agree but for the buffer. After a HelloRetryRequest, the crate's
/// flight is the transcription's records with D.4's CCS, and acknowledging
/// it processes what follows the HelloRetryRequest in `bf` as the
/// transcription does, from agreeing states again (§5.1: messages may be
/// coalesced; a HelloRetryRequest precedes no key change).
pub open spec fn buffer_agrees(p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>) -> bool
    decreases bf.len(),
{
    let c = cl.connection;
    let t = crate::transcription::connection::process_handshake_bytes(p, c, bf);
    let (s2, a) = buffer_step(p.hash, s, bf);
    let n = first_length(bf);
    match a {
        Action::None => {
            let c2 = Connection { handshake_fragments: s2.reassembly.buf, ..c };
            &&& t == Receive::Continue(Progress { connection: c2, application_data: seq![], records_to_send: seq![] })
            &&& bootstrap_agrees(p, s2, ClientConnection { connection: c2, ..cl })
        },
        // A message above the crate's 2^18 cap is `record_agrees`' (`cap`).
        Action::Fail(alert) => s2.mode == Mode::Failed && (crate::spec::extract_messages(bf) is Err
            || buffer_fail_agrees(p, s, c, bf, t, alert)),
        Action::Established(config, transcript, key) => {
            &&& s2.mode == Mode::Established
            &&& bf.len() == n
            &&& bf[0] == crate::spec::HS_SERVER_HELLO
            &&& t == after_message(p, c, bf)
            &&& bf == crate::transcription::key_exchange::write_handshake(2, first_body(bf))
            &&& crate::hello::client_spec::receive(p.hash, s.hello->Some_0, first_body(bf))
                == Ok::<crate::hello::client_spec::Outcome, u8>(
                    crate::hello::client_spec::Outcome::Established(config, transcript, key))
            &&& super::negotiation::receive_agrees(p, s.hello->Some_0, c.handshake, first_body(bf))
        },
        Action::Send(bytes) => {
            if 4 <= n && n <= bf.len() {
                let step = crate::transcription::state_machine::receive_handshake_message(p, c.handshake,
                    bf.subrange(0, n as int));
                let (c3, sent) = crate::transcription::connection::apply_actions(p,
                    Connection { handshake: step->handshake, ..c }, step->actions);
                let (records, ccs_sent) = crate::transcription::middlebox::before_second_flight(
                    cl.compatibility_mode, cl.change_cipher_spec_sent, sent);
                let s1 = State { mode: Mode::AwaitServerHello, pending_flight: seq![], retained: seq![], ..s2 };
                let cl2 = ClientConnection { connection: c3, change_cipher_spec_sent: ccs_sent, ..cl };
                &&& bf[0] == crate::spec::HS_SERVER_HELLO
                &&& step is Proceed
                &&& !step->receive_key_changes
                &&& bytes == super::ccs::flatten(records)
                &&& t == after_records(sent,
                    crate::transcription::connection::process_handshake_bytes(p, c3, bf.skip(n as int)))
                &&& s2.mode == Mode::AwaitClientHello2Send
                &&& s2.pending_flight == bytes
                &&& crate::hello::bootstrap_spec::wf(s2)
                &&& crate::hello::bootstrap_spec::acknowledge(p.hash, s2, bytes)
                    == buffer_step(p.hash, s1, bf.skip(n as int))
                &&& agrees_but_buffer(p, s1, cl2)
                &&& buffer_agrees(p, s1, cl2, bf.skip(n as int))
            } else {
                false
            }
        },
        _ => false,
    }
}

/// The crate's step on one whole record and the transcription's
/// `client_receive_stream` of it agree (see the module documentation): a
/// handshake record whose messages the crate reads is [`buffer_agrees`];
/// every other record is compared by what the crate does.
pub open spec fn record_agrees(p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>) -> bool {
    let c = cl.connection;
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
    let t = one_record(p, c, b);
    let u = crate::transcription::middlebox::client_receive_stream(p, cl, b).0;
    &&& u == match t {
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
    &&& if handshake_record(b) && crate::spec::extract_messages(buffer(s, b)) is Ok {
        &&& (s2, a) == buffer_step(p.hash, s, buffer(s, b))
        &&& t == crate::transcription::connection::process_handshake_bytes(p, c, buffer(s, b))
        &&& buffer_agrees(p, s, cl, buffer(s, b))
    } else {
        match a {
            Action::None => {
                let c2 = Connection { handshake_fragments: s2.reassembly.buf, ..c };
                &&& u == ClientReceive::Continue { client: ClientConnection { connection: c2, ..cl },
                    application_data: seq![], records_to_send: seq![] }
                &&& bootstrap_agrees(p, s2, ClientConnection { connection: c2, ..cl })
            },
            Action::Close => {
                &&& s2.mode == Mode::Closed
                &&& t == Receive::Continue(Progress { connection: Connection { read_closed: true, ..c },
                    application_data: seq![], records_to_send: seq![] })
            },
            Action::Alert(d) => t == Receive::PeerError(d as nat),
            Action::Fail(alert) => s2.mode == Mode::Failed && fail_agrees(p, s, c, b, t, alert),
            _ => false,
        }
    }
}

/// The start: the crate's first record is the transcription's
/// `start_client` records, and acknowledging exactly it leads to agreeing
/// states.
pub open spec fn start_agrees(p: Primitives, c: crate::hello::client_spec::Config,
    config: crate::transcription::middlebox::ClientConfig, x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>) -> bool
{
    let first = super::client::ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
    match crate::hello::bootstrap_spec::start(c) {
        Ok((s0, Action::Send(wire))) => {
            let (cl0, records) = crate::transcription::middlebox::start_client(p, config, first,
                x25519_private_key, retry_private_key);
            let (s1, a1) = crate::hello::bootstrap_spec::acknowledge(p.hash, s0, wire);
            &&& wire == super::ccs::flatten(records)
            &&& s0.mode == Mode::AwaitClientHelloSend
            &&& a1 == Action::None
            &&& bootstrap_agrees(p, s1, cl0)
        },
        Ok(_) => false,
        Err(_) => true,
    }
}

// ---------------------------------------------------------------------------
// Proofs.
// ---------------------------------------------------------------------------

/// The header of a whole record, on both sides.
pub proof fn lemma_header(b: Seq<u8>)
    requires whole_record(b),
    ensures
        crate::transcription::record::read_record_header(b) == Some(crate::transcription::record::RecordHeader {
            content_type: b[0] as nat,
            legacy_record_version: crate::transcription::record::read_record_header(b)->Some_0.legacy_record_version,
            length: length(b) }),
        b.subrange(5, (5 + length(b)) as int) == fragment(b),
        b.skip((5 + length(b)) as int).len() == 0,
        fragment(b).len() == length(b),
{
    super::record::lemma_read_uint(b.subrange(3, 5), 2);
    assert(b.subrange(3, 5).take(2) =~= b.subrange(3, 5));
}

/// A retry keeps the controller well-formed, in its second-ServerHello phase.
pub proof fn lemma_retry_wf(hash: spec_fn(Seq<u8>) -> Seq<u8>, before: crate::hello::client_spec::State,
    server: Seq<u8>, next: crate::hello::client_spec::State, flight: Seq<u8>)
    requires
        crate::hello::client_spec::wf(before),
        crate::hello::client_spec::receive(hash, before, server)
            == Ok::<crate::hello::client_spec::Outcome, u8>(crate::hello::client_spec::Outcome::Retry(next, flight)),
    ensures
        crate::hello::client_spec::wf(next),
        next.transcript.phase == crate::transcript::spec::Phase::SecondServerHello,
        next.config == before.config,
        next.transcript.retried,
        flight.len() <= 4528,
        !before.transcript.retried,
{
    crate::hello::bootstrap_lemmas::lemma_receive_retry_flight_bound(hash, before, server, next, flight);
    match crate::hello::spec::validate(before.config.session_id, before.transcript.retried, server) {
        Ok(crate::hello::spec::Selection::Retry(cookie)) => {
            let t1 = crate::transcript::spec::step(hash, before.transcript,
                crate::transcript::spec::Kind::HelloRetryRequest, server)->Ok_0;
            crate::transcript::lemmas::lemma_step_wf(hash, before.transcript,
                crate::transcript::spec::Kind::HelloRetryRequest, server);
            crate::transcript::lemmas::lemma_step_wf(hash, t1, crate::transcript::spec::Kind::ClientHello,
                crate::hello::client_spec::body(before.config, cookie));
        },
        _ => {},
    }
}

/// §4, §5.1: a buffer holding exactly one whole handshake message is handled
/// as [`after_message`] says.
pub proof fn lemma_process_one(p: Primitives, c: Connection, bf: Seq<u8>)
    requires
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        bf.len() == 4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length,
    ensures crate::transcription::connection::process_handshake_bytes(p, c, bf) == after_message(p, c, bf),
{
    let header = crate::transcription::key_exchange::read_handshake_header(bf)->Some_0;
    let rest = bf.subrange((4 + header.length) as int, bf.len() as int);
    assert(rest =~= Seq::<u8>::empty());
    assert(bf.subrange(0, (4 + header.length) as int) =~= bf);
    match crate::transcription::state_machine::receive_handshake_message(p, c.handshake, bf) {
        HandshakeStep::Abort(_) => {},
        HandshakeStep::Proceed { handshake, actions, receive_key_changes } => {
            let (after, sent) = crate::transcription::connection::apply_actions(p, Connection { handshake, ..c }, actions);
            let inner = crate::transcription::connection::process_handshake_bytes(p, after, rest);
            assert(crate::transcription::key_exchange::read_handshake_header(rest) is None);
            assert(inner == Receive::Continue(Progress { connection: Connection { handshake_fragments: rest, ..after },
                application_data: seq![], records_to_send: seq![] }));
            assert(sent + Seq::<Seq<u8>>::empty() =~= sent);
            assert(Connection { handshake_fragments: rest, ..after } == Connection { handshake_fragments: seq![], ..after });
        },
    }
}

/// The ClientHello2 record, as `apply_actions` writes it unprotected.
pub proof fn lemma_send_flight(p: Primitives, c: Connection, flight: Seq<u8>, version: nat)
    requires c.send == Protection::Unprotected, flight.len() <= 0x4000,
    ensures ({
        let actions = seq![crate::transcription::state_machine::Action::SendHandshake(flight, version)];
        let (after, sent) = crate::transcription::connection::apply_actions(p, c, actions);
        &&& sent == seq![crate::transcription::record::write_tls_plaintext(22, version, flight)]
        &&& after == c
    }),
{
    let actions = seq![crate::transcription::state_machine::Action::SendHandshake(flight, version)];
    let ct = crate::transcription::record::ct_handshake();
    assert(ct == 22);
    let blocks = crate::transcription::record::fragment_blocks(flight);
    assert(blocks == seq![flight]);
    let tail = blocks.subrange(1, blocks.len() as int);
    assert(tail =~= Seq::<Seq<u8>>::empty());
    let r = crate::transcription::record::write_tls_plaintext(22, version, flight);
    let u = Protection::Unprotected;
    assert(crate::transcription::connection::send_one(p, u, ct, version, flight) == (r, u));
    assert(crate::transcription::connection::send_blocks(p, u, ct, version, tail) == (Seq::<Seq<u8>>::empty(), u));
    assert(seq![r] + Seq::<Seq<u8>>::empty() =~= seq![r]);
    let (records, send) = crate::transcription::connection::send_blocks(p, u, ct, version, blocks);
    assert(records == seq![r] && send == u);
    let rest = actions.subrange(1, actions.len() as int);
    assert(rest =~= Seq::<crate::transcription::state_machine::Action>::empty());
    assert(Connection { send, ..c } == c);
    assert(crate::transcription::connection::apply_actions(p, c, rest) == (c, Seq::<Seq<u8>>::empty()));
}

/// The third and fourth bytes of a message say its body's length: the
/// message is the transcription's encoding of its type and body.
pub proof fn lemma_message(m: Seq<u8>)
    requires m.len() >= 4, m.len() == 4 + crate::spec::be_value(m.subrange(1, 4)),
    ensures m == crate::transcription::key_exchange::write_handshake(m[0] as nat, m.skip(4)),
{
    crate::lemmas_pl::lemma_be_bytes_of_be_value(m.subrange(1, 4));
    super::transcript::lemma_write_handshake(m[0], m.skip(4));
    assert(crate::spec::write_handshake(m[0], m.skip(4)) =~= m);
}

/// §4: past its first whole message, `extract_messages` goes on with the
/// rest of the buffer.
pub proof fn lemma_extract_tail(bf: Seq<u8>)
    requires
        crate::spec::extract_messages(bf) is Ok,
        crate::spec::extract_messages(bf)->Ok_0.0.len() > 0,
    ensures
        4 <= first_length(bf) <= bf.len(),
        crate::spec::extract_messages(bf.skip(first_length(bf) as int)) is Ok,
        crate::spec::extract_messages(bf.skip(first_length(bf) as int))->Ok_0.0
            == crate::spec::extract_messages(bf)->Ok_0.0.skip(1),
        crate::spec::extract_messages(bf.skip(first_length(bf) as int))->Ok_0.1
            == crate::spec::extract_messages(bf)->Ok_0.1,
        crate::spec::extract_messages(bf)->Ok_0.0[0] == bf.subrange(0, first_length(bf) as int),
{
    let n = first_length(bf);
    let tail = crate::spec::extract_messages(bf.skip(n as int));
    let ms = crate::spec::extract_messages(bf)->Ok_0.0;
    assert(bf.take(n as int) =~= bf.subrange(0, n as int));
    assert(ms =~= seq![bf.take(n as int)] + tail->Ok_0.0);
    assert(ms.skip(1) =~= tail->Ok_0.0);
}

/// What `extract_messages` leaves is the start of one message: shorter
/// than the largest.
pub proof fn lemma_extract_rest(bf: Seq<u8>)
    requires crate::spec::extract_messages(bf) is Ok,
    ensures crate::spec::extract_messages(bf)->Ok_0.1.len()
        < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY,
    decreases bf.len(),
{
    lemma_extract(bf);
    if crate::spec::extract_messages(bf)->Ok_0.0.len() > 0 {
        lemma_extract_tail(bf);
        lemma_extract_rest(bf.skip(first_length(bf) as int));
    }
}

/// [`buffer_agrees`], for every buffer, from states that agree but for the
/// buffer.
#[verifier::rlimit(300)]
pub proof fn lemma_buffer(p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        agrees_but_buffer(p, s, cl),
    ensures buffer_agrees(p, s, cl, bf),
    decreases bf.len(), 2nat,
{
    hide(crate::hello::client_spec::receive);
    hide(crate::hello::spec::validate);
    hide(super::hello::hello_failures);
    hide(super::negotiation::negotiation_agrees);
    let c = cl.connection;
    lemma_extract(bf);
    match crate::spec::extract_messages(bf) {
        crate::spec::Res::Err(_) => {},
        crate::spec::Res::Ok((ms, rest)) => {
            lemma_extract_rest(bf);
            if ms.len() == 0 {
                assert(rest == bf);
            } else {
                let n = first_length(bf);
                lemma_extract_tail(bf);
                if bf[0] == crate::spec::HS_SERVER_HELLO {
                    if bf.len() == n {
                        assert(bf.subrange(0, n as int) =~= bf);
                        lemma_process_one(p, c, bf);
                    }
                    lemma_buffer_hello(p, s, cl, bf);
                } else {
                    lemma_buffer_not_hello(p, s, cl, bf);
                }
            }
        },
    }
}

/// [`lemma_buffer`] when the first message is not a ServerHello: both sides
/// refuse it (`unexpected_message`).
#[verifier::rlimit(100)]
pub proof fn lemma_buffer_not_hello(p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>)
    requires
        agrees_but_buffer(p, s, cl),
        crate::spec::extract_messages(bf) is Ok,
        crate::spec::extract_messages(bf)->Ok_0.0.len() > 0,
        bf[0] != crate::spec::HS_SERVER_HELLO,
    ensures buffer_agrees(p, s, cl, bf),
{
    hide(crate::hello::client_spec::receive);
    hide(crate::hello::spec::validate);
    hide(super::hello::hello_failures);
    let c = cl.connection;
    lemma_extract(bf);
    lemma_extract_tail(bf);
    let ms = crate::spec::extract_messages(bf)->Ok_0.0;
    let n = first_length(bf);
    let raw = bf.subrange(0, n as int);
    assert(raw[0] == bf[0]);
    assert(crate::transcription::state_machine::receive_handshake_message(p, c.handshake, raw)
        == crate::transcription::state_machine::out_of_order(raw[0] as nat));
}

/// [`lemma_buffer`] when the first message is a ServerHello (or a
/// HelloRetryRequest): the negotiation theorem's case.
#[verifier::rlimit(300)]
pub proof fn lemma_buffer_hello(p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        agrees_but_buffer(p, s, cl),
        crate::spec::extract_messages(bf) is Ok,
        crate::spec::extract_messages(bf)->Ok_0.0.len() > 0,
        crate::spec::extract_messages(bf)->Ok_0.1.len()
            < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY,
        bf[0] == crate::spec::HS_SERVER_HELLO,
        bf.len() == first_length(bf) ==> crate::transcription::connection::process_handshake_bytes(p,
            cl.connection, bf) == after_message(p, cl.connection, bf),
    ensures buffer_agrees(p, s, cl, bf),
    decreases bf.len(), 1nat,
{
    hide(crate::hello::client_spec::receive);
    hide(crate::hello::spec::validate);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(super::hello::hello_failures);
    let c = cl.connection;
    let hello = s.hello->Some_0;
    lemma_extract(bf);
    lemma_extract_tail(bf);
    let ms = crate::spec::extract_messages(bf)->Ok_0.0;
    let rest = crate::spec::extract_messages(bf)->Ok_0.1;
    let n = first_length(bf);
    let raw = ms[0];
    assert(raw.subrange(1, 4) =~= bf.subrange(1, 4));
    lemma_message(raw);
    let body = first_body(bf);
    assert(body =~= raw.skip(4));
    assert(raw == crate::transcription::key_exchange::write_handshake(2, body));
    if bf.len() == n {
        assert(bf.subrange(0, n as int) =~= bf);
    }
    let s0 = State { reassembly: crate::spec::Reasm { buf: rest }, ..s };
    crate::hello::bootstrap_lemmas::lemma_receive_messages(p.hash, s0, ms);
    super::negotiation::lemma_receive(p, hello, c.handshake, body);
    match crate::hello::client_spec::receive(p.hash, hello, body) {
        Ok(crate::hello::client_spec::Outcome::Retry(next, flight)) => {
            lemma_buffer_retry(p, s, cl, bf, next, flight);
        },
        Ok(crate::hello::client_spec::Outcome::Established(config, transcript, key)) => {
            if bf.len() != n {
                let h = crate::transcription::key_exchange::read_server_hello(body)->Some_0;
                let step = crate::transcription::state_machine::accept_server_hello(p, c.handshake, h, raw);
                match step {
                    crate::transcription::state_machine::HandshakeStep::Abort(e) =>
                        assert(e == ClientError::SharedSecretAllZero),
                    crate::transcription::state_machine::HandshakeStep::Proceed { receive_key_changes, .. } =>
                        assert(receive_key_changes),
                }
            }
        },
        _ => {},
    }
}

/// [`lemma_buffer`] when the crate retries: ClientHello2 and its CCS are the
/// transcription's records, and what follows the HelloRetryRequest is
/// [`buffer_agrees`] again, from the states after it.
#[verifier::rlimit(100)]
pub proof fn lemma_buffer_retry(p: Primitives, s: State, cl: ClientConnection, bf: Seq<u8>,
    next: crate::hello::client_spec::State, flight: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        agrees_but_buffer(p, s, cl),
        crate::spec::extract_messages(bf) is Ok,
        crate::spec::extract_messages(bf)->Ok_0.0.len() > 0,
        bf[0] == crate::spec::HS_SERVER_HELLO,
        bf.subrange(0, first_length(bf) as int)
            == crate::transcription::key_exchange::write_handshake(2, first_body(bf)),
        crate::hello::client_spec::receive(p.hash, s.hello->Some_0, first_body(bf))
            == Ok::<crate::hello::client_spec::Outcome, u8>(crate::hello::client_spec::Outcome::Retry(next, flight)),
        super::negotiation::receive_agrees(p, s.hello->Some_0, cl.connection.handshake, first_body(bf)),
    ensures buffer_agrees(p, s, cl, bf),
    decreases bf.len(), 0nat,
{
    hide(crate::hello::client_spec::receive);
    hide(crate::hello::spec::validate);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(super::hello::hello_failures);
    lemma_extract_rest(bf);
    let c = cl.connection;
    let hello = s.hello->Some_0;
    let n = first_length(bf);
    let body = first_body(bf);
    lemma_extract(bf);
    lemma_extract_tail(bf);
    let ms = crate::spec::extract_messages(bf)->Ok_0.0;
    let rest = crate::spec::extract_messages(bf)->Ok_0.1;
    let raw = bf.subrange(0, n as int);
    lemma_retry_wf(p.hash, hello, body, next, flight);
    let step = crate::transcription::state_machine::receive_handshake_message(p, c.handshake, raw);
    let hs2 = step->handshake;
    let c2 = Connection { handshake: hs2, ..c };
    lemma_send_flight(p, c2, flight, 0x0303);
    super::record::lemma_write_plaintext(22, 0x0303, flight);
    let r = crate::transcription::record::write_tls_plaintext(22, 0x0303, flight);
    assert(crate::hello::bootstrap_spec::handshake_record(flight) == r);
    assert(crate::spec::write_plaintext(22u8, 0x0303u16, flight).len() > 0);
    super::ccs::theorem_compatibility_ccs();
    let (batch, ccs_sent) = crate::transcription::middlebox::before_second_flight(
        super::ccs::mode(hello.config), false, seq![r]);
    assert(super::ccs::flatten(batch) == if super::ccs::mode(hello.config) {
        crate::hello::bootstrap_spec::compatibility_ccs() + r } else { r });
    assert(!hello.transcript.retried);
    assert(cl.change_cipher_spec_sent == false);
    assert(cl.compatibility_mode == super::ccs::mode(hello.config));
    // The crate's side: the HelloRetryRequest, then the acknowledgement.
    let s0 = State { reassembly: crate::spec::Reasm { buf: rest }, ..s };
    crate::hello::bootstrap_lemmas::lemma_receive_messages(p.hash, s0, ms);
    assert(ms[0].skip(4) =~= body);
    let (s2, a) = buffer_step(p.hash, s, bf);
    assert(s2.hello == Some(next));
    assert(s2.retained == ms.skip(1));
    assert(s2.reassembly.buf == rest);
    assert(crate::hello::bootstrap_spec::wf(s2));
    let s1 = State { mode: Mode::AwaitServerHello, pending_flight: seq![], retained: seq![], ..s2 };
    assert(crate::hello::bootstrap_spec::acknowledge(p.hash, s2, s2.pending_flight)
        == buffer_step(p.hash, s1, bf.skip(n as int)));
    // The transcription's side: ClientHello2, then the rest of the buffer.
    assert(bf.subrange(n as int, bf.len() as int) =~= bf.skip(n as int));
    let cl2 = ClientConnection { connection: c2, change_cipher_spec_sent: ccs_sent, ..cl };
    assert(agrees_but_buffer(p, s1, cl2));
    lemma_buffer(p, s1, cl2, bf.skip(n as int));
}

/// [`record_agrees`] for a handshake record.
#[verifier::rlimit(100)]
pub proof fn lemma_handshake_record(p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        bootstrap_agrees(p, s, cl),
        whole_record(b),
        handshake_record(b),
    ensures record_agrees(p, s, cl, b),
{
    let c = cl.connection;
    lemma_header(b);
    lemma_stream_one(p, c, b);
    let bf = buffer(s, b);
    lemma_extract(bf);
    let t = one_record(p, c, b);
    assert(t == crate::transcription::connection::process_handshake_bytes(p, c, bf));
    assert(crate::hello::bootstrap_lemmas::record_step(p.hash, s, b)
        == crate::hello::bootstrap_lemmas::fragment_step(p.hash, s, fragment(b)));
    match crate::spec::extract_messages(bf) {
        crate::spec::Res::Err(_) => {},
        crate::spec::Res::Ok((ms, rest)) => {
            assert(crate::hello::bootstrap_lemmas::record_step(p.hash, s, b) == buffer_step(p.hash, s, bf));
            lemma_buffer(p, s, cl, bf);
        },
    }
}

/// [`record_agrees`] for every other record.
#[verifier::rlimit(50)]
pub proof fn lemma_other_record(p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>)
    requires
        bootstrap_agrees(p, s, cl),
        whole_record(b),
        !handshake_record(b),
    ensures record_agrees(p, s, cl, b),
{
    let c = cl.connection;
    lemma_header(b);
    lemma_stream_one(p, c, b);
    assert(crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
        cl.change_cipher_spec_sent, Seq::<Seq<u8>>::empty())
        == (Seq::<Seq<u8>>::empty(), cl.change_cipher_spec_sent));
    if b[0] == crate::spec::CT_CHANGE_CIPHER_SPEC && length(b) <= crate::spec::MAX_PLAINTEXT {
        if fragment(b) == seq![1u8] {
            assert(fragment(b) =~= seq![0x01u8]);
        }
    }
}

/// [`start_agrees`], for one configuration.
pub proof fn lemma_start(p: Primitives, c: crate::hello::client_spec::Config,
    config: crate::transcription::middlebox::ClientConfig, x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>)
    requires
        (p.x25519)(x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key,
        config.compatibility_mode == super::ccs::mode(c),
    ensures start_agrees(p, c, config, x25519_private_key, retry_private_key),
{
    match crate::hello::client_spec::start(c) {
        Err(_) => {},
        Ok((hello, flight)) => {
            super::negotiation::lemma_start(p, c, x25519_private_key, retry_private_key);
            let b = crate::hello::client_spec::body(c, Seq::empty());
            crate::hello::client_lemmas::lemma_profile(c, Seq::empty());
            crate::lemmas_pl::lemma_be_bytes_len(b.len(), 3);
            assert(flight.len() == 4 + b.len());
            crate::transcript::lemmas::lemma_start_wf(b);
            let first = super::client::ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
            let hs = crate::transcription::state_machine::start_handshake(first, x25519_private_key, retry_private_key);
            let c0 = Connection { handshake: hs, receive: Protection::Unprotected, send: Protection::Unprotected,
                handshake_fragments: seq![], read_closed: false, key_update_owed: false };
            lemma_send_flight(p, c0, flight, 0x0301);
            super::record::lemma_write_plaintext(22, 0x0301, flight);
            let r = crate::transcription::record::write_tls_plaintext(22, 0x0301, flight);
            super::ccs::lemma_flatten(r, r);
        },
    }
}

/// **The bootstrap theorem.** For every configuration the crate starts
/// with, every private key whose public value it offers, and every
/// transcription configuration in the crate's compatibility mode, the
/// crate's first record is the transcription's `start_client` records and
/// acknowledging it leads to agreeing states ([`start_agrees`]); from every
/// pair of agreeing states, on every whole record, the crate's step and the
/// transcription's `client_receive_stream` agree ([`record_agrees`]),
/// where after a HelloRetryRequest acknowledging exactly the ClientHello2
/// flight processes what followed it in its record as the transcription
/// does, and leads to agreeing states again ([`buffer_agrees`]). Hypothesis: the hash's
/// outputs are 32 bytes, and the crate hashes with the transcription's
/// hash.
pub proof fn theorem_bootstrap_equivalence(p: Primitives)
    requires super::transcript::hash_is_32(p.hash),
    ensures
        forall|c: crate::hello::client_spec::Config, config: crate::transcription::middlebox::ClientConfig,
            x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>|
            (p.x25519)(x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key
                && config.compatibility_mode == super::ccs::mode(c)
            ==> #[trigger] start_agrees(p, c, config, x25519_private_key, retry_private_key),
        forall|s: State, cl: ClientConnection, b: Seq<u8>|
            #[trigger] bootstrap_agrees(p, s, cl) && whole_record(b) ==> #[trigger] record_agrees(p, s, cl, b),
{
    assert forall|c: crate::hello::client_spec::Config, config: crate::transcription::middlebox::ClientConfig,
        x25519_private_key: Seq<u8>, retry_private_key: Seq<u8>|
        (p.x25519)(x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == c.public_key
            && config.compatibility_mode == super::ccs::mode(c)
        implies #[trigger] start_agrees(p, c, config, x25519_private_key, retry_private_key) by {
        lemma_start(p, c, config, x25519_private_key, retry_private_key);
    }
    assert forall|s: State, cl: ClientConnection, b: Seq<u8>|
        #[trigger] bootstrap_agrees(p, s, cl) && whole_record(b) implies #[trigger] record_agrees(p, s, cl, b) by {
        if handshake_record(b) {
            lemma_handshake_record(p, s, cl, b);
        } else {
            lemma_other_record(p, s, cl, b);
        }
    }
}

} // verus!
