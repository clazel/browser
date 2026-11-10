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
//! [`start_agrees`] and [`acknowledge_agrees`] say: the bytes the crate asks
//! to send are the transcription's records, and acknowledging exactly them
//! leads to agreeing states.
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
//! - **Bytes after a handshake message in the same record** while waiting
//!   for the server's Hello ([`following_bytes`]): the crate refuses
//!   (`unexpected_message`). The transcription does too when the first
//!   message fails or is a ServerHello (§5.1, the key change), but goes on
//!   after a HelloRetryRequest it accepts, since §5.1 lets messages be
//!   coalesced. Found here; see the pull request.
//! - A ServerHello the crate accepts here, whose X25519 shared secret is all
//!   zero: the transcription aborts in the same step (`accept_server_hello`),
//!   the crate in `join_spec::derive`, after this layer
//!   ([`record_agrees`]'s `Established` case states the transcription's
//!   step exactly).
//!
//! Not covered: the transport's end of file (the crate's `eof`: no
//! transcription counterpart, as `connection.rs` leaves transport closure
//! out of scope).

#[allow(unused_imports)]
use vstd::prelude::*;
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
/// transcription's client stand for the same connection (see the module
/// documentation).
pub open spec fn bootstrap_agrees(p: Primitives, s: State, cl: ClientConnection) -> bool {
    let c = cl.connection;
    &&& s.mode == Mode::AwaitServerHello
    &&& crate::hello::bootstrap_spec::wf(s)
    &&& super::negotiation::negotiation_agrees(p, s.hello->Some_0, c.handshake)
    &&& c.receive == Protection::Unprotected
    &&& c.send == Protection::Unprotected
    &&& c.handshake_fragments == s.reassembly.buf
    &&& !c.read_closed
    &&& !c.key_update_owed
    &&& cl.compatibility_mode == s.compatibility
    &&& cl.change_cipher_spec_sent == (s.hello->Some_0.transcript.retried && s.compatibility)
}

/// After a HelloRetryRequest: the crate waits for the acknowledgement of
/// its ClientHello2 flight, and is otherwise as in [`bootstrap_agrees`].
pub open spec fn retried_agrees(p: Primitives, s: State, cl: ClientConnection) -> bool {
    bootstrap_agrees(p, State { mode: Mode::AwaitServerHello, pending_flight: seq![], ..s }, cl)
        && s.mode == Mode::AwaitClientHello2Send
        && crate::hello::bootstrap_spec::wf(s)
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

/// The record completes exactly one message, of type server_hello, and
/// nothing else: the case the negotiation theorem covers.
pub open spec fn single_hello(s: State, b: Seq<u8>) -> bool {
    &&& handshake_record(b)
    &&& match crate::spec::extract_messages(buffer(s, b)) {
        crate::spec::Res::Ok((ms, rest)) => ms.len() == 1 && rest.len() == 0
            && ms[0][0] == crate::spec::HS_SERVER_HELLO,
        _ => false,
    }
}

/// The body of that message.
pub open spec fn hello_body(s: State, b: Seq<u8>) -> Seq<u8> {
    buffer(s, b).skip(4)
}

/// Two faults in one record, where each side names a different one (see
/// the module documentation).
pub open spec fn two_faults(c: Connection, b: Seq<u8>) -> bool {
    ||| b[0] != crate::spec::CT_CHANGE_CIPHER_SPEC && b[0] != crate::spec::CT_ALERT
            && b[0] != crate::spec::CT_HANDSHAKE && length(b) > crate::spec::MAX_PLAINTEXT
    ||| b[0] == crate::spec::CT_ALERT && length(b) != 0 && length(b) != 2
            && length(b) <= crate::spec::MAX_PLAINTEXT && c.handshake_fragments.len() > 0
}

/// The crate's resource caps: a handshake message above
/// `MAX_HANDSHAKE_BODY`, or (on a ServerHello the transcription accepts
/// with no failure) the transcript and cookie caps.
pub open spec fn cap(p: Primitives, s: State, c: Connection, b: Seq<u8>) -> bool {
    ||| handshake_record(b) && crate::spec::extract_messages(buffer(s, b))
            == crate::spec::Res::<(Seq<Seq<u8>>, Seq<u8>)>::Err(crate::spec::ErrKind::HandshakeTooLarge)
    ||| single_hello(s, b)
            && crate::hello::spec::validate(s.hello->Some_0.config.session_id, s.hello->Some_0.transcript.retried,
                hello_body(s, b)) is Ok
            && super::hello::hello_failures(c.handshake.hello, c.handshake.retry, hello_body(s, b)).len() == 0
}

/// A handshake record that completes a message and has more bytes after
/// it. The transcription aborts with the first message's failure, or for
/// §5.1's key change after a ServerHello; after a HelloRetryRequest it
/// accepts, it goes on (see the module documentation).
pub open spec fn following_bytes(p: Primitives, s: State, c: Connection, b: Seq<u8>, t: Receive) -> bool {
    &&& handshake_record(b)
    &&& match crate::spec::extract_messages(buffer(s, b)) {
        crate::spec::Res::Ok((ms, rest)) => {
            &&& ms.len() >= 1
            &&& (ms.len() > 1 || rest.len() > 0)
            &&& match crate::transcription::state_machine::receive_handshake_message(p, c.handshake, ms[0]) {
                HandshakeStep::Abort(e) => t == Receive::Abort(e),
                HandshakeStep::Proceed { receive_key_changes, .. } =>
                    receive_key_changes ==> t == Receive::Abort(ClientError::KeyChangeNotAligned),
            }
        },
        _ => false,
    }
}

/// When the crate fails with `alert`: the transcription aborts with that
/// alert, or one of the named differences holds.
pub open spec fn fail_agrees(p: Primitives, s: State, c: Connection, b: Seq<u8>, t: Receive, alert: u8) -> bool {
    ||| t is Abort && crate::transcription::alerts::required_alert(t->Abort_0) == alert as nat
    ||| t is Abort && two_faults(c, b)
    ||| single_hello(s, b) && super::auth_flight::alert_in(alert,
            super::hello::hello_failures(c.handshake.hello, c.handshake.retry, hello_body(s, b)))
        && t == Receive::Abort(super::hello::hello_failures(c.handshake.hello, c.handshake.retry, hello_body(s, b))[0])
    ||| alert == crate::spec::INTERNAL_ERROR && cap(p, s, c, b)
    ||| alert == crate::spec::UNEXPECTED_MESSAGE && following_bytes(p, s, c, b, t)
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

/// The crate's step on one whole record and the transcription's
/// `client_receive_stream` of it agree (see the module documentation).
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
    &&& match a {
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
        Action::Send(bytes) => match u {
            ClientReceive::Continue { client, application_data, records_to_send } => {
                &&& single_hello(s, b)
                &&& application_data == Seq::<u8>::empty()
                &&& bytes == super::ccs::flatten(records_to_send)
                &&& retried_agrees(p, s2, client)
                &&& s2.pending_flight == bytes
            },
            _ => false,
        },
        Action::Established(config, transcript, key) => {
            &&& s2.mode == Mode::Established
            &&& single_hello(s, b)
            &&& t == after_message(p, c, buffer(s, b))
            &&& buffer(s, b) == crate::transcription::key_exchange::write_handshake(2, hello_body(s, b))
            &&& crate::hello::client_spec::receive(p.hash, s.hello->Some_0, hello_body(s, b))
                == Ok::<crate::hello::client_spec::Outcome, u8>(
                    crate::hello::client_spec::Outcome::Established(config, transcript, key))
            &&& super::negotiation::receive_agrees(p, s.hello->Some_0, c.handshake, hello_body(s, b))
        },
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
            let (s1, a1) = crate::hello::bootstrap_spec::acknowledge(s0, wire);
            &&& wire == super::ccs::flatten(records)
            &&& s0.mode == Mode::AwaitClientHelloSend
            &&& a1 == Action::None
            &&& bootstrap_agrees(p, s1, cl0)
        },
        Ok(_) => false,
        Err(_) => true,
    }
}

/// Acknowledging exactly the ClientHello2 flight leads to agreeing states.
pub open spec fn acknowledge_agrees(p: Primitives, s: State, cl: ClientConnection) -> bool {
    let (s1, a1) = crate::hello::bootstrap_spec::acknowledge(s, s.pending_flight);
    a1 == Action::None && bootstrap_agrees(p, s1, cl)
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

/// §5.1: a buffer with bytes after its first whole message.
pub proof fn lemma_process_more(p: Primitives, c: Connection, bf: Seq<u8>)
    requires
        crate::transcription::key_exchange::read_handshake_header(bf) is Some,
        bf.len() > 4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length,
    ensures ({
        let n = 4 + crate::transcription::key_exchange::read_handshake_header(bf)->Some_0.length;
        let t = crate::transcription::connection::process_handshake_bytes(p, c, bf);
        match crate::transcription::state_machine::receive_handshake_message(p, c.handshake, bf.subrange(0, n as int)) {
            HandshakeStep::Abort(e) => t == Receive::Abort(e),
            HandshakeStep::Proceed { receive_key_changes, .. } =>
                receive_key_changes ==> t == Receive::Abort(ClientError::KeyChangeNotAligned),
        }
    }),
{
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

/// [`record_agrees`] for a record that completes exactly one ServerHello
/// (or HelloRetryRequest): the negotiation theorem's case.
#[verifier::rlimit(100)]
pub proof fn lemma_single_hello(p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        bootstrap_agrees(p, s, cl),
        whole_record(b),
        single_hello(s, b),
        buffer(s, b) == crate::transcription::key_exchange::write_handshake(
            buffer(s, b)[0] as nat, hello_body(s, b)),
        one_record(p, cl.connection, b) == after_message(p, cl.connection, buffer(s, b)),
        crate::hello::bootstrap_lemmas::record_step(p.hash, s, b) == crate::hello::bootstrap_lemmas::hello_step(p.hash,
            State { reassembly: crate::spec::Reasm { buf: seq![] }, ..s }, hello_body(s, b)),
    ensures record_agrees(p, s, cl, b),
{
    hide(crate::hello::client_spec::receive);
    hide(crate::hello::spec::validate);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(super::hello::hello_failures);
    let c = cl.connection;
    let hello = s.hello->Some_0;
    let bf = buffer(s, b);
    let body = hello_body(s, b);
    assert(bf == crate::transcription::key_exchange::write_handshake(2, body));
    assert(body.len() <= crate::transcript::spec::MAX_BODY) by {
        lemma_extract(bf);
    }
    super::negotiation::lemma_receive(p, hello, c.handshake, body);
    lemma_stream_one(p, c, b);
    match crate::hello::client_spec::receive(p.hash, hello, body) {
        Ok(crate::hello::client_spec::Outcome::Retry(next, flight)) => {
            lemma_hello_retry(p, s, cl, b, next, flight);
        },
        _ => {},
    }
}

/// [`lemma_single_hello`] when the crate retries.
#[verifier::rlimit(100)]
pub proof fn lemma_hello_retry(p: Primitives, s: State, cl: ClientConnection, b: Seq<u8>,
    next: crate::hello::client_spec::State, flight: Seq<u8>)
    requires
        bootstrap_agrees(p, s, cl),
        whole_record(b),
        single_hello(s, b),
        one_record(p, cl.connection, b) == after_message(p, cl.connection, buffer(s, b)),
        crate::hello::bootstrap_lemmas::record_step(p.hash, s, b) == crate::hello::bootstrap_lemmas::hello_step(p.hash,
            State { reassembly: crate::spec::Reasm { buf: seq![] }, ..s }, hello_body(s, b)),
        crate::hello::client_spec::receive(p.hash, s.hello->Some_0, hello_body(s, b))
            == Ok::<crate::hello::client_spec::Outcome, u8>(crate::hello::client_spec::Outcome::Retry(next, flight)),
        super::negotiation::receive_agrees(p, s.hello->Some_0, cl.connection.handshake, hello_body(s, b)),
        buffer(s, b) == crate::transcription::key_exchange::write_handshake(2, hello_body(s, b)),
    ensures record_agrees(p, s, cl, b),
{
    hide(crate::hello::client_spec::receive);
    hide(crate::hello::spec::validate);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(super::hello::hello_failures);
    let c = cl.connection;
    let hello = s.hello->Some_0;
    let bf = buffer(s, b);
    let body = hello_body(s, b);
    lemma_retry_wf(p.hash, hello, body, next, flight);
    lemma_stream_one(p, c, b);
    let step = crate::transcription::state_machine::receive_handshake_message(p, c.handshake, bf);
    let hs2 = step->handshake;
    lemma_send_flight(p, Connection { handshake: hs2, ..c }, flight, 0x0303);
    super::record::lemma_write_plaintext(22, 0x0303, flight);
    let r = crate::transcription::record::write_tls_plaintext(22, 0x0303, flight);
    assert(crate::hello::bootstrap_spec::handshake_record(flight) == r);
    let c2 = Connection { handshake: hs2, handshake_fragments: seq![], ..c };
    assert(one_record(p, c, b) == Receive::Continue(Progress { connection: c2,
        application_data: seq![], records_to_send: seq![r] }));
    super::ccs::theorem_compatibility_ccs();
    let (batch, sent) = crate::transcription::middlebox::before_second_flight(
        super::ccs::mode(hello.config), false, seq![r]);
    assert(super::ccs::flatten(batch) == if super::ccs::mode(hello.config) {
        crate::hello::bootstrap_spec::compatibility_ccs() + r } else { r });
    assert(!hello.transcript.retried);
    assert(cl.change_cipher_spec_sent == false);
    assert(cl.compatibility_mode == super::ccs::mode(hello.config));
    let s2 = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b).0;
    assert(s2.hello == Some(next));
    assert(s2.mode == Mode::AwaitClientHello2Send);
    assert(crate::hello::bootstrap_spec::wf(s2));
    let cl2 = ClientConnection { connection: c2, change_cipher_spec_sent: sent, ..cl };
    assert(retried_agrees(p, s2, cl2));
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
    let hello = s.hello->Some_0;
    lemma_header(b);
    lemma_stream_one(p, c, b);
    let bf = buffer(s, b);
    lemma_extract(bf);
    let t = one_record(p, c, b);
    assert(t == crate::transcription::connection::process_handshake_bytes(p, c, bf));
    match crate::spec::extract_messages(bf) {
        crate::spec::Res::Err(_) => {},
        crate::spec::Res::Ok((ms, rest)) => {
            if ms.len() == 0 {
                assert(crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
                    cl.change_cipher_spec_sent, Seq::<Seq<u8>>::empty())
                    == (Seq::<Seq<u8>>::empty(), cl.change_cipher_spec_sent));
            } else {
                let n = 4 + crate::spec::be_value(bf.subrange(1, 4));
                if bf.len() == n {
                    assert(bf.subrange(0, n as int) =~= bf);
                    lemma_process_one(p, c, bf);
                    if bf[0] == crate::spec::HS_SERVER_HELLO {
                        assert(rest =~= Seq::<u8>::empty());
                        assert(ms[0] == bf);
                        assert(single_hello(s, b));
                        lemma_message(bf);
                        assert(crate::hello::bootstrap_lemmas::record_step(p.hash, s, b)
                            == crate::hello::bootstrap_lemmas::fragment_step(p.hash, s, fragment(b)));
                        assert(crate::hello::bootstrap_lemmas::record_step(p.hash, s, b)
                            == crate::hello::bootstrap_lemmas::hello_step(p.hash,
                                State { reassembly: crate::spec::Reasm { buf: seq![] }, ..s }, hello_body(s, b)));
                        lemma_single_hello(p, s, cl, b);
                    }
                } else {
                    lemma_process_more(p, c, bf);
                    assert(bf.subrange(0, n as int) == ms[0]);
                }
            }
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
/// transcription's `client_receive_stream` agree ([`record_agrees`]); and
/// after a retry, acknowledging exactly the ClientHello2 flight leads to
/// agreeing states again ([`acknowledge_agrees`]). Hypothesis: the hash's
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
        forall|s: State, cl: ClientConnection|
            #[trigger] retried_agrees(p, s, cl) ==> acknowledge_agrees(p, s, cl),
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
    assert forall|s: State, cl: ClientConnection|
        #[trigger] retried_agrees(p, s, cl) implies acknowledge_agrees(p, s, cl) by {}
}

} // verus!
