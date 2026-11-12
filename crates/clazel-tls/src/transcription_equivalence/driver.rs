//! RFC 8446 §4.1, §5, §6 and §7.3 end to end: the crate's whole client
//! driver (`connection/driver_spec.rs`, as `connection/driver_contract.rs`
//! makes every operation of `driver_exec::Driver` a function of its state)
//! against the clean-room transcription's client (`middlebox::start_client`
//! and `client_receive_stream`, `connection::send_application_data`,
//! `close_write` and `alert_record`), from the configuration to the end of
//! the connection: [`theorem_driver_equivalence`].
//!
//! The comparison is built operation by operation: [`op_agrees`].

#[cfg(verus_only)]
use crate::connection::driver_contract::Models;
#[cfg(verus_only)]
use crate::connection::driver_spec::{Origin, Stage, Status, Step};
use crate::transcription::alerts::ClientError;
#[cfg(verus_only)]
use crate::transcription::connection::{Connection, Protection, Receive};
use crate::transcription::middlebox::ClientConnection;
#[cfg(verus_only)]
use crate::transcription::middlebox::ClientReceive;
#[cfg(verus_only)]
use crate::transcription::primitives::Primitives;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The crate's driver, as its contracts fix it.
// ---------------------------------------------------------------------------

/// What the caller asks of the driver: bytes from the server (the next
/// chunk of the stream, in any size), application data to send, or a
/// close. The driver has no KeyUpdate operation of its own
/// (`driver_exec::Driver`: `step`, `send`, `close`, `eof`).
pub enum Op {
    /// The next bytes of the server's stream.
    Feed(Seq<u8>),
    /// Application data to send.
    Send(Seq<u8>),
    /// §6.1: close the write side.
    Close,
}

/// The crate's driver as its caller sees it: the running machine, the
/// status, and the bytes the caller holds (`driver_spec` choice 3: one
/// record per step; the caller resubmits the rest).
pub struct CState {
    /// The running machine.
    pub stage: Stage,
    /// Where the connection is.
    pub status: Status,
    /// Bytes the caller holds for the next step.
    pub held: Seq<u8>,
}

/// One step of the Hello stage, as `driver_contract::hello_step_ensures`
/// fixes it: the bootstrap's `feed`, and what its action comes to.
pub open spec fn hello_out(m: Models, boot: crate::hello::bootstrap_spec::State, framing: Seq<u8>,
    scalar: Seq<u8>, input: Seq<u8>) -> (nat, Step)
{
    let e = crate::hello::bootstrap_spec::feed(m.crypto.hash, boot, framing, input);
    (e.consumed, hello_act(m, scalar, e.state, e.framing, e.action))
}

/// What the bootstrap's action comes to (`driver_contract::hello_step_ensures`),
/// from its state and framer after the step.
pub open spec fn hello_act(m: Models, scalar: Seq<u8>, state: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, action: crate::hello::bootstrap_spec::Action) -> Step
{
    match action {
        crate::hello::bootstrap_spec::Action::None => Step { send: seq![], deliver: seq![],
            stage: Stage::Hello(state, framing), status: Status::Handshaking },
        crate::hello::bootstrap_spec::Action::Send(wire) => {
            let (acked, after) = crate::hello::bootstrap_spec::acknowledge(m.crypto.hash, state, wire);
            match after {
                crate::hello::bootstrap_spec::Action::None => Step { send: wire, deliver: seq![],
                    stage: Stage::Hello(acked, framing), status: Status::Handshaking },
                crate::hello::bootstrap_spec::Action::Established(_, _, _) => Step {
                    send: wire + crate::connection::driver_contract::established_step(m, after, scalar).send,
                    ..crate::connection::driver_contract::established_step(m, after, scalar)
                },
                crate::hello::bootstrap_spec::Action::Fail(a) => Step {
                    send: wire + crate::connection::driver_spec::hello_failure(a).send,
                    ..crate::connection::driver_spec::hello_failure(a)
                },
                _ => crate::connection::driver_spec::hello_failure(crate::spec::INTERNAL_ERROR),
            }
        },
        crate::hello::bootstrap_spec::Action::Established(_, _, _) =>
            crate::connection::driver_contract::established_step(m, action, scalar),
        crate::hello::bootstrap_spec::Action::Alert(a) => crate::connection::driver_spec::peer_failed(a),
        crate::hello::bootstrap_spec::Action::Fail(a) => crate::connection::driver_spec::hello_failure(a),
        crate::hello::bootstrap_spec::Action::Close => crate::connection::driver_spec::hello_closed(),
    }
}

/// The dispatcher's ciphers over the driver's AEAD.
pub open spec fn ciphers(m: Models) -> crate::connection::dispatcher_spec::Ciphers {
    crate::connection::dispatcher_spec::Ciphers { seal: m.cipher.seal, open: m.cipher.open }
}

/// One step of the driver (`Driver::step`), as `driver_contract::step_ensures`
/// fixes it: the octets consumed and the step.
pub open spec fn cstep(m: Models, stage: Stage, status: Status, scalar: Seq<u8>, input: Seq<u8>) -> (nat, Step) {
    match stage {
        Stage::Hello(boot, framing) => hello_out(m, boot, framing, scalar, input),
        Stage::Flight(s) => {
            let r = crate::connection::dispatcher_spec::feed(m.crypto, m.verification, ciphers(m), s, input);
            (r.0, crate::connection::driver_spec::flight_out(m.crypto, m.verification, ciphers(m), r.1, r.2))
        },
        Stage::App(s) => {
            let r = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, s,
                crate::connection::post_handshake_spec::Input::Bytes(input));
            (r.2, crate::connection::driver_spec::carry_out(m.cipher, r.0, r.1))
        },
        Stage::Ended => (0, crate::connection::driver_contract::unchanged(stage, status)),
    }
}

/// `Driver::send`, as `driver_contract::send_ensures` fixes it.
pub open spec fn csend(m: Models, stage: Stage, status: Status, data: Seq<u8>) -> Step {
    match stage {
        Stage::App(s) => {
            let r = crate::connection::post_handshake_spec::send_application(m.crypto, m.cipher, s, data);
            crate::connection::driver_spec::carry_out(m.cipher, r.0, r.1)
        },
        _ => crate::connection::driver_contract::unchanged(stage, status),
    }
}

/// `Driver::close`, as `driver_contract::close_ensures` fixes it.
pub open spec fn cclose(m: Models, stage: Stage, status: Status) -> Step {
    match stage {
        Stage::App(s) => {
            let r = crate::connection::post_handshake_spec::close(m.cipher, s);
            crate::connection::driver_spec::carry_out(m.cipher, r.0, r.1)
        },
        Stage::Hello(_, _) => crate::connection::driver_spec::hello_closed(),
        Stage::Flight(s) => crate::connection::driver_spec::flight_closed(
            crate::connection::dispatcher_spec::close_wire(ciphers(m), s)),
        Stage::Ended => crate::connection::driver_contract::unchanged(stage, status),
    }
}

/// `Driver::connect`, as `driver_contract::connect_ensures` fixes it.
pub open spec fn cstart(m: Models, config: crate::hello::client_spec::Config) -> Step {
    let failed = |alert: u8| Step { send: seq![], deliver: seq![], stage: Stage::Ended,
        status: Status::Failed(alert, Origin::NotSent) };
    match crate::hello::bootstrap_spec::start(config) {
        Ok((s0, crate::hello::bootstrap_spec::Action::Send(wire))) => {
            let (s1, a1) = crate::hello::bootstrap_spec::acknowledge(m.crypto.hash, s0, wire);
            if a1 is None {
                Step { send: wire, deliver: seq![], stage: Stage::Hello(s1, seq![]), status: Status::Handshaking }
            } else {
                failed(crate::spec::INTERNAL_ERROR)
            }
        },
        Ok(_) => failed(crate::spec::INTERNAL_ERROR),
        Err(alert) => failed(alert),
    }
}

/// One operation of the caller on the crate's driver: what it sends,
/// delivers and reports (the step), and the driver after it.
pub open spec fn cop(m: Models, scalar: Seq<u8>, cs: CState, op: Op) -> (Step, CState) {
    match op {
        Op::Feed(chunk) => {
            let input = cs.held + chunk;
            let (k, out) = cstep(m, cs.stage, cs.status, scalar, input);
            (out, CState { stage: out.stage, status: out.status, held: input.skip(k as int) })
        },
        Op::Send(data) => {
            let out = csend(m, cs.stage, cs.status, data);
            (out, CState { stage: out.stage, status: out.status, held: cs.held })
        },
        Op::Close => {
            let out = cclose(m, cs.stage, cs.status);
            (out, CState { stage: out.stage, status: out.status, held: cs.held })
        },
    }
}

/// The contracts fix the driver's step: every output `Driver::step` may give
/// is [`cstep`]'s.
pub proof fn lemma_cstep(m: Models, stage: Stage, status: Status, scalar: Seq<u8>, input: Seq<u8>,
    consumed: nat, out: Step)
    requires crate::connection::driver_contract::step_ensures(m, stage, status, scalar, input, consumed, out),
    ensures (consumed, out) == cstep(m, stage, status, scalar, input),
{
    match stage {
        Stage::Hello(boot, framing) => {
            let e = crate::hello::bootstrap_spec::feed(m.crypto.hash, boot, framing, input);
            if e.action is None {
                assert(out.send =~= Seq::<u8>::empty());
                assert(out.deliver =~= Seq::<u8>::empty());
            }
            if let crate::hello::bootstrap_spec::Action::Send(wire) = e.action {
                let (acked, after) = crate::hello::bootstrap_spec::acknowledge(m.crypto.hash, e.state, wire);
                if after is None {
                    assert(out.deliver =~= Seq::<u8>::empty());
                }
            }
        },
        _ => {},
    }
}

/// The contracts fix the start: `Driver::connect` gives [`cstart`].
pub proof fn lemma_cstart(m: Models, config: crate::hello::client_spec::Config, out: Step)
    requires crate::connection::driver_contract::connect_ensures(m, config, out),
    ensures out == cstart(m, config),
{
}

// ---------------------------------------------------------------------------
// The transcription's client, as its caller drives it.
// ---------------------------------------------------------------------------

/// The transcription's client as its caller holds it: the
/// `middlebox::ClientConnection`, the bytes of the stream not yet read as a
/// whole record, and whether the caller has closed the write side (the
/// transcription itself has no write-closed state, see
/// `post_handshake`'s "Not covered"; its caller does not write after
/// `close_write`, §6.1).
pub struct TState {
    /// The client.
    pub client: ClientConnection,
    /// Bytes of the stream not yet read.
    pub buffer: Seq<u8>,
    /// The caller wrote `close_write`'s record.
    pub write_closed: bool,
}

/// How a call left the transcription's client.
pub enum TEnd {
    /// It goes on.
    Running,
    /// §6.2: it aborted with this error (its caller wrote `abort_record`).
    Aborted(ClientError),
    /// §6: the peer's error alert.
    Peer(nat),
}

/// What a call of the transcription's client gives: the bytes written, the
/// application data delivered, the client after it and how it ended.
pub struct TOut {
    /// Bytes written, in order.
    pub send: Seq<u8>,
    /// Application data delivered, in order.
    pub deliver: Seq<u8>,
    /// The client after the call.
    pub after: TState,
    /// How it ended.
    pub end: TEnd,
}

/// The transcription's records, one after the other.
pub open spec fn flat(records: Seq<Seq<u8>>) -> Seq<u8> {
    super::ccs::flatten(records)
}

/// The transcription's caller on the next chunk of the stream: it reads at
/// most one whole record of what it holds, as `connection::receive_stream`
/// reads its first (`record::read_record_header`, `record_length_failure`,
/// five bytes and `length` more), with `middlebox::client_receive_stream` of
/// that record (so D.4's dummy record included); otherwise it holds the
/// bytes. On an abort it writes `connection::abort_record` of the error, at
/// the connection it had when the record arrived.
pub open spec fn tfeed(p: Primitives, ts: TState, chunk: Seq<u8>) -> TOut {
    let w = ts.buffer + chunk;
    let c = ts.client.connection;
    let wait = TOut { send: seq![], deliver: seq![], after: TState { buffer: w, ..ts }, end: TEnd::Running };
    match crate::transcription::record::read_record_header(w) {
        None => wait,
        Some(header) =>
            if !c.read_closed && crate::transcription::connection::record_length_failure(c, header) is Some {
                let e = crate::transcription::connection::record_length_failure(c, header)->0;
                TOut { send: crate::transcription::connection::abort_record(p, c, e), deliver: seq![], after: ts,
                    end: TEnd::Aborted(e) }
            } else if w.len() < 5 + header.length {
                wait
            } else {
                let b = w.subrange(0, (5 + header.length) as int);
                let rest = w.subrange((5 + header.length) as int, w.len() as int);
                match crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 {
                    ClientReceive::Abort(e) => TOut { send: crate::transcription::connection::abort_record(p, c, e),
                        deliver: seq![], after: ts, end: TEnd::Aborted(e) },
                    ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
                    ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                        send: flat(records_to_send), deliver: application_data,
                        after: TState { client, buffer: rest, ..ts }, end: TEnd::Running },
                }
            },
    }
}

/// The transcription's caller sends application data
/// (`connection::send_application_data`; after the handshake D.4 adds
/// nothing, `middlebox`'s last modelling choice). Before CONNECTED nothing
/// is sent; after its `close_write`, the caller sends nothing.
pub open spec fn tsend(p: Primitives, ts: TState, data: Seq<u8>) -> TOut {
    let quiet = TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Running };
    if ts.write_closed {
        quiet
    } else {
        match crate::transcription::connection::send_application_data(p, ts.client.connection, data) {
            crate::transcription::connection::SendResult::NotConnected => quiet,
            crate::transcription::connection::SendResult::Sent(records, c2) => TOut { send: flat(records),
                deliver: seq![], after: TState { client: ClientConnection { connection: c2, ..ts.client }, ..ts },
                end: TEnd::Running },
        }
    }
}

/// The transcription's caller closes its write side (§6.1,
/// `connection::close_write`), once.
pub open spec fn tclose(p: Primitives, ts: TState) -> TOut {
    if ts.write_closed {
        TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Running }
    } else {
        TOut { send: crate::transcription::connection::close_write(p, ts.client.connection), deliver: seq![],
            after: TState { write_closed: true, ..ts }, end: TEnd::Running }
    }
}

/// One operation of the caller on the transcription's client.
pub open spec fn top(p: Primitives, ts: TState, op: Op) -> TOut {
    match op {
        Op::Feed(chunk) => tfeed(p, ts, chunk),
        Op::Send(data) => tsend(p, ts, data),
        Op::Close => tclose(p, ts),
    }
}

/// The transcription's start (`middlebox::start_client`) for the crate's
/// ClientHello, with the crate's scalar as the X25519 private key (and as
/// the one for a HelloRetryRequest that selects a group, which this
/// profile never accepts).
pub open spec fn tstart(p: Primitives, config: crate::hello::client_spec::Config,
    tconfig: crate::transcription::middlebox::ClientConfig, scalar: Seq<u8>) -> (TState, Seq<u8>)
{
    let first = super::client::ch_view(crate::hello::client_spec::client_hello(config, Seq::empty()));
    let (cl, records) = crate::transcription::middlebox::start_client(p, tconfig, first, scalar, scalar);
    (TState { client: cl, buffer: seq![], write_closed: false }, flat(records))
}

// ---------------------------------------------------------------------------
// The transcription's caller, record by record.
// ---------------------------------------------------------------------------

/// With a whole record `b` at the front of what it holds, the
/// transcription's caller reads exactly `b`: its result is
/// `client_receive_stream` of `b` (`record_length_failure` comes first on
/// both), and it holds the rest.
pub proof fn lemma_tfeed_whole(p: Primitives, ts: TState, chunk: Seq<u8>)
    requires
        !ts.client.connection.read_closed,
        (ts.buffer + chunk).len() >= 5,
        (ts.buffer + chunk).len() >= 5 + super::bootstrap::length(ts.buffer + chunk),
    ensures ({
        let w = ts.buffer + chunk;
        let n = 5 + super::bootstrap::length(w);
        let b = w.take(n as int);
        let c = ts.client.connection;
        &&& super::bootstrap::whole_record(b)
        &&& tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 {
            ClientReceive::Abort(e) => TOut { send: crate::transcription::connection::abort_record(p, c, e),
                deliver: seq![], after: ts, end: TEnd::Aborted(e) },
            ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
            ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                send: flat(records_to_send), deliver: application_data,
                after: TState { client, buffer: w.skip(n as int), ..ts }, end: TEnd::Running },
        }
    }),
{
    let w = ts.buffer + chunk;
    let n = 5 + super::bootstrap::length(w);
    let b = w.take(n as int);
    let c = ts.client.connection;
    super::framing::lemma_t_header(w);
    assert(b.subrange(3, 5) =~= w.subrange(3, 5));
    super::framing::lemma_t_header(b);
    assert(w.subrange(0, n as int) =~= b);
    assert(w.subrange(n as int, w.len() as int) =~= w.skip(n as int));
    let header = crate::transcription::record::read_record_header(w)->Some_0;
    assert(b.subrange(0, 5) =~= w.subrange(0, 5));
    assert(b.subrange(1, 3) =~= w.subrange(1, 3));
    assert(crate::transcription::record::read_record_header(b) == crate::transcription::record::read_record_header(w));
    super::framing::lemma_client_lifted(p, ts.client, b);
    if crate::transcription::connection::record_length_failure(c, header) is Some {
        assert(crate::transcription::connection::receive_stream(p, c, b).0
            == Receive::Abort(crate::transcription::connection::record_length_failure(c, header)->0));
    }
}

/// With no whole record at the front of what it holds, the transcription's
/// caller holds the bytes, or refuses the header's length (the framing
/// theorem's [`super::framing::split`] with no record).
pub proof fn lemma_tfeed_partial(p: Primitives, ts: TState, chunk: Seq<u8>)
    requires
        !ts.client.connection.read_closed,
        (ts.buffer + chunk).len() < 5 || (ts.buffer + chunk).len() < 5 + super::bootstrap::length(ts.buffer + chunk),
    ensures ({
        let w = ts.buffer + chunk;
        let c = ts.client.connection;
        let sp = super::framing::split(c, w);
        &&& sp.records.len() == 0
        &&& tfeed(p, ts, chunk) == match sp.end {
            super::framing::SplitEnd::Partial(_) =>
                TOut { send: seq![], deliver: seq![], after: TState { buffer: w, ..ts }, end: TEnd::Running },
            super::framing::SplitEnd::TooLong(e) => TOut {
                send: crate::transcription::connection::abort_record(p, c, e), deliver: seq![], after: ts,
                end: TEnd::Aborted(e) },
        }
    }),
{
    let w = ts.buffer + chunk;
    if w.len() >= 5 {
        super::framing::lemma_t_header(w);
    } else {
        assert(crate::transcription::record::read_record_header(w) is None) by {
            reveal_with_fuel(crate::transcription::record::read_record_header, 1);
        }
    }
}

// ---------------------------------------------------------------------------
// Encodings.
// ---------------------------------------------------------------------------

/// The crate's records, one after the other, are the transcription's.
pub proof fn lemma_concat_flat(wires: Seq<Seq<u8>>)
    ensures crate::connection::driver_spec::concat(wires) == flat(wires),
    decreases wires.len(),
{
    if wires.len() > 0 {
        lemma_concat_flat(wires.drop_last());
        lemma_flat_push(wires.drop_last(), wires.last());
        assert(wires.drop_last().push(wires.last()) =~= wires);
    }
}

/// [`flat`] of a list with one more record.
pub proof fn lemma_flat_push(records: Seq<Seq<u8>>, r: Seq<u8>)
    ensures flat(records.push(r)) == flat(records) + r,
    decreases records.len(),
{
    if records.len() == 0 {
        super::ccs::lemma_flatten(r, r);
        assert(records.push(r) =~= seq![r]);
        assert(flat(records) == Seq::<u8>::empty());
        assert(Seq::<u8>::empty() + r =~= r);
    } else {
        lemma_flat_push(records.skip(1), r);
        assert(records.push(r).skip(1) =~= records.skip(1).push(r));
        assert(records.push(r)[0] == records[0]);
        assert(records[0] + (flat(records.skip(1)) + r) =~= (records[0] + flat(records.skip(1))) + r);
    }
}

/// [`flat`] of two lists.
pub proof fn lemma_flat_append(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures flat(a + b) == flat(a) + flat(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(flat(b) == Seq::<u8>::empty());
        assert(flat(a) + Seq::<u8>::empty() =~= flat(a));
    } else {
        lemma_flat_append(a, b.drop_last());
        lemma_flat_push(a + b.drop_last(), b.last());
        lemma_flat_push(b.drop_last(), b.last());
        assert((a + b.drop_last()).push(b.last()) =~= a + b);
        assert(b.drop_last().push(b.last()) =~= b);
        assert(flat(a) + flat(b.drop_last()) + b.last() =~= flat(a) + (flat(b.drop_last()) + b.last()));
    }
}

/// §5.1, §6: a plaintext alert record is the transcription's
/// `write_tls_plaintext` of the encoded alert, with version 0x0303.
pub proof fn lemma_plaintext_alert(level: u8, description: u8)
    ensures
        crate::connection::driver_spec::plaintext_alert(level, description)
            == crate::transcription::record::write_tls_plaintext(21, 0x0303, seq![level, description]),
{
    super::record::lemma_write_plaintext(21, 0x0303, seq![level, description]);
    assert(crate::spec::write_u16(0x0303) == seq![3u8, 3u8]) by (compute_only);
    assert(crate::spec::be_bytes(2, 2) == seq![0u8, 2u8]) by (compute_only);
    assert(crate::spec::write_plaintext(21, 0x0303, seq![level, description])
        =~= crate::connection::driver_spec::plaintext_alert(level, description));
}

/// Before the handshake keys (the read side unprotected, A.1's WAIT_SH),
/// the transcription's `alert_record` is the plaintext alert, fatal unless
/// a closure alert (§6, §6.2).
pub proof fn lemma_alert_record_plain(p: Primitives, c: Connection, description: u8)
    requires
        c.send == Protection::Unprotected,
        c.handshake.state == crate::transcription::state_machine::ClientState::WaitSh,
    ensures
        crate::transcription::connection::alert_record(p, c, description as nat)
            == crate::connection::driver_spec::plaintext_alert(
                if description == 0 || description == 90 { 1u8 } else { 2u8 }, description),
{
    let level: u8 = if description == 0 || description == 90 { 1u8 } else { 2u8 };
    assert(crate::transcription::alerts::write_alert(description as nat) =~= seq![level, description]);
    lemma_plaintext_alert(level, description);
}

// ---------------------------------------------------------------------------
// The relation.
// ---------------------------------------------------------------------------

/// A.1's WAIT_SH fields that the dispatcher's start needs (the start inputs
/// of `dispatcher::accepts_server_hello`): the private key is the crate's
/// scalar (also the one for a HelloRetryRequest selecting a group, which
/// this profile never accepts), and the fields A.1 sets only from WAIT_EE
/// on (the server's key, a CertificateRequest context) are unset.
pub open spec fn wait_sh_fields(hs: crate::transcription::state_machine::ClientHandshake, scalar: Seq<u8>) -> bool {
    &&& hs.x25519_private_key == scalar
    &&& hs.retry_private_key == scalar
    &&& scalar.len() == 32
    &&& hs.server_public_key.len() == 0
    &&& hs.certificate_request_context is None
}

/// The two certificate validators agree for a host and time
/// (`auth_flight::chain_agrees`, X.509 being a parameter on both sides), and
/// the crate's 16 KiB key cap never fires: the dispatcher theorem's
/// `validator_agrees`.
pub open spec fn validators(v: crate::auth::spec::Verification, p: Primitives, host: crate::host::spec::Host,
    now: u64) -> bool
{
    &&& super::auth_flight::chain_agrees(v, p, host, now)
    &&& forall|body: Seq<u8>| #[trigger] (v.chain)(host, now, body) matches Ok(key)
        ==> key.len() <= crate::auth::spec::MAX_KEY
}

/// Every hypothesis of the theorem, each true of what both sides model and
/// each one of the theorems below: the two sides' primitives are the same
/// functions, with the lengths both model (`dispatcher::hypotheses`,
/// `post_handshake::hypotheses`), X25519 agrees (`keys::x25519_agrees`),
/// and the certificate validators agree ([`validators`]).
pub open spec fn hypotheses(m: Models, p: Primitives) -> bool {
    &&& super::dispatcher::hypotheses(m.crypto, m.verification, ciphers(m), p)
    &&& super::post_handshake::hypotheses(m.crypto, m.cipher, p)
    &&& super::keys::x25519_agrees(m.exchange, p)
    &&& forall|host: crate::host::spec::Host, now: u64| #[trigger] validators(m.verification, p, host, now)
}

/// The Hello stage and the transcription's client agree: the bootstrap
/// theorem's relation; the transcription holds the bytes the framer and
/// the caller hold, a prefix of a record the framer waits on; WAIT_SH's
/// fields ([`wait_sh_fields`]).
pub open spec fn hello_agrees(p: Primitives, scalar: Seq<u8>,
    s: crate::hello::bootstrap_spec::State, framing: Seq<u8>, held: Seq<u8>, ts: TState) -> bool
{
    &&& super::bootstrap::bootstrap_agrees(p, s, ts.client)
    &&& ts.buffer == framing + held
    &&& crate::connection::framing_spec::wf_mode(framing, false)
    &&& crate::spec::read_record(framing, false) is NeedMore
    &&& !ts.write_closed
    &&& wait_sh_fields(ts.client.connection.handshake, scalar)
}

/// The flight stage and the transcription's client agree: the dispatcher
/// theorem's relation (its framer emptied), and the transcription holds the
/// bytes the framer and the caller hold.
pub open spec fn flight_agrees(p: Primitives, v: crate::auth::spec::Verification,
    s: crate::connection::dispatcher_spec::State, held: Seq<u8>, ts: TState) -> bool
{
    &&& s.mode == crate::connection::dispatcher_spec::Mode::Handshake
    &&& crate::connection::framing_spec::wf_mode(s.framing, true)
    &&& crate::spec::read_record(s.framing, true) is NeedMore
    &&& super::dispatcher::dispatcher_agrees(p, v, crate::connection::dispatcher_spec::State { framing: seq![], ..s },
        ts.client)
    &&& ts.buffer == s.framing + held
    &&& !ts.write_closed
}

/// The application stage and the transcription's client agree: the
/// post-handshake theorem's relation with the read side open (the driver
/// closes as soon as the server's close_notify arrives, `driver_spec`
/// choice 5), the bytes held, the write side closed on both sides together,
/// and the status that of the phase.
pub open spec fn app_agrees(s: crate::connection::post_handshake_spec::State, status: Status, held: Seq<u8>,
    ts: TState) -> bool
{
    &&& super::post_handshake::post_agrees(s, ts.client.connection)
    &&& crate::connection::post_handshake_spec::can_read(s)
    &&& ts.buffer == held
    &&& ts.write_closed == (s.phase == crate::connection::post_handshake_spec::Phase::WriteClosed)
    &&& status == (if s.phase == crate::connection::post_handshake_spec::Phase::WriteClosed { Status::Closing }
        else { Status::Open })
}

/// **The state relation**: the driver and the transcription's client stand
/// for the same connection, by the running machine's own relation. An
/// ended driver agrees with nothing: the comparison has ended.
pub open spec fn driver_agrees(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState) -> bool {
    match cs.stage {
        Stage::Hello(s, framing) => cs.status == Status::Handshaking
            && hello_agrees(p, scalar, s, framing, cs.held, ts),
        Stage::Flight(s) => cs.status == Status::Handshaking && flight_agrees(p, m.verification, s, cs.held, ts),
        Stage::App(s) => app_agrees(s, cs.status, cs.held, ts),
        Stage::Ended => false,
    }
}

// ---------------------------------------------------------------------------
// How one operation's outcomes compare.
// ---------------------------------------------------------------------------

/// Both go on: the same bytes sent and delivered, and agreeing states.
pub open spec fn goes_on(m: Models, p: Primitives, scalar: Seq<u8>, cout: Step, cs2: CState, tout: TOut) -> bool {
    &&& cout.send == tout.send
    &&& cout.deliver == tout.deliver
    &&& tout.end is Running
    &&& driver_agrees(m, p, scalar, cs2, tout.after)
}

/// Both end the same way, with the same bytes: a failure of the client
/// with the same alert (the crate's last record is the transcription's
/// `abort_record`), or the server's error alert.
pub open spec fn ends_alike(cout: Step, tout: TOut) -> bool {
    &&& cout.stage is Ended
    &&& cout.send == tout.send
    &&& cout.deliver == tout.deliver
    &&& match (cout.status, tout.end) {
        (Status::Failed(a, Origin::Sent), TEnd::Aborted(e)) => crate::transcription::alerts::required_alert(e) == a as nat,
        (Status::Failed(d, Origin::Peer), TEnd::Peer(d2)) => d as nat == d2,
        _ => false,
    }
}

/// The crate ends the connection with a failure of its own.
pub open spec fn crate_fails(cout: Step) -> bool {
    &&& cout.stage is Ended
    &&& cout.status matches Status::Failed(_, origin) && origin != Origin::Peer
    &&& cout.deliver.len() == 0
}

/// There is a whole record at the front of the stream `w`.
pub open spec fn whole(w: Seq<u8>) -> bool {
    w.len() >= 5 && w.len() >= 5 + super::bootstrap::length(w)
}

/// That record.
pub open spec fn front(w: Seq<u8>) -> Seq<u8> {
    w.take((5 + super::bootstrap::length(w)) as int)
}

/// **Rejections**, as #139 compares them: the crate fails on the whole
/// record `b` at the front of the stream, and the record-level theorem of
/// the running machine holds of `b`. It says how the transcription's
/// handling of `b` relates: it aborts with the same alert, or with a
/// failure list the crate's alert is in, or a stated difference holds
/// (`bootstrap::fail_agrees`, `dispatcher::fail_agrees`,
/// `post_handshake::fail_agrees`).
pub open spec fn rejects_record(m: Models, p: Primitives, cs: CState, ts: TState, chunk: Seq<u8>, cout: Step) -> bool {
    let w = ts.buffer + chunk;
    let b = front(w);
    &&& crate_fails(cout)
    &&& whole(w)
    &&& match cs.stage {
        Stage::Hello(s, _) => {
            &&& crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, b).1
                == crate::hello::bootstrap_spec::Action::Fail(cout.status->Failed_0)
            &&& super::bootstrap::record_agrees(p, s, ts.client, b)
        },
        Stage::Flight(s) => {
            let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
            &&& crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0, b).0
                is Fail
            &&& super::dispatcher::record_agrees(m.crypto, m.verification, ciphers(m), p, s0, ts.client, b)
        },
        Stage::App(s) => {
            let r = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, s,
                crate::connection::post_handshake_spec::Input::Bytes(b));
            &&& r.0.end is Fail
            &&& super::post_handshake::record_agrees(p, m.cipher, s, ts.client.connection, b, r,
                crate::transcription::connection::receive_stream(p, ts.client.connection, b).0)
        },
        Stage::Ended => false,
    }
}

/// **Stated difference, timing** (`framing::early_reject`): the crate
/// rejects a record from its header alone, before the body has arrived; the
/// transcription waits for the body, or refuses the header's length
/// (`framing::too_long_agrees`). Every completion of the record is rejected
/// by both (`framing::lemma_early_reject`).
pub open spec fn rejects_early(cs: CState, ts: TState, chunk: Seq<u8>, cout: Step, tout: TOut) -> bool {
    let w = ts.buffer + chunk;
    let protected = !(cs.stage is Hello);
    &&& crate_fails(cout)
    &&& super::framing::early_reject(w, protected, cout.status->Failed_0)
    &&& ((tout.end is Running && tout.send.len() == 0 && tout.after.buffer == w)
        || (tout.end matches TEnd::Aborted(e)
            && super::framing::too_long_agrees(super::framing::SplitEnd::TooLong(e), w, protected, cout.status->Failed_0)))
}

/// **Stated difference, the server's close_notify** (§6.1): the crate
/// answers it with exactly the transcription's `close_write` record (if its
/// write side is open) and ends the connection (`driver_spec` choice 5,
/// and the dispatcher's and bootstrap's closing); the transcription stops
/// reading (`read_closed`) and writes nothing.
pub open spec fn peer_closed(p: Primitives, ts: TState, cout: Step, tout: TOut) -> bool {
    &&& cout.stage is Ended
    &&& cout.status == Status::Closed
    &&& cout.send == (if ts.write_closed { Seq::<u8>::empty() }
        else { crate::transcription::connection::close_write(p, ts.client.connection) })
    &&& cout.deliver == tout.deliver
    &&& tout.end is Running
    &&& tout.send.len() == 0
    &&& tout.after.client.connection.read_closed
}

/// **Stated difference, a failure after ClientHello2** (`bootstrap`'s
/// "ClientHello2 sent before a coalesced message's failure"): the record of
/// an accepted HelloRetryRequest holds a later message that fails (or a
/// ServerHello with an all-zero shared secret). The crate has sent
/// ClientHello2 (acknowledged at once, `driver_spec` choice 2) before the
/// later messages are read, then its alert; the transcription's abort
/// writes no ClientHello2, only its alert. `bootstrap::record_agrees` holds
/// of the record, and relates the two alerts.
pub open spec fn retry_then_fails(m: Models, p: Primitives, cs: CState, ts: TState, chunk: Seq<u8>, cout: Step,
    tout: TOut) -> bool
{
    let w = ts.buffer + chunk;
    let b = front(w);
    &&& crate_fails(cout)
    &&& whole(w)
    &&& cs.stage matches Stage::Hello(s, _)
    &&& crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, b).1
        matches crate::hello::bootstrap_spec::Action::Send(wire)
    &&& cout.send == wire + crate::connection::driver_spec::hello_failure(cout.status->Failed_0).send
    &&& tout.end is Aborted
    &&& tout.send == crate::transcription::connection::abort_record(p, ts.client.connection, tout.end->Aborted_0)
    &&& super::bootstrap::record_agrees(p, s, ts.client, b)
}

/// How the outcomes of feeding `chunk` compare: both go on in agreeing
/// states with the same outputs, or both end alike, or a rejection or a
/// stated difference ends the comparison (each a definition above).
pub open spec fn feed_verdict(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>,
    cout: Step, cs2: CState, tout: TOut) -> bool
{
    ||| goes_on(m, p, scalar, cout, cs2, tout)
    ||| ends_alike(cout, tout)
    ||| rejects_record(m, p, cs, ts, chunk, cout)
    ||| rejects_early(cs, ts, chunk, cout, tout)
    ||| peer_closed(p, ts, cout, tout)
    ||| retry_then_fails(m, p, cs, ts, chunk, cout, tout)
}

/// The outcomes of one operation compare.
pub open spec fn op_agrees(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, op: Op) -> bool {
    let (cout, cs2) = cop(m, scalar, cs, op);
    let tout = top(p, ts, op);
    match op {
        Op::Feed(chunk) => feed_verdict(m, p, scalar, cs, ts, chunk, cout, cs2, tout),
        _ => goes_on(m, p, scalar, cout, cs2, tout),
    }
}

// ---------------------------------------------------------------------------
// The Hello stage.
// ---------------------------------------------------------------------------

/// The Hello stage's step on the stream `x = framing + input`: with no whole
/// record at the front it waits, holding all of it, or rejects the header
/// early; with a whole record `b` it is the bootstrap's whole-record step
/// (`bootstrap_lemmas::record_step`) on `b`, having consumed exactly `b`
/// unless it failed.
pub proof fn lemma_hello_crate(m: Models, s: crate::hello::bootstrap_spec::State, framing: Seq<u8>,
    scalar: Seq<u8>, input: Seq<u8>, c: Connection)
    requires
        c.receive == Protection::Unprotected,
        s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello,
        crate::connection::framing_spec::wf_mode(framing, false),
        crate::spec::read_record(framing, false) is NeedMore,
    ensures ({
        let x = framing + input;
        let (k, out) = hello_out(m, s, framing, scalar, input);
        &&& k <= input.len()
        &&& if whole(x) {
            let (s2, a) = crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(x));
            &&& out == hello_act(m, scalar, s2, seq![], a)
            &&& (!(a is Fail) ==> framing.len() + k == 5 + super::bootstrap::length(x))
            &&& (!(a is Fail) ==> input.skip(k as int) == x.skip((5 + super::bootstrap::length(x)) as int))
        } else {
            ||| (k == input.len() && out == hello_act(m, scalar, s, x, crate::hello::bootstrap_spec::Action::None)
                && crate::connection::framing_spec::wf_mode(x, false)
                && crate::spec::read_record(x, false) is NeedMore)
            ||| (out.status matches Status::Failed(a, _) && super::framing::early_reject(x, false, a)
                && out == crate::connection::driver_spec::hello_failure(a))
        }
    }),
{
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(crate::hello::bootstrap_spec::feed);
    let x = framing + input;
    super::framing::lemma_boot_feed(m.crypto.hash, s, framing, input);
    super::framing::lemma_first(x, x.len(), false);
    super::framing::lemma_framing_agrees(c, x, false);
    let (st, k) = super::framing::first(x, false);
    let n = 5 + super::bootstrap::length(x);
    match st {
        crate::connection::framing_spec::Status::Pending => {
            assert(x.take(x.len() as int) =~= x);
            super::framing::lemma_need_more_wf(x, false);
            if whole(x) {
                super::framing::lemma_t_header(x);
                assert(false);
            }
        },
        crate::connection::framing_spec::Status::Fail(a) => {
            if whole(x) {
                let b = x.take(n as int);
                let e = crate::spec::read_record(b, false)->Fail_0;
                super::framing::lemma_record_step_fail(m.crypto.hash, s, b, e);
            }
        },
        crate::connection::framing_spec::Status::Complete => {
            assert(x.take(k as int).subrange(3, 5) =~= x.subrange(3, 5));
            assert(k == n);
            assert(input.skip((k - framing.len()) as int) =~= x.skip(n as int));
        },
    }
}


/// What the Hello stage's step on a whole record comes to, given the
/// caller's state after it (`cs2`).
pub open spec fn hello_whole(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState) -> bool
{
    let w = ts.buffer + chunk;
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(w));
    let cout = hello_act(m, scalar, s2, seq![], a);
    let cs = CState { stage: Stage::Hello(s, framing), status: Status::Handshaking, held };
    (cs2.stage == cout.stage && cs2.status == cout.status
        && (!(a is Fail) ==> cs2.held == w.skip((5 + super::bootstrap::length(w)) as int)))
        ==> feed_verdict(m, p, scalar, cs, ts, chunk, cout, cs2, tfeed(p, ts, chunk))
}

/// What a whole record's step is on the transcription's side, and facts of
/// the relation the cases use.
pub proof fn lemma_hello_facts(p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
    ensures ({
        let w = ts.buffer + chunk;
        let b = front(w);
        let c = ts.client.connection;
        &&& super::bootstrap::whole_record(b)
        &&& super::bootstrap::record_agrees(p, s, ts.client, b)
        &&& crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0
            == super::dispatcher::lifted(ts.client, super::bootstrap::one_record(p, c, b))
        &&& c.send == Protection::Unprotected
        &&& c.receive == Protection::Unprotected
        &&& !c.read_closed
        &&& c.handshake.state == crate::transcription::state_machine::ClientState::WaitSh
        &&& s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello
        &&& tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 {
            ClientReceive::Abort(e) => TOut { send: crate::transcription::connection::abort_record(p, c, e),
                deliver: seq![], after: ts, end: TEnd::Aborted(e) },
            ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
            ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                send: flat(records_to_send), deliver: application_data,
                after: TState { client, buffer: w.skip((5 + super::bootstrap::length(w)) as int), ..ts },
                end: TEnd::Running },
        }
    }),
{
    let w = ts.buffer + chunk;
    let b = front(w);
    lemma_tfeed_whole(p, ts, chunk);
    super::framing::lemma_boot_record(p, s, ts.client, b);
    super::framing::lemma_client_lifted(p, ts.client, b);
    super::bootstrap::lemma_stream_one(p, ts.client.connection, b);
}

/// A failure of the crate's own on a whole record before the handshake
/// keys: both end alike when the transcription aborts with the same alert,
/// else the record-level theorem relates the two (a rejection).
pub proof fn lemma_hello_fail(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
        crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(ts.buffer + chunk)).1 is Fail,
    ensures hello_whole(m, p, scalar, s, framing, held, ts, chunk, cs2),
{
    hide(super::bootstrap::record_agrees);
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(super::bootstrap::one_record);
    hide(goes_on);
    hide(rejects_early);
    hide(peer_closed);
    hide(retry_then_fails);
    hide(super::bootstrap::bootstrap_agrees);
    let w = ts.buffer + chunk;
    let b = front(w);
    let c = ts.client.connection;
    lemma_hello_facts(p, scalar, s, framing, held, ts, chunk);
    let alert = crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, b).1->Fail_0;
    let u = crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0;
    if let ClientReceive::Abort(e) = u {
        if crate::transcription::alerts::required_alert(e) == alert as nat {
            super::dispatcher::lemma_required_not_closure(e);
            lemma_alert_record_plain(p, c, alert);
        }
    }
}

/// The peer's error alert before the handshake keys: both end alike.
pub proof fn lemma_hello_alert(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
        crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(ts.buffer + chunk)).1 is Alert,
    ensures hello_whole(m, p, scalar, s, framing, held, ts, chunk, cs2),
{
    lemma_hello_facts(p, scalar, s, framing, held, ts, chunk);
}

/// The server's close_notify before the handshake keys: the crate answers
/// with the transcription's `close_write` record and ends; the
/// transcription stops reading ([`peer_closed`]).
pub proof fn lemma_hello_close(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
        crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(ts.buffer + chunk)).1 is Close,
    ensures hello_whole(m, p, scalar, s, framing, held, ts, chunk, cs2),
{
    lemma_hello_facts(p, scalar, s, framing, held, ts, chunk);
    lemma_alert_record_plain(p, ts.client.connection, 0);
    let w = ts.buffer + chunk;
    let b = front(w);
    assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
}

/// A record that leaves the bootstrap waiting: both go on, writing and
/// delivering nothing, in agreeing states.
pub proof fn lemma_hello_none(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
        crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(ts.buffer + chunk)).1 is None,
    ensures hello_whole(m, p, scalar, s, framing, held, ts, chunk, cs2),
{
    let w = ts.buffer + chunk;
    let b = front(w);
    let c = ts.client.connection;
    lemma_hello_facts(p, scalar, s, framing, held, ts, chunk);
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
    let c2 = Connection { handshake_fragments: s2.reassembly.buf, ..c };
    let cl2 = super::framing::with_fragments(ts.client, s2.reassembly.buf);
    assert(super::bootstrap::bootstrap_agrees(p, s2, cl2));
    super::framing::lemma_boot_quiet(p, s, ts.client, b);
    super::framing::lemma_lifted_quiet(ts.client, c2);
    super::framing::lemma_empty(false);
    assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    assert(Seq::<u8>::empty() + w.skip((5 + super::bootstrap::length(w)) as int)
        =~= w.skip((5 + super::bootstrap::length(w)) as int));
}

} // verus!
