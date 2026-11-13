//! RFC 8446 §4.1, §5, §6 and §7.3 end to end: the crate's whole client
//! driver (`connection/driver_spec.rs`, as `connection/driver_contract.rs`
//! makes every operation of `driver_exec::Driver` a function of its state)
//! against the clean-room transcription's client (`middlebox::start_client`
//! and `client_receive_stream`, `connection::send_application_data`,
//! `close_write` and `alert_record`), from the configuration to the end of
//! the connection: [`theorem_driver_equivalence`].
//!
//! **What is compared.** Both sides are driven by the same caller
//! operations ([`Op`]): the next chunk of the server's stream, in any size
//! (so any chunking of the stream is some sequence of operations),
//! application data to send, and a close, interleaved in any order. The
//! crate's side is the driver as its contracts make it a function
//! ([`cop`]: `step` on what the caller holds plus the chunk, one record at
//! most, `driver_spec` choice 3; `send`; `close`), and `connect` at the start
//! ([`cstart`]); [`lemma_cstep`] and [`lemma_cstart`] show the contracts
//! leave no other output. The transcription's side is its caller
//! ([`top`]): it reads at most one whole record of what it holds per
//! chunk, as `connection::receive_stream` reads its first (so it waits
//! exactly when that function waits, and reads the same records), through
//! `middlebox::client_receive_stream`; on an abort it writes
//! `connection::abort_record`; it sends with `send_application_data` and
//! closes with `close_write`, and writes nothing after its close_notify
//! (the transcription has no write-closed state of its own).
//!
//! **The theorem** ([`theorem_driver_equivalence`]): from the start
//! ([`start_agrees`]: the crate's first record is `start_client`'s, against
//! the crate's own ClientHello and its scalar) every run of operations
//! compares operation by operation ([`run_agrees`], [`op_agrees`]): the
//! bytes sent, the plaintext delivered and the status are the
//! transcription's and both go on in agreeing states ([`driver_agrees`]),
//! across both handoffs (the bootstrap to the dispatcher at the ServerHello,
//! [`lemma_handoff`]; the dispatcher to the transducer at the acknowledged
//! client flight, `dispatcher::ack_agrees`); or both end alike
//! ([`ends_alike`]); or the crate rejects a record and the record-level
//! theorem of its stage relates the transcription's handling of it
//! ([`rejects_record`]: the alerts equal, or the crate's that of some
//! failure in the transcription's list, or a stated difference of that
//! theorem); or one of the stated differences below holds.
//!
//! **The state relation** ([`driver_agrees`]), by stage: the bootstrap
//! theorem's `bootstrap_agrees` with the bytes held and A.1's WAIT_SH fields
//! ([`hello_agrees`], [`wait_sh_fields`]); the dispatcher theorem's
//! `dispatcher_agrees` ([`flight_agrees`]); the post-handshake theorem's
//! `post_agrees` with the read side open and the write side closed on both
//! sides together ([`app_agrees`]); the status that of the stage.
//!
//! **KeyUpdate.** Both sides owe the answer to `update_requested` (§4.6.3:
//! "prior to sending its next Application Data record") and record it the
//! same way, a flag that `post_agrees` compares; neither sends anything on
//! reading the request, both send the answer first in the caller's next
//! send, and a second request while one is owed leaves one owed on both. So
//! the comparison is exact through every KeyUpdate ([`goes_on`]).
//!
//! **Hypotheses** ([`hypotheses`]), each one of the stage theorems': the
//! two sides' primitives are the same functions with the lengths both model;
//! X25519 agrees; and the two certificate validators agree for every host
//! and time, the crate's 16 KiB key cap never firing ([`validators`],
//! `dispatcher::validator_agrees`). For the start: the scalar is 32 octets
//! and its public value is the one the configuration offers, and the
//! transcription runs in the crate's compatibility mode.
//!
//! **The domain conditions the stage theorems left to the driver:**
//! - `dispatcher::accepts_server_hello`'s start inputs are discharged:
//!   every ClientHello the crate sends offers its nine signature schemes
//!   ([`lemma_offered_schemes`]), and `server_public_key` and
//!   `certificate_request_context` are unset in WAIT_SH, with the private
//!   key the crate's scalar, through a HelloRetryRequest
//!   ([`wait_sh_fields`], [`lemma_wait_sh_step`]).
//! - The all-zero X25519 shared secret is discharged: both refuse the
//!   ServerHello with `illegal_parameter`, and the crate's plaintext alert
//!   is the transcription's `abort_record` ([`lemma_handoff`]). With bytes
//!   after that ServerHello the two still name different faults (the
//!   bootstrap's `buffer_fail_agrees`, under [`rejects_record`]).
//! - Offers are the client's profile: discharged (`dispatcher::lemma_start`
//!   proves `dispatcher_agrees`, which holds `profile_extensions`, from the
//!   crate's own offers).
//! - The message type: no condition at the driver level. The record-level
//!   theorems compare every record, a message of the wrong type included
//!   (`dispatcher::wrong_type` is a case of its `fail_agrees`).
//! - The crate's resource policies are stated, not assumed: its caps
//!   (2^18 handshake message, the transcript and cookie caps of the Hello,
//!   `internal_error`) are cases of the record-level `fail_agrees` under
//!   [`rejects_record`] and [`retry_then_fails`], and so is the 4 MiB
//!   transcript cap in the flight (`dispatcher::transcript_cap`, a case of
//!   the dispatcher's `fail_agrees`: the crate refuses with
//!   `internal_error` a message the transcription accepts, which ends the
//!   comparison under [`rejects_record`]); the 16 KiB key cap is in
//!   [`validators`]. No record is outside the comparison.
//!
//! **Stated differences** (each a definition): [`rejects_early`] (the
//! framer's timing on a header), [`peer_closed`] (the server's close_notify:
//! the crate answers with the transcription's `close_write` record and
//! ends), [`retry_then_fails`] (ClientHello2 sent before a later message of
//! its record fails), [`goes_on_coalesced`] (the client's flight in one
//! record; the comparison goes on),
//! [`exhausted_epoch`], [`oversized`] (application data above 2^14 octets)
//! and [`closes_in_handshake`] (a close before the handshake completes ends
//! the crate's connection).
//!
//! **Not covered:** transport end of file (`Driver::eof`: the crate ends
//! with `Failed(internal_error, Truncated)` and sends nothing, whatever the
//! stage; `connection.rs` leaves transport closure out of scope, so there
//! is nothing to compare); a KeyUpdate of the caller's own (the driver has
//! no such operation; `post_handshake::update_agrees` covers the
//! transducer's `update_keys`).

#[cfg(verus_only)]
use crate::connection::driver_contract::Models;
#[cfg(verus_only)]
use crate::connection::driver_spec::{Origin, Step};
use crate::connection::driver_spec::{Stage, Status};
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
/// the connection it had when the record arrived, unless it has closed its
/// write side (§6.1, as for application data).
pub open spec fn tfeed(p: Primitives, ts: TState, chunk: Seq<u8>) -> TOut {
    let w = ts.buffer + chunk;
    let c = ts.client.connection;
    let alert = |e: ClientError| if ts.write_closed { Seq::<u8>::empty() }
        else { crate::transcription::connection::abort_record(p, c, e) };
    let wait = TOut { send: seq![], deliver: seq![], after: TState { buffer: w, ..ts }, end: TEnd::Running };
    match crate::transcription::record::read_record_header(w) {
        None => wait,
        Some(header) =>
            if !c.read_closed && crate::transcription::connection::record_length_failure(c, header) is Some {
                let e = crate::transcription::connection::record_length_failure(c, header)->0;
                TOut { send: alert(e), deliver: seq![], after: ts, end: TEnd::Aborted(e) }
            } else if w.len() < 5 + header.length {
                wait
            } else {
                let b = w.subrange(0, (5 + header.length) as int);
                let rest = w.subrange((5 + header.length) as int, w.len() as int);
                match crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 {
                    ClientReceive::Abort(e) => TOut { send: alert(e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
                    ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
                    ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                        send: flat(records_to_send), deliver: application_data,
                        after: TState { client, buffer: rest, ..ts }, end: TEnd::Running },
                }
            },
    }
}

/// What the transcription's caller writes on an abort.
pub open spec fn abort_bytes(p: Primitives, ts: TState, e: ClientError) -> Seq<u8> {
    if ts.write_closed { Seq::<u8>::empty() } else { crate::transcription::connection::abort_record(p, ts.client.connection, e) }
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
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e),
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
                send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
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
/// with the same alert (the crate's last record, if its write side is open,
/// is the transcription's `abort_record`), or the server's error alert.
pub open spec fn ends_alike(cout: Step, tout: TOut) -> bool {
    &&& cout.stage is Ended
    &&& cout.send == tout.send
    &&& cout.deliver == tout.deliver
    &&& match (cout.status, tout.end) {
        (Status::Failed(a, origin), TEnd::Aborted(e)) =>
            origin != Origin::Peer && crate::transcription::alerts::required_alert(e) == a as nat,
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
        else { crate::transcription::connection::close_write(p, tout.after.client.connection) })
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
/// writes no ClientHello2, only its alert (or, where the crate's caps fired,
/// it goes on). `bootstrap::record_agrees` holds of the record, and relates
/// the two.
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
    &&& super::bootstrap::record_agrees(p, s, ts.client, b)
}

/// **Stated difference, the client's flight in one record**
/// (`dispatcher::coalesced`; §5.1: handshake messages "MAY be coalesced
/// into a single TLSPlaintext record"): on the server Finished both send
/// the client's flight, D.4's dummy record first when owed; the crate seals
/// its messages in one record, the transcription each in its own
/// (`dispatcher::protect_each`). The same bytes when no CertificateRequest
/// came (one message: then [`goes_on`] holds). Both go on in agreeing
/// states.
pub open spec fn goes_on_coalesced(m: Models, p: Primitives, scalar: Seq<u8>, ts: TState, cout: Step, cs2: CState,
    tout: TOut) -> bool
{
    let hs2 = tout.after.client.connection.handshake;
    let chts = hs2.client_handshake_traffic_secret;
    let msgs = super::dispatcher::client_flight(hs2);
    let mode = ts.client.compatibility_mode;
    let sent = ts.client.change_cipher_spec_sent;
    &&& cout.send == flat(crate::transcription::middlebox::before_second_flight(mode, sent,
        seq![super::dispatcher::coalesced(p, chts, msgs)]).0)
    &&& tout.send == flat(crate::transcription::middlebox::before_second_flight(mode, sent,
        super::dispatcher::protect_each(p, crate::transcription::record::traffic_state(p, chts), msgs)).0)
    &&& cout.deliver == tout.deliver
    &&& tout.end is Running
    &&& driver_agrees(m, p, scalar, cs2, tout.after)
}

/// **Stated difference, an exhausted receive epoch**
/// (`post_handshake::exhausted`): after a record under sequence number
/// 2^64 - 1 the crate refuses the next with `internal_error` before any of
/// its bytes; the transcription waits for its header, and refuses it then
/// (or refuses its length). Unreachable in practice.
pub open spec fn exhausted_epoch(cs: CState, cout: Step, tout: TOut) -> bool {
    &&& crate_fails(cout)
    &&& cout.status->Failed_0 == crate::spec::INTERNAL_ERROR
    &&& cs.stage matches Stage::App(s)
    &&& super::post_handshake::exhausted(s)
    &&& ((tout.end is Running && tout.send.len() == 0) || tout.end is Aborted)
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
    ||| goes_on_coalesced(m, p, scalar, ts, cout, cs2, tout)
    ||| exhausted_epoch(cs, cout, tout)
}

/// **Stated difference, application data above 2^14 octets**
/// (`post_handshake::lemma_oversized`; §5.1): the crate's
/// `send_application` takes one record's worth and refuses more as a local
/// `record_overflow` (after the KeyUpdate that is owed or due on the last
/// sequence number, if any), ending the connection; the transcription's
/// `send_application_data` fragments it.
pub open spec fn oversized(cs: CState, data: Seq<u8>, cout: Step, tout: TOut) -> bool {
    &&& data.len() > crate::spec::MAX_PLAINTEXT
    &&& cs.stage is App
    &&& cout.stage is Ended
    &&& cout.status matches Status::Failed(a, _) && a == crate::spec::RECORD_OVERFLOW
    &&& tout.end is Running
}

/// **Stated difference, a close before the handshake completes** (§6.1):
/// both write the same close_notify (in plaintext before the ServerHello,
/// under the client handshake key in the server's flight, A.1's note), and
/// the crate ends the connection; the transcription, which has no
/// write-closed state, has only written the record (its caller writes
/// nothing more).
pub open spec fn closes_in_handshake(cout: Step, tout: TOut) -> bool {
    &&& cout.stage is Ended
    &&& cout.status == Status::Closed
    &&& cout.send == tout.send
    &&& cout.deliver.len() == 0
    &&& tout.deliver.len() == 0
    &&& tout.end is Running
    &&& tout.after.write_closed
}

/// The outcomes of one operation compare.
pub open spec fn op_agrees(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, op: Op) -> bool {
    let (cout, cs2) = cop(m, scalar, cs, op);
    let tout = top(p, ts, op);
    match op {
        Op::Feed(chunk) => feed_verdict(m, p, scalar, cs, ts, chunk, cout, cs2, tout),
        Op::Send(data) => goes_on(m, p, scalar, cout, cs2, tout) || oversized(cs, data, cout, tout),
        Op::Close => goes_on(m, p, scalar, cout, cs2, tout) || closes_in_handshake(cout, tout),
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
                && super::framing::first(x, false).0 is Pending
                && crate::connection::framing_spec::wf_mode(x, false)
                && crate::spec::read_record(x, false) is NeedMore)
            ||| (out.status matches Status::Failed(a, _) && super::framing::early_reject(x, false, a)
                && super::framing::first(x, false).0 == crate::connection::framing_spec::Status::Fail(a)
                && out == crate::connection::driver_spec::hello_failure(a))
        }
    }),
{
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(crate::hello::bootstrap_spec::feed);
    hide(crate::connection::driver_contract::established_step);
    hide(crate::hello::bootstrap_spec::acknowledge);
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
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e),
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


// ---------------------------------------------------------------------------
// The handoff at the ServerHello.
// ---------------------------------------------------------------------------

/// Every ClientHello the crate sends, the first or the retry's (any
/// cookie), offers the crate's nine signature schemes: the transcription's
/// `offered_signature_schemes` of it is `auth::offered_schemes`. One of the
/// two start inputs `dispatcher::accepts_server_hello` left to the driver.
pub proof fn lemma_offered_schemes(c: crate::hello::client_spec::Config, cookie: Seq<u8>)
    ensures
        crate::transcription::key_exchange::offered_signature_schemes(
            super::client::ch_view(crate::hello::client_spec::client_hello(c, cookie))) == super::auth::offered_schemes(),
{
    let ch = crate::hello::client_spec::client_hello(c, cookie);
    let v = super::client::ch_view(ch).extensions;
    super::client::lemma_fixed_bodies();
    super::client::lemma_extensions_view(c, cookie);
    let vs = super::messages::exts_view(super::client::sni_extensions(c));
    let ksd = crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]);
    let fixed = seq![
        crate::transcription::extensions::Extension { extension_type: 43, extension_data: seq![2u8, 3u8, 4u8] },
        crate::transcription::extensions::Extension { extension_type: 13,
            extension_data: crate::spec::write_signature_schemes(crate::hello::client_spec::signatures()) },
        crate::transcription::extensions::Extension { extension_type: 10, extension_data: seq![0u8, 2u8, 0u8, 29u8] },
        crate::transcription::extensions::Extension { extension_type: 51, extension_data: ksd },
    ];
    let tail = if cookie.len() == 0 { Seq::<crate::transcription::extensions::Extension>::empty() }
        else { seq![crate::transcription::extensions::Extension { extension_type: 44, extension_data: cookie }] };
    assert(v =~= vs + (fixed + tail));
    super::client::lemma_fixed_find(fixed, tail, ksd);
    super::client::lemma_sni_find(c, 13);
    super::client::lemma_find_append(vs, fixed + tail, 13);
    assert(super::extensions::nats(crate::hello::client_spec::signatures())
        =~= seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]);
    assert(crate::transcription::extensions::read_signature_scheme_list(
        crate::transcription::extensions::write_signature_scheme_list(
            seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]))
        == Some(seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]))
        by (compute_only);
}

/// A.1's actions never change the handshake state, the read side or the
/// bytes of an unfinished message.
pub proof fn lemma_apply_keeps(p: Primitives, c: Connection, actions: Seq<crate::transcription::state_machine::Action>)
    ensures ({
        let after = crate::transcription::connection::apply_actions(p, c, actions).0;
        &&& after.handshake == c.handshake
        &&& after.read_closed == c.read_closed
        &&& after.handshake_fragments == c.handshake_fragments
    }),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let tail = actions.subrange(1, actions.len() as int);
        match actions[0] {
            crate::transcription::state_machine::Action::SendHandshake(message, version) => {
                let (records, send) = crate::transcription::connection::send_blocks(p, c.send,
                    crate::transcription::record::ct_handshake(), version,
                    crate::transcription::record::fragment_blocks(message));
                lemma_apply_keeps(p, Connection { send, ..c }, tail);
            },
            crate::transcription::state_machine::Action::SetReceiveSecret(secret) =>
                lemma_apply_keeps(p, Connection { receive: Protection::Protected(
                    crate::transcription::record::traffic_state(p, secret)), ..c }, tail),
            crate::transcription::state_machine::Action::SetSendSecret(secret) =>
                lemma_apply_keeps(p, Connection { send: Protection::Protected(
                    crate::transcription::record::traffic_state(p, secret)), ..c }, tail),
            crate::transcription::state_machine::Action::UpdateReceiveSecret =>
                lemma_apply_keeps(p, Connection { receive: crate::transcription::connection::updated_traffic(p, c.receive),
                    ..c }, tail),
            crate::transcription::state_machine::Action::RespondToKeyUpdate =>
                lemma_apply_keeps(p, Connection { key_update_owed: true, ..c }, tail),
        }
    }
}

/// A step in WAIT_SH that goes on (a HelloRetryRequest accepted) keeps
/// [`wait_sh_fields`]: `accept_hello_retry_request` keeps every field but
/// the hello, the retry record, the transcript and the private key, which
/// is one of the two the state holds.
pub proof fn lemma_wait_sh_step(p: Primitives, hs: crate::transcription::state_machine::ClientHandshake, raw: Seq<u8>,
    scalar: Seq<u8>)
    requires
        hs.state == crate::transcription::state_machine::ClientState::WaitSh,
        wait_sh_fields(hs, scalar),
        crate::transcription::state_machine::receive_handshake_message(p, hs, raw) is Proceed,
        !crate::transcription::state_machine::receive_handshake_message(p, hs, raw)->receive_key_changes,
    ensures
        wait_sh_fields(crate::transcription::state_machine::receive_handshake_message(p, hs, raw)->handshake, scalar),
        crate::transcription::state_machine::receive_handshake_message(p, hs, raw)->handshake.state
            == crate::transcription::state_machine::ClientState::WaitSh,
{
}

/// After a HelloRetryRequest (the controller's transcript is in its
/// second-ServerHello phase, so `retried`), the crate never retries again:
/// `validate` refuses a second HelloRetryRequest (§4.1.4).
pub proof fn lemma_no_second_retry(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: crate::hello::bootstrap_spec::State, bf: Seq<u8>)
    requires
        s.hello is Some,
        s.hello->Some_0.transcript.retried,
    ensures !(super::bootstrap::buffer_step(hash, s, bf).1 is Send),
{
    match crate::spec::extract_messages(bf) {
        crate::spec::Res::Ok((ms, rest)) => {
            let s1 = crate::hello::bootstrap_spec::State { reassembly: crate::spec::Reasm { buf: rest }, ..s };
            if ms.len() > 0 && ms[0].len() >= crate::spec::HANDSHAKE_HEADER && ms[0][0] == crate::spec::HS_SERVER_HELLO {
                crate::hello::bootstrap_lemmas::lemma_receive_messages(hash, s1, ms);
                let body = ms[0].skip(crate::spec::HANDSHAKE_HEADER as int);
                let hello = s.hello->Some_0;
                assert(!(crate::hello::spec::retry(crate::spec::read_server_hello(body)->Some_0, true) is Ok));
                if let Ok(crate::hello::client_spec::Outcome::Retry(_, _))
                    = crate::hello::client_spec::receive(hash, hello, body) {
                    assert(crate::hello::spec::validate(hello.config.session_id, true, body) is Ok);
                    assert(false);
                }
            }
        },
        _ => {},
    }
}

/// What `bootstrap::buffer_agrees` says of handshake bytes the crate
/// establishes on (its `Established` case), with the crate's `receive`
/// unfolded: `validate` chose the share, and the transcript took the
/// ServerHello.
pub proof fn lemma_est_facts(p: Primitives, s: crate::hello::bootstrap_spec::State, cl: ClientConnection, bf: Seq<u8>)
    requires
        super::bootstrap::agrees_but_buffer(p, s, cl),
        super::bootstrap::buffer_step(p.hash, s, bf).1 is Established,
        super::bootstrap::buffer_agrees(p, s, cl, bf),
    ensures ({
        let hello = s.hello->Some_0;
        let a = super::bootstrap::buffer_step(p.hash, s, bf).1;
        let body = super::bootstrap::first_body(bf);
        let c = cl.connection;
        &&& bf == crate::transcription::key_exchange::write_handshake(2, body)
        &&& crate::transcription::connection::process_handshake_bytes(p, c, bf) == super::bootstrap::after_message(p, c, bf)
        &&& a->Established_0 == hello.config
        &&& crate::hello::spec::validate(hello.config.session_id, hello.transcript.retried, body)
            == Ok::<crate::hello::spec::Selection, u8>(crate::hello::spec::Selection::Share(a->Established_2))
        &&& crate::transcript::spec::step(p.hash, hello.transcript, crate::transcript::spec::Kind::ServerHello, body)
            == Ok::<crate::transcript::spec::State, crate::transcript::spec::Error>(a->Established_1)
        &&& super::negotiation::receive_agrees(p, hello, c.handshake, body)
        &&& crate::hello::client_spec::wf(hello)
        &&& super::negotiation::negotiation_agrees(p, hello, c.handshake)
    }),
{
}

/// The transcription's step on the ServerHello the crate establishes on,
/// and what the dispatcher's start needs of it (the share, the transcript,
/// the ClientHello's offers: item 1's signature schemes).
pub proof fn lemma_est_step(p: Primitives, s: crate::hello::bootstrap_spec::State, cl: ClientConnection, bf: Seq<u8>)
    requires
        super::bootstrap::agrees_but_buffer(p, s, cl),
        super::bootstrap::buffer_step(p.hash, s, bf).1 is Established,
        super::bootstrap::buffer_agrees(p, s, cl, bf),
    ensures ({
        let hello = s.hello->Some_0;
        let retried = hello.transcript.retried;
        let a = super::bootstrap::buffer_step(p.hash, s, bf).1;
        let (config, transcript, key) = (a->Established_0, a->Established_1, a->Established_2);
        let body = super::bootstrap::first_body(bf);
        let hs = cl.connection.handshake;
        let h = crate::transcription::key_exchange::read_server_hello(body)->Some_0;
        &&& crate::transcription::key_exchange::read_server_hello(body) is Some
        &&& crate::transcription::extensions::find_extension(h.extensions, 51) is Some
        &&& crate::transcription::extensions::read_key_share_server_hello(
            crate::transcription::extensions::find_extension(h.extensions, 51)->0)
            == Some(crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: key })
        &&& crate::transcription::state_machine::receive_handshake_message(p, hs, bf)
            == crate::transcription::state_machine::accept_server_hello(p, hs, h, bf)
        &&& super::transcript::represents(p, transcript, hs.transcript.push(bf), retried)
        &&& (hs.retry is Some) == retried
        &&& transcript.retried == retried
        &&& config == hello.config
        &&& crate::hello::client_spec::config_ok(config)
        &&& (p.x25519)(hs.x25519_private_key, crate::transcription::primitives::x25519_basepoint()) == config.public_key
        &&& crate::transcription::key_exchange::offered_signature_schemes(hs.hello) == super::auth::offered_schemes()
        &&& super::extensions::nats(crate::hello::join_spec::extension_types(config, transcript.retried))
            == crate::transcription::extensions::extension_types(hs.hello.extensions)
        &&& crate::transcript::spec::wf(transcript)
        &&& transcript.phase == crate::transcript::spec::Phase::Handshake
        &&& hs.state == crate::transcription::state_machine::ClientState::WaitSh
    }),
{
    hide(super::bootstrap::buffer_agrees);
    hide(super::bootstrap::buffer_step);
    lemma_est_facts(p, s, cl, bf);
    let c = cl.connection;
    let hs = c.handshake;
    let hello = s.hello->Some_0;
    let config0 = hello.config;
    let retried = hello.transcript.retried;
    let a = super::bootstrap::buffer_step(p.hash, s, bf).1;
    let (config, transcript, key) = (a->Established_0, a->Established_1, a->Established_2);
    let body = super::bootstrap::first_body(bf);
    assert(body.len() <= crate::transcript::spec::MAX_BODY);
    let cookie0: Seq<u8> = if retried {
        choose|cookie: Seq<u8>| cookie.len() > 0
            && hs.hello == super::client::ch_view(#[trigger] crate::hello::client_spec::client_hello(config0, cookie))
    } else {
        Seq::empty()
    };
    assert(hs.hello == super::client::ch_view(crate::hello::client_spec::client_hello(config0, cookie0)));
    let offers = crate::hello::join_spec::extension_types(config0, cookie0.len() != 0);
    super::client::lemma_sent_is_profile(config0, cookie0);
    super::hello::lemma_validate(hs.hello, hs.retry, offers, config0.session_id, retried, body);
    lemma_offered_schemes(config0, cookie0);
    crate::transcript::lemmas::lemma_step_wf(p.hash, hello.transcript, crate::transcript::spec::Kind::ServerHello, body);
}

/// **The handoff at the ServerHello** (and item 2 of the driver's remaining
/// conditions): from a bootstrap state that agrees with the
/// transcription's client (but for the buffer), on handshake bytes whose
/// one message the crate establishes on, the crate's handoff
/// (`driver_contract::established_step`) and the transcription's step on
/// the same message (`bootstrap::after_message`) agree:
/// - the X25519 shared secret is all zero (§7.4.2): the transcription
///   aborts in `accept_server_hello`, the crate in `join_spec::derive`, both
///   with `illegal_parameter`, and the crate's plaintext alert is the
///   transcription's `abort_record`;
/// - otherwise both go on, writing and delivering nothing, and the
///   dispatcher's start agrees with the transcription's client after the
///   ServerHello (`dispatcher::lemma_start`, whose start inputs, the
///   ClientHello's signature schemes and the unset WAIT_EE fields, hold
///   here: [`lemma_est_step`], [`wait_sh_fields`]).
#[verifier::rlimit(100)]
pub proof fn lemma_handoff(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    cl: ClientConnection, bf: Seq<u8>)
    requires
        hypotheses(m, p),
        super::bootstrap::agrees_but_buffer(p, s, cl),
        wait_sh_fields(cl.connection.handshake, scalar),
        super::bootstrap::buffer_step(m.crypto.hash, s, bf).1 is Established,
        super::bootstrap::buffer_agrees(p, s, cl, bf),
    ensures ({
        let a = super::bootstrap::buffer_step(m.crypto.hash, s, bf).1;
        let out = crate::connection::driver_contract::established_step(m, a, scalar);
        let c = cl.connection;
        &&& crate::transcription::connection::process_handshake_bytes(p, c, bf)
            == super::bootstrap::after_message(p, c, bf)
        &&& match super::bootstrap::after_message(p, c, bf) {
            Receive::Abort(e) => {
                &&& e == ClientError::SharedSecretAllZero
                &&& crate::transcription::alerts::required_alert(e) == 47
                &&& out == crate::connection::driver_spec::hello_failure(47)
                &&& crate::transcription::connection::abort_record(p, c, e)
                    == crate::connection::driver_spec::hello_failure(47).send
            },
            Receive::Continue(pr) => {
                &&& pr.application_data.len() == 0
                &&& pr.records_to_send.len() == 0
                &&& out.send.len() == 0
                &&& out.deliver.len() == 0
                &&& out.status == Status::Handshaking
                &&& out.stage matches Stage::Flight(ds)
                &&& ds.framing == Seq::<u8>::empty()
                &&& ds.mode == crate::connection::dispatcher_spec::Mode::Handshake
                &&& super::dispatcher::dispatcher_agrees(p, m.verification, ds,
                    ClientConnection { connection: pr.connection, ..cl })
            },
            Receive::PeerError(_) => false,
        }
    }),
{
    hide(super::bootstrap::buffer_agrees);
    hide(super::bootstrap::buffer_step);
    hide(super::negotiation::receive_agrees);
    hide(super::negotiation::negotiation_agrees);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(super::dispatcher::dispatcher_agrees);
    hide(super::transcript::represents);
    hide(crate::transcription::key_exchange::read_server_hello);
    let c = cl.connection;
    let hs = c.handshake;
    assert(m.crypto.hash == p.hash);
    lemma_est_facts(p, s, cl, bf);
    lemma_est_step(p, s, cl, bf);
    let a = super::bootstrap::buffer_step(p.hash, s, bf).1;
    let (config, transcript, key) = (a->Established_0, a->Established_1, a->Established_2);
    assert(a == crate::hello::bootstrap_spec::Action::Established(config, transcript, key));
    let body = super::bootstrap::first_body(bf);
    let raw = bf;
    let retried = s.hello->Some_0.transcript.retried;
    let h = crate::transcription::key_exchange::read_server_hello(body)->Some_0;
    let msgs = hs.transcript.push(raw);
    assert((m.exchange.public_key)(scalar) == config.public_key);
    super::keys::theorem_handshake_keys_equivalence(m.crypto, m.exchange, p);
    let shared = (p.x25519)(scalar, key);
    let derived = crate::hello::join_spec::derive(m.crypto, m.exchange, config, transcript, key, scalar);
    assert(super::transcript::represents(p, transcript, msgs, retried));
    let step = crate::transcription::state_machine::accept_server_hello(p, hs, h, raw);
    assert(super::bootstrap::after_message(p, c, bf) == match step {
        crate::transcription::state_machine::HandshakeStep::Abort(e) => Receive::Abort(e),
        crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, .. } => {
            let (after, sent) = crate::transcription::connection::apply_actions(p, Connection { handshake, ..c }, actions);
            Receive::Continue(crate::transcription::connection::Progress {
                connection: Connection { handshake_fragments: seq![], ..after },
                application_data: seq![], records_to_send: sent })
        },
    });
    match derived {
        Err(alert) => {
            // Item 2: both refuse the all-zero shared secret, with illegal_parameter.
            assert(crate::transcription::presentation::all_zero(shared));
            assert(step == crate::transcription::state_machine::HandshakeStep::Abort(ClientError::SharedSecretAllZero));
            assert(alert == 47);
            lemma_alert_record_plain(p, c, 47);
        },
        Ok((auth_config, master)) => {
            assert(!crate::transcription::presentation::all_zero(shared));
            assert(step is Proceed);
            // `handshake_spec::start` goes through: 32-octet secrets and a well-formed transcript.
            assert(auth_config.client_secret.len() == 32);
            assert(auth_config.server_secret.len() == 32);
            super::client::lemma_offers(config, transcript.retried);
            assert(crate::hello::client_spec::signatures().len() == 9);
            assert(crate::auth::spec::config_ok(auth_config));
            assert(crate::traffic::handshake_spec::start(m.crypto, m.exchange, config, transcript, key, scalar) is Ok);
            // The transcription's step, and its actions.
            let hs1 = step->handshake;
            let a1 = step->actions;
            let shts = hs1.server_handshake_traffic_secret;
            assert(a1 == seq![crate::transcription::state_machine::Action::SetReceiveSecret(shts)]);
            let y1 = Connection { handshake: hs1, ..c };
            let y2 = Connection { receive: Protection::Protected(crate::transcription::record::traffic_state(p, shts)), ..y1 };
            assert(a1.subrange(1, 1) =~= Seq::<crate::transcription::state_machine::Action>::empty());
            assert(crate::transcription::connection::apply_actions(p, y2, Seq::empty()) == (y2, Seq::<Seq<u8>>::empty()));
            assert(crate::transcription::connection::apply_actions(p, y1, a1) == (y2, Seq::<Seq<u8>>::empty()));
            let pr = super::bootstrap::after_message(p, c, bf)->Continue_0;
            let cl1 = ClientConnection { connection: pr.connection, ..cl };
            // D.4: the dummy record is owed exactly when the transcription has not written it.
            assert(crate::traffic::handshake_spec::needs_ccs(config, transcript)
                == (cl1.compatibility_mode && !cl1.change_cipher_spec_sent));
            assert(validators(m.verification, p, config.host, config.now));
            assert(super::dispatcher::accepts_server_hello(p, c, h, raw, config, transcript, key, scalar));
            super::dispatcher::lemma_start(m.crypto, m.exchange, m.verification, ciphers(m), p, cl1, c, h, raw, config,
                transcript, key, scalar);
        },
    }
}


/// A record on which the bootstrap establishes or retries is handshake
/// bytes the crate reads as messages: the record-level theorem's
/// `buffer_agrees` holds of them.
#[verifier::rlimit(30)]
pub proof fn lemma_hs_path(p: Primitives, s: crate::hello::bootstrap_spec::State, cl: ClientConnection, b: Seq<u8>)
    requires
        super::bootstrap::record_agrees(p, s, cl, b),
        crate::hello::bootstrap_lemmas::record_step(p.hash, s, b).1 is Established
            || crate::hello::bootstrap_lemmas::record_step(p.hash, s, b).1 is Send,
    ensures ({
        let bf = super::bootstrap::buffer(s, b);
        &&& crate::hello::bootstrap_lemmas::record_step(p.hash, s, b) == super::bootstrap::buffer_step(p.hash, s, bf)
        &&& super::bootstrap::one_record(p, cl.connection, b)
            == crate::transcription::connection::process_handshake_bytes(p, cl.connection, bf)
        &&& super::bootstrap::buffer_agrees(p, s, cl, bf)
    }),
{
    hide(super::bootstrap::buffer_agrees);
    hide(super::bootstrap::buffer_step);
    hide(crate::transcription::connection::process_handshake_bytes);
    hide(crate::transcription::middlebox::client_receive_stream);
}

/// The ServerHello in its own record: the handoff ([`lemma_handoff`]).
#[verifier::rlimit(60)]
pub proof fn lemma_hello_established(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
        crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(ts.buffer + chunk)).1 is Established,
    ensures hello_whole(m, p, scalar, s, framing, held, ts, chunk, cs2),
{
    hide(super::bootstrap::buffer_agrees);
    hide(super::bootstrap::buffer_step);
    hide(super::bootstrap::record_agrees);
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(super::dispatcher::dispatcher_agrees);
    hide(goes_on_coalesced);
    hide(exhausted_epoch);
    hide(rejects_record);
    hide(rejects_early);
    hide(peer_closed);
    hide(retry_then_fails);
    let w = ts.buffer + chunk;
    let b = front(w);
    let c = ts.client.connection;
    let n = 5 + super::bootstrap::length(w);
    lemma_hello_facts(p, scalar, s, framing, held, ts, chunk);
    assert(m.crypto.hash == p.hash);
    lemma_hs_path(p, s, ts.client, b);
    let bf = super::bootstrap::buffer(s, b);
    lemma_handoff(m, p, scalar, s, ts.client, bf);
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
    let cout = hello_act(m, scalar, s2, seq![], a);
    assert(cout == crate::connection::driver_contract::established_step(m, a, scalar));
    let t = super::bootstrap::after_message(p, c, bf);
    match t {
        Receive::Continue(pr) => {
            assert(cout.send =~= Seq::<u8>::empty());
            assert(cout.deliver =~= Seq::<u8>::empty());
            assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
            assert(pr.application_data =~= Seq::<u8>::empty());
            assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
            let ds = cout.stage->Flight_0;
            assert(crate::connection::dispatcher_spec::State { framing: seq![], ..ds } == ds);
            super::framing::lemma_empty(true);
            assert(Seq::<u8>::empty() + w.skip(n as int) =~= w.skip(n as int));
        },
        _ => {},
    }
}

/// A HelloRetryRequest: ClientHello2 goes out (with D.4's dummy record)
/// and is acknowledged at once; what followed the HelloRetryRequest in its
/// record is then read, as the transcription reads it in the same step.
#[verifier::rlimit(60)]
pub proof fn lemma_hello_send(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        hello_agrees(p, scalar, s, framing, held, ts),
        whole(ts.buffer + chunk),
        crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(ts.buffer + chunk)).1 is Send,
    ensures hello_whole(m, p, scalar, s, framing, held, ts, chunk, cs2),
{
    hide(super::bootstrap::buffer_step);
    hide(super::bootstrap::record_agrees);
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(super::dispatcher::dispatcher_agrees);
    hide(super::bootstrap::bootstrap_agrees);
    hide(rejects_record);
    hide(rejects_early);
    hide(peer_closed);
    hide(ends_alike);
    hide(crate::transcription::state_machine::receive_handshake_message);
    let w = ts.buffer + chunk;
    let b = front(w);
    let cl = ts.client;
    let c = cl.connection;
    let n0 = 5 + super::bootstrap::length(w);
    lemma_hello_facts(p, scalar, s, framing, held, ts, chunk);
    assert(m.crypto.hash == p.hash);
    lemma_hs_path(p, s, cl, b);
    let bf = super::bootstrap::buffer(s, b);
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
    let wire = a->Send_0;
    // `buffer_agrees`' Send case.
    let n = super::bootstrap::first_length(bf);
    let raw = bf.subrange(0, n as int);
    let rest = bf.skip(n as int);
    let step = crate::transcription::state_machine::receive_handshake_message(p, c.handshake, raw);
    let (c3, sent) = crate::transcription::connection::apply_actions(p, Connection { handshake: step->handshake, ..c },
        step->actions);
    let (records, ccs_sent) = crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
        cl.change_cipher_spec_sent, sent);
    let s1 = crate::hello::bootstrap_spec::State { mode: crate::hello::bootstrap_spec::Mode::AwaitServerHello,
        pending_flight: seq![], retained: seq![], ..s2 };
    let cl2 = ClientConnection { connection: c3, change_cipher_spec_sent: ccs_sent, ..cl };
    let t2 = crate::transcription::connection::process_handshake_bytes(p, c3, rest);
    assert({
        &&& 4 <= n && n <= bf.len()
        &&& step is Proceed
        &&& !step->receive_key_changes
        &&& wire == super::ccs::flatten(records)
        &&& crate::transcription::connection::process_handshake_bytes(p, c, bf)
            == super::bootstrap::after_records(sent, t2)
        &&& s2.mode == crate::hello::bootstrap_spec::Mode::AwaitClientHello2Send
        &&& crate::hello::bootstrap_spec::wf(s2)
        &&& crate::hello::bootstrap_spec::acknowledge(p.hash, s2, wire) == super::bootstrap::buffer_step(p.hash, s1, rest)
        &&& super::bootstrap::agrees_but_buffer(p, s1, cl2)
        &&& super::bootstrap::buffer_agrees(p, s1, cl2, rest)
    });
    // ClientHello2's step keeps WAIT_SH's fields, and leaves the controller retried.
    lemma_apply_keeps(p, Connection { handshake: step->handshake, ..c }, step->actions);
    lemma_wait_sh_step(p, c.handshake, raw, scalar);
    assert(wait_sh_fields(c3.handshake, scalar));
    assert(s1.hello->Some_0.transcript.retried);
    lemma_no_second_retry(p.hash, s1, rest);
    let (acked, after) = super::bootstrap::buffer_step(p.hash, s1, rest);
    let cout = hello_act(m, scalar, s2, seq![], a);
    let u = crate::transcription::middlebox::client_receive_stream(p, cl, b).0;
    assert(u == super::dispatcher::lifted(cl, super::bootstrap::after_records(sent, t2)));
    assert(sent + Seq::<Seq<u8>>::empty() =~= sent);
    match after {
        crate::hello::bootstrap_spec::Action::None => {
            let c2 = Connection { handshake_fragments: acked.reassembly.buf, ..c3 };
            assert(t2 == Receive::Continue(crate::transcription::connection::Progress { connection: c2,
                application_data: seq![], records_to_send: seq![] }));
            assert(super::bootstrap::bootstrap_agrees(p, acked, ClientConnection { connection: c2, ..cl2 }));
            assert(cout.deliver =~= Seq::<u8>::empty());
            super::framing::lemma_empty(false);
            assert(Seq::<u8>::empty() + w.skip(n0 as int) =~= w.skip(n0 as int));
        },
        crate::hello::bootstrap_spec::Action::Fail(alert) => {
            assert(retry_then_fails(m, p, CState { stage: Stage::Hello(s, framing), status: Status::Handshaking, held },
                ts, chunk, cout, tfeed(p, ts, chunk)));
        },
        crate::hello::bootstrap_spec::Action::Established(_, _, _) => {
            lemma_handoff(m, p, scalar, s1, cl2, rest);
            let est = crate::connection::driver_contract::established_step(m, after, scalar);
            match super::bootstrap::after_message(p, c3, rest) {
                Receive::Continue(pr) => {
                    assert(cout.send =~= wire);
                    assert(cout.deliver =~= Seq::<u8>::empty());
                    assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
                    assert(pr.application_data =~= Seq::<u8>::empty());
                    let ds = cout.stage->Flight_0;
                    assert(crate::connection::dispatcher_spec::State { framing: seq![], ..ds } == ds);
                    super::framing::lemma_empty(true);
                    assert(Seq::<u8>::empty() + w.skip(n0 as int) =~= w.skip(n0 as int));
                },
                _ => {
                    assert(retry_then_fails(m, p, CState { stage: Stage::Hello(s, framing), status: Status::Handshaking,
                        held }, ts, chunk, cout, tfeed(p, ts, chunk)));
                },
            }
        },
        _ => {},
    }
}

/// **The Hello stage, one operation**: feeding a chunk agrees
/// ([`op_agrees`]).
pub proof fn lemma_hello_feed(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is Hello,
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(hello_whole);
    hide(hello_act);
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(super::bootstrap::bootstrap_agrees);
    let (s, framing) = match cs.stage { Stage::Hello(s, f) => (s, f), _ => arbitrary() };
    let input = cs.held + chunk;
    let x = framing + input;
    assert(x =~= ts.buffer + chunk);
    let c = ts.client.connection;
    assert(c.receive == Protection::Unprotected && s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello) by {
        reveal(super::bootstrap::bootstrap_agrees);
    }
    lemma_hello_crate(m, s, framing, scalar, input, c);
    let (k, cout) = hello_out(m, s, framing, scalar, input);
    let cs2 = CState { stage: cout.stage, status: cout.status, held: input.skip(k as int) };
    assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
    if whole(x) {
        let (s2, a) = crate::hello::bootstrap_lemmas::record_step(m.crypto.hash, s, front(x));
        match a {
            crate::hello::bootstrap_spec::Action::None =>
                lemma_hello_none(m, p, scalar, s, framing, cs.held, ts, chunk, cs2),
            crate::hello::bootstrap_spec::Action::Send(_) =>
                lemma_hello_send(m, p, scalar, s, framing, cs.held, ts, chunk, cs2),
            crate::hello::bootstrap_spec::Action::Established(_, _, _) =>
                lemma_hello_established(m, p, scalar, s, framing, cs.held, ts, chunk, cs2),
            crate::hello::bootstrap_spec::Action::Alert(_) =>
                lemma_hello_alert(m, p, scalar, s, framing, cs.held, ts, chunk, cs2),
            crate::hello::bootstrap_spec::Action::Fail(_) =>
                lemma_hello_fail(m, p, scalar, s, framing, cs.held, ts, chunk, cs2),
            crate::hello::bootstrap_spec::Action::Close =>
                lemma_hello_close(m, p, scalar, s, framing, cs.held, ts, chunk, cs2),
        }
        reveal(hello_whole);
    } else {
        reveal(super::bootstrap::bootstrap_agrees);
        lemma_tfeed_partial(p, ts, chunk);
        super::framing::lemma_framing_agrees(c, x, false);
        let (st, _) = super::framing::first(x, false);
        if st is Pending {
            reveal(hello_act);
            assert(input.skip(k as int) =~= Seq::<u8>::empty());
            assert(x + Seq::<u8>::empty() =~= x);
        }
    }
}

// ---------------------------------------------------------------------------
// The flight stage.
// ---------------------------------------------------------------------------

/// What the flight stage's step on a whole record comes to, given the
/// caller's state after it (`cs2`).
pub open spec fn flight_whole(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::connection::dispatcher_spec::State,
    held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState) -> bool
{
    let w = ts.buffer + chunk;
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0, front(w));
    let cout = crate::connection::driver_spec::flight_out(m.crypto, m.verification, ciphers(m), a, s2);
    let cs = CState { stage: Stage::Flight(s), status: Status::Handshaking, held };
    (cs2.stage == cout.stage && cs2.status == cout.status
        && (!(a is Fail) ==> cs2.held == w.skip((5 + super::bootstrap::length(w)) as int)))
        ==> feed_verdict(m, p, scalar, cs, ts, chunk, cout, cs2, tfeed(p, ts, chunk))
}

/// The record-level facts of a whole record in the flight.
pub proof fn lemma_flight_facts(m: Models, p: Primitives, s: crate::connection::dispatcher_spec::State, held: Seq<u8>,
    ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
    ensures ({
        let w = ts.buffer + chunk;
        let b = front(w);
        let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
        let y = ts.client.connection;
        &&& super::bootstrap::whole_record(b)
        &&& super::dispatcher::record_agrees(m.crypto, m.verification, ciphers(m), p, s0, ts.client, b)
        &&& super::dispatcher::in_flight(y.handshake.state)
        &&& !y.read_closed
        &&& !ts.write_closed
        &&& tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 {
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
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
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    super::framing::lemma_disp_agrees_facts(p, m.verification, s0, ts.client);
    lemma_tfeed_whole(p, ts, chunk);
    super::dispatcher::lemma_receive(m.crypto, m.verification, ciphers(m), p, s0, ts.client, b);
    assert(super::dispatcher::in_flight(ts.client.connection.handshake.state)) by {
        reveal(super::dispatcher::dispatcher_agrees);
    }
}

/// The outcome facts of a whole record in the flight: the
/// dispatcher theorem's `outcome_agrees`, and the transcription's result
/// as its caller sees it.
pub open spec fn flight_case(m: Models, p: Primitives, s: crate::connection::dispatcher_spec::State, ts: TState,
    chunk: Seq<u8>) -> bool
{
    let w = ts.buffer + chunk;
    let b = front(w);
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0, b);
    let t = super::bootstrap::one_record(p, ts.client.connection, b);
    &&& crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 == super::dispatcher::lifted(ts.client, t)
    &&& super::dispatcher::outcome_agrees(m.crypto, m.verification, ciphers(m), p, s0, ts.client, a, s2, t, true)
}

/// [`flight_case`], from the dispatcher theorem's `record_agrees`.
pub proof fn lemma_flight_case(m: Models, p: Primitives, s: crate::connection::dispatcher_spec::State, held: Seq<u8>,
    ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
    ensures flight_case(m, p, s, ts, chunk),
{
    lemma_flight_facts(m, p, s, held, ts, chunk);
}

/// The flight's step on a whole record that goes on quietly (nothing to
/// do, a dropped change_cipher_spec, a user_canceled): both go on.
pub proof fn lemma_flight_quiet(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::connection::dispatcher_spec::State,
    held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
        flight_case(m, p, s, ts, chunk),
        tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, front(ts.buffer + chunk)).0 {
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
            ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
            ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                send: flat(records_to_send), deliver: application_data,
                after: TState { client, buffer: (ts.buffer + chunk).skip((5 + super::bootstrap::length(ts.buffer + chunk)) as int), ..ts },
                end: TEnd::Running },
        },
        ({
            let a = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m),
                crate::connection::dispatcher_spec::State { framing: seq![], ..s }, front(ts.buffer + chunk)).0;
            a is None || a is Ignored || a is Cancelled
        }),
    ensures flight_whole(m, p, scalar, s, held, ts, chunk, cs2),
{
    hide(super::dispatcher::dispatcher_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(super::bootstrap::one_record);
    hide(rejects_record);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(exhausted_epoch);
    hide(goes_on_coalesced);
    hide(peer_closed);
    hide(ends_alike);
    let w = ts.buffer + chunk;
    let n = 5 + super::bootstrap::length(w);
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0, front(w));
    let t = super::bootstrap::one_record(p, ts.client.connection, front(w));
    let pr = t->Continue_0;
    assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
    assert(pr.application_data =~= Seq::<u8>::empty());
    assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    assert(s2.mode == crate::connection::dispatcher_spec::Mode::Handshake && s2.framing.len() == 0) by {
        reveal(super::dispatcher::dispatcher_agrees);
    }
    assert(s2.framing =~= Seq::<u8>::empty());
    assert(crate::connection::dispatcher_spec::State { framing: seq![], ..s2 } == s2);
    super::framing::lemma_empty(true);
    assert(Seq::<u8>::empty() + w.skip(n as int) =~= w.skip(n as int));
}

/// The flight's step on the server Finished: the client's flight goes out
/// and is acknowledged at once (`driver_spec` choice 2), the transducer
/// starts, and the transcription is in CONNECTED with the same bytes sent,
/// or the same messages in one record per message ([`goes_on_coalesced`]).
#[verifier::rlimit(40)]
pub proof fn lemma_flight_send(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::connection::dispatcher_spec::State,
    held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
        flight_case(m, p, s, ts, chunk),
        tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, front(ts.buffer + chunk)).0 {
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
            ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
            ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                send: flat(records_to_send), deliver: application_data,
                after: TState { client, buffer: (ts.buffer + chunk).skip((5 + super::bootstrap::length(ts.buffer + chunk)) as int), ..ts },
                end: TEnd::Running },
        },
        crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m),
            crate::connection::dispatcher_spec::State { framing: seq![], ..s }, front(ts.buffer + chunk)).0 is Send,
    ensures flight_whole(m, p, scalar, s, held, ts, chunk, cs2),
{
    hide(super::dispatcher::dispatcher_agrees);
    hide(super::post_handshake::post_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(super::bootstrap::one_record);
    hide(rejects_record);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(exhausted_epoch);
    hide(peer_closed);
    hide(ends_alike);
    let c = m.crypto;
    let v = m.verification;
    let f = ciphers(m);
    let w = ts.buffer + chunk;
    let n = 5 + super::bootstrap::length(w);
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s0, front(w));
    let wire = a->Send_0;
    let t = super::bootstrap::one_record(p, ts.client.connection, front(w));
    let pr = t->Continue_0;
    assert(super::dispatcher::sent_agrees(c, v, f, p, ts.client, pr, wire, s2));
    assert(super::dispatcher::ack_agrees(c, v, f, p, s2, pr.connection));
    assert(s2.pending_flight == wire);
    let cout = crate::connection::driver_spec::flight_out(c, v, f, a, s2);
    let ack = crate::connection::dispatcher_spec::acknowledge(c, v, f, s2, wire);
    let app = crate::connection::post_handshake_spec::start(c, ack.1.client_application_secret,
        ack.1.server_application_secret)->Ok_0;
    assert(cout == Step { send: wire, deliver: seq![], stage: Stage::App(app), status: Status::Open });
    assert(app.phase == crate::connection::post_handshake_spec::Phase::Open);
    assert(pr.application_data =~= Seq::<u8>::empty());
    let cs = CState { stage: Stage::Flight(s), status: Status::Handshaking, held };
    let tout = tfeed(p, ts, chunk);
    if cs2.stage == cout.stage && cs2.status == cout.status && cs2.held == w.skip(n as int) {
        assert(driver_agrees(m, p, scalar, cs2, tout.after));
        if super::dispatcher::client_flight(pr.connection.handshake).len() == 1 {
            assert(goes_on(m, p, scalar, cout, cs2, tout));
        } else {
            assert(goes_on_coalesced(m, p, scalar, ts, cout, cs2, tout));
        }
    }
}

/// The flight's step on a whole record that fails, or the server's error
/// alert: both end alike, or the crate rejects as the dispatcher theorem
/// compares rejections.
pub proof fn lemma_flight_fail(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::connection::dispatcher_spec::State,
    held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
        flight_case(m, p, s, ts, chunk),
        super::dispatcher::record_agrees(m.crypto, m.verification, ciphers(m), p,
            crate::connection::dispatcher_spec::State { framing: seq![], ..s }, ts.client, front(ts.buffer + chunk)),
        tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, front(ts.buffer + chunk)).0 {
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
            ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
            ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                send: flat(records_to_send), deliver: application_data,
                after: TState { client, buffer: (ts.buffer + chunk).skip((5 + super::bootstrap::length(ts.buffer + chunk)) as int), ..ts },
                end: TEnd::Running },
        },
        ({
            let a = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m),
                crate::connection::dispatcher_spec::State { framing: seq![], ..s }, front(ts.buffer + chunk)).0;
            a is Fail || a is PeerAlert
        }),
    ensures flight_whole(m, p, scalar, s, held, ts, chunk, cs2),
{
    hide(super::dispatcher::dispatcher_agrees);
    hide(super::dispatcher::record_agrees);
    hide(super::dispatcher::fail_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(super::bootstrap::one_record);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(exhausted_epoch);
    hide(goes_on_coalesced);
    hide(peer_closed);
    hide(goes_on);
    let w = ts.buffer + chunk;
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0, front(w));
    let u = crate::transcription::middlebox::client_receive_stream(p, ts.client, front(w)).0;
    let cout = crate::connection::driver_spec::flight_out(m.crypto, m.verification, ciphers(m), a, s2);
    let tout = tfeed(p, ts, chunk);
    if let ClientReceive::Abort(e) = u {
        if let crate::connection::dispatcher_spec::Action::Fail(alert, _) = a {
            if crate::transcription::alerts::required_alert(e) == alert as nat {
                assert(ends_alike(cout, tout));
            }
        }
    }
}

/// The flight's step on the server's close_notify: the crate answers with
/// the transcription's `close_write` record and ends; the transcription
/// stops reading ([`peer_closed`]).
pub proof fn lemma_flight_close(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::connection::dispatcher_spec::State,
    held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
        flight_case(m, p, s, ts, chunk),
        super::dispatcher::in_flight(ts.client.connection.handshake.state),
        tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, front(ts.buffer + chunk)).0 {
            ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
            ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
            ClientReceive::Continue { client, application_data, records_to_send } => TOut {
                send: flat(records_to_send), deliver: application_data,
                after: TState { client, buffer: (ts.buffer + chunk).skip((5 + super::bootstrap::length(ts.buffer + chunk)) as int), ..ts },
                end: TEnd::Running },
        },
        crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m),
            crate::connection::dispatcher_spec::State { framing: seq![], ..s }, front(ts.buffer + chunk)).0 is Close,
    ensures flight_whole(m, p, scalar, s, held, ts, chunk, cs2),
{
    hide(super::dispatcher::dispatcher_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(super::bootstrap::one_record);
    hide(rejects_record);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(exhausted_epoch);
    hide(goes_on_coalesced);
    hide(goes_on);
    hide(ends_alike);
    let w = ts.buffer + chunk;
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0, front(w));
    let y = ts.client.connection;
    let t = super::bootstrap::one_record(p, y, front(w));
    let pr = t->Continue_0;
    assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
    assert(pr.application_data =~= Seq::<u8>::empty());
    assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    super::dispatcher::lemma_alert_record_kept(p, y, pr.connection, 0);
    let cout = crate::connection::driver_spec::flight_out(m.crypto, m.verification, ciphers(m), a, s2);
    assert(peer_closed(p, ts, cout, tfeed(p, ts, chunk)));
}

/// The flight stage on a whole record.
#[verifier::rlimit(40)]
pub proof fn lemma_flight_whole(m: Models, p: Primitives, scalar: Seq<u8>, s: crate::connection::dispatcher_spec::State,
    held: Seq<u8>, ts: TState, chunk: Seq<u8>, cs2: CState)
    requires
        hypotheses(m, p),
        flight_agrees(p, m.verification, s, held, ts),
        whole(ts.buffer + chunk),
    ensures flight_whole(m, p, scalar, s, held, ts, chunk, cs2),
{
    hide(flight_case);
    hide(feed_verdict);
    hide(flight_whole);
    hide(tfeed);
    hide(super::dispatcher::record_agrees);
    hide(super::dispatcher::dispatcher_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    lemma_flight_facts(m, p, s, held, ts, chunk);
    lemma_flight_case(m, p, s, held, ts, chunk);
    let a = crate::connection::dispatcher_spec::receive_record(m.crypto, m.verification, ciphers(m), s0,
        front(ts.buffer + chunk)).0;
    match a {
        crate::connection::dispatcher_spec::Action::None | crate::connection::dispatcher_spec::Action::Ignored
            | crate::connection::dispatcher_spec::Action::Cancelled =>
            lemma_flight_quiet(m, p, scalar, s, held, ts, chunk, cs2),
        crate::connection::dispatcher_spec::Action::Send(_) =>
            lemma_flight_send(m, p, scalar, s, held, ts, chunk, cs2),
        crate::connection::dispatcher_spec::Action::Fail(_, _) | crate::connection::dispatcher_spec::Action::PeerAlert(_) =>
            lemma_flight_fail(m, p, scalar, s, held, ts, chunk, cs2),
        crate::connection::dispatcher_spec::Action::Close(_) =>
            lemma_flight_close(m, p, scalar, s, held, ts, chunk, cs2),
        crate::connection::dispatcher_spec::Action::Ready => {
            reveal(flight_case);
        },
    }
}

/// The flight stage with no whole record at the front: it waits (both
/// go on), or rejects the header early.
#[verifier::rlimit(80)]
pub proof fn lemma_flight_partial(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is Flight,
        !whole(ts.buffer + chunk),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::connection::dispatcher_spec::feed);
    hide(super::dispatcher::dispatcher_agrees);
    hide(rejects_record);
    hide(retry_then_fails);
    hide(exhausted_epoch);
    hide(goes_on_coalesced);
    hide(peer_closed);
    hide(ends_alike);
    let s = cs.stage->Flight_0;
    let c = m.crypto;
    let v = m.verification;
    let f = ciphers(m);
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let input = cs.held + chunk;
    let x = s.framing + input;
    assert(x =~= ts.buffer + chunk);
    let cl = ts.client;
    let y = cl.connection;
    super::framing::lemma_disp_agrees_facts(p, v, s0, cl);
    assert(super::dispatcher::in_flight(y.handshake.state)) by {
        reveal(super::dispatcher::dispatcher_agrees);
    }
    super::framing::lemma_disp_feed(c, v, f, s, input);
    super::framing::lemma_first(x, x.len(), true);
    super::framing::lemma_framing_agrees(y, x, true);
    lemma_tfeed_partial(p, ts, chunk);
    let (st, k) = super::framing::first(x, true);
    let r = crate::connection::dispatcher_spec::feed(c, v, f, s, input);
    let cout = crate::connection::driver_spec::flight_out(c, v, f, r.1, r.2);
    let cs2 = CState { stage: cout.stage, status: cout.status, held: input.skip(r.0 as int) };
    assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
    let tout = tfeed(p, ts, chunk);
    if st is Pending {
        assert(input.skip(r.0 as int) =~= Seq::<u8>::empty());
        assert(x + Seq::<u8>::empty() =~= x);
        assert(x.take(x.len() as int) =~= x);
        super::framing::lemma_need_more_wf(x, true);
        assert(crate::connection::dispatcher_spec::State { framing: seq![], ..r.2 } == s0);
        assert(goes_on(m, p, scalar, cout, cs2, tout));
    } else if st is Fail {
        let a = st->Fail_0;
        super::framing::lemma_early_alert(x, a);
        super::dispatcher::lemma_fatal(f, p, s0, y, a);
        assert(rejects_early(cs, ts, chunk, cout, tout));
    } else {
        assert(x.take(k as int).subrange(3, 5) =~= x.subrange(3, 5));
    }
}

/// **The flight stage, one operation**: feeding a chunk agrees
/// ([`op_agrees`]).
pub proof fn lemma_flight_feed(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is Flight,
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(flight_whole);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::connection::dispatcher_spec::feed);
    hide(super::dispatcher::dispatcher_agrees);
    hide(crate::connection::driver_spec::flight_out);
    hide(feed_verdict);
    if !whole(ts.buffer + chunk) {
        lemma_flight_partial(m, p, scalar, cs, ts, chunk);
    } else {
        let s = cs.stage->Flight_0;
        let c = m.crypto;
        let v = m.verification;
        let f = ciphers(m);
        let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
        let input = cs.held + chunk;
        let x = s.framing + input;
        assert(x =~= ts.buffer + chunk);
        let y = ts.client.connection;
        super::framing::lemma_disp_agrees_facts(p, v, s0, ts.client);
        super::framing::lemma_disp_feed(c, v, f, s, input);
        super::framing::lemma_first(x, x.len(), true);
        super::framing::lemma_framing_agrees(y, x, true);
        let (st, k) = super::framing::first(x, true);
        let r = crate::connection::dispatcher_spec::feed(c, v, f, s, input);
        let cout = crate::connection::driver_spec::flight_out(c, v, f, r.1, r.2);
        let cs2 = CState { stage: cout.stage, status: cout.status, held: input.skip(r.0 as int) };
        assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
        let n = 5 + super::bootstrap::length(x);
        let b = front(x);
        match st {
            crate::connection::framing_spec::Status::Complete => {
                assert(x.take(k as int).subrange(3, 5) =~= x.subrange(3, 5));
                assert(k == n);
                assert(input.skip((k - s.framing.len()) as int) =~= x.skip(n as int));
            },
            crate::connection::framing_spec::Status::Fail(a) => {
                assert(b.subrange(3, 5) =~= x.subrange(3, 5));
                reveal(crate::connection::dispatcher_spec::receive_record);
            },
            crate::connection::framing_spec::Status::Pending => {
                super::framing::lemma_t_header(x);
            },
        }
        lemma_flight_whole(m, p, scalar, s, cs.held, ts, chunk, cs2);
        reveal(flight_whole);
    }
}


// ---------------------------------------------------------------------------
// The application stage.
// ---------------------------------------------------------------------------

/// A step of the transducer that goes on (`End::Continue`) from a state
/// that reads keeps its phase: only the server's close_notify and failures
/// change it, and those end the step otherwise.
pub proof fn lemma_continue_phase(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, wire: Seq<u8>)
    requires crate::connection::post_handshake_spec::can_read(s),
    ensures ({
        let r = crate::connection::post_handshake_spec::step(c, f, s, crate::connection::post_handshake_spec::Input::Bytes(wire));
        r.0.end is Continue ==> r.1.phase == s.phase
    }),
{
    match s.receiver {
        Some(rx) => {
            match crate::traffic::spec::receive(crate::connection::post_handshake_spec::open_of(f, rx), rx, wire) {
                (rx2, crate::traffic::spec::Read::Record(typ, content, used)) => {
                    lemma_record_phase(c, f, crate::connection::post_handshake_spec::State { receiver: Some(rx2), ..s },
                        typ, content);
                },
                _ => {},
            }
        },
        None => {},
    }
}

/// [`lemma_continue_phase`] for one record's content.
pub proof fn lemma_record_phase(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, typ: u8, content: Seq<u8>)
    ensures ({
        let r = crate::connection::post_handshake_spec::record(c, f, s, typ, content);
        r.0.end is Continue ==> r.1.phase == s.phase
    }),
{
    match crate::spec::feed_record(s.reassembly, crate::spec::Record { ctype: typ, fragment: content }) {
        crate::spec::Res::Ok((crate::spec::Event::Messages(ms), r)) => {
            lemma_messages_phase(c, f, crate::connection::post_handshake_spec::State { reassembly: r, ..s }, ms);
        },
        _ => {},
    }
}

/// [`lemma_continue_phase`] for a record's messages.
pub proof fn lemma_messages_phase(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, ms: Seq<Seq<u8>>)
    ensures ({
        let r = crate::connection::post_handshake_spec::messages(c, f, s, ms);
        r.0.end is Continue ==> r.1.phase == s.phase
    }),
    decreases ms.len(),
{
    if ms.len() > 0 {
        lemma_message_phase(c, f, s, ms[0], ms.len() == 1);
        let r = crate::connection::post_handshake_spec::message(c, f, s, ms[0], ms.len() == 1);
        crate::connection::post_handshake_lemmas::lemma_message_end(c, f, s, ms[0], ms.len() == 1);
        if crate::connection::post_handshake_spec::can_read(r.1) {
            lemma_messages_phase(c, f, r.1, ms.skip(1));
        }
    }
}

/// [`lemma_continue_phase`] for one message.
pub proof fn lemma_message_phase(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, m: Seq<u8>, last: bool)
    ensures ({
        let r = crate::connection::post_handshake_spec::message(c, f, s, m, last);
        r.0.end is Continue ==> r.1.phase == s.phase
    }),
{
}

/// What the application stage's step on the stream comes to.
pub open spec fn app_out(m: Models, s: crate::connection::post_handshake_spec::State, w: Seq<u8>) -> (nat, Step) {
    let r = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, s,
        crate::connection::post_handshake_spec::Input::Bytes(w));
    (r.2, crate::connection::driver_spec::carry_out(m.cipher, r.0, r.1))
}

/// A step of the transducer from a state that reads ends with the server's
/// close_notify only through `peer_closed`: `PeerClosed` leaves it
/// `ReadClosed`, `Close` (our close_notify already sent) `Closed`.
pub proof fn lemma_closed_phase(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, wire: Seq<u8>)
    requires crate::connection::post_handshake_spec::can_read(s),
    ensures ({
        let r = crate::connection::post_handshake_spec::step(c, f, s, crate::connection::post_handshake_spec::Input::Bytes(wire));
        &&& r.0.end is PeerClosed ==> r.1.phase == crate::connection::post_handshake_spec::Phase::ReadClosed
            && s.phase == crate::connection::post_handshake_spec::Phase::Open
        &&& r.0.end is Close ==> r.1.phase == crate::connection::post_handshake_spec::Phase::Closed
            && s.phase == crate::connection::post_handshake_spec::Phase::WriteClosed
    }),
{
    match s.receiver {
        Some(rx) => {
            match crate::traffic::spec::receive(crate::connection::post_handshake_spec::open_of(f, rx), rx, wire) {
                (rx2, crate::traffic::spec::Read::Record(typ, content, used)) => {
                    let s1 = crate::connection::post_handshake_spec::State { receiver: Some(rx2), ..s };
                    match crate::spec::feed_record(s1.reassembly, crate::spec::Record { ctype: typ, fragment: content }) {
                        crate::spec::Res::Ok((crate::spec::Event::Messages(ms), r)) => {
                            lemma_messages_open_end(c, f, crate::connection::post_handshake_spec::State { reassembly: r, ..s1 }, ms);
                        },
                        _ => {},
                    }
                },
                _ => {},
            }
        },
        None => {},
    }
}

/// A record's messages end the connection only by a failure.
pub proof fn lemma_messages_open_end(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, ms: Seq<Seq<u8>>)
    ensures ({
        let e = crate::connection::post_handshake_spec::messages(c, f, s, ms).0.end;
        e is Continue || e is Fail
    }),
    decreases ms.len(),
{
    if ms.len() > 0 {
        let r = crate::connection::post_handshake_spec::message(c, f, s, ms[0], ms.len() == 1);
        if crate::connection::post_handshake_spec::can_read(r.1) {
            lemma_messages_open_end(c, f, r.1, ms.skip(1));
        }
    }
}

/// The record-level facts of a whole record in the application stage: the
/// step on the stream is the step on the record, the post-handshake
/// theorem's `outcome_agrees` holds of it, and the transcription's caller
/// reads it.
pub open spec fn app_case(m: Models, p: Primitives, s: crate::connection::post_handshake_spec::State, ts: TState,
    chunk: Seq<u8>) -> bool
{
    let w = ts.buffer + chunk;
    let b = front(w);
    let conn = ts.client.connection;
    let r = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, s,
        crate::connection::post_handshake_spec::Input::Bytes(w));
    let rb = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, s,
        crate::connection::post_handshake_spec::Input::Bytes(b));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    &&& r.0 == rb.0
    &&& r.1 == rb.1
    &&& super::post_handshake::record_agrees(p, m.cipher, s, conn, b, rb, tb)
    &&& super::post_handshake::outcome_agrees(p, s, conn, rb.0, rb.1, tb, match rb.0.end {
        crate::connection::post_handshake_spec::End::Fail(a) => super::post_handshake::fail_agrees(m.cipher, s, b, tb, a),
        _ => true })
    &&& (r.0.end is Continue ==> r.2 == 5 + super::bootstrap::length(w) && r.1.phase == s.phase)
    &&& (r.0.end is PeerClosed ==> r.1.phase == crate::connection::post_handshake_spec::Phase::ReadClosed
        && s.phase == crate::connection::post_handshake_spec::Phase::Open)
    &&& (r.0.end is Close ==> r.1.phase == crate::connection::post_handshake_spec::Phase::Closed
        && s.phase == crate::connection::post_handshake_spec::Phase::WriteClosed)
    &&& crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 == super::dispatcher::lifted(ts.client, tb)
    &&& tfeed(p, ts, chunk) == match crate::transcription::middlebox::client_receive_stream(p, ts.client, b).0 {
        ClientReceive::Abort(e) => TOut { send: abort_bytes(p, ts, e), deliver: seq![], after: ts, end: TEnd::Aborted(e) },
        ClientReceive::PeerError(d) => TOut { send: seq![], deliver: seq![], after: ts, end: TEnd::Peer(d) },
        ClientReceive::Continue { client, application_data, records_to_send } => TOut {
            send: flat(records_to_send), deliver: application_data,
            after: TState { client, buffer: w.skip((5 + super::bootstrap::length(w)) as int), ..ts },
            end: TEnd::Running },
    }
}

/// [`app_case`].
pub proof fn lemma_app_case(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App,
        app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
        whole(ts.buffer + chunk),
    ensures app_case(m, p, cs.stage->App_0, ts, chunk),
{
    hide(super::post_handshake::record_agrees);
    hide(super::post_handshake::post_agrees);
    hide(crate::connection::post_handshake_spec::step);
    hide(crate::transcription::connection::receive_stream);
    let s = cs.stage->App_0;
    let c = m.crypto;
    let f = m.cipher;
    let conn = ts.client.connection;
    let w = ts.buffer + chunk;
    let b = front(w);
    super::post_handshake::lemma_receive_open_facts(s, conn);
    super::framing::lemma_post_whole(c, f, p, s, conn, w);
    lemma_tfeed_whole(p, ts, chunk);
    super::framing::lemma_client_lifted(p, ts.client, b);
    lemma_continue_phase(c, f, s, w);
    lemma_closed_phase(c, f, s, w);
    let rb = crate::connection::post_handshake_spec::step(c, f, s, crate::connection::post_handshake_spec::Input::Bytes(b));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    assert(super::post_handshake::outcome_agrees(p, s, conn, rb.0, rb.1, tb, match rb.0.end {
        crate::connection::post_handshake_spec::End::Fail(a) => super::post_handshake::fail_agrees(f, s, b, tb, a),
        _ => true })) by {
        reveal(super::post_handshake::record_agrees);
    }
}

/// The application stage on a whole record that goes on: both go on, the
/// crate sending nothing (an `update_requested` is owed an answer on both
/// sides).
#[verifier::rlimit(40)]
pub proof fn lemma_app_continue(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App,
        app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
        whole(ts.buffer + chunk),
        app_case(m, p, cs.stage->App_0, ts, chunk),
        crate::connection::post_handshake_spec::step(m.crypto, m.cipher, cs.stage->App_0,
            crate::connection::post_handshake_spec::Input::Bytes(ts.buffer + chunk)).0.end is Continue,
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(super::post_handshake::record_agrees);
    hide(super::post_handshake::post_agrees);
    hide(crate::connection::post_handshake_spec::step);
    hide(crate::transcription::connection::receive_stream);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(rejects_record);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(goes_on_coalesced);
    hide(exhausted_epoch);
    hide(peer_closed);
    hide(ends_alike);
    let s = cs.stage->App_0;
    let f = m.cipher;
    let conn = ts.client.connection;
    let w = ts.buffer + chunk;
    assert(w =~= cs.held + chunk);
    let b = front(w);
    let r = crate::connection::post_handshake_spec::step(m.crypto, f, s, crate::connection::post_handshake_spec::Input::Bytes(w));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    let cout = crate::connection::driver_spec::carry_out(f, r.0, r.1);
    let cs2 = CState { stage: cout.stage, status: cout.status, held: (cs.held + chunk).skip(r.2 as int) };
    assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
    let tout = tfeed(p, ts, chunk);
    let pr = tb->Continue_0;
    let conn2 = pr.connection;
    assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
    assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    lemma_concat_flat(r.0.wires);
    assert(ts.write_closed == (s.phase == crate::connection::post_handshake_spec::Phase::WriteClosed));
    assert(r.0.wires =~= Seq::<Seq<u8>>::empty());
    assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
    assert(goes_on(m, p, scalar, cout, cs2, tout));
}

/// The application stage on a whole record that fails, or the server's
/// error alert: both end alike, or the crate rejects as the post-handshake
/// theorem compares rejections.
#[verifier::rlimit(40)]
pub proof fn lemma_app_fail(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App,
        app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
        whole(ts.buffer + chunk),
        app_case(m, p, cs.stage->App_0, ts, chunk),
        ({
            let e = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, cs.stage->App_0,
                crate::connection::post_handshake_spec::Input::Bytes(ts.buffer + chunk)).0.end;
            e is Fail || e is PeerAlert
        }),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(super::post_handshake::record_agrees);
    hide(super::post_handshake::post_agrees);
    hide(super::post_handshake::fail_agrees);
    hide(crate::connection::post_handshake_spec::step);
    hide(crate::transcription::connection::receive_stream);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(goes_on_coalesced);
    hide(exhausted_epoch);
    hide(peer_closed);
    hide(goes_on);
    let s = cs.stage->App_0;
    let f = m.cipher;
    let conn = ts.client.connection;
    let w = ts.buffer + chunk;
    assert(w =~= cs.held + chunk);
    let b = front(w);
    let r = crate::connection::post_handshake_spec::step(m.crypto, f, s, crate::connection::post_handshake_spec::Input::Bytes(w));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    let cout = crate::connection::driver_spec::carry_out(f, r.0, r.1);
    let cs2 = CState { stage: cout.stage, status: cout.status, held: (cs.held + chunk).skip(r.2 as int) };
    assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
    let tout = tfeed(p, ts, chunk);
    lemma_concat_flat(r.0.wires);
    assert(ts.write_closed == !crate::connection::post_handshake_spec::can_write(s));
    match r.0.end {
        crate::connection::post_handshake_spec::End::Fail(a) => {
            if let Receive::Abort(e) = tb {
                if crate::transcription::alerts::required_alert(e) == a as nat {
                    super::ccs::lemma_flatten(crate::transcription::connection::alert_record(p, conn, a as nat),
                        crate::transcription::connection::alert_record(p, conn, a as nat));
                    assert(Seq::<u8>::empty() + crate::transcription::connection::alert_record(p, conn, a as nat)
                        =~= crate::transcription::connection::alert_record(p, conn, a as nat));
                    assert(r.0.delivered =~= Seq::<u8>::empty());
                    assert(ends_alike(cout, tout));
                }
            }
        },
        _ => {
            assert(r.0.wires =~= Seq::<Seq<u8>>::empty());
            assert(r.0.delivered =~= Seq::<u8>::empty());
            assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
            assert(ends_alike(cout, tout));
        },
    }
}

/// The application stage on the server's close_notify: the crate answers
/// with the transcription's `close_write` record if its write side is open,
/// and ends; the transcription stops reading ([`peer_closed`]).
#[verifier::rlimit(80)]
pub proof fn lemma_app_closed(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App,
        app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
        whole(ts.buffer + chunk),
        app_case(m, p, cs.stage->App_0, ts, chunk),
        ({
            let e = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, cs.stage->App_0,
                crate::connection::post_handshake_spec::Input::Bytes(ts.buffer + chunk)).0.end;
            e is PeerClosed || e is Close
        }),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(super::post_handshake::record_agrees);
    hide(crate::connection::post_handshake_spec::step);
    hide(crate::transcription::connection::receive_stream);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(rejects_record);
    hide(rejects_early);
    hide(retry_then_fails);
    hide(goes_on_coalesced);
    hide(exhausted_epoch);
    hide(goes_on);
    hide(ends_alike);
    let s = cs.stage->App_0;
    let f = m.cipher;
    let conn = ts.client.connection;
    let w = ts.buffer + chunk;
    assert(w =~= cs.held + chunk);
    let b = front(w);
    let r = crate::connection::post_handshake_spec::step(m.crypto, f, s, crate::connection::post_handshake_spec::Input::Bytes(w));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    let cout = crate::connection::driver_spec::carry_out(f, r.0, r.1);
    let cs2 = CState { stage: cout.stage, status: cout.status, held: (cs.held + chunk).skip(r.2 as int) };
    assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
    let tout = tfeed(p, ts, chunk);
    let pr = tb->Continue_0;
    let conn2 = pr.connection;
    assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
    assert(flat(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    lemma_concat_flat(r.0.wires);
    if r.0.end is PeerClosed {
        assert(r.1.phase == crate::connection::post_handshake_spec::Phase::ReadClosed);
        super::post_handshake::lemma_close(f, p, r.1, conn2);
        let rc = crate::connection::post_handshake_spec::close(f, r.1);
        lemma_concat_flat(rc.0.wires);
        super::ccs::lemma_flatten(crate::transcription::connection::close_write(p, conn2),
            crate::transcription::connection::close_write(p, conn2));
        assert(r.0.wires =~= Seq::<Seq<u8>>::empty());
        assert(Seq::<u8>::empty() + crate::transcription::connection::close_write(p, conn2)
            =~= crate::transcription::connection::close_write(p, conn2));
        assert(ts.write_closed == false);
        assert(peer_closed(p, ts, cout, tout));
    } else {
        assert(r.1.phase == crate::connection::post_handshake_spec::Phase::Closed);
        assert(r.0.wires =~= Seq::<Seq<u8>>::empty());
        assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        assert(peer_closed(p, ts, cout, tout));
    }
}

/// The application stage on a whole record.
pub proof fn lemma_app_whole(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App,
        app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
        whole(ts.buffer + chunk),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(app_case);
    hide(op_agrees);
    hide(driver_agrees);
    hide(crate::connection::post_handshake_spec::step);
    lemma_app_case(m, p, scalar, cs, ts, chunk);
    let e = crate::connection::post_handshake_spec::step(m.crypto, m.cipher, cs.stage->App_0,
        crate::connection::post_handshake_spec::Input::Bytes(ts.buffer + chunk)).0.end;
    match e {
        crate::connection::post_handshake_spec::End::Continue => lemma_app_continue(m, p, scalar, cs, ts, chunk),
        crate::connection::post_handshake_spec::End::Fail(_) | crate::connection::post_handshake_spec::End::PeerAlert(_) =>
            lemma_app_fail(m, p, scalar, cs, ts, chunk),
        _ => lemma_app_closed(m, p, scalar, cs, ts, chunk),
    }
}

/// **The application stage, one operation**: feeding a chunk agrees
/// ([`op_agrees`]).
#[verifier::rlimit(40)]
pub proof fn lemma_app_feed(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, chunk: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App,
        app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Feed(chunk)),
{
    hide(super::post_handshake::post_agrees);
    hide(crate::connection::post_handshake_spec::step);
    hide(rejects_record);
    hide(retry_then_fails);
    hide(goes_on_coalesced);
    let w = ts.buffer + chunk;
    if whole(w) {
        lemma_app_whole(m, p, scalar, cs, ts, chunk);
    } else {
        let s = cs.stage->App_0;
        let c = m.crypto;
        let f = m.cipher;
        let conn = ts.client.connection;
        assert(w =~= cs.held + chunk);
        super::post_handshake::lemma_receive_open_facts(s, conn);
        super::framing::lemma_post_partial(c, f, p, s, conn, w);
        lemma_tfeed_partial(p, ts, chunk);
        super::framing::lemma_stream_partial(p, conn, w);
        let r = crate::connection::post_handshake_spec::step(c, f, s, crate::connection::post_handshake_spec::Input::Bytes(w));
        let cout = crate::connection::driver_spec::carry_out(f, r.0, r.1);
        let cs2 = CState { stage: cout.stage, status: cout.status, held: (cs.held + chunk).skip(r.2 as int) };
        assert(cop(m, scalar, cs, Op::Feed(chunk)) == (cout, cs2));
        let tout = tfeed(p, ts, chunk);
        if super::framing::post_waits(r) {
            assert(cs2.held =~= w);
            assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
            lemma_concat_flat(Seq::<Seq<u8>>::empty());
            assert(goes_on(m, p, scalar, cout, cs2, tout));
        } else {
            lemma_concat_flat(r.0.wires);
            let a = r.0.end->Fail_0;
            if super::post_handshake::exhausted(s) && a == crate::spec::INTERNAL_ERROR {
                assert(exhausted_epoch(cs, cout, tout) || rejects_early(cs, ts, chunk, cout, tout));
            } else {
                assert(rejects_early(cs, ts, chunk, cout, tout));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The caller's sends and closes.
// ---------------------------------------------------------------------------

/// Sending application data that goes on keeps the transducer's phase.
pub proof fn lemma_send_phase(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, data: Seq<u8>)
    ensures ({
        let r = crate::connection::post_handshake_spec::send_application(c, f, s, data);
        r.0.end is Continue ==> r.1.phase == s.phase
    }),
{
}

/// **Sending application data** agrees: before the handshake ends neither
/// sends anything (`driver_contract::send_ensures`; the transcription's
/// `send_application_data` is `NotConnected`); after it, the crate's record
/// is the transcription's (`post_handshake::send_agrees`, with the owed
/// KeyUpdate of §4.6.3 and §5.3's KeyUpdate before the last sequence number
/// on both sides), or neither
/// sends after its close_notify; or data above 2^14 octets is the stated
/// difference [`oversized`].
#[verifier::rlimit(40)]
pub proof fn lemma_send_op(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, data: Seq<u8>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App ==> app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Send(data)),
{
    hide(super::post_handshake::post_agrees);
    hide(super::bootstrap::bootstrap_agrees);
    hide(super::dispatcher::dispatcher_agrees);
    let (cout, cs2) = cop(m, scalar, cs, Op::Send(data));
    let tout = top(p, ts, Op::Send(data));
    let conn = ts.client.connection;
    match cs.stage {
        Stage::Hello(s, _) => {
            assert(conn.handshake.state == crate::transcription::state_machine::ClientState::WaitSh) by {
                reveal(super::bootstrap::bootstrap_agrees);
            }
            assert(cs2 == cs);
            assert(tout.after == ts);
        },
        Stage::Flight(s) => {
            let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
            super::framing::lemma_disp_agrees_facts(p, m.verification, s0, ts.client);
            assert(super::dispatcher::in_flight(conn.handshake.state)) by {
                reveal(super::dispatcher::dispatcher_agrees);
            }
            assert(cs2 == cs);
            assert(tout.after == ts);
        },
        Stage::App(s) => {
            super::post_handshake::lemma_receive_open_facts(s, conn);
            let c = m.crypto;
            let f = m.cipher;
            let r = crate::connection::post_handshake_spec::send_application(c, f, s, data);
            if s.phase == crate::connection::post_handshake_spec::Phase::Open {
                if data.len() <= crate::spec::MAX_PLAINTEXT {
                    super::post_handshake::lemma_send_application(c, f, p, s, conn, data);
                    lemma_send_phase(c, f, s, data);
                    lemma_concat_flat(r.0.wires);
                    assert(Seq::<u8>::empty() + flat(r.0.wires) =~= flat(r.0.wires));
                    assert(r.0.delivered =~= Seq::<u8>::empty());
                    assert(goes_on(m, p, scalar, cout, cs2, tout));
                } else {
                    super::post_handshake::lemma_oversized(c, f, p, s, conn, data);
                    assert(oversized(cs, data, cout, tout));
                }
            } else {
                assert(cout.send =~= Seq::<u8>::empty());
                assert(cs2 == cs);
            }
        },
        Stage::Ended => {},
    }
}

/// **Closing** agrees: before the handshake ends, both write the same
/// close_notify (the plaintext one before the ServerHello, the one under
/// the client handshake key in the flight), and the crate ends the
/// connection (the stated difference [`closes_in_handshake`]); after it,
/// the crate's `close` is the transcription's `close_write`
/// (`post_handshake::close_agrees`) and both go on reading, or neither
/// writes after its close_notify.
#[verifier::rlimit(80)]
pub proof fn lemma_close_op(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
        cs.stage is App ==> app_agrees(cs.stage->App_0, cs.status, cs.held, ts),
    ensures op_agrees(m, p, scalar, cs, ts, Op::Close),
{
    hide(super::post_handshake::post_agrees);
    hide(crate::connection::dispatcher_spec::close_wire);
    hide(super::bootstrap::bootstrap_agrees);
    hide(super::dispatcher::dispatcher_agrees);
    let (cout, cs2) = cop(m, scalar, cs, Op::Close);
    let tout = top(p, ts, Op::Close);
    let conn = ts.client.connection;
    match cs.stage {
        Stage::Hello(s, _) => {
            assert(conn.handshake.state == crate::transcription::state_machine::ClientState::WaitSh
                && conn.send == Protection::Unprotected) by {
                reveal(super::bootstrap::bootstrap_agrees);
            }
            lemma_alert_record_plain(p, conn, 0);
            assert(closes_in_handshake(cout, tout));
        },
        Stage::Flight(s) => {
            let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
            super::framing::lemma_disp_agrees_facts(p, m.verification, s0, ts.client);
            assert(super::dispatcher::in_flight(conn.handshake.state)) by {
                reveal(super::dispatcher::dispatcher_agrees);
            }
            super::dispatcher::lemma_closing(ciphers(m), p, s0, conn);
            assert(crate::connection::dispatcher_spec::close_wire(ciphers(m), s)
                == crate::connection::dispatcher_spec::close_wire(ciphers(m), s0)) by {
                reveal(crate::connection::dispatcher_spec::close_wire);
            }
            assert(closes_in_handshake(cout, tout));
        },
        Stage::App(s) => {
            super::post_handshake::lemma_receive_open_facts(s, conn);
            let f = m.cipher;
            let r = crate::connection::post_handshake_spec::close(f, s);
            if s.phase == crate::connection::post_handshake_spec::Phase::Open {
                super::post_handshake::lemma_close(f, p, s, conn);
                lemma_concat_flat(r.0.wires);
                super::ccs::lemma_flatten(crate::transcription::connection::close_write(p, conn),
                    crate::transcription::connection::close_write(p, conn));
                assert(Seq::<u8>::empty() + crate::transcription::connection::close_write(p, conn)
                    =~= crate::transcription::connection::close_write(p, conn));
                assert(r.0.delivered =~= Seq::<u8>::empty());
                assert(r.1.phase == crate::connection::post_handshake_spec::Phase::WriteClosed);
                assert(goes_on(m, p, scalar, cout, cs2, tout));
            } else {
                assert(cout.send =~= Seq::<u8>::empty());
                assert(cs2 == cs);
            }
        },
        Stage::Ended => {},
    }
}

// ---------------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------------

/// One operation, from agreeing states, agrees.
pub proof fn lemma_op(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, op: Op)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
    ensures op_agrees(m, p, scalar, cs, ts, op),
{
    match op {
        Op::Feed(chunk) => match cs.stage {
            Stage::Hello(_, _) => lemma_hello_feed(m, p, scalar, cs, ts, chunk),
            Stage::Flight(_) => lemma_flight_feed(m, p, scalar, cs, ts, chunk),
            Stage::App(_) => lemma_app_feed(m, p, scalar, cs, ts, chunk),
            Stage::Ended => {},
        },
        Op::Send(data) => lemma_send_op(m, p, scalar, cs, ts, data),
        Op::Close => lemma_close_op(m, p, scalar, cs, ts),
    }
}

/// The run of the caller's operations `ops` compares: each operation's
/// outcomes agree ([`op_agrees`]), and the next is compared from the states
/// after it as long as they agree ([`driver_agrees`]); a rejection, an end
/// or a stated difference ends the comparison.
pub open spec fn run_agrees(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, ops: Seq<Op>) -> bool
    decreases ops.len(),
{
    if ops.len() == 0 {
        true
    } else {
        let (_, cs2) = cop(m, scalar, cs, ops[0]);
        let tout = top(p, ts, ops[0]);
        &&& op_agrees(m, p, scalar, cs, ts, ops[0])
        &&& (driver_agrees(m, p, scalar, cs2, tout.after) ==> run_agrees(m, p, scalar, cs2, tout.after, ops.skip(1)))
    }
}

/// [`run_agrees`] from agreeing states, for every run.
pub proof fn lemma_run(m: Models, p: Primitives, scalar: Seq<u8>, cs: CState, ts: TState, ops: Seq<Op>)
    requires
        hypotheses(m, p),
        driver_agrees(m, p, scalar, cs, ts),
    ensures run_agrees(m, p, scalar, cs, ts, ops),
    decreases ops.len(),
{
    hide(op_agrees);
    hide(driver_agrees);
    if ops.len() > 0 {
        lemma_op(m, p, scalar, cs, ts, ops[0]);
        let (_, cs2) = cop(m, scalar, cs, ops[0]);
        let tout = top(p, ts, ops[0]);
        if driver_agrees(m, p, scalar, cs2, tout.after) {
            lemma_run(m, p, scalar, cs2, tout.after, ops.skip(1));
        }
    }
}

/// The start: the crate's first record (`Driver::connect`) is the
/// transcription's `start_client` records, the driver then waits in its
/// Hello stage, and the two agree ([`driver_agrees`]). A configuration the
/// crate's `client_spec::config_ok` refuses ends the connection before
/// anything is sent; the transcription has no such refusal (its
/// `start_client` expects a ClientHello meeting `client_hello_conforms`,
/// which `client::theorem_client_hello_equivalence` shows the crate's is
/// for every configuration it accepts).
pub open spec fn start_agrees(m: Models, p: Primitives, config: crate::hello::client_spec::Config,
    tconfig: crate::transcription::middlebox::ClientConfig, scalar: Seq<u8>) -> bool
{
    let out = cstart(m, config);
    let (ts, sent) = tstart(p, config, tconfig, scalar);
    match crate::hello::client_spec::start(config) {
        Err(alert) => out == Step { send: seq![], deliver: seq![], stage: Stage::Ended,
            status: Status::Failed(alert, Origin::NotSent) },
        Ok(_) => {
            &&& out.send == sent
            &&& out.deliver.len() == 0
            &&& driver_agrees(m, p, scalar, CState { stage: out.stage, status: out.status, held: seq![] }, ts)
        },
    }
}

/// [`start_agrees`], for one configuration.
pub proof fn lemma_start(m: Models, p: Primitives, config: crate::hello::client_spec::Config,
    tconfig: crate::transcription::middlebox::ClientConfig, scalar: Seq<u8>)
    requires
        hypotheses(m, p),
        scalar.len() == 32,
        (p.x25519)(scalar, crate::transcription::primitives::x25519_basepoint()) == config.public_key,
        tconfig.compatibility_mode == super::ccs::mode(config),
    ensures start_agrees(m, p, config, tconfig, scalar),
{
    super::bootstrap::lemma_start(p, config, tconfig, scalar, scalar);
    assert(m.crypto.hash == p.hash);
    match crate::hello::client_spec::start(config) {
        Err(_) => {},
        Ok(_) => {
            let first = super::client::ch_view(crate::hello::client_spec::client_hello(config, Seq::empty()));
            let hs = crate::transcription::state_machine::start_handshake(first, scalar, scalar);
            let c0 = Connection { handshake: hs, receive: Protection::Unprotected, send: Protection::Unprotected,
                handshake_fragments: seq![], read_closed: false, key_update_owed: false };
            lemma_apply_keeps(p, c0, seq![crate::transcription::state_machine::Action::SendHandshake(
                crate::transcription::key_exchange::write_client_hello(first),
                crate::transcription::state_machine::initial_client_hello_record_version())]);
            super::framing::lemma_empty(false);
            assert(Seq::<u8>::empty() + Seq::<u8>::empty() =~= Seq::<u8>::empty());
        },
    }
}

/// **The driver theorem.** RFC 8446 §4.1, §5, §6 and §7.3, end to end,
/// under [`hypotheses`] (the two sides' primitives are the same functions;
/// the certificate validators agree): for every configuration the crate
/// starts with, every X25519 scalar whose public value the configuration
/// offers, and the transcription in the crate's compatibility mode,
/// - **the start agrees** ([`start_agrees`]): the crate's first record is
///   `start_client`'s, and the two then agree ([`driver_agrees`]);
/// - **every run agrees** ([`run_agrees`]): for every sequence of the
///   caller's operations (bytes of the server's stream in any chunks, with
///   application data and a close interleaved anywhere), each operation's
///   outcomes compare ([`op_agrees`]): the bytes sent, the data delivered
///   and the status are the transcription's, both going on in agreeing
///   states, across the two handoffs (the bootstrap to the dispatcher at the
///   ServerHello, the dispatcher to the transducer at the acknowledged
///   client flight); or both end alike; or the crate rejects a record as the
///   record-level theorems compare rejections; or one of the stated
///   differences holds, after which the comparison ends: [`rejects_early`],
///   [`peer_closed`], [`retry_then_fails`], [`goes_on_coalesced`] (which goes
///   on), [`exhausted_epoch`], [`oversized`] and [`closes_in_handshake`]. Every record is compared: the crate's
///   caps are cases of the record-level theorems' rejections.
pub proof fn theorem_driver_equivalence(m: Models, p: Primitives)
    requires hypotheses(m, p),
    ensures
        forall|config: crate::hello::client_spec::Config, tconfig: crate::transcription::middlebox::ClientConfig,
            scalar: Seq<u8>|
            scalar.len() == 32
                && (p.x25519)(scalar, crate::transcription::primitives::x25519_basepoint()) == config.public_key
                && tconfig.compatibility_mode == super::ccs::mode(config)
            ==> #[trigger] start_agrees(m, p, config, tconfig, scalar),
        forall|scalar: Seq<u8>, cs: CState, ts: TState, ops: Seq<Op>|
            #[trigger] driver_agrees(m, p, scalar, cs, ts) ==> #[trigger] run_agrees(m, p, scalar, cs, ts, ops),
{
    assert forall|config: crate::hello::client_spec::Config, tconfig: crate::transcription::middlebox::ClientConfig,
        scalar: Seq<u8>|
        scalar.len() == 32
            && (p.x25519)(scalar, crate::transcription::primitives::x25519_basepoint()) == config.public_key
            && tconfig.compatibility_mode == super::ccs::mode(config)
        implies #[trigger] start_agrees(m, p, config, tconfig, scalar) by {
        lemma_start(m, p, config, tconfig, scalar);
    }
    assert forall|scalar: Seq<u8>, cs: CState, ts: TState, ops: Seq<Op>|
        #[trigger] driver_agrees(m, p, scalar, cs, ts) implies #[trigger] run_agrees(m, p, scalar, cs, ts, ops) by {
        lemma_run(m, p, scalar, cs, ts, ops);
    }
}


} // verus!
