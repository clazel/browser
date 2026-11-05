//! RFC 8446 §5, §7.3 and Appendix A.1: the initial protected connection flight.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-5>.
//!
//! Modelling choices:
//! - The connection begins after the final ServerHello and Hello's validated
//!   key handoff. ClientHello/ServerHello negotiation stays in `hello`.
//! - The active handshake/application epochs and Auth state are explicit.
//!   Key transitions happen only after the exact client flight is acknowledged.
//! - TCP input is processed one record prefix at a time. `framing` owns bytes
//!   already consumed from the caller; unconsumed suffix bytes remain caller
//!   owned. The reassembler owns only an unfinished handshake message.
//! - The compatibility CCS is a one-byte dummy record, tracked separately
//!   from the protected record epochs. For an HRR retry it was already sent
//!   before ClientHello2 by the Hello driver.
//! - RFC 8446 §5.1 forbids interleaving a handshake message with another
//!   record type, and a compatibility CCS is another record type. It is
//!   dropped only while no handshake message is partly received
//!   (`message_boundary`); in the middle of one it is fatal unexpected_message.
//! - Terminal states retain no authentication secrets, traffic epochs, or
//!   partial input. NewSessionTicket bodies are parsed and discarded; ticket
//!   caching, PSK resumption, 0-RTT, and secret-erasure guarantees are not
//!   modelled. Production transport, cryptography, and X.509 validation are
//!   also outside this module.
//! - RFC 8446 §6 and §6.2: a fatal error the client detects itself is
//!   `Fail(description, wire)` ([`fatal`]). `wire` is the protected record
//!   of the fatal alert ([`alert_wire`]), computed from the state before
//!   any key is dropped, so the caller puts it on the wire as the last
//!   record of the connection. It is sealed under the write epoch the peer
//!   reads next ([`alert_epoch`]): the client handshake epoch while the
//!   server's flight is received (`Handshake`). Its sequence number is that
//!   epoch's next one (§5.3), which no record has used, and the epoch is dropped with
//!   every other key ([`failed`]), so nothing is sealed under it afterwards.
//! - `wire` is `None` where no settled write epoch is held. In
//!   `AwaitClientFlight` the client Finished is sealed but not acknowledged,
//!   and the server reads the record after it under the client application
//!   key, which is not installed. Also when the epoch has failed or spent its
//!   sequence numbers (`traffic::spec::send` refuses), and in `Failed` and
//!   `Closed`, which hold no key.
//! - `Ready` is where this machine ends. It holds the two application traffic
//!   secrets and nothing else, and `post_handshake_spec` takes over from them
//!   (`dispatcher_contract::handoff_ensures`), with both directions at sequence
//!   number 0. So one machine runs after the handshake, and it is the one
//!   the post-handshake theorems are about.
//! - The transport ending before close_notify (§6.1, truncation) is
//!   `Fail(internal_error, None)` ([`die`]): the peer has closed the
//!   connection, so nothing is sent, as in `post_handshake_spec` (choice 6).
//! - A fatal alert received from the peer (any alert but close_notify and
//!   user_canceled) is `PeerAlert(description)` ([`receive_fatal_alert`]). It
//!   is never answered (§6: "Upon receiving an error alert, the TLS
//!   implementation SHOULD indicate an error to the application and MUST
//!   NOT allow any further data to be sent or received on the connection"),
//!   and every key is dropped as for a local failure.
//! - No compatibility CCS precedes a fatal alert, even while `ccs_pending`:
//!   Appendix D.4 puts the dummy CCS before the client's second flight, which
//!   the alert replaces, and §5 makes it optional for the peer (it "MUST
//!   simply drop it"), so the alert record alone is a valid record stream.
//! - §6.1: "Each party MUST send a "close_notify" alert before closing its
//!   write side". A close during the server's flight, the peer's or ours, is
//!   `Close(wire)`: our close_notify sealed like a fatal alert ([`close_wire`]),
//!   or `None` where no settled write epoch is held.
//! - RFC prose and equations have no numbered algorithm steps.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Initial TLS 1.3 connection-dispatch phase.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Receive and authenticate the server flight with handshake keys.
    Handshake,
    /// The client flight is protected and awaits its exact I/O acknowledgement.
    AwaitClientFlight,
    /// The client flight is acknowledged; the application traffic secrets are
    /// derived and `post_handshake_spec` takes over.
    Ready,
    /// Fatal error; all key and partial-input state is dropped.
    Failed,
    /// Transport closed; all key and partial-input state is dropped.
    Closed,
}

/// One ordered I/O effect from the dispatcher.
pub enum Action {
    /// Incomplete input, or a complete record that has no outward effect.
    None,
    /// Exact protected client flight awaiting its send acknowledgement.
    Send(Seq<u8>),
    /// The client flight was acknowledged and the transducer can take over.
    Ready,
    /// A permitted unprotected compatibility CCS was dropped.
    Ignored,
    /// A nonfatal user_canceled alert was reported without changing TLS state.
    Cancelled,
    /// RFC 8446 §6.2: a fatal error detected locally, with its alert
    /// description and the protected fatal alert record to send
    /// ([`alert_wire`]), or `None` when no settled write epoch is held.
    /// Every key is dropped.
    Fail(u8, Option<Seq<u8>>),
    /// RFC 8446 §6: the peer's fatal alert. It is not answered, and every key
    /// is dropped.
    PeerAlert(u8),
    /// §6.1: the connection closed during the flight, with our sealed
    /// close_notify ([`close_wire`]), or `None` when no epoch can seal it.
    Close(Option<Seq<u8>>),
}

/// Connection-owned protocol state after the final ServerHello.
pub struct State {
    /// Protocol phase.
    pub mode: Mode,
    /// Authentication/transcript state, absent after terminal failure/close.
    pub auth: Option<crate::auth::spec::State>,
    /// Client handshake send epoch, absent after the application transition.
    pub handshake_sender: Option<crate::traffic::spec::State>,
    /// Server handshake receive epoch, absent after the application transition.
    pub handshake_receiver: Option<crate::traffic::spec::State>,
    /// Application master secret, retained only until the traffic secrets exist.
    pub master: Seq<u8>,
    /// `client_application_traffic_secret_0`, derived after client-flight ack.
    pub client_application_secret: Seq<u8>,
    /// `server_application_traffic_secret_0`, derived after client-flight ack.
    pub server_application_secret: Seq<u8>,
    /// Bytes of one incomplete handshake message.
    pub reassembly: crate::spec::Reasm,
    /// Consumed wire prefix for one record; never contains a following record.
    pub framing: Seq<u8>,
    /// Whether the dummy compatibility CCS remains due before the client flight.
    pub ccs_pending: bool,
    /// Exact protected client flight awaiting acknowledgement.
    pub pending_flight: Seq<u8>,
}

/// Cipher functions retained from the factory for each active epoch.
pub struct Ciphers {
    /// Key-explicit encryption function supplied by the factory.
    pub seal: crate::traffic::spec::Seal,
    /// Key-explicit authentication function supplied by the factory.
    pub open: crate::traffic::spec::Open,
}

/// Key-explicit cipher functions retained by the connection across epochs.
pub open spec fn cipher_models(factory: crate::traffic::spec::Cipher, _state: State) -> Ciphers {
    Ciphers { seal: factory.seal, open: factory.open }
}

/// Reject any valid transition that has incomplete handshake input.
pub open spec fn message_boundary(s: State) -> bool {
    crate::spec::at_message_boundary(s.reassembly)
}

/// Appendix D.4 dummy CCS record, sent only when the retained Hello profile owes it.
pub open spec fn compatibility_ccs_record() -> Seq<u8> { seq![20u8, 3u8, 3u8, 0u8, 1u8, 1u8] }

/// RFC 8446 §5.1 "Handshake messages MUST NOT be interleaved with other
/// record types" and Appendix D.4: an unprotected compatibility CCS is dropped
/// only in the server-flight phases of the handshake, and only when no
/// handshake message is partly received.
pub open spec fn compatibility_ccs_dropped(mode: Mode, phase: Option<crate::auth::spec::Phase>,
    reassembly: crate::spec::Reasm) -> bool {
    mode == Mode::Handshake
        && match phase {
            Some(p) => p != crate::auth::spec::Phase::SendFinished && p != crate::auth::spec::Phase::Ready,
            None => false,
        }
        && crate::spec::at_message_boundary(reassembly)
}

/// The effect of one valid unprotected compatibility CCS record: dropped with
/// no state change when permitted, else a fatal unexpected_message.
pub open spec fn receive_compatibility_ccs(ciphers: Ciphers, s: State) -> (Action, State) {
    let phase = match s.auth { Some(a) => Some(a.phase), None => None };
    if compatibility_ccs_dropped(s.mode, phase, s.reassembly) {
        (Action::Ignored, s)
    } else {
        fatal(ciphers, s, crate::spec::UNEXPECTED_MESSAGE)
    }
}

/// A handshake record flight has Finished as its last complete message.
pub open spec fn finished_is_last(messages: Seq<Seq<u8>>) -> bool {
    messages.len() > 0 && messages.last().len() >= crate::spec::HANDSHAKE_HEADER
        && messages.last()[0] == 20
}

/// Whether all traffic epochs and authentication state have been discarded.
pub open spec fn no_live_secrets(s: State) -> bool {
    s.auth is None && s.handshake_sender is None && s.handshake_receiver is None
        && s.master.len() == 0
        && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0
}

/// Outward effects agree with the state transition that makes them safe.
pub open spec fn action_refines(action: Action, after: State) -> bool {
    match action {
        Action::Send(wire) => after.mode == Mode::AwaitClientFlight && after.pending_flight == wire,
        Action::Ready => after.mode == Mode::Ready,
        Action::Fail(_, _) => super::dispatcher_contract::terminal_ensures(after, Mode::Failed),
        Action::PeerAlert(_) => super::dispatcher_contract::terminal_ensures(after, Mode::Failed),
        Action::Close(_) => super::dispatcher_contract::terminal_ensures(after, Mode::Closed),
        Action::Cancelled => true,
        Action::None | Action::Ignored => true,
    }
}

/// Lifecycle, bounds, and key-phase invariants for the initial connection.
pub open spec fn wf(s: State) -> bool {
    // Runtime `resources_wf` carries the concrete Buffer/Reassembler bounds.
    match s.mode {
            Mode::Handshake => s.auth is Some && s.handshake_sender is Some
                && s.handshake_receiver is Some && s.master.len() == 32
                && s.pending_flight.len() == 0
                && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0,
            Mode::AwaitClientFlight => s.auth is Some && s.handshake_sender is Some
                && s.handshake_receiver is Some && s.master.len() == 32
                && s.pending_flight.len() > 0 && !s.ccs_pending
                && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0
                && crate::spec::at_message_boundary(s.reassembly)
                && s.framing.len() == 0
                && match s.auth { Some(a) => a.phase == crate::auth::spec::Phase::SendFinished,
                    None => false },
            Mode::Ready => s.auth is Some && s.handshake_sender is None
                && s.handshake_receiver is None && s.master.len() == 0
                && s.pending_flight.len() == 0 && !s.ccs_pending
                && s.client_application_secret.len() == 32 && s.server_application_secret.len() == 32
                && crate::spec::at_message_boundary(s.reassembly)
                && s.framing.len() == 0
                && match s.auth { Some(a) => a.phase == crate::auth::spec::Phase::Ready,
                    None => false },
            Mode::Failed | Mode::Closed => no_live_secrets(s)
                && s.reassembly.buf.len() == 0 && s.framing.len() == 0
                && s.pending_flight.len() == 0 && !s.ccs_pending,
        }
}

/// Start from the validated Hello/handshake-key handoff with empty buffers.
pub open spec fn start(h: crate::traffic::handshake_spec::Handoff, ccs_pending: bool) -> State {
    State {
        mode: Mode::Handshake,
        auth: Some(h.0),
        handshake_sender: Some(h.1),
        handshake_receiver: Some(h.2),
        master: h.3,
        client_application_secret: seq![],
        server_application_secret: seq![],
        reassembly: crate::spec::reasm_new(),
        framing: seq![],
        ccs_pending,
        pending_flight: seq![],
    }
}

/// §5.2: the key-explicit AEAD encryption under one epoch's key.
pub open spec fn seal_with(ciphers: Ciphers, epoch: crate::traffic::spec::State)
    -> spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>
{
    |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| (ciphers.seal)(epoch.key, n, ad, p)
}

/// §6, §5.3: the settled write epoch a fatal alert is sealed under, the one
/// whose key the peer reads our next record with: the client handshake epoch
/// during the server's flight. None in every other state.
pub open spec fn alert_epoch(s: State) -> Option<crate::traffic::spec::State> {
    match s.mode {
        Mode::Handshake => s.handshake_sender,
        Mode::AwaitClientFlight | Mode::Ready | Mode::Failed | Mode::Closed => None,
    }
}

/// §6, §6.2: the content of a fatal alert record. "All the alerts listed
/// in Section 6.2 MUST be sent with AlertLevel=fatal".
pub open spec fn fatal_alert(description: u8) -> Seq<u8> {
    crate::spec::write_alert(crate::spec::Alert { level: crate::spec::LEVEL_FATAL, description })
}

/// §5.2, §5.3, §6.2: the protected record of the fatal alert, under the
/// next sequence number of [`alert_epoch`]; None when there is no such
/// epoch or it cannot seal another record.
pub open spec fn alert_wire(ciphers: Ciphers, s: State, description: u8) -> Option<Seq<u8>> {
    match alert_epoch(s) {
        Some(epoch) => match crate::traffic::spec::send(seal_with(ciphers, epoch), epoch,
            crate::spec::CT_ALERT, fatal_alert(description), 0) {
            (_, Ok(record)) => Some(record),
            (_, Err(_)) => None,
        },
        None => None,
    }
}

/// §6, §6.1: the content of our close_notify.
pub open spec fn close_notify_alert() -> Seq<u8> {
    crate::spec::write_alert(crate::spec::Alert { level: crate::spec::LEVEL_WARNING, description: crate::spec::CLOSE_NOTIFY })
}

/// §5.2, §5.3, §6.1: our protected close_notify, under the next sequence
/// number of [`alert_epoch`]; None when there is no such epoch or it cannot
/// seal another record.
pub open spec fn close_wire(ciphers: Ciphers, s: State) -> Option<Seq<u8>> {
    match alert_epoch(s) {
        Some(epoch) => match crate::traffic::spec::send(seal_with(ciphers, epoch), epoch,
            crate::spec::CT_ALERT, close_notify_alert(), 0) {
            (_, Ok(record)) => Some(record),
            (_, Err(_)) => None,
        },
        None => None,
    }
}

/// §6.1: close during the flight: our close_notify goes out, if it can, and
/// every key is dropped.
pub open spec fn closing(ciphers: Ciphers, s: State) -> (Action, State) {
    (Action::Close(close_wire(ciphers, s)), closed())
}

/// §6.2: "Whenever an implementation encounters a fatal error condition, it
/// SHOULD send an appropriate fatal alert and MUST close the connection
/// without sending or receiving any additional data." The alert is sealed
/// from the state before the failure; then every key is dropped.
pub open spec fn fatal(ciphers: Ciphers, s: State, description: u8) -> (Action, State) {
    (Action::Fail(description, alert_wire(ciphers, s, description)), failed())
}

/// §6.1: the transport ended before close_notify. The peer has closed the
/// connection, so no alert is sent.
pub open spec fn die(description: u8) -> (Action, State) {
    (Action::Fail(description, None), failed())
}

/// §6, §6.2: a fatal alert from the peer ends the connection and is not
/// answered. (The connection's ciphers and state are parameters so that the
/// answer the RFC rules out could be written here; they are not used.)
pub open spec fn receive_fatal_alert(_ciphers: Ciphers, _s: State, description: u8) -> (Action, State) {
    (Action::PeerAlert(description), failed())
}

/// Drop every secret and partial input after a fatal local or peer error.
pub open spec fn failed() -> State {
    State {
        mode: Mode::Failed,
        auth: None,
        handshake_sender: None,
        handshake_receiver: None,
        master: seq![],
        client_application_secret: seq![],
        server_application_secret: seq![],
        reassembly: crate::spec::reasm_new(),
        framing: seq![],
        ccs_pending: false,
        pending_flight: seq![],
    }
}

/// Drop every secret and partial input after transport closure.
pub open spec fn closed() -> State {
    State { mode: Mode::Closed, ..failed() }
}
} // verus!
