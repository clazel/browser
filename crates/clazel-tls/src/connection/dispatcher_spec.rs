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
//! - Terminal states retain no authentication secrets, traffic epochs, or
//!   partial input. NewSessionTicket bodies are parsed and discarded; ticket
//!   caching, PSK resumption, 0-RTT, and secret-erasure guarantees are not
//!   modelled. Production transport, cryptography, and X.509 validation are
//!   also outside this module.
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
    /// Application keys are installed and Auth permits delivery.
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
    /// Application keys installed after the client flight was acknowledged.
    Ready,
    /// Plaintext released only by Auth in the Ready phase.
    Deliver(Seq<u8>),
    /// A permitted unprotected compatibility CCS was dropped.
    Ignored,
    /// The peer closed its write direction with close_notify; local writes remain possible.
    PeerClosed,
    /// A nonfatal user_canceled alert was reported without changing TLS state.
    Cancelled,
    /// Local close_notify has been acknowledged; the receive direction remains open.
    WriteClosed,
    /// Fatal error; caller may send at most one alert and must terminate.
    Fail(u8),
    /// Both read and write directions have closed, or the active transport closed.
    Close,
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
    /// Client application send epoch, installed only after client-flight ack.
    pub application_sender: Option<crate::traffic::spec::State>,
    /// Server application receive epoch, installed only after client-flight ack.
    pub application_receiver: Option<crate::traffic::spec::State>,
    /// Application master secret, retained only until application epochs install.
    pub master: Seq<u8>,
    /// Current client application traffic secret for the send direction.
    pub client_application_secret: Seq<u8>,
    /// Current server application traffic secret for the receive direction.
    pub server_application_secret: Seq<u8>,
    /// Bytes of one incomplete handshake message.
    pub reassembly: crate::spec::Reasm,
    /// Consumed wire prefix for one record; never contains a following record.
    pub framing: Seq<u8>,
    /// Whether the dummy compatibility CCS remains due before the client flight.
    pub ccs_pending: bool,
    /// Exact protected client flight awaiting acknowledgement.
    pub pending_flight: Seq<u8>,
    /// Next client traffic secret awaiting exact KeyUpdate send acknowledgement.
    pub pending_update_secret: Seq<u8>,
    /// Exact protected KeyUpdate record awaiting send acknowledgement.
    pub pending_update_wire: Seq<u8>,
    /// Request bit carried by the pending KeyUpdate.
    pub pending_update_request: Option<u8>,
    /// Whether the pending update is the required response to a peer request.
    pub pending_update_is_response: bool,
    /// A received update_requested still requires a later KeyUpdate(0).
    pub response_due: bool,
    /// The peer's write side ended with close_notify.
    pub peer_write_closed: bool,
    /// Local write side ended after close_notify was acknowledged.
    pub local_write_closed: bool,
    /// Exact close_notify record awaiting send acknowledgement.
    pub pending_close_wire: Seq<u8>,
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

/// A handshake record flight has Finished as its last complete message.
pub open spec fn finished_is_last(messages: Seq<Seq<u8>>) -> bool {
    messages.len() > 0 && messages.last().len() >= crate::spec::HANDSHAKE_HEADER
        && messages.last()[0] == 20
}

/// RFC 8446 §4.6.1: recognize a fully parsed NewSessionTicket body inside its
/// handshake encoding. This profile discards tickets and never derives PSKs.
pub open spec fn valid_discarded_ticket(message: Seq<u8>) -> bool {
    match crate::spec::parse_handshake(message, crate::schedule::spec::HASH_LEN as nat) {
        crate::spec::Res::Ok(crate::spec::HsMsg::NewSessionTicket(_)) => true,
        _ => false,
    }
}

/// Whether all traffic epochs and authentication state have been discarded.
pub open spec fn no_live_secrets(s: State) -> bool {
    s.auth is None && s.handshake_sender is None && s.handshake_receiver is None
        && s.application_sender is None && s.application_receiver is None && s.master.len() == 0
        && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0
        && s.pending_update_secret.len() == 0 && s.pending_update_wire.len() == 0
        && s.pending_update_request is None && !s.pending_update_is_response && !s.response_due
        && s.pending_close_wire.len() == 0
}

/// Outward effects agree with the state transition that makes them safe.
pub open spec fn action_refines(action: Action, after: State) -> bool {
    match action {
        Action::Send(wire) => (after.mode == Mode::AwaitClientFlight && after.pending_flight == wire)
            || (after.mode == Mode::Ready && (after.pending_update_wire == wire
                || after.pending_close_wire == wire)),
        Action::Ready => after.mode == Mode::Ready,
        Action::Deliver(_) => after.mode == Mode::Ready,
        Action::Fail(_) => super::dispatcher_contract::terminal_ensures(after, Mode::Failed),
        Action::Close => super::dispatcher_contract::terminal_ensures(after, Mode::Closed),
        Action::PeerClosed => after.mode == Mode::Ready && after.peer_write_closed,
        Action::Cancelled => true,
        Action::WriteClosed => after.mode == Mode::Ready && after.local_write_closed,
        Action::None | Action::Ignored => true,
    }
}

/// Lifecycle, bounds, and key-phase invariants for the initial connection.
pub open spec fn wf(s: State) -> bool {
    // Runtime `resources_wf` carries the concrete Buffer/Reassembler bounds.
    match s.mode {
            Mode::Handshake => s.auth is Some && s.handshake_sender is Some
                && s.handshake_receiver is Some && s.application_sender is None
                && s.application_receiver is None && s.master.len() == 32
                && s.pending_flight.len() == 0
                && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0
                && s.pending_update_secret.len() == 0 && s.pending_update_wire.len() == 0
                && s.pending_update_request is None && !s.pending_update_is_response && !s.response_due
                && !s.peer_write_closed && !s.local_write_closed && s.pending_close_wire.len() == 0
                && s.auth is Some,
            Mode::AwaitClientFlight => s.auth is Some && s.handshake_sender is Some
                && s.handshake_receiver is Some && s.application_sender is None
                && s.application_receiver is None && s.master.len() == 32
                && s.pending_flight.len() > 0 && !s.ccs_pending
                && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0
                && s.pending_update_secret.len() == 0 && s.pending_update_wire.len() == 0
                && s.pending_update_request is None && !s.pending_update_is_response && !s.response_due
                && !s.peer_write_closed && !s.local_write_closed && s.pending_close_wire.len() == 0
                && crate::spec::at_message_boundary(s.reassembly)
                && s.framing.len() == 0
                && match s.auth { Some(a) => a.phase == crate::auth::spec::Phase::SendFinished,
                    None => false },
            Mode::Ready => s.auth is Some && s.handshake_sender is None
                && s.handshake_receiver is None && s.application_sender is Some
                && s.application_receiver is Some && s.master.len() == 0
                && match s.application_sender { Some(epoch) => !epoch.failed, None => false }
                && match s.application_receiver { Some(epoch) => !epoch.failed, None => false }
                && s.pending_flight.len() == 0 && !s.ccs_pending
                && s.client_application_secret.len() == 32 && s.server_application_secret.len() == 32
                && match s.pending_update_request {
                    Some(request) => request <= 1 && s.pending_update_secret.len() == 32
                        && (!s.pending_update_is_response || request == 0),
                    None => s.pending_update_secret.len() == 0 && s.pending_update_wire.len() == 0
                        && !s.pending_update_is_response,
                }
                && (s.pending_close_wire.len() == 0 || !s.local_write_closed)
                && (!s.local_write_closed || s.pending_close_wire.len() == 0)
                && match s.auth { Some(a) => a.phase == crate::auth::spec::Phase::Ready,
                    None => false },
            Mode::Failed | Mode::Closed => no_live_secrets(s)
                && s.reassembly.buf.len() == 0 && s.framing.len() == 0
                && s.pending_flight.len() == 0 && !s.ccs_pending
                && s.client_application_secret.len() == 0 && s.server_application_secret.len() == 0
                && s.pending_update_secret.len() == 0 && s.pending_update_wire.len() == 0
                && s.pending_update_request is None && !s.pending_update_is_response && !s.response_due
                && !s.peer_write_closed && !s.local_write_closed && s.pending_close_wire.len() == 0,
        }
}

/// Start from the validated Hello/handshake-key handoff with empty buffers.
pub open spec fn start(h: crate::traffic::handshake_spec::Handoff, ccs_pending: bool) -> State {
    State {
        mode: Mode::Handshake,
        auth: Some(h.0),
        handshake_sender: Some(h.1),
        handshake_receiver: Some(h.2),
        application_sender: None,
        application_receiver: None,
        master: h.3,
        client_application_secret: seq![],
        server_application_secret: seq![],
        reassembly: crate::spec::reasm_new(),
        framing: seq![],
        ccs_pending,
        pending_flight: seq![],
        pending_update_secret: seq![],
        pending_update_wire: seq![],
        pending_update_request: None,
        pending_update_is_response: false,
        response_due: false,
        peer_write_closed: false,
        local_write_closed: false,
        pending_close_wire: seq![],
    }
}

/// Protect a KeyUpdate with the current client epoch. The epoch changes only
/// after the caller acknowledges the exact returned wire bytes.
pub open spec fn prepare_key_update(c: crate::schedule::spec::Crypto,
    ciphers: Ciphers, s: State, request: u8, is_response: bool) -> State
{
    if request > 1 || (is_response && request != 0) || (is_response != s.response_due) { s }
    else { match (s.application_sender, s.pending_update_request) {
        (Some(sender), None) => {
            let body = crate::spec::write_key_update(request);
            let message = crate::spec::write_handshake(crate::spec::HS_KEY_UPDATE, body);
            let next_secret = crate::schedule::spec::next_traffic_secret(c, s.client_application_secret);
            let seal = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| (ciphers.seal)(sender.key, n, ad, p);
            match crate::traffic::spec::send(seal, sender,
                crate::spec::CT_HANDSHAKE, message, 0) {
                (sender_after, Ok(wire)) => State {
                    application_sender: Some(sender_after),
                    pending_update_secret: next_secret,
                    pending_update_wire: wire,
                    pending_update_request: Some(request),
                    pending_update_is_response: is_response,
                    response_due: if is_response { false } else { s.response_due },
                    ..s
                },
                _ => failed(),
            }
        },
        _ => s,
    } }
}

/// Receive a syntactically valid KeyUpdate under the old receive epoch and
/// install the next server secret before processing another record.
pub open spec fn receive_key_update(c: crate::schedule::spec::Crypto, s: State,
    request: u8) -> State
{
    let next_secret = crate::schedule::spec::next_traffic_secret(c, s.server_application_secret);
    match crate::traffic::spec::start(c, next_secret) {
        Ok(epoch) => State {
            application_receiver: Some(epoch),
            server_application_secret: next_secret,
            response_due: s.response_due || request == 1,
            ..s
        },
        // A derived secret that cannot form a new epoch must not leave a
        // next-secret/old-key mismatch in the model.
        Err(_) => failed(),
    }
}

/// Acknowledging a protected KeyUpdate installs its next send epoch at
/// sequence zero; it does not modify the independently advancing receive side.
pub open spec fn acknowledge_key_update(c: crate::schedule::spec::Crypto,
    s: State, acknowledgement: Seq<u8>) -> State
{
    match s.pending_update_request {
        Some(_) if acknowledgement == s.pending_update_wire =>
            match crate::traffic::spec::start(c, s.pending_update_secret) {
                Ok(epoch) => State {
                    application_sender: Some(epoch),
                    client_application_secret: s.pending_update_secret,
                    pending_update_secret: seq![],
                    pending_update_wire: seq![],
                    pending_update_request: None,
                    pending_update_is_response: false,
                    ..s
                },
                // Never advance the traffic secret while retaining old keys.
                Err(_) => failed(),
            },
        _ => s,
    }
}

/// Complete a send acknowledgement and, if a peer request arrived while the
/// previous update was in flight, immediately queue the required KeyUpdate(0).
pub open spec fn acknowledge_key_update_and_respond(c: crate::schedule::spec::Crypto,
    ciphers: Ciphers, s: State, acknowledgement: Seq<u8>) -> State
{
    let acknowledged = acknowledge_key_update(c, s, acknowledgement);
    if acknowledged.response_due {
        prepare_key_update(c, ciphers, acknowledged, 0, true)
    } else {
        acknowledged
    }
}

/// A peer request rotates the receive epoch immediately. If no local update is
/// outstanding, queue its mandatory unrequested response before app data.
pub open spec fn receive_key_update_and_respond(c: crate::schedule::spec::Crypto,
    ciphers: Ciphers, s: State, request: u8) -> State
{
    let received = receive_key_update(c, s, request);
    if received.response_due && received.pending_update_request is None {
        prepare_key_update(c, ciphers, received, 0, true)
    } else {
        received
    }
}

/// Receive a close_notify as an orderly close of only the peer's write side.
/// The local send epoch and pending sends are preserved (§6.1).
pub open spec fn receive_close_notify(s: State) -> State {
    if s.mode != Mode::Ready || s.peer_write_closed { s }
    else if s.local_write_closed { closed() }
    else { State { peer_write_closed: true, ..s } }
}

/// Protect a local close_notify under the active application epoch. It waits
/// until any KeyUpdate and mandatory response have been acknowledged.
pub open spec fn prepare_close_notify(c: crate::schedule::spec::Crypto,
    ciphers: Ciphers, s: State) -> State {
    if s.mode != Mode::Ready || s.local_write_closed || s.pending_close_wire.len() > 0
        || s.pending_update_request is Some || s.response_due { s }
    else { match s.application_sender {
        Some(sender) => {
            let close = crate::spec::write_alert(crate::spec::Alert {
                level: crate::spec::LEVEL_WARNING,
                description: crate::spec::CLOSE_NOTIFY,
            });
            let seal = |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| (ciphers.seal)(sender.key, n, ad, p);
            match crate::traffic::spec::send(seal, sender, crate::spec::CT_ALERT, close, 0) {
                (sender_after, Ok(wire)) => State {
                    application_sender: Some(sender_after),
                    pending_close_wire: wire,
                    ..s
                },
                _ => failed(),
            }
        },
        None => failed(),
    } }
}

/// A close_notify flight closes the local write side only after its exact
/// protected bytes have been acknowledged by the transport.
pub open spec fn acknowledge_close_notify(s: State, acknowledgement: Seq<u8>) -> State {
    if s.pending_close_wire.len() == 0 || acknowledgement != s.pending_close_wire { failed() }
    else if s.peer_write_closed { closed() }
    else { State { local_write_closed: true, pending_close_wire: seq![], ..s } }
}

/// Drop every secret and partial input after a fatal local or peer error.
pub open spec fn failed() -> State {
    State {
        mode: Mode::Failed,
        auth: None,
        handshake_sender: None,
        handshake_receiver: None,
        application_sender: None,
        application_receiver: None,
        master: seq![],
        client_application_secret: seq![],
        server_application_secret: seq![],
        reassembly: crate::spec::reasm_new(),
        framing: seq![],
        ccs_pending: false,
        pending_flight: seq![],
        pending_update_secret: seq![],
        pending_update_wire: seq![],
        pending_update_request: None,
        pending_update_is_response: false,
        response_due: false,
        peer_write_closed: false,
        local_write_closed: false,
        pending_close_wire: seq![],
    }
}

/// Drop every secret and partial input after transport closure.
pub open spec fn closed() -> State {
    State { mode: Mode::Closed, ..failed() }
}
} // verus!
