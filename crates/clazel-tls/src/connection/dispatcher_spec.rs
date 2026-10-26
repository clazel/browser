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
//!   partial input. No production transport, cryptography, X.509 validation,
//!   post-handshake messages, or secret-erasure guarantee is modelled here.
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
    /// Client-handshake encryption function.
    pub handshake_seal: crate::traffic::contract::Seal3,
    /// Server-handshake authentication function.
    pub handshake_open: crate::traffic::contract::Open3,
    /// Client-application encryption function.
    pub application_seal: crate::traffic::contract::Seal3,
    /// Server-application authentication function.
    pub application_open: crate::traffic::contract::Open3,
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

/// Whether all traffic epochs and authentication state have been discarded.
pub open spec fn no_live_secrets(s: State) -> bool {
    s.auth is None && s.handshake_sender is None && s.handshake_receiver is None
        && s.application_sender is None && s.application_receiver is None && s.master.len() == 0
}

/// Lifecycle, bounds, and key-phase invariants for the initial connection.
pub open spec fn wf(s: State) -> bool {
    s.framing.len() <= super::framing_spec::MAX_BUFFER
        && s.reassembly.buf.len() < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY
        && match s.mode {
            Mode::Handshake => s.auth is Some && s.handshake_sender is Some
                && s.handshake_receiver is Some && s.application_sender is None
                && s.application_receiver is None && s.master.len() == 32
                && s.pending_flight.len() == 0
                && match s.auth { Some(a) => a.phase != crate::auth::spec::Phase::SendFinished,
                    None => false },
            Mode::AwaitClientFlight => s.auth is Some && s.handshake_sender is Some
                && s.handshake_receiver is Some && s.application_sender is None
                && s.application_receiver is None && s.master.len() == 32
                && s.pending_flight.len() > 0 && !s.ccs_pending
                && crate::spec::at_message_boundary(s.reassembly)
                && match s.auth { Some(a) => a.phase == crate::auth::spec::Phase::SendFinished,
                    None => false },
            Mode::Ready => s.auth is Some && s.handshake_sender is None
                && s.handshake_receiver is None && s.application_sender is Some
                && s.application_receiver is Some && s.master.len() == 0
                && s.pending_flight.len() == 0 && !s.ccs_pending
                && crate::spec::at_message_boundary(s.reassembly)
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
        application_sender: None,
        application_receiver: None,
        master: h.3,
        reassembly: crate::spec::reasm_new(),
        framing: seq![],
        ccs_pending,
        pending_flight: seq![],
    }
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
