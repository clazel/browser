//! RFC 8446 (August 2018) §4.1.2–§4.1.4, §5, §5.1 and Appendix D.4:
//! action-driven client bootstrap through the final ServerHello.
//! Source: <https://www.rfc-editor.org/rfc/rfc8446#section-4.1.2>.
//!
//! Modelling choices:
//! - The caller's transport acknowledgement is an explicit input and must
//!   equal the exact emitted wire flight before another peer record is read.
//! - Record framing and handshake reassembly remain the existing verified
//!   components; this model consumes their complete record/message events.
//! - The existing Hello controller remains the sole owner of negotiation,
//!   retry-cookie validation and transcript updates. This state only gates
//!   when its result may be consumed or sent.
//! - A nonempty legacy session ID requests compatibility mode. For an HRR,
//!   the client dummy CCS is prefixed to the CH2 flight as Appendix D.4 allows.
//!   Without HRR, the later protected-handshake driver owns that CCS.
//! - Authentication, key derivation, socket I/O, early data and PSK are outside
//!   this bootstrap model.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// Bootstrap state, including the send acknowledgement gate.
#[derive(PartialEq, Eq)]
pub enum Mode {
    /// Initial ClientHello is awaiting an exact transport-send acknowledgement.
    AwaitClientHelloSend,
    /// Acknowledged ClientHello; waiting for one server Hello response.
    AwaitServerHello,
    /// Retry ClientHello2 is awaiting an exact send acknowledgement.
    AwaitClientHello2Send,
    /// Final ServerHello was accepted and can be handed to the next layer.
    Established,
    /// A protocol or transport error ended bootstrap.
    Failed,
    /// The peer closed before the final ServerHello.
    Closed,
}

/// One caller-visible bootstrap effect.
pub enum Action {
    /// More input or an accepted compatibility record without another effect.
    None,
    /// Exact plaintext wire flight that must be acknowledged before input.
    Send(Seq<u8>),
    /// Accepted parameters/transcript/share for the existing key-agreement join.
    Established(super::client_spec::Config, crate::transcript::spec::State, Seq<u8>),
    /// A nonfatal peer alert was received.
    Alert(u8),
    /// Bootstrap failed with a TLS alert description.
    Fail(u8),
    /// The peer closed before bootstrap completed.
    Close,
}

/// Parsed events supplied by the existing record/reassembly layers.
pub enum PeerEvent {
    /// Valid RFC 8446 dummy CCS record.
    Ccs,
    /// A TLSPlaintext handshake fragment; reassembly follows RFC 8446 §5.1.
    HandshakeFragment(Seq<u8>),
    /// An alert record decoded by the existing reassembler.
    Alert(u8, u8),
    /// Record, framing, or handshake-message parser rejected the input.
    Error(u8),
    /// Transport reached EOF before a complete handshake response.
    Eof,
}

/// The state needed to gate the pre-ServerHello client lifecycle.
pub struct State {
    /// Current bootstrap phase.
    pub mode: Mode,
    /// Existing negotiation controller; absent only after completion/terminality.
    pub hello: Option<super::client_spec::State>,
    /// The exact wire bytes awaiting transport acknowledgement.
    pub pending_flight: Seq<u8>,
    /// Whether Appendix D.4 compatibility was requested by the ClientHello.
    pub compatibility: bool,
    /// Partial handshake-message bytes retained by the existing reassembly model.
    pub reassembly: crate::spec::Reasm,
}

/// Bootstrap state is well-formed and does not retain live negotiation state
/// after success or terminal failure.
pub open spec fn wf(s: State) -> bool {
    (match s.mode {
        Mode::AwaitClientHelloSend | Mode::AwaitServerHello | Mode::AwaitClientHello2Send =>
            s.hello is Some,
        Mode::Established | Mode::Failed | Mode::Closed => s.hello is None,
    })
    && (match s.mode {
        Mode::AwaitClientHelloSend | Mode::AwaitClientHello2Send => s.pending_flight.len() > 0,
        _ => s.pending_flight.len() == 0,
    })
    && match s.hello {
        Some(h) => super::client_spec::wf(h)
            && s.compatibility == (h.config.session_id.len() > 0)
            && match s.mode {
                Mode::AwaitClientHelloSend | Mode::AwaitServerHello =>
                    h.transcript.phase == crate::transcript::spec::Phase::FirstServerHello,
                Mode::AwaitClientHello2Send =>
                    h.transcript.phase == crate::transcript::spec::Phase::SecondServerHello,
                _ => false,
            },
        None => true,
    }
    && s.reassembly.buf.len() < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY
}

/// Wrap one handshake flight in a TLSPlaintext record, RFC 8446 §5.1.
pub open spec fn handshake_record(flight: Seq<u8>) -> Seq<u8> {
    crate::spec::write_plaintext(crate::spec::CT_HANDSHAKE, 0x0303, flight)
}

/// RFC 8446 §4.1.2 and §5.1: build the ClientHello and emit its exact record.
pub open spec fn start(c: super::client_spec::Config) -> Result<(State, Action), u8> {
    match super::client_spec::start(c) {
        Err(alert) => Err(alert),
        Ok((hello, flight)) => {
            let wire = handshake_record(flight);
            Ok((State {
                mode: Mode::AwaitClientHelloSend,
                hello: Some(hello),
                pending_flight: wire,
                compatibility: c.session_id.len() > 0,
                reassembly: crate::spec::reasm_new(),
            }, Action::Send(wire)))
        },
    }
}

/// Exact-send acknowledgement opens the receive gate for the matching flight.
pub open spec fn acknowledge(s: State, sent: Seq<u8>) -> (State, Action) {
    if !wf(s) { (State { mode: Mode::Failed, hello: None, pending_flight: seq![],
        compatibility: s.compatibility, reassembly: s.reassembly }, Action::Fail(crate::spec::INTERNAL_ERROR)) }
    else if s.mode == Mode::AwaitClientHelloSend && sent == s.pending_flight {
        (State { mode: Mode::AwaitServerHello, hello: s.hello,
            pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly }, Action::None)
    } else if s.mode == Mode::AwaitClientHello2Send && sent == s.pending_flight {
        (State { mode: Mode::AwaitServerHello, hello: s.hello,
            pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly }, Action::None)
    } else {
        (State { mode: Mode::Failed, hello: None, pending_flight: seq![],
            compatibility: s.compatibility, reassembly: s.reassembly }, Action::Fail(crate::spec::INTERNAL_ERROR))
    }
}

/// Appendix D.4's one-byte dummy CCS record, placed immediately before CH2.
pub open spec fn compatibility_ccs() -> Seq<u8> {
    seq![20u8, 3u8, 3u8, 0u8, 1u8, 1u8]
}

/// Process one complete peer event after the prior client flight was acked.
/// The existing Hello controller alone validates and applies ServerHello/HRR.
pub open spec fn receive(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, event: PeerEvent)
    -> (State, Action)
    recommends wf(s), s.mode == Mode::AwaitServerHello,
{
    match event {
        PeerEvent::Ccs => match crate::spec::feed_ccs(s.reassembly) {
            crate::spec::Res::Ok((_, reassembly)) =>
                (State { mode: s.mode, hello: s.hello, pending_flight: s.pending_flight,
                    compatibility: s.compatibility, reassembly }, Action::None),
            crate::spec::Res::Err(error) => (State { mode: Mode::Failed, hello: None,
                pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
                Action::Fail(crate::spec::alert_of(error))),
        },
        PeerEvent::Error(alert) => (State { mode: Mode::Failed, hello: None,
            pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly }, Action::Fail(alert)),
        PeerEvent::Eof => (State { mode: Mode::Failed, hello: None,
            pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
            Action::Fail(crate::spec::INTERNAL_ERROR)),
        PeerEvent::Alert(level, description) => {
            match crate::spec::feed_record(s.reassembly,
                crate::spec::Record { ctype: crate::spec::CT_ALERT, fragment: seq![level, description] }) {
                crate::spec::Res::Err(error) => (State { mode: Mode::Failed, hello: None,
                    pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
                    Action::Fail(crate::spec::alert_of(error))),
                crate::spec::Res::Ok((_, reassembly)) => {
                    if description == crate::spec::CLOSE_NOTIFY {
                        (State { mode: Mode::Closed, hello: None, pending_flight: seq![],
                            compatibility: s.compatibility, reassembly }, Action::Close)
                    } else {
                        (State { mode: Mode::Failed, hello: None, pending_flight: seq![],
                            compatibility: s.compatibility, reassembly }, Action::Alert(description))
                    }
                },
            }
        },
        PeerEvent::HandshakeFragment(fragment) => {
            match crate::spec::feed_record(s.reassembly,
                crate::spec::Record { ctype: crate::spec::CT_HANDSHAKE, fragment }) {
                crate::spec::Res::Err(error) => (State { mode: Mode::Failed, hello: None,
                    pending_flight: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
                    Action::Fail(crate::spec::alert_of(error))),
                crate::spec::Res::Ok((crate::spec::Event::Messages(messages), reassembly)) => {
                    if messages.len() == 0 {
                        (State { mode: s.mode, hello: s.hello, pending_flight: s.pending_flight,
                            compatibility: s.compatibility, reassembly }, Action::None)
                    } else if messages.len() != 1 || reassembly.buf.len() != 0 {
                        (State { mode: Mode::Failed, hello: None, pending_flight: seq![],
                            compatibility: s.compatibility, reassembly }, Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
                    } else {
                        let message = messages[0];
                        if message.len() < crate::spec::HANDSHAKE_HEADER
                            || message[0] != crate::spec::HS_SERVER_HELLO {
                            (State { mode: Mode::Failed, hello: None, pending_flight: seq![],
                                compatibility: s.compatibility, reassembly }, Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
                        } else {
                            let body = message.skip(crate::spec::HANDSHAKE_HEADER as int);
                            match s.hello {
                    None => (State { mode: Mode::Failed, hello: None,
                        pending_flight: seq![], compatibility: s.compatibility, reassembly },
                        Action::Fail(crate::spec::INTERNAL_ERROR)),
                    Some(hello) => match super::client_spec::receive(hash, hello, body) {
                        Err(alert) => (State { mode: Mode::Failed, hello: None,
                            pending_flight: seq![], compatibility: s.compatibility, reassembly }, Action::Fail(alert)),
                        Ok(super::client_spec::Outcome::Established(config, transcript, peer_key)) =>
                            (State { mode: Mode::Established, hello: None,
                                pending_flight: seq![], compatibility: s.compatibility, reassembly },
                                Action::Established(config, transcript, peer_key)),
                        Ok(super::client_spec::Outcome::Retry(next, flight)) => {
                            let hrr = if s.compatibility {
                                compatibility_ccs() + handshake_record(flight)
                            } else { handshake_record(flight) };
                            (State { mode: Mode::AwaitClientHello2Send, hello: Some(next),
                                pending_flight: hrr, compatibility: s.compatibility, reassembly }, Action::Send(hrr))
                        },
                    },
                            }
                        }
                    }
                },
                crate::spec::Res::Ok((_, reassembly)) => (State { mode: Mode::Failed,
                    hello: None, pending_flight: seq![], compatibility: s.compatibility, reassembly },
                    Action::Fail(crate::spec::UNEXPECTED_MESSAGE)),
            }
        },
    }
}
} // verus!
