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
//! - A valid unencrypted CCS is dropped only at a handshake message boundary
//!   and is fatal (unexpected_message) inside a fragmented ServerHello or HRR:
//!   §5 and §5.1 conflict there; see docs/ERRATA.md. The connection
//!   dispatcher applies the same rule to protected handshake messages.
//! - RFC 8446 §5.1: "Handshake messages MAY be coalesced into a single
//!   TLSPlaintext record", and the alignment rule ("all messages immediately
//!   preceding a key change align with a record boundary") does not cover a
//!   HelloRetryRequest, which precedes no key change. So the messages that
//!   follow an accepted HelloRetryRequest in its record are kept
//!   ([`State::retained`]), with the unfinished one's bytes in the
//!   reassembly state, and are processed, in order, once ClientHello2 is
//!   acknowledged: the acknowledgement gate means nothing the server sent is
//!   consumed before the flight that answers what came before it. After a
//!   ServerHello, which precedes the handshake key change, any following byte
//!   is `unexpected_message`, after the ServerHello's own checks.
//! - RFC 8446 §6.1: a received user_canceled is not an error alert and
//!   closes nothing (it "SHOULD be followed by a close_notify"): bootstrap
//!   goes on reading, as the dispatcher and the post-handshake transducer do.
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
    /// The peer's error alert (§6: any alert but close_notify and
    /// user_canceled) ended bootstrap. A user_canceled is not one (§6.1):
    /// it changes nothing, and reading goes on.
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

/// Result of consuming one caller-owned byte prefix.
pub struct Feed {
    /// Number of bytes copied into the one-record framer.
    pub consumed: nat,
    /// Resulting lifecycle state.
    pub state: State,
    /// Bytes retained by the one-record plaintext framer.
    pub framing: Seq<u8>,
    /// Caller-visible effect.
    pub action: Action,
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
    /// §5.1: the complete handshake messages that followed an accepted
    /// HelloRetryRequest in its record, in order, processed once ClientHello2
    /// is acknowledged (empty in every other mode).
    pub retained: Seq<Seq<u8>>,
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
                Mode::AwaitClientHelloSend =>
                    h.transcript.phase == crate::transcript::spec::Phase::FirstServerHello,
                Mode::AwaitServerHello =>
                    h.transcript.phase == crate::transcript::spec::Phase::FirstServerHello
                        || h.transcript.phase == crate::transcript::spec::Phase::SecondServerHello,
                Mode::AwaitClientHello2Send =>
                    h.transcript.phase == crate::transcript::spec::Phase::SecondServerHello,
                _ => false,
            },
        None => true,
    }
    && s.reassembly.buf.len() < crate::spec::HANDSHAKE_HEADER + crate::spec::MAX_HANDSHAKE_BODY
    && (s.mode != Mode::AwaitClientHello2Send ==> s.retained.len() == 0)
}

/// Wrap one handshake flight in a TLSPlaintext record, RFC 8446 §5.1: the
/// record of the second ClientHello, whose version "MUST" be 0x0303 ("a
/// record containing a second ClientHello or a ServerHello MUST have
/// version 0x0303").
pub open spec fn handshake_record(flight: Seq<u8>) -> Seq<u8> {
    crate::spec::write_plaintext(crate::spec::CT_HANDSHAKE, 0x0303, flight)
}

/// The record of the initial ClientHello, RFC 8446 §5.1: "a record
/// containing an initial ClientHello SHOULD have version 0x0301 (reflecting
/// TLS 1.0)" (and `legacy_record_version`: "MUST be set to 0x0303 for all
/// records ... other than an initial ClientHello ..., where it MAY also be
/// 0x0301"). The SHOULD is followed.
pub open spec fn initial_record(flight: Seq<u8>) -> Seq<u8> {
    crate::spec::write_plaintext(crate::spec::CT_HANDSHAKE, 0x0301, flight)
}

/// RFC 8446 §4.1.2 and §5.1: build the ClientHello and emit its exact record.
pub open spec fn start(c: super::client_spec::Config) -> Result<(State, Action), u8> {
    match super::client_spec::start(c) {
        Err(alert) => Err(alert),
        Ok((hello, flight)) => {
            let wire = initial_record(flight);
            Ok((State {
                mode: Mode::AwaitClientHelloSend,
                hello: Some(hello),
                pending_flight: wire,
                retained: seq![],
                compatibility: c.session_id.len() > 0,
                reassembly: crate::spec::reasm_new(),
            }, Action::Send(wire)))
        },
    }
}

/// Exact-send acknowledgement opens the receive gate for the matching flight.
/// After ClientHello2, the messages retained from the HelloRetryRequest's
/// record are processed then, in order ([`receive_messages`]), as if they had
/// just arrived: §5.1 lets them share its record.
pub open spec fn acknowledge(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, sent: Seq<u8>) -> (State, Action) {
    if !wf(s) { (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
        compatibility: s.compatibility, reassembly: s.reassembly }, Action::Fail(crate::spec::INTERNAL_ERROR)) }
    else if s.mode == Mode::AwaitClientHelloSend && sent == s.pending_flight {
        (State { mode: Mode::AwaitServerHello, hello: s.hello,
            pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly: s.reassembly }, Action::None)
    } else if s.mode == Mode::AwaitClientHello2Send && sent == s.pending_flight {
        receive_messages(hash, State { mode: Mode::AwaitServerHello, hello: s.hello,
            pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
            s.retained)
    } else {
        (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
            compatibility: s.compatibility, reassembly: s.reassembly }, Action::Fail(crate::spec::INTERNAL_ERROR))
    }
}

/// Appendix D.4's one-byte dummy CCS record, placed immediately before CH2.
pub open spec fn compatibility_ccs() -> Seq<u8> {
    seq![20u8, 3u8, 3u8, 0u8, 1u8, 1u8]
}

/// RFC 8446 §4 and §5.1: the complete handshake messages a record gave (or
/// that were retained after a HelloRetryRequest), in order. `s` already holds
/// the reassembly state after that record: the bytes of an unfinished message.
/// The first message is the server's Hello; what may follow it depends on
/// what it was.
pub open spec fn receive_messages(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, messages: Seq<Seq<u8>>)
    -> (State, Action)
{
    if messages.len() == 0 {
        (s, Action::None)
    } else {
        let message = messages[0];
        let reassembly = s.reassembly;
        if message.len() < crate::spec::HANDSHAKE_HEADER || message[0] != crate::spec::HS_SERVER_HELLO {
            // §4.1.3, Appendix A.1: in WAIT_SH only a ServerHello (or a
            // HelloRetryRequest, which has its type) may arrive.
            (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                compatibility: s.compatibility, reassembly }, Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
        } else {
            let body = message.skip(crate::spec::HANDSHAKE_HEADER as int);
            match s.hello {
                None => (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                    compatibility: s.compatibility, reassembly }, Action::Fail(crate::spec::INTERNAL_ERROR)),
                Some(hello) => match super::client_spec::receive(hash, hello, body) {
                    Err(alert) => (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                        compatibility: s.compatibility, reassembly }, Action::Fail(alert)),
                    Ok(super::client_spec::Outcome::Established(config, transcript, peer_key)) =>
                        if messages.len() != 1 || reassembly.buf.len() != 0 {
                            // §5.1: "Handshake messages MUST NOT span key changes.
                            // Implementations MUST verify that all messages
                            // immediately preceding a key change align with a
                            // record boundary; if not, then they MUST terminate the
                            // connection with an "unexpected_message" alert." The
                            // handshake keys follow the ServerHello.
                            (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                                compatibility: s.compatibility, reassembly }, Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
                        } else {
                            (State { mode: Mode::Established, hello: None, pending_flight: seq![], retained: seq![],
                                compatibility: s.compatibility, reassembly }, Action::Established(config, transcript, peer_key))
                        },
                    // §5.1: a HelloRetryRequest precedes no key change, so the
                    // messages after it in its record are kept for after
                    // ClientHello2 ([`acknowledge`]).
                    Ok(super::client_spec::Outcome::Retry(next, flight)) => {
                        let hrr = if s.compatibility {
                            compatibility_ccs() + handshake_record(flight)
                        } else { handshake_record(flight) };
                        (State { mode: Mode::AwaitClientHello2Send, hello: Some(next), pending_flight: hrr,
                            retained: messages.skip(1), compatibility: s.compatibility, reassembly }, Action::Send(hrr))
                    },
                },
            }
        }
    }
}

/// Process one complete peer event after the prior client flight was acked.
/// The existing Hello controller alone validates and applies ServerHello/HRR.
pub open spec fn receive(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, event: PeerEvent)
    -> (State, Action)
    recommends wf(s), s.mode == Mode::AwaitServerHello,
{
    match event {
        // RFC 8446 §5 says to drop a valid unencrypted CCS "at any time after
        // the first ClientHello message has been sent or received and before
        // the peer's Finished message has been received", but §5.1 says
        // handshake messages "MUST NOT be interleaved with other record types".
        // We drop it only at a handshake message boundary; inside a
        // fragmented message it is fatal (docs/ERRATA.md, RFC 8446 §5).
        PeerEvent::Ccs => if crate::spec::at_message_boundary(s.reassembly) {
            (s, Action::None)
        } else {
            (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                compatibility: s.compatibility, reassembly: s.reassembly },
                Action::Fail(crate::spec::UNEXPECTED_MESSAGE))
        },
        PeerEvent::Error(alert) => (State { mode: Mode::Failed, hello: None,
            pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly: s.reassembly }, Action::Fail(alert)),
        PeerEvent::Eof => (State { mode: Mode::Failed, hello: None,
            pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
            Action::Fail(crate::spec::INTERNAL_ERROR)),
        PeerEvent::Alert(level, description) => {
            match crate::spec::feed_record(s.reassembly,
                crate::spec::Record { ctype: crate::spec::CT_ALERT, fragment: seq![level, description] }) {
                crate::spec::Res::Err(error) => (State { mode: Mode::Failed, hello: None,
                    pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
                    Action::Fail(crate::spec::alert_of(error))),
                crate::spec::Res::Ok((_, reassembly)) => {
                    if description == crate::spec::CLOSE_NOTIFY {
                        (State { mode: Mode::Closed, hello: None, pending_flight: seq![], retained: seq![],
                            compatibility: s.compatibility, reassembly }, Action::Close)
                    } else if description == crate::spec::USER_CANCELED {
                        // RFC 8446 §6.1: user_canceled "notifies the recipient that the
                        // sender is canceling the handshake" and "SHOULD be followed by a
                        // close_notify": it is not an error alert and closes nothing, so
                        // reading goes on until the close_notify.
                        (State { reassembly, ..s }, Action::None)
                    } else {
                        (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                            compatibility: s.compatibility, reassembly }, Action::Alert(description))
                    }
                },
            }
        },
        PeerEvent::HandshakeFragment(fragment) => {
            match crate::spec::feed_record(s.reassembly,
                crate::spec::Record { ctype: crate::spec::CT_HANDSHAKE, fragment }) {
                crate::spec::Res::Err(error) => (State { mode: Mode::Failed, hello: None,
                    pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly: s.reassembly },
                    Action::Fail(crate::spec::alert_of(error))),
                crate::spec::Res::Ok((crate::spec::Event::Messages(messages), reassembly)) =>
                    receive_messages(hash, State { reassembly, ..s }, messages),
                crate::spec::Res::Ok((_, reassembly)) => (State { mode: Mode::Failed,
                    hello: None, pending_flight: seq![], retained: seq![], compatibility: s.compatibility, reassembly },
                    Action::Fail(crate::spec::UNEXPECTED_MESSAGE)),
            }
        },
    }
}

/// RFC 8446 §5.1: consume only the first unprotected record, then reassemble
/// its handshake/alert event. Caller-owned suffix bytes remain unconsumed.
pub open spec fn feed(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State,
    framing: Seq<u8>, input: Seq<u8>) -> Feed
    recommends wf(s), crate::connection::framing_spec::wf_mode(framing, false),
{
    if s.mode != Mode::AwaitServerHello {
        Feed { consumed: 0, state: s, framing, action: Action::None }
    } else {
        let framed = crate::connection::framing_spec::feed_mode(framing, input, false);
        match framed.status {
            crate::connection::framing_spec::Status::Pending => Feed {
                consumed: framed.consumed, state: s, framing: framed.buffer, action: Action::None,
            },
            crate::connection::framing_spec::Status::Fail(alert) => Feed {
                consumed: framed.consumed,
                state: State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                    compatibility: s.compatibility, reassembly: s.reassembly },
                framing: framed.buffer, action: Action::Fail(alert),
            },
            crate::connection::framing_spec::Status::Complete => {
                match crate::spec::read_record(framed.buffer, false) {
                    crate::spec::Read::Done(frame, rest) => {
                        if rest.len() != 0 {
                            Feed { consumed: framed.consumed,
                                state: State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                                    compatibility: s.compatibility, reassembly: s.reassembly },
                                framing: seq![], action: Action::Fail(crate::spec::UNEXPECTED_MESSAGE) }
                        } else {
                            let received = match frame {
                                crate::spec::Frame::Ccs => receive(hash, s, PeerEvent::Ccs),
                                crate::spec::Frame::Plain(rec) if rec.ctype == crate::spec::CT_HANDSHAKE =>
                                    receive(hash, s, PeerEvent::HandshakeFragment(rec.fragment)),
                                crate::spec::Frame::Plain(rec) if rec.ctype == crate::spec::CT_ALERT =>
                                    match crate::spec::read_alert(rec.fragment) {
                                        Some(alert) => receive(hash, s,
                                            PeerEvent::Alert(alert.level, alert.description)),
                                        None => receive(hash, s, PeerEvent::Error(crate::spec::DECODE_ERROR)),
                                    },
                                _ => receive(hash, s, PeerEvent::Error(crate::spec::UNEXPECTED_MESSAGE)),
                            };
                            Feed { consumed: framed.consumed, state: received.0,
                                framing: seq![], action: received.1 }
                        }
                    },
                    crate::spec::Read::Fail(error) => Feed {
                        consumed: framed.consumed,
                        state: State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                            compatibility: s.compatibility, reassembly: s.reassembly },
                        framing: seq![], action: Action::Fail(crate::spec::alert_of(error)),
                    },
                    crate::spec::Read::NeedMore => Feed {
                        consumed: framed.consumed,
                        state: State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
                            compatibility: s.compatibility, reassembly: s.reassembly },
                        framing: seq![], action: Action::Fail(crate::spec::DECODE_ERROR),
                    },
                }
            },
        }
    }
}

/// EOF before a final ServerHello is truncation; terminal states stay terminal.
pub open spec fn eof(s: State) -> (State, Action) {
    if s.mode == Mode::Failed || s.mode == Mode::Closed || s.mode == Mode::Established {
        (s, Action::None)
    } else {
        (State { mode: Mode::Failed, hello: None, pending_flight: seq![], retained: seq![],
            compatibility: s.compatibility, reassembly: s.reassembly },
            Action::Fail(crate::spec::INTERNAL_ERROR))
    }
}
} // verus!
