//! RFC 8446 §4.1, §5, §6 and §7.3: the client as one machine, joining the
//! three that run in turn. Source:
//! <https://www.rfc-editor.org/rfc/rfc8446#section-2> (an RFC is immutable, so
//! there is no commit to pin).
//!
//! The stages are `hello::bootstrap` through the ServerHello, the dispatcher
//! (`dispatcher_spec`) for the server's flight, and the transducer
//! (`post_handshake_spec`) from then on. This module holds what the join
//! itself decides: what each machine's output becomes on the wire, and when
//! the next stage starts.
//!
//! Modelling choices:
//! 1. **The stage is the state.** [`Stage`] holds the abstract state of the
//!    machine that is running and nothing else. A machine that has handed over
//!    is gone, with its keys.
//! 2. **Every send is acknowledged at once.** `Bootstrap` and the dispatcher
//!    wait for the exact bytes they emitted. This machine hands them to its
//!    caller in the same step, so it acknowledges in the same step (the
//!    transport is assumed to accept them, as `post_handshake_spec` choice 3).
//! 3. **One record per step**, as the machines take them. Buffering the rest
//!    of the input and resubmitting it is the caller's.
//! 4. **Plaintext alerts before the handshake keys.** `Bootstrap` puts no alert
//!    on the wire, so this machine writes the record ([`plaintext_alert`]):
//!    §6 and §5.1, an alert before keys are installed is a plaintext record.
//! 5. **Close.** The server's close_notify is answered with ours once the
//!    handshake has completed: §6.1 makes that a choice, and this client has
//!    nothing left to send when the server is done. [`close`] ends the write
//!    side.
//! 6. **A `Fail` after a `Send`** is reported as [`Origin::Sent`]. The one
//!    other record that can precede a `Fail` is a KeyUpdate whose next epoch
//!    could not start, which cannot happen for a 32-octet secret.
//! 7. RFC prose has no numbered algorithm steps; the comments cite sections.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {

/// Who raised a failure, and whether it went on the wire.
#[derive(PartialEq, Eq)]
pub enum Origin {
    /// The client detected it, and the fatal alert is the last record sent.
    Sent,
    /// The client detected it, and no alert could be sent.
    NotSent,
    /// The server sent this fatal alert. It is not answered.
    Peer,
    /// The transport closed before a close_notify (§6.1); nothing was sent.
    Truncated,
}

/// Where the connection is.
#[derive(PartialEq, Eq)]
pub enum Status {
    /// The handshake is running.
    Handshaking,
    /// The handshake completed.
    Open,
    /// Our close_notify has been sent; the server's has not arrived.
    Closing,
    /// Both close_notify alerts have been seen. Final.
    Closed,
    /// The connection failed, with this alert. Final.
    Failed(u8, Origin),
}

/// `Closed` or `Failed`.
pub open spec fn is_final(s: Status) -> bool { s is Closed || s is Failed }

/// The machine that is running, in its abstract state.
pub enum Stage {
    /// Through the ServerHello: its state and its framing buffer.
    Hello(crate::hello::bootstrap_spec::State, Seq<u8>),
    /// The server's protected flight.
    Flight(super::dispatcher_spec::State),
    /// Application traffic.
    App(super::post_handshake_spec::State),
    /// `Closed` or `Failed`: no machine holds a key.
    Ended,
}

/// One step's effect: octets to send, plaintext to deliver, and where the
/// machine is afterwards.
pub struct Step {
    /// Octets for the transport, in order.
    pub send: Seq<u8>,
    /// Plaintext from the server, in order.
    pub deliver: Seq<u8>,
    /// The machine that runs next.
    pub stage: Stage,
    /// Where the connection is.
    pub status: Status,
}

/// RFC 8446 §5.1, §6: a plaintext alert record. `legacy_record_version` is
/// 0x0303 (§5.1), and the fragment is the two octets of the alert.
pub open spec fn plaintext_alert(level: u8, description: u8) -> Seq<u8> {
    seq![crate::spec::CT_ALERT, 3u8, 3u8, 0u8, 2u8, level, description]
}

/// The records of `wires`, one after the other.
pub open spec fn concat(wires: Seq<Seq<u8>>) -> Seq<u8>
    decreases wires.len(),
{
    if wires.len() == 0 { seq![] } else { concat(wires.drop_last()) + wires.last() }
}

/// What a step that ended the transducer, or left it running, comes to.
/// `prefix` is what the step already sent and `deliver` what it delivered.
pub open spec fn settle(prefix: Seq<u8>, deliver: Seq<u8>, o: super::post_handshake_spec::Out,
    s: super::post_handshake_spec::State) -> Step
{
    let send = prefix + concat(o.wires);
    let ended = |status: Status| Step { send, deliver, stage: Stage::Ended, status };
    match o.end {
        super::post_handshake_spec::End::Continue => Step {
            send, deliver, stage: Stage::App(s),
            status: if s.phase == super::post_handshake_spec::Phase::WriteClosed { Status::Closing } else { Status::Open },
        },
        super::post_handshake_spec::End::Close => ended(Status::Closed),
        super::post_handshake_spec::End::Fail(a) =>
            ended(Status::Failed(a, if send.len() > 0 { Origin::Sent } else { Origin::NotSent })),
        super::post_handshake_spec::End::PeerAlert(a) => ended(Status::Failed(a, Origin::Peer)),
        // Choice 5 calls `close` here, which cannot report this.
        super::post_handshake_spec::End::PeerClosed =>
            ended(Status::Failed(crate::spec::INTERNAL_ERROR, Origin::NotSent)),
    }
}

/// What the transducer's output comes to: choice 5 answers the server's
/// close_notify with ours in the same step.
pub open spec fn carry_out(f: crate::traffic::spec::Cipher, o: super::post_handshake_spec::Out,
    s: super::post_handshake_spec::State) -> Step
{
    match o.end {
        super::post_handshake_spec::End::PeerClosed => {
            let r = super::post_handshake_spec::close(f, s);
            settle(concat(o.wires), o.delivered, r.0, r.1)
        },
        _ => settle(seq![], o.delivered, o, s),
    }
}

/// A failure the dispatcher reported: its sealed alert, if any, goes last.
pub open spec fn flight_failure(description: u8, wire: Option<Seq<u8>>) -> Step {
    match wire {
        Some(record) => Step { send: record, deliver: seq![], stage: Stage::Ended,
            status: Status::Failed(description, Origin::Sent) },
        None => Step { send: seq![], deliver: seq![], stage: Stage::Ended,
            status: Status::Failed(description, Origin::NotSent) },
    }
}

/// A local failure before the handshake keys: choice 4.
pub open spec fn hello_failure(description: u8) -> Step {
    Step { send: plaintext_alert(crate::spec::LEVEL_FATAL, description), deliver: seq![],
        stage: Stage::Ended, status: Status::Failed(description, Origin::Sent) }
}

/// §6.1: the server's close_notify during the Hello exchange, answered with
/// ours in plaintext.
pub open spec fn hello_closed() -> Step {
    Step { send: plaintext_alert(crate::spec::LEVEL_WARNING, crate::spec::CLOSE_NOTIFY), deliver: seq![],
        stage: Stage::Ended, status: Status::Closed }
}

/// §6.1: truncation, whichever machine reports it.
pub open spec fn truncated(description: u8) -> Step {
    Step { send: seq![], deliver: seq![], stage: Stage::Ended,
        status: Status::Failed(description, Origin::Truncated) }
}

/// The server's fatal alert, whichever machine reports it (§6: not answered).
pub open spec fn peer_failed(description: u8) -> Step {
    Step { send: seq![], deliver: seq![], stage: Stage::Ended,
        status: Status::Failed(description, Origin::Peer) }
}
} // verus!
