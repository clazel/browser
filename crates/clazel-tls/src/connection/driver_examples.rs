//! Concrete examples of [`super::driver_spec`], one per rule of the join,
//! evaluated by Verus. The states are `post_handshake_examples`' fixtures.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// An output with no records and nothing delivered, ending as `end`.
pub open spec fn ending(end: super::post_handshake_spec::End) -> super::post_handshake_spec::Out {
    super::post_handshake_spec::Out { wires: seq![], delivered: seq![], end }
}

/// One record, ending as `end`.
pub open spec fn one_record(end: super::post_handshake_spec::End) -> super::post_handshake_spec::Out {
    super::post_handshake_spec::Out { wires: seq![seq![1u8, 2u8]], delivered: seq![], end }
}

/// The connection after our close_notify.
pub open spec fn write_closed() -> super::post_handshake_spec::State {
    super::post_handshake_spec::close(super::post_handshake_examples::cipher(), super::post_handshake_examples::ready()).1
}

/// The connection after the server's close_notify.
pub open spec fn read_closed() -> super::post_handshake_spec::State {
    super::post_handshake_examples::rec(21, seq![1u8, 0]).1
}

/// The result of a step, in the transducer's terms.
pub open spec fn carried(o: super::post_handshake_spec::Out, s: super::post_handshake_spec::State) -> super::driver_spec::Step {
    super::driver_spec::carry_out(super::post_handshake_examples::cipher(), o, s)
}

/// §5.1, §6: a plaintext alert is a record of type 21, version 0x0303 and
/// length 2.
pub proof fn lemma_plaintext_alert()
    ensures super::driver_spec::plaintext_alert(2, 40) == seq![21u8, 3, 3, 0, 2, 2, 40],
{
    assert(super::driver_spec::plaintext_alert(2, 40) == seq![21u8, 3, 3, 0, 2, 2, 40]) by (compute_only);
}

/// Records go out in order, whole.
pub proof fn lemma_concat()
    ensures super::driver_spec::concat(seq![seq![1u8, 2u8], seq![3u8]]) == seq![1u8, 2, 3],
{
    assert(super::driver_spec::concat(seq![seq![1u8, 2u8], seq![3u8]]) == seq![1u8, 2, 3]) by (compute_only);
}

/// A step that goes on leaves the transducer running: `Open`, and `Closing`
/// once our close_notify has gone.
pub proof fn lemma_continue_status()
    ensures
        carried(ending(super::post_handshake_spec::End::Continue), super::post_handshake_examples::ready()).status
            == super::driver_spec::Status::Open,
        carried(ending(super::post_handshake_spec::End::Continue), write_closed()).status
            == super::driver_spec::Status::Closing,
{
    assert(carried(ending(super::post_handshake_spec::End::Continue), super::post_handshake_examples::ready()).status
        == super::driver_spec::Status::Open) by (compute_only);
    assert(carried(ending(super::post_handshake_spec::End::Continue), write_closed()).status
        == super::driver_spec::Status::Closing) by (compute_only);
}

/// §6.1: the server's close_notify is answered with ours in the same step,
/// and the connection is closed.
pub proof fn lemma_peer_close_answered()
    ensures
        carried(ending(super::post_handshake_spec::End::PeerClosed), read_closed()).send.len() > 0,
        carried(ending(super::post_handshake_spec::End::PeerClosed), read_closed()).status
            == super::driver_spec::Status::Closed,
{
    assert(carried(ending(super::post_handshake_spec::End::PeerClosed), read_closed()).send.len() > 0) by (compute_only);
    assert(carried(ending(super::post_handshake_spec::End::PeerClosed), read_closed()).status
        == super::driver_spec::Status::Closed) by (compute_only);
}

/// §6: a failure with a record says the alert went out, one without says it
/// did not, and the server's alert is the server's.
pub proof fn lemma_origins()
    ensures
        carried(one_record(super::post_handshake_spec::End::Fail(40u8)), super::post_handshake_spec::failed()).status
            == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Sent),
        carried(ending(super::post_handshake_spec::End::Fail(40u8)), super::post_handshake_spec::failed()).status
            == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::NotSent),
        carried(ending(super::post_handshake_spec::End::PeerAlert(40u8)), super::post_handshake_spec::failed()).status
            == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Peer),
{
    assert(carried(one_record(super::post_handshake_spec::End::Fail(40u8)), super::post_handshake_spec::failed()).status
        == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Sent)) by (compute_only);
    assert(carried(ending(super::post_handshake_spec::End::Fail(40u8)), super::post_handshake_spec::failed()).status
        == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::NotSent)) by (compute_only);
    assert(carried(ending(super::post_handshake_spec::End::PeerAlert(40u8)), super::post_handshake_spec::failed()).status
        == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Peer)) by (compute_only);
}

/// §6.2: the dispatcher's sealed alert goes on the wire; without one, nothing.
pub proof fn lemma_flight_failure()
    ensures
        super::driver_spec::flight_failure(40, Some(seq![9u8])).send == seq![9u8],
        super::driver_spec::flight_failure(40, Some(seq![9u8])).status
            == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Sent),
        super::driver_spec::flight_failure(40, None).status
            == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::NotSent),
{
    assert(super::driver_spec::flight_failure(40, Some(seq![9u8])).send == seq![9u8]) by (compute_only);
    assert(super::driver_spec::flight_failure(40, Some(seq![9u8])).status
        == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Sent)) by (compute_only);
    assert(super::driver_spec::flight_failure(40, None).status
        == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::NotSent)) by (compute_only);
}

/// §6.1: a close during the flight sends what the dispatcher sealed.
pub proof fn lemma_flight_closed()
    ensures
        super::driver_spec::flight_closed(Some(seq![9u8])).send == seq![9u8],
        super::driver_spec::flight_closed(Some(seq![9u8])).status == super::driver_spec::Status::Closed,
{
    assert(super::driver_spec::flight_closed(Some(seq![9u8])).send == seq![9u8]) by (compute_only);
    assert(super::driver_spec::flight_closed(Some(seq![9u8])).status == super::driver_spec::Status::Closed) by (compute_only);
}

/// §6.1 and choice 4: before the handshake keys, a failure and a close are
/// plaintext alerts at their levels.
pub proof fn lemma_hello_alerts()
    ensures
        super::driver_spec::hello_failure(40).send == seq![21u8, 3, 3, 0, 2, 2, 40],
        super::driver_spec::hello_closed().send == seq![21u8, 3, 3, 0, 2, 1, 0],
        super::driver_spec::hello_closed().status == super::driver_spec::Status::Closed,
{
    assert(super::driver_spec::hello_failure(40).send == seq![21u8, 3, 3, 0, 2, 2, 40]) by (compute_only);
    assert(super::driver_spec::hello_closed().send == seq![21u8, 3, 3, 0, 2, 1, 0]) by (compute_only);
    assert(super::driver_spec::hello_closed().status == super::driver_spec::Status::Closed) by (compute_only);
}

/// §6.1, §6: truncation sends only the record it is given (our close_notify,
/// or nothing) and is reported as truncation; the peer's alert sends nothing.
pub proof fn lemma_nothing_sent()
    ensures
        super::driver_spec::truncated(seq![], 80).send.len() == 0,
        super::driver_spec::truncated(seq![9u8], 80).send == seq![9u8],
        super::driver_spec::truncated(seq![], 80).status
            == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated),
        super::driver_spec::peer_failed(40).send.len() == 0,
{
    assert(super::driver_spec::truncated(seq![], 80).send.len() == 0) by (compute_only);
    assert(super::driver_spec::truncated(seq![9u8], 80).send == seq![9u8]) by (compute_only);
    assert(super::driver_spec::truncated(seq![], 80).status
        == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated)) by (compute_only);
    assert(super::driver_spec::peer_failed(40).send.len() == 0) by (compute_only);
}

/// The bootstrap waiting for the server's Hello (the fields `eof` does not
/// read are left empty).
pub open spec fn hello_waiting() -> crate::hello::bootstrap_spec::State {
    crate::hello::bootstrap_spec::State {
        mode: crate::hello::bootstrap_spec::Mode::AwaitServerHello,
        hello: None,
        pending_flight: seq![],
        compatibility: false,
        reassembly: crate::spec::reasm_new(),
        retained: seq![],
    }
}

/// The joined client's end of the transport over the transducer's fixtures.
pub open spec fn eof_at(stage: super::driver_spec::Stage, status: super::driver_spec::Status)
    -> super::driver_spec::Step
{
    super::driver_spec::eof(super::post_handshake_examples::crypto(), super::post_handshake_examples::cipher(),
        stage, status)
}

/// §6.1 and choice 7: the end of the transport while a machine runs is a
/// truncation, `Failed(internal_error, Truncated)`, never `Closed`: during
/// the Hello exchange, the server's flight and application traffic, and
/// after our close_notify.
pub proof fn lemma_eof_truncates()
    ensures
        eof_at(super::driver_spec::Stage::Hello(hello_waiting(), seq![]), super::driver_spec::Status::Handshaking).status
            == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated),
        eof_at(super::driver_spec::Stage::App(super::post_handshake_examples::ready()), super::driver_spec::Status::Open).status
            == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated),
        eof_at(super::driver_spec::Stage::App(write_closed()), super::driver_spec::Status::Closing).status
            == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated),
        super::driver_spec::flight_eof(super::dispatcher_certificates::alert_ciphers(),
            super::dispatcher_certificates::sample_flight_state()).status
            == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated),
{
    assert(eof_at(super::driver_spec::Stage::Hello(hello_waiting(), seq![]), super::driver_spec::Status::Handshaking).status
        == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated)) by (compute_only);
    assert(eof_at(super::driver_spec::Stage::App(super::post_handshake_examples::ready()), super::driver_spec::Status::Open).status
        == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated)) by (compute_only);
    assert(eof_at(super::driver_spec::Stage::App(write_closed()), super::driver_spec::Status::Closing).status
        == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated)) by (compute_only);
    assert(super::driver_spec::flight_eof(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state()).status
        == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated)) by (compute_only);
}

/// §6.1 and choice 7: while our write side is open the end of the transport
/// sends our close_notify: in plaintext (warning, close_notify) during the
/// Hello exchange, sealed under the client handshake epoch at sequence number
/// 0 during the server's flight, and after the handshake the record a close
/// sends.
pub proof fn lemma_eof_sends_close_notify()
    ensures
        eof_at(super::driver_spec::Stage::Hello(hello_waiting(), seq![]), super::driver_spec::Status::Handshaking).send
            == seq![21u8, 3, 3, 0, 2, 1, 0],
        super::driver_spec::flight_eof(super::dispatcher_certificates::alert_ciphers(),
            super::dispatcher_certificates::sample_flight_state()).send
            == seq![23u8, 3, 3, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 21],
        eof_at(super::driver_spec::Stage::App(super::post_handshake_examples::ready()), super::driver_spec::Status::Open).send
            == carried(super::post_handshake_spec::close(super::post_handshake_examples::cipher(),
                super::post_handshake_examples::ready()).0, write_closed()).send,
        eof_at(super::driver_spec::Stage::App(super::post_handshake_examples::ready()), super::driver_spec::Status::Open).send.len() > 0,
{
    assert(eof_at(super::driver_spec::Stage::Hello(hello_waiting(), seq![]), super::driver_spec::Status::Handshaking).send
        == seq![21u8, 3, 3, 0, 2, 1, 0]) by (compute_only);
    assert(super::driver_spec::flight_eof(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state()).send
        == seq![23u8, 3, 3, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 21]) by (compute_only);
    assert(eof_at(super::driver_spec::Stage::App(super::post_handshake_examples::ready()), super::driver_spec::Status::Open).send
        == carried(super::post_handshake_spec::close(super::post_handshake_examples::cipher(),
            super::post_handshake_examples::ready()).0, write_closed()).send) by (compute_only);
    assert(eof_at(super::driver_spec::Stage::App(super::post_handshake_examples::ready()), super::driver_spec::Status::Open).send.len() > 0)
        by (compute_only);
}

/// §6.1 and choice 7: after our close_notify the end of the transport sends
/// nothing, and once the connection has ended nothing changes: one that
/// ended as `Closed` stays `Closed` and sends nothing.
pub proof fn lemma_eof_after_close()
    ensures
        eof_at(super::driver_spec::Stage::App(write_closed()), super::driver_spec::Status::Closing).send.len() == 0,
        eof_at(super::driver_spec::Stage::Ended, super::driver_spec::Status::Closed).send.len() == 0,
        eof_at(super::driver_spec::Stage::Ended, super::driver_spec::Status::Closed).status
            == super::driver_spec::Status::Closed,
{
    assert(eof_at(super::driver_spec::Stage::App(write_closed()), super::driver_spec::Status::Closing).send.len() == 0)
        by (compute_only);
    assert(eof_at(super::driver_spec::Stage::Ended, super::driver_spec::Status::Closed).send.len() == 0) by (compute_only);
    assert(eof_at(super::driver_spec::Stage::Ended, super::driver_spec::Status::Closed).status
        == super::driver_spec::Status::Closed) by (compute_only);
}

/// The dispatcher's step over its fixtures, carried through the join.
pub open spec fn carried_flight(action: super::dispatcher_spec::Action, after: super::dispatcher_spec::State)
    -> super::driver_spec::Step
{
    super::driver_spec::flight_out(crate::auth::examples::crypto(), crate::auth::examples::verifier(),
        super::dispatcher_certificates::flight_ciphers(), action, after)
}

/// The client flight of `dispatcher_certificates::awaiting`, carried through.
pub open spec fn flight_went_out() -> super::driver_spec::Step {
    carried_flight(super::dispatcher_spec::Action::Send(super::dispatcher_certificates::awaiting(false).pending_flight),
        super::dispatcher_certificates::awaiting(false))
}

/// The state the acknowledgement of that flight reaches.
pub open spec fn ready_state() -> super::dispatcher_spec::State {
    super::dispatcher_certificates::acked(super::dispatcher_certificates::awaiting(false),
        super::dispatcher_certificates::awaiting(false).pending_flight).1
}

/// §6: while the dispatcher goes on, the join stays in the flight and sends
/// nothing: a dropped record, a partial one, or user_canceled.
pub proof fn lemma_flight_goes_on()
    ensures
        carried_flight(super::dispatcher_spec::Action::Cancelled, super::dispatcher_certificates::flight_start()).stage
            == super::driver_spec::Stage::Flight(super::dispatcher_certificates::flight_start()),
        carried_flight(super::dispatcher_spec::Action::Cancelled, super::dispatcher_certificates::flight_start()).status
            == super::driver_spec::Status::Handshaking,
        carried_flight(super::dispatcher_spec::Action::Ignored, super::dispatcher_certificates::flight_start()).status
            == super::driver_spec::Status::Handshaking,
        carried_flight(super::dispatcher_spec::Action::None, super::dispatcher_certificates::flight_start()).send.len() == 0,
{
    assert(carried_flight(super::dispatcher_spec::Action::Cancelled, super::dispatcher_certificates::flight_start()).stage
        == super::driver_spec::Stage::Flight(super::dispatcher_certificates::flight_start())) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::Cancelled, super::dispatcher_certificates::flight_start()).status
        == super::driver_spec::Status::Handshaking) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::Ignored, super::dispatcher_certificates::flight_start()).status
        == super::driver_spec::Status::Handshaking) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::None, super::dispatcher_certificates::flight_start()).send.len() == 0) by (compute_only);
}

/// §6, §6.1: the dispatcher's three ends reach the wire as it said: its sealed
/// alert, nothing for the server's alert, and its sealed close_notify.
pub proof fn lemma_flight_ends()
    ensures
        carried_flight(super::dispatcher_spec::Action::Fail(40u8, Some(seq![9u8])), super::dispatcher_spec::failed()).send == seq![9u8],
        carried_flight(super::dispatcher_spec::Action::PeerAlert(40u8), super::dispatcher_spec::failed()).send.len() == 0,
        carried_flight(super::dispatcher_spec::Action::PeerAlert(40u8), super::dispatcher_spec::failed()).status
            == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Peer),
        carried_flight(super::dispatcher_spec::Action::Close(Some(seq![9u8])), super::dispatcher_spec::closed()).send == seq![9u8],
        carried_flight(super::dispatcher_spec::Action::Close(Some(seq![9u8])), super::dispatcher_spec::closed()).status
            == super::driver_spec::Status::Closed,
{
    assert(carried_flight(super::dispatcher_spec::Action::Fail(40u8, Some(seq![9u8])), super::dispatcher_spec::failed()).send == seq![9u8]) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::PeerAlert(40u8), super::dispatcher_spec::failed()).send.len() == 0) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::PeerAlert(40u8), super::dispatcher_spec::failed()).status
        == super::driver_spec::Status::Failed(40u8, super::driver_spec::Origin::Peer)) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::Close(Some(seq![9u8])), super::dispatcher_spec::closed()).send == seq![9u8]) by (compute_only);
    assert(carried_flight(super::dispatcher_spec::Action::Close(Some(seq![9u8])), super::dispatcher_spec::closed()).status
        == super::driver_spec::Status::Closed) by (compute_only);
}

/// §4.4.4, §7.3: the client flight goes out and is acknowledged in the same
/// step (choice 2), and the transducer starts from the application secrets.
pub proof fn lemma_flight_sent_starts_the_transducer()
    ensures
        flight_went_out().send == super::dispatcher_certificates::awaiting(false).pending_flight,
        flight_went_out().status == super::driver_spec::Status::Open,
        flight_went_out().stage == super::driver_spec::Stage::App(super::post_handshake_spec::start(
            crate::auth::examples::crypto(), ready_state().client_application_secret, ready_state().server_application_secret).unwrap()),
{
    assert(flight_went_out().send == super::dispatcher_certificates::awaiting(false).pending_flight) by (compute_only);
    assert(flight_went_out().status == super::driver_spec::Status::Open) by (compute_only);
    assert(flight_went_out().stage == super::driver_spec::Stage::App(super::post_handshake_spec::start(
        crate::auth::examples::crypto(), ready_state().client_application_secret, ready_state().server_application_secret).unwrap())) by (compute_only);
}
} // verus!
