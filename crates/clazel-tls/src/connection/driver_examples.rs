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

/// §6.1, §6: truncation and the peer's alert send nothing.
pub proof fn lemma_nothing_sent()
    ensures
        super::driver_spec::truncated(80).send.len() == 0,
        super::driver_spec::truncated(80).status
            == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated),
        super::driver_spec::peer_failed(40).send.len() == 0,
{
    assert(super::driver_spec::truncated(80).send.len() == 0) by (compute_only);
    assert(super::driver_spec::truncated(80).status
        == super::driver_spec::Status::Failed(80u8, super::driver_spec::Origin::Truncated)) by (compute_only);
    assert(super::driver_spec::peer_failed(40).send.len() == 0) by (compute_only);
}
} // verus!
