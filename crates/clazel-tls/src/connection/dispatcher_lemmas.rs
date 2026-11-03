//! RFC 8446 KeyUpdate and fatal-alert facts about the dispatcher spec, used
//! by proofs and mutation certificates: general lemmas, and concrete ones
//! evaluated on the fixtures of `dispatcher_certificates`.
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// RFC 8446 §4.6.3: request_update is a one-byte enum in {0,1}; a value 2
/// is rejected by the KeyUpdate transition rather than queued for sending.
pub proof fn lemma_key_update_request_is_bounded()
    ensures super::dispatcher_spec::prepare_key_update(
        super::dispatcher_certificates::crypto(),
        super::dispatcher_certificates::ciphers(),
        super::dispatcher_certificates::sample_ready_state(), 2, false)
            == super::dispatcher_certificates::sample_ready_state(),
{
    assert(super::dispatcher_spec::prepare_key_update(
        super::dispatcher_certificates::crypto(),
        super::dispatcher_certificates::ciphers(),
        super::dispatcher_certificates::sample_ready_state(), 2, false)
            == super::dispatcher_certificates::sample_ready_state());
}

/// Invalid traffic secrets cannot leave the model paired with stale epochs.
pub proof fn lemma_key_update_epoch_start_failure_is_terminal()
    ensures
        super::dispatcher_spec::receive_key_update(
            super::dispatcher_certificates::crypto(),
            super::dispatcher_certificates::sample_ready_state(), 0)
                == super::dispatcher_spec::failed(),
        super::dispatcher_spec::acknowledge_key_update(
            super::dispatcher_certificates::crypto(),
            super::dispatcher_certificates::sample_bad_update_state(), seq![7u8])
                == super::dispatcher_spec::failed(),
{
    reveal(super::dispatcher_spec::receive_key_update);
    reveal(super::dispatcher_spec::acknowledge_key_update);
    reveal(crate::traffic::spec::start);
    reveal(crate::schedule::spec::next_traffic_secret);
    reveal(crate::schedule::spec::expand_label);
    reveal(super::dispatcher_certificates::crypto);
    reveal(super::dispatcher_certificates::empty_expand);
    assert(crate::schedule::spec::next_traffic_secret(
        super::dispatcher_certificates::crypto(),
        super::dispatcher_certificates::sample_ready_state().server_application_secret) == seq![]);
    assert(crate::traffic::spec::start(
        super::dispatcher_certificates::crypto(), seq![]) == Err(80u8));
    assert(super::dispatcher_spec::receive_key_update(
        super::dispatcher_certificates::crypto(),
        super::dispatcher_certificates::sample_ready_state(), 0)
            == super::dispatcher_spec::failed());
    assert(crate::traffic::spec::start(
        super::dispatcher_certificates::crypto(), seq![]) == Err(80u8));
    assert(super::dispatcher_spec::acknowledge_key_update(
        super::dispatcher_certificates::crypto(),
        super::dispatcher_certificates::sample_bad_update_state(), seq![7u8])
            == super::dispatcher_spec::failed());
}

/// RFC 8446 §4.6.3 and §6.1: after our close_notify, update_requested still
/// rotates the receive epoch but owes no KeyUpdate in reply.
pub proof fn lemma_key_update_after_close_owes_no_response()
    ensures !super::dispatcher_spec::receive_key_update(
        super::dispatcher_certificates::passthrough_crypto(),
        super::dispatcher_certificates::sample_write_closed_state(), 1).response_due,
{
    assert(!super::dispatcher_spec::receive_key_update(
        super::dispatcher_certificates::passthrough_crypto(),
        super::dispatcher_certificates::sample_write_closed_state(), 1).response_due) by (compute_only);
}

/// RFC 8446 §6.1: receiving close_notify closes the peer write direction but
/// retains local application sending resources until separately closed.
pub proof fn lemma_peer_close_is_directional()
    ensures {
        let before = super::dispatcher_certificates::sample_ready_state();
        let after = super::dispatcher_spec::receive_close_notify(before);
        after.mode == super::dispatcher_spec::Mode::Ready
            && after.peer_write_closed && !after.local_write_closed
            && after.application_sender == before.application_sender
            && after.pending_update_wire == before.pending_update_wire
            && after.pending_update_secret == before.pending_update_secret
            && after.pending_update_request == before.pending_update_request
            && after.response_due == before.response_due
    },
{
    reveal(super::dispatcher_spec::receive_close_notify);
    assert(super::dispatcher_spec::receive_close_notify(
        super::dispatcher_certificates::sample_ready_state()) ==
        super::dispatcher_spec::State {
            peer_write_closed: true,
            ..super::dispatcher_certificates::sample_ready_state()
        });
}

/// RFC 8446 §5.1: a compatibility CCS between the fragments of one handshake
/// message interleaves another record type and is refused; at a boundary the
/// same record is still dropped.
pub proof fn lemma_compatibility_ccs_not_dropped_mid_message()
    ensures
        !super::dispatcher_spec::compatibility_ccs_dropped(super::dispatcher_spec::Mode::Handshake,
            Some(crate::auth::spec::Phase::Finished), crate::spec::Reasm { buf: seq![1u8] }),
        super::dispatcher_spec::compatibility_ccs_dropped(super::dispatcher_spec::Mode::Handshake,
            Some(crate::auth::spec::Phase::Finished), crate::spec::reasm_new()),
{
    reveal(crate::spec::reasm_new);
}

// ---------------------------------------------------------------------------
// RFC 8446 §5.3, §6, §6.1, §6.2: the fatal alerts the dispatcher sends.
// ---------------------------------------------------------------------------

/// §5.3, §6.2: a locally detected fatal error sends the fatal alert sealed
/// under the settled write epoch's next sequence number, the one no record
/// has used, with the key-explicit AEAD at that epoch's key.
pub proof fn lemma_alert_uses_next_sequence_number(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8, epoch: crate::traffic::spec::State, n: u64)
    requires
        super::dispatcher_spec::alert_epoch(s) == Some(epoch),
        epoch.next == Some(n),
        !epoch.failed,
    ensures
        super::dispatcher_spec::fatal(ciphers, s, description).0 == super::dispatcher_spec::Action::Fail(
            description, Some(crate::spec::encrypt_record(super::dispatcher_spec::seal_with(ciphers, epoch), 16,
                epoch.iv, n, crate::spec::CT_ALERT, super::dispatcher_spec::fatal_alert(description), 0))),
{
    assert(super::dispatcher_spec::fatal_alert(description).len() == 2);
}

/// §5.3, §6.2: the alert is the last record under its key. The state after a
/// fatal error holds no key at all, so nothing is sealed after the alert
/// under the sequence number it took, or any other.
pub proof fn lemma_alert_is_the_last_record(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8)
    ensures
        super::dispatcher_spec::fatal(ciphers, s, description).1 == super::dispatcher_spec::failed(),
        super::dispatcher_spec::no_live_secrets(super::dispatcher_spec::fatal(ciphers, s, description).1),
        super::dispatcher_spec::alert_epoch(super::dispatcher_spec::fatal(ciphers, s, description).1) is None,
{}

/// The epoch an alert is sealed under is a write epoch the client holds, in
/// a phase where the peer reads it next: the handshake epoch during the
/// server's flight, the application epoch after the handshake while our write
/// side is open and no KeyUpdate is pending. Awaiting the Finished
/// acknowledgement, failed and closed, there is none.
pub proof fn lemma_alert_epoch_is_held(s: super::dispatcher_spec::State)
    ensures
        match super::dispatcher_spec::alert_epoch(s) {
            Some(e) => (s.mode == super::dispatcher_spec::Mode::Handshake && s.handshake_sender == Some(e))
                || (s.mode == super::dispatcher_spec::Mode::Ready && s.application_sender == Some(e)
                    && super::dispatcher_spec::write_open(s) && s.pending_update_request is None),
            None => true,
        },
        (s.mode == super::dispatcher_spec::Mode::AwaitClientFlight
            || s.mode == super::dispatcher_spec::Mode::Failed
            || s.mode == super::dispatcher_spec::Mode::Closed)
            ==> super::dispatcher_spec::alert_epoch(s) is None,
{}

/// If no write key is held and settled, no protected alert is sent.
pub proof fn lemma_no_write_key_no_alert(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8)
    requires super::dispatcher_spec::alert_epoch(s) is None,
    ensures super::dispatcher_spec::fatal(ciphers, s, description).0
        == super::dispatcher_spec::Action::Fail(description, None),
{}

/// §6, §6.2: a fatal alert from the peer is never answered, in any state.
pub proof fn lemma_peer_alert_not_answered(ciphers: super::dispatcher_spec::Ciphers,
    s: super::dispatcher_spec::State, description: u8)
    ensures super::dispatcher_spec::receive_fatal_alert(ciphers, s, description)
        == (super::dispatcher_spec::Action::PeerAlert(description), super::dispatcher_spec::failed()),
{}

/// §6.1: a truncated connection sends nothing.
pub proof fn lemma_truncation_sends_nothing(description: u8)
    ensures super::dispatcher_spec::die(description)
        == (super::dispatcher_spec::Action::Fail(description, None), super::dispatcher_spec::failed()),
{}

/// §6.2: during the server's flight, a local error (here bad_certificate, 42)
/// is sent as a fatal alert, sealed under the client handshake epoch at
/// sequence number 0. With the fixture AEAD the record is the header
/// (application_data, 0x0303, 19 octets), the nonce (all zero), then the
/// inner plaintext: level 2 (fatal), 42, content type 21 (alert).
pub proof fn lemma_flight_failure_sends_alert()
    ensures super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state(), 42).0
        == super::dispatcher_spec::Action::Fail(42u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 42, 21])),
{
    assert(super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_flight_state(), 42).0
        == super::dispatcher_spec::Action::Fail(42u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 42, 21]))) by (compute_only);
}

/// §5.3, §6.2: after the handshake, with five records already sent, a local
/// error (unexpected_message, 10) is sealed under the client application
/// epoch at sequence number 5, not a number already used: the nonce's last
/// octet is 5.
pub proof fn lemma_application_failure_sends_alert_at_next_number()
    ensures super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_ready_at(5), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 10, 21])),
{
    assert(super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_ready_at(5), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, Some(seq![23u8, 3, 3, 0, 19,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 10, 21]))) by (compute_only);
}

/// While a sealed KeyUpdate awaits acknowledgement the peer's read key is not
/// settled, so no alert is sealed.
pub proof fn lemma_no_alert_while_update_pending()
    ensures super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_update_pending(), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, None),
{
    assert(super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_update_pending(), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, None)) by (compute_only);
}

/// §6.1: after our close_notify nothing more is written, not even an alert.
pub proof fn lemma_no_alert_after_close_notify()
    ensures super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_close_sent(), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, None),
{
    assert(super::dispatcher_spec::fatal(super::dispatcher_certificates::alert_ciphers(),
        super::dispatcher_certificates::sample_close_sent(), 10).0
        == super::dispatcher_spec::Action::Fail(10u8, None)) by (compute_only);
}
} // verus!
