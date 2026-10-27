//! Concrete RFC 8446 KeyUpdate facts used by proofs and mutation certificates.
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
} // verus!
