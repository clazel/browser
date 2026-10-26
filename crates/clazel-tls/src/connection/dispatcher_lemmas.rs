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
} // verus!
