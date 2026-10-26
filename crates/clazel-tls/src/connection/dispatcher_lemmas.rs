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
} // verus!
