//! Empty injection point for certified authentication mutation kills.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A nonempty initial server Certificate context is rejected by the auth profile.
pub proof fn lemma_nonempty_server_certificate_context_is_rejected()
    ensures !initial_certificate_context_valid(seq![7u8])
{
    assert(!initial_certificate_context_valid(seq![7u8])) by (compute_only);
}

}
