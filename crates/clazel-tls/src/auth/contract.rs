//! Contracts for RFC 8446's initial certificate-authentication state machine.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Runtime invariant also records the SHA-256 application checkpoint's length.
pub open spec fn exec_wf(s: super::spec::State) -> bool {
    super::spec::wf(s)
        && (s.phase == super::spec::Phase::SendFinished || s.phase == super::spec::Phase::Ready ==> s.application_hash.len() == 32)
}
/// Starting returns the stated initial state and establishes the runtime invariant.
pub open spec fn start_ensures(config: super::spec::Config, transcript: crate::transcript::spec::State,
    result: Result<super::spec::State, u8>) -> bool
{
    result == super::spec::start(config, transcript)
        && match result { Ok(s) => exec_wf(s), Err(_) => true }
}
/// Every executable effect refines the pure step and preserves the runtime invariant.
pub open spec fn step_ensures(c: crate::schedule::spec::Crypto, v: super::spec::Verification,
    before: super::spec::State, input: super::spec::Input, after: super::spec::State, action: super::spec::Action) -> bool
{
    (after, action) == super::spec::step(c, v, before, input) && exec_wf(after)
}
/// Application delivery requires all three peer checks and the client's send ack.
pub open spec fn delivery_safe(before: super::spec::State, action: super::spec::Action) -> bool {
    action is Deliver ==> before.phase == super::spec::Phase::Ready
        && before.chain_checked && before.signature_checked && before.finished_checked && before.client_sent
}
/// The only emitted client flight follows successful chain, signature and MAC checks.
pub open spec fn send_safe(after: super::spec::State, action: super::spec::Action) -> bool {
    action is Send ==> after.phase == super::spec::Phase::SendFinished
        && after.chain_checked && after.signature_checked && after.finished_checked && !after.client_sent
}
} // verus!
