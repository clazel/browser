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
/// §4.4.2: a state whose chain check passed holds the end-entity key that
/// the chain validator returned for the state's own host and clock and some
/// Certificate body. (Which body is not named; the step that set the key
/// passed it, `lemmas::theorem_certificate_binding`.)
pub open spec fn chain_justified(v: super::spec::Verification, s: super::spec::State) -> bool {
    s.chain_checked ==> exists|body: Seq<u8>| #[trigger] (v.chain)(s.config.host, s.config.now, body) == Ok::<Seq<u8>, super::spec::CertificateError>(s.key)
}
/// Over every finite trace of peer and I/O inputs, the key that
/// CertificateVerify is checked with, and every later state's, is one the
/// chain validator returned for the captured host and clock: no input
/// sequence reaches chain_checked any other way, and none changes the host,
/// the clock or the key afterwards except through another validation.
pub open spec fn thm_chain_justified_trace(c: crate::schedule::spec::Crypto, v: super::spec::Verification,
    s: super::spec::State, inputs: Seq<super::spec::Input>) -> bool
{
    super::spec::wf(s) && chain_justified(v, s) ==> chain_justified(v, super::spec::run(c, v, s, inputs))
}
} // verus!
