//! Contracts for generated ClientHello and retained Hello negotiation state.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// The builder emits exactly the profile's body; bounded, valid inputs only.
pub open spec fn build_requires(c: super::client_spec::Config, cookie: Seq<u8>) -> bool {
    super::client_spec::config_ok(c) && super::client_spec::cookie_ok(cookie)
}
/// Builder refinement against the RFC-structured ClientHello representation.
pub open spec fn build_ensures(c: super::client_spec::Config, cookie: Seq<u8>, out: Seq<u8>) -> bool {
    out == super::client_spec::body(c, cookie) && out.len() <= crate::transcript::spec::MAX_BODY
}
/// Starting captures the actual configuration and exact first flight.
pub open spec fn start_ensures(c: super::client_spec::Config, out: Result<(super::client_spec::State, Seq<u8>), u8>) -> bool {
    out == super::client_spec::start(c) && match out { Ok((s, _)) => super::client_spec::wf(s), Err(_) => true }
}
/// Refinement and preserved retry invariant or authenticated-flight prerequisites.
pub open spec fn receive_ensures(hash: spec_fn(Seq<u8>) -> Seq<u8>, before: super::client_spec::State,
    server: Seq<u8>, out: Result<super::client_spec::Outcome, u8>) -> bool
{
    out == super::client_spec::receive(hash, before, server)
        && match out {
            Ok(super::client_spec::Outcome::Retry(s, _)) => super::client_spec::wf(s) && s.config == before.config && s.transcript.retried,
            Ok(super::client_spec::Outcome::Established(c, t, key)) => c == before.config
                && crate::transcript::spec::wf(t) && t.phase == crate::transcript::spec::Phase::Handshake && key.len() == 32,
            Err(_) => true,
        }
}
} // verus!
