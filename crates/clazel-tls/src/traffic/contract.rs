//! Contracts for the fixed cipher profile's protected traffic-key epochs.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Key/IV derivation, fresh sequence zero, and fixed-profile invariant.
pub open spec fn start_ensures(c: crate::schedule::spec::Crypto, secret: Seq<u8>, out: Result<super::spec::State, u8>) -> bool {
    out == super::spec::start(c, secret) && match out { Ok(s) => super::spec::wf(s), Err(_) => true }
}
/// Exact record construction and state transition, without counter wrap/reset.
pub open spec fn send_ensures(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>, before: super::spec::State,
    typ: u8, content: Seq<u8>, padding: nat, after: super::spec::State, out: Result<Seq<u8>, u8>) -> bool
{
    (after, out) == super::spec::send(seal, before, typ, content, padding) && super::spec::wf(after)
}
/// Exact framing/MAC/inner parsing and preserved epoch invariant.
pub open spec fn receive_ensures(open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, before: super::spec::State,
    wire: Seq<u8>, after: super::spec::State, out: super::spec::Read) -> bool
{
    (after, out) == super::spec::receive(open, before, wire) && super::spec::wf(after)
}
} // verus!
