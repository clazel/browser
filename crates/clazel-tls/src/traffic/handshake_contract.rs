//! Contracts for installing the Hello handoff's exact handshake record directions.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Exact pipeline and ready-to-use epoch/authentication invariants.
pub open spec fn start_ensures(c: crate::schedule::spec::Crypto, k: crate::hello::join_spec::KeyExchange,
    config: crate::hello::client_spec::Config, transcript: crate::transcript::spec::State,
    peer_key: Seq<u8>, private_key: Seq<u8>, out: Result<super::handshake_spec::Handoff, u8>) -> bool
{
    out == super::handshake_spec::start(c, k, config, transcript, peer_key, private_key)
        && match out { Err(_) => true, Ok((auth, sender, receiver, master)) =>
            crate::auth::contract::exec_wf(auth) && super::spec::wf(sender) && super::spec::wf(receiver)
                && sender.next == Some(0) && receiver.next == Some(0) && !sender.failed && !receiver.failed && master.len() == 32 }
}
} // verus!
