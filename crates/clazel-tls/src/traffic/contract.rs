//! Contracts for the fixed cipher profile's protected traffic-key epochs.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Installed-key encryption function.
pub type Seal3 = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>;
/// Installed-key authentication/decryption function.
pub type Open3 = spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>;
/// Cipher encryption is bound to this exact factory and derived key.
pub open spec fn sealed_bound(f: super::spec::Cipher, key: Seq<u8>, seal: Seal3) -> bool {
    forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] seal(n, ad, p) == (f.seal)(key, n, ad, p)
}
/// Cipher authentication is bound to this exact factory and derived key.
pub open spec fn opened_bound(f: super::spec::Cipher, key: Seq<u8>, open: Open3) -> bool {
    forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] open(n, ad, ct) == (f.open)(key, n, ad, ct)
}
/// A record operation cannot change its installed cipher function.
pub open spec fn seal_preserved(before: Seal3, after: Seal3) -> bool {
    forall|n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| #[trigger] after(n, ad, p) == before(n, ad, p)
}
/// A record operation cannot replace its installed authentication function.
pub open spec fn open_preserved(before: Open3, after: Open3) -> bool {
    forall|n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>| #[trigger] after(n, ad, ct) == before(n, ad, ct)
}
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
