//! Contracts for RFC 8446 §4.4.1 transcript accumulation and §4.4.3 inputs.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Start succeeds with the first ClientHello encoding, or reports the body limit.
pub open spec fn start_ensures(body: Seq<u8>, result: Result<super::spec::State, super::spec::Error>) -> bool {
    result == super::spec::start(body)
        && match result { Ok(s) => super::spec::wf(s), Err(_) => true }
}

/// Accepted messages refine step and preserve wf; rejected messages leave the state unchanged.
pub open spec fn push_ensures(hash: spec_fn(Seq<u8>) -> Seq<u8>, before: super::spec::State,
    kind: super::spec::Kind, body: Seq<u8>, after: super::spec::State,
    result: Result<(), super::spec::Error>) -> bool
{
    match super::spec::step(hash, before, kind, body) {
        Ok(s) => result == Ok(()) && after == s && super::spec::wf(after),
        Err(e) => result == Err(e) && after == before,
    }
}

/// §4.4.3: exactly the context-separated signature input, of SHA-256 length.
pub open spec fn certificate_verify_ensures(server: bool, hash: Seq<u8>, out: Seq<u8>) -> bool {
    out == super::spec::certificate_verify_input(server, hash) && out.len() == 130
}
} // verus!
