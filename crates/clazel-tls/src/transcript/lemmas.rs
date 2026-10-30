//! Properties of RFC 8446 transcript construction, without crypto assumptions.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
/// §4: a handshake encoding has its four-byte header and the body.
pub proof fn lemma_message_length(t: u8, body: Seq<u8>)
    ensures crate::spec::write_handshake(t, body).len() == 4 + body.len(),
{
    crate::lemmas_pl::lemma_be_bytes_len(body.len(), 3);
}

/// Starting the accumulator preserves the retained-byte bound and phase invariant.
pub proof fn lemma_start_wf(body: Seq<u8>)
    ensures match start(body) { Ok(s) => wf(s), Err(_) => true },
{
    lemma_message_length(1, body);
}

/// Appending preserves the invariant, including which phases imply a retry.
pub proof fn lemma_step_wf(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, k: Kind, b: Seq<u8>)
    requires wf(s),
    ensures match step(hash, s, k, b) { Ok(next) => wf(next), Err(_) => true },
{
    match s.phase {
        Phase::FirstServerHello => {},
        Phase::SecondClientHello => {},
        Phase::SecondServerHello => {},
        Phase::Handshake => {},
    }
}

/// §4.1.4: after accepting a retry, every subsequent retry is refused.
pub proof fn theorem_retry_once(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, body: Seq<u8>)
    requires wf(s), s.retried,
    ensures step(hash, s, Kind::HelloRetryRequest, body) is Err,
{
}

/// An accepted operation never clears the record that a retry occurred.
pub proof fn theorem_retry_monotone(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, kind: Kind, body: Seq<u8>)
    ensures match step(hash, s, kind, body) {
        Ok(next) => s.retried ==> next.retried,
        Err(_) => true,
    },
{
}

/// §4.4.1: ordinary messages retain the previous transcript as an exact prefix.
pub proof fn theorem_append(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, kind: Kind, body: Seq<u8>)
    requires kind != Kind::HelloRetryRequest,
    ensures match step(hash, s, kind, body) {
        Ok(next) => next.messages == s.messages + crate::spec::write_handshake(wire_type(kind), body),
        Err(_) => true,
    },
{
}

/// §4.4.1: the retry transcript is synthetic message_hash followed by the HRR.
pub proof fn theorem_retry_transcript(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: State, body: Seq<u8>)
    ensures match step(hash, s, Kind::HelloRetryRequest, body) {
        Ok(next) => next.messages == crate::spec::write_handshake(254, hash(s.messages))
            + crate::spec::write_handshake(2, body),
        Err(_) => true,
    },
{
}
} // verus!
