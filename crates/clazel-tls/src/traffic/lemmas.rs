//! Counter, terminal-state and plaintext-release properties of record epochs.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// §5.3: advancing never wraps to zero or repeats the used counter.
pub proof fn lemma_advance(s: super::spec::State, n: u64)
    requires s.next == Some(n),
    ensures match super::spec::advance(s).next {
        Some(m) => m > n,
        None => n == u64::MAX,
    },
{}
/// Metadata invariant survives both encryption and authentication failures.
pub proof fn lemma_preserves_wf(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, s: super::spec::State,
    typ: u8, content: Seq<u8>, padding: nat, wire: Seq<u8>)
    requires super::spec::wf(s),
    ensures super::spec::wf(super::spec::send(seal, s, typ, content, padding).0),
        super::spec::wf(super::spec::receive(open, s, wire).0),
{}
/// A failed epoch can never emit ciphertext or release decrypted record content.
pub proof fn lemma_failed_absorbs(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, s: super::spec::State,
    typ: u8, content: Seq<u8>, padding: nat, wire: Seq<u8>)
    requires s.failed,
    ensures super::spec::send(seal, s, typ, content, padding) == (s, Err(80u8)),
        super::spec::receive(open, s, wire) == (s, super::spec::Read::Fail(80)),
{}
/// Exhaustion terminates instead of using sequence zero with an existing key.
pub proof fn lemma_exhausted(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>, s: super::spec::State,
    typ: u8, content: Seq<u8>, padding: nat, wire: Seq<u8>)
    requires !s.failed, s.next is None,
    ensures super::spec::send(seal, s, typ, content, padding) == (super::spec::failed(s), Err(80u8)),
        super::spec::receive(open, s, wire) == (super::spec::failed(s), super::spec::Read::Fail(80)),
{}
/// A successful send consumes exactly the next counter once, preserving its key/IV.
pub proof fn lemma_sent_counter(seal: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8>,
    s: super::spec::State, typ: u8, content: Seq<u8>, padding: nat)
    requires super::spec::send(seal, s, typ, content, padding).1 is Ok,
    ensures !s.failed, s.next is Some,
        super::spec::send(seal, s, typ, content, padding).0 == super::spec::advance(s),
{}
/// Incomplete input does not consume a sequence number or replace key material.
pub proof fn lemma_need_more(open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    s: super::spec::State, wire: Seq<u8>)
    requires super::spec::receive(open, s, wire).1 is NeedMore,
    ensures super::spec::receive(open, s, wire).0 == s,
{}
/// A returned record passed inner type/size checks and advances exactly once.
pub proof fn lemma_plaintext_release(open: spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>>,
    s: super::spec::State, wire: Seq<u8>, typ: u8, content: Seq<u8>, consumed: nat)
    requires super::spec::receive(open, s, wire).1 == super::spec::Read::Record(typ, content, consumed),
    ensures !s.failed, s.next is Some,
        super::spec::receive(open, s, wire).0 == super::spec::advance(s),
        typ == 21 || typ == 22 || typ == 23,
        content.len() <= crate::spec::MAX_PLAINTEXT,
        (typ == 21 || typ == 22) ==> content.len() > 0,
{}
} // verus!
