//! Concrete RFC 8446 transcript and signature-input witnesses.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Initial ClientHello encoding, used as a small witness.
pub open spec fn initial() -> State {
    State { messages: seq![1u8, 0u8, 0u8, 1u8, 7u8], phase: Phase::FirstServerHello, retried: false }
}
/// A tagged hash exposes which bytes the retry rewrite hashes; not cryptography.
pub open spec fn hash(s: Seq<u8>) -> Seq<u8> { seq![42u8] + s }
/// The state after accepting a retry, as the RFC equation spells it.
pub open spec fn retried() -> State {
    State { messages: seq![254u8, 0u8, 0u8, 6u8, 42u8, 1u8, 0u8, 0u8, 1u8, 7u8, 2u8, 0u8, 0u8, 1u8, 8u8], phase: Phase::SecondClientHello, retried: true }
}

/// Concrete RFC 8446 start rule.
pub proof fn lemma_start()
    ensures start(seq![7u8]) == Ok(initial()),
{
    assert(start(seq![7u8]) == Ok(initial())) by (compute_only);
}

/// Concrete RFC 8446 ordinary rule.
pub proof fn lemma_ordinary()
    ensures step(|s: Seq<u8>| hash(s), initial(), Kind::ServerHello, seq![8u8]) == Ok(State { messages: seq![1u8, 0u8, 0u8, 1u8, 7u8, 2u8, 0u8, 0u8, 1u8, 8u8], phase: Phase::Handshake, retried: false }),
{
    assert(step(|s: Seq<u8>| hash(s), initial(), Kind::ServerHello, seq![8u8]) == Ok(State { messages: seq![1u8, 0u8, 0u8, 1u8, 7u8, 2u8, 0u8, 0u8, 1u8, 8u8], phase: Phase::Handshake, retried: false })) by (compute_only);
}

/// Concrete RFC 8446 retry rule.
pub proof fn lemma_retry()
    ensures step(|s: Seq<u8>| hash(s), initial(), Kind::HelloRetryRequest, seq![8u8]) == Ok(retried()),
{
    assert(step(|s: Seq<u8>| hash(s), initial(), Kind::HelloRetryRequest, seq![8u8]) == Ok(retried())) by (compute_only);
}

/// Concrete RFC 8446 repeat rule.
pub proof fn lemma_repeat()
    ensures step(|s: Seq<u8>| hash(s), retried(), Kind::HelloRetryRequest, seq![8u8]) == Err(Error::UnexpectedMessage),
{
    assert(step(|s: Seq<u8>| hash(s), retried(), Kind::HelloRetryRequest, seq![8u8]) == Err(Error::UnexpectedMessage)) by (compute_only);
}

/// Concrete RFC 8446 first_order rule.
pub proof fn lemma_first_order()
    ensures next_phase(Phase::FirstServerHello, Kind::Certificate) == None,
{
    assert(next_phase(Phase::FirstServerHello, Kind::Certificate) == None) by (compute_only);
}

/// Concrete RFC 8446 second_client rule.
pub proof fn lemma_second_client()
    ensures next_phase(Phase::SecondClientHello, Kind::ServerHello) == None,
{
    assert(next_phase(Phase::SecondClientHello, Kind::ServerHello) == None) by (compute_only);
}

/// Concrete RFC 8446 second_server rule.
pub proof fn lemma_second_server()
    ensures next_phase(Phase::SecondServerHello, Kind::ClientHello) == None,
{
    assert(next_phase(Phase::SecondServerHello, Kind::ClientHello) == None) by (compute_only);
}

/// Concrete RFC 8446 server_input rule.
pub proof fn lemma_server_input()
    ensures certificate_verify_input(true, seq![1u8]) == seq![32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 115u8, 101u8, 114u8, 118u8, 101u8, 114u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8, 0u8, 1u8],
{
    assert(certificate_verify_input(true, seq![1u8]) == seq![32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 115u8, 101u8, 114u8, 118u8, 101u8, 114u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8, 0u8, 1u8]) by (compute_only);
}

/// Concrete RFC 8446 client_input rule.
pub proof fn lemma_client_input()
    ensures certificate_verify_input(false, seq![1u8]) == seq![32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 99u8, 108u8, 105u8, 101u8, 110u8, 116u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8, 0u8, 1u8],
{
    assert(certificate_verify_input(false, seq![1u8]) == seq![32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 32u8, 84u8, 76u8, 83u8, 32u8, 49u8, 46u8, 51u8, 44u8, 32u8, 99u8, 108u8, 105u8, 101u8, 110u8, 116u8, 32u8, 67u8, 101u8, 114u8, 116u8, 105u8, 102u8, 105u8, 99u8, 97u8, 116u8, 101u8, 86u8, 101u8, 114u8, 105u8, 102u8, 121u8, 0u8, 1u8]) by (compute_only);
}

} // verus!
