//! Concrete RFC 8446 §5.2/§5.3/§5.4/§7.3 record-epoch witnesses.
//! These input-sensitive functions are protocol fixtures, not cryptography.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Total first octet for fixed-size fixture primitives.
pub open spec fn first(s: Seq<u8>) -> u8 { if s.len() == 0 { 0 } else { s[0] } }
/// Total last octet, binding fixture tags to the counter's low byte.
pub open spec fn last(s: Seq<u8>) -> u8 { if s.len() == 0 { 0 } else { s[s.len() - 1] } }
/// Input-sensitive fixed-size crypto fixture. Hash(empty) differs from empty.
pub open spec fn crypto() -> crate::schedule::spec::Crypto {
    crate::schedule::spec::Crypto {
        hash: |m: Seq<u8>| Seq::new(32, |i: int| ((m.len() + 1) % 251) as u8),
        extract: |s: Seq<u8>, k: Seq<u8>| Seq::new(32, |i: int| first(s) ^ first(k)),
        expand: |secret: Seq<u8>, info: Seq<u8>, n: nat| Seq::new(n, |i: int|
            first(secret) ^ (if info.len() > 9 { info[9] } else { 0u8 }) ^ last(info)),
        hmac: |k: Seq<u8>, m: Seq<u8>| Seq::new(32, |i: int| first(k) ^ first(m)),
    }
}
/// Scalar traffic secret 49 yields key octets 90 and IV octets 88 in this fixture.
pub open spec fn initial() -> super::spec::State {
    super::spec::start(crypto(), Seq::new(32, |i: int| 49u8)).unwrap()
}
/// MAC-like fixture including nonce and AD input, with the required tag length.
pub open spec fn seal() -> spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Seq<u8> {
    |n: Seq<u8>, ad: Seq<u8>, p: Seq<u8>| p + Seq::new(16, |i: int| first(n) ^ last(n) ^ first(ad))
}
/// One protected application record for sequence zero and IV octets 88.
pub open spec fn wire() -> Seq<u8> { seq![23u8,3u8,3u8,0u8,18u8,42u8,23u8] + Seq::new(16, |i: int| 23u8) }
/// Only the exact fixture's nonce, AD and ciphertext authenticate.
pub open spec fn open() -> spec_fn(Seq<u8>, Seq<u8>, Seq<u8>) -> Option<Seq<u8>> {
    |n: Seq<u8>, ad: Seq<u8>, ct: Seq<u8>|
        if n == Seq::new(12, |i: int| 88u8) && ad == seq![23u8,3u8,3u8,0u8,18u8]
            && ct == seq![42u8,23u8] + Seq::new(16, |i: int| 23u8) { Some(seq![42u8,23u8]) } else { None }
}
/// Concrete record-epoch requirement: traffic start zero.
pub proof fn lemma_traffic_start_zero()
    ensures initial().next == Some(0u64),
{
    assert(initial().next == Some(0u64)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic iv label.
pub proof fn lemma_traffic_iv_label()
    ensures initial().iv == Seq::new(12, |i: int| 88u8),
{
    assert(initial().iv == Seq::new(12, |i: int| 88u8)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic empty context.
pub proof fn lemma_traffic_empty_context()
    ensures initial().key == Seq::new(32, |i: int| 90u8),
{
    assert(initial().key == Seq::new(32, |i: int| 90u8)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic advance.
pub proof fn lemma_traffic_advance()
    ensures super::spec::advance(initial()).next == Some(1u64),
{
    assert(super::spec::advance(initial()).next == Some(1u64)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic no wrap.
pub proof fn lemma_traffic_no_wrap()
    ensures super::spec::advance(super::spec::State { next: Some(u64::MAX), ..initial() }).next is None,
{
    assert(super::spec::advance(super::spec::State { next: Some(u64::MAX), ..initial() }).next is None) by (compute_only);
}
/// Concrete record-epoch requirement: traffic failed send.
pub proof fn lemma_traffic_failed_send()
    ensures super::spec::send(seal(), super::spec::failed(initial()), 23, seq![42u8], 0).1 == Err(80u8),
{
    assert(super::spec::send(seal(), super::spec::failed(initial()), 23, seq![42u8], 0).1 == Err(80u8)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic failed receive.
pub proof fn lemma_traffic_failed_receive()
    ensures super::spec::receive(open(), super::spec::failed(initial()), wire()).1 == super::spec::Read::Fail(80),
{
    assert(super::spec::receive(open(), super::spec::failed(initial()), wire()).1 == super::spec::Read::Fail(80)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic incomplete counter.
pub proof fn lemma_traffic_incomplete_counter()
    ensures super::spec::receive(open(), initial(), seq![23u8,3u8,3u8,0u8,18u8]).0 == initial(),
{
    assert(super::spec::receive(open(), initial(), seq![23u8,3u8,3u8,0u8,18u8]).0 == initial()) by (compute_only);
}
/// Concrete record-epoch requirement: traffic received counter.
pub proof fn lemma_traffic_received_counter()
    ensures super::spec::receive(open(), initial(), wire()).0.next == Some(1u64),
{
    assert(super::spec::receive(open(), initial(), wire()).0.next == Some(1u64)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic mac terminal.
pub proof fn lemma_traffic_mac_terminal()
    ensures super::spec::receive(open(), initial(), seq![23u8,3u8,3u8,0u8,1u8,0u8]).0.failed,
{
    assert(super::spec::receive(open(), initial(), seq![23u8,3u8,3u8,0u8,1u8,0u8]).0.failed) by (compute_only);
}
/// Concrete record-epoch requirement: traffic padding inner bound.
pub proof fn lemma_traffic_padding_inner_bound()
    ensures super::spec::send_error(23, seq![42u8], 16384) == Some(22u8),
{
    assert(super::spec::send_error(23, seq![42u8], 16384) == Some(22u8)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic plaintext bound.
pub proof fn lemma_traffic_plaintext_bound()
    ensures super::spec::send_error(23, Seq::new(16385, |i: int| 42u8), 0) == Some(22u8),
{
    assert(super::spec::send_error(23, Seq::new(16385, |i: int| 42u8), 0) == Some(22u8)) by (compute_only);
}
/// Concrete record-epoch requirement: traffic no protected ccs.
pub proof fn lemma_traffic_no_protected_ccs()
    ensures super::spec::send_error(20, seq![1u8], 0) == Some(10u8),
{
    assert(super::spec::send_error(20, seq![1u8], 0) == Some(10u8)) by (compute_only);
}
} // verus!
