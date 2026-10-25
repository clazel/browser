//! Concrete Hello construction and key-handoff mutation witnesses.
//! The input-sensitive primitive/key-exchange functions are protocol fixtures,
//! not real cryptography. RFC 8446 (August 2018) §4.1.2, §7.1 and §7.4.2.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Canonical target, captured time and public share for the fixture scalar 5.
pub open spec fn config() -> super::client_spec::Config {
    super::client_spec::Config { host: seq![104u8], now: 7, random: Seq::new(32, |i: int| 1u8),
        session_id: seq![7u8], public_key: Seq::new(32, |i: int| 5u8), send_sni: true }
}
/// Total first/last byte helpers for input-sensitive fixture functions.
pub open spec fn first(s: Seq<u8>) -> u8 { if s.len() == 0 { 0 } else { s[0] } }
/// Total last byte, used to bind expanded output to the transcript-hash context.
pub open spec fn last(s: Seq<u8>) -> u8 { if s.len() == 0 { 0 } else { s[s.len() - 1] } }
/// Pure, input-sensitive fixed-size fixtures; no crypto correctness claim.
pub open spec fn crypto() -> crate::schedule::spec::Crypto {
    crate::schedule::spec::Crypto {
        hash: |m: Seq<u8>| Seq::new(32, |i: int| (m.len() % 251) as u8),
        extract: |salt: Seq<u8>, ikm: Seq<u8>| Seq::new(32, |i: int| first(salt) ^ first(ikm)),
        expand: |secret: Seq<u8>, info: Seq<u8>, n: nat| Seq::new(n, |i: int|
            first(secret) ^ (if info.len() > 9 { info[9] } else { 0u8 }) ^ last(info)),
        hmac: |key: Seq<u8>, message: Seq<u8>| Seq::new(32, |i: int| first(key) ^ first(message)),
    }
}
/// Fixture key agreement binds both explicit private and peer public inputs.
pub open spec fn exchange() -> super::join_spec::KeyExchange {
    super::join_spec::KeyExchange {
        public_key: |private_key: Seq<u8>| Seq::new(32, |i: int| first(private_key)),
        shared_secret: |private_key: Seq<u8>, peer: Seq<u8>| Some(Seq::new(32, |i: int| first(private_key) ^ first(peer))),
    }
}
/// Abstract retained final-SH prefix, with ten bytes to distinguish Hash(prefix).
pub open spec fn transcript() -> crate::transcript::spec::State {
    crate::transcript::spec::State { messages: seq![1u8,0u8,0u8,1u8,9u8,2u8,0u8,0u8,1u8,8u8],
        phase: crate::transcript::spec::Phase::Handshake, retried: false }
}
/// Run the join on one fixture context. Scalar 5 and peer 17 yield shared 20,
/// handshake 112, master 20, server traffic 9 and client traffic 25.
pub open spec fn attempt(c: super::client_spec::Config, peer: Seq<u8>) -> Result<(crate::auth::spec::State, Seq<u8>), u8> {
    super::join_spec::into_auth(crypto(), exchange(), c, transcript(), peer, Seq::new(32, |i: int| 5u8))
}
/// Concrete RFC 8446 requirement: client cipher.
pub proof fn lemma_client_cipher()
    ensures super::client_spec::client_hello(config(), seq![]).cipher_suites == seq![0x1303u16],
{
    assert(super::client_spec::client_hello(config(), seq![]).cipher_suites == seq![0x1303u16]) by (compute_only);
}
/// Concrete RFC 8446 requirement: client public share.
pub proof fn lemma_client_public_share()
    ensures super::client_spec::extensions(config(), seq![])[4].data == seq![0u8,36u8,0u8,29u8,0u8,32u8] + Seq::new(32, |i: int| 5u8),
{
    assert(super::client_spec::extensions(config(), seq![])[4].data == seq![0u8,36u8,0u8,29u8,0u8,32u8] + Seq::new(32, |i: int| 5u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: client cookie.
pub proof fn lemma_client_cookie()
    ensures super::client_spec::extensions(config(), seq![0u8,1u8,9u8]).len() == 6,
{
    assert(super::client_spec::extensions(config(), seq![0u8,1u8,9u8]).len() == 6) by (compute_only);
}
/// Concrete RFC 8446 requirement: join key binding.
pub proof fn lemma_join_key_binding()
    ensures attempt(super::client_spec::Config { public_key: Seq::new(32, |i: int| 6u8), ..config() }, Seq::new(32, |i: int| 17u8)) == Err(80u8),
{
    assert(attempt(super::client_spec::Config { public_key: Seq::new(32, |i: int| 6u8), ..config() }, Seq::new(32, |i: int| 17u8)) == Err(80u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: join zero secret.
pub proof fn lemma_join_zero_secret()
    ensures attempt(config(), Seq::new(32, |i: int| 5u8)) == Err(47u8),
{
    assert(attempt(config(), Seq::new(32, |i: int| 5u8)) == Err(47u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: join checks shared not peer.
pub proof fn lemma_join_checks_shared_not_peer()
    ensures attempt(config(), Seq::new(32, |i: int| 0u8)) is Ok,
{
    assert(attempt(config(), Seq::new(32, |i: int| 0u8)) is Ok) by (compute_only);
}
/// Concrete RFC 8446 requirement: join server label.
pub proof fn lemma_join_server_label()
    ensures super::join_spec::auth_config(crypto(), config(), transcript(), Seq::new(32, |i: int| 112u8)).server_secret == Seq::new(32, |i: int| 9u8),
{
    assert(super::join_spec::auth_config(crypto(), config(), transcript(), Seq::new(32, |i: int| 112u8)).server_secret == Seq::new(32, |i: int| 9u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: join client label.
pub proof fn lemma_join_client_label()
    ensures super::join_spec::auth_config(crypto(), config(), transcript(), Seq::new(32, |i: int| 112u8)).client_secret == Seq::new(32, |i: int| 25u8),
{
    assert(super::join_spec::auth_config(crypto(), config(), transcript(), Seq::new(32, |i: int| 112u8)).client_secret == Seq::new(32, |i: int| 25u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: join transcript.
pub proof fn lemma_join_transcript()
    ensures super::join_spec::auth_config(crypto(), config(), transcript(), Seq::new(32, |i: int| 112u8)).server_secret == Seq::new(32, |i: int| 9u8),
{
    assert(super::join_spec::auth_config(crypto(), config(), transcript(), Seq::new(32, |i: int| 112u8)).server_secret == Seq::new(32, |i: int| 9u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: join master source.
pub proof fn lemma_join_master_source()
    ensures attempt(config(), Seq::new(32, |i: int| 17u8)).unwrap().1 == Seq::new(32, |i: int| 20u8),
{
    assert(attempt(config(), Seq::new(32, |i: int| 17u8)).unwrap().1 == Seq::new(32, |i: int| 20u8)) by (compute_only);
}
/// Concrete RFC 8446 requirement: join host.
pub proof fn lemma_join_host()
    ensures attempt(config(), Seq::new(32, |i: int| 17u8)).unwrap().0.config.host == seq![104u8],
{
    assert(attempt(config(), Seq::new(32, |i: int| 17u8)).unwrap().0.config.host == seq![104u8]) by (compute_only);
}
/// Concrete RFC 8446 requirement: join time.
pub proof fn lemma_join_time()
    ensures attempt(config(), Seq::new(32, |i: int| 17u8)).unwrap().0.config.now == 7,
{
    assert(attempt(config(), Seq::new(32, |i: int| 17u8)).unwrap().0.config.now == 7) by (compute_only);
}
} // verus!
