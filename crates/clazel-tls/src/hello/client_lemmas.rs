//! Encoding bounds and retained-configuration properties of the Hello exchange.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// The final ClientHello's encoded extension types are exactly the auth offers.
pub proof fn lemma_offer_binding(c: super::client_spec::Config, cookie: Seq<u8>)
    ensures super::client_spec::extensions(c, cookie).map_values(|e: crate::spec::Ext| e.etype)
        == super::join_spec::extension_types(c, cookie.len() > 0),
{
    assert(super::client_spec::extensions(c, cookie).map_values(|e: crate::spec::Ext| e.etype)
        =~= super::join_spec::extension_types(c, cookie.len() > 0));
}
/// The recursive zero test is exactly the existence of a nonzero octet.
pub proof fn lemma_nonzero_exists(bytes: Seq<u8>)
    ensures super::join_spec::nonzero(bytes) == (exists|i: int| 0 <= i < bytes.len() && #[trigger] bytes[i] != 0),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        let prefix = bytes.drop_last();
        lemma_nonzero_exists(prefix);
        if bytes.last() != 0 { assert(bytes[bytes.len() - 1] != 0); }
        else if super::join_spec::nonzero(prefix) {
            let i = choose|i: int| 0 <= i < prefix.len() && #[trigger] prefix[i] != 0;
            assert(bytes[i] == prefix[i]);
        } else {
            assert forall|i: int| 0 <= i < bytes.len() implies #[trigger] bytes[i] == 0 by {
                if i < prefix.len() { assert(bytes[i] == prefix[i]); }
                else { assert(i == bytes.len() - 1); }
            }
        }
    }
}
/// An established authentication state retains the exact Hello target and prefix.
pub proof fn lemma_auth_binding(c: crate::schedule::spec::Crypto, k: super::join_spec::KeyExchange,
    config: super::client_spec::Config, transcript: crate::transcript::spec::State,
    peer: Seq<u8>, private_key: Seq<u8>, auth: crate::auth::spec::State, master: Seq<u8>)
    requires super::join_spec::into_auth(c, k, config, transcript, peer, private_key) == Ok((auth, master)),
    ensures auth.config.host == config.host, auth.config.now == config.now,
        auth.transcript == transcript, auth.phase == crate::auth::spec::Phase::EncryptedExtensions,
        private_key.len() == 32, (k.public_key)(private_key) == config.public_key,
        (k.shared_secret)(private_key, peer) is Some,
        super::join_spec::nonzero((k.shared_secret)(private_key, peer).unwrap()),
{}
/// A successful retry changes the transcript/flight but never the captured configuration.
pub proof fn lemma_retry_configuration(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: super::client_spec::State,
    server: Seq<u8>, cookie: Seq<u8>, next: super::client_spec::State, flight: Seq<u8>)
    requires super::client_spec::retry(hash, s, server, cookie) == Ok(super::client_spec::Outcome::Retry(next, flight)),
    ensures next.config == s.config, next.transcript.retried,
        flight == crate::spec::write_handshake(1, super::client_spec::body(s.config, cookie)),
{}
/// §3.4: a vector encoding adds its prescribed length width.
pub proof fn lemma_vec_len(bytes: Seq<u8>, ceiling: nat)
    ensures crate::spec::write_vec(bytes, ceiling).len() == bytes.len() + crate::spec::len_width(ceiling),
{
    crate::lemmas_pl::lemma_be_bytes_len(bytes.len(), crate::spec::len_width(ceiling));
}
/// Encoded extension lengths, including type and length prefixes.
pub open spec fn extension_len(es: Seq<crate::spec::Ext>) -> nat
    decreases es.len(),
{
    if es.len() == 0 { 0 } else { 4 + es[0].data.len() + extension_len(es.skip(1)) }
}
/// §4.2: every extension adds a two-byte type and two-byte length.
pub proof fn lemma_extensions_len(es: Seq<crate::spec::Ext>)
    ensures crate::spec::write_list(es, |e: crate::spec::Ext| crate::spec::write_ext(e)).len() == extension_len(es),
    decreases es.len(),
{
    if es.len() > 0 {
        crate::lemmas_pl::lemma_be_bytes_len(es[0].etype as nat, 2);
        lemma_vec_len(es[0].data, 65535);
        lemma_extensions_len(es.skip(1));
    }
}
/// §4.1.2/§4.2: the fixed profile always fits the existing checked encoder.
pub proof fn lemma_profile(c: super::client_spec::Config, cookie: Seq<u8>)
    requires super::client_spec::config_ok(c), cookie.len() <= super::client_spec::MAX_COOKIE,
    ensures crate::contract::client_hello_requires(super::client_spec::client_hello(c, cookie)),
        super::client_spec::body(c, cookie).len() <= 4524,
{
    reveal_with_fuel(crate::spec::write_list, 4);
    let sni = crate::spec::write_server_name_ch(seq![crate::spec::ServerName { host_name: c.host }]);
    let key = crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]);
    lemma_vec_len(c.host, 65535);
    lemma_vec_len(seq![0u8] + crate::spec::write_vec(c.host, 65535), 65535);
    assert(sni.len() == c.host.len() + 5);
    crate::lemmas_pl::lemma_be_bytes_len(29, 2);
    lemma_vec_len(c.public_key, 65535);
    lemma_vec_len(crate::spec::write_key_share(crate::spec::KeyShare { group: 29, key_exchange: c.public_key }), 65535);
    assert(key.len() == 38);
    assert(crate::spec::write_signature_schemes(super::client_spec::signatures()).len() == 18) by (compute_only);
    let es = super::client_spec::extensions(c, cookie);
    reveal_with_fuel(extension_len, 8);
    lemma_extensions_len(es);
    assert(extension_len(es) == 79 + (if c.send_sni { c.host.len() + 9 } else { 0 })
        + (if cookie.len() == 0 { 0 } else { cookie.len() + 4 }));
    assert forall|i: int| 0 <= i < es.len() implies (#[trigger] es[i]).data.len() <= 65535 by {
        if c.send_sni { if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} }
        else { if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} }
    }
    assert(crate::contract::client_hello_requires(super::client_spec::client_hello(c, cookie)));
    crate::lemmas_pl::lemma_be_bytes_len(0x0303, 2);
    lemma_vec_len(c.session_id, 32);
    assert(crate::spec::write_u16s(seq![0x1303u16]) == seq![19u8, 3u8]) by (compute_only);
    lemma_vec_len(seq![19u8, 3u8], 65534);
    lemma_vec_len(seq![0u8], 255);
    lemma_vec_len(crate::spec::write_list(es, |e: crate::spec::Ext| crate::spec::write_ext(e)), 65535);
}
/// §4.1.2: retry leaves every field except the cookie extension unchanged.
pub proof fn lemma_retry_fields(c: super::client_spec::Config, cookie: Seq<u8>)
    ensures super::client_spec::client_hello(c, cookie).random == super::client_spec::client_hello(c, seq![]).random,
        super::client_spec::client_hello(c, cookie).session_id == c.session_id,
        super::client_spec::client_hello(c, cookie).cipher_suites == seq![0x1303u16],
        super::client_spec::extensions(c, cookie).take(super::client_spec::extensions(c, seq![]).len() as int)
            == super::client_spec::extensions(c, seq![]),
{
    assert(super::client_spec::extensions(c, cookie).take(super::client_spec::extensions(c, seq![]).len() as int)
        =~= super::client_spec::extensions(c, seq![]));
}
} // verus!
