//! RFC 8446 §4.1.2, §4.2.1, §4.2.3, §4.2.7 and §4.2.8: the ClientHello of
//! `hello/client_spec.rs` proven equal to the clean-room transcription's
//! `build_client_hello` (`key_exchange.rs`), with RFC 6066 §3's server_name
//! from [`super::host`]: [`theorem_client_hello_equivalence`].
//!
//! For every configuration the crate accepts (`config_ok`):
//! - the first ClientHello is, field for field, `build_client_hello` of the
//!   configuration's Random, session ID, the crate's signature schemes and
//!   its X25519 public value, after the server_name extension (if any);
//! - every ClientHello it sends, the first or the retry's with a cookie,
//!   meets the hello theorem's hypothesis [`super::hello::sent_is_profile`]
//!   with the crate's own `join_spec::extension_types` as the offers, so
//!   that hypothesis is discharged for every state the crate reaches.
//!
//! Not covered here: the transcription's `client_hello_conforms` on the
//! result, and the retry's `second_client_hello` (the ClientHello2 of a
//! cookie-only HelloRetryRequest); both are listed in #139.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A crate ClientHello as the transcription's.
pub open spec fn ch_view(ch: crate::spec::ClientHello) -> crate::transcription::key_exchange::ClientHello {
    crate::transcription::key_exchange::ClientHello {
        legacy_version: ch.legacy_version as nat,
        random: ch.random,
        legacy_session_id: ch.session_id,
        cipher_suites: super::extensions::nats(ch.cipher_suites),
        legacy_compression_methods: ch.compression,
        extensions: super::messages::exts_view(ch.extensions),
    }
}

/// The crate's server_name extension, if its host sends one (the first
/// part of `client_spec::extensions`).
pub open spec fn sni_extensions(c: crate::hello::client_spec::Config) -> Seq<crate::spec::Ext> {
    match crate::host::spec::sni_host_name(c.host) {
        Some(name) => seq![crate::spec::Ext { etype: 0,
            data: crate::spec::write_server_name_ch(seq![crate::spec::ServerName { host_name: name }]) }],
        None => seq![],
    }
}

/// §4.2.8: the crate's one-share KeyShareClientHello is the transcription's,
/// and the transcription reads it back.
pub proof fn lemma_key_share(pk: Seq<u8>)
    requires pk.len() == 32,
    ensures ({
        let shares = seq![crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: pk }];
        let data = crate::transcription::extensions::write_key_share_client_hello(shares);
        &&& crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: pk }]) == data
        &&& crate::transcription::extensions::read_key_share_client_hello(data) == Some(shares)
    }),
{
    let k = crate::spec::KeyShare { group: 29, key_exchange: pk };
    let e = crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: pk };
    let head = seq![0u8, 36u8, 0u8, 29u8, 0u8, 32u8];
    assert(crate::spec::be_bytes(29, 2) =~= seq![0u8, 29u8]) by (compute_only);
    assert(crate::spec::be_bytes(32, 2) =~= seq![0u8, 32u8]) by (compute_only);
    assert(crate::spec::be_bytes(36, 2) =~= seq![0u8, 36u8]) by (compute_only);
    assert(crate::transcription::presentation::uint16(0x001D) =~= seq![0u8, 29u8]) by (compute_only);
    assert(crate::transcription::presentation::encode_uint(32, 2) =~= seq![0u8, 32u8]) by (compute_only);
    assert(crate::transcription::presentation::encode_uint(36, 2) =~= seq![0u8, 36u8]) by (compute_only);
    let wk = crate::spec::write_key_share(k);
    assert(wk =~= seq![0u8, 29u8] + (seq![0u8, 32u8] + pk));
    let w = |x: crate::spec::KeyShare| crate::spec::write_key_share(x);
    assert(seq![k].skip(1) =~= Seq::<crate::spec::KeyShare>::empty());
    assert(crate::spec::write_list(Seq::<crate::spec::KeyShare>::empty(), w) == Seq::<u8>::empty());
    assert(crate::spec::write_list(seq![k], w) == w(k) + crate::spec::write_list(seq![k].skip(1), w));
    assert(crate::spec::write_list(seq![k], w) =~= wk);
    let tl = crate::transcription::extensions::write_key_share_list(seq![e]);
    assert(seq![e].subrange(1, 1) =~= Seq::<crate::transcription::extensions::KeyShareEntry>::empty());
    assert(crate::transcription::extensions::write_key_share_list(Seq::<crate::transcription::extensions::KeyShareEntry>::empty()) == Seq::<u8>::empty());
    assert(crate::transcription::presentation::length_field_width(0xffff) == 2);
    assert(crate::transcription::presentation::write_vector(pk, 0xffff) =~= seq![0u8, 32u8] + pk);
    assert(tl == crate::transcription::presentation::uint16(0x001D) + crate::transcription::presentation::write_vector(pk, 0xffff)
        + crate::transcription::extensions::write_key_share_list(seq![e].subrange(1, 1)));
    assert(tl =~= seq![0u8, 29u8] + (seq![0u8, 32u8] + pk));
    let data = crate::transcription::extensions::write_key_share_client_hello(seq![e]);
    assert(data =~= head + pk);
    assert(crate::spec::write_key_share_ch(seq![k]) =~= head + pk);
    // Reading it back.
    let body = data.subrange(2, 38);
    assert(crate::transcription::presentation::read_uint(data, 2) == 36) by {
        assert(crate::transcription::presentation::read_uint(data, 0) == 0);
        assert(crate::transcription::presentation::read_uint(data, 1) == data[0] as nat);
        assert(data[0] == 0u8 && data[1] == 36u8);
    }
    assert(crate::transcription::presentation::read_vector(data, 0, 0xffff) == Some((body, data.subrange(38, 38))));
    assert(body.subrange(2, 36)[0] == 0u8 && body.subrange(2, 36)[1] == 32u8);
    assert(crate::transcription::presentation::read_uint(body.subrange(2, 36), 2) == 32) by {
        assert(crate::transcription::presentation::read_uint(body.subrange(2, 36), 0) == 0);
        assert(crate::transcription::presentation::read_uint(body.subrange(2, 36), 1) == 0);
    }
    assert(crate::transcription::presentation::read_uint(body, 2) == 29) by {
        assert(crate::transcription::presentation::read_uint(body, 0) == 0);
        assert(crate::transcription::presentation::read_uint(body, 1) == 0);
        assert(body[0] == 0u8 && body[1] == 29u8);
    }
    assert(body.subrange(4, 36) =~= pk);
    assert(body.subrange(36, 36) =~= Seq::<u8>::empty());
    assert(crate::transcription::extensions::read_key_share_list(body.subrange(36, 36)) == Some(Seq::<crate::transcription::extensions::KeyShareEntry>::empty()));
    assert(seq![e] + Seq::<crate::transcription::extensions::KeyShareEntry>::empty() =~= seq![e]);
}

/// The writers of the crate's fixed extension bodies are the
/// transcription's (§4.2.1, §4.2.3, §4.2.7), and the transcription reads
/// the offers back.
pub proof fn lemma_fixed_bodies()
    ensures
        seq![2u8, 3u8, 4u8] == crate::transcription::extensions::write_supported_versions_client(seq![0x0304nat]),
        crate::spec::write_signature_schemes(crate::hello::client_spec::signatures())
            == crate::transcription::extensions::write_signature_scheme_list(super::extensions::nats(crate::hello::client_spec::signatures())),
        seq![0u8, 2u8, 0u8, 29u8] == crate::transcription::extensions::write_named_group_list(seq![0x001Dnat]),
        crate::transcription::extensions::read_supported_versions_client(seq![2u8, 3u8, 4u8]) == Some(seq![0x0304nat]),
        crate::transcription::extensions::read_named_group_list(seq![0u8, 2u8, 0u8, 29u8]) == Some(seq![0x001Dnat]),
{
    assert(seq![2u8, 3u8, 4u8] =~= crate::transcription::extensions::write_supported_versions_client(seq![0x0304nat])) by (compute_only);
    assert(super::extensions::nats(crate::hello::client_spec::signatures())
        =~= seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]);
    assert(crate::spec::write_signature_schemes(crate::hello::client_spec::signatures())
        =~= crate::transcription::extensions::write_signature_scheme_list(
            seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat])) by (compute_only);
    assert(seq![0u8, 2u8, 0u8, 29u8] =~= crate::transcription::extensions::write_named_group_list(seq![0x001Dnat])) by (compute_only);
    assert(crate::transcription::extensions::read_supported_versions_client(seq![2u8, 3u8, 4u8]) == Some(seq![0x0304nat])) by (compute_only);
    assert(crate::transcription::extensions::read_named_group_list(seq![0u8, 2u8, 0u8, 29u8]) == Some(seq![0x001Dnat])) by (compute_only);
}

/// The crate's ClientHello extensions, as the server_name part followed by
/// the four the profile always sends and the retry's cookie.
pub proof fn lemma_extensions_view(c: crate::hello::client_spec::Config, cookie: Seq<u8>)
    ensures ({
        let fixed = seq![
            crate::transcription::extensions::Extension { extension_type: 43, extension_data: seq![2u8, 3u8, 4u8] },
            crate::transcription::extensions::Extension { extension_type: 13,
                extension_data: crate::spec::write_signature_schemes(crate::hello::client_spec::signatures()) },
            crate::transcription::extensions::Extension { extension_type: 10, extension_data: seq![0u8, 2u8, 0u8, 29u8] },
            crate::transcription::extensions::Extension { extension_type: 51,
                extension_data: crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]) },
        ];
        let tail = if cookie.len() == 0 { Seq::<crate::transcription::extensions::Extension>::empty() }
            else { seq![crate::transcription::extensions::Extension { extension_type: 44, extension_data: cookie }] };
        super::messages::exts_view(crate::hello::client_spec::extensions(c, cookie))
            == super::messages::exts_view(sni_extensions(c)) + fixed + tail
    }),
{
    let es = crate::hello::client_spec::extensions(c, cookie);
    let v = super::messages::exts_view(es);
    let s = sni_extensions(c);
    assert(es.len() == s.len() + 4 + (if cookie.len() == 0 { 0int } else { 1int }));
    assert(v =~= super::messages::exts_view(s) + seq![
            crate::transcription::extensions::Extension { extension_type: 43, extension_data: seq![2u8, 3u8, 4u8] },
            crate::transcription::extensions::Extension { extension_type: 13,
                extension_data: crate::spec::write_signature_schemes(crate::hello::client_spec::signatures()) },
            crate::transcription::extensions::Extension { extension_type: 10, extension_data: seq![0u8, 2u8, 0u8, 29u8] },
            crate::transcription::extensions::Extension { extension_type: 51,
                extension_data: crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]) },
        ] + (if cookie.len() == 0 { Seq::<crate::transcription::extensions::Extension>::empty() }
            else { seq![crate::transcription::extensions::Extension { extension_type: 44, extension_data: cookie }] }));
}

/// The first ClientHello is `build_client_hello`'s, field for field.
pub proof fn lemma_first_client_hello(c: crate::hello::client_spec::Config)
    requires crate::hello::client_spec::config_ok(c),
    ensures
        ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()))
            == crate::transcription::key_exchange::build_client_hello(c.random, c.session_id,
                super::extensions::nats(crate::hello::client_spec::signatures()), Some(c.public_key),
                super::messages::exts_view(sni_extensions(c))),
{
    lemma_extensions_view(c, Seq::empty());
    lemma_fixed_bodies();
    lemma_key_share(c.public_key);
    let ch = crate::hello::client_spec::client_hello(c, Seq::empty());
    assert(super::extensions::nats(ch.cipher_suites) =~= seq![0x1303nat]);
    let b = crate::transcription::key_exchange::build_client_hello(c.random, c.session_id,
        super::extensions::nats(crate::hello::client_spec::signatures()), Some(c.public_key),
        super::messages::exts_view(sni_extensions(c)));
    assert(ch_view(ch).extensions =~= b.extensions);
}

/// The types of the crate's extensions are `join_spec::extension_types`.
pub proof fn lemma_types(c: crate::hello::client_spec::Config, cookie: Seq<u8>)
    ensures
        crate::transcription::extensions::extension_types(super::messages::exts_view(crate::hello::client_spec::extensions(c, cookie)))
            == super::extensions::nats(crate::hello::join_spec::extension_types(c, cookie.len() != 0)),
{
    let es = crate::hello::client_spec::extensions(c, cookie);
    super::extensions::lemma_types(es);
    assert(es.map_values(|e: crate::spec::Ext| e.etype as nat)
        =~= super::extensions::nats(crate::hello::join_spec::extension_types(c, cookie.len() != 0)));
}

/// Every ClientHello the crate sends, the first or the retry's, meets the
/// hello theorem's hypothesis, with the crate's own offers.
pub proof fn lemma_sent_is_profile(c: crate::hello::client_spec::Config, cookie: Seq<u8>)
    requires crate::hello::client_spec::config_ok(c),
    ensures
        super::hello::sent_is_profile(ch_view(crate::hello::client_spec::client_hello(c, cookie)), c.session_id,
            crate::hello::join_spec::extension_types(c, cookie.len() != 0)),
{
    let ch = crate::hello::client_spec::client_hello(c, cookie);
    let v = ch_view(ch).extensions;
    lemma_types(c, cookie);
    lemma_fixed_bodies();
    lemma_key_share(c.public_key);
    lemma_extensions_view(c, cookie);
    lemma_offers(c, cookie.len() != 0);
    assert(super::extensions::nats(ch.cipher_suites) =~= seq![0x1303nat]);
    let vs = super::messages::exts_view(sni_extensions(c));
    let ksd = crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]);
    let fixed = seq![
        crate::transcription::extensions::Extension { extension_type: 43, extension_data: seq![2u8, 3u8, 4u8] },
        crate::transcription::extensions::Extension { extension_type: 13,
            extension_data: crate::spec::write_signature_schemes(crate::hello::client_spec::signatures()) },
        crate::transcription::extensions::Extension { extension_type: 10, extension_data: seq![0u8, 2u8, 0u8, 29u8] },
        crate::transcription::extensions::Extension { extension_type: 51, extension_data: ksd },
    ];
    let tail = if cookie.len() == 0 { Seq::<crate::transcription::extensions::Extension>::empty() }
        else { seq![crate::transcription::extensions::Extension { extension_type: 44, extension_data: cookie }] };
    assert(v =~= vs + (fixed + tail));
    lemma_fixed_find(fixed, tail, ksd);
    lemma_sni_find(c, 43);
    lemma_sni_find(c, 10);
    lemma_sni_find(c, 51);
    lemma_find_append(vs, fixed + tail, 43);
    lemma_find_append(vs, fixed + tail, 10);
    lemma_find_append(vs, fixed + tail, 51);
    let shares = seq![crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: c.public_key }];
    assert(crate::transcription::key_exchange::offered_shares(ch_view(ch)) == shares);
    assert(shares.subrange(1, 1) =~= Seq::<crate::transcription::extensions::KeyShareEntry>::empty());
    assert(crate::transcription::extensions::share_groups(Seq::<crate::transcription::extensions::KeyShareEntry>::empty()) == Seq::<nat>::empty());
    assert(crate::transcription::extensions::share_groups(shares) =~= seq![0x001Dnat]);
}

/// `find_extension` over two blocks: the first one's, else the second's.
pub proof fn lemma_find_append(a: Seq<crate::transcription::extensions::Extension>,
    b: Seq<crate::transcription::extensions::Extension>, t: nat)
    ensures
        crate::transcription::extensions::find_extension(a + b, t) == match crate::transcription::extensions::find_extension(a, t) {
            Some(d) => Some(d),
            None => crate::transcription::extensions::find_extension(b, t),
        },
    decreases a.len(),
{
    if a.len() > 0 {
        assert((a + b).subrange(1, (a + b).len() as int) =~= a.subrange(1, a.len() as int) + b);
        lemma_find_append(a.subrange(1, a.len() as int), b, t);
    } else {
        assert(a + b =~= b);
    }
}

/// The server_name part holds no extension but server_name.
pub proof fn lemma_sni_find(c: crate::hello::client_spec::Config, t: nat)
    requires t != 0,
    ensures crate::transcription::extensions::find_extension(super::messages::exts_view(sni_extensions(c)), t) is None,
{
    let s = sni_extensions(c);
    let vs = super::messages::exts_view(s);
    if crate::host::spec::sni_host_name(c.host) is Some {
        assert(s.len() == 1 && s[0].etype == 0);
        assert(vs.len() == 1 && vs[0].extension_type == 0);
        assert(vs.subrange(1, vs.len() as int) =~= Seq::<crate::transcription::extensions::Extension>::empty());
        assert(crate::transcription::extensions::find_extension(Seq::<crate::transcription::extensions::Extension>::empty(), t) is None);
        assert(crate::transcription::extensions::find_extension(vs, t)
            == crate::transcription::extensions::find_extension(vs.subrange(1, vs.len() as int), t));
    } else {
        assert(vs =~= Seq::<crate::transcription::extensions::Extension>::empty());
    }
}

/// The four fixed extensions, found by type.
pub proof fn lemma_fixed_find(fixed: Seq<crate::transcription::extensions::Extension>,
    tail: Seq<crate::transcription::extensions::Extension>, ksd: Seq<u8>)
    requires
        fixed == seq![
            crate::transcription::extensions::Extension { extension_type: 43, extension_data: seq![2u8, 3u8, 4u8] },
            crate::transcription::extensions::Extension { extension_type: 13,
                extension_data: crate::spec::write_signature_schemes(crate::hello::client_spec::signatures()) },
            crate::transcription::extensions::Extension { extension_type: 10, extension_data: seq![0u8, 2u8, 0u8, 29u8] },
            crate::transcription::extensions::Extension { extension_type: 51, extension_data: ksd },
        ],
    ensures
        crate::transcription::extensions::find_extension(fixed + tail, 43) == Some(seq![2u8, 3u8, 4u8]),
        crate::transcription::extensions::find_extension(fixed + tail, 10) == Some(seq![0u8, 2u8, 0u8, 29u8]),
        crate::transcription::extensions::find_extension(fixed + tail, 51) == Some(ksd),
{
    let l = fixed + tail;
    let l1 = l.subrange(1, l.len() as int);
    let l2 = l1.subrange(1, l1.len() as int);
    let l3 = l2.subrange(1, l2.len() as int);
    assert(l[0] == fixed[0]);
    assert(l1[0] == fixed[1]);
    assert(l2[0] == fixed[2]);
    assert(l3[0] == fixed[3]);
    assert(crate::transcription::extensions::find_extension(l3, 51) == Some(ksd));
    assert(crate::transcription::extensions::find_extension(l2, 51) == Some(ksd));
    assert(crate::transcription::extensions::find_extension(l1, 51) == Some(ksd));
    assert(crate::transcription::extensions::find_extension(l2, 10) == Some(seq![0u8, 2u8, 0u8, 29u8]));
    assert(crate::transcription::extensions::find_extension(l1, 10) == Some(seq![0u8, 2u8, 0u8, 29u8]));
}

/// The crate's offers are a `profile_extensions` list with
/// supported_versions and key_share.
pub proof fn lemma_offers(c: crate::hello::client_spec::Config, retried: bool)
    ensures ({
        let offers = crate::hello::join_spec::extension_types(c, retried);
        &&& crate::auth::spec::profile_extensions(offers)
        &&& crate::auth::spec::member(offers, 43)
        &&& crate::auth::spec::member(offers, 51)
    }),
{
    let offers = crate::hello::join_spec::extension_types(c, retried);
    let sni = crate::host::spec::sni_host_name(c.host) is Some;
    let x = if sni && retried { seq![0u16, 43u16, 13u16, 10u16, 51u16, 44u16] }
        else if sni { seq![0u16, 43u16, 13u16, 10u16, 51u16] }
        else if retried { seq![43u16, 13u16, 10u16, 51u16, 44u16] }
        else { seq![43u16, 13u16, 10u16, 51u16] };
    assert(offers =~= x);
    assert(crate::auth::spec::profile_extensions(seq![0u16, 43u16, 13u16, 10u16, 51u16, 44u16])
        && crate::auth::spec::member(seq![0u16, 43u16, 13u16, 10u16, 51u16, 44u16], 43)
        && crate::auth::spec::member(seq![0u16, 43u16, 13u16, 10u16, 51u16, 44u16], 51)) by (compute_only);
    assert(crate::auth::spec::profile_extensions(seq![0u16, 43u16, 13u16, 10u16, 51u16])
        && crate::auth::spec::member(seq![0u16, 43u16, 13u16, 10u16, 51u16], 43)
        && crate::auth::spec::member(seq![0u16, 43u16, 13u16, 10u16, 51u16], 51)) by (compute_only);
    assert(crate::auth::spec::profile_extensions(seq![43u16, 13u16, 10u16, 51u16, 44u16])
        && crate::auth::spec::member(seq![43u16, 13u16, 10u16, 51u16, 44u16], 43)
        && crate::auth::spec::member(seq![43u16, 13u16, 10u16, 51u16, 44u16], 51)) by (compute_only);
    assert(crate::auth::spec::profile_extensions(seq![43u16, 13u16, 10u16, 51u16])
        && crate::auth::spec::member(seq![43u16, 13u16, 10u16, 51u16], 43)
        && crate::auth::spec::member(seq![43u16, 13u16, 10u16, 51u16], 51)) by (compute_only);
}

/// **The client_spec theorem.** For every configuration the crate accepts:
/// its first ClientHello is the transcription's `build_client_hello` of the
/// same inputs, after the server_name extension; and every ClientHello it
/// sends (with any cookie) meets the hello theorem's profile hypothesis.
pub proof fn theorem_client_hello_equivalence()
    ensures
        forall|c: crate::hello::client_spec::Config| #[trigger] crate::hello::client_spec::config_ok(c) ==>
            ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()))
                == crate::transcription::key_exchange::build_client_hello(c.random, c.session_id,
                    super::extensions::nats(crate::hello::client_spec::signatures()), Some(c.public_key),
                    super::messages::exts_view(sni_extensions(c))),
        forall|c: crate::hello::client_spec::Config, cookie: Seq<u8>| crate::hello::client_spec::config_ok(c) ==>
            super::hello::sent_is_profile(ch_view(#[trigger] crate::hello::client_spec::client_hello(c, cookie)), c.session_id,
                crate::hello::join_spec::extension_types(c, cookie.len() != 0)),
{
    assert forall|c: crate::hello::client_spec::Config| #[trigger] crate::hello::client_spec::config_ok(c) implies
        ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()))
            == crate::transcription::key_exchange::build_client_hello(c.random, c.session_id,
                super::extensions::nats(crate::hello::client_spec::signatures()), Some(c.public_key),
                super::messages::exts_view(sni_extensions(c))) by {
        lemma_first_client_hello(c);
    }
    assert forall|c: crate::hello::client_spec::Config, cookie: Seq<u8>| crate::hello::client_spec::config_ok(c) implies
        super::hello::sent_is_profile(ch_view(#[trigger] crate::hello::client_spec::client_hello(c, cookie)), c.session_id,
            crate::hello::join_spec::extension_types(c, cookie.len() != 0)) by {
        lemma_sent_is_profile(c, cookie);
    }
}

} // verus!
