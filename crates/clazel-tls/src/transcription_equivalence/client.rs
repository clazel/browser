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
//!   that hypothesis is discharged for every state the crate reaches;
//! - the first ClientHello meets the transcription's
//!   `client_hello_conforms`, with the crate's signature schemes;
//! - after every first HelloRetryRequest the crate accepts, the
//!   transcription accepts it too and keeps
//!   [`super::hello::profile_retry_record`] of it (§4.2.8 leaves the
//!   profile no group to select, so it has no key_share), and the crate's
//!   ClientHello2 is the transcription's `second_client_hello` and meets
//!   `second_client_hello_conforms` ([`retry_agrees`]).

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
        crate::transcription::extensions::find_extension(fixed + tail, 13)
            == Some(crate::spec::write_signature_schemes(crate::hello::client_spec::signatures())),
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
    assert(crate::transcription::extensions::find_extension(l1, 13)
        == Some(crate::spec::write_signature_schemes(crate::hello::client_spec::signatures())));
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

// ---------------------------------------------------------------------------
// `client_hello_conforms` on the first ClientHello.
// ---------------------------------------------------------------------------

/// Whether some type of the list is one §4.2's table knows, but not for `m`
/// ([`crate::transcription::extensions::any_not_specified`] over the types).
pub open spec fn types_not_specified(types: Seq<nat>, m: crate::transcription::extensions::TableMessage) -> bool
    decreases types.len(),
{
    if types.len() == 0 {
        false
    } else {
        crate::transcription::extensions::recognized_but_not_specified(types[0], m)
            || types_not_specified(types.subrange(1, types.len() as int), m)
    }
}

/// The types of the crate's ClientHello extensions: server_name if the host
/// sends it, the four the profile always sends, and the retry's cookie.
pub open spec fn profile_types(sni: bool, retried: bool) -> Seq<nat> {
    if sni && retried { seq![0nat, 43nat, 13nat, 10nat, 51nat, 44nat] }
    else if sni { seq![0nat, 43nat, 13nat, 10nat, 51nat] }
    else if retried { seq![43nat, 13nat, 10nat, 51nat, 44nat] }
    else { seq![43nat, 13nat, 10nat, 51nat] }
}

/// §4.2's duplicate and table rules, and a miss of `find_extension`, depend
/// only on the types of the block.
pub proof fn lemma_block_by_types(v: Seq<crate::transcription::extensions::Extension>,
    m: crate::transcription::extensions::TableMessage, t: nat)
    ensures
        crate::transcription::extensions::has_duplicate_extension(v)
            == !crate::transcription::extensions::has_no_repeats(crate::transcription::extensions::extension_types(v)),
        crate::transcription::extensions::any_not_specified(v, m)
            == types_not_specified(crate::transcription::extensions::extension_types(v), m),
        !crate::transcription::presentation::list_has(crate::transcription::extensions::extension_types(v), t)
            ==> crate::transcription::extensions::find_extension(v, t) is None,
    decreases v.len(),
{
    if v.len() > 0 {
        let tail = v.subrange(1, v.len() as int);
        lemma_block_by_types(tail, m, t);
        let ty = crate::transcription::extensions::extension_types(v);
        assert(ty == seq![v[0].extension_type] + crate::transcription::extensions::extension_types(tail));
        assert(ty.subrange(1, ty.len() as int) =~= crate::transcription::extensions::extension_types(tail));
        assert(ty[0] == v[0].extension_type);
    }
}

/// The types of the crate's ClientHello extensions, as [`profile_types`].
pub proof fn lemma_profile_types(c: crate::hello::client_spec::Config, cookie: Seq<u8>)
    ensures
        crate::transcription::extensions::extension_types(super::messages::exts_view(crate::hello::client_spec::extensions(c, cookie)))
            == profile_types(crate::host::spec::sni_host_name(c.host) is Some, cookie.len() != 0),
{
    lemma_types(c, cookie);
    let offers = crate::hello::join_spec::extension_types(c, cookie.len() != 0);
    let sni = crate::host::spec::sni_host_name(c.host) is Some;
    let retried = cookie.len() != 0;
    let x = if sni && retried { seq![0u16, 43u16, 13u16, 10u16, 51u16, 44u16] }
        else if sni { seq![0u16, 43u16, 13u16, 10u16, 51u16] }
        else if retried { seq![43u16, 13u16, 10u16, 51u16, 44u16] }
        else { seq![43u16, 13u16, 10u16, 51u16] };
    assert(offers =~= x);
    assert(super::extensions::nats(offers) =~= profile_types(sni, retried));
}

/// The facts about the four lists of [`profile_types`] that the profile's
/// conformance needs, evaluated.
pub proof fn lemma_profile_types_facts(sni: bool)
    ensures ({
        let ty = profile_types(sni, false);
        let ch = crate::transcription::extensions::TableMessage::Ch;
        &&& crate::transcription::extensions::has_no_repeats(ty)
        &&& !types_not_specified(ty, ch)
        &&& !crate::transcription::presentation::list_has(ty, 44nat)
        &&& !crate::transcription::presentation::list_has(ty, 41nat)
        &&& !crate::transcription::presentation::list_has(ty, 45nat)
        &&& !crate::transcription::presentation::list_has(ty, 42nat)
        &&& !crate::transcription::presentation::list_has(ty, 49nat)
        &&& !crate::transcription::presentation::list_has(ty, 19nat)
        &&& !crate::transcription::presentation::list_has(ty, 20nat)
    }),
{
    let ch = crate::transcription::extensions::TableMessage::Ch;
    let e = Seq::<nat>::empty();
    let l51 = seq![51nat] + e;
    let l10 = seq![10nat] + l51;
    let l13 = seq![13nat] + l10;
    let l43 = seq![43nat] + l13;
    let l0 = seq![0nat] + l43;
    lemma_cons(51, e, ch);
    lemma_cons(10, l51, ch);
    lemma_cons(13, l10, ch);
    lemma_cons(43, l13, ch);
    lemma_cons(0, l43, ch);
    assert(forall|v: nat| !crate::transcription::presentation::list_has(e, v));
    assert(crate::transcription::extensions::has_no_repeats(e));
    assert(!types_not_specified(e, ch));
    // §4.2's table, by the crate's evaluated `extension_allowed` and
    // [`super::extensions::lemma_table`].
    assert(super::extensions::table_message(crate::spec::MsgKind::Ch) == ch);
    super::extensions::lemma_table(0, crate::spec::MsgKind::Ch);
    super::extensions::lemma_table(43, crate::spec::MsgKind::Ch);
    super::extensions::lemma_table(13, crate::spec::MsgKind::Ch);
    super::extensions::lemma_table(10, crate::spec::MsgKind::Ch);
    super::extensions::lemma_table(51, crate::spec::MsgKind::Ch);
    assert(crate::spec::extension_allowed(0, crate::spec::MsgKind::Ch)) by (compute_only);
    assert(crate::spec::extension_allowed(43, crate::spec::MsgKind::Ch)) by (compute_only);
    assert(crate::spec::extension_allowed(13, crate::spec::MsgKind::Ch)) by (compute_only);
    assert(crate::spec::extension_allowed(10, crate::spec::MsgKind::Ch)) by (compute_only);
    assert(crate::spec::extension_allowed(51, crate::spec::MsgKind::Ch)) by (compute_only);
    assert(profile_types(true, false) =~= l0);
    assert(profile_types(false, false) =~= l43);
}

/// One step of `list_has`, `has_no_repeats` and [`types_not_specified`]
/// on a list with a first element.
pub proof fn lemma_cons(t: nat, rest: Seq<nat>, m: crate::transcription::extensions::TableMessage)
    ensures
        forall|v: nat| #[trigger] crate::transcription::presentation::list_has(seq![t] + rest, v)
            == (t == v || crate::transcription::presentation::list_has(rest, v)),
        crate::transcription::extensions::has_no_repeats(seq![t] + rest)
            == (!crate::transcription::presentation::list_has(rest, t) && crate::transcription::extensions::has_no_repeats(rest)),
        types_not_specified(seq![t] + rest, m)
            == (crate::transcription::extensions::recognized_but_not_specified(t, m) || types_not_specified(rest, m)),
{
    let s = seq![t] + rest;
    assert(s.subrange(1, s.len() as int) =~= rest);
    assert(s[0] == t);
}

/// §4.1.2, §4.2, §4.2.1, §4.2.3, §4.2.7, §4.2.8, §9.2: the crate's first
/// ClientHello meets the transcription's `client_hello_conforms`, with the
/// crate's signature schemes as the parameter.
pub proof fn lemma_first_conforms(c: crate::hello::client_spec::Config)
    requires crate::hello::client_spec::config_ok(c),
    ensures
        crate::transcription::key_exchange::client_hello_conforms(
            ch_view(crate::hello::client_spec::client_hello(c, Seq::empty())),
            super::extensions::nats(crate::hello::client_spec::signatures())),
{
    let cookie = Seq::<u8>::empty();
    let ch = crate::hello::client_spec::client_hello(c, cookie);
    let h = ch_view(ch);
    let v = h.extensions;
    let tm = crate::transcription::extensions::TableMessage::Ch;
    lemma_sent_is_profile(c, cookie);
    lemma_profile_types(c, cookie);
    lemma_profile_types_facts(crate::host::spec::sni_host_name(c.host) is Some);
    lemma_block_by_types(v, tm, 44);
    lemma_block_by_types(v, tm, 41);
    lemma_block_by_types(v, tm, 45);
    lemma_block_by_types(v, tm, 42);
    lemma_block_by_types(v, tm, 49);
    lemma_block_by_types(v, tm, 19);
    lemma_block_by_types(v, tm, 20);
    // The fields.
    assert(super::extensions::nats(ch.cipher_suites) =~= seq![0x1303nat]);
    // signature_algorithms and key_share, found.
    lemma_fixed_bodies();
    lemma_key_share(c.public_key);
    lemma_extensions_view(c, cookie);
    let vs = super::messages::exts_view(sni_extensions(c));
    let ksd = crate::spec::write_key_share_ch(seq![crate::spec::KeyShare { group: 29, key_exchange: c.public_key }]);
    let fixed = seq![
        crate::transcription::extensions::Extension { extension_type: 43, extension_data: seq![2u8, 3u8, 4u8] },
        crate::transcription::extensions::Extension { extension_type: 13,
            extension_data: crate::spec::write_signature_schemes(crate::hello::client_spec::signatures()) },
        crate::transcription::extensions::Extension { extension_type: 10, extension_data: seq![0u8, 2u8, 0u8, 29u8] },
        crate::transcription::extensions::Extension { extension_type: 51, extension_data: ksd },
    ];
    let tail = Seq::<crate::transcription::extensions::Extension>::empty();
    assert(v =~= vs + (fixed + tail));
    lemma_fixed_find(fixed, tail, ksd);
    lemma_sni_find(c, 13);
    lemma_sni_find(c, 51);
    lemma_find_append(vs, fixed + tail, 13);
    lemma_find_append(vs, fixed + tail, 51);
    let schemes = seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat];
    assert(super::extensions::nats(crate::hello::client_spec::signatures()) =~= schemes);
    // Evaluated on the literal list (a `let`-bound name stays symbolic in
    // `compute_only`).
    assert(crate::transcription::extensions::read_signature_scheme_list(
        crate::transcription::extensions::write_signature_scheme_list(
            seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]))
        == Some(seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]))
        by (compute_only);
    assert(crate::transcription::extensions::legacy_schemes_are_last(
        seq![0x0403nat, 0x0503nat, 0x0804nat, 0x0805nat, 0x0806nat, 0x0807nat, 0x0401nat, 0x0501nat, 0x0601nat]))
        by (compute_only);
    let shares = seq![crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: c.public_key }];
    assert(crate::transcription::key_exchange::offered_shares(h) == shares);
    assert(shares.subrange(1, 1) =~= Seq::<crate::transcription::extensions::KeyShareEntry>::empty());
    assert(crate::transcription::extensions::share_groups(Seq::<crate::transcription::extensions::KeyShareEntry>::empty()) == Seq::<nat>::empty());
    assert(crate::transcription::extensions::share_groups(shares) =~= seq![0x001Dnat]);
    let x = seq![0x001Dnat];
    assert(x.subrange(1, 1) =~= Seq::<nat>::empty());
    assert(crate::transcription::extensions::is_subsequence(Seq::<nat>::empty(), Seq::<nat>::empty()));
    assert(crate::transcription::extensions::is_subsequence(x, x));
    assert(!crate::transcription::presentation::list_has(Seq::<nat>::empty(), 0x001Dnat));
    assert(crate::transcription::extensions::has_no_repeats(Seq::<nat>::empty()));
    assert(crate::transcription::extensions::has_no_repeats(x));
}

// ---------------------------------------------------------------------------
// ClientHello2 against `second_client_hello`.
// ---------------------------------------------------------------------------

/// §4.1.4, §4.2.2, §4.2.8: a first HelloRetryRequest the transcription
/// accepts in answer to a ClientHello of the profile carries no key_share
/// (§4.2.8's two checks rule out every group: X25519 is the one offered,
/// and it is already shared), so the record kept of it is
/// [`super::hello::profile_retry_record`]; and its cookie, if any, reads.
pub proof fn lemma_retry_accepted(sent: crate::transcription::key_exchange::ClientHello, session_id: Seq<u8>,
    offers: Seq<u16>, h: crate::transcription::key_exchange::ServerHello)
    requires
        super::hello::sent_is_profile(sent, session_id, offers),
        crate::transcription::key_exchange::hello_retry_request_failures(sent, h).len() == 0,
    ensures
        crate::transcription::extensions::find_extension(h.extensions, 51) is None,
        crate::transcription::key_exchange::retry_record(h) == super::hello::profile_retry_record(),
        crate::transcription::extensions::find_extension(h.extensions, 44) is Some ==>
            crate::transcription::extensions::read_cookie(crate::transcription::extensions::find_extension(h.extensions, 44)->0) is Some,
{
    reveal_with_fuel(crate::transcription::presentation::list_has, 2);
    let a = crate::transcription::alerts::fails_if(h.legacy_version == 0x0300, crate::transcription::alerts::ClientError::VersionNotSupported);
    let a2 = crate::transcription::alerts::fails_if(h.legacy_version != 0x0303, crate::transcription::alerts::ClientError::RetryLegacyVersion);
    let c1 = crate::transcription::alerts::fails_if(h.legacy_session_id_echo != sent.legacy_session_id,
        crate::transcription::alerts::ClientError::SessionIdEchoMismatch);
    let c2 = crate::transcription::alerts::fails_if(!crate::transcription::presentation::list_has(sent.cipher_suites, h.cipher_suite),
        crate::transcription::alerts::ClientError::CipherSuiteNotOffered);
    let c3 = crate::transcription::alerts::fails_if(h.legacy_compression_method != 0,
        crate::transcription::alerts::ClientError::CompressionMethodNotZero);
    let b = match crate::transcription::extensions::find_extension(h.extensions, 43) {
        None => seq![crate::transcription::alerts::ClientError::SupportedVersionsMissing],
        Some(data) => crate::transcription::key_exchange::selected_version_failures(sent, data),
    };
    let rb = crate::transcription::extensions::response_block_failures(h.extensions,
        crate::transcription::extensions::extension_types(sent.extensions), crate::transcription::extensions::TableMessage::Hrr);
    let ck = match crate::transcription::extensions::find_extension(h.extensions, 44) {
        None => Seq::<crate::transcription::alerts::ClientError>::empty(),
        Some(data) => crate::transcription::alerts::fails_if(crate::transcription::extensions::read_cookie(data) is None,
            crate::transcription::alerts::ClientError::Malformed),
    };
    let ks = match crate::transcription::extensions::find_extension(h.extensions, 51) {
        None => Seq::<crate::transcription::alerts::ClientError>::empty(),
        Some(data) => match crate::transcription::extensions::read_key_share_hello_retry_request(data) {
            None => seq![crate::transcription::alerts::ClientError::Malformed],
            Some(selected_group) =>
                crate::transcription::alerts::fails_if(!crate::transcription::presentation::list_has(
                    crate::transcription::key_exchange::offered_groups(sent), selected_group),
                    crate::transcription::alerts::ClientError::RetryGroupNotOffered)
                + crate::transcription::alerts::fails_if(crate::transcription::presentation::list_has(
                    crate::transcription::extensions::share_groups(crate::transcription::key_exchange::offered_shares(sent)), selected_group),
                    crate::transcription::alerts::ClientError::RetryGroupAlreadyShared),
        },
    };
    let rc = crate::transcription::alerts::fails_if(crate::transcription::key_exchange::retry_changes_nothing(h),
        crate::transcription::alerts::ClientError::RetryWithoutChange);
    assert(crate::transcription::key_exchange::hello_field_failures(sent, h) == c1 + c2 + c3);
    assert(crate::transcription::key_exchange::hello_retry_request_failures(sent, h) == a + a2 + (c1 + c2 + c3) + b + rb + ck + ks + rc);
    assert(c2.len() == 0 && b.len() == 0 && ck.len() == 0 && ks.len() == 0);
    // §4.1.3 cipher_suite: the one offered.
    assert(seq![0x1303nat].subrange(1, 1) =~= Seq::<nat>::empty());
    assert(crate::transcription::presentation::list_has(seq![0x1303nat], h.cipher_suite));
    assert(h.cipher_suite == 0x1303);
    // §4.2.1 selected_version: the one offered.
    assert(seq![0x0304nat].subrange(1, 1) =~= Seq::<nat>::empty());
    match crate::transcription::extensions::find_extension(h.extensions, 43) {
        None => {},
        Some(data) => {
            match crate::transcription::extensions::read_supported_versions_server(data) {
                None => {},
                Some(v) => {
                    assert(crate::transcription::presentation::list_has(seq![0x0304nat], v));
                    assert(v == 0x0304);
                },
            }
        },
    }
    // §4.2.8: no group is left to select.
    assert(seq![0x001Dnat].subrange(1, 1) =~= Seq::<nat>::empty());
    match crate::transcription::extensions::find_extension(h.extensions, 51) {
        None => {},
        Some(data) => {
            match crate::transcription::extensions::read_key_share_hello_retry_request(data) {
                None => {},
                Some(g) => {
                    if g == 0x001D {
                        assert(crate::transcription::presentation::list_has(seq![0x001Dnat], g));
                    } else {
                        assert(!crate::transcription::presentation::list_has(seq![0x001Dnat], g));
                    }
                    assert(ks.len() > 0);
                },
            }
        },
    }
}

/// `replace_key_share` with no new share changes nothing.
pub proof fn lemma_replace_none(es: Seq<crate::transcription::extensions::Extension>)
    ensures crate::transcription::key_exchange::replace_key_share(es, None) == es,
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_replace_none(es.subrange(1, es.len() as int));
        assert(seq![es[0]] + es.subrange(1, es.len() as int) =~= es);
    }
}

/// `without_retry_changes` over two blocks is the two results joined.
pub proof fn lemma_without_retry_changes_append(a: Seq<crate::transcription::extensions::Extension>,
    b: Seq<crate::transcription::extensions::Extension>)
    ensures
        crate::transcription::key_exchange::without_retry_changes(a + b)
            == crate::transcription::key_exchange::without_retry_changes(a) + crate::transcription::key_exchange::without_retry_changes(b),
    decreases a.len(),
{
    if a.len() > 0 {
        let at = a.subrange(1, a.len() as int);
        assert((a + b).subrange(1, (a + b).len() as int) =~= at + b);
        assert((a + b)[0] == a[0]);
        lemma_without_retry_changes_append(at, b);
        let wa = crate::transcription::key_exchange::without_retry_changes(at);
        let wb = crate::transcription::key_exchange::without_retry_changes(b);
        assert(seq![a[0]] + (wa + wb) =~= (seq![a[0]] + wa) + wb);
    } else {
        assert(a + b =~= b);
        assert(Seq::<crate::transcription::extensions::Extension>::empty() + crate::transcription::key_exchange::without_retry_changes(b)
            =~= crate::transcription::key_exchange::without_retry_changes(b));
    }
}

/// §4.1.2: after a HelloRetryRequest with a cookie and no key_share, the
/// crate's ClientHello2 is the transcription's `second_client_hello` of its
/// first ClientHello (for any new public value, which a request without
/// key_share leaves unused), and meets `second_client_hello_conforms`.
pub proof fn lemma_second_client_hello(c: crate::hello::client_spec::Config, cookie: Seq<u8>,
    retry_extensions: Seq<crate::transcription::extensions::Extension>, public_key: Seq<u8>)
    requires
        cookie.len() > 0,
        crate::transcription::extensions::find_extension(retry_extensions, 51) is None,
        crate::transcription::extensions::find_extension(retry_extensions, 44) == Some(cookie),
    ensures ({
        let first = ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
        let second = ch_view(crate::hello::client_spec::client_hello(c, cookie));
        &&& second == crate::transcription::key_exchange::second_client_hello(first, retry_extensions, public_key)
        &&& crate::transcription::key_exchange::second_client_hello_conforms(first, retry_extensions, second)
    }),
{
    let first = ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
    let second = ch_view(crate::hello::client_spec::client_hello(c, cookie));
    lemma_extensions_view(c, Seq::empty());
    lemma_extensions_view(c, cookie);
    let v1 = first.extensions;
    let v2 = second.extensions;
    let ck = seq![crate::transcription::extensions::Extension { extension_type: 44, extension_data: cookie }];
    assert(v2 =~= v1 + ck);
    lemma_replace_none(v1);
    let built = crate::transcription::key_exchange::second_client_hello(first, retry_extensions, public_key);
    assert(built.extensions =~= v2);
    assert(second == built);
    // Everything but the cookie is unchanged, in the same order.
    lemma_without_retry_changes_append(v1, ck);
    assert(ck.subrange(1, 1) =~= Seq::<crate::transcription::extensions::Extension>::empty());
    assert(crate::transcription::key_exchange::without_retry_changes(Seq::<crate::transcription::extensions::Extension>::empty())
        == Seq::<crate::transcription::extensions::Extension>::empty());
    assert(crate::transcription::key_exchange::without_retry_changes(ck) =~= Seq::<crate::transcription::extensions::Extension>::empty());
    assert(crate::transcription::key_exchange::without_retry_changes(v1) + Seq::<crate::transcription::extensions::Extension>::empty()
        =~= crate::transcription::key_exchange::without_retry_changes(v1));
    // key_share unchanged, and the cookie copied.
    lemma_find_append(v1, ck, 51);
    lemma_find_append(v1, ck, 44);
    assert(crate::transcription::extensions::find_extension(Seq::<crate::transcription::extensions::Extension>::empty(), 51) is None);
    assert(crate::transcription::extensions::find_extension(ck, 51)
        == crate::transcription::extensions::find_extension(ck.subrange(1, 1), 51));
    assert(crate::transcription::extensions::find_extension(ck, 44) == Some(cookie));
    lemma_profile_types(c, Seq::empty());
    lemma_profile_types_facts(crate::host::spec::sni_host_name(c.host) is Some);
    lemma_block_by_types(v1, crate::transcription::extensions::TableMessage::Ch, 44);
}

/// What the crate does with a first HelloRetryRequest it accepts, in the
/// transcription's terms: the body is a HelloRetryRequest the
/// transcription accepts, the record it keeps is
/// [`super::hello::profile_retry_record`], and the crate's ClientHello2 is
/// `second_client_hello` and conforms.
pub open spec fn retry_agrees(c: crate::hello::client_spec::Config, body: Seq<u8>, public_key: Seq<u8>) -> bool {
    match crate::hello::spec::validate(c.session_id, false, body) {
        Ok(crate::hello::spec::Selection::Retry(cookie)) => {
            let first = ch_view(crate::hello::client_spec::client_hello(c, Seq::empty()));
            let second = ch_view(crate::hello::client_spec::client_hello(c, cookie));
            match crate::transcription::key_exchange::read_server_hello(body) {
                None => false,
                Some(h) => {
                    &&& crate::transcription::key_exchange::is_hello_retry_request(h)
                    &&& crate::transcription::key_exchange::hello_retry_request_failures(first, h).len() == 0
                    &&& crate::transcription::key_exchange::retry_record(h) == super::hello::profile_retry_record()
                    &&& second == crate::transcription::key_exchange::second_client_hello(first, h.extensions, public_key)
                    &&& crate::transcription::key_exchange::second_client_hello_conforms(first, h.extensions, second)
                },
            }
        },
        _ => true,
    }
}

/// [`retry_agrees`], for one configuration and body.
pub proof fn lemma_retry(c: crate::hello::client_spec::Config, body: Seq<u8>, public_key: Seq<u8>)
    requires
        crate::hello::client_spec::config_ok(c),
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures retry_agrees(c, body, public_key),
{
    let empty = Seq::<u8>::empty();
    let sent = ch_view(crate::hello::client_spec::client_hello(c, empty));
    let offers = crate::hello::join_spec::extension_types(c, false);
    lemma_sent_is_profile(c, empty);
    assert(super::hello::sent_is_profile(sent, c.session_id, offers));
    assert(super::hello::retry_is_profile(false, None));
    super::hello::lemma_validate(sent, None, offers, c.session_id, false, body);
    super::hello::lemma_read_server_hello(body);
    match crate::hello::spec::validate(c.session_id, false, body) {
        Ok(crate::hello::spec::Selection::Retry(cookie)) => {
            let h = crate::transcription::key_exchange::read_server_hello(body)->Some_0;
            assert(crate::spec::read_server_hello(body) is Some);
            assert(crate::transcription::key_exchange::read_server_hello_any_version(body) == Some(h));
            let hrr = crate::transcription::key_exchange::hello_retry_request_failures(sent, h);
            assert(crate::transcription::alerts::fails_if(false, crate::transcription::alerts::ClientError::SecondHelloRetryRequest)
                =~= Seq::<crate::transcription::alerts::ClientError>::empty());
            assert(super::hello::hello_failures(sent, None, body)
                == crate::transcription::alerts::fails_if(false, crate::transcription::alerts::ClientError::SecondHelloRetryRequest) + hrr);
            assert(hrr.len() == 0);
            lemma_retry_accepted(sent, c.session_id, offers, h);
            assert(crate::transcription::presentation::length_field_width(0xffff) == 2);
            assert(cookie.len() > 0);
            lemma_second_client_hello(c, cookie, h.extensions, public_key);
        },
        _ => {},
    }
}

/// **The client_spec theorem.** For every configuration the crate accepts:
/// its first ClientHello is the transcription's `build_client_hello` of the
/// same inputs, after the server_name extension, and meets
/// `client_hello_conforms`; every ClientHello it sends (with any cookie)
/// meets the hello theorem's profile hypothesis; and after every first
/// HelloRetryRequest it accepts, the transcription accepts it too, keeps
/// [`super::hello::profile_retry_record`] of it, and its ClientHello2 is
/// the crate's ([`retry_agrees`]).
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
        forall|c: crate::hello::client_spec::Config| #[trigger] crate::hello::client_spec::config_ok(c) ==>
            crate::transcription::key_exchange::client_hello_conforms(
                ch_view(crate::hello::client_spec::client_hello(c, Seq::empty())),
                super::extensions::nats(crate::hello::client_spec::signatures())),
        forall|c: crate::hello::client_spec::Config, body: Seq<u8>, public_key: Seq<u8>|
            crate::hello::client_spec::config_ok(c) && body.len() <= crate::transcript::spec::MAX_BODY
            ==> #[trigger] retry_agrees(c, body, public_key),
{
    assert forall|c: crate::hello::client_spec::Config| #[trigger] crate::hello::client_spec::config_ok(c) implies
        crate::transcription::key_exchange::client_hello_conforms(
            ch_view(crate::hello::client_spec::client_hello(c, Seq::empty())),
            super::extensions::nats(crate::hello::client_spec::signatures())) by {
        lemma_first_conforms(c);
    }
    assert forall|c: crate::hello::client_spec::Config, body: Seq<u8>, public_key: Seq<u8>|
        crate::hello::client_spec::config_ok(c) && body.len() <= crate::transcript::spec::MAX_BODY
        implies #[trigger] retry_agrees(c, body, public_key) by {
        lemma_retry(c, body, public_key);
    }
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
