//! RFC 8446 §4.1.3, §4.1.4, §4.2.1, §4.2.2 and §4.2.8: `hello/spec.rs`'s
//! `validate`, the client's acceptance of one ServerHello or
//! HelloRetryRequest body, proven equal to the clean-room transcription's
//! `receive_server_hello` in WAIT_SH: [`theorem_hello_equivalence`].
//!
//! The transcription's applicable failures of a body are its own lists,
//! composed as `receive_server_hello` composes them ([`hello_failures`]):
//! `[Malformed]` if `read_server_hello_any_version` fails; for a
//! HelloRetryRequest, `SecondHelloRetryRequest` if a retry came before,
//! followed by `hello_retry_request_failures` of `read_server_hello` (or
//! `[Malformed]`); without supported_versions, `older_server_hello_failures`;
//! otherwise `server_hello_failures`. [`lemma_receive`] proves that
//! `receive_server_hello` aborts with the first of them, and otherwise
//! accepts. The ServerHello's extension bodies are in that list
//! (`extension_body_failures`), and the HelloRetryRequest's are checked
//! inline by `hello_retry_request_failures`; both are compared here.
//!
//! How rejections are compared (the maintainer's decision on #139): the
//! crate rejects exactly when the transcription does, and the crate's alert
//! is that of *some* failure in the list ([`super::auth_flight::alert_in`]).
//! The crate checks the extension block (duplicates, the table, the bodies)
//! while parsing, before the version and the fields, so the orders differ.
//! On acceptance, the selection is the same: the cookie's `extension_data`,
//! or the server's X25519 `key_exchange`.
//!
//! Two conditions on the state the two sides are in, each a fact of the
//! client's own ClientHello (`hello/client_spec.rs`), not of the input.
//! Neither is left as a hypothesis: [`super::client`] proves the first for
//! every ClientHello the crate sends (`lemma_sent_is_profile`), and
//! [`super::negotiation`] proves both for every state the crate's
//! negotiation controller reaches (`negotiation_agrees`), which
//! [`super::bootstrap`] carries through the record layer:
//! - [`sent_is_profile`]: the transcription's ClientHello offers what the
//!   crate's profile offers: the crate's session ID, TLS 1.3 only,
//!   TLS_CHACHA20_POLY1305_SHA256 only, X25519 only with one X25519 share,
//!   and the extension types of a `profile_extensions` list that includes
//!   supported_versions and key_share.
//! - [`retry_is_profile`]: a retry came exactly when the crate's `retried`
//!   says so, and the record the transcription kept of it is that of a
//!   HelloRetryRequest this profile accepts (`{0x1303, 0x0304, None}`: the
//!   crate accepts only a cookie-only HelloRetryRequest, since any
//!   key_share in one names an unoffered group or the one already shared).
//!
//! Domain: the crate's resource policy does not fire (a body of at most
//! `MAX_BODY` octets) and its session ID has at most 32 bytes, which
//! `client_spec::config_ok` guarantees.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A crate ServerHello as the transcription's.
pub open spec fn sh_view(sh: crate::spec::ServerHello) -> crate::transcription::key_exchange::ServerHello {
    crate::transcription::key_exchange::ServerHello {
        legacy_version: sh.legacy_version as nat,
        random: sh.random,
        legacy_session_id_echo: sh.session_id_echo,
        cipher_suite: sh.cipher_suite as nat,
        legacy_compression_method: sh.compression as nat,
        extensions: super::messages::exts_view(sh.extensions),
    }
}

/// The crate's ServerHello fields before `extensions` (with none), and the
/// bytes after them: the prefix that `read_server_hello` and the legacy
/// preflight share.
pub open spec fn crate_prefix(b: Seq<u8>) -> Option<(crate::spec::ServerHello, Seq<u8>)> {
    match crate::spec::read_uint(b, 2) {
        None => None,
        Some((ver, r1)) => match crate::spec::read_fixed(r1, 32) {
            None => None,
            Some((random, r2)) => match crate::spec::read_vec(r2, 0, 32) {
                None => None,
                Some((sid, r3)) => match crate::spec::read_uint(r3, 2) {
                    None => None,
                    Some((cs, r4)) => match crate::spec::read_uint(r4, 1) {
                        None => None,
                        Some((comp, r5)) => Some((
                            crate::spec::ServerHello {
                                legacy_version: ver as u16,
                                random,
                                session_id_echo: sid,
                                cipher_suite: cs as u16,
                                compression: comp as u8,
                                extensions: Seq::empty(),
                            },
                            r5,
                        )),
                    },
                },
            },
        },
    }
}

/// Two bytes read as a `uint16` fit in one.
pub proof fn lemma_uint16(b: Seq<u8>)
    requires b.len() >= 2,
    ensures
        crate::transcription::presentation::read_uint(b, 2) < 0x10000,
        crate::transcription::presentation::read_uint(b, 1) == b[0] as nat,
{
    let v = crate::transcription::presentation::read_uint(b, 2);
    assert(crate::transcription::presentation::read_uint(b, 0) == 0);
    assert(crate::transcription::presentation::read_uint(b, 1) == b[0] as nat);
    assert(v == (b[0] as nat) * 256 + (b[1] as nat));
    let (x, y) = (b[0] as nat, b[1] as nat);
    assert(x * 256 + y < 0x10000) by (nonlinear_arith) requires x < 256, y < 256;
}

/// §4.1.3: the fields before `extensions` read the same on both sides.
pub proof fn lemma_prefix(b: Seq<u8>)
    ensures
        match crate_prefix(b) {
            None => crate::transcription::key_exchange::read_server_hello_prefix(b) is None,
            Some((h, r)) => crate::transcription::key_exchange::read_server_hello_prefix(b) == Some((sh_view(h), r))
                && b.len() >= 34 && h.random == b.subrange(2, 34),
        },
{
    if b.len() >= 34 {
        super::record::lemma_read_uint(b, 2);
        lemma_uint16(b);
        let r1 = b.skip(2);
        assert(r1.take(32) =~= b.subrange(2, 34));
        assert(r1.skip(32) =~= b.subrange(34, b.len() as int));
        let r2 = b.subrange(34, b.len() as int);
        super::messages::lemma_read_vec(r2, 0, 32);
        match crate::spec::read_vec(r2, 0, 32) {
            None => {},
            Some((sid, r3)) => {
                if r3.len() >= 3 {
                    super::record::lemma_read_uint(r3, 2);
                    lemma_uint16(r3);
                    let r4 = r3.skip(2);
                    super::record::lemma_read_uint(r4, 1);
                    assert(crate::transcription::presentation::read_uint(r4, 0) == 0);
                    assert(crate::transcription::presentation::read_uint(r4, 1) == r4[0] as nat);
                    assert(r4[0] == r3[2]);
                    assert(r4.skip(1) =~= r3.subrange(3, r3.len() as int));
                    assert(sh_view(crate_prefix(b)->Some_0.0).extensions =~= Seq::empty());
                }
            },
        }
    }
}

/// A vector read with a floor is the same vector read with floor 0.
pub proof fn lemma_read_vec_floor(b: Seq<u8>, floor: nat, ceil: nat)
    requires crate::spec::read_vec(b, floor, ceil) is Some,
    ensures crate::spec::read_vec(b, 0, ceil) == crate::spec::read_vec(b, floor, ceil),
{
}

/// §4.1.3: a ServerHello body reads the same on both sides, and what the
/// TLS 1.3 parser reads, the any-version reader reads too.
pub proof fn lemma_read_server_hello(b: Seq<u8>)
    ensures
        match crate::spec::read_server_hello(b) {
            None => crate::transcription::key_exchange::read_server_hello(b) is None,
            Some(sh) => {
                &&& crate::transcription::key_exchange::read_server_hello(b) == Some(sh_view(sh))
                &&& crate::transcription::key_exchange::read_server_hello_any_version(b) == Some(sh_view(sh))
            },
        },
{
    lemma_prefix(b);
    match crate_prefix(b) {
        None => {},
        Some((h, r5)) => {
            super::messages::lemma_read_exts(r5, 6, 65535);
            super::messages::lemma_read_exts(r5, 0, 65535);
            if crate::spec::read_exts(r5, 6, 65535) is Some {
                lemma_read_vec_floor(r5, 6, 65535);
                assert(r5.len() > 0);
            }
        },
    }
}

/// The crate's legacy preflight: a body the any-version reader accepts,
/// without supported_versions; its Random is the crate's `server_random`.
pub proof fn lemma_preflight(b: Seq<u8>)
    ensures
        crate::spec::legacy_server_hello_without_supported_versions(b)
            == match crate::transcription::key_exchange::read_server_hello_any_version(b) {
                None => false,
                Some(any) => crate::transcription::extensions::find_extension(any.extensions, 43) is None,
            },
        match crate::transcription::key_exchange::read_server_hello_any_version(b) {
            None => true,
            Some(any) => any.random == crate::hello::spec::server_random(b),
        },
{
    lemma_prefix(b);
    match crate_prefix(b) {
        None => {},
        Some((h, r5)) => {
            super::messages::lemma_read_exts(r5, 0, 65535);
            if r5.len() != 0 {
                match crate::spec::read_exts(r5, 0, 65535) {
                    None => {},
                    Some((es, rest)) => {
                        super::auth_flight::lemma_find(es, 43);
                    },
                }
            }
        },
    }
}

/// §4.2.1 `selected_version` and §4.2.8 `selected_group`: one `uint16`,
/// the whole of `extension_data`, on both sides.
pub proof fn lemma_u16_body(data: Seq<u8>)
    ensures
        match crate::spec::read_supported_versions_sh(data) {
            None => crate::transcription::extensions::read_supported_versions_server(data) is None,
            Some(v) => crate::transcription::extensions::read_supported_versions_server(data) == Some(v as nat),
        },
        crate::spec::read_key_share_hrr(data) == crate::spec::read_supported_versions_sh(data),
        crate::transcription::extensions::read_key_share_hello_retry_request(data)
            == crate::transcription::extensions::read_supported_versions_server(data),
{
    if data.len() >= 2 {
        super::record::lemma_read_uint(data, 2);
        lemma_uint16(data);
    }
}

/// §4.2.2 Cookie: the same reader on both sides.
pub proof fn lemma_cookie_body(data: Seq<u8>)
    ensures
        crate::spec::read_cookie(data) == crate::transcription::extensions::read_cookie(data),
{
    super::messages::lemma_read_vec(data, 1, 65535);
}

/// §4.2.8 KeyShareServerHello: the same entry on both sides.
pub proof fn lemma_key_share_body(data: Seq<u8>)
    ensures
        match crate::spec::read_key_share_sh(data) {
            None => crate::transcription::extensions::read_key_share_server_hello(data) is None,
            Some(k) => crate::transcription::extensions::read_key_share_server_hello(data)
                == Some(crate::transcription::extensions::KeyShareEntry { group: k.group as nat, key_exchange: k.key_exchange }),
        },
{
    if data.len() >= 2 {
        super::record::lemma_read_uint(data, 2);
        lemma_uint16(data);
        assert(data.skip(2) =~= data.subrange(2, data.len() as int));
        super::messages::lemma_read_vec(data.skip(2), 1, 65535);
    }
}

/// One ServerHello extension's body (§4.2.1, §4.2.8; the table allows no
/// other whose body the crate reads): a body the crate refuses is
/// malformed for the transcription, and an accepted supported_versions or
/// key_share has no body failure.
pub proof fn lemma_sh_body(offered: Seq<crate::transcription::extensions::Extension>, e: crate::spec::Ext)
    requires crate::spec::extension_allowed(e.etype, crate::spec::MsgKind::Sh),
    ensures ({
        let f = crate::transcription::extension_bodies::one_body_failures(offered, super::messages::ext_view(e),
            crate::transcription::extensions::TableMessage::Sh);
        &&& !crate::spec::ext_body_ok(e, crate::spec::MsgKind::Sh) ==> f == seq![crate::transcription::alerts::ClientError::Malformed]
        &&& crate::spec::ext_body_ok(e, crate::spec::MsgKind::Sh) && (e.etype == 43 || e.etype == 51) ==> f == Seq::<crate::transcription::alerts::ClientError>::empty()
    }),
{
    super::extensions::lemma_table(e.etype, crate::spec::MsgKind::Sh);
    lemma_u16_body(e.data);
    lemma_key_share_body(e.data);
    reveal_with_fuel(crate::transcription::presentation::list_has, 8);
}

/// The ServerHello's block of bodies: with every extension allowed, a body
/// the crate refuses is a `decode_error` failure of the transcription's, and
/// a block the crate accepts and finds offered has none.
pub proof fn lemma_sh_bodies(offered: Seq<crate::transcription::extensions::Extension>, es: Seq<crate::spec::Ext>)
    requires crate::spec::all_allowed(es, crate::spec::MsgKind::Sh),
    ensures ({
        let f = crate::transcription::extension_bodies::extension_body_failures(offered, super::messages::exts_view(es),
            crate::transcription::extensions::TableMessage::Sh);
        &&& !crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Sh) ==> super::auth_flight::alert_in(50, f)
        &&& crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Sh) && crate::hello::spec::offered(es, false)
            ==> f == Seq::<crate::transcription::alerts::ClientError>::empty()
    }),
    decreases es.len(),
{
    if es.len() > 0 {
        let v = super::messages::exts_view(es);
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        assert(v[0] == super::messages::ext_view(es[0]));
        lemma_sh_bodies(offered, es.skip(1));
        lemma_sh_body(offered, es[0]);
        let head = crate::transcription::extension_bodies::one_body_failures(offered, v[0],
            crate::transcription::extensions::TableMessage::Sh);
        let tail = crate::transcription::extension_bodies::extension_body_failures(offered, super::messages::exts_view(es.skip(1)),
            crate::transcription::extensions::TableMessage::Sh);
        super::auth_flight::lemma_alert_in_concat(50, head, tail);
        if !crate::spec::ext_body_ok(es[0], crate::spec::MsgKind::Sh) {
            assert(head[0] == crate::transcription::alerts::ClientError::Malformed);
            assert(crate::transcription::alerts::required_alert(head[0]) == 50nat);
        }
        if crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Sh) && crate::hello::spec::offered(es, false) {
            assert(head + tail =~= Seq::<crate::transcription::alerts::ClientError>::empty());
        }
    }
}

/// The HelloRetryRequest's block of bodies: with no duplicate and every
/// extension allowed, a body the crate refuses is that of the first (so
/// the only) supported_versions, cookie or key_share.
pub proof fn lemma_hrr_bodies(es: Seq<crate::spec::Ext>)
    requires
        crate::spec::all_allowed(es, crate::spec::MsgKind::Hrr),
        crate::spec::exts_unique(es),
        !crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Hrr),
    ensures
        (crate::hello::spec::extension(es, 43) is Some
            && crate::spec::read_supported_versions_sh(crate::hello::spec::extension(es, 43)->Some_0) is None)
        || (crate::hello::spec::extension(es, 44) is Some
            && crate::spec::read_cookie(crate::hello::spec::extension(es, 44)->Some_0) is None)
        || (crate::hello::spec::extension(es, 51) is Some
            && crate::spec::read_key_share_hrr(crate::hello::spec::extension(es, 51)->Some_0) is None),
    decreases es.len(),
{
    if crate::spec::ext_body_ok(es[0], crate::spec::MsgKind::Hrr) {
        lemma_hrr_bodies(es.skip(1));
        super::auth_flight::lemma_find(es.skip(1), 43);
        super::auth_flight::lemma_find(es.skip(1), 44);
        super::auth_flight::lemma_find(es.skip(1), 51);
        super::auth_flight::lemma_find(es, 43);
        super::auth_flight::lemma_find(es, 44);
        super::auth_flight::lemma_find(es, 51);
    }
}

/// §4.2's offered rule for a ServerHello (`retry` false) or a
/// HelloRetryRequest (`retry` true, with the cookie exception): the crate's
/// `offered` is the transcription's, for the profile's offers.
pub proof fn lemma_offered(es: Seq<crate::spec::Ext>, offers: Seq<u16>, retry: bool)
    requires
        crate::spec::all_allowed(es, if retry { crate::spec::MsgKind::Hrr } else { crate::spec::MsgKind::Sh }),
        crate::auth::spec::profile_extensions(offers),
        crate::auth::spec::member(offers, 43),
        crate::auth::spec::member(offers, 51),
    ensures
        crate::hello::spec::offered(es, retry) == !crate::transcription::extensions::any_not_offered(
            super::messages::exts_view(es), super::extensions::nats(offers),
            if retry { crate::transcription::extensions::TableMessage::Hrr } else { crate::transcription::extensions::TableMessage::Sh }),
    decreases es.len(),
{
    if es.len() > 0 {
        let v = super::messages::exts_view(es);
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_offered(es.skip(1), offers, retry);
        let t = es[0].etype;
        super::extensions::lemma_list_has_nats(offers, t);
        super::extensions::lemma_list_has_nats(offers, 43);
        super::extensions::lemma_list_has_nats(offers, 51);
        if crate::auth::spec::member(offers, t) {
            super::bodies::lemma_profile_member(offers, t);
        }
    }
}

// ---------------------------------------------------------------------------
// The two sides' results.
// ---------------------------------------------------------------------------

/// The transcription's applicable failures of a body in WAIT_SH, composed
/// as `receive_server_hello` composes its lists ([`lemma_receive`]).
pub open spec fn hello_failures(sent: crate::transcription::key_exchange::ClientHello,
    retry: Option<crate::transcription::key_exchange::RetryRecord>, body: Seq<u8>)
    -> Seq<crate::transcription::alerts::ClientError>
{
    match crate::transcription::key_exchange::read_server_hello_any_version(body) {
        None => seq![crate::transcription::alerts::ClientError::Malformed],
        Some(any) =>
            if crate::transcription::key_exchange::is_hello_retry_request(any) {
                crate::transcription::alerts::fails_if(retry is Some, crate::transcription::alerts::ClientError::SecondHelloRetryRequest)
                + match crate::transcription::key_exchange::read_server_hello(body) {
                    None => seq![crate::transcription::alerts::ClientError::Malformed],
                    Some(hello) => crate::transcription::key_exchange::hello_retry_request_failures(sent, hello),
                }
            } else if crate::transcription::extensions::find_extension(any.extensions, 43) is None {
                crate::transcription::key_exchange::older_server_hello_failures(any)
            } else {
                match crate::transcription::key_exchange::read_server_hello(body) {
                    None => seq![crate::transcription::alerts::ClientError::Malformed],
                    Some(hello) => crate::transcription::key_exchange::server_hello_failures(sent, hello, retry),
                }
            },
    }
}

/// The transcription's ClientHello offers what the crate's profile offers
/// (see the module documentation).
pub open spec fn sent_is_profile(sent: crate::transcription::key_exchange::ClientHello, session_id: Seq<u8>,
    offers: Seq<u16>) -> bool
{
    &&& sent.legacy_session_id == session_id
    &&& sent.cipher_suites == seq![0x1303nat]
    &&& crate::transcription::key_exchange::offered_versions(sent) == seq![0x0304nat]
    &&& crate::transcription::key_exchange::offered_groups(sent) == seq![0x001Dnat]
    &&& crate::transcription::extensions::share_groups(crate::transcription::key_exchange::offered_shares(sent)) == seq![0x001Dnat]
    &&& crate::auth::spec::profile_extensions(offers)
    &&& crate::auth::spec::member(offers, 43)
    &&& crate::auth::spec::member(offers, 51)
    &&& super::extensions::nats(offers) == crate::transcription::extensions::extension_types(sent.extensions)
}

/// What the transcription kept of a HelloRetryRequest this profile
/// accepted: a cookie-only one, for TLS 1.3 and the profile's suite.
pub open spec fn profile_retry_record() -> crate::transcription::key_exchange::RetryRecord {
    crate::transcription::key_exchange::RetryRecord { cipher_suite: 0x1303, selected_version: 0x0304, selected_group: None }
}

/// A retry came exactly when the crate says so, and it was one this
/// profile accepts.
pub open spec fn retry_is_profile(retried: bool, retry: Option<crate::transcription::key_exchange::RetryRecord>) -> bool {
    &&& (retry is Some) == retried
    &&& retry is Some ==> retry == Some(profile_retry_record())
}

/// The crate's `validate` after a body was read as a ServerHello: the
/// compression byte and the extension block (`parse_handshake_body`), then
/// `parsed`.
pub open spec fn crate_after_read(sh: crate::spec::ServerHello, session_id: Seq<u8>, retried: bool)
    -> Result<crate::hello::spec::Selection, u8>
{
    if sh.compression != 0 {
        Err(crate::spec::alert_of(crate::spec::ErrKind::InvalidEnum))
    } else {
        match crate::spec::check_extensions(sh.extensions, crate::spec::server_hello_kind(sh)) {
            Some(k) => Err(crate::spec::alert_of(k)),
            None => crate::hello::spec::parsed(sh, session_id, retried),
        }
    }
}

/// `validate`, unfolded through `parse_handshake_body`.
pub proof fn lemma_validate_unfold(session_id: Seq<u8>, retried: bool, body: Seq<u8>)
    requires
        session_id.len() <= 32,
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures
        crate::hello::spec::validate(session_id, retried, body) ==
            if crate::spec::legacy_server_hello_without_supported_versions(body)
                && crate::hello::spec::server_random(body) != crate::spec::hrr_random() {
                Err(crate::hello::spec::below_tls13(crate::hello::spec::server_random(body)))
            } else {
                match crate::spec::read_server_hello(body) {
                    None => Err(50u8),
                    Some(sh) => crate_after_read(sh, session_id, retried),
                }
            },
{
}

/// The crate's result and the transcription's failures agree: a rejection
/// has an alert of some failure in the list (so the list is not empty), and
/// an acceptance has an empty list and the same selection.
pub open spec fn hello_agrees(r: Result<crate::hello::spec::Selection, u8>,
    sent: crate::transcription::key_exchange::ClientHello,
    retry: Option<crate::transcription::key_exchange::RetryRecord>, body: Seq<u8>) -> bool
{
    let f = hello_failures(sent, retry, body);
    match r {
        Err(alert) => super::auth_flight::alert_in(alert, f),
        Ok(crate::hello::spec::Selection::Retry(cookie)) => f.len() == 0
            && match crate::transcription::key_exchange::read_server_hello(body) {
                Some(h) => crate::transcription::key_exchange::is_hello_retry_request(h)
                    && crate::transcription::extensions::find_extension(h.extensions, 44) == Some(cookie),
                None => false,
            },
        Ok(crate::hello::spec::Selection::Share(key)) => f.len() == 0
            && match crate::transcription::key_exchange::read_server_hello(body) {
                Some(h) => !crate::transcription::key_exchange::is_hello_retry_request(h)
                    && crate::transcription::extensions::find_extension(h.extensions, 51) is Some
                    && crate::transcription::extensions::read_key_share_server_hello(
                        crate::transcription::extensions::find_extension(h.extensions, 51)->0)
                        == Some(crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: key }),
                None => false,
            },
    }
}

/// An alert of some failure of one part is an alert of some failure of
/// the list of eight parts.
pub proof fn lemma_in8(a: u8, x1: Seq<crate::transcription::alerts::ClientError>,
    x2: Seq<crate::transcription::alerts::ClientError>, x3: Seq<crate::transcription::alerts::ClientError>,
    x4: Seq<crate::transcription::alerts::ClientError>, x5: Seq<crate::transcription::alerts::ClientError>,
    x6: Seq<crate::transcription::alerts::ClientError>, x7: Seq<crate::transcription::alerts::ClientError>,
    x8: Seq<crate::transcription::alerts::ClientError>)
    ensures
        super::auth_flight::alert_in(a, x1) || super::auth_flight::alert_in(a, x2) || super::auth_flight::alert_in(a, x3)
            || super::auth_flight::alert_in(a, x4) || super::auth_flight::alert_in(a, x5) || super::auth_flight::alert_in(a, x6)
            || super::auth_flight::alert_in(a, x7) || super::auth_flight::alert_in(a, x8)
            ==> super::auth_flight::alert_in(a, x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8),
{
    super::auth_flight::lemma_alert_in_concat(a, x1, x2);
    super::auth_flight::lemma_alert_in_concat(a, x1 + x2, x3);
    super::auth_flight::lemma_alert_in_concat(a, x1 + x2 + x3, x4);
    super::auth_flight::lemma_alert_in_concat(a, x1 + x2 + x3 + x4, x5);
    super::auth_flight::lemma_alert_in_concat(a, x1 + x2 + x3 + x4 + x5, x6);
    super::auth_flight::lemma_alert_in_concat(a, x1 + x2 + x3 + x4 + x5 + x6, x7);
    super::auth_flight::lemma_alert_in_concat(a, x1 + x2 + x3 + x4 + x5 + x6 + x7, x8);
}

/// The one failure of a singleton list.
pub proof fn lemma_in1(a: u8, e: crate::transcription::alerts::ClientError, rest: Seq<crate::transcription::alerts::ClientError>)
    requires crate::transcription::alerts::required_alert(e) == a as nat,
    ensures
        super::auth_flight::alert_in(a, seq![e]),
        super::auth_flight::alert_in(a, seq![e] + rest),
        super::auth_flight::alert_in(a, rest + seq![e]),
{
    assert(seq![e][0] == e);
    super::auth_flight::lemma_alert_in_concat(a, seq![e], rest);
    super::auth_flight::lemma_alert_in_concat(a, rest, seq![e]);
}

/// The two Randoms of a HelloRetryRequest are the same value.
pub proof fn lemma_hrr_random()
    ensures crate::spec::hrr_random() == crate::transcription::key_exchange::hello_retry_request_random(),
{
    assert(crate::spec::hrr_random() =~= crate::transcription::key_exchange::hello_retry_request_random());
}

/// §4.1.3 and §4.1.4, a ServerHello that is not a HelloRetryRequest and
/// carries supported_versions: the crate's checks after reading it, against
/// `server_hello_failures`.
#[verifier::rlimit(400)]
pub proof fn lemma_server_hello(sent: crate::transcription::key_exchange::ClientHello,
    retry: Option<crate::transcription::key_exchange::RetryRecord>, offers: Seq<u16>,
    session_id: Seq<u8>, retried: bool, sh: crate::spec::ServerHello)
    requires
        sent_is_profile(sent, session_id, offers),
        retry_is_profile(retried, retry),
        !crate::spec::is_hello_retry_request(sh),
        crate::hello::spec::extension(sh.extensions, 43) is Some,
    ensures ({
        let h = sh_view(sh);
        let f = crate::transcription::key_exchange::server_hello_failures(sent, h, retry);
        match crate_after_read(sh, session_id, retried) {
            Err(alert) => super::auth_flight::alert_in(alert, f),
            Ok(crate::hello::spec::Selection::Retry(_)) => false,
            Ok(crate::hello::spec::Selection::Share(key)) => f.len() == 0
                && crate::transcription::extensions::find_extension(h.extensions, 51) is Some
                && crate::transcription::extensions::read_key_share_server_hello(
                    crate::transcription::extensions::find_extension(h.extensions, 51)->0)
                    == Some(crate::transcription::extensions::KeyShareEntry { group: 0x001D, key_exchange: key }),
        }
    }),
{
    reveal_with_fuel(crate::transcription::presentation::list_has, 3);
    let h = sh_view(sh);
    let es = sh.extensions;
    let v = super::messages::exts_view(es);
    let types = crate::transcription::extensions::extension_types(sent.extensions);
    let sm = crate::transcription::extensions::TableMessage::Sh;
    let a = crate::transcription::alerts::fails_if(h.legacy_version == 0x0300, crate::transcription::alerts::ClientError::VersionNotSupported);
    let b = match crate::transcription::extensions::find_extension(h.extensions, 43) {
        None => seq![crate::transcription::alerts::ClientError::SupportedVersionsMissing],
        Some(data) => crate::transcription::key_exchange::selected_version_failures(sent, data)
            + match (retry, crate::transcription::extensions::read_supported_versions_server(data)) {
                (Some(r), Some(selected_version)) =>
                    crate::transcription::alerts::fails_if(selected_version != r.selected_version, crate::transcription::alerts::ClientError::SelectedVersionChanged),
                _ => seq![],
            },
    };
    let c = crate::transcription::key_exchange::hello_field_failures(sent, h);
    let d = match retry {
        Some(r) => crate::transcription::alerts::fails_if(h.cipher_suite != r.cipher_suite, crate::transcription::alerts::ClientError::CipherSuiteChanged),
        None => seq![],
    };
    let dup = crate::transcription::alerts::fails_if(crate::transcription::extensions::has_duplicate_extension(v),
        crate::transcription::alerts::ClientError::DuplicateExtension);
    let nsp = crate::transcription::alerts::fails_if(crate::transcription::extensions::any_not_specified(v, sm),
        crate::transcription::alerts::ClientError::ExtensionNotSpecifiedForMessage);
    let nof = crate::transcription::alerts::fails_if(crate::transcription::extensions::any_not_offered(v, types, sm),
        crate::transcription::alerts::ClientError::ExtensionNotOffered);
    let e = crate::transcription::extensions::response_block_failures(v, types, sm);
    let g = crate::transcription::key_exchange::server_share_failures(sent, h, retry);
    let bf = crate::transcription::extension_bodies::extension_body_failures(sent.extensions, v, sm);
    let f = crate::transcription::key_exchange::server_hello_failures(sent, h, retry);
    assert(f == a + b + c + d + e + g + bf);
    assert(e == dup + nsp + nof);
    let empty = Seq::<crate::transcription::alerts::ClientError>::empty();
    assert(f =~= a + b + c + d + e + g + bf + empty);
    assert(!crate::transcription::key_exchange::is_hello_retry_request(h)) by { lemma_hrr_random(); }
    assert(crate::spec::server_hello_kind(sh) == crate::spec::MsgKind::Sh);
    super::auth_flight::lemma_find(es, 43);
    super::auth_flight::lemma_find(es, 51);
    super::extensions::lemma_unique(es);
    super::extensions::lemma_all_allowed(es, crate::spec::MsgKind::Sh);
    super::auth_flight::lemma_alert_in_concat(47, dup, nsp);
    super::auth_flight::lemma_alert_in_concat(47, dup + nsp, nof);
    super::auth_flight::lemma_alert_in_concat(110, dup + nsp, nof);
    let c1 = crate::transcription::alerts::fails_if(h.legacy_session_id_echo != sent.legacy_session_id, crate::transcription::alerts::ClientError::SessionIdEchoMismatch);
    let c2 = crate::transcription::alerts::fails_if(!crate::transcription::presentation::list_has(sent.cipher_suites, h.cipher_suite), crate::transcription::alerts::ClientError::CipherSuiteNotOffered);
    let c3 = crate::transcription::alerts::fails_if(h.legacy_compression_method != 0, crate::transcription::alerts::ClientError::CompressionMethodNotZero);
    assert(c == c1 + c2 + c3);
    super::auth_flight::lemma_alert_in_concat(47, c1, c2);
    super::auth_flight::lemma_alert_in_concat(47, c1 + c2, c3);
    let r = crate_after_read(sh, session_id, retried);
    if sh.compression != 0 {
        lemma_in1(47, crate::transcription::alerts::ClientError::CompressionMethodNotZero, empty);
        lemma_in8(47, a, b, c, d, e, g, bf, empty);
    } else if !crate::spec::exts_unique(es) {
        lemma_in1(47, crate::transcription::alerts::ClientError::DuplicateExtension, empty);
        lemma_in8(47, a, b, c, d, e, g, bf, empty);
    } else if !crate::spec::all_allowed(es, crate::spec::MsgKind::Sh) {
        lemma_in1(47, crate::transcription::alerts::ClientError::ExtensionNotSpecifiedForMessage, empty);
        lemma_in8(47, a, b, c, d, e, g, bf, empty);
    } else if !crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Sh) {
        lemma_sh_bodies(sent.extensions, es);
        lemma_in8(50, a, b, c, d, e, g, bf, empty);
    } else if sh.legacy_version == 0x0300 {
        lemma_in1(70, crate::transcription::alerts::ClientError::VersionNotSupported, empty);
        lemma_in8(70, a, b, c, d, e, g, bf, empty);
    } else {
        let data = crate::hello::spec::extension(es, 43)->Some_0;
        lemma_u16_body(data);
        let svf = crate::transcription::key_exchange::selected_version_failures(sent, data);
        let svc = match (retry, crate::transcription::extensions::read_supported_versions_server(data)) {
            (Some(rr), Some(selected_version)) =>
                crate::transcription::alerts::fails_if(selected_version != rr.selected_version, crate::transcription::alerts::ClientError::SelectedVersionChanged),
            _ => seq![],
        };
        assert(b == svf + svc);
        super::auth_flight::lemma_alert_in_concat(50, svf, svc);
        super::auth_flight::lemma_alert_in_concat(47, svf, svc);
        match crate::spec::read_supported_versions_sh(data) {
            None => {
                lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, empty);
                lemma_in8(50, a, b, c, d, e, g, bf, empty);
            },
            Some(version) => {
                if version != 0x0304 {
                    assert(svf[0] == crate::transcription::alerts::ClientError::SelectedVersionNotAcceptable);
                    assert(crate::transcription::alerts::required_alert(svf[0]) == 47nat);
                    lemma_in8(47, a, b, c, d, e, g, bf, empty);
                } else if sh.session_id_echo != session_id || sh.cipher_suite != 0x1303 {
                    if sh.session_id_echo != session_id {
                        lemma_in1(47, crate::transcription::alerts::ClientError::SessionIdEchoMismatch, empty);
                    } else {
                        lemma_in1(47, crate::transcription::alerts::ClientError::CipherSuiteNotOffered, empty);
                    }
                    lemma_in8(47, a, b, c, d, e, g, bf, empty);
                } else {
                    lemma_offered(es, offers, false);
                    if !crate::hello::spec::offered(es, false) {
                        lemma_in1(110, crate::transcription::alerts::ClientError::ExtensionNotOffered, empty);
                        lemma_in8(110, a, b, c, d, e, g, bf, empty);
                    } else {
                        assert(svf =~= empty);
                        assert(svc =~= empty);
                        assert(a =~= empty);
                        assert(c =~= empty);
                        assert(d =~= empty);
                        assert(e =~= empty);
                        lemma_sh_bodies(sent.extensions, es);
                        assert(bf =~= empty);
                        match crate::hello::spec::extension(es, 51) {
                            None => {
                                lemma_in1(109, crate::transcription::alerts::ClientError::KeyShareMissing, empty);
                                lemma_in8(109, a, b, c, d, e, g, bf, empty);
                            },
                            Some(kd) => {
                                lemma_key_share_body(kd);
                                match crate::spec::read_key_share_sh(kd) {
                                    None => {
                                        lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, empty);
                                        lemma_in8(50, a, b, c, d, e, g, bf, empty);
                                    },
                                    Some(k) => {
                                        let g1 = crate::transcription::alerts::fails_if(
                                            !crate::transcription::presentation::list_has(seq![0x001Dnat], k.group as nat),
                                            crate::transcription::alerts::ClientError::ServerShareGroupNotOffered);
                                        let g3 = crate::transcription::alerts::fails_if(
                                            k.group as nat == 0x001Dnat && k.key_exchange.len() != 32,
                                            crate::transcription::alerts::ClientError::ServerShareWrongLength);
                                        assert(g == g1 + empty + g3);
                                        super::auth_flight::lemma_alert_in_concat(47, g1 + empty, g3);
                                        super::auth_flight::lemma_alert_in_concat(47, g1, empty);
                                        if k.group != 29 {
                                            lemma_in1(47, crate::transcription::alerts::ClientError::ServerShareGroupNotOffered, empty);
                                            lemma_in8(47, a, b, c, d, e, g, bf, empty);
                                        } else if k.key_exchange.len() != 32 {
                                            lemma_in1(47, crate::transcription::alerts::ClientError::ServerShareWrongLength, empty);
                                            lemma_in8(47, a, b, c, d, e, g, bf, empty);
                                        } else {
                                            assert(g =~= empty);
                                            assert(f =~= empty);
                                        }
                                    },
                                }
                            },
                        }
                    }
                }
            },
        }
    }
}

/// The body the crate found for type `t` passed its body check.
pub proof fn lemma_found_body_ok(es: Seq<crate::spec::Ext>, m: crate::spec::MsgKind, t: u16)
    requires
        crate::spec::all_bodies_ok(es, m),
        crate::hello::spec::extension(es, t) is Some,
    ensures
        crate::spec::ext_body_ok(crate::spec::Ext { etype: t, data: crate::hello::spec::extension(es, t)->Some_0 }, m),
    decreases es.len(),
{
    if es[0].etype != t {
        lemma_found_body_ok(es.skip(1), m, t);
    } else {
        assert(es[0] == crate::spec::Ext { etype: t, data: crate::hello::spec::extension(es, t)->Some_0 });
    }
}

/// §4.1.4, §4.2.2 and §4.2.8, a HelloRetryRequest: the crate's checks after
/// reading it, against `SecondHelloRetryRequest` (if a retry came before)
/// and `hello_retry_request_failures`.
#[verifier::rlimit(400)]
pub proof fn lemma_retry_request(sent: crate::transcription::key_exchange::ClientHello,
    retry: Option<crate::transcription::key_exchange::RetryRecord>, offers: Seq<u16>,
    session_id: Seq<u8>, retried: bool, sh: crate::spec::ServerHello)
    requires
        sent_is_profile(sent, session_id, offers),
        retry_is_profile(retried, retry),
        crate::spec::is_hello_retry_request(sh),
    ensures ({
        let h = sh_view(sh);
        let f = crate::transcription::alerts::fails_if(retry is Some, crate::transcription::alerts::ClientError::SecondHelloRetryRequest)
            + crate::transcription::key_exchange::hello_retry_request_failures(sent, h);
        match crate_after_read(sh, session_id, retried) {
            Err(alert) => super::auth_flight::alert_in(alert, f),
            Ok(crate::hello::spec::Selection::Retry(cookie)) => f.len() == 0
                && crate::transcription::extensions::find_extension(h.extensions, 44) == Some(cookie),
            Ok(crate::hello::spec::Selection::Share(_)) => false,
        }
    }),
{
    reveal_with_fuel(crate::transcription::presentation::list_has, 3);
    let h = sh_view(sh);
    let es = sh.extensions;
    let v = super::messages::exts_view(es);
    let types = crate::transcription::extensions::extension_types(sent.extensions);
    let hm = crate::transcription::extensions::TableMessage::Hrr;
    let sr = crate::transcription::alerts::fails_if(retry is Some, crate::transcription::alerts::ClientError::SecondHelloRetryRequest);
    let a = crate::transcription::alerts::fails_if(h.legacy_version == 0x0300, crate::transcription::alerts::ClientError::VersionNotSupported);
    let a2 = crate::transcription::alerts::fails_if(h.legacy_version != 0x0303, crate::transcription::alerts::ClientError::RetryLegacyVersion);
    let c = crate::transcription::key_exchange::hello_field_failures(sent, h);
    let b = match crate::transcription::extensions::find_extension(h.extensions, 43) {
        None => seq![crate::transcription::alerts::ClientError::SupportedVersionsMissing],
        Some(data) => crate::transcription::key_exchange::selected_version_failures(sent, data),
    };
    let dup = crate::transcription::alerts::fails_if(crate::transcription::extensions::has_duplicate_extension(v),
        crate::transcription::alerts::ClientError::DuplicateExtension);
    let nsp = crate::transcription::alerts::fails_if(crate::transcription::extensions::any_not_specified(v, hm),
        crate::transcription::alerts::ClientError::ExtensionNotSpecifiedForMessage);
    let nof = crate::transcription::alerts::fails_if(crate::transcription::extensions::any_not_offered(v, types, hm),
        crate::transcription::alerts::ClientError::ExtensionNotOffered);
    let e = crate::transcription::extensions::response_block_failures(v, types, hm);
    let k = match crate::transcription::extensions::find_extension(h.extensions, 44) {
        None => seq![],
        Some(data) => crate::transcription::alerts::fails_if(crate::transcription::extensions::read_cookie(data) is None,
            crate::transcription::alerts::ClientError::Malformed),
    };
    let s = match crate::transcription::extensions::find_extension(h.extensions, 51) {
        None => seq![],
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
    let n = crate::transcription::alerts::fails_if(crate::transcription::key_exchange::retry_changes_nothing(h),
        crate::transcription::alerts::ClientError::RetryWithoutChange);
    let hf = crate::transcription::key_exchange::hello_retry_request_failures(sent, h);
    assert(hf == a + a2 + c + b + e + k + s + n);
    assert(e == dup + nsp + nof);
    let f = sr + hf;
    let empty = Seq::<crate::transcription::alerts::ClientError>::empty();
    assert(crate::transcription::key_exchange::is_hello_retry_request(h)) by { lemma_hrr_random(); }
    assert(crate::spec::server_hello_kind(sh) == crate::spec::MsgKind::Hrr);
    super::auth_flight::lemma_find(es, 43);
    super::auth_flight::lemma_find(es, 44);
    super::auth_flight::lemma_find(es, 51);
    super::extensions::lemma_unique(es);
    super::extensions::lemma_all_allowed(es, crate::spec::MsgKind::Hrr);
    super::auth_flight::lemma_alert_in_concat(47, dup, nsp);
    super::auth_flight::lemma_alert_in_concat(47, dup + nsp, nof);
    super::auth_flight::lemma_alert_in_concat(110, dup + nsp, nof);
    let c1 = crate::transcription::alerts::fails_if(h.legacy_session_id_echo != sent.legacy_session_id, crate::transcription::alerts::ClientError::SessionIdEchoMismatch);
    let c2 = crate::transcription::alerts::fails_if(!crate::transcription::presentation::list_has(sent.cipher_suites, h.cipher_suite), crate::transcription::alerts::ClientError::CipherSuiteNotOffered);
    let c3 = crate::transcription::alerts::fails_if(h.legacy_compression_method != 0, crate::transcription::alerts::ClientError::CompressionMethodNotZero);
    assert(c == c1 + c2 + c3);
    super::auth_flight::lemma_alert_in_concat(47, c1, c2);
    super::auth_flight::lemma_alert_in_concat(47, c1 + c2, c3);
    // Every alert below is shown in a part of `hf`, then lifted to `f`.
    super::auth_flight::lemma_alert_in_concat(47, sr, hf);
    super::auth_flight::lemma_alert_in_concat(50, sr, hf);
    super::auth_flight::lemma_alert_in_concat(70, sr, hf);
    super::auth_flight::lemma_alert_in_concat(109, sr, hf);
    super::auth_flight::lemma_alert_in_concat(110, sr, hf);
    super::auth_flight::lemma_alert_in_concat(10, sr, hf);
    if sh.compression != 0 {
        lemma_in1(47, crate::transcription::alerts::ClientError::CompressionMethodNotZero, empty);
        lemma_in8(47, a, a2, c, b, e, k, s, n);
    } else if !crate::spec::exts_unique(es) {
        lemma_in1(47, crate::transcription::alerts::ClientError::DuplicateExtension, empty);
        lemma_in8(47, a, a2, c, b, e, k, s, n);
    } else if !crate::spec::all_allowed(es, crate::spec::MsgKind::Hrr) {
        lemma_in1(47, crate::transcription::alerts::ClientError::ExtensionNotSpecifiedForMessage, empty);
        lemma_in8(47, a, a2, c, b, e, k, s, n);
    } else if !crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Hrr) {
        lemma_hrr_bodies(es);
        lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, empty);
        if crate::hello::spec::extension(es, 43) is Some
            && crate::spec::read_supported_versions_sh(crate::hello::spec::extension(es, 43)->Some_0) is None {
            lemma_u16_body(crate::hello::spec::extension(es, 43)->Some_0);
        } else if crate::hello::spec::extension(es, 44) is Some
            && crate::spec::read_cookie(crate::hello::spec::extension(es, 44)->Some_0) is None {
            lemma_cookie_body(crate::hello::spec::extension(es, 44)->Some_0);
        } else {
            lemma_u16_body(crate::hello::spec::extension(es, 51)->Some_0);
        }
        lemma_in8(50, a, a2, c, b, e, k, s, n);
    } else if sh.legacy_version == 0x0300 {
        lemma_in1(70, crate::transcription::alerts::ClientError::VersionNotSupported, empty);
        lemma_in8(70, a, a2, c, b, e, k, s, n);
    } else if sh.legacy_version != 0x0303 {
        lemma_in1(47, crate::transcription::alerts::ClientError::RetryLegacyVersion, empty);
        lemma_in8(47, a, a2, c, b, e, k, s, n);
    } else {
        match crate::hello::spec::extension(es, 43) {
            None => {
                lemma_in1(109, crate::transcription::alerts::ClientError::SupportedVersionsMissing, empty);
                lemma_in8(109, a, a2, c, b, e, k, s, n);
            },
            Some(data) => {
                lemma_u16_body(data);
                let svf = crate::transcription::key_exchange::selected_version_failures(sent, data);
                assert(b == svf);
                match crate::spec::read_supported_versions_sh(data) {
                    None => {
                        lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, empty);
                        lemma_in8(50, a, a2, c, b, e, k, s, n);
                    },
                    Some(version) => {
                        if version != 0x0304 {
                            assert(svf[0] == crate::transcription::alerts::ClientError::SelectedVersionNotAcceptable);
                            assert(crate::transcription::alerts::required_alert(svf[0]) == 47nat);
                            lemma_in8(47, a, a2, c, b, e, k, s, n);
                        } else if sh.session_id_echo != session_id || sh.cipher_suite != 0x1303 {
                            if sh.session_id_echo != session_id {
                                lemma_in1(47, crate::transcription::alerts::ClientError::SessionIdEchoMismatch, empty);
                            } else {
                                lemma_in1(47, crate::transcription::alerts::ClientError::CipherSuiteNotOffered, empty);
                            }
                            lemma_in8(47, a, a2, c, b, e, k, s, n);
                        } else {
                            lemma_offered(es, offers, true);
                            if !crate::hello::spec::offered(es, true) {
                                lemma_in1(110, crate::transcription::alerts::ClientError::ExtensionNotOffered, empty);
                                lemma_in8(110, a, a2, c, b, e, k, s, n);
                            } else if retried {
                                lemma_in1(10, crate::transcription::alerts::ClientError::SecondHelloRetryRequest, empty);
                            } else if crate::hello::spec::extension(es, 51) is Some {
                                let kd = crate::hello::spec::extension(es, 51)->Some_0;
                                lemma_found_body_ok(es, crate::spec::MsgKind::Hrr, 51);
                                lemma_u16_body(kd);
                                let group = crate::spec::read_key_share_hrr(kd)->Some_0;
                                let s1 = crate::transcription::alerts::fails_if(!crate::transcription::presentation::list_has(
                                    seq![0x001Dnat], group as nat), crate::transcription::alerts::ClientError::RetryGroupNotOffered);
                                let s2 = crate::transcription::alerts::fails_if(crate::transcription::presentation::list_has(
                                    seq![0x001Dnat], group as nat), crate::transcription::alerts::ClientError::RetryGroupAlreadyShared);
                                assert(s == s1 + s2);
                                super::auth_flight::lemma_alert_in_concat(47, s1, s2);
                                if group == 29 {
                                    lemma_in1(47, crate::transcription::alerts::ClientError::RetryGroupAlreadyShared, empty);
                                } else {
                                    lemma_in1(47, crate::transcription::alerts::ClientError::RetryGroupNotOffered, empty);
                                }
                                lemma_in8(47, a, a2, c, b, e, k, s, n);
                            } else {
                                match crate::hello::spec::extension(es, 44) {
                                    None => {
                                        lemma_in1(47, crate::transcription::alerts::ClientError::RetryWithoutChange, empty);
                                        lemma_in8(47, a, a2, c, b, e, k, s, n);
                                    },
                                    Some(cd) => {
                                        lemma_cookie_body(cd);
                                        if crate::spec::read_cookie(cd) is None {
                                            lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, empty);
                                            lemma_in8(50, a, a2, c, b, e, k, s, n);
                                        } else {
                                            assert(sr =~= empty);
                                            assert(a =~= empty);
                                            assert(a2 =~= empty);
                                            assert(c =~= empty);
                                            assert(b =~= empty);
                                            assert(e =~= empty);
                                            assert(k =~= empty);
                                            assert(s =~= empty);
                                            assert(n =~= empty);
                                            assert(f =~= empty);
                                        }
                                    },
                                }
                            }
                        }
                    },
                }
            },
        }
    }
}

/// `validate` against the transcription's failures of the same body, under
/// the module's hypotheses.
#[verifier::rlimit(400)]
pub proof fn lemma_validate(sent: crate::transcription::key_exchange::ClientHello,
    retry: Option<crate::transcription::key_exchange::RetryRecord>, offers: Seq<u16>,
    session_id: Seq<u8>, retried: bool, body: Seq<u8>)
    requires
        sent_is_profile(sent, session_id, offers),
        retry_is_profile(retried, retry),
        session_id.len() <= 32,
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures
        hello_agrees(crate::hello::spec::validate(session_id, retried, body), sent, retry, body),
{
    lemma_validate_unfold(session_id, retried, body);
    lemma_preflight(body);
    lemma_read_server_hello(body);
    lemma_hrr_random();
    let f = hello_failures(sent, retry, body);
    let empty = Seq::<crate::transcription::alerts::ClientError>::empty();
    let sr = crate::transcription::alerts::fails_if(retry is Some, crate::transcription::alerts::ClientError::SecondHelloRetryRequest);
    if crate::spec::legacy_server_hello_without_supported_versions(body)
        && crate::hello::spec::server_random(body) != crate::spec::hrr_random() {
        let any = crate::transcription::key_exchange::read_server_hello_any_version(body)->Some_0;
        assert(!crate::transcription::key_exchange::is_hello_retry_request(any));
        assert(f == crate::transcription::key_exchange::older_server_hello_failures(any));
        assert(crate::hello::spec::downgrade_tls12() =~= crate::transcription::key_exchange::downgrade_tls12());
        assert(crate::hello::spec::downgrade_tls11() =~= crate::transcription::key_exchange::downgrade_tls11());
        let sentinel = crate::hello::spec::downgrade_sentinel(any.random);
        assert(sentinel == crate::transcription::key_exchange::has_downgrade_sentinel(any.random));
        let x = crate::transcription::alerts::fails_if(sentinel, crate::transcription::alerts::ClientError::DowngradeSentinel);
        let vns = seq![crate::transcription::alerts::ClientError::VersionNotSupported];
        lemma_in1(70, crate::transcription::alerts::ClientError::VersionNotSupported, empty);
        if sentinel {
            lemma_in1(47, crate::transcription::alerts::ClientError::DowngradeSentinel, empty);
        }
        if any.legacy_version <= 0x0303 {
            assert(f == x + vns);
            super::auth_flight::lemma_alert_in_concat(70, x, vns);
            super::auth_flight::lemma_alert_in_concat(47, x, vns);
        } else {
            let svm = seq![crate::transcription::alerts::ClientError::SupportedVersionsMissing];
            assert(f == svm + vns + x);
            super::auth_flight::lemma_alert_in_concat(70, svm, vns);
            super::auth_flight::lemma_alert_in_concat(70, svm + vns, x);
            super::auth_flight::lemma_alert_in_concat(47, svm + vns, x);
        }
    } else {
        match crate::spec::read_server_hello(body) {
            None => {
                lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, sr);
                lemma_in1(50, crate::transcription::alerts::ClientError::Malformed, empty);
            },
            Some(sh) => {
                let h = sh_view(sh);
                if crate::spec::is_hello_retry_request(sh) {
                    lemma_retry_request(sent, retry, offers, session_id, retried, sh);
                } else {
                    super::auth_flight::lemma_find(sh.extensions, 43);
                    lemma_server_hello(sent, retry, offers, session_id, retried, sh);
                }
            },
        }
    }
}

/// The transcription's WAIT_SH step on a server_hello message aborts with
/// the first of [`hello_failures`], and otherwise accepts the
/// HelloRetryRequest or the ServerHello it read.
pub open spec fn receive_agrees(p: crate::transcription::primitives::Primitives,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>) -> bool
{
    let raw = crate::transcription::key_exchange::write_handshake(2, body);
    let step = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
    let f = hello_failures(hs.hello, hs.retry, body);
    &&& f.len() > 0 ==> step == crate::transcription::state_machine::HandshakeStep::Abort(f[0])
    &&& f.len() == 0 ==> match crate::transcription::key_exchange::read_server_hello(body) {
        Some(h) => step == if crate::transcription::key_exchange::is_hello_retry_request(h) {
                crate::transcription::state_machine::accept_hello_retry_request(p, hs, h, raw)
            } else {
                crate::transcription::state_machine::accept_server_hello(p, hs, h, raw)
            },
        None => false,
    }
}

/// [`receive_agrees`], for one state and body.
pub proof fn lemma_receive(p: crate::transcription::primitives::Primitives,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires hs.state == crate::transcription::state_machine::ClientState::WaitSh,
    ensures receive_agrees(p, hs, body), ({
        let raw = crate::transcription::key_exchange::write_handshake(2, body);
        let step = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
        let f = hello_failures(hs.hello, hs.retry, body);
        &&& f.len() > 0 ==> step == crate::transcription::state_machine::HandshakeStep::Abort(f[0])
        &&& f.len() == 0 ==> match crate::transcription::key_exchange::read_server_hello(body) {
            Some(h) => step == if crate::transcription::key_exchange::is_hello_retry_request(h) {
                    crate::transcription::state_machine::accept_hello_retry_request(p, hs, h, raw)
                } else {
                    crate::transcription::state_machine::accept_server_hello(p, hs, h, raw)
                },
            None => false,
        }
    }),
{
    super::auth::lemma_raw(2, body);
    lemma_read_server_hello(body);
    let raw = crate::transcription::key_exchange::write_handshake(2, body);
    assert(crate::transcription::state_machine::receive_handshake_message(p, hs, raw)
        == crate::transcription::state_machine::receive_server_hello(p, hs, body, raw));
    let f = hello_failures(hs.hello, hs.retry, body);
    match crate::transcription::key_exchange::read_server_hello_any_version(body) {
        None => {},
        Some(any) => {
            if crate::transcription::key_exchange::is_hello_retry_request(any) {
                let rest = match crate::transcription::key_exchange::read_server_hello(body) {
                    None => seq![crate::transcription::alerts::ClientError::Malformed],
                    Some(hello) => crate::transcription::key_exchange::hello_retry_request_failures(hs.hello, hello),
                };
                if hs.retry is None {
                    assert(f =~= rest);
                }
            } else if crate::transcription::extensions::find_extension(any.extensions, 43) is None {
                let older = crate::transcription::key_exchange::older_server_hello_failures(any);
                assert(older.len() > 0);
            }
        },
    }
}

/// **The hello theorem.** For every body, every session ID and retry flag,
/// and every transcription state in WAIT_SH that matches the crate's
/// profile: `validate` rejects exactly when the transcription has a
/// failure, with the alert of one of them; on acceptance the selection is
/// the transcription's (the cookie, or the server's X25519 share); and the
/// transcription's step aborts with its first failure or accepts.
pub proof fn theorem_hello_equivalence()
    ensures
        forall|sent: crate::transcription::key_exchange::ClientHello,
            retry: Option<crate::transcription::key_exchange::RetryRecord>,
            session_id: Seq<u8>, retried: bool, body: Seq<u8>|
            (exists|offers: Seq<u16>| sent_is_profile(sent, session_id, offers))
                && retry_is_profile(retried, retry)
                && session_id.len() <= 32
                && body.len() <= crate::transcript::spec::MAX_BODY
            ==> #[trigger] hello_agrees(crate::hello::spec::validate(session_id, retried, body), sent, retry, body),
        forall|p: crate::transcription::primitives::Primitives,
            hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            hs.state == crate::transcription::state_machine::ClientState::WaitSh ==> #[trigger] receive_agrees(p, hs, body),
{
    assert forall|sent: crate::transcription::key_exchange::ClientHello,
        retry: Option<crate::transcription::key_exchange::RetryRecord>,
        session_id: Seq<u8>, retried: bool, body: Seq<u8>|
        (exists|offers: Seq<u16>| sent_is_profile(sent, session_id, offers))
            && retry_is_profile(retried, retry)
            && session_id.len() <= 32
            && body.len() <= crate::transcript::spec::MAX_BODY
        implies #[trigger] hello_agrees(crate::hello::spec::validate(session_id, retried, body), sent, retry, body) by {
        let offers = choose|offers: Seq<u16>| sent_is_profile(sent, session_id, offers);
        lemma_validate(sent, retry, offers, session_id, retried, body);
    }
    assert forall|p: crate::transcription::primitives::Primitives,
        hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        hs.state == crate::transcription::state_machine::ClientState::WaitSh implies #[trigger] receive_agrees(p, hs, body) by {
        lemma_receive(p, hs, body);
    }
}

} // verus!
