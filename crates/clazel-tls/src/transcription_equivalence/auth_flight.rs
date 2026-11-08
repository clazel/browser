//! RFC 8446 §4.3.1, §4.3.2, §4.4.2 and Appendix A.1: the
//! EncryptedExtensions, CertificateRequest and Certificate steps of
//! `auth/spec.rs`'s `step` proven equal to the clean-room transcription's
//! `receive_handshake_message` in WAIT_EE, WAIT_CERT_CR and WAIT_CERT:
//! [`theorem_auth_flight_equivalence`]. With [`super::auth`]'s
//! CertificateVerify and Finished steps this covers every message of the
//! server's flight.
//!
//! How rejections are compared (the maintainer's decision on #139: no order
//! is chosen where the RFC ranks none): the crate rejects exactly when the
//! transcription does, and the crate's alert is that of *some* failure in the
//! transcription's list of failures of the message ([`alert_in`]); the
//! transcription's own alert is that of the first. The transcription's lists
//! (`encrypted_extensions_failures`, `certificate_request_failures`,
//! `certificate_failures`) hold every failure of the message's checks, not
//! only the first, so no transcription change was needed. Where the two
//! orders coincide the alerts are equal, which the theorem then also says.
//!
//! Domain, and why:
//! - **The message is the one the state expects.** A message of another type
//!   is refused on both sides, but the crate reads its body first, so a
//!   malformed one is `decode_error` on its side and `unexpected_message` on
//!   the transcription's. That is the multi-fault case again; it is not
//!   covered here.
//! - **Temporary, waiting on a clean-room transcription:** the bodies of the
//!   extensions the crate reads are well formed (`all_bodies_ok`), in
//!   EncryptedExtensions and CertificateRequest. The crate checks them
//!   (`ext_body_ok`: RFC 6066's empty `server_name` response, the syntax of
//!   `supported_groups`, `signature_algorithms_cert` and the others); the
//!   transcription does not yet. A separate clean-room session is adding
//!   them; this condition goes when they land.
//! - The crate's resource policies do not fire ([`super::auth::within_policy`],
//!   and an end-entity key of at most 16 KiB).
//! - Chain validation agrees ([`chain_agrees`]): the crate's validator takes
//!   the host, the clock and the Certificate body; the transcription's takes
//!   the parsed `certificate_list`. They agree when, for the body of every
//!   Certificate, both accept with the same key or both refuse, the crate's
//!   alert being what the transcription's `required_alert` makes of its.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Some failure of the list requires this alert.
pub open spec fn alert_in(alert: u8, failures: Seq<crate::transcription::alerts::ClientError>) -> bool {
    exists|i: int| 0 <= i < failures.len() && #[trigger] crate::transcription::alerts::required_alert(failures[i]) == alert as nat
}

/// The two certificate validators agree on every Certificate body.
pub open spec fn chain_agrees(v: crate::auth::spec::Verification, p: crate::transcription::primitives::Primitives,
    host: crate::host::spec::Host, now: u64) -> bool
{
    forall|body: Seq<u8>| (#[trigger] crate::spec::read_certificate(body)) is Some ==> {
        let entries = super::messages::certificate_view(crate::spec::read_certificate(body)->Some_0).certificate_list;
        match (v.chain)(host, now, body) {
            Ok(key) => (p.validate_certificate_chain)(entries) == crate::transcription::primitives::ChainResult::Accepted(key),
            Err(error) => exists|alert: nat|
                (p.validate_certificate_chain)(entries) == crate::transcription::primitives::ChainResult::Rejected(alert)
                && crate::transcription::alerts::required_alert(crate::transcription::alerts::ClientError::ChainRejected(alert))
                    == crate::auth::spec::certificate_alert(error) as nat,
        }
    }
}

/// The crate's step and the transcription's agree on one message, with
/// rejections compared by membership in `failures`.
pub open spec fn flight_agrees(p: crate::transcription::primitives::Primitives,
    crate_step: (crate::auth::spec::State, crate::auth::spec::Action),
    t_step: crate::transcription::state_machine::HandshakeStep,
    failures: Seq<crate::transcription::alerts::ClientError>) -> bool
{
    match crate_step.1 {
        crate::auth::spec::Action::Fail(alert) => match t_step {
            crate::transcription::state_machine::HandshakeStep::Abort(e) =>
                alert_in(alert, seq![e] + failures),
            _ => false,
        },
        crate::auth::spec::Action::None => match t_step {
            crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                actions.len() == 0 && !receive_key_changes && super::auth::auth_agrees(p, crate_step.0, handshake),
            _ => false,
        },
        _ => false,
    }
}

/// The crate's step on a body of the expected type, through its parser.
pub proof fn lemma_crate_receive(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    s: crate::auth::spec::State, t: u8, body: Seq<u8>)
    requires
        body.len() <= crate::transcript::spec::MAX_BODY,
        s.phase != crate::auth::spec::Phase::Failed && s.phase != crate::auth::spec::Phase::Closed,
    ensures
        crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(t, body))
            == match crate::spec::parse_handshake_body(t, body, 32) {
                crate::spec::Res::Err(error) => crate::auth::spec::fail(s, crate::spec::alert_of(error)),
                crate::spec::Res::Ok(message) => crate::auth::spec::dispatch(c, v, s, body, message),
            },
{
}

/// The crate's parser on the three message types.
pub proof fn lemma_parse(body: Seq<u8>)
    ensures
        crate::spec::parse_handshake_body(8, body, 32) == match crate::spec::read_encrypted_extensions(body) {
            None => crate::spec::Res::<crate::spec::HsMsg>::Err(crate::spec::ErrKind::Decode),
            Some(es) => match crate::spec::check_extensions(es, crate::spec::MsgKind::Ee) {
                Some(k) => crate::spec::Res::Err(k),
                None => crate::spec::Res::Ok(crate::spec::HsMsg::EncryptedExtensions(es)),
            },
        },
        crate::spec::parse_handshake_body(13, body, 32) == match crate::spec::read_certificate_request(body) {
            None => crate::spec::Res::<crate::spec::HsMsg>::Err(crate::spec::ErrKind::Decode),
            Some(r) => match crate::spec::check_extensions(r.extensions, crate::spec::MsgKind::Cr) {
                Some(k) => crate::spec::Res::Err(k),
                None => crate::spec::Res::Ok(crate::spec::HsMsg::CertificateRequest(r)),
            },
        },
        crate::spec::parse_handshake_body(11, body, 32) == match crate::spec::read_certificate(body) {
            None => crate::spec::Res::<crate::spec::HsMsg>::Err(crate::spec::ErrKind::Decode),
            Some(cert) => match crate::spec::certificate_entries_error(cert.entries) {
                Some(k) => crate::spec::Res::Err(k),
                None => crate::spec::Res::Ok(crate::spec::HsMsg::Certificate(cert)),
            },
        },
{
}

/// The transcription's step on the three message types in their states.
pub proof fn lemma_t_receive(p: crate::transcription::primitives::Primitives,
    hs: crate::transcription::state_machine::ClientHandshake, t: u8, body: Seq<u8>)
    ensures ({
        let raw = crate::transcription::key_exchange::write_handshake(t as nat, body);
        let step = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
        &&& (hs.state == crate::transcription::state_machine::ClientState::WaitEe && t == 8 ==>
            step == crate::transcription::state_machine::receive_encrypted_extensions(hs, body, raw))
        &&& (hs.state == crate::transcription::state_machine::ClientState::WaitCertCr && t == 13 ==>
            step == crate::transcription::state_machine::receive_certificate_request(hs, body, raw))
        &&& ((hs.state == crate::transcription::state_machine::ClientState::WaitCertCr
                || hs.state == crate::transcription::state_machine::ClientState::WaitCert) && t == 11 ==>
            step == crate::transcription::state_machine::receive_certificate(p, hs, body, raw))
    }),
{
    super::auth::lemma_raw(t, body);
}

/// §4.3.1 syntax: EncryptedExtensions reads the same on both sides.
pub proof fn lemma_read_ee(body: Seq<u8>)
    ensures
        match crate::spec::read_encrypted_extensions(body) {
            None => crate::transcription::authentication::read_encrypted_extensions(body) is None,
            Some(es) => crate::transcription::authentication::read_encrypted_extensions(body)
                == Some(crate::transcription::authentication::EncryptedExtensions { extensions: super::messages::exts_view(es) }),
        },
{
    super::messages::lemma_read_exts(body, 0, 65535);
}

/// §4.3.2 syntax: CertificateRequest reads the same on both sides.
pub proof fn lemma_read_cr(body: Seq<u8>)
    ensures
        match crate::spec::read_certificate_request(body) {
            None => crate::transcription::authentication::read_certificate_request(body) is None,
            Some(r) => crate::transcription::authentication::read_certificate_request(body)
                == Some(crate::transcription::authentication::CertificateRequest {
                    certificate_request_context: r.context, extensions: super::messages::exts_view(r.extensions) }),
        },
{
    super::messages::lemma_read_vec(body, 0, 255);
    match crate::spec::read_vec(body, 0, 255) {
        None => {},
        Some((ctx, r1)) => { super::messages::lemma_read_exts(r1, 2, 65535); },
    }
}

/// `find_extension` finds an extension exactly when `has_ext` does.
pub proof fn lemma_find(es: Seq<crate::spec::Ext>, t: u16)
    ensures
        crate::spec::has_ext(es, t)
            == (crate::transcription::extensions::find_extension(super::messages::exts_view(es), t as nat) is Some),
        crate::hello::spec::extension(es, t)
            == crate::transcription::extensions::find_extension(super::messages::exts_view(es), t as nat),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_find(es.skip(1), t);
    }
}

/// In a Certificate entry, the table admits no extension whose body the
/// crate reads, so its body check never fires there.
pub proof fn lemma_ct_bodies(es: Seq<crate::spec::Ext>)
    requires crate::spec::all_allowed(es, crate::spec::MsgKind::Ct),
    ensures crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ct),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_ct_bodies(es.skip(1));
    }
}

/// The Certificate entries: the crate's first per-entry error is in the
/// transcription's per-entry failures, and with none, those failures are
/// all "not offered", present exactly when the crate's offered rule fails.
pub proof fn lemma_entries(entries: Seq<crate::spec::CertificateEntry>, sent: crate::transcription::key_exchange::ClientHello,
    offers: Seq<u16>)
    requires super::extensions::nats(offers) == crate::transcription::extensions::extension_types(sent.extensions),
    ensures ({
        let failures = crate::transcription::authentication::certificate_entries_failures(sent,
            entries.map_values(|e: crate::spec::CertificateEntry| super::messages::entry_view(e)));
        match crate::spec::certificate_entries_error(entries) {
            Some(k) => crate::spec::alert_of(k) == 47 && alert_in(47, failures),
            None => {
                &&& (failures.len() == 0) == crate::auth::spec::certificate_extensions_offered(entries, offers)
                &&& forall|i: int| 0 <= i < failures.len() ==>
                    failures[i] == crate::transcription::alerts::ClientError::ExtensionNotOffered
            },
        }
    }),
    decreases entries.len(),
{
    let view = entries.map_values(|e: crate::spec::CertificateEntry| super::messages::entry_view(e));
    let failures = crate::transcription::authentication::certificate_entries_failures(sent, view);
    if entries.len() > 0 {
        let first = entries[0];
        let rest = entries.skip(1);
        assert(view.subrange(1, view.len() as int) =~= rest.map_values(|e: crate::spec::CertificateEntry| super::messages::entry_view(e)));
        lemma_entries(rest, sent, offers);
        let es = first.extensions;
        let ev = super::messages::exts_view(es);
        let mine = crate::transcription::extensions::response_block_failures(ev,
            crate::transcription::extensions::extension_types(sent.extensions), crate::transcription::extensions::TableMessage::Ct);
        let tail = crate::transcription::authentication::certificate_entries_failures(sent,
            rest.map_values(|e: crate::spec::CertificateEntry| super::messages::entry_view(e)));
        assert(failures == mine + tail);
        super::extensions::lemma_unique(es);
        super::extensions::lemma_all_allowed(es, crate::spec::MsgKind::Ct);
        super::extensions::lemma_offered(es, offers, crate::spec::MsgKind::Ct);
        if crate::spec::exts_unique(es) && crate::spec::all_allowed(es, crate::spec::MsgKind::Ct) {
            lemma_ct_bodies(es);
            assert(crate::spec::check_extensions(es, crate::spec::MsgKind::Ct) is None);
            match crate::spec::certificate_entries_error(rest) {
                Some(k) => {
                    let i = choose|i: int| 0 <= i < tail.len()
                        && #[trigger] crate::transcription::alerts::required_alert(tail[i]) == 47nat;
                    assert(failures[mine.len() + i] == tail[i]);
                },
                None => {
                    assert forall|i: int| 0 <= i < failures.len() implies
                        failures[i] == crate::transcription::alerts::ClientError::ExtensionNotOffered by {
                        if i >= mine.len() { assert(failures[i] == tail[i - mine.len()]); }
                    }
                },
            }
        } else {
            assert(mine.len() > 0);
            assert(crate::transcription::alerts::required_alert(mine[0]) == 47nat);
            assert(failures[0] == mine[0]);
        }
    }
}

/// WAIT_EE: one EncryptedExtensions body. The two orders coincide, so the
/// alert is the same.
pub proof fn lemma_ee(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives, s: crate::auth::spec::State,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        super::schedule::crypto_agrees(c, p),
        super::auth::auth_agrees(p, s, hs),
        s.phase == crate::auth::spec::Phase::EncryptedExtensions,
        super::auth::within_policy(s, body),
        crate::spec::read_encrypted_extensions(body) matches Some(es) ==> crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ee),
    ensures
        super::auth::step_agrees(p, crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(8, body)),
            crate::transcription::state_machine::receive_handshake_message(p, hs,
                crate::transcription::key_exchange::write_handshake(8, body))),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::parse_handshake_body);
    let raw = crate::transcription::key_exchange::write_handshake(8, body);
    super::auth::lemma_raw(8, body);
    lemma_crate_receive(c, v, s, 8, body);
    lemma_parse(body);
    lemma_t_receive(p, hs, 8, body);
    lemma_read_ee(body);
    match crate::spec::read_encrypted_extensions(body) {
        None => {},
        Some(es) => {
            super::extensions::lemma_unique(es);
            super::extensions::lemma_all_allowed(es, crate::spec::MsgKind::Ee);
            super::extensions::lemma_offered(es, s.config.extensions, crate::spec::MsgKind::Ee);
            if crate::spec::check_extensions(es, crate::spec::MsgKind::Ee) is None
                && crate::auth::spec::extensions_offered(es, s.config.extensions)
            {
                let kind = crate::transcript::spec::Kind::EncryptedExtensions;
                assert(crate::transcript::spec::step(c.hash, s.transcript, kind, body) is Ok);
                super::transcript::lemma_step(p, s.transcript, hs.transcript, hs.retry is Some, kind, body);
                super::transcript::lemma_write_handshake(8, body);
            }
        },
    }
}

/// WAIT_CERT_CR: one CertificateRequest body. The orders coincide in alert
/// (every check but the missing extension is illegal_parameter).
pub proof fn lemma_cr(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives, s: crate::auth::spec::State,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        super::schedule::crypto_agrees(c, p),
        super::auth::auth_agrees(p, s, hs),
        s.phase == crate::auth::spec::Phase::CertificateOrRequest,
        super::auth::within_policy(s, body),
        crate::spec::read_certificate_request(body) matches Some(r) ==> crate::spec::all_bodies_ok(r.extensions, crate::spec::MsgKind::Cr),
    ensures
        super::auth::step_agrees(p, crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(13, body)),
            crate::transcription::state_machine::receive_handshake_message(p, hs,
                crate::transcription::key_exchange::write_handshake(13, body))),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::parse_handshake_body);
    let raw = crate::transcription::key_exchange::write_handshake(13, body);
    super::auth::lemma_raw(13, body);
    lemma_crate_receive(c, v, s, 13, body);
    lemma_parse(body);
    lemma_t_receive(p, hs, 13, body);
    lemma_read_cr(body);
    match crate::spec::read_certificate_request(body) {
        None => {},
        Some(r) => {
            let es = r.extensions;
            super::extensions::lemma_unique(es);
            super::extensions::lemma_all_allowed(es, crate::spec::MsgKind::Cr);
            lemma_find(es, 13);
            lemma_signature_algorithms_body(es);
            if crate::spec::check_extensions(es, crate::spec::MsgKind::Cr) is None && r.context.len() == 0
                && crate::spec::has_ext(es, 13)
            {
                let kind = crate::transcript::spec::Kind::CertificateRequest;
                let s1 = crate::auth::spec::State { requested: true, ..s };
                assert(crate::transcript::spec::step(c.hash, s1.transcript, kind, body) is Ok);
                super::transcript::lemma_step(p, s1.transcript, hs.transcript, hs.retry is Some, kind, body);
                super::transcript::lemma_write_handshake(13, body);
            }
        },
    }
}

/// In a block whose bodies are well formed, a signature_algorithms
/// extension reads as a SignatureSchemeList on the transcription's side.
pub proof fn lemma_signature_algorithms_body(es: Seq<crate::spec::Ext>)
    ensures
        crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Cr) ==>
            match crate::transcription::extensions::find_extension(super::messages::exts_view(es), 13) {
                Some(data) => crate::transcription::extensions::read_signature_scheme_list(data) is Some,
                None => true,
            },
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_signature_algorithms_body(es.skip(1));
        if es[0].etype == 13 && crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Cr) {
            lemma_schemes_list(es[0].data);
        }
    }
}

/// §4.2.3 syntax: a SignatureSchemeList the crate reads, the transcription
/// reads.
pub proof fn lemma_schemes_list(data: Seq<u8>)
    ensures crate::spec::read_signature_schemes(data) is Some ==> crate::transcription::extensions::read_signature_scheme_list(data) is Some,
{
    super::messages::lemma_read_vec(data, 2, 0xfffe);
    if crate::spec::read_signature_schemes(data) is Some {
        match crate::spec::read_vec(data, 2, 0xfffe) {
            None => {},
            Some((body, rest)) => { lemma_u16s(body); },
        }
    }
}

/// A body of `uint16`s the crate reads, the transcription reads.
pub proof fn lemma_u16s(body: Seq<u8>)
    ensures crate::spec::read_u16s(body) is Some ==> crate::transcription::presentation::read_uint16_list(body) is Some,
    decreases body.len(),
{
    if body.len() >= 2 {
        assert(body.skip(2) =~= body.subrange(2, body.len() as int));
        lemma_u16s(body.skip(2));
    }
}

/// WAIT_CERT_CR or WAIT_CERT: one Certificate body. The orders differ, so
/// the crate's alert is compared by membership.
#[verifier::rlimit(200)]
pub proof fn lemma_certificate(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives, s: crate::auth::spec::State,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        super::schedule::crypto_agrees(c, p),
        super::auth::auth_agrees(p, s, hs),
        s.phase == crate::auth::spec::Phase::CertificateOrRequest || s.phase == crate::auth::spec::Phase::Certificate,
        super::auth::within_policy(s, body),
        chain_agrees(v, p, s.config.host, s.config.now),
        (v.chain)(s.config.host, s.config.now, body) matches Ok(key) ==> key.len() <= crate::auth::spec::MAX_KEY,
    ensures
        flight_agrees(p, crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(11, body)),
            crate::transcription::state_machine::receive_handshake_message(p, hs,
                crate::transcription::key_exchange::write_handshake(11, body)),
            match crate::transcription::authentication::read_certificate(body) {
                Some(m) => crate::transcription::authentication::certificate_failures(hs.hello, m),
                None => seq![],
            }),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::parse_handshake_body);
    let raw = crate::transcription::key_exchange::write_handshake(11, body);
    super::auth::lemma_raw(11, body);
    lemma_crate_receive(c, v, s, 11, body);
    lemma_parse(body);
    lemma_t_receive(p, hs, 11, body);
    super::messages::lemma_read_certificate(body);
    match crate::spec::read_certificate(body) {
        None => {
            let t = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
            assert(t == crate::transcription::state_machine::HandshakeStep::Abort(crate::transcription::alerts::ClientError::Malformed));
            assert(crate::transcription::alerts::required_alert(seq![crate::transcription::alerts::ClientError::Malformed][0]) == 50nat);
            assert((seq![crate::transcription::alerts::ClientError::Malformed] + Seq::<crate::transcription::alerts::ClientError>::empty())[0] == crate::transcription::alerts::ClientError::Malformed);
            assert(alert_in(50, seq![crate::transcription::alerts::ClientError::Malformed] + Seq::<crate::transcription::alerts::ClientError>::empty()));
        },
        Some(cert) => {
            let m = super::messages::certificate_view(cert);
            let failures = crate::transcription::authentication::certificate_failures(hs.hello, m);
            let head = crate::transcription::alerts::fails_if(m.certificate_request_context.len() != 0,
                    crate::transcription::alerts::ClientError::CertificateContextNotEmpty)
                + crate::transcription::alerts::fails_if(m.certificate_list.len() == 0,
                    crate::transcription::alerts::ClientError::EmptyServerCertificate);
            let entries_failures = crate::transcription::authentication::certificate_entries_failures(hs.hello, m.certificate_list);
            assert(failures == head + entries_failures);
            lemma_entries(cert.entries, hs.hello, s.config.extensions);
            let t = crate::transcription::state_machine::receive_handshake_message(p, hs, raw);
            let all = |e: crate::transcription::alerts::ClientError| seq![e] + failures;
            match crate::spec::certificate_entries_error(cert.entries) {
                Some(k) => {
                    let i = choose|i: int| 0 <= i < entries_failures.len()
                        && #[trigger] crate::transcription::alerts::required_alert(entries_failures[i]) == 47nat;
                    assert(failures[head.len() + i] == entries_failures[i]);
                    assert(failures.len() > 0);
                    assert(t == crate::transcription::state_machine::HandshakeStep::Abort(failures[0]));
                    assert((seq![failures[0]] + failures)[1 + head.len() + i] == entries_failures[i]);
                    assert(crate::transcription::alerts::required_alert((seq![failures[0]] + failures)[1 + head.len() + i]) == 47nat);
                    assert(alert_in(47, seq![failures[0]] + failures));
                },
                None => {
                    if cert.context.len() != 0 {
                        assert(failures[0] == crate::transcription::alerts::ClientError::CertificateContextNotEmpty);
                        assert((seq![failures[0]] + failures)[0] == failures[0]);
                        assert(crate::transcription::alerts::required_alert((seq![failures[0]] + failures)[0]) == crate::transcription::alerts::required_alert(failures[0]));
                    } else if cert.entries.len() == 0 {
                        assert(failures[0] == crate::transcription::alerts::ClientError::EmptyServerCertificate);
                        assert((seq![failures[0]] + failures)[0] == failures[0]);
                        assert(crate::transcription::alerts::required_alert((seq![failures[0]] + failures)[0]) == crate::transcription::alerts::required_alert(failures[0]));
                    } else if !crate::auth::spec::certificate_extensions_offered(cert.entries, s.config.extensions) {
                        assert(head.len() == 0);
                        assert(failures[0] == crate::transcription::alerts::ClientError::ExtensionNotOffered);
                        assert((seq![failures[0]] + failures)[0] == failures[0]);
                        assert(crate::transcription::alerts::required_alert((seq![failures[0]] + failures)[0]) == crate::transcription::alerts::required_alert(failures[0]));
                    } else {
                        assert(failures.len() == 0);
                        assert(chain_agrees(v, p, s.config.host, s.config.now));
                        assert(crate::spec::read_certificate(body) is Some);
                        match (v.chain)(s.config.host, s.config.now, body) {
                            Err(error) => {
                                let alert = choose|alert: nat|
                                    (p.validate_certificate_chain)(m.certificate_list) == crate::transcription::primitives::ChainResult::Rejected(alert)
                                    && crate::transcription::alerts::required_alert(crate::transcription::alerts::ClientError::ChainRejected(alert))
                                        == crate::auth::spec::certificate_alert(error) as nat;
                                let e = crate::transcription::alerts::ClientError::ChainRejected(alert);
                                assert(t == crate::transcription::state_machine::HandshakeStep::Abort(e));
                                assert((seq![e] + failures)[0] == e);
                                assert(crate::transcription::alerts::required_alert((seq![e] + failures)[0]) == crate::auth::spec::certificate_alert(error) as nat);
                            },
                            Ok(key) => {
                                let kind = crate::transcript::spec::Kind::Certificate;
                                let s1 = crate::auth::spec::State { key, chain_checked: true, ..s };
                                assert(crate::transcript::spec::step(c.hash, s1.transcript, kind, body) is Ok);
                                super::transcript::lemma_step(p, s1.transcript, hs.transcript, hs.retry is Some, kind, body);
                                super::transcript::lemma_write_handshake(11, body);
                            },
                        }
                    }
                },
            }
        },
    }
}

/// RFC 8446 §4.3.1, §4.3.2, §4.4.2 and Appendix A.1, for every related pair
/// of states and every body of the expected type, under the domain above:
/// the crate's EncryptedExtensions and CertificateRequest steps fail with
/// the transcription's alert or both go on with related states; its
/// Certificate step rejects exactly when the transcription's does, with an
/// alert of one of the transcription's failures, or both go on.
pub proof fn theorem_auth_flight_equivalence(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
    ensures
        forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            #[trigger] super::auth::auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::EncryptedExtensions
                && super::auth::within_policy(s, body)
                && (crate::spec::read_encrypted_extensions(body) matches Some(es) ==> crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ee)) ==>
                super::auth::step_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(8, body)),
                    crate::transcription::state_machine::receive_handshake_message(p, hs,
                        crate::transcription::key_exchange::write_handshake(8, body))),
        forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            #[trigger] super::auth::auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::CertificateOrRequest
                && super::auth::within_policy(s, body)
                && (crate::spec::read_certificate_request(body) matches Some(r) ==> crate::spec::all_bodies_ok(r.extensions, crate::spec::MsgKind::Cr)) ==>
                super::auth::step_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(13, body)),
                    crate::transcription::state_machine::receive_handshake_message(p, hs,
                        crate::transcription::key_exchange::write_handshake(13, body))),
        forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            #[trigger] super::auth::auth_agrees(p, s, hs)
                && (s.phase == crate::auth::spec::Phase::CertificateOrRequest || s.phase == crate::auth::spec::Phase::Certificate)
                && super::auth::within_policy(s, body)
                && chain_agrees(v, p, s.config.host, s.config.now)
                && ((v.chain)(s.config.host, s.config.now, body) matches Ok(key) ==> key.len() <= crate::auth::spec::MAX_KEY) ==>
                flight_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(11, body)),
                    crate::transcription::state_machine::receive_handshake_message(p, hs,
                        crate::transcription::key_exchange::write_handshake(11, body)),
                    match crate::transcription::authentication::read_certificate(body) {
                        Some(m) => crate::transcription::authentication::certificate_failures(hs.hello, m),
                        None => seq![],
                    }),
{
    assert forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        #[trigger] super::auth::auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::EncryptedExtensions
            && super::auth::within_policy(s, body)
            && (crate::spec::read_encrypted_extensions(body) matches Some(es) ==> crate::spec::all_bodies_ok(es, crate::spec::MsgKind::Ee)) implies
            super::auth::step_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(8, body)),
                crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(8, body)))
    by { lemma_ee(c, v, p, s, hs, body); }
    assert forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        #[trigger] super::auth::auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::CertificateOrRequest
            && super::auth::within_policy(s, body)
            && (crate::spec::read_certificate_request(body) matches Some(r) ==> crate::spec::all_bodies_ok(r.extensions, crate::spec::MsgKind::Cr)) implies
            super::auth::step_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(13, body)),
                crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(13, body)))
    by { lemma_cr(c, v, p, s, hs, body); }
    assert forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        #[trigger] super::auth::auth_agrees(p, s, hs)
            && (s.phase == crate::auth::spec::Phase::CertificateOrRequest || s.phase == crate::auth::spec::Phase::Certificate)
            && super::auth::within_policy(s, body)
            && chain_agrees(v, p, s.config.host, s.config.now)
            && ((v.chain)(s.config.host, s.config.now, body) matches Ok(key) ==> key.len() <= crate::auth::spec::MAX_KEY) implies
            flight_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(11, body)),
                crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(11, body)),
                match crate::transcription::authentication::read_certificate(body) {
                    Some(m) => crate::transcription::authentication::certificate_failures(hs.hello, m),
                    None => seq![],
                })
    by { lemma_certificate(c, v, p, s, hs, body); }
}

} // verus!
