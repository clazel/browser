//! RFC 8446 §4.4.3, §4.4.4 and Appendix A.1: the CertificateVerify and
//! Finished steps of `auth/spec.rs`'s `step` proven equal to the clean-room
//! transcription's `state_machine::receive_handshake_message` in WAIT_CV and
//! WAIT_FINISHED, for every state, body and primitive:
//! [`theorem_auth_verify_finished_equivalence`].
//!
//! **Scope: two of the five messages of the server's flight.** The
//! EncryptedExtensions, CertificateRequest and Certificate steps are *not*
//! proven here; the PR lists why (two acceptance disagreements in
//! EncryptedExtensions, and the order of "unexpected in this state" against
//! syntax).
//!
//! How the states are related ([`auth_agrees`]): the crate's transcript
//! stands for the transcription's ([`super::transcript::represents`]), the
//! end-entity key and the two handshake traffic secrets are the same, the
//! crate's offered signature schemes are `client_spec::signatures()` and the
//! transcription's ClientHello offered the same list, a CertificateRequest
//! was received on one side exactly when on the other (with the empty
//! context, the only one either accepts in the main handshake), and the
//! crate's phase is the transcription's state.
//!
//! Primitives ([`verification_agrees`]): the crate's signature check
//! `signature(key, scheme, content, signature)` is the transcription's
//! `verify_signature(scheme, key, content, signature)`, and the
//! transcription's separate `key_compatible` is always true: the crate folds
//! "compatible with the key" (§4.4.3) into the verifier, which the
//! transcription's `primitives.rs` names as the instantiation that "loses
//! nothing but the alert". So a scheme incompatible with the key is
//! `decrypt_error` here, where a transcription with a separate check would
//! say `illegal_parameter` (its choice by §6's note).
//!
//! Domain: the crate's resource policies do not fire (a body above 2^18
//! bytes, or a transcript above 4 MiB, is its `internal_error`; the RFC and
//! the transcription have neither), and HMAC's outputs are 32 bytes
//! (HMAC-SHA256, which both sides model; without it the crate's transcript
//! bound could refuse the client Finished, which the transcription never
//! does).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's offered signature schemes, as the transcription's numbers.
pub open spec fn offered_schemes() -> Seq<nat> {
    seq![0x0403nat, 0x0503, 0x0804, 0x0805, 0x0806, 0x0807, 0x0401, 0x0501, 0x0601]
}

/// The crate's phase is the transcription's A.1 state.
pub open spec fn phase_is(phase: crate::auth::spec::Phase, state: crate::transcription::state_machine::ClientState) -> bool {
    match phase {
        crate::auth::spec::Phase::EncryptedExtensions => state == crate::transcription::state_machine::ClientState::WaitEe,
        crate::auth::spec::Phase::CertificateOrRequest => state == crate::transcription::state_machine::ClientState::WaitCertCr,
        crate::auth::spec::Phase::Certificate => state == crate::transcription::state_machine::ClientState::WaitCert,
        crate::auth::spec::Phase::CertificateVerify => state == crate::transcription::state_machine::ClientState::WaitCv,
        crate::auth::spec::Phase::Finished => state == crate::transcription::state_machine::ClientState::WaitFinished,
        _ => false,
    }
}

/// The crate's authentication state stands for the transcription's handshake.
pub open spec fn auth_agrees(p: crate::transcription::primitives::Primitives, s: crate::auth::spec::State,
    hs: crate::transcription::state_machine::ClientHandshake) -> bool
{
    &&& super::transcript::represents(p, s.transcript, hs.transcript, hs.retry is Some)
    &&& s.transcript.phase == crate::transcript::spec::Phase::Handshake
    &&& s.key == hs.server_public_key
    &&& s.config.server_secret == hs.server_handshake_traffic_secret
    &&& s.config.client_secret == hs.client_handshake_traffic_secret
    &&& s.config.signatures == crate::hello::client_spec::signatures()
    &&& crate::transcription::key_exchange::offered_signature_schemes(hs.hello) == offered_schemes()
    &&& super::extensions::nats(s.config.extensions) == crate::transcription::extensions::extension_types(hs.hello.extensions)
    &&& (s.requested <==> hs.certificate_request_context is Some)
    &&& (hs.certificate_request_context matches Some(context) ==> context.len() == 0)
    &&& phase_is(s.phase, hs.state)
}

/// The crate's signature check is the transcription's, with no separate key
/// compatibility check.
pub open spec fn verification_agrees(v: crate::auth::spec::Verification, p: crate::transcription::primitives::Primitives) -> bool {
    &&& forall|key: Seq<u8>, scheme: u16, content: Seq<u8>, signature: Seq<u8>|
        #[trigger] (v.signature)(key, scheme, content, signature) == (p.verify_signature)(scheme as nat, key, content, signature)
    &&& forall|scheme: nat, key: Seq<u8>| #[trigger] (p.key_compatible)(scheme, key)
}

/// Both sides model HMAC-SHA256: every output is 32 bytes.
pub open spec fn hmac_is_32(hmac: spec_fn(Seq<u8>, Seq<u8>) -> Seq<u8>) -> bool {
    forall|k: Seq<u8>, m: Seq<u8>| #[trigger] hmac(k, m).len() == 32
}

/// The crate's resource policies leave room for the step.
pub open spec fn within_policy(s: crate::auth::spec::State, body: Seq<u8>) -> bool {
    body.len() <= crate::transcript::spec::MAX_BODY
        && s.transcript.messages.len() + body.len() + 4 + 8 + 36 <= crate::transcript::spec::MAX_TRANSCRIPT
}

/// The crate's transcript cap (4 MiB, `internal_error`) refuses a message
/// the transcription accepts. It can fire only outside [`within_policy`].
pub open spec fn transcript_capped(s: crate::auth::spec::State, body: Seq<u8>,
    crate_step: (crate::auth::spec::State, crate::auth::spec::Action),
    t_step: crate::transcription::state_machine::HandshakeStep) -> bool
{
    crate_step.1 == crate::auth::spec::Action::Fail(crate::spec::INTERNAL_ERROR) && t_step is Proceed
        && !within_policy(s, body)
}

/// The crate's step and the transcription's agree on one message: the same
/// alert, or both go on, with the states still related and the same
/// messages sent.
pub open spec fn step_agrees(p: crate::transcription::primitives::Primitives,
    crate_step: (crate::auth::spec::State, crate::auth::spec::Action),
    t_step: crate::transcription::state_machine::HandshakeStep) -> bool
{
    match crate_step.1 {
        crate::auth::spec::Action::Fail(alert) => match t_step {
            crate::transcription::state_machine::HandshakeStep::Abort(e) =>
                crate::transcription::alerts::required_alert(e) == alert as nat,
            _ => false,
        },
        crate::auth::spec::Action::None => match t_step {
            crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                actions.len() == 0 && !receive_key_changes && auth_agrees(p, crate_step.0, handshake),
            _ => false,
        },
        _ => false,
    }
}

/// `write_handshake`'s type byte and body.
pub proof fn lemma_raw(t: u8, body: Seq<u8>)
    ensures ({
        let raw = crate::transcription::key_exchange::write_handshake(t as nat, body);
        &&& raw.len() == body.len() + 4
        &&& raw[0] == t
        &&& raw.subrange(4, raw.len() as int) == body
        &&& raw == crate::spec::write_handshake(t, body)
        &&& crate::spec::write_handshake(t, body).len() == body.len() + 4
    }),
{
    super::transcript::lemma_write_handshake(t, body);
    crate::lemmas_pl::lemma_be_bytes_len(body.len(), 3);
    let raw = crate::spec::write_handshake(t, body);
    assert(raw.subrange(4, raw.len() as int) =~= body);
}

/// The two schemes lists, element for element.
pub proof fn lemma_schemes(alg: u16)
    ensures
        crate::auth::spec::member(crate::hello::client_spec::signatures(), alg)
            == crate::transcription::presentation::list_has(offered_schemes(), alg as nat),
        crate::auth::spec::member(crate::hello::client_spec::signatures(), alg) && !crate::auth::spec::signature_scheme(alg)
            ==> crate::transcription::extensions::scheme_refers_solely_to_certificates(alg as nat),
        crate::auth::spec::signature_scheme(alg)
            ==> !crate::transcription::extensions::scheme_refers_solely_to_certificates(alg as nat),
{
    reveal_with_fuel(crate::auth::spec::member, 10);
    reveal_with_fuel(crate::transcription::presentation::list_has, 10);
    let sigs = crate::hello::client_spec::signatures();
    let ours = offered_schemes();
    assert(sigs.skip(1) =~= seq![0x0503u16, 0x0804u16, 0x0805u16, 0x0806u16, 0x0807u16, 0x0401u16, 0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1) =~= seq![0x0804u16, 0x0805u16, 0x0806u16, 0x0807u16, 0x0401u16, 0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1) =~= seq![0x0805u16, 0x0806u16, 0x0807u16, 0x0401u16, 0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1).skip(1) =~= seq![0x0806u16, 0x0807u16, 0x0401u16, 0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1).skip(1).skip(1) =~= seq![0x0807u16, 0x0401u16, 0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1).skip(1).skip(1).skip(1) =~= seq![0x0401u16, 0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1).skip(1).skip(1).skip(1).skip(1) =~= seq![0x0501u16, 0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1).skip(1).skip(1).skip(1).skip(1).skip(1) =~= seq![0x0601u16]);
    assert(sigs.skip(1).skip(1).skip(1).skip(1).skip(1).skip(1).skip(1).skip(1).skip(1) =~= Seq::<u16>::empty());
    let o1 = ours.subrange(1, 9);
    assert(o1 =~= seq![0x0503nat, 0x0804, 0x0805, 0x0806, 0x0807, 0x0401, 0x0501, 0x0601]);
    assert(o1.subrange(1, 8) =~= seq![0x0804nat, 0x0805, 0x0806, 0x0807, 0x0401, 0x0501, 0x0601]);
    assert(o1.subrange(1, 8).subrange(1, 7) =~= seq![0x0805nat, 0x0806, 0x0807, 0x0401, 0x0501, 0x0601]);
    assert(o1.subrange(1, 8).subrange(1, 7).subrange(1, 6) =~= seq![0x0806nat, 0x0807, 0x0401, 0x0501, 0x0601]);
    assert(o1.subrange(1, 8).subrange(1, 7).subrange(1, 6).subrange(1, 5) =~= seq![0x0807nat, 0x0401, 0x0501, 0x0601]);
    assert(o1.subrange(1, 8).subrange(1, 7).subrange(1, 6).subrange(1, 5).subrange(1, 4) =~= seq![0x0401nat, 0x0501, 0x0601]);
    assert(o1.subrange(1, 8).subrange(1, 7).subrange(1, 6).subrange(1, 5).subrange(1, 4).subrange(1, 3) =~= seq![0x0501nat, 0x0601]);
    assert(o1.subrange(1, 8).subrange(1, 7).subrange(1, 6).subrange(1, 5).subrange(1, 4).subrange(1, 3).subrange(1, 2) =~= seq![0x0601nat]);
    assert(o1.subrange(1, 8).subrange(1, 7).subrange(1, 6).subrange(1, 5).subrange(1, 4).subrange(1, 3).subrange(1, 2).subrange(1, 1) =~= Seq::<nat>::empty());
}

/// §4.4.3 syntax: the crate's CertificateVerify reader is the transcription's.
pub proof fn lemma_read_certificate_verify(body: Seq<u8>)
    ensures
        match crate::spec::read_certificate_verify(body) {
            None => crate::transcription::authentication::read_certificate_verify(body) is None,
            Some(cv) => crate::transcription::authentication::read_certificate_verify(body)
                == Some(crate::transcription::authentication::CertificateVerify {
                    algorithm: cv.algorithm as nat, signature: cv.signature }),
        },
{
    if body.len() >= 2 {
        let r = body.skip(2);
        assert(r =~= body.subrange(2, body.len() as int));
        super::messages::lemma_read_vec(r, 0, 65535);
        super::record::lemma_read_uint(body, 2);
        crate::lemmas_pl::lemma_be_value_bound(body.take(2));
        crate::lemmas_pl::lemma_pow256_widths();
    }
}

/// WAIT_CV: one CertificateVerify body.
pub proof fn lemma_certificate_verify(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives, s: crate::auth::spec::State,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        verification_agrees(v, p),
        auth_agrees(p, s, hs),
        s.phase == crate::auth::spec::Phase::CertificateVerify,
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures
        step_agrees(p, crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(15, body)),
            crate::transcription::state_machine::receive_handshake_message(p, hs,
                crate::transcription::key_exchange::write_handshake(15, body)))
            || transcript_capped(s, body, crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(15, body)),
                crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(15, body))),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::parse_handshake_body);
    let raw = crate::transcription::key_exchange::write_handshake(15, body);
    lemma_raw(15, body);
    lemma_read_certificate_verify(body);
    let retried = hs.retry is Some;
    lemma_t_dispatch(p, hs, 15, body);
    lemma_crate_cv(c, v, s, body);
    match crate::spec::read_certificate_verify(body) {
        None => {},
        Some(cv) => {
            let tcv = crate::transcription::authentication::CertificateVerify { algorithm: cv.algorithm as nat, signature: cv.signature };
            lemma_schemes(cv.algorithm);
            lemma_hash_represents(p, s.transcript, hs.transcript, retried);
            let th = crate::transcription::authentication::transcript_hash(p, hs.transcript, retried);
            lemma_cv_content(th);
            let input = crate::transcript::spec::certificate_verify_input(true, (c.hash)(s.transcript.messages));
            assert(input == crate::transcription::authentication::certificate_verify_content(
                crate::transcription::authentication::server_certificate_verify_context(), th));
            let failures = crate::transcription::authentication::certificate_verify_failures(p, hs.hello, tcv, hs.transcript, retried, hs.server_public_key);
            let checked = crate::auth::spec::State { signature_checked: true, ..s };
            if !crate::auth::spec::signature_scheme(cv.algorithm) || !crate::auth::spec::member(s.config.signatures, cv.algorithm) {
                assert(failures.len() > 0);
                assert(crate::transcription::alerts::required_alert(failures[0]) == 47);
            } else if !(v.signature)(s.key, cv.algorithm, input, cv.signature) {
                assert(failures =~= seq![crate::transcription::alerts::ClientError::CertificateVerifyFailed]);
            } else {
                assert(failures =~= Seq::<crate::transcription::alerts::ClientError>::empty());
                let kind = crate::transcript::spec::Kind::CertificateVerify;
                if crate::transcript::spec::step(c.hash, checked.transcript, kind, body) is Ok {
                    super::transcript::lemma_step(p, checked.transcript, hs.transcript, retried, kind, body);
                    super::transcript::lemma_write_handshake(15, body);
                } else {
                    assert(!within_policy(s, body));
                }
            }
        },
    }
}

/// The crate's step on a CertificateVerify body in its phase.
pub proof fn lemma_crate_cv(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    s: crate::auth::spec::State, body: Seq<u8>)
    requires s.phase == crate::auth::spec::Phase::CertificateVerify, body.len() <= crate::transcript::spec::MAX_BODY,
    ensures crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(15, body)) == match crate::spec::read_certificate_verify(body) {
        None => crate::auth::spec::fail(s, 50),
        Some(cv) => crate::auth::spec::on_verify(c, v, s, body, cv.algorithm, cv.signature),
    },
{
}

/// The crate's step on a Finished body in its phase.
pub proof fn lemma_crate_finished(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    s: crate::auth::spec::State, body: Seq<u8>)
    requires s.phase == crate::auth::spec::Phase::Finished, body.len() <= crate::transcript::spec::MAX_BODY,
    ensures crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(20, body))
        == if body.len() != 32 { crate::auth::spec::fail(s, 50) } else { crate::auth::spec::accept_finished(c, s, body) },
{
}

/// The transcription's step on one message in WAIT_CV or WAIT_FINISHED.
pub proof fn lemma_t_dispatch(p: crate::transcription::primitives::Primitives,
    hs: crate::transcription::state_machine::ClientHandshake, t: u8, body: Seq<u8>)
    requires
        hs.state == crate::transcription::state_machine::ClientState::WaitCv && t == 15
            || hs.state == crate::transcription::state_machine::ClientState::WaitFinished && t == 20,
    ensures ({
        let raw = crate::transcription::key_exchange::write_handshake(t as nat, body);
        crate::transcription::state_machine::receive_handshake_message(p, hs, raw)
            == if t == 15 { crate::transcription::state_machine::receive_certificate_verify(p, hs, body, raw) }
               else { crate::transcription::state_machine::receive_finished(p, hs, body, raw) }
    }),
{
    lemma_raw(t, body);
}

/// A represented transcript hashes to the transcription's Transcript-Hash.
pub proof fn lemma_hash_represents(p: crate::transcription::primitives::Primitives, s: crate::transcript::spec::State,
    messages: Seq<Seq<u8>>, retried: bool)
    requires super::transcript::represents(p, s, messages, retried),
    ensures (p.hash)(s.messages) == crate::transcription::authentication::transcript_hash(p, messages, retried),
{
}

/// §4.4.3: the server's signed content is the same bytes.
pub proof fn lemma_cv_content(th: Seq<u8>)
    ensures crate::transcript::spec::certificate_verify_input(true, th)
        == crate::transcription::authentication::certificate_verify_content(
            crate::transcription::authentication::server_certificate_verify_context(), th),
{
    assert(crate::transcript::spec::context(true) =~= crate::transcription::authentication::server_certificate_verify_context());
    super::transcript::lemma_repeat(0x20, 64);
    assert(Seq::new(64, |i: int| 32u8) =~= crate::transcription::presentation::repeat_byte(0x20, 64));
}

/// WAIT_FINISHED: one Finished body.
#[verifier::rlimit(60)]
pub proof fn lemma_finished(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives, s: crate::auth::spec::State,
    hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>)
    requires
        hmac_is_32(p.hmac),
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        auth_agrees(p, s, hs),
        s.phase == crate::auth::spec::Phase::Finished,
        body.len() <= crate::transcript::spec::MAX_BODY,
    ensures ({
        let (after, action) = crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(20, body));
        let t = crate::transcription::state_machine::receive_handshake_message(p, hs,
            crate::transcription::key_exchange::write_handshake(20, body));
        let retried = hs.retry is Some;
        match action {
            crate::auth::spec::Action::Fail(alert) => match t {
                crate::transcription::state_machine::HandshakeStep::Abort(e) =>
                    crate::transcription::alerts::required_alert(e) == alert as nat,
                _ => alert == crate::spec::INTERNAL_ERROR && !within_policy(s, body),
            },
            crate::auth::spec::Action::Send(flight) => match t {
                crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, receive_key_changes } => {
                    &&& receive_key_changes
                    &&& handshake.state == crate::transcription::state_machine::ClientState::Connected
                    &&& super::transcript::represents(p, after.transcript, handshake.transcript, retried)
                    // The flight is the messages the transcription sends, in order.
                    &&& flight == crate::transcription::presentation::concatenate(
                            handshake.transcript.subrange(hs.transcript.len() as int + 1, handshake.transcript.len() as int))
                    &&& actions == seq![crate::transcription::state_machine::Action::SetSendSecret(hs.client_handshake_traffic_secret)]
                        + crate::transcription::state_machine::send_each(
                            handshake.transcript.subrange(hs.transcript.len() as int + 1, handshake.transcript.len() - 1))
                        + seq![
                            crate::transcription::state_machine::Action::SendHandshake(handshake.transcript.last(), 0x0303),
                            crate::transcription::state_machine::Action::SetSendSecret(
                                crate::transcription::key_schedule::client_application_traffic_secret_0(p,
                                    crate::transcription::key_schedule::master_secret(p, hs.handshake_secret),
                                    hs.transcript.push(crate::transcription::key_exchange::write_handshake(20, body)), retried)),
                            crate::transcription::state_machine::Action::SetReceiveSecret(
                                crate::transcription::key_schedule::server_application_traffic_secret_0(p,
                                    crate::transcription::key_schedule::master_secret(p, hs.handshake_secret),
                                    hs.transcript.push(crate::transcription::key_exchange::write_handshake(20, body)), retried)),
                        ]
                    // The hash the dispatcher derives the application secrets from.
                    &&& after.application_hash == crate::transcription::authentication::transcript_hash(p,
                            hs.transcript.push(crate::transcription::key_exchange::write_handshake(20, body)), retried)
                },
                _ => false,
            },
            _ => false,
        }
    }),
{
    hide(crate::auth::spec::step);
    hide(crate::transcription::state_machine::receive_handshake_message);
    hide(crate::spec::parse_handshake_body);
    let raw = crate::transcription::key_exchange::write_handshake(20, body);
    lemma_raw(20, body);
    lemma_hash_represents(p, s.transcript, hs.transcript, hs.retry is Some);
    lemma_t_dispatch(p, hs, 20, body);
    lemma_crate_finished(c, v, s, body);
    super::keys::lemma_derive_on_transcript(c, p, s.config.server_secret, crate::schedule::spec::Label::Finished,
        s.transcript, hs.transcript, hs.retry is Some);
    let retried = hs.retry is Some;
    if body.len() == 32 && body == crate::schedule::spec::finished(c, s.config.server_secret, s.transcript.messages) {
        let fin = crate::transcript::spec::Kind::Finished;
        let s0 = crate::auth::spec::State { finished_checked: true, ..s };
        let ok1 = crate::transcript::spec::step(c.hash, s0.transcript, fin, body);
        let cb = crate::auth::spec::empty_certificate();
        let k11 = crate::transcript::spec::Kind::Certificate;
        if !(ok1 is Ok) {
            assert(!within_policy(s, body));
        } else if s.requested && !(crate::transcript::spec::step(c.hash, ok1->Ok_0, k11, cb) is Ok) {
            assert(!within_policy(s, body));
        } else if s.requested && !(crate::transcript::spec::step(c.hash,
            crate::transcript::spec::step(c.hash, ok1->Ok_0, k11, cb)->Ok_0, fin,
            crate::schedule::spec::finished(c, s.config.client_secret,
                crate::transcript::spec::step(c.hash, ok1->Ok_0, k11, cb)->Ok_0.messages)) is Ok) {
            assert(!within_policy(s, body));
        } else if !s.requested && !(crate::transcript::spec::step(c.hash, ok1->Ok_0, fin,
            crate::schedule::spec::finished(c, s.config.client_secret, ok1->Ok_0.messages)) is Ok) {
            assert(!within_policy(s, body));
        } else {
        assert(crate::transcript::spec::step(c.hash, s0.transcript, fin, body) is Ok);
        super::transcript::lemma_step(p, s0.transcript, hs.transcript, retried, fin, body);
        super::transcript::lemma_write_handshake(20, body);
        let t1 = crate::transcript::spec::step(c.hash, s0.transcript, fin, body)->Ok_0;
        let m1 = hs.transcript.push(raw);
        assert(super::transcript::represents(p, t1, m1, retried));
        // The client's Certificate, if requested.
        let cert_body = crate::auth::spec::empty_certificate();
        let cert_raw = crate::transcription::key_exchange::write_handshake(11, cert_body);
        let t_cert = crate::transcription::authentication::write_certificate(
            crate::transcription::authentication::Certificate { certificate_request_context: seq![], certificate_list: seq![] });
        assert(crate::transcription::authentication::write_certificate_entries(seq![]) =~= Seq::<u8>::empty());
        assert(crate::transcription::presentation::write_vector(seq![], 0xff) =~= seq![0u8]) by (compute_only);
        assert(crate::transcription::presentation::write_vector(seq![], 0xff_ffff) =~= seq![0u8, 0u8, 0u8]) by (compute_only);
        assert(cert_body =~= seq![0u8] + seq![0u8, 0u8, 0u8]);
        assert(t_cert == cert_raw);
        if s.requested {
            let context = hs.certificate_request_context->Some_0;
            assert(context =~= Seq::<u8>::empty());
            let t2 = crate::transcript::spec::step(c.hash, t1, crate::transcript::spec::Kind::Certificate, cert_body)->Ok_0;
            assert(crate::transcript::spec::step(c.hash, t1, crate::transcript::spec::Kind::Certificate, cert_body) is Ok);
            super::transcript::lemma_step(p, t1, m1, retried, crate::transcript::spec::Kind::Certificate, cert_body);
            super::transcript::lemma_write_handshake(11, cert_body);
            assert(super::transcript::represents(p, t2, m1.push(cert_raw), retried));
            assert(m1 + seq![cert_raw] =~= m1.push(cert_raw));
            super::keys::lemma_derive_on_transcript(c, p, s.config.client_secret, crate::schedule::spec::Label::Finished,
                t2, m1.push(cert_raw), retried);
            let own = crate::schedule::spec::finished(c, s.config.client_secret, t2.messages);
            lemma_raw(20, own);
            assert(own.len() == 32);
            assert(crate::transcript::spec::step(c.hash, t2, fin, own) is Ok);
            super::transcript::lemma_step(p, t2, m1.push(cert_raw), retried, fin, own);
            super::transcript::lemma_write_handshake(20, own);
            let t3 = crate::transcript::spec::step(c.hash, t2, fin, own)->Ok_0;
            let m3 = m1.push(cert_raw).push(crate::transcription::key_exchange::write_handshake(20, own));
            assert(super::transcript::represents(p, t3, m3, retried));
            super::transcript::lemma_write_handshake(11, cert_body);
            super::transcript::lemma_write_handshake(20, own);
            assert(m3.subrange(hs.transcript.len() as int + 1, m3.len() as int) =~= seq![cert_raw, crate::transcription::key_exchange::write_handshake(20, own)]);
            assert(m3.subrange(hs.transcript.len() as int + 1, m3.len() - 1) =~= seq![cert_raw]);
            assert(seq![cert_raw].subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
            assert(crate::transcription::presentation::concatenate(seq![crate::transcription::key_exchange::write_handshake(20, own)].subrange(1, 1)) =~= Seq::<u8>::empty());
            super::transcript::lemma_concatenate_one(crate::transcription::key_exchange::write_handshake(20, own));
            assert(seq![cert_raw, crate::transcription::key_exchange::write_handshake(20, own)].subrange(1, 2)
                =~= seq![crate::transcription::key_exchange::write_handshake(20, own)]);
            assert(crate::transcription::state_machine::send_each(seq![cert_raw].subrange(1, 1)) =~= Seq::<crate::transcription::state_machine::Action>::empty());
        } else {
            super::keys::lemma_derive_on_transcript(c, p, s.config.client_secret, crate::schedule::spec::Label::Finished,
                t1, m1, retried);
            let own = crate::schedule::spec::finished(c, s.config.client_secret, t1.messages);
            lemma_raw(20, own);
            assert(own.len() == 32);
            assert(crate::transcript::spec::step(c.hash, t1, fin, own) is Ok);
            super::transcript::lemma_step(p, t1, m1, retried, fin, own);
            super::transcript::lemma_write_handshake(20, own);
            let t3 = crate::transcript::spec::step(c.hash, t1, fin, own)->Ok_0;
            let m3 = m1.push(crate::transcription::key_exchange::write_handshake(20, own));
            assert(super::transcript::represents(p, t3, m3, retried));
            assert(m1 + Seq::<Seq<u8>>::empty() =~= m1);
            super::transcript::lemma_write_handshake(20, own);
            assert(m3.subrange(hs.transcript.len() as int + 1, m3.len() as int) =~= seq![crate::transcription::key_exchange::write_handshake(20, own)]);
            assert(m3.subrange(hs.transcript.len() as int + 1, m3.len() - 1) =~= Seq::<Seq<u8>>::empty());
            super::transcript::lemma_concatenate_one(crate::transcription::key_exchange::write_handshake(20, own));
            assert(Seq::<u8>::empty() + crate::spec::write_handshake(20, own) =~= crate::spec::write_handshake(20, own));
        }
        }
    }
}

/// RFC 8446 §4.4.3, §4.4.4 and Appendix A.1, for every related pair of
/// states and every body: in WAIT_CV and WAIT_FINISHED the crate's
/// authentication step and the transcription's fail with the same alert, or
/// both go on with the states still related; after the server Finished the
/// crate's client flight is the transcription's messages, in order, and the
/// hash it keeps for the application secrets is the transcription's
/// Transcript-Hash through the server Finished.
pub proof fn theorem_auth_verify_finished_equivalence(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    p: crate::transcription::primitives::Primitives)
    requires
        hmac_is_32(p.hmac),
        super::schedule::crypto_agrees(c, p),
        super::transcript::hash_is_32(p.hash),
        verification_agrees(v, p),
    ensures
        forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            #[trigger] auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::CertificateVerify && within_policy(s, body) ==>
                step_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(15, body)),
                    crate::transcription::state_machine::receive_handshake_message(p, hs,
                        crate::transcription::key_exchange::write_handshake(15, body))),
        forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
            #[trigger] auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::Finished && within_policy(s, body) ==>
                match (#[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(20, body))).1 {
                    crate::auth::spec::Action::Fail(alert) => match crate::transcription::state_machine::receive_handshake_message(p, hs,
                        crate::transcription::key_exchange::write_handshake(20, body)) {
                        crate::transcription::state_machine::HandshakeStep::Abort(e) =>
                            crate::transcription::alerts::required_alert(e) == alert as nat,
                        _ => false,
                    },
                    crate::auth::spec::Action::Send(flight) => match crate::transcription::state_machine::receive_handshake_message(p, hs,
                        crate::transcription::key_exchange::write_handshake(20, body)) {
                        crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                            receive_key_changes
                                && handshake.state == crate::transcription::state_machine::ClientState::Connected
                                && flight == crate::transcription::presentation::concatenate(
                                    handshake.transcript.subrange(hs.transcript.len() as int + 1, handshake.transcript.len() as int)),
                        _ => false,
                    },
                    _ => false,
                },
{
    assert forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        #[trigger] auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::CertificateVerify && within_policy(s, body) implies
            step_agrees(p, #[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(15, body)),
                crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(15, body)))
    by { lemma_certificate_verify(c, v, p, s, hs, body); }
    assert forall|s: crate::auth::spec::State, hs: crate::transcription::state_machine::ClientHandshake, body: Seq<u8>|
        #[trigger] auth_agrees(p, s, hs) && s.phase == crate::auth::spec::Phase::Finished && within_policy(s, body) implies
            match (#[trigger] crate::auth::spec::step(c, v, s, crate::auth::spec::Input::Handshake(20, body))).1 {
                crate::auth::spec::Action::Fail(alert) => match crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(20, body)) {
                    crate::transcription::state_machine::HandshakeStep::Abort(e) =>
                        crate::transcription::alerts::required_alert(e) == alert as nat,
                    _ => false,
                },
                crate::auth::spec::Action::Send(flight) => match crate::transcription::state_machine::receive_handshake_message(p, hs,
                    crate::transcription::key_exchange::write_handshake(20, body)) {
                    crate::transcription::state_machine::HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                        receive_key_changes
                            && handshake.state == crate::transcription::state_machine::ClientState::Connected
                            && flight == crate::transcription::presentation::concatenate(
                                handshake.transcript.subrange(hs.transcript.len() as int + 1, handshake.transcript.len() as int)),
                    _ => false,
                },
                _ => false,
            }
    by { lemma_finished(c, v, p, s, hs, body); }
}

} // verus!
