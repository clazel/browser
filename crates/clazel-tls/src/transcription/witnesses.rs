//! Witnesses that the definitions of this transcription do what their sections say.
//! Each is a concrete evaluation (`by (compute)`), so it shows a definition on one
//! input, and proves nothing for all inputs.
//!
//! Two sets of abstract primitives are used:
//! - [`trace_primitives`] is a lookup table of RFC 8448 §3's own values, keyed on the
//!   exact bytes the trace passes in. A wrong input to any primitive (a wrong label, a
//!   wrong transcript, a wrong secret) returns an empty sequence, and the run fails. So
//!   a passing run says the key schedule, the transcript and the order of messages feed
//!   each primitive what that independent trace fed it, and get out what it got.
//! - [`toy_primitives`] is a small keyed checksum, to drive the record layer with records
//!   this file builds, including ones that must be refused. These runs say nothing about
//!   the RFC beyond the transitions and alerts they name.
//!
//! Modelling choices: the toy server's messages are built with this transcription's own
//! encoders, so they are no evidence for the encoders. The RFC 8448 round trips are.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::alerts::*;
#[cfg(verus_only)]
use super::authentication::*;
#[cfg(verus_only)]
use super::connection::*;
#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::key_schedule::*;
#[cfg(verus_only)]
use super::post_handshake::*;
#[cfg(verus_only)]
use super::presentation::*;
#[cfg(verus_only)]
use super::primitives::*;
#[cfg(verus_only)]
use super::record::*;
#[cfg(verus_only)]
use super::rfc8448_data::*;
#[cfg(verus_only)]
use super::state_machine::*;

verus! {

// ==========================================================================
// RFC 8448 §3 as a table of primitives.
// ==========================================================================

/// No bytes.
pub open spec fn no_bytes() -> Seq<u8> {
    seq![]
}

/// The body of a handshake message.
pub open spec fn body_of(message: Seq<u8>) -> Seq<u8> {
    message.subrange(4, message.len() as int)
}

/// §3's Hash, for the transcripts the trace hashes.
pub open spec fn trace_hash(m: Seq<u8>) -> Seq<u8> {
    let through_sh = s3_client_hello() + s3_server_hello();
    let through_ct = through_sh + s3_encrypted_extensions() + s3_certificate();
    let through_cv = through_ct + s3_certificate_verify();
    let through_sf = through_cv + s3_server_finished();
    let through_cf = through_sf + s3_client_finished();
    if m.len() == 0 { s3_derived_for_handshake_hash() }
    else if m == through_sh { s3_c_hs_traffic_hash() }
    else if m == through_ct { s3_hash_through_certificate() }
    else if m == through_cv { s3_hash_through_certificate_verify() }
    else if m == through_sf { s3_c_ap_traffic_hash() }
    else if m == through_cf { s3_res_master_hash() }
    else { seq![] }
}

/// §3's HKDF-Extract.
pub open spec fn trace_extract(salt: Seq<u8>, ikm: Seq<u8>) -> Seq<u8> {
    if salt == zero_value() && ikm == zero_value() { s3_early_secret() }
    else if salt == s3_derived_for_handshake() && ikm == s3_shared_secret() { s3_handshake_secret() }
    else if salt == s3_derived_for_master() && ikm == zero_value() { s3_master_secret() }
    else { seq![] }
}

/// §3's HKDF-Expand with L = 32.
pub open spec fn trace_expand(prk: Seq<u8>, info: Seq<u8>, length: nat) -> Seq<u8> {
    if length != 32 { seq![] }
    else if prk == s3_early_secret() && info == s3_derived_for_handshake_info() { s3_derived_for_handshake() }
    else if prk == s3_handshake_secret() && info == s3_c_hs_traffic_info() { s3_c_hs_traffic() }
    else if prk == s3_handshake_secret() && info == s3_s_hs_traffic_info() { s3_s_hs_traffic() }
    else if prk == s3_handshake_secret() && info == s3_derived_for_master_info() { s3_derived_for_master() }
    else if prk == s3_master_secret() && info == s3_c_ap_traffic_info() { s3_c_ap_traffic() }
    else if prk == s3_master_secret() && info == s3_s_ap_traffic_info() { s3_s_ap_traffic() }
    else if prk == s3_master_secret() && info == s3_exp_master_info() { s3_exp_master() }
    else if prk == s3_master_secret() && info == s3_res_master_info() { s3_res_master() }
    else if prk == s3_s_hs_traffic() && info == s3_finished_info() { s3_server_finished_key() }
    else if prk == s3_c_hs_traffic() && info == s3_finished_info() { s3_client_finished_key() }
    else if prk == s3_res_master() && info == s3_resumption_info() { s3_resumption() }
    else { seq![] }
}

/// §3's HMAC.
pub open spec fn trace_hmac(key: Seq<u8>, message: Seq<u8>) -> Seq<u8> {
    if key == s3_server_finished_key() && message == s3_hash_through_certificate_verify() { s3_server_verify_data() }
    else if key == s3_client_finished_key() && message == s3_c_ap_traffic_hash() { s3_client_verify_data() }
    else { seq![] }
}

/// §3's primitives. The signature is checked only for what it covers; §3's RSA key is
/// not verified here. The AEAD is not used by the handshake layer.
pub open spec fn trace_primitives() -> Primitives {
    Primitives {
        hash: |m: Seq<u8>| trace_hash(m),
        hkdf_extract: |salt: Seq<u8>, ikm: Seq<u8>| trace_extract(salt, ikm),
        hkdf_expand: |prk: Seq<u8>, info: Seq<u8>, length: nat| trace_expand(prk, info, length),
        hmac: |key: Seq<u8>, message: Seq<u8>| trace_hmac(key, message),
        aead_encrypt: |key: Seq<u8>, nonce: Seq<u8>, additional: Seq<u8>, plaintext: Seq<u8>| seq![],
        aead_decrypt: |key: Seq<u8>, nonce: Seq<u8>, additional: Seq<u8>, ciphertext: Seq<u8>| None,
        x25519: |scalar: Seq<u8>, u: Seq<u8>|
            if scalar == s3_client_private() && u == s3_server_public() { s3_shared_secret() } else { seq![] },
        verify_signature: |scheme: nat, key: Seq<u8>, content: Seq<u8>, signature: Seq<u8>|
            scheme == rsa_pss_rsae_sha256() && key == seq![0xAAu8]
                && content == certificate_verify_content(server_certificate_verify_context(), s3_hash_through_certificate())
                && signature == body_of(s3_certificate_verify()).subrange(4, 132),
        key_compatible: |scheme: nat, key: Seq<u8>| true,
        validate_certificate_chain: |entries: Seq<CertificateEntry>| ChainResult::Accepted(seq![0xAAu8]),
    }
}

/// §3's ClientHello, decoded. Its first share is X25519's.
pub open spec fn s3_hello() -> ClientHello {
    read_client_hello(body_of(s3_client_hello()))->0
}

/// Runs the handshake layer over a list of messages; the actions are of the last one.
pub open spec fn run_messages(p: Primitives, hs: ClientHandshake, messages: Seq<Seq<u8>>, last: HandshakeStep) -> HandshakeStep
    decreases messages.len(),
{
    if messages.len() == 0 {
        last
    } else {
        match receive_handshake_message(p, hs, messages[0]) {
            HandshakeStep::Abort(e) => HandshakeStep::Abort(e),
            HandshakeStep::Proceed { handshake, actions, receive_key_changes } =>
                run_messages(p, handshake, messages.subrange(1, messages.len() as int),
                    HandshakeStep::Proceed { handshake, actions, receive_key_changes }),
        }
    }
}

/// RFC 8448 §3's server flight, through the state machine, from its own ClientHello.
pub open spec fn s3_run() -> HandshakeStep {
    let hs = start_handshake(s3_hello(), s3_client_private(), seq![]);
    run_messages(trace_primitives(), hs,
        seq![s3_server_hello(), s3_encrypted_extensions(), s3_certificate(), s3_certificate_verify(), s3_server_finished()],
        proceed(hs, seq![]))
}

/// §4.1 to §7, A.1: RFC 8448 §3's handshake runs to CONNECTED, and what comes out is the
/// trace's own client Finished message and secrets, with the actions in A.1's order.
proof fn rfc8448_s3_handshake_reaches_connected()
    ensures
        match s3_run() {
            HandshakeStep::Abort(_) => false,
            HandshakeStep::Proceed { handshake, actions, receive_key_changes } => {
                &&& handshake.state == ClientState::Connected
                &&& handshake.resumption_master_secret == s3_res_master()
                &&& handshake.exporter_master_secret == s3_exp_master()
                &&& receive_key_changes
                &&& actions == seq![
                    Action::SetSendSecret(s3_c_hs_traffic()),
                    Action::SendHandshake(s3_client_finished(), 0x0303),
                    Action::SetSendSecret(s3_c_ap_traffic()),
                    Action::SetReceiveSecret(s3_s_ap_traffic()),
                ]
            },
        },
{
    assert(match s3_run() {
        HandshakeStep::Abort(_) => false,
        HandshakeStep::Proceed { handshake, actions, receive_key_changes } => {
            &&& handshake.state == ClientState::Connected
            &&& handshake.resumption_master_secret == s3_res_master()
            &&& handshake.exporter_master_secret == s3_exp_master()
            &&& receive_key_changes
            &&& actions == seq![
                Action::SetSendSecret(s3_c_hs_traffic()),
                Action::SendHandshake(s3_client_finished(), 0x0303),
                Action::SetSendSecret(s3_c_ap_traffic()),
                Action::SetReceiveSecret(s3_s_ap_traffic()),
            ]
        },
    }) by (compute);
}

/// §7.1: the label encoding, against the `info` bytes the trace prints, for each label
/// the trace shows. The context of each is its printed `hash`.
proof fn rfc8448_labels()
    ensures
        hkdf_label(32, label_derived(), s3_derived_for_handshake_hash()) == s3_derived_for_handshake_info(),
        hkdf_label(32, label_c_hs_traffic(), s3_c_hs_traffic_hash()) == s3_c_hs_traffic_info(),
        hkdf_label(32, label_s_hs_traffic(), s3_s_hs_traffic_hash()) == s3_s_hs_traffic_info(),
        hkdf_label(32, label_c_ap_traffic(), s3_c_ap_traffic_hash()) == s3_c_ap_traffic_info(),
        hkdf_label(32, label_s_ap_traffic(), s3_s_ap_traffic_hash()) == s3_s_ap_traffic_info(),
        hkdf_label(32, label_exp_master(), s3_exp_master_hash()) == s3_exp_master_info(),
        hkdf_label(32, label_res_master(), s3_res_master_hash()) == s3_res_master_info(),
        hkdf_label(32, label_resumption(), s3_resumption_hash()) == s3_resumption_info(),
        hkdf_label(32, label_finished(), seq![]) == s3_finished_info(),
        hkdf_label(16, label_key(), seq![]) == s3_key_info_16(),
        hkdf_label(12, label_iv(), seq![]) == s3_iv_info(),
        hkdf_label(32, label_c_e_traffic(), s4_c_e_traffic_info().subrange(21, 53)) == s4_c_e_traffic_info(),
        hkdf_label(32, label_e_exp_master(), s4_e_exp_master_info().subrange(22, 54)) == s4_e_exp_master_info(),
{
    assert(hkdf_label(32, label_derived(), s3_derived_for_handshake_hash()) == s3_derived_for_handshake_info()) by (compute);
    assert(hkdf_label(32, label_c_hs_traffic(), s3_c_hs_traffic_hash()) == s3_c_hs_traffic_info()) by (compute);
    assert(hkdf_label(32, label_s_hs_traffic(), s3_s_hs_traffic_hash()) == s3_s_hs_traffic_info()) by (compute);
    assert(hkdf_label(32, label_c_ap_traffic(), s3_c_ap_traffic_hash()) == s3_c_ap_traffic_info()) by (compute);
    assert(hkdf_label(32, label_s_ap_traffic(), s3_s_ap_traffic_hash()) == s3_s_ap_traffic_info()) by (compute);
    assert(hkdf_label(32, label_exp_master(), s3_exp_master_hash()) == s3_exp_master_info()) by (compute);
    assert(hkdf_label(32, label_res_master(), s3_res_master_hash()) == s3_res_master_info()) by (compute);
    assert(hkdf_label(32, label_resumption(), s3_resumption_hash()) == s3_resumption_info()) by (compute);
    assert(hkdf_label(32, label_finished(), seq![]) == s3_finished_info()) by (compute);
    assert(hkdf_label(16, label_key(), seq![]) == s3_key_info_16()) by (compute);
    assert(hkdf_label(12, label_iv(), seq![]) == s3_iv_info()) by (compute);
    assert(hkdf_label(32, label_c_e_traffic(), s4_c_e_traffic_info().subrange(21, 53)) == s4_c_e_traffic_info()) by (compute);
    assert(hkdf_label(32, label_e_exp_master(), s4_e_exp_master_info().subrange(22, 54)) == s4_e_exp_master_info()) by (compute);
}

/// §4.6.1: the PSK of the trace's ticket (nonce 00 00).
proof fn rfc8448_ticket_psk()
    ensures
        ticket_psk(trace_primitives(), s3_res_master(), read_new_session_ticket(body_of(s3_new_session_ticket()))->0.ticket_nonce)
            == s3_resumption(),
{
    assert(ticket_psk(trace_primitives(), s3_res_master(), read_new_session_ticket(body_of(s3_new_session_ticket()))->0.ticket_nonce)
        == s3_resumption()) by (compute);
}

/// §4: every message of the trace decodes through `select`, and encodes back to its bytes.
proof fn rfc8448_messages_round_trip()
    ensures
        write_client_hello(s3_hello()) == s3_client_hello(),
        write_server_hello(read_server_hello(body_of(s3_server_hello()))->0) == s3_server_hello(),
        write_encrypted_extensions(read_encrypted_extensions(body_of(s3_encrypted_extensions()))->0) == s3_encrypted_extensions(),
        write_certificate(read_certificate(body_of(s3_certificate()))->0) == s3_certificate(),
        write_certificate_verify(read_certificate_verify(body_of(s3_certificate_verify()))->0) == s3_certificate_verify(),
        write_finished(read_finished(body_of(s3_server_finished()))->0.verify_data) == s3_server_finished(),
        write_new_session_ticket(read_new_session_ticket(body_of(s3_new_session_ticket()))->0) == s3_new_session_ticket(),
        write_server_hello(read_server_hello(body_of(s5_request()))->0) == s5_request(),
        write_client_hello(read_client_hello(body_of(s5_client_hello2()))->0) == s5_client_hello2(),
        read_handshake(s3_client_hello()) is Some,
        read_handshake(s3_certificate()) is Some,
        read_handshake(s3_new_session_ticket()) is Some,
{
    assert(write_client_hello(s3_hello()) == s3_client_hello()) by (compute);
    assert(write_server_hello(read_server_hello(body_of(s3_server_hello()))->0) == s3_server_hello()) by (compute);
    assert(write_encrypted_extensions(read_encrypted_extensions(body_of(s3_encrypted_extensions()))->0) == s3_encrypted_extensions()) by (compute);
    assert(write_certificate(read_certificate(body_of(s3_certificate()))->0) == s3_certificate()) by (compute);
    assert(write_certificate_verify(read_certificate_verify(body_of(s3_certificate_verify()))->0) == s3_certificate_verify()) by (compute);
    assert(write_finished(read_finished(body_of(s3_server_finished()))->0.verify_data) == s3_server_finished()) by (compute);
    assert(write_new_session_ticket(read_new_session_ticket(body_of(s3_new_session_ticket()))->0) == s3_new_session_ticket()) by (compute);
    assert(write_server_hello(read_server_hello(body_of(s5_request()))->0) == s5_request()) by (compute);
    assert(write_client_hello(read_client_hello(body_of(s5_client_hello2()))->0) == s5_client_hello2()) by (compute);
    assert(read_handshake(s3_client_hello()) is Some) by (compute);
    assert(read_handshake(s3_certificate()) is Some) by (compute);
    assert(read_handshake(s3_new_session_ticket()) is Some) by (compute);
}

/// §5.1, §6: the trace's plaintext record header and its alert payload.
proof fn rfc8448_record_forms()
    ensures
        write_record_header(ct_application_data(), 0x0303, (s3_server_flight_record().len() - 5) as nat)
            == s3_server_flight_record().subrange(0, 5),
        // §5.2: its length is the payload, the inner type, and the expansion.
        s3_server_flight_payload().len() + 1 + 16 == s3_server_flight_record().len() - 5,
        write_alert(ad_close_notify()) == s3_alert_payload(),
        // §5.3: the first record uses the IV as its nonce.
        per_record_nonce(s3_server_handshake_iv(), 0) == s3_server_handshake_iv(),
        // §5.3: the sequence number goes into the low bytes.
        per_record_nonce(seq![0u8, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF], 0x0102)
            == seq![0u8, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFD],
{
    assert(write_record_header(ct_application_data(), 0x0303, (s3_server_flight_record().len() - 5) as nat)
        == s3_server_flight_record().subrange(0, 5)) by (compute);
    assert(s3_server_flight_payload().len() + 1 + 16 == s3_server_flight_record().len() - 5) by (compute);
    assert(write_alert(ad_close_notify()) == s3_alert_payload()) by (compute);
    assert(per_record_nonce(s3_server_handshake_iv(), 0) == s3_server_handshake_iv()) by (compute);
    assert(per_record_nonce(seq![0u8, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF], 0x0102)
        == seq![0u8, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE, 0xFD]) by (compute);
}

/// §4.4.1: `Transcript-Hash` over RFC 8448 §5's retried handshake, with Hash a table
/// that knows only Hash(ClientHello1) and Hash(synthetic || HRR || CH2 || SH), so the
/// synthetic message's exact bytes are what makes it come out.
proof fn rfc8448_s5_synthetic_transcript()
    ensures
        transcript_hash(s5_hash_table(), seq![s5_client_hello1(), s5_request(), s5_client_hello2(), s5_server_hello()], true)
            == s5_c_hs_hash(),
{
    assert(transcript_hash(s5_hash_table(), seq![s5_client_hello1(), s5_request(), s5_client_hello2(), s5_server_hello()], true)
        == s5_c_hs_hash()) by (compute);
}

/// A table of RFC 8448 §5's Hash; the other primitives are unused.
pub open spec fn s5_hash_table() -> Primitives {
    Primitives {
        hash: |m: Seq<u8>|
            if m == s5_client_hello1() {
                s5_hash_of_client_hello1()
            } else if m == seq![0xFEu8, 0, 0, 32] + s5_hash_of_client_hello1() + s5_request() + s5_client_hello2() + s5_server_hello() {
                s5_c_hs_hash()
            } else {
                seq![]
            },
        ..trace_primitives()
    }
}

/// §4.1.2, §4.1.4: RFC 8448 §5's second ClientHello is what the first plus the request
/// require, the request passes its checks, and so does the ServerHello after it.
proof fn rfc8448_s5_retry_conforms()
    ensures
        hello_retry_request_failures(read_client_hello(body_of(s5_client_hello1()))->0,
            read_server_hello(body_of(s5_request()))->0).len() == 0,
        second_client_hello_conforms(
            read_client_hello(body_of(s5_client_hello1()))->0,
            read_server_hello(body_of(s5_request()))->0.extensions,
            read_client_hello(body_of(s5_client_hello2()))->0),
        server_hello_failures(
            read_client_hello(body_of(s5_client_hello2()))->0,
            read_server_hello(body_of(s5_server_hello()))->0,
            Some(retry_record(read_server_hello(body_of(s5_request()))->0))).len() == 0,
        // §4.1.3: the special Random, as the trace shows it.
        is_hello_retry_request(read_server_hello(body_of(s5_request()))->0),
{
    assert(hello_retry_request_failures(read_client_hello(body_of(s5_client_hello1()))->0,
        read_server_hello(body_of(s5_request()))->0).len() == 0) by (compute);
    assert(second_client_hello_conforms(
        read_client_hello(body_of(s5_client_hello1()))->0,
        read_server_hello(body_of(s5_request()))->0.extensions,
        read_client_hello(body_of(s5_client_hello2()))->0)) by (compute);
    assert(server_hello_failures(
        read_client_hello(body_of(s5_client_hello2()))->0,
        read_server_hello(body_of(s5_server_hello()))->0,
        Some(retry_record(read_server_hello(body_of(s5_request()))->0))).len() == 0) by (compute);
    assert(is_hello_retry_request(read_server_hello(body_of(s5_request()))->0)) by (compute);
}

/// §4.4.3's own worked example of the content covered, byte for byte from the RFC.
proof fn certificate_verify_worked_example()
    ensures
        certificate_verify_content(server_certificate_verify_context(), repeat_byte(0x01, 32)) == seq![
            0x20u8, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
            0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
            0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
            0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
            0x54, 0x4c, 0x53, 0x20, 0x31, 0x2e, 0x33, 0x2c, 0x20, 0x73, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20,
            0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x56, 0x65, 0x72, 0x69, 0x66,
            0x79,
            0x00,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
        ],
{
    assert(certificate_verify_content(server_certificate_verify_context(), repeat_byte(0x01, 32)) == seq![
        0x20u8, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
        0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
        0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
        0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
        0x54, 0x4c, 0x53, 0x20, 0x31, 0x2e, 0x33, 0x2c, 0x20, 0x73, 0x65, 0x72, 0x76, 0x65, 0x72, 0x20,
        0x43, 0x65, 0x72, 0x74, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x65, 0x56, 0x65, 0x72, 0x69, 0x66,
        0x79,
        0x00,
        0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
        0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    ]) by (compute);
}

// ==========================================================================
// A toy set of primitives, for the record layer and the failure paths.
// ==========================================================================

/// A keyed checksum of the bytes, 32 of them.
pub open spec fn toy_digest(m: Seq<u8>) -> Seq<u8> {
    uint16(toy_sum(m, 0)) + uint16(m.len() % 65536) + repeat_byte(0x5A, 28)
}

/// A checksum.
pub open spec fn toy_sum(m: Seq<u8>, acc: nat) -> nat
    decreases m.len(),
{
    if m.len() == 0 {
        acc
    } else {
        toy_sum(m.subrange(1, m.len() as int), (acc * 31 + m[0] as nat) % 65521)
    }
}

/// A toy AEAD tag.
pub open spec fn toy_tag(key: Seq<u8>, nonce: Seq<u8>, additional: Seq<u8>, plaintext: Seq<u8>) -> Seq<u8> {
    toy_digest(key + nonce + additional + plaintext).subrange(0, 16)
}

/// The primitives of the toy runs.
pub open spec fn toy_primitives() -> Primitives {
    Primitives {
        hash: |m: Seq<u8>| toy_digest(m),
        hkdf_extract: |salt: Seq<u8>, ikm: Seq<u8>| toy_digest(salt + ikm),
        hkdf_expand: |prk: Seq<u8>, info: Seq<u8>, length: nat| toy_digest(prk + info).subrange(0, length as int),
        hmac: |key: Seq<u8>, message: Seq<u8>| toy_digest(key + message),
        aead_encrypt: |key: Seq<u8>, nonce: Seq<u8>, additional: Seq<u8>, plaintext: Seq<u8>|
            plaintext + toy_tag(key, nonce, additional, plaintext),
        aead_decrypt: |key: Seq<u8>, nonce: Seq<u8>, additional: Seq<u8>, ciphertext: Seq<u8>|
            if ciphertext.len() < 16 {
                None
            } else {
                let plaintext = ciphertext.subrange(0, ciphertext.len() - 16);
                if ciphertext.subrange(ciphertext.len() - 16, ciphertext.len() as int) == toy_tag(key, nonce, additional, plaintext) {
                    Some(plaintext)
                } else {
                    None
                }
            },
        x25519: |scalar: Seq<u8>, u: Seq<u8>| if all_zero(u) { zero_value() } else { toy_digest(scalar + u) },
        verify_signature: |scheme: nat, key: Seq<u8>, content: Seq<u8>, signature: Seq<u8>| signature == toy_digest(content),
        key_compatible: |scheme: nat, key: Seq<u8>| scheme != ed448(),
        validate_certificate_chain: |entries: Seq<CertificateEntry>|
            if entries[0].cert_data == seq![0xEEu8] { ChainResult::Accepted(seq![0xABu8]) } else { ChainResult::Rejected(ad_unknown_ca()) },
    }
}

/// A 32-byte value.
pub open spec fn toy_bytes(byte: u8) -> Seq<u8> {
    repeat_byte(byte, 32)
}

/// The profile's schemes for the toy runs, one of each kind the checks treat apart.
pub open spec fn toy_schemes() -> Seq<nat> {
    seq![ed25519(), ed448(), rsa_pss_rsae_sha256(), rsa_pkcs1_sha256(), rsa_pkcs1_sha1()]
}

/// An extension.
pub open spec fn ext(extension_type: nat, extension_data: Seq<u8>) -> Extension {
    Extension { extension_type, extension_data }
}

/// A toy ClientHello. `share` is the public value, or none for an empty list.
pub open spec fn toy_hello(share: bool) -> ClientHello {
    build_client_hello(toy_bytes(0x11), seq![0x77u8], toy_schemes(),
        if share { Some(toy_digest(toy_bytes(0x22) + x25519_basepoint())) } else { None },
        seq![ext(ext_server_name(), seq![]), ext(ext_status_request(), seq![])])
}

/// The toy ClientHello with a session id the conformance predicate accepts.
pub open spec fn toy_conforming_hello() -> ClientHello {
    ClientHello { legacy_session_id: toy_bytes(0x33), ..toy_hello(true) }
}

/// §4.1.2, §4.2.1, §4.2.7, §4.2.8, §9.2: the builder meets the predicate, and the
/// predicate is not vacuous.
proof fn client_hello_conformance()
    ensures
        client_hello_conforms(toy_conforming_hello(), toy_schemes()),
        // The session id must be empty or 32 bytes.
        !client_hello_conforms(toy_hello(true), toy_schemes()),
        // A second suite is outside the profile.
        !client_hello_conforms(ClientHello { cipher_suites: seq![0x1301nat, 0x1303nat], ..toy_conforming_hello() }, toy_schemes()),
        // Legacy schemes must be last (§4.2.3).
        !legacy_schemes_are_last(seq![rsa_pkcs1_sha1(), ed25519()]),
        legacy_schemes_are_last(toy_schemes()),
        // §4.2.8: shares are a subsequence of the groups, in order.
        is_subsequence(seq![0x17nat, 0x1Dnat], seq![0x18nat, 0x17nat, 0x19nat, 0x1Dnat]),
        !is_subsequence(seq![0x1Dnat, 0x17nat], seq![0x17nat, 0x1Dnat]),
{
    assert(client_hello_conforms(toy_conforming_hello(), toy_schemes())) by (compute);
    assert(!client_hello_conforms(toy_hello(true), toy_schemes())) by (compute);
    assert(!client_hello_conforms(ClientHello { cipher_suites: seq![0x1301nat, 0x1303nat], ..toy_conforming_hello() }, toy_schemes())) by (compute);
    assert(!legacy_schemes_are_last(seq![rsa_pkcs1_sha1(), ed25519()])) by (compute);
    assert(legacy_schemes_are_last(toy_schemes())) by (compute);
    assert(is_subsequence(seq![0x17nat, 0x1Dnat], seq![0x18nat, 0x17nat, 0x19nat, 0x1Dnat])) by (compute);
    assert(!is_subsequence(seq![0x1Dnat, 0x17nat], seq![0x17nat, 0x1Dnat])) by (compute);
}

/// §4.2's table, a row of each shape, and "recognizes".
proof fn extension_table_rows()
    ensures
        !recognized_but_not_specified(ext_key_share(), TableMessage::Sh),
        !recognized_but_not_specified(ext_key_share(), TableMessage::Hrr),
        recognized_but_not_specified(ext_key_share(), TableMessage::Ee),
        recognized_but_not_specified(ext_server_name(), TableMessage::Sh),
        !recognized_but_not_specified(ext_status_request(), TableMessage::Ct),
        recognized_but_not_specified(ext_supported_versions(), TableMessage::Ee),
        !recognized_but_not_specified(ext_early_data(), TableMessage::Nst),
        recognized_but_not_specified(ext_oid_filters(), TableMessage::Ch),
        !recognized_but_not_specified(ext_cookie(), TableMessage::Hrr),
        recognized_but_not_specified(ext_cookie(), TableMessage::Sh),
        // No row, so never "recognized": record_size_limit, renegotiation_info.
        !recognized_but_not_specified(28, TableMessage::Sh),
        !recognized_but_not_specified(0xff01, TableMessage::Sh),
{
    assert(!recognized_but_not_specified(ext_key_share(), TableMessage::Sh)) by (compute);
    assert(!recognized_but_not_specified(ext_key_share(), TableMessage::Hrr)) by (compute);
    assert(recognized_but_not_specified(ext_key_share(), TableMessage::Ee)) by (compute);
    assert(recognized_but_not_specified(ext_server_name(), TableMessage::Sh)) by (compute);
    assert(!recognized_but_not_specified(ext_status_request(), TableMessage::Ct)) by (compute);
    assert(recognized_but_not_specified(ext_supported_versions(), TableMessage::Ee)) by (compute);
    assert(!recognized_but_not_specified(ext_early_data(), TableMessage::Nst)) by (compute);
    assert(recognized_but_not_specified(ext_oid_filters(), TableMessage::Ch)) by (compute);
    assert(!recognized_but_not_specified(ext_cookie(), TableMessage::Hrr)) by (compute);
    assert(recognized_but_not_specified(ext_cookie(), TableMessage::Sh)) by (compute);
    assert(!recognized_but_not_specified(28, TableMessage::Sh)) by (compute);
    assert(!recognized_but_not_specified(0xff01, TableMessage::Sh)) by (compute);
}

/// §3.4: length fields follow the ceiling, and bounds and sizes are enforced.
proof fn presentation_vectors()
    ensures
        length_field_width(32) == 1,
        length_field_width(254) == 1,
        length_field_width(0xfffe) == 2,
        length_field_width(0xff_ffff) == 3,
        read_vector(seq![2u8, 7, 8, 9], 0, 32) == Some((seq![7u8, 8], seq![9u8])),
        read_vector(seq![3u8, 7, 8], 0, 32) is None,
        read_vector(seq![0u8], 1, 32) is None,
        read_vector(seq![33u8], 0, 32) is None,
        read_uint16_list(seq![1u8, 2, 3]) is None,
        read_uint16_list(seq![1u8, 2, 3, 4]) == Some(seq![0x0102nat, 0x0304nat]),
        // §5.4: scanning past the zeros.
        read_inner_plaintext(seq![9u8, 22, 0, 0]) == Some((seq![9u8], 22nat)),
        read_inner_plaintext(seq![0u8, 0]) is None,
{
    assert(length_field_width(32) == 1) by (compute);
    assert(length_field_width(254) == 1) by (compute);
    assert(length_field_width(0xfffe) == 2) by (compute);
    assert(length_field_width(0xff_ffff) == 3) by (compute);
    assert(read_vector(seq![2u8, 7, 8, 9], 0, 32) == Some((seq![7u8, 8], seq![9u8]))) by (compute);
    assert(read_vector(seq![3u8, 7, 8], 0, 32) is None) by (compute);
    assert(read_vector(seq![0u8], 1, 32) is None) by (compute);
    assert(read_vector(seq![33u8], 0, 32) is None) by (compute);
    assert(read_uint16_list(seq![1u8, 2, 3]) is None) by (compute);
    assert(read_uint16_list(seq![1u8, 2, 3, 4]) == Some(seq![0x0102nat, 0x0304nat])) by (compute);
    assert(read_inner_plaintext(seq![9u8, 22, 0, 0]) == Some((seq![9u8], 22nat))) by (compute);
    assert(read_inner_plaintext(seq![0u8, 0]) is None) by (compute);
}

/// §6, §6.1, §6.2: classes and levels.
proof fn alert_classes()
    ensures
        is_closure_alert(ad_close_notify()),
        is_closure_alert(ad_user_canceled()),
        !is_closure_alert(ad_unexpected_message()),
        // "Unknown Alert types MUST be treated as error alerts."
        !is_closure_alert(200),
        write_alert(ad_decode_error()) == seq![2u8, 50],
        write_alert(ad_user_canceled()) == seq![1u8, 90],
        // §4.4.2.2: "by default".
        required_alert(ClientError::ChainRejected(ad_unknown_ca())) == ad_unknown_ca(),
        required_alert(ClientError::ChainRejected(ad_decode_error())) == ad_unsupported_certificate(),
{
    assert(is_closure_alert(ad_close_notify())) by (compute);
    assert(is_closure_alert(ad_user_canceled())) by (compute);
    assert(!is_closure_alert(ad_unexpected_message())) by (compute);
    assert(!is_closure_alert(200)) by (compute);
    assert(write_alert(ad_decode_error()) == seq![2u8, 50]) by (compute);
    assert(write_alert(ad_user_canceled()) == seq![1u8, 90]) by (compute);
    assert(required_alert(ClientError::ChainRejected(ad_unknown_ca())) == ad_unknown_ca()) by (compute);
    assert(required_alert(ClientError::ChainRejected(ad_decode_error())) == ad_unsupported_certificate()) by (compute);
}

// --------------------------------------------------------------------------
// The toy server's messages.
// --------------------------------------------------------------------------

/// The toy server's X25519 share.
pub open spec fn toy_server_share() -> Seq<u8> {
    toy_bytes(0x44)
}

/// A toy ServerHello that passes every check against `toy_hello`.
pub open spec fn toy_server_hello() -> ServerHello {
    ServerHello {
        legacy_version: 0x0303,
        random: toy_bytes(0x55),
        legacy_session_id_echo: seq![0x77u8],
        cipher_suite: 0x1303,
        legacy_compression_method: 0,
        extensions: seq![
            ext(ext_supported_versions(), uint16(0x0304)),
            ext(ext_key_share(), uint16(group_x25519()) + write_vector(toy_server_share(), 0xffff)),
        ],
    }
}

/// The handshake just after sending `toy_hello(true)`.
pub open spec fn hs_wait_sh() -> ClientHandshake {
    start_handshake(toy_hello(true), toy_bytes(0x22), toy_bytes(0x23))
}

/// The result of `step` as its error, if it aborted.
pub open spec fn aborted_with(step: HandshakeStep, error: ClientError) -> bool {
    match step {
        HandshakeStep::Abort(e) => e == error,
        _ => false,
    }
}

/// The handshake after a step.
pub open spec fn after(step: HandshakeStep) -> ClientHandshake {
    step->handshake
}

/// The result of a toy ServerHello in WAIT_SH.
pub open spec fn sh_step(hello: ServerHello) -> HandshakeStep {
    receive_handshake_message(toy_primitives(), hs_wait_sh(), write_server_hello(hello))
}

/// §4.1.3, §4.2.1, §4.2, §4.2.8, §7.4.2, D.1: which alert each ServerHello failure gets.
proof fn server_hello_checks()
    ensures
        after(sh_step(toy_server_hello())).state == ClientState::WaitEe,
        // §4.1.3: legacy_session_id_echo.
        aborted_with(sh_step(ServerHello { legacy_session_id_echo: seq![], ..toy_server_hello() }), ClientError::SessionIdEchoMismatch),
        // §4.1.3: cipher_suite.
        aborted_with(sh_step(ServerHello { cipher_suite: 0x1301, ..toy_server_hello() }), ClientError::CipherSuiteNotOffered),
        // §4.1.3: legacy_compression_method.
        aborted_with(sh_step(ServerHello { legacy_compression_method: 1, ..toy_server_hello() }), ClientError::CompressionMethodNotZero),
        // §4.2.1: with the extension, legacy_version is ignored...
        after(sh_step(ServerHello { legacy_version: 0x0301, ..toy_server_hello() })).state == ClientState::WaitEe,
        // ...but D.5: 0x0300 aborts anyway.
        aborted_with(sh_step(ServerHello { legacy_version: 0x0300, ..toy_server_hello() }), ClientError::VersionNotSupported),
        // §4.2.1: a version not offered, or before TLS 1.3.
        aborted_with(sh_step(ServerHello { extensions: seq![ext(ext_supported_versions(), uint16(0x0303)), toy_server_hello().extensions[1]], ..toy_server_hello() }),
            ClientError::SelectedVersionNotAcceptable),
        aborted_with(sh_step(ServerHello { extensions: seq![ext(ext_supported_versions(), seq![3u8]), toy_server_hello().extensions[1]], ..toy_server_hello() }),
            ClientError::Malformed),
        // §4.1.3, D.1: no supported_versions.
        aborted_with(sh_step(ServerHello { extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::VersionNotSupported),
        aborted_with(sh_step(ServerHello { legacy_version: 0x0304, extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::SupportedVersionsMissing),
        // §4.1.3: both sentinels; a TLS 1.2 hello of no extensions at all is still read.
        aborted_with(sh_step(ServerHello { random: toy_bytes(0x55).subrange(0, 24) + downgrade_tls12(), extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::DowngradeSentinel),
        aborted_with(sh_step(ServerHello { random: toy_bytes(0x55).subrange(0, 24) + downgrade_tls11(), extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::DowngradeSentinel),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(),
            write_handshake(ht_server_hello(), uint16(0x0303) + toy_bytes(0x55).subrange(0, 24) + downgrade_tls12()
                + seq![1u8, 0x77] + uint16(0xC02F) + seq![0u8])), ClientError::DowngradeSentinel),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(),
            write_handshake(ht_server_hello(), uint16(0x0303) + toy_bytes(0x55) + seq![1u8, 0x77] + uint16(0xC02F) + seq![0u8])), ClientError::VersionNotSupported),
        // §4.2: not for this message, then not offered.
        aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::ExtensionNotSpecifiedForMessage),
        aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![ext(0x1234, seq![])], ..toy_server_hello() }), ClientError::ExtensionNotOffered),
        // No PSK was offered, so its response is one with no request.
        aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![ext(ext_pre_shared_key(), uint16(0))], ..toy_server_hello() }), ClientError::ExtensionNotOffered),
        // §4.2: duplicates.
        aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![toy_server_hello().extensions[1]], ..toy_server_hello() }), ClientError::DuplicateExtension),
        // §4.2.8, §9.2.
        aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0]], ..toy_server_hello() }), ClientError::KeyShareMissing),
        aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(0x0017) + write_vector(toy_server_share(), 0xffff))], ..toy_server_hello() }), ClientError::ServerShareGroupNotOffered),
        aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(group_x25519()) + write_vector(seq![1u8], 0xffff))], ..toy_server_hello() }), ClientError::ServerShareWrongLength),
        aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(group_x25519()))], ..toy_server_hello() }), ClientError::Malformed),
        // §7.4.2.
        aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(group_x25519()) + write_vector(repeat_byte(0, 32), 0xffff))], ..toy_server_hello() }), ClientError::SharedSecretAllZero),
{
    assert(after(sh_step(toy_server_hello())).state == ClientState::WaitEe) by (compute);
    assert(aborted_with(sh_step(ServerHello { legacy_session_id_echo: seq![], ..toy_server_hello() }), ClientError::SessionIdEchoMismatch)) by (compute);
    assert(aborted_with(sh_step(ServerHello { cipher_suite: 0x1301, ..toy_server_hello() }), ClientError::CipherSuiteNotOffered)) by (compute);
    assert(aborted_with(sh_step(ServerHello { legacy_compression_method: 1, ..toy_server_hello() }), ClientError::CompressionMethodNotZero)) by (compute);
    assert(after(sh_step(ServerHello { legacy_version: 0x0301, ..toy_server_hello() })).state == ClientState::WaitEe) by (compute);
    assert(aborted_with(sh_step(ServerHello { legacy_version: 0x0300, ..toy_server_hello() }), ClientError::VersionNotSupported)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![ext(ext_supported_versions(), uint16(0x0303)), toy_server_hello().extensions[1]], ..toy_server_hello() }),
        ClientError::SelectedVersionNotAcceptable)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![ext(ext_supported_versions(), seq![3u8]), toy_server_hello().extensions[1]], ..toy_server_hello() }),
        ClientError::Malformed)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::VersionNotSupported)) by (compute);
    assert(aborted_with(sh_step(ServerHello { legacy_version: 0x0304, extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::SupportedVersionsMissing)) by (compute);
    assert(aborted_with(sh_step(ServerHello { random: toy_bytes(0x55).subrange(0, 24) + downgrade_tls12(), extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::DowngradeSentinel)) by (compute);
    assert(aborted_with(sh_step(ServerHello { random: toy_bytes(0x55).subrange(0, 24) + downgrade_tls11(), extensions: seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::DowngradeSentinel)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(),
        write_handshake(ht_server_hello(), uint16(0x0303) + toy_bytes(0x55).subrange(0, 24) + downgrade_tls12()
            + seq![1u8, 0x77] + uint16(0xC02F) + seq![0u8])), ClientError::DowngradeSentinel)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(),
        write_handshake(ht_server_hello(), uint16(0x0303) + toy_bytes(0x55) + seq![1u8, 0x77] + uint16(0xC02F) + seq![0u8])), ClientError::VersionNotSupported)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![ext(ext_server_name(), seq![])], ..toy_server_hello() }), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![ext(0x1234, seq![])], ..toy_server_hello() }), ClientError::ExtensionNotOffered)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![ext(ext_pre_shared_key(), uint16(0))], ..toy_server_hello() }), ClientError::ExtensionNotOffered)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: toy_server_hello().extensions + seq![toy_server_hello().extensions[1]], ..toy_server_hello() }), ClientError::DuplicateExtension)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0]], ..toy_server_hello() }), ClientError::KeyShareMissing)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(0x0017) + write_vector(toy_server_share(), 0xffff))], ..toy_server_hello() }), ClientError::ServerShareGroupNotOffered)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(group_x25519()) + write_vector(seq![1u8], 0xffff))], ..toy_server_hello() }), ClientError::ServerShareWrongLength)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(group_x25519()))], ..toy_server_hello() }), ClientError::Malformed)) by (compute);
    assert(aborted_with(sh_step(ServerHello { extensions: seq![toy_server_hello().extensions[0], ext(ext_key_share(), uint16(group_x25519()) + write_vector(repeat_byte(0, 32), 0xffff))], ..toy_server_hello() }), ClientError::SharedSecretAllZero)) by (compute);
}

/// A HelloRetryRequest of the given extensions, otherwise right for `toy_hello`.
pub open spec fn toy_retry(extensions: Seq<Extension>) -> ServerHello {
    ServerHello { random: hello_retry_request_random(), extensions, ..toy_server_hello() }
}

/// supported_versions as a HelloRetryRequest has it.
pub open spec fn retry_versions() -> Extension {
    ext(ext_supported_versions(), uint16(0x0304))
}

/// A cookie extension holding two bytes.
pub open spec fn retry_cookie() -> Extension {
    ext(ext_cookie(), write_vector(seq![0xC0u8, 0x01], 0xffff))
}

/// key_share of a HelloRetryRequest selecting X25519.
pub open spec fn retry_key_share() -> Extension {
    ext(ext_key_share(), uint16(group_x25519()))
}

/// The handshake after sending `toy_hello(false)`, whose shares are empty.
pub open spec fn hs_no_share() -> ClientHandshake {
    start_handshake(toy_hello(false), toy_bytes(0x22), toy_bytes(0x23))
}

/// A HelloRetryRequest's result in WAIT_SH, from a client with no shares.
pub open spec fn retry_step(hello: ServerHello) -> HandshakeStep {
    receive_handshake_message(toy_primitives(), hs_no_share(), write_server_hello(hello))
}

/// The handshake after a good HelloRetryRequest with a cookie and a group selected.
pub open spec fn hs_retried() -> ClientHandshake {
    after(retry_step(toy_retry(seq![retry_versions(), retry_cookie(), retry_key_share()])))
}

/// §4.1.2, §4.1.4, §4.2.2, §4.2.8, §4.4.1.
proof fn hello_retry_request_checks()
    ensures
        // §4.1.2: still waiting; the second hello conforms and holds a share and the cookie.
        hs_retried().state == ClientState::WaitSh,
        second_client_hello_conforms(hs_retried().first_hello,
            seq![retry_versions(), retry_cookie(), retry_key_share()], hs_retried().hello),
        share_groups(offered_shares(hs_retried().hello)) == seq![group_x25519()],
        // The new share comes from the retry key.
        offered_shares(hs_retried().hello)[0].key_exchange == toy_digest(toy_bytes(0x23) + x25519_basepoint()),
        hs_retried().x25519_private_key == toy_bytes(0x23),
        hs_retried().transcript.len() == 3,
        // The conformance predicate is not vacuous: a changed random fails it.
        !second_client_hello_conforms(hs_retried().first_hello,
            seq![retry_versions(), retry_cookie(), retry_key_share()],
            ClientHello { random: toy_bytes(0x12), ..hs_retried().hello }),
        // §4.1.4: a second one.
        aborted_with(receive_handshake_message(toy_primitives(), hs_retried(), write_server_hello(toy_retry(seq![retry_versions(), retry_cookie()]))),
            ClientError::SecondHelloRetryRequest),
        // §4.1.4: no change.
        aborted_with(retry_step(toy_retry(seq![retry_versions()])), ClientError::RetryWithoutChange),
        // §4.1.4: legacy_version is checked here.
        aborted_with(retry_step(ServerHello { legacy_version: 0x0301, ..toy_retry(seq![retry_versions(), retry_cookie()]) }), ClientError::RetryLegacyVersion),
        // §4.1.4: extensions.
        aborted_with(retry_step(toy_retry(seq![retry_cookie()])), ClientError::SupportedVersionsMissing),
        aborted_with(retry_step(toy_retry(seq![retry_versions(), ext(ext_server_name(), seq![])])), ClientError::ExtensionNotSpecifiedForMessage),
        // §4.2.2: the cookie's floor.
        aborted_with(retry_step(toy_retry(seq![retry_versions(), ext(ext_cookie(), uint16(0))])), ClientError::Malformed),
        // §4.2.8 (1) and (2).
        aborted_with(retry_step(toy_retry(seq![retry_versions(), ext(ext_key_share(), uint16(0x0017))])), ClientError::RetryGroupNotOffered),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(), write_server_hello(toy_retry(seq![retry_versions(), retry_key_share()]))),
            ClientError::RetryGroupAlreadyShared),
        // §4.1.4, §4.2.8: the ServerHello after it.
        after(receive_handshake_message(toy_primitives(), hs_retried(), write_server_hello(toy_server_hello()))).state == ClientState::WaitEe,
        aborted_with(receive_handshake_message(toy_primitives(),
            ClientHandshake { retry: Some(RetryRecord { cipher_suite: 0x1301, ..hs_retried().retry->0 }), ..hs_retried() },
            write_server_hello(toy_server_hello())), ClientError::CipherSuiteChanged),
        aborted_with(receive_handshake_message(toy_primitives(),
            ClientHandshake { retry: Some(RetryRecord { selected_version: 0x0305, ..hs_retried().retry->0 }), ..hs_retried() },
            write_server_hello(toy_server_hello())), ClientError::SelectedVersionChanged),
        aborted_with(receive_handshake_message(toy_primitives(),
            ClientHandshake { retry: Some(RetryRecord { selected_group: Some(0x0017), ..hs_retried().retry->0 }), ..hs_retried() },
            write_server_hello(toy_server_hello())), ClientError::ServerShareGroupChanged),
{
    assert(hs_retried().state == ClientState::WaitSh) by (compute);
    assert(second_client_hello_conforms(hs_retried().first_hello,
        seq![retry_versions(), retry_cookie(), retry_key_share()], hs_retried().hello)) by (compute);
    assert(share_groups(offered_shares(hs_retried().hello)) == seq![group_x25519()]) by (compute);
    assert(offered_shares(hs_retried().hello)[0].key_exchange == toy_digest(toy_bytes(0x23) + x25519_basepoint())) by (compute);
    assert(hs_retried().x25519_private_key == toy_bytes(0x23)) by (compute);
    assert(hs_retried().transcript.len() == 3) by (compute);
    assert(!second_client_hello_conforms(hs_retried().first_hello,
        seq![retry_versions(), retry_cookie(), retry_key_share()],
        ClientHello { random: toy_bytes(0x12), ..hs_retried().hello })) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_retried(), write_server_hello(toy_retry(seq![retry_versions(), retry_cookie()]))),
        ClientError::SecondHelloRetryRequest)) by (compute);
    assert(aborted_with(retry_step(toy_retry(seq![retry_versions()])), ClientError::RetryWithoutChange)) by (compute);
    assert(aborted_with(retry_step(ServerHello { legacy_version: 0x0301, ..toy_retry(seq![retry_versions(), retry_cookie()]) }), ClientError::RetryLegacyVersion)) by (compute);
    assert(aborted_with(retry_step(toy_retry(seq![retry_cookie()])), ClientError::SupportedVersionsMissing)) by (compute);
    assert(aborted_with(retry_step(toy_retry(seq![retry_versions(), ext(ext_server_name(), seq![])])), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
    assert(aborted_with(retry_step(toy_retry(seq![retry_versions(), ext(ext_cookie(), uint16(0))])), ClientError::Malformed)) by (compute);
    assert(aborted_with(retry_step(toy_retry(seq![retry_versions(), ext(ext_key_share(), uint16(0x0017))])), ClientError::RetryGroupNotOffered)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(), write_server_hello(toy_retry(seq![retry_versions(), retry_key_share()]))),
        ClientError::RetryGroupAlreadyShared)) by (compute);
    assert(after(receive_handshake_message(toy_primitives(), hs_retried(), write_server_hello(toy_server_hello()))).state == ClientState::WaitEe) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(),
        ClientHandshake { retry: Some(RetryRecord { cipher_suite: 0x1301, ..hs_retried().retry->0 }), ..hs_retried() },
        write_server_hello(toy_server_hello())), ClientError::CipherSuiteChanged)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(),
        ClientHandshake { retry: Some(RetryRecord { selected_version: 0x0305, ..hs_retried().retry->0 }), ..hs_retried() },
        write_server_hello(toy_server_hello())), ClientError::SelectedVersionChanged)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(),
        ClientHandshake { retry: Some(RetryRecord { selected_group: Some(0x0017), ..hs_retried().retry->0 }), ..hs_retried() },
        write_server_hello(toy_server_hello())), ClientError::ServerShareGroupChanged)) by (compute);
}

/// WAIT_EE: the handshake after the toy ServerHello.
pub open spec fn hs_wait_ee() -> ClientHandshake {
    after(sh_step(toy_server_hello()))
}

/// A good toy EncryptedExtensions: server_name, which the client offered.
pub open spec fn toy_ee() -> Seq<u8> {
    write_encrypted_extensions(EncryptedExtensions { extensions: seq![ext(ext_server_name(), seq![])] })
}

/// WAIT_CERT_CR.
pub open spec fn hs_wait_cert_cr() -> ClientHandshake {
    after(receive_handshake_message(toy_primitives(), hs_wait_ee(), toy_ee()))
}

/// A toy Certificate with one entry.
pub open spec fn toy_certificate(cert_data: Seq<u8>, extensions: Seq<Extension>) -> Seq<u8> {
    write_certificate(Certificate {
        certificate_request_context: seq![],
        certificate_list: seq![CertificateEntry { cert_data, extensions }],
    })
}

/// WAIT_CV.
pub open spec fn hs_wait_cv() -> ClientHandshake {
    after(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![])))
}

/// A CertificateVerify of `scheme`, correctly signed at `hs`.
pub open spec fn toy_cv(hs: ClientHandshake, scheme: nat) -> Seq<u8> {
    write_certificate_verify(CertificateVerify {
        algorithm: scheme,
        signature: toy_digest(certificate_verify_content(server_certificate_verify_context(),
            transcript_hash(toy_primitives(), hs.transcript, hs.retry is Some))),
    })
}

/// WAIT_FINISHED.
pub open spec fn hs_wait_finished() -> ClientHandshake {
    after(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), ed25519())))
}

/// The right server Finished at `hs`.
pub open spec fn toy_finished(hs: ClientHandshake) -> Seq<u8> {
    write_finished(verify_data(toy_primitives(), hs.server_handshake_traffic_secret, hs.transcript, hs.retry is Some))
}

/// §4.3, §4.4: which alert each failure gets, and the order of A.1.
proof fn server_parameters_and_authentication_checks()
    ensures
        hs_wait_cert_cr().state == ClientState::WaitCertCr,
        hs_wait_cv().state == ClientState::WaitCv,
        hs_wait_finished().state == ClientState::WaitFinished,
        // §4.3.1: forbidden, not offered.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_ee(),
            write_encrypted_extensions(EncryptedExtensions { extensions: seq![ext(ext_key_share(), seq![])] })), ClientError::ExtensionNotSpecifiedForMessage),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_ee(),
            write_encrypted_extensions(EncryptedExtensions { extensions: seq![ext(ext_application_layer_protocol_negotiation(), seq![])] })), ClientError::ExtensionNotOffered),
        // A.1: out of order.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_ee(), toy_certificate(seq![0xEEu8], seq![])), ClientError::UnexpectedHandshakeMessage),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_finished(hs_wait_cert_cr())), ClientError::UnexpectedHandshakeMessage),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(), write_key_update(0)), ClientError::KeyUpdateBeforeFinished),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_finished(), write_handshake(ht_end_of_early_data(), seq![])), ClientError::EndOfEarlyDataReceived),
        // §4.4.2, §4.4.2.4.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(),
            write_certificate(Certificate { certificate_request_context: seq![], certificate_list: seq![] })), ClientError::EmptyServerCertificate),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(),
            write_certificate(Certificate { certificate_request_context: seq![1u8], certificate_list: seq![CertificateEntry { cert_data: seq![0xEEu8], extensions: seq![] }] })), ClientError::CertificateContextNotEmpty),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![ext(ext_key_share(), seq![])])), ClientError::ExtensionNotSpecifiedForMessage),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![ext(ext_signed_certificate_timestamp(), seq![])])), ClientError::ExtensionNotOffered),
        after(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![ext(ext_status_request(), seq![])]))).state == ClientState::WaitCv,
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xDDu8], seq![])), ClientError::ChainRejected(ad_unknown_ca())),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), write_handshake(ht_certificate(), seq![0u8, 0, 0, 1])), ClientError::Malformed),
        // §4.4.3.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), ecdsa_secp256r1_sha256())), ClientError::SignatureSchemeNotOffered),
        // Offered for certificates, but not usable here, whatever it is offered for.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), rsa_pkcs1_sha256())), ClientError::SignatureSchemeForbidden),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), rsa_pkcs1_sha1())), ClientError::SignatureSchemeForbidden),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), ed448())), ClientError::SignatureSchemeKeyMismatch),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(),
            write_certificate_verify(CertificateVerify { algorithm: ed25519(), signature: seq![1u8] })), ClientError::CertificateVerifyFailed),
        // §4.4.4.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_finished(), write_finished(toy_bytes(0))), ClientError::FinishedIncorrect),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_finished(), write_finished(seq![1u8])), ClientError::Malformed),
        after(receive_handshake_message(toy_primitives(), hs_wait_finished(), toy_finished(hs_wait_finished()))).state == ClientState::Connected,
{
    assert(hs_wait_cert_cr().state == ClientState::WaitCertCr) by (compute);
    assert(hs_wait_cv().state == ClientState::WaitCv) by (compute);
    assert(hs_wait_finished().state == ClientState::WaitFinished) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_ee(),
        write_encrypted_extensions(EncryptedExtensions { extensions: seq![ext(ext_key_share(), seq![])] })), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_ee(),
        write_encrypted_extensions(EncryptedExtensions { extensions: seq![ext(ext_application_layer_protocol_negotiation(), seq![])] })), ClientError::ExtensionNotOffered)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_ee(), toy_certificate(seq![0xEEu8], seq![])), ClientError::UnexpectedHandshakeMessage)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_finished(hs_wait_cert_cr())), ClientError::UnexpectedHandshakeMessage)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_sh(), write_key_update(0)), ClientError::KeyUpdateBeforeFinished)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_finished(), write_handshake(ht_end_of_early_data(), seq![])), ClientError::EndOfEarlyDataReceived)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(),
        write_certificate(Certificate { certificate_request_context: seq![], certificate_list: seq![] })), ClientError::EmptyServerCertificate)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(),
        write_certificate(Certificate { certificate_request_context: seq![1u8], certificate_list: seq![CertificateEntry { cert_data: seq![0xEEu8], extensions: seq![] }] })), ClientError::CertificateContextNotEmpty)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![ext(ext_key_share(), seq![])])), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![ext(ext_signed_certificate_timestamp(), seq![])])), ClientError::ExtensionNotOffered)) by (compute);
    assert(after(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xEEu8], seq![ext(ext_status_request(), seq![])]))).state == ClientState::WaitCv) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_certificate(seq![0xDDu8], seq![])), ClientError::ChainRejected(ad_unknown_ca()))) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), write_handshake(ht_certificate(), seq![0u8, 0, 0, 1])), ClientError::Malformed)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), ecdsa_secp256r1_sha256())), ClientError::SignatureSchemeNotOffered)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), rsa_pkcs1_sha256())), ClientError::SignatureSchemeForbidden)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), rsa_pkcs1_sha1())), ClientError::SignatureSchemeForbidden)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(), toy_cv(hs_wait_cv(), ed448())), ClientError::SignatureSchemeKeyMismatch)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cv(),
        write_certificate_verify(CertificateVerify { algorithm: ed25519(), signature: seq![1u8] })), ClientError::CertificateVerifyFailed)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_finished(), write_finished(toy_bytes(0))), ClientError::FinishedIncorrect)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_finished(), write_finished(seq![1u8])), ClientError::Malformed)) by (compute);
    assert(after(receive_handshake_message(toy_primitives(), hs_wait_finished(), toy_finished(hs_wait_finished()))).state == ClientState::Connected) by (compute);
}

/// A good toy CertificateRequest with the given context.
pub open spec fn toy_cr(context: Seq<u8>) -> Seq<u8> {
    write_certificate_request(CertificateRequest {
        certificate_request_context: context,
        extensions: seq![ext(ext_signature_algorithms(), write_signature_scheme_list(seq![ed25519()])), ext(0x1234, seq![])],
    })
}

/// §4.3.2 and §4.4.2: a requested certificate is answered by an empty one, whose bytes
/// are the empty context and empty list, and which enters the client Finished's and
/// the resumption secret's transcript.
pub open spec fn cr_run() -> HandshakeStep {
    let p = toy_primitives();
    let wait_cert = after(receive_handshake_message(p, hs_wait_cert_cr(), toy_cr(seq![])));
    let wait_cv = after(receive_handshake_message(p, wait_cert, toy_certificate(seq![0xEEu8], seq![])));
    let wait_finished = after(receive_handshake_message(p, wait_cv, toy_cv(wait_cv, ed25519())));
    receive_handshake_message(p, wait_finished, toy_finished(wait_finished))
}

/// §4.3.2, §4.4.2, §4.6.2.
proof fn certificate_request_checks()
    ensures
        after(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_cr(seq![]))).state == ClientState::WaitCert,
        after(cr_run()).state == ClientState::Connected,
        // The transcript gains: Certificate, then Finished. `0b 00 00 04 00 00 00 00`.
        after(cr_run()).transcript[after(cr_run()).transcript.len() - 2] == seq![0x0bu8, 0, 0, 4, 0, 0, 0, 0],
        // A.1's order, with the Certificate before the Finished.
        (cr_run()->actions).len() == 5,
        (cr_run()->actions)[1] == Action::SendHandshake(seq![0x0bu8, 0, 0, 4, 0, 0, 0, 0], 0x0303),
        // §4.3.2.
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_cr(seq![1u8])), ClientError::RequestContextNotEmpty),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), write_certificate_request(CertificateRequest {
            certificate_request_context: seq![], extensions: seq![ext(0x1234, seq![])] })), ClientError::SignatureAlgorithmsMissing),
        aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), write_certificate_request(CertificateRequest {
            certificate_request_context: seq![], extensions: seq![ext(ext_key_share(), seq![])] })), ClientError::ExtensionNotSpecifiedForMessage),
        // §4.6.2.
        aborted_with(receive_handshake_message(toy_primitives(), after(cr_run()), toy_cr(seq![1u8])), ClientError::PostHandshakeAuthNotOffered),
{
    assert(after(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_cr(seq![]))).state == ClientState::WaitCert) by (compute);
    assert(after(cr_run()).state == ClientState::Connected) by (compute);
    assert(after(cr_run()).transcript[after(cr_run()).transcript.len() - 2] == seq![0x0bu8, 0, 0, 4, 0, 0, 0, 0]) by (compute);
    assert((cr_run()->actions).len() == 5) by (compute);
    assert((cr_run()->actions)[1] == Action::SendHandshake(seq![0x0bu8, 0, 0, 4, 0, 0, 0, 0], 0x0303)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), toy_cr(seq![1u8])), ClientError::RequestContextNotEmpty)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), write_certificate_request(CertificateRequest {
        certificate_request_context: seq![], extensions: seq![ext(0x1234, seq![])] })), ClientError::SignatureAlgorithmsMissing)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_wait_cert_cr(), write_certificate_request(CertificateRequest {
        certificate_request_context: seq![], extensions: seq![ext(ext_key_share(), seq![])] })), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), after(cr_run()), toy_cr(seq![1u8])), ClientError::PostHandshakeAuthNotOffered)) by (compute);
}

/// A toy NewSessionTicket with a lifetime and extensions.
pub open spec fn toy_ticket(ticket_lifetime: nat, extensions: Seq<Extension>) -> Seq<u8> {
    write_new_session_ticket(NewSessionTicket {
        ticket_lifetime, ticket_age_add: 7, ticket_nonce: seq![0u8], ticket: seq![1u8], extensions,
    })
}

/// CONNECTED, after the plain toy handshake.
pub open spec fn hs_connected() -> ClientHandshake {
    after(receive_handshake_message(toy_primitives(), hs_wait_finished(), toy_finished(hs_wait_finished())))
}

/// §4.6.1, §4.6.3: post-handshake messages.
proof fn post_handshake_checks()
{
    // Unrecognized is ignored; recognized but not for NST is not.
    assert(after(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(604800, seq![]))) == hs_connected()) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(604801, seq![])), ClientError::TicketLifetimeTooLong)) by (compute);
    assert(after(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(1, seq![ext(0x1234, seq![])]))) == hs_connected()) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), toy_ticket(1, seq![ext(ext_key_share(), seq![])])), ClientError::ExtensionNotSpecifiedForMessage)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), write_key_update(2)), ClientError::KeyUpdateBadRequest)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), write_handshake(ht_key_update(), seq![])), ClientError::Malformed)) by (compute);
    assert(aborted_with(receive_handshake_message(toy_primitives(), hs_connected(), write_server_hello(toy_server_hello())), ClientError::UnexpectedHandshakeMessage)) by (compute);
    assert((receive_handshake_message(toy_primitives(), hs_connected(), write_key_update(1))->actions)
        == seq![Action::UpdateReceiveSecret, Action::RespondToKeyUpdate]) by (compute);
    assert((receive_handshake_message(toy_primitives(), hs_connected(), write_key_update(0))->actions)
        == seq![Action::UpdateReceiveSecret]) by (compute);
}

// --------------------------------------------------------------------------
// The record layer, driven with records.
// --------------------------------------------------------------------------

/// The connection after the toy ClientHello.
pub open spec fn conn_wait_sh() -> Connection {
    start_connection(toy_primitives(), toy_hello(true), toy_bytes(0x22), toy_bytes(0x23)).0
}

/// What `stream` does to `connection`.
pub open spec fn stream_result(connection: Connection, stream: Seq<u8>) -> Receive {
    receive_stream(toy_primitives(), connection, stream).0
}

/// The connection after `result`.
pub open spec fn conn_after(result: Receive) -> Connection {
    (result->Continue_0).connection
}

/// Whether `result` aborted with this error.
pub open spec fn receive_aborted(result: Receive, error: ClientError) -> bool {
    match result {
        Receive::Abort(e) => e == error,
        _ => false,
    }
}

/// A plaintext record.
pub open spec fn plain(content_type: nat, fragment: Seq<u8>) -> Seq<u8> {
    write_tls_plaintext(content_type, 0x0303, fragment)
}

/// The toy ServerHello as a record.
pub open spec fn toy_sh_record() -> Seq<u8> {
    plain(ct_handshake(), write_server_hello(toy_server_hello()))
}

/// The connection after the toy ServerHello.
pub open spec fn conn_wait_ee() -> Connection {
    conn_after(stream_result(conn_wait_sh(), toy_sh_record()))
}

/// A record the server protects, under the server's handshake keys at a sequence number.
pub open spec fn server_hs_record(seq_no: nat, content_type: nat, content: Seq<u8>) -> Seq<u8> {
    protect_record(toy_primitives(),
        TrafficState { sequence_number: seq_no, ..traffic_state(toy_primitives(), conn_wait_ee().handshake.server_handshake_traffic_secret) },
        content_type, content)
}

/// The rest of the server's flight, coalesced in one record.
pub open spec fn toy_flight() -> Seq<u8> {
    toy_ee() + toy_certificate(seq![0xEEu8], seq![]) + toy_cv(hs_wait_cv(), ed25519()) + toy_finished(hs_wait_finished())
}

/// The whole first flight as one stream, with a compatibility change_cipher_spec.
pub open spec fn toy_first_flight_stream() -> Seq<u8> {
    toy_sh_record() + plain(ct_change_cipher_spec(), seq![1u8]) + server_hs_record(0, ct_handshake(), toy_flight())
}

/// The result of the first flight.
pub open spec fn first_flight() -> Receive {
    stream_result(conn_wait_sh(), toy_first_flight_stream())
}

/// CONNECTED, at the record layer.
pub open spec fn conn_connected() -> Connection {
    conn_after(first_flight())
}

/// A record the server protects, under its first application key at a sequence number.
pub open spec fn server_ap_record(seq_no: nat, content_type: nat, content: Seq<u8>) -> Seq<u8> {
    protect_record(toy_primitives(),
        TrafficState { sequence_number: seq_no, ..conn_connected().receive->Protected_0 },
        content_type, content)
}

/// §4.1, §5, A.1: a whole handshake by records.
proof fn handshake_over_records()
    ensures
        // §5.1: the initial ClientHello's record has version 0x0301.
        (start_connection(toy_primitives(), toy_hello(true), toy_bytes(0x22), toy_bytes(0x23)).1)
            == seq![write_tls_plaintext(ct_handshake(), 0x0301, write_client_hello(toy_hello(true)))],
        // A.1: K_recv = handshake after ServerHello; K_send unchanged.
        conn_wait_ee().handshake.state == ClientState::WaitEe,
        conn_wait_ee().receive is Protected,
        conn_wait_ee().send is Unprotected,
        conn_connected().handshake.state == ClientState::Connected,
        // The client's second flight: its Finished, under its handshake key at number 0.
        (first_flight()->Continue_0).records_to_send == seq![
            protect_record(toy_primitives(), traffic_state(toy_primitives(), conn_connected().handshake.client_handshake_traffic_secret),
                ct_handshake(), conn_connected().handshake.transcript.last())],
        // A.1: K_send = K_recv = application, each at sequence number 0.
        (conn_connected().receive->Protected_0).sequence_number == 0,
        (conn_connected().send->Protected_0).sequence_number == 0,
        // §5.1: split over records works the same.
        conn_after(stream_result(conn_wait_sh(), toy_sh_record() + server_hs_record(0, ct_handshake(), toy_flight().subrange(0, 10))
            + server_hs_record(1, ct_handshake(), toy_flight().subrange(10, toy_flight().len() as int)))).handshake.state == ClientState::Connected,
        // §5.1: an incomplete record leaves the bytes to come.
        receive_stream(toy_primitives(), conn_wait_sh(), toy_sh_record().subrange(0, 7)).1 == toy_sh_record().subrange(0, 7),
{
    assert((start_connection(toy_primitives(), toy_hello(true), toy_bytes(0x22), toy_bytes(0x23)).1)
        == seq![write_tls_plaintext(ct_handshake(), 0x0301, write_client_hello(toy_hello(true)))]) by (compute);
    assert(conn_wait_ee().handshake.state == ClientState::WaitEe) by (compute);
    assert(conn_wait_ee().receive is Protected) by (compute);
    assert(conn_wait_ee().send is Unprotected) by (compute);
    assert(conn_connected().handshake.state == ClientState::Connected) by (compute);
    assert((first_flight()->Continue_0).records_to_send == seq![
        protect_record(toy_primitives(), traffic_state(toy_primitives(), conn_connected().handshake.client_handshake_traffic_secret),
            ct_handshake(), conn_connected().handshake.transcript.last())]) by (compute);
    assert((conn_connected().receive->Protected_0).sequence_number == 0) by (compute);
    assert((conn_connected().send->Protected_0).sequence_number == 0) by (compute);
    assert(conn_after(stream_result(conn_wait_sh(), toy_sh_record() + server_hs_record(0, ct_handshake(), toy_flight().subrange(0, 10))
        + server_hs_record(1, ct_handshake(), toy_flight().subrange(10, toy_flight().len() as int)))).handshake.state == ClientState::Connected) by (compute);
    assert(receive_stream(toy_primitives(), conn_wait_sh(), toy_sh_record().subrange(0, 7)).1 == toy_sh_record().subrange(0, 7)) by (compute);
}

/// §5, §5.1, §5.2, §5.4: refusals by the record layer, unprotected.
proof fn record_refusals_unprotected()
{
    // §5.1, by the header alone.
    // §5: a change_cipher_spec of the right value, dropped; another, refused.
    // §5: an unprotected application data record; an unknown type; invalid(0).
    // §5.1, §5.4: zero length.
    // §5.1, §6: one alert exactly.
    // §6: error alerts, by value not level, and unknown ones.
    // §6.1: closure alerts, by value not level, and data after them is ignored.
    // §5.1: reassembly and interleaving, a change_cipher_spec included.
    // §5.1: ServerHello must end its record.
    // §4: the wrong message first; message_hash has no arm of `select`.
    assert(receive_aborted(stream_result(conn_wait_sh(), seq![22u8, 3, 3, 0x40, 0x01]), ClientError::PlaintextTooLong)) by (compute);
    assert(!receive_aborted(stream_result(conn_wait_sh(), seq![22u8, 3, 3, 0x40, 0x00]), ClientError::PlaintextTooLong)) by (compute);
    assert(conn_after(stream_result(conn_wait_sh(), plain(ct_change_cipher_spec(), seq![1u8]))) == conn_wait_sh()) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_change_cipher_spec(), seq![2u8])), ClientError::ChangeCipherSpecBadValue)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_change_cipher_spec(), seq![1u8, 1])), ClientError::ChangeCipherSpecBadValue)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_application_data(), seq![1u8])), ClientError::UnexpectedRecordType)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(99, seq![1u8])), ClientError::UnexpectedRecordType)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_invalid(), seq![1u8])), ClientError::UnexpectedRecordType)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_handshake(), seq![])), ClientError::ZeroLengthContent)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_alert(), seq![])), ClientError::ZeroLengthContent)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_alert(), seq![2u8])), ClientError::Malformed)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_alert(), seq![2u8, 40, 2, 40])), ClientError::Malformed)) by (compute);
    assert(stream_result(conn_wait_sh(), plain(ct_alert(), seq![1u8, 40])) == Receive::PeerError(40)) by (compute);
    assert(stream_result(conn_wait_sh(), plain(ct_alert(), seq![2u8, 200])) == Receive::PeerError(200)) by (compute);
    assert(conn_after(stream_result(conn_wait_sh(), plain(ct_alert(), seq![2u8, 0]))).read_closed) by (compute);
    // Changed by the equivalence author: user_canceled closes nothing (§6.1).
    assert(conn_after(stream_result(conn_wait_sh(), plain(ct_alert(), seq![1u8, 90]))) == conn_wait_sh()) by (compute);
    assert(conn_after(stream_result(conn_wait_sh(), plain(ct_alert(), seq![1u8, 0]) + plain(99, seq![1u8]))).read_closed) by (compute);
    assert(conn_after(stream_result(conn_wait_sh(), plain(ct_handshake(), seq![2u8, 0]))).handshake_fragments == seq![2u8, 0]) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_handshake(), seq![2u8, 0]) + plain(ct_alert(), seq![1u8, 0])), ClientError::InterleavedRecord)) by (compute);
    // Changed by the equivalence author with `receive_record`: a change_cipher_spec
    // inside a fragmented message is refused (docs/ERRATA.md).
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_handshake(), seq![2u8, 0]) + plain(ct_change_cipher_spec(), seq![1u8])), ClientError::InterleavedRecord)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_handshake(), write_server_hello(toy_server_hello()) + seq![8u8])), ClientError::KeyChangeNotAligned)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_handshake(), toy_ee())), ClientError::UnexpectedHandshakeMessage)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_sh(), plain(ct_handshake(), write_handshake(ht_message_hash(), toy_bytes(1)))), ClientError::UnexpectedHandshakeMessage)) by (compute);
}

/// §5, §5.2, §5.3, §5.4: refusals and successes by the record layer, protected.
proof fn record_behaviour_protected()
{
    // §5.2, by the header alone.
    // §5.1, §5.2: a plaintext record when protection is engaged, except §5's.
    // §5.2: failed deprotection, including a truncated record, and a wrong number.
    // §5.2: additional_data covers the version as received.
    // §5.3: the read number advances past each protected record, and only those.
    // §5: a protected change_cipher_spec.
    // §5.4: zero-length content, and no content type at all.
    // §6.2: premature application data.
    // §5: an unknown inner type.
    // After CONNECTED: application data, also of zero length (§5.1).
    // §5: "after the peer's Finished message".
    // §5.1: KeyUpdate must end its record.
    // §6.1: close_notify, then nothing is read.
    assert(receive_aborted(stream_result(conn_wait_ee(), seq![23u8, 3, 3, 0x41, 0x01]), ClientError::CiphertextTooLong)) by (compute);
    assert(!receive_aborted(stream_result(conn_wait_ee(), seq![23u8, 3, 3, 0x41, 0x00]), ClientError::CiphertextTooLong)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), plain(ct_alert(), seq![2u8, 40])), ClientError::UnexpectedRecordType)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), plain(ct_handshake(), toy_ee())), ClientError::UnexpectedRecordType)) by (compute);
    assert(conn_after(stream_result(conn_wait_ee(), plain(ct_change_cipher_spec(), seq![1u8]))) == conn_wait_ee()) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), seq![23u8, 3, 3, 0, 1, 0]), ClientError::DeprotectionFailed)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), server_hs_record(1, ct_handshake(), toy_ee())), ClientError::DeprotectionFailed)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(),
        seq![23u8, 3, 1] + server_hs_record(0, ct_handshake(), toy_ee()).subrange(3, server_hs_record(0, ct_handshake(), toy_ee()).len() as int)),
        ClientError::DeprotectionFailed)) by (compute);
    assert((conn_after(stream_result(conn_wait_ee(), server_hs_record(0, ct_handshake(), toy_ee()))).receive->Protected_0).sequence_number == 1) by (compute);
    assert((conn_after(stream_result(conn_wait_ee(), plain(ct_change_cipher_spec(), seq![1u8]) + server_hs_record(0, ct_handshake(), toy_ee()))).receive->Protected_0).sequence_number == 1) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), server_hs_record(0, ct_change_cipher_spec(), seq![1u8])), ClientError::ChangeCipherSpecProtected)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), server_hs_record(0, ct_handshake(), seq![])), ClientError::ZeroLengthContent)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), server_hs_record(0, ct_alert(), seq![])), ClientError::ZeroLengthContent)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), server_hs_record(0, ct_application_data(), seq![1u8])), ClientError::UnexpectedRecordType)) by (compute);
    assert(receive_aborted(stream_result(conn_wait_ee(), server_hs_record(0, 99, seq![1u8])), ClientError::UnexpectedRecordType)) by (compute);
    assert((stream_result(conn_connected(), server_ap_record(0, ct_application_data(), seq![1u8, 2]))->Continue_0).application_data == seq![1u8, 2]) by (compute);
    assert((stream_result(conn_connected(), server_ap_record(0, ct_application_data(), seq![]))->Continue_0).application_data == no_bytes()) by (compute);
    assert(receive_aborted(stream_result(conn_connected(), plain(ct_change_cipher_spec(), seq![1u8])), ClientError::UnexpectedRecordType)) by (compute);
    assert(receive_aborted(stream_result(conn_connected(), server_ap_record(0, ct_handshake(), write_key_update(0) + seq![4u8])), ClientError::KeyChangeNotAligned)) by (compute);
    assert((stream_result(conn_connected(), server_ap_record(0, ct_alert(), seq![1u8, 0]) + server_ap_record(1, ct_application_data(), seq![1u8]))->Continue_0).application_data == no_bytes()) by (compute);
}

/// The connection after the server sends a KeyUpdate asking for one back.
pub open spec fn conn_updated() -> Connection {
    conn_after(stream_result(conn_connected(), server_ap_record(0, ct_handshake(), write_key_update(update_requested()))))
}

/// §4.6.3, §7.2: the key update, both ways.
proof fn key_updates()
    ensures
        // The receive key moves to the next generation at sequence number 0.
        (conn_updated().receive->Protected_0).secret
            == next_application_traffic_secret(toy_primitives(), (conn_connected().receive->Protected_0).secret),
        (conn_updated().receive->Protected_0).sequence_number == 0,
        conn_updated().key_update_owed,
        // §4.6.3: the next data goes after a KeyUpdate of ours, under the old key, then
        // the new one; and only one is owed.
        match send_application_data(toy_primitives(), conn_updated(), seq![9u8]) {
            SendResult::Sent(records, after) => {
                &&& records.len() == 2
                &&& records[0] == protect_record(toy_primitives(), conn_updated().send->Protected_0, ct_handshake(), write_key_update(update_not_requested()))
                &&& records[1] == protect_record(toy_primitives(),
                    traffic_state(toy_primitives(), next_application_traffic_secret(toy_primitives(), (conn_updated().send->Protected_0).secret)),
                    ct_application_data(), seq![9u8])
                &&& !after.key_update_owed
                &&& (after.send->Protected_0).sequence_number == 1
            },
            _ => false,
        },
        // §5.3: a plain send advances the number, and A.1's "can send app data after here".
        match send_application_data(toy_primitives(), conn_connected(), seq![9u8]) {
            SendResult::Sent(records, after) => records.len() == 1 && (after.send->Protected_0).sequence_number == 1,
            _ => false,
        },
        send_application_data(toy_primitives(), conn_wait_ee(), seq![9u8]) == SendResult::NotConnected,
        // §5.1: application data is fragmented at 2^14.
        fragment_blocks(repeat_byte(1, 3)) == seq![repeat_byte(1, 3)],
{
    assert((conn_updated().receive->Protected_0).secret
        == next_application_traffic_secret(toy_primitives(), (conn_connected().receive->Protected_0).secret)) by (compute);
    assert((conn_updated().receive->Protected_0).sequence_number == 0) by (compute);
    assert(conn_updated().key_update_owed) by (compute);
    assert(match send_application_data(toy_primitives(), conn_updated(), seq![9u8]) {
        SendResult::Sent(records, after) => {
            &&& records.len() == 2
            &&& records[0] == protect_record(toy_primitives(), conn_updated().send->Protected_0, ct_handshake(), write_key_update(update_not_requested()))
            &&& records[1] == protect_record(toy_primitives(),
                traffic_state(toy_primitives(), next_application_traffic_secret(toy_primitives(), (conn_updated().send->Protected_0).secret)),
                ct_application_data(), seq![9u8])
            &&& !after.key_update_owed
            &&& (after.send->Protected_0).sequence_number == 1
        },
        _ => false,
    }) by (compute);
    assert(match send_application_data(toy_primitives(), conn_connected(), seq![9u8]) {
        SendResult::Sent(records, after) => records.len() == 1 && (after.send->Protected_0).sequence_number == 1,
        _ => false,
    }) by (compute);
    assert(send_application_data(toy_primitives(), conn_wait_ee(), seq![9u8]) == SendResult::NotConnected) by (compute);
    assert(fragment_blocks(repeat_byte(1, 3)) == seq![repeat_byte(1, 3)]) by (compute);
}

/// §6, A.1's note: what an alert is sent under, by state.
proof fn alert_protection()
    ensures
        // Before ServerHello: in the clear, level fatal.
        abort_record(toy_primitives(), conn_wait_sh(), ClientError::Malformed) == write_tls_plaintext(ct_alert(), 0x0303, seq![2u8, 50]),
        // After ServerHello, before Finished: A.1's note, under the handshake keys.
        abort_record(toy_primitives(), conn_wait_ee(), ClientError::Malformed)
            == protect_record(toy_primitives(), traffic_state(toy_primitives(), conn_wait_ee().handshake.client_handshake_traffic_secret), ct_alert(), seq![2u8, 50]),
        // After Finished: §4.4.4, under the application keys.
        abort_record(toy_primitives(), conn_connected(), ClientError::Malformed)
            == protect_record(toy_primitives(), conn_connected().send->Protected_0, ct_alert(), seq![2u8, 50]),
        close_write(toy_primitives(), conn_connected())
            == protect_record(toy_primitives(), conn_connected().send->Protected_0, ct_alert(), seq![1u8, 0]),
{
    assert(abort_record(toy_primitives(), conn_wait_sh(), ClientError::Malformed) == write_tls_plaintext(ct_alert(), 0x0303, seq![2u8, 50])) by (compute);
    assert(abort_record(toy_primitives(), conn_wait_ee(), ClientError::Malformed)
        == protect_record(toy_primitives(), traffic_state(toy_primitives(), conn_wait_ee().handshake.client_handshake_traffic_secret), ct_alert(), seq![2u8, 50])) by (compute);
    assert(abort_record(toy_primitives(), conn_connected(), ClientError::Malformed)
        == protect_record(toy_primitives(), conn_connected().send->Protected_0, ct_alert(), seq![2u8, 50])) by (compute);
    assert(close_write(toy_primitives(), conn_connected())
        == protect_record(toy_primitives(), conn_connected().send->Protected_0, ct_alert(), seq![1u8, 0])) by (compute);
}

} // verus!
