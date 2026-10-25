//! Adversarial tests for the fixed TLS 1.3 ServerHello negotiation profile.
//! Acceptance is parameter selection only; it does not authenticate the peer.

use clazel_tls::hello::exec::{Selection, validate};
use clazel_tls::spec::{
    DECODE_ERROR, ILLEGAL_PARAMETER, INTERNAL_ERROR, MISSING_EXTENSION, UNEXPECTED_MESSAGE,
    UNSUPPORTED_EXTENSION,
};

const SESSION_ID: &[u8] = b"session-id";
const RANDOM: [u8; 32] = [0x55; 32];
const X25519_SHARE: [u8; 32] = [0x66; 32];
const COOKIE: [u8; 4] = [0xde, 0xad, 0xbe, 0xef];
const HRR_RANDOM: [u8; 32] = [
    0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c,
];

/// Build a ServerHello body directly from its presentation-language fields.
/// This keeps expected wire fields independent from the production encoder.
fn server_hello(
    legacy_version: u16,
    random: &[u8; 32],
    session_id: &[u8],
    cipher_suite: u16,
    compression: u8,
    extensions: &[(u16, &[u8])],
) -> Vec<u8> {
    let mut extension_bytes = Vec::new();
    for (extension_type, data) in extensions {
        extension_bytes.extend_from_slice(&extension_type.to_be_bytes());
        let extension_length = u16::try_from(data.len()).unwrap_or(u16::MAX);
        extension_bytes.extend_from_slice(&extension_length.to_be_bytes());
        extension_bytes.extend_from_slice(data);
    }
    let mut body = Vec::new();
    body.extend_from_slice(&legacy_version.to_be_bytes());
    body.extend_from_slice(random);
    let session_length = u8::try_from(session_id.len()).unwrap_or(u8::MAX);
    body.push(session_length);
    body.extend_from_slice(session_id);
    body.extend_from_slice(&cipher_suite.to_be_bytes());
    body.push(compression);
    let extensions_length = u16::try_from(extension_bytes.len()).unwrap_or(u16::MAX);
    body.extend_from_slice(&extensions_length.to_be_bytes());
    body.extend_from_slice(&extension_bytes);
    body
}

fn supported_versions(version: u16) -> [u8; 2] {
    version.to_be_bytes()
}

fn server_key_share(group: u16, key: &[u8]) -> Vec<u8> {
    let mut data = Vec::new();
    data.extend_from_slice(&group.to_be_bytes());
    let key_length = u16::try_from(key.len()).unwrap_or(u16::MAX);
    data.extend_from_slice(&key_length.to_be_bytes());
    data.extend_from_slice(key);
    data
}

fn valid_extensions(key: &[u8]) -> Vec<(u16, Vec<u8>)> {
    vec![
        (43, supported_versions(0x0304).to_vec()),
        (51, server_key_share(29, key)),
    ]
}

fn borrow_extensions(extensions: &[(u16, Vec<u8>)]) -> Vec<(u16, &[u8])> {
    extensions
        .iter()
        .map(|(kind, data)| (*kind, data.as_slice()))
        .collect()
}

fn normal_server_hello(session_id: &[u8]) -> Vec<u8> {
    let extensions = valid_extensions(&X25519_SHARE);
    server_hello(
        0x0303,
        &RANDOM,
        session_id,
        0x1303,
        0,
        &borrow_extensions(&extensions),
    )
}

#[test]
fn accepts_only_the_fixed_profile_and_returns_the_raw_x25519_share() -> Result<(), String> {
    for session_id in [&b""[..], SESSION_ID] {
        let body = normal_server_hello(session_id);
        match validate(session_id, false, &body) {
            Ok(Selection::Share(share)) => assert_eq!(share, X25519_SHARE),
            other => return Err(format!("expected offered X25519 share, got {other:?}")),
        }
    }
    Ok(())
}

#[test]
fn rejects_invalid_legacy_fields_and_selected_version() {
    let extensions = valid_extensions(&X25519_SHARE);
    let extension_refs = borrow_extensions(&extensions);
    let cases = [
        server_hello(0x0303, &RANDOM, b"other", 0x1303, 0, &extension_refs),
        server_hello(0x0303, &RANDOM, SESSION_ID, 0x1301, 0, &extension_refs),
        server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 1, &extension_refs),
    ];
    for body in cases {
        assert_eq!(validate(SESSION_ID, false, &body), Err(ILLEGAL_PARAMETER));
    }

    // RFC 8446 §4.2.1: supported_versions takes precedence over the legacy field.
    let ignored_legacy = server_hello(0x0304, &RANDOM, SESSION_ID, 0x1303, 0, &extension_refs);
    assert_eq!(
        validate(SESSION_ID, false, &ignored_legacy),
        Ok(Selection::Share(&X25519_SHARE))
    );

    let bad_version = supported_versions(0x0303);
    let key_share = server_key_share(29, &X25519_SHARE);
    let extensions = [(43, bad_version.as_slice()), (51, key_share.as_slice())];
    let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &extensions);
    assert_eq!(validate(SESSION_ID, false, &body), Err(ILLEGAL_PARAMETER));
}

#[test]
fn requires_a_valid_offered_x25519_share() {
    let version = supported_versions(0x0304);
    let no_share = [(43, version.as_slice())];
    let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &no_share);
    assert_eq!(validate(SESSION_ID, false, &body), Err(MISSING_EXTENSION));

    for (group, key) in [
        (23, &X25519_SHARE[..]),
        (29, &[0x77; 31][..]),
        (29, &[0x77; 33][..]),
    ] {
        let key_share = server_key_share(group, key);
        let extensions = [(43, version.as_slice()), (51, key_share.as_slice())];
        let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &extensions);
        assert_eq!(validate(SESSION_ID, false, &body), Err(ILLEGAL_PARAMETER));
    }
}

#[test]
fn parser_rejects_malformed_and_duplicate_extensions_before_negotiation() {
    let malformed_version = [3, 4, 5];
    let key_share = server_key_share(29, &X25519_SHARE);
    let malformed = [
        (43, malformed_version.as_slice()),
        (51, key_share.as_slice()),
    ];
    let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &malformed);
    assert_eq!(validate(SESSION_ID, false, &body), Err(DECODE_ERROR));

    let version = supported_versions(0x0304);
    let duplicate = [
        (43, version.as_slice()),
        (43, version.as_slice()),
        (51, key_share.as_slice()),
    ];
    let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &duplicate);
    assert_eq!(validate(SESSION_ID, false, &body), Err(ILLEGAL_PARAMETER));

    let unknown = [
        (43, version.as_slice()),
        (0xfafa, &[1, 2][..]),
        (51, key_share.as_slice()),
    ];
    let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &unknown);
    assert_eq!(
        validate(SESSION_ID, false, &body),
        Err(UNSUPPORTED_EXTENSION)
    );
}

#[test]
fn cookie_only_retry_returns_exact_extension_data_and_rejects_invalid_retries() {
    let version = supported_versions(0x0304);
    let mut cookie_data = Vec::new();
    cookie_data.extend_from_slice(&u16::try_from(COOKIE.len()).unwrap_or(0).to_be_bytes());
    cookie_data.extend_from_slice(&COOKIE);
    let extensions = [(43, version.as_slice()), (44, cookie_data.as_slice())];
    let body = server_hello(0x0303, &HRR_RANDOM, SESSION_ID, 0x1303, 0, &extensions);
    assert_eq!(
        validate(SESSION_ID, false, &body),
        Ok(Selection::Retry(&cookie_data))
    );
    assert_eq!(validate(SESSION_ID, true, &body), Err(UNEXPECTED_MESSAGE));

    let version_only = [(43, version.as_slice())];
    let noop = server_hello(0x0303, &HRR_RANDOM, SESSION_ID, 0x1303, 0, &version_only);
    assert_eq!(validate(SESSION_ID, false, &noop), Err(ILLEGAL_PARAMETER));

    let selected_group = 29u16.to_be_bytes();
    let redundant_share = [(43, version.as_slice()), (51, selected_group.as_slice())];
    let redundant = server_hello(0x0303, &HRR_RANDOM, SESSION_ID, 0x1303, 0, &redundant_share);
    assert_eq!(
        validate(SESSION_ID, false, &redundant),
        Err(ILLEGAL_PARAMETER)
    );
    // A valid cookie must not mask a request to replace an already offered share.
    let cookie_and_share = [
        (43, version.as_slice()),
        (44, cookie_data.as_slice()),
        (51, selected_group.as_slice()),
    ];
    let redundant = server_hello(
        0x0303,
        &HRR_RANDOM,
        SESSION_ID,
        0x1303,
        0,
        &cookie_and_share,
    );
    assert_eq!(
        validate(SESSION_ID, false, &redundant),
        Err(ILLEGAL_PARAMETER)
    );

    let unoffered_group = 23u16.to_be_bytes();
    let asks_for_group = [(43, version.as_slice()), (51, unoffered_group.as_slice())];
    let unoffered = server_hello(0x0303, &HRR_RANDOM, SESSION_ID, 0x1303, 0, &asks_for_group);
    assert_eq!(
        validate(SESSION_ID, false, &unoffered),
        Err(ILLEGAL_PARAMETER)
    );
}

#[test]
fn rejects_invalid_local_bounds_before_parsing() {
    let body = normal_server_hello(SESSION_ID);
    let oversized_session = vec![0; 33];
    assert_eq!(
        validate(&oversized_session, false, &body),
        Err(INTERNAL_ERROR)
    );

    let oversized_body = vec![0; 262_145];
    assert_eq!(
        validate(SESSION_ID, false, &oversized_body),
        Err(INTERNAL_ERROR)
    );
}

#[test]
fn rejects_missing_versions_misplaced_extensions_and_malformed_retry_cookies() {
    let key = server_key_share(29, &X25519_SHARE);
    let body = server_hello(0x0303, &RANDOM, SESSION_ID, 0x1303, 0, &[(51, &key)]);
    assert_eq!(validate(SESSION_ID, false, &body), Err(MISSING_EXTENSION));

    let version = supported_versions(0x0304);
    // Cookie is the HRR-only exception; it cannot appear in a final ServerHello.
    let body = server_hello(
        0x0303,
        &RANDOM,
        SESSION_ID,
        0x1303,
        0,
        &[(43, &version), (51, &key), (44, &[0, 1, 9])],
    );
    assert_eq!(validate(SESSION_ID, false, &body), Err(ILLEGAL_PARAMETER));

    for cookie in [&[0, 0][..], &[0, 2, 9][..], &[0, 1, 9, 10][..]] {
        let body = server_hello(
            0x0303,
            &HRR_RANDOM,
            SESSION_ID,
            0x1303,
            0,
            &[(43, &version), (44, cookie)],
        );
        assert_eq!(validate(SESSION_ID, false, &body), Err(DECODE_ERROR));
    }
}

#[test]
fn accepts_final_server_hello_after_retry_and_checks_every_truncated_prefix() {
    let body = normal_server_hello(SESSION_ID);
    assert_eq!(
        validate(SESSION_ID, true, &body),
        Ok(Selection::Share(&X25519_SHARE))
    );
    for end in 0..body.len() {
        let prefix = body.get(..end).unwrap_or(&[]);
        assert_eq!(validate(SESSION_ID, false, prefix), Err(DECODE_ERROR));
    }
    let mut trailing = body;
    trailing.push(0);
    assert_eq!(validate(SESSION_ID, false, &trailing), Err(DECODE_ERROR));
}
