//! Action-driven client bootstrap tests through final ServerHello.
//! TestCrypto is an input-sensitive deterministic protocol double, not real
//! SHA-256/HKDF/HMAC or production cryptography.

use clazel_tls::hello::bootstrap::{Action, Bootstrap};
use clazel_tls::hello::client::Config;
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::spec::{INTERNAL_ERROR, UNEXPECTED_MESSAGE};
use clazel_tls::{encode, record};
use sha2::{Digest, Sha256};

const HOST: &[u8] = b"bootstrap.example.test";
const SESSION: &[u8] = b"middlebox-id";
const RANDOM: [u8; 32] = [0x35; 32];
const CLIENT_KEY: [u8; 32] = [0x48; 32];
const SERVER_KEY: [u8; 32] = [0x5a; 32];
const HRR_RANDOM: [u8; 32] = [
    0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c,
];

/// Deterministic transcript provider only; not an interoperable crypto suite.
struct TestCrypto;

impl Crypto for TestCrypto {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let mut input = b"bootstrap extract".to_vec();
        input.extend_from_slice(salt);
        input.extend_from_slice(ikm);
        Sha256::digest(input).to_vec()
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut input = b"bootstrap expand".to_vec();
        input.extend_from_slice(secret);
        input.extend_from_slice(info);
        let block = Sha256::digest(input);
        let mut output = Vec::with_capacity(usize::from(length));
        while output.len() < usize::from(length) {
            output.extend_from_slice(&block);
        }
        output.truncate(usize::from(length));
        output
    }

    fn hmac(&self, key: &[u8], message: &[u8]) -> Vec<u8> {
        let mut input = b"bootstrap hmac".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(message);
        Sha256::digest(input).to_vec()
    }
}

fn config(session_id: &[u8]) -> Config {
    Config {
        host: HOST.to_vec(),
        now: 1_800_000_000,
        random: RANDOM.to_vec(),
        session_id: session_id.to_vec(),
        public_key: CLIENT_KEY.to_vec(),
        send_sni: true,
    }
}

fn handshake(kind: u8, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    encode::write_handshake(&mut out, kind, body);
    out
}

fn plaintext(kind: u8, content: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    record::write_plaintext(&mut out, kind, 0x0303, content);
    out
}

fn server_hello(session_id: &[u8], retry: bool) -> Vec<u8> {
    let mut extensions = Vec::new();
    if retry {
        extensions.extend_from_slice(&[0, 43, 0, 2, 3, 4]);
        let cookie = [0, 5, 0xde, 0xad, 0xbe, 0xef, 0x01];
        extensions.extend_from_slice(&[0, 44]);
        extensions.extend_from_slice(&(cookie.len() as u16).to_be_bytes());
        extensions.extend_from_slice(&cookie);
    } else {
        extensions.extend_from_slice(&[0, 43, 0, 2, 3, 4]);
        let mut key_share = Vec::new();
        key_share.extend_from_slice(&29u16.to_be_bytes());
        key_share.extend_from_slice(&(SERVER_KEY.len() as u16).to_be_bytes());
        key_share.extend_from_slice(&SERVER_KEY);
        extensions.extend_from_slice(&[0, 51]);
        extensions.extend_from_slice(&(key_share.len() as u16).to_be_bytes());
        extensions.extend_from_slice(&key_share);
    }

    let mut body = Vec::new();
    body.extend_from_slice(&0x0303u16.to_be_bytes());
    body.extend_from_slice(if retry { &HRR_RANDOM } else { &[0x71; 32] });
    body.push(session_id.len() as u8);
    body.extend_from_slice(session_id);
    body.extend_from_slice(&0x1303u16.to_be_bytes());
    body.push(0);
    body.extend_from_slice(&(extensions.len() as u16).to_be_bytes());
    body.extend_from_slice(&extensions);
    body
}

fn started(session_id: &[u8]) -> Result<(Bootstrap<TestCrypto>, Vec<u8>), String> {
    match Bootstrap::start(config(session_id), TestCrypto) {
        Ok((bootstrap, Action::Send(wire))) => Ok((bootstrap, wire)),
        Ok(_) => Err("start did not emit ClientHello".to_owned()),
        Err(alert) => Err(format!("start failed with alert {alert}")),
    }
}

fn ack_initial(bootstrap: &mut Bootstrap<TestCrypto>, wire: &[u8]) -> Result<(), String> {
    if !matches!(bootstrap.acknowledge_send(wire), Action::None) {
        return Err("exact ClientHello acknowledgement was rejected".to_owned());
    }
    Ok(())
}

#[test]
fn exact_send_ack_gates_peer_input_and_wrong_ack_is_terminal() -> Result<(), String> {
    let (mut bootstrap, client_wire) = started(SESSION)?;
    assert_eq!(client_wire.first(), Some(&22));

    let wrong = [client_wire.as_slice(), &[0]].concat();
    assert!(matches!(
        bootstrap.acknowledge_send(&wrong),
        Action::Fail(INTERNAL_ERROR)
    ));
    let peer = plaintext(22, &handshake(2, &server_hello(SESSION, false)));
    assert_eq!(bootstrap.feed(&peer).0, 0);
    assert!(matches!(bootstrap.eof(), Action::None));
    Ok(())
}

#[test]
fn ccs_inside_fragmented_server_hello_is_unexpected_message() -> Result<(), String> {
    let (mut bootstrap, client_wire) = started(SESSION)?;
    ack_initial(&mut bootstrap, &client_wire)?;

    let hello = handshake(2, &server_hello(SESSION, false));
    let split = hello.len() / 2;
    let first_record = plaintext(22, hello.get(..split).ok_or("missing first fragment")?);
    let (consumed, first_action) = bootstrap.feed(&first_record);
    assert_eq!(consumed, first_record.len());
    assert!(matches!(first_action, Action::None));

    // RFC 8446 §5 says to drop a CCS at any time, but §5.1 forbids any other
    // record between fragments of one handshake message. Inside a message the
    // CCS is fatal (docs/ERRATA.md); it is dropped only at a boundary.
    let dummy_ccs = [20, 3, 3, 0, 1, 1];
    let (consumed, ccs_action) = bootstrap.feed(&dummy_ccs);
    assert_eq!(consumed, dummy_ccs.len());
    assert!(matches!(ccs_action, Action::Fail(UNEXPECTED_MESSAGE)));

    // The failure is terminal: the remaining fragment is not accepted.
    let last_record = plaintext(22, hello.get(split..).ok_or("missing last fragment")?);
    let (_, final_action) = bootstrap.feed(&last_record);
    assert!(!matches!(final_action, Action::Established(_)));
    Ok(())
}

#[test]
fn ccs_at_message_boundary_before_server_hello_is_dropped() -> Result<(), String> {
    let (mut bootstrap, client_wire) = started(SESSION)?;
    ack_initial(&mut bootstrap, &client_wire)?;

    let dummy_ccs = [20, 3, 3, 0, 1, 1];
    let (consumed, ccs_action) = bootstrap.feed(&dummy_ccs);
    assert_eq!(consumed, dummy_ccs.len());
    assert!(matches!(ccs_action, Action::None));

    let hello = plaintext(22, &handshake(2, &server_hello(SESSION, false)));
    let (consumed, action) = bootstrap.feed(&hello);
    assert_eq!(consumed, hello.len());
    assert!(matches!(action, Action::Established(_)));
    Ok(())
}

#[test]
fn retry_flight_orders_compatibility_ccs_and_requires_exact_ack() -> Result<(), String> {
    let (mut bootstrap, client_wire) = started(SESSION)?;
    ack_initial(&mut bootstrap, &client_wire)?;

    let retry_record = plaintext(22, &handshake(2, &server_hello(SESSION, true)));
    let (consumed, action) = bootstrap.feed(&retry_record);
    assert_eq!(consumed, retry_record.len());
    let retry_wire = match action {
        Action::Send(wire) => wire,
        _ => return Err("valid HRR did not produce a second ClientHello".to_owned()),
    };
    assert_eq!(retry_wire.get(..6), Some(&[20, 3, 3, 0, 1, 1][..]));
    assert_eq!(retry_wire.get(6), Some(&22));

    let server = plaintext(22, &handshake(2, &server_hello(SESSION, false)));
    assert_eq!(bootstrap.feed(&server).0, 0);
    assert!(matches!(
        bootstrap.acknowledge_send(&retry_wire),
        Action::None
    ));
    let (consumed, action) = bootstrap.feed(&server);
    assert_eq!(consumed, server.len());
    assert!(matches!(action, Action::Established(_)));
    Ok(())
}

#[test]
fn no_compatibility_ccs_for_empty_session_id_and_coalesced_suffix_stays_unconsumed()
-> Result<(), String> {
    let (mut bootstrap, client_wire) = started(&[])?;
    ack_initial(&mut bootstrap, &client_wire)?;
    let retry = plaintext(22, &handshake(2, &server_hello(&[], true)));
    let (_, action) = bootstrap.feed(&retry);
    let retry_wire = match action {
        Action::Send(wire) => wire,
        _ => return Err("valid HRR did not produce a retry flight".to_owned()),
    };
    assert_eq!(retry_wire.first(), Some(&22));
    assert!(matches!(
        bootstrap.acknowledge_send(&retry_wire),
        Action::None
    ));

    let final_record = plaintext(22, &handshake(2, &server_hello(&[], false)));
    let suffix = [final_record.as_slice(), &[20, 3, 3, 0, 1, 1]].concat();
    let (consumed, action) = bootstrap.feed(&suffix);
    assert_eq!(consumed, final_record.len());
    assert!(matches!(action, Action::Established(_)));
    assert_eq!(
        bootstrap
            .feed(suffix.get(consumed..).ok_or("bad consumed boundary")?)
            .0,
        0
    );
    Ok(())
}

#[test]
fn application_data_and_eof_before_server_hello_fail_closed() -> Result<(), String> {
    let (mut bootstrap, client_wire) = started(&[])?;
    ack_initial(&mut bootstrap, &client_wire)?;
    let app = plaintext(23, b"early application data");
    let (consumed, action) = bootstrap.feed(&app);
    assert_eq!(consumed, 5); // The type is rejected as soon as the record header is complete.
    assert!(matches!(action, Action::Fail(UNEXPECTED_MESSAGE)));

    let (mut truncated, truncated_wire) = started(&[])?;
    ack_initial(&mut truncated, &truncated_wire)?;
    assert!(matches!(truncated.eof(), Action::Fail(INTERNAL_ERROR)));
    Ok(())
}
