//! Tests for the initial ClientHello and cookie-only retry controller.
//! The provider below is input-sensitive but is only a transcript test double.

use clazel_tls::hello::client::{Config, Established, Hello, Outcome};
use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::spec::{ILLEGAL_PARAMETER, INTERNAL_ERROR, UNEXPECTED_MESSAGE};
use clazel_tls::types::{ClientHello, HsMsg};
use clazel_tls::{encode, handshake};
use sha2::{Digest, Sha256};

const HOST: &[u8] = b"www.example.test";
const SESSION_ID: &[u8] = b"client-session";
const RANDOM: [u8; 32] = [0x11; 32];
const PUBLIC_KEY: [u8; 32] = [0x22; 32];
const SERVER_KEY: [u8; 32] = [0x33; 32];
const HRR_RANDOM: [u8; 32] = [
    0xcf, 0x21, 0xad, 0x74, 0xe5, 0x9a, 0x61, 0x11, 0xbe, 0x1d, 0x8c, 0x02, 0x1e, 0x65, 0xb8, 0x91,
    0xc2, 0xa2, 0x11, 0x16, 0x7a, 0xbb, 0x8c, 0x5e, 0x07, 0x9e, 0x09, 0xe2, 0xc8, 0xa8, 0x33, 0x9c,
];

/// Deterministic test provider, not real SHA-256/HKDF/HMAC or production crypto.
struct TestCrypto;

impl Crypto for TestCrypto {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let mut input = b"test extract".to_vec();
        input.extend_from_slice(salt);
        input.extend_from_slice(ikm);
        Sha256::digest(input).to_vec()
    }

    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut input = b"test expand".to_vec();
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
        let mut input = b"test hmac".to_vec();
        input.extend_from_slice(key);
        input.extend_from_slice(message);
        Sha256::digest(input).to_vec()
    }
}

fn config() -> Config {
    Config {
        host: HOST.to_vec(),
        now: 1_800_000_000,
        random: RANDOM.to_vec(),
        session_id: SESSION_ID.to_vec(),
        public_key: PUBLIC_KEY.to_vec(),
        send_sni: true,
    }
}

fn handshake_message(kind: u8, body: &[u8]) -> Vec<u8> {
    let mut message = Vec::new();
    encode::write_handshake(&mut message, kind, body);
    message
}

fn client_hello(flight: &[u8]) -> Result<ClientHello<'_>, String> {
    match handshake::parse_handshake(flight, 32) {
        Ok(HsMsg::ClientHello(hello)) => Ok(hello),
        Ok(other) => Err(format!("expected ClientHello, got {other:?}")),
        Err(error) => Err(format!("invalid ClientHello encoding: {error:?}")),
    }
}

fn extension_data<'a>(hello: &'a ClientHello<'_>, kind: u16) -> Option<&'a [u8]> {
    hello
        .extensions
        .iter()
        .find(|extension| extension.etype == kind)
        .map(|extension| extension.data)
}

fn extension_bytes(extensions: &[(u16, &[u8])]) -> Vec<u8> {
    let mut encoded = Vec::new();
    for (kind, data) in extensions {
        encoded.extend_from_slice(&kind.to_be_bytes());
        let length = u16::try_from(data.len()).unwrap_or(u16::MAX);
        encoded.extend_from_slice(&length.to_be_bytes());
        encoded.extend_from_slice(data);
    }
    encoded
}

fn server_hello(random: &[u8; 32], session_id: &[u8], extensions: &[(u16, &[u8])]) -> Vec<u8> {
    let encoded_extensions = extension_bytes(extensions);
    let mut body = Vec::new();
    body.extend_from_slice(&0x0303u16.to_be_bytes());
    body.extend_from_slice(random);
    body.push(u8::try_from(session_id.len()).unwrap_or(u8::MAX));
    body.extend_from_slice(session_id);
    body.extend_from_slice(&0x1303u16.to_be_bytes());
    body.push(0);
    body.extend_from_slice(
        &u16::try_from(encoded_extensions.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    body.extend_from_slice(&encoded_extensions);
    body
}

fn supported_versions() -> [u8; 2] {
    [3, 4]
}

fn server_key_share(key: &[u8]) -> Vec<u8> {
    let mut data = Vec::new();
    data.extend_from_slice(&29u16.to_be_bytes());
    data.extend_from_slice(&u16::try_from(key.len()).unwrap_or(u16::MAX).to_be_bytes());
    data.extend_from_slice(key);
    data
}

fn final_server_hello(session_id: &[u8]) -> Vec<u8> {
    let version = supported_versions();
    let key = server_key_share(&SERVER_KEY);
    server_hello(&[0x44; 32], session_id, &[(43, &version), (51, &key)])
}

fn retry_server_hello(session_id: &[u8], cookie: &[u8]) -> Vec<u8> {
    let version = supported_versions();
    server_hello(&HRR_RANDOM, session_id, &[(43, &version), (44, cookie)])
}

fn cookie_extension_data(cookie: &[u8]) -> Vec<u8> {
    let mut data = Vec::new();
    data.extend_from_slice(
        &u16::try_from(cookie.len())
            .unwrap_or(u16::MAX)
            .to_be_bytes(),
    );
    data.extend_from_slice(cookie);
    data
}

fn assert_same_client_hello_fields(first: &ClientHello<'_>, second: &ClientHello<'_>) {
    assert_eq!(second.legacy_version, first.legacy_version);
    assert_eq!(second.random, first.random);
    assert_eq!(second.session_id, first.session_id);
    assert_eq!(second.cipher_suites, first.cipher_suites);
    assert_eq!(second.compression, first.compression);
    for kind in [0, 43, 13, 10, 51] {
        assert_eq!(extension_data(second, kind), extension_data(first, kind));
    }
}

#[test]
fn start_emits_the_fixed_client_profile_and_respects_sni_choice() -> Result<(), String> {
    let (_, flight) = Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let hello = client_hello(&flight)?;
    assert_eq!(hello.legacy_version, 0x0303);
    assert_eq!(hello.random, RANDOM);
    assert_eq!(hello.session_id, SESSION_ID);
    assert_eq!(hello.cipher_suites, vec![0x1303]);
    assert_eq!(hello.compression, [0]);
    assert_eq!(
        hello
            .extensions
            .iter()
            .map(|extension| extension.etype)
            .collect::<Vec<_>>(),
        vec![0, 43, 13, 10, 51]
    );
    assert_eq!(
        extension_data(&hello, 0),
        Some(expected_sni(HOST).as_slice())
    );
    assert_eq!(extension_data(&hello, 43), Some(&[2, 3, 4][..]));
    assert_eq!(
        extension_data(&hello, 13),
        Some(expected_signatures().as_slice())
    );
    assert_eq!(extension_data(&hello, 10), Some(&[0, 2, 0, 29][..]));
    assert_eq!(
        extension_data(&hello, 51),
        Some(expected_client_key_share(&PUBLIC_KEY).as_slice())
    );
    assert_eq!(extension_data(&hello, 44), None);

    let mut ip_config = config();
    ip_config.host = b"192.0.2.10".to_vec();
    ip_config.send_sni = false;
    let (_, flight) = Hello::start(ip_config).map_err(|alert| format!("IP start alert {alert}"))?;
    let hello = client_hello(&flight)?;
    assert_eq!(extension_data(&hello, 0), None);
    assert_eq!(hello.session_id, SESSION_ID);
    Ok(())
}

#[test]
fn accepts_profile_bounds_and_rejects_invalid_configuration() -> Result<(), String> {
    let mut maximal = config();
    maximal.host = vec![b'h'; 253];
    maximal.session_id = vec![0x77; 32];
    let (_, flight) =
        Hello::start(maximal).map_err(|alert| format!("maximum config alert {alert}"))?;
    let hello = client_hello(&flight)?;
    assert_eq!(hello.session_id.len(), 32);

    let mut invalid = config();
    invalid.host.clear();
    assert!(matches!(Hello::start(invalid), Err(INTERNAL_ERROR)));
    let mut invalid = config();
    invalid.host = vec![b'h'; 254];
    assert!(matches!(Hello::start(invalid), Err(INTERNAL_ERROR)));
    let mut invalid = config();
    invalid.random.pop();
    assert!(matches!(Hello::start(invalid), Err(INTERNAL_ERROR)));
    let mut invalid = config();
    invalid.session_id = vec![0; 32];
    invalid.session_id.push(0);
    assert!(matches!(Hello::start(invalid), Err(INTERNAL_ERROR)));
    let mut invalid = config();
    invalid.public_key.pop();
    assert!(matches!(Hello::start(invalid), Err(INTERNAL_ERROR)));
    Ok(())
}

#[test]
fn cookie_retry_echoes_cookie_and_preserves_client_hello_offers() -> Result<(), String> {
    let crypto = TestCrypto;
    let original_config = config();
    let (hello, first_flight) =
        Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let first = client_hello(&first_flight)?;
    let cookie = b"opaque cookie";
    let raw_cookie = cookie_extension_data(cookie);
    let hrr = retry_server_hello(&original_config.session_id, &raw_cookie);
    let (hello, second_flight) = match hello
        .receive(&crypto, &hrr)
        .map_err(|alert| format!("first retry rejected with {alert}"))?
    {
        Outcome::Retry(hello, flight) => (hello, flight),
        Outcome::Established(_) => return Err("HRR established the connection".to_owned()),
    };
    let second = client_hello(&second_flight)?;
    assert_same_client_hello_fields(&first, &second);
    assert_eq!(extension_data(&second, 44), Some(raw_cookie.as_slice()));
    assert_ne!(first_flight, second_flight);

    let server = final_server_hello(&original_config.session_id);
    let established = match hello
        .receive(&crypto, &server)
        .map_err(|alert| format!("final ServerHello rejected with {alert}"))?
    {
        Outcome::Established(established) => established,
        Outcome::Retry(_, _) => return Err("final ServerHello requested a retry".to_owned()),
    };
    assert_established_prefix(
        established,
        &crypto,
        &original_config,
        &first_flight,
        &hrr,
        &second_flight,
        &server,
    )?;
    Ok(())
}

fn assert_established_prefix(
    established: Established,
    crypto: &TestCrypto,
    original_config: &Config,
    first_flight: &[u8],
    hrr_body: &[u8],
    second_flight: &[u8],
    server_body: &[u8],
) -> Result<(), String> {
    let (captured, transcript, peer_key) = established.into_parts();
    assert_eq!(captured.host, original_config.host);
    assert_eq!(captured.now, original_config.now);
    assert_eq!(captured.random, original_config.random);
    assert_eq!(captured.session_id, original_config.session_id);
    assert_eq!(captured.public_key, original_config.public_key);
    assert_eq!(captured.send_sni, original_config.send_sni);
    assert_eq!(peer_key, SERVER_KEY);
    let initial_hash = crypto.hash(first_flight);
    let mut expected_messages = handshake_message(254, &initial_hash);
    expected_messages.extend_from_slice(&handshake_message(2, hrr_body));
    expected_messages.extend_from_slice(second_flight);
    expected_messages.extend_from_slice(&handshake_message(2, server_body));
    assert_eq!(transcript.messages(), expected_messages);
    Ok(())
}

#[test]
fn rejects_wrong_session_echo_repeated_retry_and_oversized_cookie() -> Result<(), String> {
    let crypto = TestCrypto;
    let (hello, _) = Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let wrong_echo = final_server_hello(b"wrong session");
    assert!(matches!(
        hello.receive(&crypto, &wrong_echo),
        Err(ILLEGAL_PARAMETER)
    ));

    let (hello, _) = Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let raw_cookie = cookie_extension_data(b"cookie");
    let hrr = retry_server_hello(SESSION_ID, &raw_cookie);
    let hello = match hello.receive(&crypto, &hrr) {
        Ok(Outcome::Retry(hello, _)) => hello,
        _ => return Err("first HRR should produce a retry controller".to_owned()),
    };
    assert!(matches!(
        hello.receive(&crypto, &hrr),
        Err(UNEXPECTED_MESSAGE)
    ));

    let (hello, _) = Hello::start(config()).map_err(|alert| format!("start alert {alert}"))?;
    let over_limit = vec![0x5a; 4097];
    let raw_cookie = cookie_extension_data(&over_limit);
    let hrr = retry_server_hello(SESSION_ID, &raw_cookie);
    assert!(matches!(hello.receive(&crypto, &hrr), Err(INTERNAL_ERROR)));
    Ok(())
}

fn expected_sni(host: &[u8]) -> Vec<u8> {
    let name_length = u16::try_from(host.len()).unwrap_or(u16::MAX);
    let list_length = name_length.saturating_add(3);
    let mut data = Vec::new();
    data.extend_from_slice(&list_length.to_be_bytes());
    data.push(0);
    data.extend_from_slice(&name_length.to_be_bytes());
    data.extend_from_slice(host);
    data
}

fn expected_signatures() -> Vec<u8> {
    let schemes = [
        0x0403u16, 0x0804, 0x0805, 0x0806, 0x0807, 0x0401, 0x0501, 0x0601,
    ];
    let mut data = Vec::new();
    data.extend_from_slice(&16u16.to_be_bytes());
    for scheme in schemes {
        data.extend_from_slice(&scheme.to_be_bytes());
    }
    data
}

fn expected_client_key_share(key: &[u8]) -> Vec<u8> {
    let key_length = u16::try_from(key.len()).unwrap_or(u16::MAX);
    let entry_length = key_length.saturating_add(4);
    let mut data = Vec::new();
    data.extend_from_slice(&entry_length.to_be_bytes());
    data.extend_from_slice(&29u16.to_be_bytes());
    data.extend_from_slice(&key_length.to_be_bytes());
    data.extend_from_slice(key);
    data
}
