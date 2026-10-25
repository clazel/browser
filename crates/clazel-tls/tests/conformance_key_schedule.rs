//! RFC 8448 §3 and §5 through the proven key-schedule implementation.
//! The test-only reference provider uses RustCrypto SHA-256 and RFC 5869
//! §2.2/§2.3 plus RFC 2104 §2 for HKDF/HMAC. It is checked against RFC 5869
//! Appendix A.1 before the TLS vectors. It is neither shipped nor proven.
//! These are key-schedule tests, not tests of the future handshake machine.

mod key_schedule_vectors;

use clazel_tls::schedule::crypto::Crypto;
use clazel_tls::schedule::exec::{
    derive_secret, early_secret, expand_label, finished, handshake_secret, hkdf_label,
    master_secret, update_secret, write_iv, write_key,
};
use clazel_tls::schedule::spec::Label;
use sha2::{Digest, Sha256};

struct Reference;

impl Crypto for Reference {
    fn hash(&self, messages: &[u8]) -> Vec<u8> {
        Sha256::digest(messages).to_vec()
    }

    // RFC 5869 §2.2, PRK = HMAC-Hash(salt, IKM).
    fn extract(&self, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        self.hmac(salt, ikm)
    }

    // RFC 5869 §2.3, T(0) empty; T(i) = HMAC(PRK, T(i-1)|info|i).
    fn expand(&self, secret: &[u8], info: &[u8], length: u16) -> Vec<u8> {
        let mut out = Vec::new();
        let mut previous = Vec::new();
        for counter in 1..=u8::MAX {
            if out.len() >= usize::from(length) {
                break;
            }
            let mut message = previous;
            message.extend_from_slice(info);
            message.push(counter);
            previous = self.hmac(secret, &message);
            out.extend_from_slice(&previous);
        }
        out.truncate(usize::from(length));
        out
    }

    // RFC 2104 §2, SHA-256's block size is 64 octets.
    fn hmac(&self, key: &[u8], message: &[u8]) -> Vec<u8> {
        let key = if key.len() > 64 {
            self.hash(key)
        } else {
            key.to_vec()
        };
        let mut padded = key;
        padded.resize(64, 0);
        let inner_pad: Vec<u8> = padded.iter().map(|b| b ^ 0x36).collect();
        let outer_pad: Vec<u8> = padded.iter().map(|b| b ^ 0x5c).collect();
        let mut inner = Sha256::new();
        inner.update(inner_pad);
        inner.update(message);
        let mut outer = Sha256::new();
        outer.update(outer_pad);
        outer.update(inner.finalize());
        outer.finalize().to_vec()
    }
}

fn hex(s: &str) -> Result<Vec<u8>, String> {
    s.split_whitespace()
        .map(|b| u8::from_str_radix(b, 16).map_err(|e| format!("invalid fixture: {e}")))
        .collect()
}

#[test]
fn reference_provider_matches_rfc5869_appendix_a1() -> Result<(), String> {
    let reference = Reference;
    let ikm = vec![0x0b; 22];
    let salt = hex("00 01 02 03 04 05 06 07 08 09 0a 0b 0c")?;
    let info = hex("f0 f1 f2 f3 f4 f5 f6 f7 f8 f9")?;
    let prk = reference.extract(&salt, &ikm);
    let expected_prk = hex(
        "07 77 09 36 2c 2e 32 df 0d dc 3f 0d c4 7b ba 63 90 b6 c7 3b b5 0f 9c 31 22 ec 84 4a d7 c2 b3 e5",
    )?;
    let expected_okm = hex(
        "3c b2 5f 25 fa ac d5 7a 90 43 4f 64 d0 36 2f 2a 2d 2d 0a 90 cf 1a 5a 4c 5d b0 2d 56 ec c4 c5 bf 34 00 72 08 d5 b8 87 18 58 65",
    )?;
    let passed = prk == expected_prk && reference.expand(&prk, &info, 42) == expected_okm;
    println!(
        "clazel-conformance: suite=\"RFC 5869 Appendix A.1 reference provider\" pass={} xfail=0 fail={} total=1",
        usize::from(passed),
        usize::from(!passed)
    );
    assert!(passed);
    Ok(())
}

fn label(s: &str) -> Result<Label, String> {
    Ok(match s {
        "derived" => Label::Derived,
        "c hs traffic" => Label::ClientHandshake,
        "s hs traffic" => Label::ServerHandshake,
        "c ap traffic" => Label::ClientApplication,
        "s ap traffic" => Label::ServerApplication,
        "finished" => Label::Finished,
        "key" => Label::Key,
        "iv" => Label::Iv,
        _ => return Err(format!("unknown fixture label {s}")),
    })
}

#[test]
fn rfc8448_key_schedule() -> Result<(), String> {
    let crypto = Reference;
    let mut early = Vec::new();
    let mut handshake = Vec::new();
    let mut pass = 0usize;
    for v in key_schedule_vectors::VECTORS {
        let secret = hex(v.secret)?;
        let context = hex(v.context)?;
        let expected = hex(v.output)?;
        let messages = hex(v.messages)?;
        let passed = match v.kind {
            "early" => {
                early = early_secret(&crypto);
                early == expected
            }
            "handshake" => {
                handshake = handshake_secret(&crypto, &early, &context);
                handshake == expected
            }
            "master" => master_secret(&crypto, &handshake) == expected,
            "expand" => {
                let label = label(v.label)?;
                let length = u16::try_from(expected.len())
                    .map_err(|e| format!("invalid fixture length: {e}"))?;
                let info_ok = hkdf_label(v.label.as_bytes(), &context, length) == hex(v.info)?;
                let expansion_ok =
                    expand_label(&crypto, &secret, label, &context, length) == expected;
                let derivation_ok = match label {
                    Label::Derived
                    | Label::ClientHandshake
                    | Label::ServerHandshake
                    | Label::ClientApplication
                    | Label::ServerApplication => {
                        derive_secret(&crypto, &secret, label, &messages) == expected
                    }
                    Label::Finished => finished(&crypto, &secret, &messages) == hex(v.finished)?,
                    Label::Iv => write_iv(&crypto, &secret) == expected,
                    _ => true,
                };
                info_ok && expansion_ok && derivation_ok
            }
            _ => false,
        };
        if passed {
            pass = pass.saturating_add(1);
        } else {
            eprintln!(
                "RFC 8448 section {} line {}: {} {} failed",
                v.section, v.line, v.kind, v.label
            );
        }
    }
    let total = key_schedule_vectors::VECTORS.len();
    println!(
        "clazel-conformance: suite=\"RFC 8448 key schedule sections 3 and 5\" pass={pass} xfail=0 fail={} total={total}",
        total.saturating_sub(pass)
    );
    assert_eq!(pass, total);
    Ok(())
}

#[test]
fn chacha_key_and_updates_use_the_right_labels_and_lengths() -> Result<(), String> {
    let crypto = Reference;
    let secret = [0x42; 32];
    // A separately encoded HKDF info field, as RFC 8446 §7.2/§7.3 spells it.
    let key_info = hex("00 20 09 74 6c 73 31 33 20 6b 65 79 00")?;
    let update_info = hex("00 20 11 74 6c 73 31 33 20 74 72 61 66 66 69 63 20 75 70 64 00")?;
    assert_eq!(
        write_key(&crypto, &secret),
        crypto.expand(&secret, &key_info, 32)
    );
    let next = update_secret(&crypto, &secret);
    assert_eq!(next, crypto.expand(&secret, &update_info, 32));
    assert_ne!(write_key(&crypto, &secret), write_key(&crypto, &next));
    Ok(())
}

#[test]
fn transcript_accumulator_matches_rfc8448() -> Result<(), String> {
    use clazel_tls::transcript::exec::Transcript;
    use clazel_tls::transcript::spec::Kind;
    let crypto = Reference;
    let mut pass = 0usize;
    let mut total = 0usize;
    for section in [3, 5] {
        let mut messages = key_schedule_vectors::TRANSCRIPT_MESSAGES
            .iter()
            .filter(|m| m.section == section)
            .peekable();
        let mut transcript: Option<Transcript> = None;
        for v in key_schedule_vectors::VECTORS
            .iter()
            .filter(|v| v.section == section)
        {
            while messages.peek().is_some_and(|m| m.line < v.line) {
                let m = messages.next().ok_or("missing transcript message")?;
                let bytes = hex(m.hex)?;
                let body = bytes.get(4..).ok_or("missing handshake header")?;
                match &mut transcript {
                    None => {
                        assert_eq!(m.kind, Kind::ClientHello);
                        transcript = Some(Transcript::new(body).map_err(|e| format!("{e:?}"))?);
                    }
                    Some(t) => t
                        .push(&crypto, m.kind, body)
                        .map_err(|e| format!("{e:?}"))?,
                }
            }
            if v.kind != "expand"
                || !matches!(
                    label(v.label)?,
                    Label::ClientHandshake
                        | Label::ServerHandshake
                        | Label::ClientApplication
                        | Label::ServerApplication
                        | Label::Finished
                )
            {
                continue;
            }
            total = total.saturating_add(1);
            let t = transcript.as_ref().ok_or("missing transcript")?;
            let expected_messages = hex(v.messages)?;
            let checked_value = if v.label == "finished" {
                finished(&crypto, &hex(v.secret)?, t.messages()) == hex(v.finished)?
            } else {
                t.hash(&crypto) == hex(v.context)?
            };
            let passed = t.messages() == expected_messages && checked_value;
            if passed {
                pass = pass.saturating_add(1);
            } else {
                eprintln!("transcript section {section} line {}: {}", v.line, v.label);
            }
            assert_eq!(t.retried(), section == 5);
        }
    }
    // Independently count the checks in the source table, not the successful loop iterations.
    let expected_total = key_schedule_vectors::VECTORS
        .iter()
        .filter(|v| {
            v.kind == "expand"
                && matches!(
                    v.label,
                    "c hs traffic" | "s hs traffic" | "c ap traffic" | "s ap traffic" | "finished"
                )
        })
        .count();
    println!(
        "clazel-conformance: suite=\"RFC 8448 live transcripts sections 3 and 5\" pass={pass} xfail=0 fail={} total={expected_total}",
        expected_total.saturating_sub(pass)
    );
    assert_eq!(total, expected_total);
    assert_eq!(pass, expected_total);
    Ok(())
}

#[test]
fn certificate_verify_input_matches_rfc8446_section_4_4_3() -> Result<(), String> {
    use clazel_tls::transcript::exec::certificate_verify_input;
    // The RFC's explicit example: SHA-256 transcript hash of 32 octets of 01.
    let server = certificate_verify_input(true, &[1; 32]);
    let mut expected = vec![0x20; 64];
    expected.extend_from_slice(&hex("54 4c 53 20 31 2e 33 2c 20 73 65 72 76 65 72 20 43 65 72 74 69 66 69 63 61 74 65 56 65 72 69 66 79")?);
    expected.push(0);
    expected.extend_from_slice(&[1; 32]);
    let passed = server == expected;
    println!(
        "clazel-conformance: suite=\"RFC 8446 section 4.4.3 signature input example\" pass={} xfail=0 fail={} total=1",
        usize::from(passed),
        usize::from(!passed)
    );
    assert!(passed);
    let client = certificate_verify_input(false, &[1; 32]);
    assert_eq!(client.len(), 130);
    assert_ne!(client, server);
    Ok(())
}

#[test]
fn transcript_rejects_bad_hello_order_and_preserves_state() -> Result<(), String> {
    use clazel_tls::transcript::exec::Transcript;
    use clazel_tls::transcript::spec::{Error, Kind, MAX_BODY};
    let crypto = Reference;
    let mut t = Transcript::new(&[1]).map_err(|e| format!("{e:?}"))?;
    let initial = t.messages().to_vec();
    assert_eq!(
        t.push(&crypto, Kind::Finished, &[2]),
        Err(Error::UnexpectedMessage)
    );
    assert_eq!(t.messages(), initial);
    t.push(&crypto, Kind::HelloRetryRequest, &[2])
        .map_err(|e| format!("{e:?}"))?;
    for next in [None, Some(Kind::ClientHello), Some(Kind::ServerHello)] {
        if let Some(k) = next {
            t.push(&crypto, k, &[3]).map_err(|e| format!("{e:?}"))?;
        }
        let before = t.messages().to_vec();
        let phase = t.phase();
        assert_eq!(
            t.push(&crypto, Kind::HelloRetryRequest, &[2]),
            Err(Error::UnexpectedMessage)
        );
        assert_eq!(t.messages(), before);
        assert_eq!(t.phase(), phase);
        assert!(t.retried());
    }
    let before = t.messages().to_vec();
    let oversized = vec![0; MAX_BODY.saturating_add(1)];
    assert!(matches!(Transcript::new(&oversized), Err(Error::TooLarge)));
    assert_eq!(
        t.push(&crypto, Kind::Certificate, &oversized),
        Err(Error::TooLarge)
    );
    assert_eq!(t.messages(), before);
    Ok(())
}

#[test]
fn transcript_capacity_is_inclusive_and_failure_keeps_the_transcript() -> Result<(), String> {
    use clazel_tls::transcript::exec::Transcript;
    use clazel_tls::transcript::spec::{Error, Kind, MAX_BODY, MAX_TRANSCRIPT};
    let crypto = Reference;
    let mut t = Transcript::new(&[7]).map_err(|e| format!("{e:?}"))?;
    t.push(&crypto, Kind::ServerHello, &[8])
        .map_err(|e| format!("{e:?}"))?;
    let body = vec![0x42; MAX_BODY];
    while t.messages().len() < MAX_TRANSCRIPT {
        let remaining = MAX_TRANSCRIPT.saturating_sub(t.messages().len());
        assert!(remaining >= 4);
        let body_len = remaining.saturating_sub(4).min(MAX_BODY);
        let chunk = body.get(..body_len).ok_or("invalid test chunk")?;
        t.push(&crypto, Kind::Certificate, chunk)
            .map_err(|e| format!("{e:?}"))?;
    }
    assert_eq!(t.messages().len(), MAX_TRANSCRIPT);
    let before = t.messages().to_vec();
    assert_eq!(t.push(&crypto, Kind::Finished, &[]), Err(Error::TooLarge));
    assert_eq!(t.messages(), before);
    assert!(!t.retried());
    Ok(())
}
