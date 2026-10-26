//! TLS 1.3 record layer and handshake message conformance (phase-3.md item
//! 3.5d).
//!
//! The proofs show the executable code equals `src/spec.rs`. This file
//! checks the spec against the outside world, always through the proven
//! code:
//!
//! 1. Every handshake message of RFC 8448 sections 3 to 7 is read and then
//!    written again, byte for byte, and each message's extensions are read
//!    as their types say (`tests/rfc8448/mod.rs` holds the vectors).
//! 2. Every record of those sections is read off the wire and written again;
//!    an encrypted record's header is the additional data of RFC 8446
//!    section 5.2, its decrypted inner plaintext (the RFC gives the content)
//!    is read by the padding scan, and every proper prefix of a record is
//!    "need more". A toy AEAD (not a cipher) stands in for ChaCha20-Poly1305
//!    to run `encrypt_record` and `decrypt_record` on the same content.
//! 3. The handshake payloads of those records are fed to the reassembler
//!    whole and split into fragments of several sizes.
//! 4. Hand-built cases, one or more per error rule of RFC 8446 sections 5
//!    and 6, each with the alert section 6.2 names.
//! 5. A differential test against rustls's message codec.

mod rfc8448;

use clazel_tls::encode::{
    alert_for, push_extensions, read_alert, write_alert, write_certificate,
    write_certificate_request, write_certificate_verify, write_client_hello,
    write_encrypted_extensions, write_handshake, write_key_update, write_new_session_ticket,
    write_server_hello,
};
use clazel_tls::extension::{
    cookie, key_share_ch, key_share_hrr, key_share_sh, named_groups, read_exts, server_name_ch,
    signature_schemes, supported_versions_ch, supported_versions_sh,
};
use clazel_tls::handshake::{
    is_hello_retry_request, parse_handshake, read_certificate, read_certificate_request,
    read_client_hello, read_encrypted_extensions, read_new_session_ticket, read_server_hello,
};
use clazel_tls::reader::Cur;
use clazel_tls::reassemble::{Event, Reassembler};
use clazel_tls::record::{
    Aead, Frame, ReadOut, additional_data, decrypt_record, encrypt_record, open_inner_plaintext,
    per_record_nonce, read_record, write_plaintext,
};
use clazel_tls::spec::{Alert, ErrKind, MAX_HANDSHAKE_BODY};
use clazel_tls::types::{Extension, HsMsg};
use rfc8448::{MESSAGES, RECORDS};

/// The hash of the only cipher suite of this client.
const HASH_LEN: usize = 32;

fn hex(s: &str) -> Vec<u8> {
    s.split_whitespace()
        .filter_map(|b| u8::from_str_radix(b, 16).ok())
        .collect()
}

/// A message's bytes: type, three-byte length, body.
fn wrapped(t: u8, body: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    write_handshake(&mut out, t, body);
    out
}

/// Write a parsed message again.
fn reencode(m: &HsMsg<'_>) -> Vec<u8> {
    let mut body = Vec::new();
    match m {
        HsMsg::ClientHello(ch) => {
            write_client_hello(&mut body, ch);
            wrapped(1, &body)
        }
        HsMsg::ServerHello(sh) => {
            write_server_hello(&mut body, sh);
            wrapped(2, &body)
        }
        HsMsg::NewSessionTicket(n) => {
            write_new_session_ticket(&mut body, n);
            wrapped(4, &body)
        }
        HsMsg::EndOfEarlyData => wrapped(5, &body),
        HsMsg::EncryptedExtensions(es) => {
            write_encrypted_extensions(&mut body, es);
            wrapped(8, &body)
        }
        HsMsg::Certificate(c) => {
            write_certificate(&mut body, c);
            wrapped(11, &body)
        }
        HsMsg::CertificateRequest(c) => {
            write_certificate_request(&mut body, c);
            wrapped(13, &body)
        }
        HsMsg::CertificateVerify(c) => {
            write_certificate_verify(&mut body, c);
            wrapped(15, &body)
        }
        HsMsg::Finished(v) => wrapped(20, v),
        HsMsg::KeyUpdate(r) => {
            write_key_update(&mut body, *r);
            wrapped(24, &body)
        }
    }
}

/// The RFC's name for a parsed message.
fn name_of(m: &HsMsg<'_>) -> &'static str {
    match m {
        HsMsg::ClientHello(_) => "ClientHello",
        HsMsg::ServerHello(_) => "ServerHello",
        HsMsg::NewSessionTicket(_) => "NewSessionTicket",
        HsMsg::EndOfEarlyData => "EndOfEarlyData",
        HsMsg::EncryptedExtensions(_) => "EncryptedExtensions",
        HsMsg::Certificate(_) => "Certificate",
        HsMsg::CertificateRequest(_) => "CertificateRequest",
        HsMsg::CertificateVerify(_) => "CertificateVerify",
        HsMsg::Finished(_) => "Finished",
        HsMsg::KeyUpdate(_) => "KeyUpdate",
    }
}

fn ext_data<'a>(es: &'a [Extension<'a>], t: u16) -> Option<&'a [u8]> {
    es.iter().find(|e| e.etype == t).map(|e| e.data)
}

/// The extensions of a message read as their types say: the typed readers
/// accept the data of every extension this crate reads.
fn typed_extensions(m: &HsMsg<'_>, is_hrr: bool) -> Result<(), String> {
    let need = |what: &str, ok: bool| {
        if ok {
            Ok(())
        } else {
            Err(format!("typed read of {what} failed"))
        }
    };
    match m {
        HsMsg::ClientHello(ch) => {
            let es = ch.extensions.as_slice();
            if let Some(d) = ext_data(es, 43) {
                need(
                    "supported_versions",
                    supported_versions_ch(d).is_some_and(|v| v.contains(&0x0304)),
                )?;
            }
            if let Some(d) = ext_data(es, 10) {
                need("supported_groups", named_groups(d).is_some())?;
            }
            if let Some(d) = ext_data(es, 13) {
                need("signature_algorithms", signature_schemes(d).is_some())?;
            }
            if let Some(d) = ext_data(es, 50) {
                need("signature_algorithms_cert", signature_schemes(d).is_some())?;
            }
            if let Some(d) = ext_data(es, 51) {
                need("key_share", key_share_ch(d).is_some())?;
            }
            if let Some(d) = ext_data(es, 0) {
                need("server_name", server_name_ch(d).is_some())?;
            }
            if let Some(d) = ext_data(es, 44) {
                need("cookie", cookie(d).is_some())?;
            }
            Ok(())
        }
        HsMsg::ServerHello(sh) => {
            let es = sh.extensions.as_slice();
            let d = ext_data(es, 43).ok_or("no supported_versions")?;
            need(
                "supported_versions",
                supported_versions_sh(d) == Some(0x0304),
            )?;
            if let Some(d) = ext_data(es, 51) {
                if is_hrr {
                    need("key_share (HRR)", key_share_hrr(d).is_some())?;
                } else {
                    need("key_share (SH)", key_share_sh(d).is_some())?;
                }
            }
            if let Some(d) = ext_data(es, 44) {
                need("cookie", is_hrr && cookie(d).is_some())?;
            }
            Ok(())
        }
        HsMsg::CertificateRequest(c) => {
            let d = ext_data(c.extensions.as_slice(), 13).ok_or("no signature_algorithms")?;
            need("signature_algorithms", signature_schemes(d).is_some())
        }
        _ => Ok(()),
    }
}

/// The checks on one RFC 8448 message: read, written again, named as the
/// RFC names it, its extensions read as their types say, and a
/// HelloRetryRequest recognised exactly where RFC 8448 section 5 has one.
fn check_message(v: &rfc8448::Message) -> Result<(), String> {
    let bytes = hex(v.hex);
    let m = parse_handshake(&bytes, HASH_LEN).map_err(|e| format!("rejected: {e:?}"))?;
    if name_of(&m) != v.name {
        return Err(format!("read as {}", name_of(&m)));
    }
    let again = reencode(&m);
    if again != bytes {
        return Err("does not write back to the same bytes".to_owned());
    }
    let hrr = match &m {
        HsMsg::ServerHello(sh) => is_hello_retry_request(sh),
        _ => false,
    };
    // Section 5's first ServerHello (line 1656) is the HelloRetryRequest.
    let expect_hrr = v.section == 5 && v.line == 1656;
    if matches!(m, HsMsg::ServerHello(_)) && hrr != expect_hrr {
        return Err(format!("HelloRetryRequest recognised as {hrr}"));
    }
    typed_extensions(&m, hrr)
}

/// RFC 8448 section 4, line 886: the 0-RTT ClientHello as the RFC shows it
/// before the PSK binders are computed. Its length field (0x01fc) is already
/// the final one, so these 477 octets are a prefix of the 512-octet message at
/// line 972 (the record payload), not a message: the length does not match
/// and the reader must refuse it with `decode_error`. Expected failure, with
/// the reason checked below.
const PREFIX_LINE: u32 = 886;

/// The line of the complete message that [`PREFIX_LINE`] is a prefix of.
const PREFIX_OF_PAYLOAD_LINE: u32 = 972;

/// Whether `v` is the expected failure: it is rejected as `decode_error` and is
/// a proper prefix of the payload at line 972.
fn is_expected_prefix(v: &rfc8448::Message) -> bool {
    if v.line != PREFIX_LINE {
        return false;
    }
    let bytes = hex(v.hex);
    let full = RECORDS
        .iter()
        .find(|r| r.payload_line == PREFIX_OF_PAYLOAD_LINE)
        .map(|r| hex(r.payload));
    parse_handshake(&bytes, HASH_LEN).err() == Some(ErrKind::Decode)
        && full.is_some_and(|f| f.len() > bytes.len() && f.starts_with(&bytes))
}

#[test]
fn rfc8448_messages() {
    let mut failures = Vec::new();
    let mut failed = 0usize;
    let mut xfail = 0usize;
    for v in MESSAGES {
        match check_message(v) {
            Ok(()) => {}
            Err(_) if is_expected_prefix(v) => xfail = xfail.saturating_add(1),
            Err(why) => {
                failed = failed.saturating_add(1);
                failures.push(format!(
                    "RFC 8448 section {} line {} ({} {}): {why}",
                    v.section, v.line, v.actor, v.name
                ));
            }
        }
    }
    // Summary line for the README table; format in xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"RFC 8448 handshake messages (sections 3 to 7)\" pass={} xfail={xfail} fail={failed} total={}",
        MESSAGES.len().saturating_sub(failed).saturating_sub(xfail),
        MESSAGES.len()
    );
    assert_eq!(
        MESSAGES.len(),
        40,
        "RFC 8448 sections 3 to 7 hold 40 handshake messages"
    );
    assert_eq!(xfail, 1, "exactly one message is a prefix (line 886)");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A stand-in for an AEAD: not a cipher. The keystream is a function of
/// the nonce, and the tag of the additional data, the nonce and the
/// plaintext, so a wrong nonce, header or byte fails to open. It exists to
/// run the generic record functions on real record contents.
struct ToyAead;

impl ToyAead {
    fn stream(nonce: &[u8], i: usize) -> u8 {
        let mut h: u8 = 0x5a;
        for n in nonce {
            h = h.wrapping_mul(31).wrapping_add(*n);
        }
        h.wrapping_add(u8::try_from(i % 251).unwrap_or(0))
    }

    fn tag(nonce: &[u8], ad: &[u8], pt: &[u8]) -> Vec<u8> {
        let mut state: [u8; 16] = [7; 16];
        for (k, b) in nonce.iter().chain(ad).chain(pt).enumerate() {
            let slot = k % 16;
            if let Some(s) = state.get_mut(slot) {
                *s = s.wrapping_mul(33).wrapping_add(*b).rotate_left(3);
            }
        }
        state.to_vec()
    }
}

impl Aead for ToyAead {
    fn tag_len(&self) -> usize {
        16
    }

    fn nonce_len(&self) -> usize {
        12
    }

    fn seal(&self, nonce: &[u8], ad: &[u8], plaintext: &[u8]) -> Vec<u8> {
        let mut out: Vec<u8> = plaintext
            .iter()
            .enumerate()
            .map(|(i, b)| b ^ Self::stream(nonce, i))
            .collect();
        out.extend(Self::tag(nonce, ad, plaintext));
        out
    }

    fn open(&self, nonce: &[u8], ad: &[u8], ciphertext: &[u8]) -> Option<Vec<u8>> {
        let split = ciphertext.len().checked_sub(16)?;
        let (body, tag) = ciphertext.split_at(split);
        let pt: Vec<u8> = body
            .iter()
            .enumerate()
            .map(|(i, b)| b ^ Self::stream(nonce, i))
            .collect();
        if Self::tag(nonce, ad, &pt) == tag {
            Some(pt)
        } else {
            None
        }
    }
}

const IV: [u8; 12] = [
    0xA5, 0x1B, 0x2C, 0x3D, 0x4E, 0x5F, 0x60, 0x71, 0x82, 0x93, 0xA4, 0xB5,
];

/// The content type that goes inside a record, from the RFC's step.
fn inner_type(step: &str) -> Option<u8> {
    if step.contains("handshake") {
        Some(22)
    } else if step.contains("alert") {
        Some(21)
    } else if step.contains("application_data") {
        Some(23)
    } else {
        None
    }
}

fn check_record(r: &rfc8448::Record) -> Result<(), String> {
    let bytes = hex(r.record);
    let payload = hex(r.payload);
    let protected = bytes.first() == Some(&0x17);
    let (frame, rest) = match read_record(&bytes, protected) {
        ReadOut::Done(f, rest) => (f, rest),
        other => return Err(format!("not read: {other:?}")),
    };
    if !rest.is_empty() {
        return Err("bytes left after the record".to_owned());
    }
    let version = u16::from_be_bytes([
        bytes.get(1).copied().unwrap_or(0),
        bytes.get(2).copied().unwrap_or(0),
    ]);
    match frame {
        Frame::Plain(t, frag) => {
            if frag != payload.as_slice() || Some(t) != inner_type(r.step) {
                return Err("fragment is not the RFC's payload".to_owned());
            }
            let mut again = Vec::new();
            write_plaintext(&mut again, t, version, frag);
            if again != bytes {
                return Err("does not write back to the same bytes".to_owned());
            }
        }
        Frame::Ccs => {
            if payload != [1u8] || bytes != [0x14, 3, 3, 0, 1, 1] {
                return Err("change_cipher_spec is not 01".to_owned());
            }
            let mut st = Reassembler::new();
            if !matches!(st.feed_ccs(), Ok(Event::Ignored)) {
                return Err("change_cipher_spec not dropped".to_owned());
            }
        }
        Frame::Protected(h, body) => {
            if !protected || h != additional_data(body.len()).as_slice() {
                return Err("header is not the additional data".to_owned());
            }
            let mut again = h.to_vec();
            again.extend_from_slice(body);
            if again != bytes {
                return Err("does not write back to the same bytes".to_owned());
            }
            let ct = inner_type(r.step).ok_or("unknown step")?;
            // The RFC gives the decrypted content; the inner plaintext is
            // that and the content type, plus any padding.
            for padding in [0usize, 1, 17] {
                let mut inner = payload.clone();
                inner.push(ct);
                inner.extend(std::iter::repeat_n(0u8, padding));
                match open_inner_plaintext(inner) {
                    Ok((t, content)) if t == ct && content == payload => {}
                    other => {
                        return Err(format!("inner plaintext with padding {padding}: {other:?}"));
                    }
                }
            }
            // Protect the same content with the toy AEAD and read it back.
            let aead = ToyAead;
            for (seq, padding) in [(0u64, 0usize), (1, 5), (u64::MAX, 0)] {
                let rec = encrypt_record(&aead, &IV, seq, ct, &payload, padding);
                let (hdr, body) = match read_record(&rec, true) {
                    ReadOut::Done(Frame::Protected(h, b), []) => (h, b),
                    other => return Err(format!("protected record not read back: {other:?}")),
                };
                match decrypt_record(&aead, &IV, seq, hdr, body) {
                    Ok((t, content)) if t == ct && content == payload => {}
                    other => return Err(format!("decrypt gave {other:?}")),
                }
                // A different sequence number (so a different nonce) fails.
                if decrypt_record(&aead, &IV, seq.wrapping_add(1), hdr, body).is_ok() {
                    return Err("a wrong nonce opened".to_owned());
                }
            }
        }
    }
    // "No decision before the data": every proper prefix is "need more".
    for n in 0..bytes.len() {
        let prefix = bytes.get(..n).unwrap_or(&[]);
        if !matches!(read_record(prefix, protected), ReadOut::NeedMore) {
            return Err(format!("the prefix of {n} bytes is not 'need more'"));
        }
    }
    Ok(())
}

#[test]
fn rfc8448_records() {
    let mut failures = Vec::new();
    let mut failed = 0usize;
    for r in RECORDS {
        if let Err(why) = check_record(r) {
            failed = failed.saturating_add(1);
            failures.push(format!(
                "RFC 8448 section {} line {} ({} {}): {why}",
                r.section, r.record_line, r.actor, r.step
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"RFC 8448 records (sections 3 to 7)\" pass={} xfail=0 fail={failed} total={}",
        RECORDS.len().saturating_sub(failed),
        RECORDS.len()
    );
    assert_eq!(
        RECORDS.len(),
        41,
        "RFC 8448 sections 3 to 7 hold 41 records"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Split a payload into whole handshake messages.
fn split_messages(payload: &[u8]) -> Option<Vec<Vec<u8>>> {
    let mut out = Vec::new();
    let mut rest = payload;
    while !rest.is_empty() {
        let len = usize::try_from(u32::from_be_bytes([
            0,
            *rest.get(1)?,
            *rest.get(2)?,
            *rest.get(3)?,
        ]))
        .ok()?;
        let total = len.checked_add(4)?;
        out.push(rest.get(..total)?.to_vec());
        rest = rest.get(total..)?;
    }
    Some(out)
}

/// Feed `payload` to a fresh reassembler in fragments of `size` bytes and
/// collect the messages. `None` if the reassembler refuses anything.
fn reassemble(payload: &[u8], size: usize) -> Option<Vec<Vec<u8>>> {
    let mut st = Reassembler::new();
    let mut got = Vec::new();
    for chunk in payload.chunks(size.max(1)) {
        match st.feed_record(22, chunk) {
            Ok(Event::Messages(ms)) => got.extend(ms),
            _ => return None,
        }
    }
    st.at_message_boundary().then_some(got)
}

fn check_reassembly(r: &rfc8448::Record) -> Result<(), String> {
    let payload = hex(r.payload);
    let expected = split_messages(&payload).ok_or("payload is not whole messages")?;
    for size in [payload.len().max(1), 1, 2, 7, 100, 16384] {
        let got = reassemble(&payload, size).ok_or(format!("fragments of {size} refused"))?;
        if got != expected {
            return Err(format!("fragments of {size} gave other messages"));
        }
    }
    // Every message that comes out is a message `parse_handshake` reads.
    for m in &expected {
        parse_handshake(m, HASH_LEN).map_err(|e| format!("message rejected: {e:?}"))?;
    }
    // Messages never appear before their last byte: all proper prefixes of
    // the first message give nothing.
    if let Some(first) = expected.first() {
        for n in 1..first.len() {
            let mut st = Reassembler::new();
            match st.feed_record(22, first.get(..n).unwrap_or(&[])) {
                Ok(Event::Messages(ms)) if ms.is_empty() => {}
                other => return Err(format!("prefix of {n} bytes gave {other:?}")),
            }
        }
    }
    Ok(())
}

#[test]
fn rfc8448_reassembly() {
    let flights: Vec<&rfc8448::Record> = RECORDS
        .iter()
        .filter(|r| r.step.contains("handshake record"))
        .collect();
    let mut failures = Vec::new();
    let mut failed = 0usize;
    for r in &flights {
        if let Err(why) = check_reassembly(r) {
            failed = failed.saturating_add(1);
            failures.push(format!(
                "RFC 8448 section {} line {}: {why}",
                r.section, r.payload_line
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"RFC 8448 handshake payloads through the reassembler\" pass={} xfail=0 fail={failed} total={}",
        flights.len().saturating_sub(failed),
        flights.len()
    );
    assert!(!flights.is_empty());
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// ---------------------------------------------------------------------------
// Hand-built cases: one or more per error rule.
// ---------------------------------------------------------------------------

/// One hand-built case: a name and whether it behaves as the standard says.
struct Case {
    rule: &'static str,
    ok: bool,
}

fn alert_number(k: ErrKind) -> u8 {
    alert_for(k).description
}

fn fails_with(input: &[u8], protected: bool, kind: ErrKind) -> bool {
    matches!(read_record(input, protected), ReadOut::Fail(k) if k == kind)
}

fn parse_err(msg: &[u8]) -> Option<ErrKind> {
    parse_handshake(msg, HASH_LEN).err()
}

/// A ClientHello body from literal pieces: `legacy_version` 0x0303, the
/// random, `sid`, `suites`, `comp`, and the raw extension block `exts`.
fn client_hello_body(sid: &[u8], suites: &[u8], comp: &[u8], exts: &[u8]) -> Vec<u8> {
    let mut b = vec![3u8, 3];
    b.extend([0u8; 32]);
    b.push(u8::try_from(sid.len()).unwrap_or(0));
    b.extend(sid);
    b.extend(u16::try_from(suites.len()).unwrap_or(0).to_be_bytes());
    b.extend(suites);
    b.push(u8::try_from(comp.len()).unwrap_or(0));
    b.extend(comp);
    b.extend(u16::try_from(exts.len()).unwrap_or(0).to_be_bytes());
    b.extend(exts);
    b
}

/// `supported_versions` (0x0304) and `signature_algorithms` as extensions.
const GOOD_EXTS: [u8; 15] = [0, 0x2b, 0, 3, 2, 3, 4, 0, 13, 0, 4, 0, 2, 4, 3];

fn hand_built_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    let mut add = |rule: &'static str, ok: bool| cases.push(Case { rule, ok });
    // 5.1: a record over 2^14 is record_overflow, 22 on the wire.
    add(
        "record over 2^14 (plaintext)",
        fails_with(&[22, 3, 3, 0x40, 1], false, ErrKind::RecordOverflow),
    );
    add(
        "record of exactly 2^14 is waited for",
        matches!(read_record(&[22, 3, 3, 0x40, 0], false), ReadOut::NeedMore),
    );
    add(
        "record_overflow alert is 22",
        alert_number(ErrKind::RecordOverflow) == 22,
    );
    // 5.2: a ciphertext over 2^14 + 256.
    add(
        "record over 2^14 + 256 (ciphertext)",
        fails_with(&[23, 3, 3, 0x41, 1], true, ErrKind::RecordOverflow),
    );
    add(
        "ciphertext of exactly 2^14 + 256 is waited for",
        matches!(read_record(&[23, 3, 3, 0x41, 0], true), ReadOut::NeedMore),
    );
    // 5.1: zero-length handshake and alert fragments.
    add(
        "zero-length handshake fragment",
        fails_with(&[22, 3, 3, 0, 0], false, ErrKind::ZeroLengthFragment),
    );
    add(
        "zero-length alert fragment",
        fails_with(&[21, 3, 3, 0, 0], false, ErrKind::ZeroLengthFragment),
    );
    add(
        "zero-length application data is allowed",
        matches!(read_record(&[23, 3, 3, 0, 0], true), ReadOut::Done(..)),
    );
    add(
        "zero-length fragment alert is unexpected_message (10)",
        alert_number(ErrKind::ZeroLengthFragment) == 10,
    );
    // 5.1: no interleaving.
    let mut partial = Reassembler::new();
    let started = matches!(partial.feed_record(22, &[1, 0, 0, 9, 7]), Ok(Event::Messages(ms)) if ms.is_empty());
    add("a handshake message begun in one record", started);
    add(
        "application data inside a handshake message",
        matches!(partial.feed_record(23, &[1]), Err(ErrKind::Interleaved)),
    );
    let mut partial = Reassembler::new();
    let _ = partial.feed_record(22, &[1, 0, 0, 9, 7]);
    add(
        "an alert inside a handshake message",
        matches!(partial.feed_record(21, &[2, 40]), Err(ErrKind::Interleaved)),
    );
    let mut partial = Reassembler::new();
    let _ = partial.feed_record(22, &[1, 0, 0, 9, 7]);
    add(
        "change_cipher_spec inside a handshake message",
        matches!(partial.feed_ccs(), Err(ErrKind::Interleaved)),
    );
    add(
        "interleaving alert is unexpected_message (10)",
        alert_number(ErrKind::Interleaved) == 10,
    );
    let mut st = Reassembler::new();
    add(
        "an alert with two alerts coalesced",
        matches!(st.feed_record(21, &[1, 0, 2, 40]), Err(ErrKind::Decode)),
    );
    // 5: unexpected record types.
    add(
        "record type invalid(0)",
        fails_with(&[0, 3, 3, 0, 1, 7], false, ErrKind::UnexpectedContentType),
    );
    add(
        "record type heartbeat(24)",
        fails_with(&[24, 3, 3, 0, 1, 7], false, ErrKind::UnexpectedContentType),
    );
    add(
        "application data before protection",
        fails_with(&[23, 3, 3, 0, 1, 7], false, ErrKind::UnexpectedContentType),
    );
    add(
        "a handshake record after protection",
        fails_with(&[22, 3, 3, 0, 1, 7], true, ErrKind::UnexpectedContentType),
    );
    add(
        "change_cipher_spec other than 01",
        fails_with(&[20, 3, 3, 0, 1, 2], false, ErrKind::BadChangeCipherSpec),
    );
    add(
        "change_cipher_spec 01 is dropped",
        matches!(
            read_record(&[20, 3, 3, 0, 1, 1], false),
            ReadOut::Done(Frame::Ccs, _)
        ),
    );
    // 5.1 and 5.2: legacy_record_version.
    add(
        "legacy_record_version 0x0304",
        fails_with(&[22, 3, 4, 0, 1, 7], false, ErrKind::BadLegacyRecordVersion),
    );
    add(
        "legacy_record_version 0x0200",
        fails_with(&[22, 2, 0, 0, 1, 7], false, ErrKind::BadLegacyRecordVersion),
    );
    add(
        "legacy_record_version 0x0301 on a protected record",
        fails_with(&[23, 3, 1, 0, 1, 7], true, ErrKind::BadLegacyRecordVersion),
    );
    add(
        "legacy_record_version 0x0301 on a first ClientHello",
        matches!(read_record(&[22, 3, 1, 0, 1, 7], false), ReadOut::Done(..)),
    );
    // 5.4: all-zero inner plaintext, and the rest of the inner rules.
    add(
        "all-zero inner plaintext",
        matches!(
            open_inner_plaintext(vec![0, 0, 0]),
            Err(ErrKind::AllZeroInnerPlaintext)
        ),
    );
    add(
        "empty inner plaintext",
        matches!(
            open_inner_plaintext(Vec::new()),
            Err(ErrKind::AllZeroInnerPlaintext)
        ),
    );
    add(
        "a protected change_cipher_spec",
        matches!(
            open_inner_plaintext(vec![1, 20]),
            Err(ErrKind::BadChangeCipherSpec)
        ),
    );
    add(
        "an unknown inner content type",
        matches!(
            open_inner_plaintext(vec![1, 99]),
            Err(ErrKind::UnexpectedContentType)
        ),
    );
    add(
        "an empty handshake inner plaintext",
        matches!(
            open_inner_plaintext(vec![22]),
            Err(ErrKind::ZeroLengthFragment)
        ),
    );
    let mut big = vec![7u8; 16385];
    big.push(23);
    add(
        "inner content over 2^14",
        matches!(open_inner_plaintext(big), Err(ErrKind::RecordOverflow)),
    );
    let mut ok_big = vec![7u8; 16384];
    ok_big.push(23);
    add(
        "inner content of exactly 2^14",
        matches!(open_inner_plaintext(ok_big), Ok((23, c)) if c.len() == 16384),
    );
    // 5.2: a record whose decryption fails.
    let rec = encrypt_record(&ToyAead, &IV, 3, 22, &[1, 0, 0, 0], 0);
    let opened = match read_record(&rec, true) {
        ReadOut::Done(Frame::Protected(h, b), _) => Some(decrypt_record(&ToyAead, &IV, 4, h, b)),
        _ => None,
    };
    add(
        "decryption failure is bad_record_mac",
        matches!(opened, Some(Err(ErrKind::BadRecordMac))),
    );
    add(
        "bad_record_mac alert is 20",
        alert_number(ErrKind::BadRecordMac) == 20,
    );
    // 4: handshake framing.
    add(
        "unknown handshake type 0",
        parse_err(&[0, 0, 0, 0]) == Some(ErrKind::UnexpectedHandshakeType),
    );
    add(
        "unknown handshake type 3",
        parse_err(&[3, 0, 0, 0]) == Some(ErrKind::UnexpectedHandshakeType),
    );
    add(
        "message_hash(254) is not a message",
        parse_err(&[254, 0, 0, 0]) == Some(ErrKind::UnexpectedHandshakeType),
    );
    add(
        "unknown handshake type alert is unexpected_message (10)",
        alert_number(ErrKind::UnexpectedHandshakeType) == 10,
    );
    add(
        "a length that exceeds the message",
        parse_err(&[24, 0, 0, 2, 0]) == Some(ErrKind::Decode),
    );
    add(
        "a length shorter than the message",
        parse_err(&[24, 0, 0, 1, 0, 0]) == Some(ErrKind::Decode),
    );
    add(
        "truncated header",
        parse_err(&[24, 0, 0]) == Some(ErrKind::Decode),
    );
    add(
        "decode_error alert is 50",
        alert_number(ErrKind::Decode) == 50,
    );
    add(
        "KeyUpdate with an undefined request",
        parse_err(&[24, 0, 0, 1, 2]) == Some(ErrKind::InvalidEnum),
    );
    add(
        "invalid enum alert is illegal_parameter (47)",
        alert_number(ErrKind::InvalidEnum) == 47,
    );
    let mut too_big = Reassembler::new();
    add(
        "handshake message over the limit",
        matches!(
            too_big.feed_record(22, &[1, 4, 0, 1]),
            Err(ErrKind::HandshakeTooLarge)
        ) && MAX_HANDSHAKE_BODY == 262_144,
    );
    // 4.2: extensions.
    let dup = [8u8, 0, 0, 10, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0];
    add(
        "duplicate extension",
        parse_err(&dup) == Some(ErrKind::DuplicateExtension),
    );
    add(
        "duplicate extension alert is illegal_parameter (47)",
        alert_number(ErrKind::DuplicateExtension) == 47,
    );
    let wrong = [8u8, 0, 0, 8, 0, 6, 0, 0x2b, 0, 2, 3, 4];
    add(
        "supported_versions in EncryptedExtensions",
        parse_err(&wrong) == Some(ErrKind::ExtensionNotAllowed),
    );
    let sh_name = {
        let mut b = vec![3u8, 3];
        b.extend([0u8; 32]);
        b.extend([0u8, 0x13, 3, 0]);
        b.extend([0u8, 10, 0, 0, 0, 0, 0, 0x2b, 0, 2, 3, 4]);
        wrapped(2, &b)
    };
    add(
        "server_name in a ServerHello",
        parse_err(&sh_name) == Some(ErrKind::ExtensionNotAllowed),
    );
    let sh_missing = {
        let mut b = vec![3u8, 3];
        b.extend([0u8; 32]);
        b.extend([0u8, 0x13, 3, 0]);
        b.extend([0u8, 6, 0x12, 0x34, 0, 2, 0xAA, 0xBB]);
        wrapped(2, &b)
    };
    add(
        "ServerHello without supported_versions is structurally decoded",
        matches!(
            parse_handshake(&sh_missing, HASH_LEN),
            Ok(HsMsg::ServerHello(_))
        ),
    );
    add(
        "missing extension alert is 109",
        alert_number(ErrKind::MissingExtension) == 109,
    );
    let sh_bad = {
        let mut b = vec![3u8, 3];
        b.extend([0u8; 32]);
        b.extend([0u8, 0x13, 3, 0]);
        b.extend([0u8, 7, 0, 0x2b, 0, 3, 3, 4, 5]);
        wrapped(2, &b)
    };
    add(
        "supported_versions of the wrong size",
        parse_err(&sh_bad) == Some(ErrKind::Decode),
    );
    // Vector lengths outside their bounds.
    let good = wrapped(1, &client_hello_body(&[], &[0x13, 3], &[0], &GOOD_EXTS));
    add(
        "a minimal ClientHello is read",
        parse_handshake(&good, HASH_LEN).is_ok(),
    );
    let sid33 = wrapped(
        1,
        &client_hello_body(&[1; 33], &[0x13, 3], &[0], &GOOD_EXTS),
    );
    add(
        "legacy_session_id of 33 bytes",
        parse_err(&sid33) == Some(ErrKind::Decode),
    );
    let sid32 = wrapped(
        1,
        &client_hello_body(&[1; 32], &[0x13, 3], &[0], &GOOD_EXTS),
    );
    add(
        "legacy_session_id of 32 bytes",
        parse_handshake(&sid32, HASH_LEN).is_ok(),
    );
    let no_suites = wrapped(1, &client_hello_body(&[], &[], &[0], &GOOD_EXTS));
    add(
        "no cipher suites",
        parse_err(&no_suites) == Some(ErrKind::Decode),
    );
    let odd_suites = wrapped(1, &client_hello_body(&[], &[0x13, 3, 1], &[0], &GOOD_EXTS));
    add(
        "a cipher suite list of odd length",
        parse_err(&odd_suites) == Some(ErrKind::Decode),
    );
    let no_comp = wrapped(1, &client_hello_body(&[], &[0x13, 3], &[], &GOOD_EXTS));
    add(
        "no compression methods",
        parse_err(&no_comp) == Some(ErrKind::Decode),
    );
    let comp1 = wrapped(1, &client_hello_body(&[], &[0x13, 3], &[1], &GOOD_EXTS));
    add(
        "compression method 1",
        parse_err(&comp1) == Some(ErrKind::InvalidEnum),
    );
    let short_exts = wrapped(
        1,
        &client_hello_body(&[], &[0x13, 3], &[0], &GOOD_EXTS[..7]),
    );
    add(
        "an extension block of 7 bytes",
        parse_err(&short_exts) == Some(ErrKind::Decode),
    );
    let mut trailing = client_hello_body(&[], &[0x13, 3], &[0], &GOOD_EXTS);
    trailing.push(0);
    add(
        "a byte after the extensions",
        parse_err(&wrapped(1, &trailing)) == Some(ErrKind::Decode),
    );
    let ticket0 = [4u8, 0, 0, 13, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, 0, 0];
    add(
        "a NewSessionTicket with an empty ticket",
        parse_err(&ticket0) == Some(ErrKind::Decode),
    );
    let cr0 = [13u8, 0, 0, 3, 0, 0, 0];
    add(
        "a CertificateRequest with no extensions",
        parse_err(&cr0) == Some(ErrKind::Decode),
    );
    let cert_ctx = [11u8, 0, 0, 5, 1, 7, 0, 0, 0];
    add(
        "a Certificate context is preserved for the authentication layer",
        matches!(parse_handshake(&cert_ctx, HASH_LEN), Ok(HsMsg::Certificate(c)) if c.context == [7]),
    );
    add(
        "finished of the wrong size",
        parse_handshake(&[20, 0, 0, 2, 7, 8], HASH_LEN).err() == Some(ErrKind::Decode),
    );
    // 6: alerts.
    let mut out = Vec::new();
    write_alert(
        &mut out,
        Alert {
            level: 2,
            description: 40,
        },
    );
    add(
        "an alert is written as two bytes and read back",
        out == [2, 40]
            && read_alert(&out)
                == Some(Alert {
                    level: 2,
                    description: 40,
                }),
    );
    add("an alert of one byte", read_alert(&[2]).is_none());
    add("an alert of three bytes", read_alert(&[2, 40, 0]).is_none());
    cases
}

#[test]
fn hand_built_error_rules() {
    let cases = hand_built_cases();
    let failed: Vec<&Case> = cases.iter().filter(|c| !c.ok).collect();
    println!(
        "clazel-conformance: suite=\"hand-built cases, one or more per error rule of RFC 8446 sections 4 to 6\" pass={} xfail=0 fail={} total={}",
        cases.len().saturating_sub(failed.len()),
        failed.len(),
        cases.len()
    );
    let names: Vec<&str> = failed.iter().map(|c| c.rule).collect();
    assert!(
        failed.is_empty(),
        "cases that did not behave as the standard says: {names:?}"
    );
}

/// Extension blocks written by `push_extensions` are what the reader reads
/// (a quick round trip through the real code on every RFC 8448 extension
/// block, complementing the proof).
#[test]
fn extension_blocks_round_trip() {
    let mut blocks = 0usize;
    for v in MESSAGES {
        let bytes = hex(v.hex);
        if let Ok(HsMsg::ClientHello(ch)) = parse_handshake(&bytes, HASH_LEN) {
            let mut out = Vec::new();
            push_extensions(&mut out, &ch.extensions);
            let mut expect = Vec::new();
            for e in &ch.extensions {
                expect.extend(e.etype.to_be_bytes());
                expect.extend(u16::try_from(e.data.len()).unwrap_or(0).to_be_bytes());
                expect.extend(e.data);
            }
            assert_eq!(out, expect);
            blocks = blocks.saturating_add(1);
        }
    }
    assert!(blocks >= 5, "RFC 8448 has at least five ClientHellos");
}

/// The nonce of RFC 8446 section 5.3 on the RFC 8448 style IV: the sequence
/// number XORed into the last eight bytes.
#[test]
fn nonce_matches_the_standard() {
    let nonce = per_record_nonce(&IV, 0x0102_0304_0506_0708);
    let mut expect = IV;
    for (i, b) in 0x0102_0304_0506_0708u64.to_be_bytes().iter().enumerate() {
        if let Some(e) = expect.get_mut(i.saturating_add(4)) {
            *e ^= b;
        }
    }
    assert_eq!(nonce, expect);
    assert_eq!(per_record_nonce(&IV, 0), IV);
}

// ---------------------------------------------------------------------------
// Differential test against rustls's message codec.
//
// rustls 0.23.46, with default features off (no cryptography provider is
// built), exposes `rustls::internal::msgs`: `MessagePayload::new` (which reads
// one handshake message, an alert or a change_cipher_spec and returns an
// error where the message is malformed), the message fragmenter, and the
// numeric enums. Its handshake message types are not public, so the
// comparison is of what each side accepts, of the bytes each side puts in
// records, and of the numbers.
// ---------------------------------------------------------------------------

use rustls::internal::msgs::base::Payload;
use rustls::internal::msgs::enums::ExtensionType;
use rustls::internal::msgs::fragmenter::MessageFragmenter;
use rustls::internal::msgs::message::{MessagePayload, PlainMessage};
use rustls::{AlertDescription, ContentType, HandshakeType, ProtocolVersion};

/// A small deterministic generator (xorshift), so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }

    fn byte(&mut self) -> u8 {
        u8::try_from(self.next() & 0xFF).unwrap_or(0)
    }
}

fn print_suite(name: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{name}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
}

/// The numbers RFC 8446 gives, as rustls spells them: content types,
/// handshake types, alert descriptions and the extension types of the
/// section 4.2 table.
#[test]
fn rustls_enum_numbers() {
    let mut checks: Vec<(&str, bool)> = Vec::new();
    let mut add = |name: &'static str, ours: u64, theirs: u64| checks.push((name, ours == theirs));
    add(
        "change_cipher_spec",
        20,
        u64::from(u8::from(ContentType::ChangeCipherSpec)),
    );
    add("alert", 21, u64::from(u8::from(ContentType::Alert)));
    add("handshake", 22, u64::from(u8::from(ContentType::Handshake)));
    add(
        "application_data",
        23,
        u64::from(u8::from(ContentType::ApplicationData)),
    );
    add(
        "client_hello",
        1,
        u64::from(u8::from(HandshakeType::ClientHello)),
    );
    add(
        "server_hello",
        2,
        u64::from(u8::from(HandshakeType::ServerHello)),
    );
    add(
        "new_session_ticket",
        4,
        u64::from(u8::from(HandshakeType::NewSessionTicket)),
    );
    add(
        "end_of_early_data",
        5,
        u64::from(u8::from(HandshakeType::EndOfEarlyData)),
    );
    add(
        "encrypted_extensions",
        8,
        u64::from(u8::from(HandshakeType::EncryptedExtensions)),
    );
    add(
        "certificate",
        11,
        u64::from(u8::from(HandshakeType::Certificate)),
    );
    add(
        "certificate_request",
        13,
        u64::from(u8::from(HandshakeType::CertificateRequest)),
    );
    add(
        "certificate_verify",
        15,
        u64::from(u8::from(HandshakeType::CertificateVerify)),
    );
    add("finished", 20, u64::from(u8::from(HandshakeType::Finished)));
    add(
        "key_update",
        24,
        u64::from(u8::from(HandshakeType::KeyUpdate)),
    );
    let alerts: [(&str, u8, AlertDescription); 27] = [
        ("close_notify", 0, AlertDescription::CloseNotify),
        (
            "unexpected_message",
            10,
            AlertDescription::UnexpectedMessage,
        ),
        ("bad_record_mac", 20, AlertDescription::BadRecordMac),
        ("record_overflow", 22, AlertDescription::RecordOverflow),
        ("handshake_failure", 40, AlertDescription::HandshakeFailure),
        ("bad_certificate", 42, AlertDescription::BadCertificate),
        (
            "unsupported_certificate",
            43,
            AlertDescription::UnsupportedCertificate,
        ),
        (
            "certificate_revoked",
            44,
            AlertDescription::CertificateRevoked,
        ),
        (
            "certificate_expired",
            45,
            AlertDescription::CertificateExpired,
        ),
        (
            "certificate_unknown",
            46,
            AlertDescription::CertificateUnknown,
        ),
        ("illegal_parameter", 47, AlertDescription::IllegalParameter),
        ("unknown_ca", 48, AlertDescription::UnknownCA),
        ("access_denied", 49, AlertDescription::AccessDenied),
        ("decode_error", 50, AlertDescription::DecodeError),
        ("decrypt_error", 51, AlertDescription::DecryptError),
        ("protocol_version", 70, AlertDescription::ProtocolVersion),
        (
            "insufficient_security",
            71,
            AlertDescription::InsufficientSecurity,
        ),
        ("internal_error", 80, AlertDescription::InternalError),
        (
            "inappropriate_fallback",
            86,
            AlertDescription::InappropriateFallback,
        ),
        ("user_canceled", 90, AlertDescription::UserCanceled),
        ("missing_extension", 109, AlertDescription::MissingExtension),
        (
            "unsupported_extension",
            110,
            AlertDescription::UnsupportedExtension,
        ),
        ("unrecognized_name", 112, AlertDescription::UnrecognisedName),
        (
            "bad_certificate_status_response",
            113,
            AlertDescription::BadCertificateStatusResponse,
        ),
        (
            "unknown_psk_identity",
            115,
            AlertDescription::UnknownPSKIdentity,
        ),
        (
            "certificate_required",
            116,
            AlertDescription::CertificateRequired,
        ),
        (
            "no_application_protocol",
            120,
            AlertDescription::NoApplicationProtocol,
        ),
    ];
    for (name, ours, theirs) in alerts {
        checks.push((name, ours == u8::from(theirs)));
    }
    // The alert each error kind maps to is a defined alert of RFC 8446
    // section 6.2: rustls names it too.
    for k in [
        ErrKind::Decode,
        ErrKind::RecordOverflow,
        ErrKind::UnexpectedContentType,
        ErrKind::UnexpectedHandshakeType,
        ErrKind::ZeroLengthFragment,
        ErrKind::Interleaved,
        ErrKind::AllZeroInnerPlaintext,
        ErrKind::BadChangeCipherSpec,
        ErrKind::BadLegacyRecordVersion,
        ErrKind::HandshakeTooLarge,
        ErrKind::DuplicateExtension,
        ErrKind::ExtensionNotAllowed,
        ErrKind::InvalidEnum,
        ErrKind::NonEmptyContext,
        ErrKind::MissingExtension,
        ErrKind::BadRecordMac,
    ] {
        let named = !matches!(
            AlertDescription::from(alert_number(k)),
            AlertDescription::Unknown(_)
        );
        checks.push(("the alert of an error kind is a named alert", named));
    }
    let ext: [(u16, ExtensionType); 22] = [
        (0, ExtensionType::ServerName),
        (1, ExtensionType::MaxFragmentLength),
        (5, ExtensionType::StatusRequest),
        (10, ExtensionType::EllipticCurves),
        (13, ExtensionType::SignatureAlgorithms),
        (14, ExtensionType::UseSRTP),
        (15, ExtensionType::Heartbeat),
        (16, ExtensionType::ALProtocolNegotiation),
        (18, ExtensionType::SCT),
        (19, ExtensionType::ClientCertificateType),
        (20, ExtensionType::ServerCertificateType),
        (21, ExtensionType::Padding),
        (41, ExtensionType::PreSharedKey),
        (42, ExtensionType::EarlyData),
        (43, ExtensionType::SupportedVersions),
        (44, ExtensionType::Cookie),
        (45, ExtensionType::PSKKeyExchangeModes),
        (47, ExtensionType::CertificateAuthorities),
        (48, ExtensionType::OIDFilters),
        (49, ExtensionType::PostHandshakeAuth),
        (50, ExtensionType::SignatureAlgorithmsCert),
        (51, ExtensionType::KeyShare),
    ];
    for (ours, theirs) in ext {
        checks.push(("extension type", ours == u16::from(theirs)));
    }
    let failed: Vec<&str> = checks
        .iter()
        .filter(|(_, ok)| !ok)
        .map(|(n, _)| *n)
        .collect();
    print_suite(
        "rustls enum numbers (content, handshake, alert, extension types)",
        checks.len().saturating_sub(failed.len()),
        0,
        failed.len(),
        checks.len(),
    );
    assert!(
        failed.is_empty(),
        "numbers that differ from rustls: {failed:?}"
    );
}

/// One message of a flight at the front of `bytes`, as a reassembler would
/// cut it (rustls's `MessagePayload::new` reads one handshake message and
/// leaves what follows).
fn first_message(bytes: &[u8]) -> Option<&[u8]> {
    let len = usize::try_from(u32::from_be_bytes([
        0,
        *bytes.get(1)?,
        *bytes.get(2)?,
        *bytes.get(3)?,
    ]))
    .ok()?;
    bytes.get(..len.checked_add(4)?)
}

fn rustls_accepts_handshake(msg: &[u8]) -> bool {
    MessagePayload::new(ContentType::Handshake, ProtocolVersion::TLSv1_3, msg).is_ok()
}

/// Mutate `msg` in one of several ways, never touching its first byte (the
/// message type: a message read as another type is a question about what each
/// reader does with bytes that are not that message, which the type-specific
/// rules above do not answer).
fn mutate(msg: &[u8], r: &mut Rng) -> Vec<u8> {
    let mut m = msg.to_vec();
    let body_len = m.len().saturating_sub(1);
    match r.below(6) {
        0 if body_len > 0 => {
            let i = r.below(body_len).saturating_add(1);
            if let Some(b) = m.get_mut(i) {
                *b = r.byte();
            }
        }
        1 if body_len > 0 => m.truncate(r.below(body_len).saturating_add(1)),
        2 => m.push(r.byte()),
        3 if m.len() > 4 => {
            // Change one of the three length bytes.
            let i = r.below(3).saturating_add(1);
            if let Some(b) = m.get_mut(i) {
                *b = r.byte();
            }
        }
        4 if body_len > 0 => {
            let i = r.below(body_len).saturating_add(1);
            m.remove(i);
        }
        _ => {
            let i = r.below(m.len()).max(1).min(m.len());
            m.insert(i, r.byte());
        }
    }
    m
}

/// How the two readers compare on one handshake message.
#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    /// Both accept or both reject.
    Agree,
    /// We reject for a rule about meaning rather than syntax, which rustls
    /// applies after parsing (or not at all), or for the data of an extension
    /// that rustls keeps opaque in that message.
    OursStricter,
    /// rustls rejects an extension of a ServerHello or HelloRetryRequest that
    /// was not offered, which RFC 8446 section 4.2 leaves to the handshake
    /// (`unsupported_extension`, phase-3.md item 3.5e); we only apply the
    /// table, which allows a type that is not one of its rows.
    RustlsStricter,
    /// A difference nobody listed.
    Unexplained(String),
}

fn hex_of(b: &[u8]) -> String {
    b.iter()
        .map(|x| format!("{x:02x}"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn compare_handshake(msg: &[u8]) -> Verdict {
    // Cut one message like the reassembler would; shorter than its length
    // field says is rejected by both.
    let Some(one) = first_message(msg) else {
        let theirs = rustls_accepts_handshake(msg);
        let ours = parse_handshake(msg, HASH_LEN).is_ok();
        return if !theirs && !ours {
            Verdict::Agree
        } else {
            Verdict::Unexplained(format!(
                "short input: ours {ours} theirs {theirs}: {}",
                hex_of(msg)
            ))
        };
    };
    let ours = parse_handshake(one, HASH_LEN);
    let theirs = rustls_accepts_handshake(one);
    match (ours, theirs) {
        (Ok(_), true) | (Err(_), false) => Verdict::Agree,
        // Rules about meaning rather than syntax, which rustls checks in its
        // state machine (or in the extension's own typed reader) and not
        // when it reads the message: duplicates, extensions in the wrong
        // message, a missing supported_versions, a non-empty certificate
        // context, an invalid enum, and a message type it does not know
        // (rustls keeps an unknown type as `Unknown`).
        (
            Err(
                ErrKind::DuplicateExtension
                | ErrKind::ExtensionNotAllowed
                | ErrKind::MissingExtension
                | ErrKind::NonEmptyContext
                | ErrKind::InvalidEnum
                | ErrKind::UnexpectedHandshakeType,
            ),
            true,
        ) => Verdict::OursStricter,
        // `decode_error` where the message's own structure reads: the data of
        // an extension that this crate reads as its type says (a malformed
        // `supported_groups` in EncryptedExtensions, an unknown `name_type`
        // in `server_name`) while rustls keeps the data opaque; or a
        // Finished of another length than the hash's, which rustls does not
        // know when it parses.
        (Err(ErrKind::Decode), true)
            if structure_parses(one)
                || relaxed_structure_parses(one)
                || one.first() == Some(&20) =>
        {
            Verdict::OursStricter
        }
        (Err(k), true) => Verdict::Unexplained(format!(
            "we say {k:?}, rustls accepts, type {}, len {}: {}",
            one.first().copied().unwrap_or(0),
            one.len(),
            hex_of(one)
        )),
        (Ok(HsMsg::ServerHello(sh)), false) if has_unoffered_type(&sh) => Verdict::RustlsStricter,
        (Ok(m), false) if has_opaque_extension(&m) => Verdict::RustlsStricter,
        (Ok(_), false) => {
            Verdict::Unexplained(format!("we accept, rustls rejects: {}", hex_of(one)))
        }
    }
}

/// Whether the message has an extension whose data this crate keeps opaque
/// (every type but `server_name`, `supported_groups`, `signature_algorithms`,
/// `signature_algorithms_cert`, `supported_versions`, `cookie` and
/// `key_share`): rustls reads the data of many of them (`renegotiation_info`,
/// `session_ticket`, `ec_point_formats`, ALPN, `record_size_limit`,
/// `early_data` ...), so a mutation in one is a rejection only it makes.
fn has_opaque_extension(m: &HsMsg<'_>) -> bool {
    let opaque = |es: &[Extension<'_>]| {
        es.iter()
            .any(|e| !matches!(e.etype, 0 | 10 | 13 | 50 | 43 | 44 | 51))
    };
    match m {
        HsMsg::ClientHello(c) => opaque(&c.extensions),
        HsMsg::ServerHello(c) => opaque(&c.extensions),
        HsMsg::EncryptedExtensions(es) => opaque(es),
        HsMsg::CertificateRequest(c) => opaque(&c.extensions),
        HsMsg::NewSessionTicket(c) => opaque(&c.extensions),
        HsMsg::Certificate(c) => c.entries.iter().any(|e| opaque(&e.extensions)),
        _ => false,
    }
}

/// Whether the message reads if the floors of RFC 8446 Appendix B on its
/// extension block were zero: `ClientHello` `extensions<8..2^16-1>`,
/// `ServerHello` `extensions<6..2^16-1>`, `CertificateRequest`
/// `extensions<2..2^16-1>`, and the extension block's presence in a
/// ClientHello and ServerHello. rustls enforces none of them.
fn relaxed_structure_parses(one: &[u8]) -> bool {
    let body = one.get(4..).unwrap_or(&[]);
    let mut c = Cur::new(body);
    let ok = match one.first() {
        Some(1) => {
            c.u16().is_some()
                && c.fixed(32).is_some()
                && c.vec(0, 32).is_some()
                && c.vec(2, 65534).is_some()
                && c.vec(1, 255).is_some()
        }
        Some(2) => {
            c.u16().is_some()
                && c.fixed(32).is_some()
                && c.vec(0, 32).is_some()
                && c.u16().is_some()
                && c.u8().is_some()
        }
        Some(13) => c.vec(0, 255).is_some(),
        _ => false,
    };
    // RFC 8446 section 4.1.2 lets a server receive a ClientHello with no
    // extension block at all (an earlier version's); the Appendix B grammar
    // this crate follows has one, and so does a ServerHello.
    let may_omit = matches!(one.first(), Some(1 | 2)) && c.is_empty();
    ok && (may_omit || (read_exts(&mut c, 0, 65535).is_some() && c.is_empty()))
}

/// Whether the message's own structure (not the bodies of its extensions)
/// reads.
fn structure_parses(one: &[u8]) -> bool {
    let body = one.get(4..).unwrap_or(&[]);
    match one.first() {
        Some(1) => read_client_hello(body).is_some(),
        Some(2) => read_server_hello(body).is_some(),
        Some(4) => read_new_session_ticket(body).is_some(),
        Some(8) => read_encrypted_extensions(body).is_some(),
        Some(11) => read_certificate(body).is_some(),
        Some(13) => read_certificate_request(body).is_some(),
        _ => false,
    }
}

/// Whether a ServerHello or HelloRetryRequest has an extension of a type that
/// can only be answered if it was offered and that RFC 8446 does not define
/// for it (neither `supported_versions`, `key_share`, `pre_shared_key` nor, in
/// a HelloRetryRequest, `cookie`).
fn has_unoffered_type(sh: &clazel_tls::types::ServerHello<'_>) -> bool {
    let hrr = is_hello_retry_request(sh);
    sh.extensions
        .iter()
        .any(|e| !matches!(e.etype, 43 | 51) && !(hrr && e.etype == 44) && !(!hrr && e.etype == 41))
}

#[test]
fn rustls_handshake_acceptance() {
    let originals: Vec<Vec<u8>> = MESSAGES.iter().map(|m| hex(m.hex)).collect();
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut cases: Vec<Vec<u8>> = originals.clone();
    // Miri runs the tests too, about a hundred times slower: fewer mutations.
    let per_message: usize = if cfg!(miri) { 8 } else { 400 };
    for o in &originals {
        for _ in 0..per_message {
            cases.push(mutate(o, &mut rng));
        }
    }
    let (mut agree, mut stricter, mut unexplained) = (0usize, 0usize, Vec::new());
    for c in &cases {
        match compare_handshake(c) {
            Verdict::Agree => agree = agree.saturating_add(1),
            Verdict::OursStricter | Verdict::RustlsStricter => {
                stricter = stricter.saturating_add(1)
            }
            Verdict::Unexplained(why) => unexplained.push(why),
        }
    }
    print_suite(
        &format!(
            "rustls handshake message acceptance (RFC 8448 messages and {per_message} mutations each)"
        ),
        agree,
        stricter,
        unexplained.len(),
        cases.len(),
    );
    for u in &unexplained {
        println!("UNEXPLAINED {}", u);
    }
    assert!(
        unexplained.is_empty(),
        "{} unexplained differences, first: {:?}",
        unexplained.len(),
        unexplained.first()
    );
}

/// Every two-byte payload is an alert for both; the lengths either side of
/// it are for neither; every one-byte change_cipher_spec payload is
/// accepted by both only when it is 0x01.
#[test]
fn rustls_alerts_and_change_cipher_spec() {
    let mut total = 0usize;
    let mut bad: Vec<String> = Vec::new();
    let levels: Vec<u8> = if cfg!(miri) {
        vec![0, 1, 2, 255]
    } else {
        (0..=255u8).collect()
    };
    for level in levels {
        for desc in 0..=255u8 {
            total = total.saturating_add(1);
            let ours = read_alert(&[level, desc]).is_some();
            let theirs =
                MessagePayload::new(ContentType::Alert, ProtocolVersion::TLSv1_3, &[level, desc])
                    .is_ok();
            if !(ours && theirs) {
                bad.push(format!("alert {level} {desc}"));
            }
        }
    }
    for payload in [&[][..], &[2][..], &[2, 40, 0][..], &[2, 40, 2, 40][..]] {
        total = total.saturating_add(1);
        let ours = read_alert(payload).is_some();
        let theirs =
            MessagePayload::new(ContentType::Alert, ProtocolVersion::TLSv1_3, payload).is_ok();
        if ours || theirs {
            bad.push(format!(
                "alert payload {payload:?}: ours {ours} theirs {theirs}"
            ));
        }
    }
    for b in 0..=255u8 {
        total = total.saturating_add(1);
        let ours = matches!(
            read_record(&[20, 3, 3, 0, 1, b], false),
            ReadOut::Done(Frame::Ccs, _)
        );
        let theirs = MessagePayload::new(
            ContentType::ChangeCipherSpec,
            ProtocolVersion::TLSv1_3,
            &[b],
        )
        .is_ok();
        if ours != theirs || ours != (b == 1) {
            bad.push(format!(
                "change_cipher_spec {b}: ours {ours} theirs {theirs}"
            ));
        }
    }
    print_suite(
        "rustls alerts (all 65536 two-byte payloads) and change_cipher_spec",
        total.saturating_sub(bad.len()),
        0,
        bad.len(),
        total,
    );
    assert!(bad.is_empty(), "{:?}", bad.first());
}

/// rustls cuts the RFC 8448 handshake payloads into records of several
/// maximum sizes; we read each record, find the header rustls wrote is the
/// one we write, and reassemble the messages.
#[test]
fn rustls_fragmenter() {
    let flights: Vec<Vec<u8>> = RECORDS
        .iter()
        .filter(|r| r.step.contains("handshake record"))
        .map(|r| hex(r.payload))
        .collect();
    let mut cases = 0usize;
    let mut bad: Vec<String> = Vec::new();
    for payload in &flights {
        for max in [32usize, 33, 64, 100, 517, 4096, 16389] {
            cases = cases.saturating_add(1);
            let mut fragmenter = MessageFragmenter::default();
            if fragmenter.set_max_fragment_size(Some(max)).is_err() {
                bad.push(format!("rustls refuses a maximum of {max}"));
                continue;
            }
            let plain = PlainMessage {
                typ: ContentType::Handshake,
                version: ProtocolVersion::TLSv1_2,
                payload: Payload::Owned(payload.clone()),
            };
            let mut st = Reassembler::new();
            let mut got: Vec<Vec<u8>> = Vec::new();
            let mut ok = true;
            for frag in fragmenter.fragment_message(&plain) {
                let body = frag.payload.to_vec();
                let mut record = vec![u8::from(frag.typ)];
                record.extend(u16::from(frag.version).to_be_bytes());
                record.extend(u16::try_from(body.len()).unwrap_or(0).to_be_bytes());
                record.extend(&body);
                match read_record(&record, false) {
                    ReadOut::Done(Frame::Plain(22, f), []) if f == body.as_slice() => {}
                    other => {
                        bad.push(format!(
                            "size {max}: a record from rustls reads as {other:?}"
                        ));
                        ok = false;
                        break;
                    }
                }
                let mut ours = Vec::new();
                write_plaintext(&mut ours, 22, 0x0303, &body);
                if ours != record || record.len() > max {
                    bad.push(format!(
                        "size {max}: header bytes differ or the record is over the size"
                    ));
                    ok = false;
                    break;
                }
                match st.feed_record(22, &body) {
                    Ok(Event::Messages(ms)) => got.extend(ms),
                    other => {
                        bad.push(format!("size {max}: reassembly gave {other:?}"));
                        ok = false;
                        break;
                    }
                }
            }
            if ok
                && (got != split_messages(payload).unwrap_or_default() || !st.at_message_boundary())
            {
                bad.push(format!("size {max}: other messages out"));
            }
        }
    }
    print_suite(
        "rustls fragmenter (RFC 8448 payloads, 7 sizes)",
        cases.saturating_sub(bad.len()),
        0,
        bad.len(),
        cases,
    );
    assert!(bad.is_empty(), "{:?}", bad.first());
}
