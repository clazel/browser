//! The root certificate table for `clazel-x509` (Phase 3 item 3.5b/3.5g).
//!
//! NSS's `lib/ckfw/builtins/certdata.txt` is vendored, byte for byte, under
//! `crates/clazel-x509/data/nss-<commit>/` with a `SOURCE.md` giving the
//! upstream commit, URLs and SHA-256. This module turns it into
//! `crates/clazel-x509/src/roots/data.rs`, a Rust file of constant data that
//! is committed (as `psl.rs` does for the Public Suffix List). `cargo xtask
//! tables` writes it; `check` and `verify` fail if the vendored file's hash
//! differs from `SOURCE.md` or the committed file differs from what this
//! produces.
//!
//! The trust store is part of the trusted base, so what this module derives
//! is kept to simple, stated steps (each is listed in the generated file's
//! header and in the crate's README):
//! - the file is a list of objects; an object is a run of attribute lines
//!   (`NAME TYPE VALUE`, or `NAME MULTILINE_OCTAL` and the lines up to
//!   `END`, whose `\ooo` escapes are bytes) ended by a blank line. The
//!   objects of class `CKO_CERTIFICATE` and `CKO_NSS_TRUST` are used;
//! - a trust object belongs to the certificate object with the same
//!   `CKA_ISSUER` and `CKA_SERIAL_NUMBER` (NSS's own key). Exactly one of
//!   each must exist for every object, with equal `CKA_LABEL`s, and no two
//!   certificates share a key or a DER encoding;
//! - a certificate is a root of the table when its trust object has
//!   `CKA_TRUST_SERVER_AUTH` equal to `CKT_NSS_TRUSTED_DELEGATOR`. Any other
//!   value excludes it: `CKT_NSS_MUST_VERIFY_TRUST` ("not a trust anchor
//!   for TLS servers", the value that e-mail-only and code-signing-only roots
//!   have here), `CKT_NSS_NOT_TRUSTED` (distrusted). A further value stops
//!   the generator rather than being guessed;
//! - `CKA_NSS_SERVER_DISTRUST_AFTER` is carried, not applied: `CK_FALSE`
//!   gives `None`, and a 13-octet `UTCTime` text (`YYMMDDHHMMSSZ`) gives
//!   `Some` of it. It is read from the certificate object (where NSS puts it);
//!   any other value, or one on the trust object, stops the generator;
//! - the SHA-256 of each certificate's DER is computed here and must equal
//!   the `# Fingerprint (SHA-256)` comment NSS writes above the object (a
//!   cross-check of the data, not an input);
//! - the labels are the `CKA_LABEL` strings (UTF-8, no escapes) and rows keep
//!   the order the certificates have in the file; no sorting.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::reviews;
use crate::workspace;

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-x509/data/nss-0a2b0c75";
/// The generated file, relative to the repository root.
const OUTPUT: &str = "crates/clazel-x509/src/roots/data.rs";
/// The files `SOURCE.md` must list, besides itself and LICENSE.
const FILES: &[&str] = &["certdata.txt"];

/// Compare (or, with `write`, rewrite) the generated table. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_sources(&dir);
    let mut notes = Vec::new();
    if !problems.is_empty() {
        return (problems, notes);
    }
    let fresh = match std::fs::read_to_string(dir.join("certdata.txt"))
        .map_err(|e| e.to_string())
        .and_then(|t| generate(&t))
    {
        Ok(f) => f,
        Err(e) => return (vec![format!("{DATA_DIR}: {e}")], notes),
    };
    let current = std::fs::read_to_string(OUTPUT).ok();
    if current.as_deref() == Some(fresh.as_str()) {
        notes.push(format!("{OUTPUT}: up to date"));
    } else if write {
        match std::fs::write(OUTPUT, &fresh) {
            Ok(()) => notes.push(format!("{OUTPUT}: written")),
            Err(e) => problems.push(format!("{OUTPUT}: {e}")),
        }
    } else if current.is_none() {
        problems.push(format!("{OUTPUT}: missing; run `cargo xtask tables`"));
    } else {
        problems.push(format!(
            "{OUTPUT}: stale (differs from what xtask/src/roots.rs produces); \
             run `cargo xtask tables` and commit the result"
        ));
    }
    (problems, notes)
}

/// Every vendored file is listed in `SOURCE.md` with its SHA-256, and
/// matches it; nothing else is in the directory.
fn check_sources(dir: &Path) -> Vec<String> {
    let rel = workspace::relative(dir);
    let source = match std::fs::read_to_string(dir.join("SOURCE.md")) {
        Ok(s) => s,
        Err(e) => return vec![format!("{rel}/SOURCE.md: {e}")],
    };
    let mut problems = Vec::new();
    for file in FILES {
        let listed = source.lines().find_map(|l| {
            let rest = l.trim().strip_prefix("SHA-256:")?.trim();
            let (hash, name) = rest.split_once(char::is_whitespace)?;
            (name.trim().trim_matches('`') == *file).then(|| hash.to_ascii_lowercase())
        });
        let Some(listed) = listed else {
            problems.push(format!(
                "{rel}/SOURCE.md: no \"SHA-256: <hash> {file}\" line"
            ));
            continue;
        };
        match reviews::sha256(&dir.join(file)) {
            Ok(actual) if actual == listed => {}
            Ok(actual) => problems.push(format!(
                "{rel}/{file}: SHA-256 {actual} differs from SOURCE.md ({listed})"
            )),
            Err(e) => problems.push(e),
        }
    }
    if !source.lines().any(|l| l.trim().starts_with("License:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"License:\" line"));
    }
    if !source.lines().any(|l| l.trim().starts_with("Commit:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"Commit:\" line"));
    }
    match std::fs::read_dir(dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !FILES.contains(&name.as_str()) && name != "SOURCE.md" && name != "LICENSE" {
                    problems.push(format!("{rel}/{name}: not an input of xtask/src/roots.rs"));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

/// FIPS 180-4 section 6.2, SHA-256 of `data`.
fn sha256(data: &[u8]) -> [u8; 32] {
    const K: [u32; 64] = [
        0x428a_2f98,
        0x7137_4491,
        0xb5c0_fbcf,
        0xe9b5_dba5,
        0x3956_c25b,
        0x59f1_11f1,
        0x923f_82a4,
        0xab1c_5ed5,
        0xd807_aa98,
        0x1283_5b01,
        0x2431_85be,
        0x550c_7dc3,
        0x72be_5d74,
        0x80de_b1fe,
        0x9bdc_06a7,
        0xc19b_f174,
        0xe49b_69c1,
        0xefbe_4786,
        0x0fc1_9dc6,
        0x240c_a1cc,
        0x2de9_2c6f,
        0x4a74_84aa,
        0x5cb0_a9dc,
        0x76f9_88da,
        0x983e_5152,
        0xa831_c66d,
        0xb003_27c8,
        0xbf59_7fc7,
        0xc6e0_0bf3,
        0xd5a7_9147,
        0x06ca_6351,
        0x1429_2967,
        0x27b7_0a85,
        0x2e1b_2138,
        0x4d2c_6dfc,
        0x5338_0d13,
        0x650a_7354,
        0x766a_0abb,
        0x81c2_c92e,
        0x9272_2c85,
        0xa2bf_e8a1,
        0xa81a_664b,
        0xc24b_8b70,
        0xc76c_51a3,
        0xd192_e819,
        0xd699_0624,
        0xf40e_3585,
        0x106a_a070,
        0x19a4_c116,
        0x1e37_6c08,
        0x2748_774c,
        0x34b0_bcb5,
        0x391c_0cb3,
        0x4ed8_aa4a,
        0x5b9c_ca4f,
        0x682e_6ff3,
        0x748f_82ee,
        0x78a5_636f,
        0x84c8_7814,
        0x8cc7_0208,
        0x90be_fffa,
        0xa450_6ceb,
        0xbef9_a3f7,
        0xc671_78f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09_e667,
        0xbb67_ae85,
        0x3c6e_f372,
        0xa54f_f53a,
        0x510e_527f,
        0x9b05_688c,
        0x1f83_d9ab,
        0x5be0_cd19,
    ];
    let mut padded = data.to_vec();
    padded.push(0x80);
    while padded.len().checked_rem(64) != Some(56) {
        padded.push(0);
    }
    let bits = u64::try_from(data.len()).unwrap_or(0).wrapping_mul(8);
    padded.extend_from_slice(&bits.to_be_bytes());
    for block in padded.as_chunks::<64>().0 {
        let mut w: Vec<u32> = block
            .as_chunks::<4>()
            .0
            .iter()
            .map(|c| u32::from_be_bytes(*c))
            .collect();
        for i in 16..64usize {
            let at = |back: usize| w.get(i.wrapping_sub(back)).copied().unwrap_or(0);
            let s0 = at(15).rotate_right(7) ^ at(15).rotate_right(18) ^ (at(15) >> 3);
            let s1 = at(2).rotate_right(17) ^ at(2).rotate_right(19) ^ (at(2) >> 10);
            let next = at(16).wrapping_add(s0).wrapping_add(at(7)).wrapping_add(s1);
            w.push(next);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for (k, wi) in K.iter().zip(w.iter()) {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(*k)
                .wrapping_add(*wi);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        let [h0, h1, h2, h3, h4, h5, h6, h7] = h;
        h = [
            h0.wrapping_add(a),
            h1.wrapping_add(b),
            h2.wrapping_add(c),
            h3.wrapping_add(d),
            h4.wrapping_add(e),
            h5.wrapping_add(f),
            h6.wrapping_add(g),
            h7.wrapping_add(hh),
        ];
    }
    let mut out = Vec::with_capacity(32);
    for word in h {
        out.extend_from_slice(&word.to_be_bytes());
    }
    <[u8; 32]>::try_from(out).unwrap_or([0; 32])
}

/// Lower-case hex of `bytes`.
fn hex(bytes: &[u8]) -> String {
    let mut s = String::new();
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

/// One attribute value.
enum Value {
    /// The rest of a single-line attribute after its type (a quoted
    /// `UTF8` value is stored without its quotes).
    Text(String),
    /// A `MULTILINE_OCTAL` value, decoded.
    Bytes(Vec<u8>),
}

/// One object of the file.
struct Object {
    /// The first line of the object, for messages.
    line: usize,
    /// The `#` comment lines directly above it.
    comments: Vec<String>,
    attrs: BTreeMap<String, Value>,
}

impl Object {
    fn text(&self, name: &str) -> Result<&str, String> {
        match self.attrs.get(name) {
            Some(Value::Text(t)) => Ok(t),
            _ => Err(format!("line {}: no single-line {name}", self.line)),
        }
    }

    fn bytes(&self, name: &str) -> Result<&[u8], String> {
        match self.attrs.get(name) {
            Some(Value::Bytes(b)) => Ok(b),
            _ => Err(format!("line {}: no MULTILINE_OCTAL {name}", self.line)),
        }
    }
}

/// `\ooo` escapes (three octal digits each) to bytes.
fn decode_octal(line: &str, at: usize) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    let mut rest = line.trim_end();
    while !rest.is_empty() {
        let Some(after) = rest.strip_prefix('\\') else {
            return Err(format!("line {at}: expected `\\ooo`, found {rest:?}"));
        };
        let digits = after
            .get(..3)
            .filter(|d| d.bytes().all(|b| (b'0'..=b'7').contains(&b)))
            .ok_or_else(|| format!("line {at}: bad octal escape in {line:?}"))?;
        let value = u16::from_str_radix(digits, 8).map_err(|e| format!("line {at}: {e}"))?;
        out.push(u8::try_from(value).map_err(|_| format!("line {at}: octal escape over 255"))?);
        rest = after.get(3..).unwrap_or("");
    }
    Ok(out)
}

/// The objects after `BEGINDATA`, as the module docs describe.
fn objects(text: &str) -> Result<Vec<Object>, String> {
    let mut out = Vec::new();
    let mut pending: Vec<String> = Vec::new();
    let mut current: Option<Object> = None;
    let mut lines = text.lines().enumerate();
    let mut begun = false;
    while let Some((i, line)) = lines.next() {
        let at = i.saturating_add(1);
        if !begun {
            begun = line.trim() == "BEGINDATA";
            continue;
        }
        let line = line.trim_end();
        if line.is_empty() {
            if let Some(o) = current.take() {
                out.push(o);
            }
            pending.clear();
            continue;
        }
        if line.starts_with('#') {
            if current.is_none() {
                pending.push(line.to_owned());
            }
            continue;
        }
        let mut parts = line.splitn(3, ' ');
        let name = parts.next().unwrap_or("");
        let ty = parts
            .next()
            .ok_or_else(|| format!("line {at}: attribute without a type: {line:?}"))?;
        let rest = parts.next().unwrap_or("");
        let obj = current.get_or_insert_with(|| Object {
            line: at,
            comments: std::mem::take(&mut pending),
            attrs: BTreeMap::new(),
        });
        if name == "CKA_CLASS" && !obj.attrs.is_empty() {
            return Err(format!("line {at}: object not ended by a blank line"));
        }
        let value = if ty == "MULTILINE_OCTAL" {
            let mut bytes = Vec::new();
            loop {
                let Some((j, l)) = lines.next() else {
                    return Err(format!("line {at}: {name} has no END"));
                };
                if l.trim_end() == "END" {
                    break;
                }
                bytes.extend(decode_octal(l, j.saturating_add(1))?);
            }
            Value::Bytes(bytes)
        } else if ty == "UTF8" {
            let inner = rest
                .strip_prefix('"')
                .and_then(|r| r.strip_suffix('"'))
                .ok_or_else(|| format!("line {at}: unquoted UTF8 value {rest:?}"))?;
            if inner.contains(['"', '\\']) {
                return Err(format!("line {at}: escape or quote in a UTF8 value"));
            }
            Value::Text(inner.to_owned())
        } else {
            Value::Text(rest.to_owned())
        };
        if obj.attrs.insert(name.to_owned(), value).is_some() {
            return Err(format!("line {at}: {name} given twice"));
        }
    }
    if let Some(o) = current.take() {
        out.push(o);
    }
    if !begun {
        return Err("no BEGINDATA line".into());
    }
    Ok(out)
}

/// The `# Fingerprint (SHA-256): AA:BB:...` comment, as lower-case hex.
fn fingerprint_comment(o: &Object) -> Result<String, String> {
    let mut found = None;
    for c in &o.comments {
        if let Some(v) = c.strip_prefix("# Fingerprint (SHA-256):") {
            let h: String = v.trim().split(':').collect::<String>().to_ascii_lowercase();
            if found.replace(h).is_some() {
                return Err(format!("line {}: two SHA-256 fingerprint comments", o.line));
            }
        }
    }
    found.ok_or_else(|| format!("line {}: no SHA-256 fingerprint comment", o.line))
}

/// Why a certificate is not in the table.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Excluded {
    /// `CKT_NSS_NOT_TRUSTED` for server authentication.
    Distrusted,
    /// Not a server-auth anchor, but a trusted delegator for e-mail only.
    EmailOnly,
    /// Not a server-auth anchor, but a trusted delegator for code signing only.
    CodeSigningOnly,
    /// Not a server-auth anchor and trusted for nothing else either.
    MustVerify,
}

impl Excluded {
    fn describe(self) -> &'static str {
        match self {
            Excluded::Distrusted => "server auth CKT_NSS_NOT_TRUSTED (distrusted)",
            Excluded::EmailOnly => {
                "server auth CKT_NSS_MUST_VERIFY_TRUST, e-mail protection trusted (e-mail only)"
            }
            Excluded::CodeSigningOnly => {
                "server auth CKT_NSS_MUST_VERIFY_TRUST, code signing trusted (code signing only)"
            }
            Excluded::MustVerify => "server auth CKT_NSS_MUST_VERIFY_TRUST, nothing else trusted",
        }
    }
}

/// One root of the table.
struct Root {
    label: String,
    der: Vec<u8>,
    sha256: [u8; 32],
    distrust_after: Option<String>,
}

/// The table's roots and the counts of what was left out.
struct Table {
    roots: Vec<Root>,
    certificates: usize,
    excluded: BTreeMap<Excluded, usize>,
    with_distrust_after: usize,
}

const TRUSTED: &str = "CKT_NSS_TRUSTED_DELEGATOR";
const MUST_VERIFY: &str = "CKT_NSS_MUST_VERIFY_TRUST";
const NOT_TRUSTED: &str = "CKT_NSS_NOT_TRUSTED";

/// The rules of the module docs, over the text of `certdata.txt`.
fn table(text: &str) -> Result<Table, String> {
    let objs = objects(text)?;
    let mut certs = Vec::new();
    let mut trusts: BTreeMap<(Vec<u8>, Vec<u8>), &Object> = BTreeMap::new();
    for o in &objs {
        match o.text("CKA_CLASS")? {
            "CKO_CERTIFICATE" => certs.push(o),
            "CKO_NSS_TRUST" => {
                let key = (
                    o.bytes("CKA_ISSUER")?.to_vec(),
                    o.bytes("CKA_SERIAL_NUMBER")?.to_vec(),
                );
                if trusts.insert(key, o).is_some() {
                    return Err(format!("line {}: two trust objects for one key", o.line));
                }
            }
            "CKO_NSS_BUILTIN_ROOT_LIST" => {}
            other => return Err(format!("line {}: unknown object class {other}", o.line)),
        }
    }
    let mut keys: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    let mut ders: Vec<&[u8]> = Vec::new();
    let mut roots = Vec::new();
    let mut excluded: BTreeMap<Excluded, usize> = BTreeMap::new();
    let mut with_distrust_after = 0usize;
    for c in &certs {
        let key = (
            c.bytes("CKA_ISSUER")?.to_vec(),
            c.bytes("CKA_SERIAL_NUMBER")?.to_vec(),
        );
        if keys.contains(&key) {
            return Err(format!(
                "line {}: two certificates with one issuer and serial",
                c.line
            ));
        }
        let der = c.bytes("CKA_VALUE")?;
        if ders.contains(&der) {
            return Err(format!("line {}: a certificate given twice", c.line));
        }
        check_der(der).map_err(|e| format!("line {}: {e}", c.line))?;
        let label = c.text("CKA_LABEL")?;
        let Some(t) = trusts.remove(&key) else {
            return Err(format!("line {}: {label:?} has no trust object", c.line));
        };
        if t.text("CKA_LABEL")? != label {
            return Err(format!(
                "line {}: trust label differs from {label:?}",
                t.line
            ));
        }
        let digest = sha256(der);
        for o in [c, t] {
            if fingerprint_comment(o)? != hex(&digest) {
                return Err(format!(
                    "line {}: SHA-256 of {label:?} differs from the fingerprint comment",
                    o.line
                ));
            }
        }
        match t.attrs.get("CKA_NSS_SERVER_DISTRUST_AFTER") {
            None => {}
            Some(Value::Text(v)) if v == "CK_FALSE" => {}
            Some(_) => {
                return Err(format!(
                    "line {}: CKA_NSS_SERVER_DISTRUST_AFTER on a trust object",
                    t.line
                ));
            }
        }
        let distrust_after = match c.attrs.get("CKA_NSS_SERVER_DISTRUST_AFTER") {
            None => None,
            Some(Value::Text(v)) if v == "CK_FALSE" => None,
            Some(Value::Bytes(b)) => {
                Some(utc_time(b).map_err(|e| format!("line {}: {e}", c.line))?)
            }
            Some(Value::Text(v)) => {
                return Err(format!(
                    "line {}: unexpected CKA_NSS_SERVER_DISTRUST_AFTER {v:?}",
                    c.line
                ));
            }
        };
        let trust_of = |name: &str| -> Result<&str, String> {
            let v = t.text(name)?;
            if [TRUSTED, MUST_VERIFY, NOT_TRUSTED].contains(&v) {
                Ok(v)
            } else {
                Err(format!("line {}: unknown {name} value {v}", t.line))
            }
        };
        let server = trust_of("CKA_TRUST_SERVER_AUTH")?;
        let email = trust_of("CKA_TRUST_EMAIL_PROTECTION")?;
        let code = trust_of("CKA_TRUST_CODE_SIGNING")?;
        if server == TRUSTED {
            if distrust_after.is_some() {
                with_distrust_after = with_distrust_after.saturating_add(1);
            }
            roots.push(Root {
                label: label.to_owned(),
                der: der.to_vec(),
                sha256: digest,
                distrust_after,
            });
        } else {
            let why = if server == NOT_TRUSTED {
                Excluded::Distrusted
            } else if email == TRUSTED && code != TRUSTED {
                Excluded::EmailOnly
            } else if code == TRUSTED && email != TRUSTED {
                Excluded::CodeSigningOnly
            } else {
                Excluded::MustVerify
            };
            let n = excluded.entry(why).or_insert(0);
            *n = n.saturating_add(1);
        }
        keys.push(key);
        ders.push(der);
    }
    if let Some(((_, _), t)) = trusts.iter().next() {
        return Err(format!(
            "line {}: trust object without a certificate",
            t.line
        ));
    }
    if roots.is_empty() {
        return Err("no roots".into());
    }
    Ok(Table {
        roots,
        certificates: certs.len(),
        excluded,
        with_distrust_after,
    })
}

/// The DER is one SEQUENCE whose length covers the whole value.
fn check_der(der: &[u8]) -> Result<(), String> {
    let mut it = der.iter().copied();
    if it.next() != Some(0x30) {
        return Err("certificate is not a DER SEQUENCE".into());
    }
    let first = it.next().ok_or("certificate is truncated")?;
    let (len, header) = if first < 0x80 {
        (usize::from(first), 2usize)
    } else {
        let n = usize::from(first & 0x7f);
        if n == 0 || n > 3 {
            return Err("unsupported certificate length form".into());
        }
        let mut len = 0usize;
        for _ in 0..n {
            let b = it.next().ok_or("certificate is truncated")?;
            len = len.saturating_mul(256).saturating_add(usize::from(b));
        }
        (len, n.saturating_add(2))
    };
    if header.saturating_add(len) != der.len() {
        return Err("certificate length does not cover the value".into());
    }
    Ok(())
}

/// A `CKA_NSS_SERVER_DISTRUST_AFTER` value: thirteen octets of `UTCTime`
/// text, `YYMMDDHHMMSSZ`.
fn utc_time(bytes: &[u8]) -> Result<String, String> {
    let ok = bytes.len() == 13
        && bytes.last() == Some(&b'Z')
        && bytes.iter().take(12).all(u8::is_ascii_digit);
    if !ok {
        return Err(format!(
            "CKA_NSS_SERVER_DISTRUST_AFTER is not YYMMDDHHMMSSZ: {bytes:?}"
        ));
    }
    Ok(String::from_utf8_lossy(bytes).into_owned())
}

/// A Rust string literal for ASCII text, escaping everything else.
fn literal(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' | '\\' => {
                out.push('\\');
                out.push(c);
            }
            ' '..='~' => out.push(c),
            _ => {
                let _ = write!(out, "\\u{{{:x}}}", u32::from(c));
            }
        }
    }
    out.push('"');
    out
}

fn generate(text: &str) -> Result<String, String> {
    let t = table(text)?;
    let mut out = String::new();
    out.push_str(HEADER);
    let _ = writeln!(
        out,
        "// Counts (from certdata.txt): {} certificates; {} in the table, {} of those with a\n\
         // server distrust-after date. Left out:",
        t.certificates,
        t.roots.len(),
        t.with_distrust_after
    );
    for (why, n) in &t.excluded {
        let _ = writeln!(out, "//   {n}: {}", why.describe());
    }
    out.push('\n');
    out.push_str("use super::Root;\n\n");
    let _ = writeln!(
        out,
        "/// The roots, in `certdata.txt` order.\npub static ROOTS: [Root; {}] = [",
        t.roots.len()
    );
    for r in &t.roots {
        out.push_str("    Root {\n");
        let _ = writeln!(out, "        label: {},", literal(&r.label));
        out.push_str("        sha256: [");
        for (i, b) in r.sha256.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            let _ = write!(out, "0x{b:02x}");
        }
        out.push_str("],\n");
        match &r.distrust_after {
            Some(d) => {
                let _ = writeln!(out, "        server_distrust_after: Some({}),", literal(d));
            }
            None => out.push_str("        server_distrust_after: None,\n"),
        }
        out.push_str("        der: &[\n");
        for chunk in r.der.chunks(16) {
            out.push_str("            ");
            for b in chunk {
                let _ = write!(out, "0x{b:02x}, ");
            }
            out.truncate(out.trim_end().len());
            out.push('\n');
        }
        out.push_str("        ],\n    },\n");
    }
    out.push_str("];\n");
    Ok(out)
}

const HEADER: &str = "\
//! The root certificate table, generated from NSS's `certdata.txt`.
//!
// @generated by `cargo xtask tables` (xtask/src/roots.rs) from
// crates/clazel-x509/data/nss-0a2b0c75/ (the nss-dev/nss commit and the
// SHA-256 of the file are in SOURCE.md there). Do not edit: `cargo xtask
// check` fails if this differs from what the generator produces.
//
// What the generator derives (the crate's README repeats it):
// - A row is a CKO_CERTIFICATE object whose CKO_NSS_TRUST object (the one
//   with the same CKA_ISSUER and CKA_SERIAL_NUMBER) has
//   CKA_TRUST_SERVER_AUTH CK_TRUST CKT_NSS_TRUSTED_DELEGATOR. Every other
//   certificate is left out: CKT_NSS_MUST_VERIFY_TRUST (which includes the
//   e-mail-only and code-signing-only roots) and CKT_NSS_NOT_TRUSTED. Any other
//   trust value stops the generator.
// - `der` is CKA_VALUE, `label` is CKA_LABEL, `sha256` is the SHA-256 of
//   `der` (computed by the generator and checked against NSS's
//   `# Fingerprint (SHA-256)` comment).
// - CKA_NSS_SERVER_DISTRUST_AFTER is carried, not applied: `None` for
//   CK_FALSE, otherwise `Some` of the UTCTime text (YYMMDDHHMMSSZ). Whether a
//   root is still trusted for a leaf issued after that date is the verifier's
//   decision, not the table's.
// - Rows keep the order of certdata.txt. Checked when generating: each
//   certificate has exactly one trust object and each trust object one
//   certificate, with equal labels; no two certificates share an issuer and
//   serial or a DER encoding; each DER value is one SEQUENCE whose length
//   covers it.
//
";

#[cfg(test)]
mod tests {
    use super::{decode_octal, hex, sha256, utc_time};

    #[test]
    fn sha256_known_answers() {
        // FIPS 180-4 examples and the NIST two-block message.
        assert_eq!(
            hex(&sha256(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex(&sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hex(&sha256(
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
            )),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn octal_escapes() {
        assert_eq!(
            decode_octal("\\060\\202\\377", 1),
            Ok(vec![0x30, 0x82, 0xff])
        );
        assert!(decode_octal("\\400", 1).is_err());
        assert!(decode_octal("\\08", 1).is_err());
        assert!(decode_octal("x", 1).is_err());
    }

    #[test]
    fn distrust_after_format() {
        assert_eq!(utc_time(b"241130235959Z"), Ok("241130235959Z".to_owned()));
        assert!(utc_time(b"2411302359Z").is_err());
        assert!(utc_time(b"24113023595aZ").is_err());
    }
}
