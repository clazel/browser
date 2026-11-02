//! x509-limbo `limbo.json` (C2SP): path-validation testcases, reduced to two
//! derived artefacts, because the corpus is far too large to become Rust
//! literals (41.8 MB, 30,379 distinct certificates).
//!
//! * `tests/generated/x509_limbo.rs`: a Rust index of the testcases (id,
//!   validation kind, expected result and peer name, validation time,
//!   features, importance) whose certificates are indices into
//! * `tests/generated/x509_limbo_certs.bin`: every distinct certificate as
//!   DER, concatenated in order of first use (leaf, then trust anchors, then
//!   intermediates, per testcase). The index records each one's offset and
//!   length.
//!
//! The PEM text of every `trusted_certs`, `untrusted_intermediates` and
//! `peer_certificate` is decoded here with a small strict base64 decoder of
//! our own (clazel-base64 works on code points under Verus and is not a
//! dependency of xtask). The converter checks the shape it relies on, that
//! testcase ids are unique, that every PEM has exactly one CERTIFICATE block
//! with canonical padded base64, and that every DER starts with a SEQUENCE.
//! A null `validation_time` becomes the empty string in the index, a null
//! `max_chain_depth` becomes `None`. `max_chain_depth`, `key_usage` and
//! `extended_key_usage` are carried because a verdict needs them. Fields the
//! harness does not use (`peer_certificate_key`, CRLs, signature algorithm
//! lists) are not carried over.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &["limbo.json"];

/// Name of the binary artefact beside the generated index.
pub const CERTS_BIN: &str = "x509_limbo_certs.bin";

const BEGIN: &str = "-----BEGIN CERTIFICATE-----";
const END: &str = "-----END CERTIFICATE-----";

struct Case {
    id: String,
    kind: String,
    expected: String,
    peer: (String, String),
    peer_names: Vec<(String, String)>,
    time: String,
    features: Vec<String>,
    importance: String,
    max_chain_depth: Option<u32>,
    key_usage: Vec<String>,
    extended_key_usage: Vec<String>,
    trusted: Vec<usize>,
    intermediates: Vec<usize>,
    leaf: usize,
}

struct Loaded {
    cases: Vec<Case>,
    certs: Vec<Vec<u8>>,
}

fn sextet(b: u8) -> Option<u32> {
    match b {
        b'A'..=b'Z' => Some(u32::from(b).saturating_sub(u32::from(b'A'))),
        b'a'..=b'z' => Some(
            u32::from(b)
                .saturating_sub(u32::from(b'a'))
                .saturating_add(26),
        ),
        b'0'..=b'9' => Some(
            u32::from(b)
                .saturating_sub(u32::from(b'0'))
                .saturating_add(52),
        ),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

/// Strict standard-alphabet base64 with padding and no stray characters.
fn base64(text: &str) -> Result<Vec<u8>, String> {
    let bytes = text.as_bytes();
    if bytes.is_empty() || !bytes.len().is_multiple_of(4) {
        return Err("base64 length is not a positive multiple of 4".to_owned());
    }
    let mut out = Vec::new();
    let (groups, _) = bytes.as_chunks::<4>();
    let last = groups.len().saturating_sub(1);
    for (i, g) in groups.iter().enumerate() {
        let pad = g.iter().rev().take_while(|&&b| b == b'=').count();
        if pad > 2 || (pad > 0 && i != last) {
            return Err("misplaced base64 padding".to_owned());
        }
        let mut acc = 0u32;
        for &b in g.iter().take(4usize.saturating_sub(pad)) {
            acc = acc
                .saturating_mul(64)
                .saturating_add(sextet(b).ok_or("bad base64 digit")?);
        }
        acc = acc
            .checked_shl(
                u32::try_from(pad)
                    .map_err(|e| e.to_string())?
                    .saturating_mul(6),
            )
            .ok_or("shift")?;
        let b3 = acc.to_be_bytes();
        let keep = 3usize.saturating_sub(pad);
        out.extend(b3.iter().skip(1).take(keep));
        // Canonical: the bits below the kept ones must be zero.
        let low_mask = match pad {
            1 => 0xff,
            2 => 0xffff,
            _ => 0,
        };
        if acc & low_mask != 0 {
            return Err("non-canonical base64 padding bits".to_owned());
        }
    }
    Ok(out)
}

fn pem_to_der(pem: &str, at: &str) -> Result<Vec<u8>, String> {
    let t = pem.trim();
    let body = t
        .strip_prefix(BEGIN)
        .and_then(|r| r.strip_suffix(END))
        .ok_or_else(|| format!("{at}: not exactly one CERTIFICATE PEM block"))?;
    if body.contains("-----") {
        return Err(format!("{at}: more than one PEM block"));
    }
    let joined: String = body.split_whitespace().collect();
    let der = base64(&joined).map_err(|e| format!("{at}: {e}"))?;
    if der.first() != Some(&0x30) {
        return Err(format!("{at}: DER does not start with a SEQUENCE"));
    }
    Ok(der)
}

fn text<'a>(v: &'a Value, key: &str, at: &str) -> Result<&'a str, String> {
    v.get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{at}: no string {key:?}"))
}

fn strings(v: &Value, key: &str, at: &str) -> Result<Vec<String>, String> {
    v.get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{at}: no array {key:?}"))?
        .iter()
        .map(|s| {
            s.as_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("{at}: {key:?} holds a non-string"))
        })
        .collect()
}

fn peer(v: &Value, at: &str) -> Result<(String, String), String> {
    match v {
        Value::Null => Ok((String::new(), String::new())),
        Value::Object(_) => Ok((
            text(v, "kind", at)?.to_owned(),
            text(v, "value", at)?.to_owned(),
        )),
        _ => Err(format!("{at}: peer name is neither null nor an object")),
    }
}

fn load(dir: &Path) -> Result<Loaded, String> {
    let path = dir.join("limbo.json");
    let raw = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let json: Value = serde_json::from_str(&raw).map_err(|e| format!("limbo.json: {e}"))?;
    if json.get("version").and_then(Value::as_u64) != Some(1) {
        return Err("limbo.json: version is not 1".to_owned());
    }
    let tests = json
        .get("testcases")
        .and_then(Value::as_array)
        .ok_or("limbo.json: no testcases")?;
    let mut certs: Vec<Vec<u8>> = Vec::new();
    let mut seen: HashMap<Vec<u8>, usize> = HashMap::new();
    let mut ids: HashMap<String, ()> = HashMap::new();
    let mut cases = Vec::new();
    let mut intern = |der: Vec<u8>| -> usize {
        if let Some(&i) = seen.get(&der) {
            return i;
        }
        let i = certs.len();
        seen.insert(der.clone(), i);
        certs.push(der);
        i
    };
    for t in tests {
        let id = text(t, "id", "testcase")?.to_owned();
        let at = format!("testcase {id}");
        if ids.insert(id.clone(), ()).is_some() {
            return Err(format!("{at}: duplicate id"));
        }
        let kind = text(t, "validation_kind", &at)?.to_owned();
        if !["SERVER", "CLIENT"].contains(&kind.as_str()) {
            return Err(format!("{at}: unknown validation_kind {kind:?}"));
        }
        let expected = text(t, "expected_result", &at)?.to_owned();
        if !["SUCCESS", "FAILURE"].contains(&expected.as_str()) {
            return Err(format!("{at}: unknown expected_result {expected:?}"));
        }
        let leaf_pem = text(t, "peer_certificate", &at)?;
        let leaf = intern(pem_to_der(leaf_pem, &format!("{at}: peer_certificate"))?);
        let mut trusted = Vec::new();
        for p in strings(t, "trusted_certs", &at)? {
            trusted.push(intern(pem_to_der(&p, &format!("{at}: trusted_certs"))?));
        }
        let mut intermediates = Vec::new();
        for p in strings(t, "untrusted_intermediates", &at)? {
            intermediates.push(intern(pem_to_der(&p, &format!("{at}: intermediate"))?));
        }
        let mut peer_names = Vec::new();
        for n in t
            .get("expected_peer_names")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("{at}: no expected_peer_names"))?
        {
            peer_names.push(peer(n, &at)?);
        }
        cases.push(Case {
            peer: peer(t.get("expected_peer_name").unwrap_or(&Value::Null), &at)?,
            peer_names,
            time: match t.get("validation_time") {
                Some(Value::Null) => String::new(),
                _ => text(t, "validation_time", &at)?.to_owned(),
            },
            features: strings(t, "features", &at)?,
            importance: text(t, "importance", &at)?.to_owned(),
            max_chain_depth: match t.get("max_chain_depth") {
                Some(Value::Null) | None => None,
                Some(v) => Some(
                    v.as_u64()
                        .and_then(|n| u32::try_from(n).ok())
                        .ok_or_else(|| format!("{at}: max_chain_depth is not a u32"))?,
                ),
            },
            key_usage: strings(t, "key_usage", &at)?,
            extended_key_usage: strings(t, "extended_key_usage", &at)?,
            id,
            kind,
            expected,
            trusted,
            intermediates,
            leaf,
        });
    }
    Ok(Loaded { cases, certs })
}

fn list<T: std::fmt::Display>(items: &[T]) -> String {
    items
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

/// The generated Rust index.
pub fn convert(dir: &Path) -> Result<String, String> {
    let l = load(dir)?;
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/x509-limbo/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/x509_limbo.rs) produces.\n\
         // Source, commit and license: tests/data/x509-limbo/SOURCE.md.\n\
         // Certificates are in tests/generated/x509_limbo_certs.bin.\n\
         /// Number of testcases in `limbo.json`.\n",
    );
    writeln!(out, "const TESTCASE_COUNT: usize = {};", l.cases.len()).map_err(|e| e.to_string())?;
    out.push_str("/// (offset, length) of each distinct certificate in the binary file.\n");
    out.push_str("const CERT_SPANS: &[(u32, u32)] = &[\n");
    let mut off = 0usize;
    for c in &l.certs {
        writeln!(out, "    ({off}, {}),", c.len()).map_err(|e| e.to_string())?;
        off = off
            .checked_add(c.len())
            .ok_or("certificate bytes overflow")?;
    }
    out.push_str("];\nconst CASES: &[Case] = &[\n");
    for c in &l.cases {
        let names = c
            .peer_names
            .iter()
            .map(|(k, v)| format!("({k:?}, {v:?})"))
            .collect::<Vec<_>>()
            .join(", ");
        let features = c
            .features
            .iter()
            .map(|f| format!("{f:?}"))
            .collect::<Vec<_>>()
            .join(", ");
        let quoted = |items: &[String]| {
            items
                .iter()
                .map(|f| format!("{f:?}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let depth = match c.max_chain_depth {
            Some(n) => format!("Some({n})"),
            None => "None".to_owned(),
        };
        writeln!(
            out,
            "    Case {{ id: {:?}, kind: {:?}, expected: {:?}, peer: ({:?}, {:?}), peer_names: &[{}], time: {:?}, features: &[{}], importance: {:?}, max_chain_depth: {}, key_usage: &[{}], extended_key_usage: &[{}], trusted: &[{}], intermediates: &[{}], leaf: {} }},",
            c.id, c.kind, c.expected, c.peer.0, c.peer.1, names, c.time, features, c.importance,
            depth, quoted(&c.key_usage), quoted(&c.extended_key_usage),
            list(&c.trusted), list(&c.intermediates), c.leaf
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}

/// The binary certificate file.
pub fn convert_certs(dir: &Path) -> Result<Vec<u8>, String> {
    Ok(load(dir)?.certs.concat())
}

#[cfg(test)]
mod tests {
    use super::{base64, pem_to_der};

    #[test]
    fn base64_is_strict() {
        assert_eq!(base64("TWFu"), Ok(b"Man".to_vec()));
        assert_eq!(base64("TWE="), Ok(b"Ma".to_vec()));
        assert_eq!(base64("TQ=="), Ok(b"M".to_vec()));
        assert!(base64("TWF").is_err());
        assert!(base64("TWF=u===").is_err());
        assert!(base64("TQ==TQ==").is_err());
        assert!(base64("TR==").is_err(), "non-zero padding bits");
        assert!(base64("T!Fu").is_err());
    }

    #[test]
    fn pem_needs_one_certificate_block_with_a_sequence() {
        let ok = format!("{}\nMAA=\n{}\n", super::BEGIN, super::END);
        assert_eq!(pem_to_der(&ok, "t"), Ok(vec![0x30, 0x00]));
        assert!(pem_to_der("MAA=", "t").is_err());
        let two = format!("{ok}{ok}");
        assert!(pem_to_der(&two, "t").is_err());
        let not_seq = format!("{}\nAQA=\n{}", super::BEGIN, super::END);
        assert!(pem_to_der(&not_seq, "t").is_err());
    }
}
