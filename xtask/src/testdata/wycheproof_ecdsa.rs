//! Wycheproof `ecdsa_secp384r1_*_test.json` (class `EcdsaVerify`): ECDSA
//! P-384 signature verification vectors with DER-encoded signatures, as a
//! table of keys and a table of (digest, signature, expected result, flags)
//! cases.
//!
//! Each file has `algorithm` (`ECDSA`), `numberOfTests`, and `testGroups`,
//! one per public key: `publicKey` with `curve` (`secp384r1`) and
//! `uncompressed` (the 97-octet ECPoint as hex), `sha`, `type`
//! (`EcdsaVerify`) and `tests`, each with `tcId`, `comment`, `flags`, `msg`
//! and `sig` as hex (`sig` is a DER `Ecdsa-Sig-Value`, possibly damaged) and
//! `result` (`valid`, `invalid` or `acceptable`). The converter checks all of
//! that, and that `numberOfTests` is the number of tests found.
//!
//! The verifier takes a digest, not a message, so the converter hashes `msg`
//! with the group's `sha` (see `hash.rs`). The signature stays DER: the test
//! parses it with `clazel-der`, so the malformed encodings are decided by
//! our own decoder.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

use super::hash;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "ecdsa_secp384r1_sha256_test.json",
    "ecdsa_secp384r1_sha384_test.json",
    "ecdsa_secp384r1_sha512_test.json",
];

struct Key {
    file: String,
    group: usize,
    sha: String,
    point: String,
}

struct Case {
    key: usize,
    tc_id: u64,
    result: String,
    flags: Vec<String>,
    comment: String,
    digest: String,
    sig: String,
}

fn hex(v: Option<&Value>, what: &str) -> Result<String, String> {
    let s = v
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{what}: not a string"))?;
    hash::from_hex(s).map_err(|e| format!("{what}: {e}"))?;
    Ok(s.to_ascii_lowercase())
}

fn text<'a>(v: &'a Value, key: &str, what: &str) -> Result<&'a str, String> {
    v.get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{what}: no string {key:?}"))
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let mut keys = Vec::new();
    let mut cases = Vec::new();
    let mut counts = Vec::new();
    for file in FILES {
        let path = dir.join(file);
        let raw = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let json: Value =
            serde_json::from_str(&raw).map_err(|e| format!("{file}: not JSON: {e}"))?;
        if text(&json, "algorithm", file)? != "ECDSA" {
            return Err(format!("{file}: algorithm is not ECDSA"));
        }
        let declared = json
            .get("numberOfTests")
            .and_then(Value::as_u64)
            .ok_or_else(|| format!("{file}: no numberOfTests"))?;
        let groups = json
            .get("testGroups")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("{file}: no testGroups"))?;
        let mut found = 0u64;
        for (gi, g) in groups.iter().enumerate() {
            let at = format!("{file}: group {gi}");
            if text(g, "type", &at)? != "EcdsaVerify" {
                return Err(format!("{at}: type is not EcdsaVerify"));
            }
            let pk = g
                .get("publicKey")
                .ok_or_else(|| format!("{at}: no publicKey"))?;
            if text(pk, "curve", &at)? != "secp384r1" {
                return Err(format!("{at}: curve is not secp384r1"));
            }
            let sha = text(g, "sha", &at)?;
            if !["SHA-256", "SHA-384", "SHA-512"].contains(&sha) {
                return Err(format!("{at}: unexpected hash {sha:?}"));
            }
            let point = hex(pk.get("uncompressed"), &format!("{at}: uncompressed"))?;
            keys.push(Key {
                file: (*file).to_owned(),
                group: gi,
                sha: sha.to_owned(),
                point,
            });
            let key = keys.len().saturating_sub(1);
            let tests = g
                .get("tests")
                .and_then(Value::as_array)
                .ok_or_else(|| format!("{at}: no tests"))?;
            for t in tests {
                let tc_id = t
                    .get("tcId")
                    .and_then(Value::as_u64)
                    .ok_or_else(|| format!("{at}: test without tcId"))?;
                let at = format!("{file}: tcId {tc_id}");
                let result = text(t, "result", &at)?;
                if !["valid", "invalid", "acceptable"].contains(&result) {
                    return Err(format!("{at}: unknown result {result:?}"));
                }
                let flags = t
                    .get("flags")
                    .and_then(Value::as_array)
                    .ok_or_else(|| format!("{at}: no flags"))?
                    .iter()
                    .map(|f| {
                        f.as_str()
                            .map(str::to_owned)
                            .ok_or_else(|| format!("{at}: flag is not a string"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let msg = hash::from_hex(&hex(t.get("msg"), &format!("{at}: msg"))?)?;
                cases.push(Case {
                    key,
                    tc_id,
                    result: result.to_owned(),
                    flags,
                    comment: text(t, "comment", &at)?.to_owned(),
                    digest: hash::to_hex(&hash::digest(sha, &msg)?),
                    sig: hex(t.get("sig"), &format!("{at}: sig"))?,
                });
                found = found.saturating_add(1);
            }
        }
        if found != declared {
            return Err(format!(
                "{file}: numberOfTests is {declared}, found {found} tests"
            ));
        }
        counts.push(((*file).to_owned(), declared));
    }
    render(&keys, &cases, &counts)
}

fn render(keys: &[Key], cases: &[Case], counts: &[(String, u64)]) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/wycheproof-ecdsa-p384/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wycheproof_ecdsa.rs) produces.\n\
         // Source, commit and license: tests/data/wycheproof-ecdsa-p384/SOURCE.md.\n\
         // Octet strings are lower-case hex. `digest` is the hash of the test's\n\
         // `msg` under its group's hash, computed by the converter.\n\
         /// Each file's own `numberOfTests`.\n\
         const NUMBER_OF_TESTS: &[(&str, usize)] = &[\n",
    );
    for (file, n) in counts {
        writeln!(out, "    ({file:?}, {n}),").map_err(|e| e.to_string())?;
    }
    out.push_str("];\n/// One entry per `testGroups` element.\nconst KEYS: &[Key] = &[\n");
    for k in keys {
        writeln!(
            out,
            "    Key {{ file: {:?}, group: {}, sha: {:?}, point: {:?} }},",
            k.file, k.group, k.sha, k.point
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\nconst CASES: &[Case] = &[\n");
    for c in cases {
        let flags = c
            .flags
            .iter()
            .map(|f| format!("{f:?}"))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            out,
            "    Case {{ key: {}, tc_id: {}, result: {:?}, flags: &[{}], comment: {:?}, digest: {:?}, sig: {:?} }},",
            c.key, c.tc_id, c.result, flags, c.comment, c.digest, c.sig
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}
