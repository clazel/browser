//! Wycheproof `rsa_signature_*_test.json` (class `RsassaPkcs1Verify`): RSA
//! PKCS#1 v1.5 signature verification vectors, as a table of keys and a
//! table of (message, signature, expected result, flags) cases.
//!
//! Each file has `algorithm` (`RSASSA-PKCS1-v1_5`), `numberOfTests`, and
//! `testGroups`, one per public key: `publicKey` with `modulus` and
//! `publicExponent` as hex, `sha`, `type` (`RsassaPkcs1Verify`) and `tests`,
//! each with `tcId`, `comment`, `flags`, `msg` and `sig` as hex and `result`
//! (`valid`, `invalid` or `acceptable`). The converter checks all of that
//! and that `numberOfTests` is the number of tests found, so an upstream
//! change of shape fails the conversion instead of changing what the table
//! means. The table records the file's own `numberOfTests`, which the
//! conformance test uses as the independent count of each suite.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "rsa_signature_2048_sha256_test.json",
    "rsa_signature_2048_sha384_test.json",
    "rsa_signature_3072_sha256_test.json",
    "rsa_signature_4096_sha512_test.json",
];

struct Key {
    file: String,
    group: usize,
    key_size: u64,
    sha: String,
    modulus: String,
    exponent: String,
}

struct Case {
    key: usize,
    tc_id: u64,
    result: String,
    flags: Vec<String>,
    comment: String,
    msg: String,
    sig: String,
}

fn hex(v: &Value, what: &str) -> Result<String, String> {
    let s = v.as_str().ok_or_else(|| format!("{what}: not a string"))?;
    if !s.len().is_multiple_of(2) || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("{what}: not even-length hex: {s:?}"));
    }
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
        if text(&json, "algorithm", file)? != "RSASSA-PKCS1-v1_5" {
            return Err(format!("{file}: algorithm is not RSASSA-PKCS1-v1_5"));
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
            if text(g, "type", &at)? != "RsassaPkcs1Verify" {
                return Err(format!("{at}: type is not RsassaPkcs1Verify"));
            }
            let pk = g
                .get("publicKey")
                .ok_or_else(|| format!("{at}: no publicKey"))?;
            let key_size = g
                .get("keySize")
                .and_then(Value::as_u64)
                .ok_or_else(|| format!("{at}: no keySize"))?;
            keys.push(Key {
                file: (*file).to_owned(),
                group: gi,
                key_size,
                sha: text(g, "sha", &at)?.to_owned(),
                modulus: hex(
                    pk.get("modulus").unwrap_or(&Value::Null),
                    &format!("{at}: modulus"),
                )?,
                exponent: hex(
                    pk.get("publicExponent").unwrap_or(&Value::Null),
                    &format!("{at}: publicExponent"),
                )?,
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
                cases.push(Case {
                    key,
                    tc_id,
                    result: result.to_owned(),
                    flags,
                    comment: text(t, "comment", &at)?.to_owned(),
                    msg: hex(t.get("msg").unwrap_or(&Value::Null), &format!("{at}: msg"))?,
                    sig: hex(t.get("sig").unwrap_or(&Value::Null), &format!("{at}: sig"))?,
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
        "// @generated by `cargo xtask testdata` from tests/data/wycheproof-rsa-pkcs1/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wycheproof_rsa.rs) produces.\n\
         // Source, commit and license: tests/data/wycheproof-rsa-pkcs1/SOURCE.md.\n\
         // Octet strings are lower-case hex.\n\
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
            "    Key {{ file: {:?}, group: {}, key_size: {}, sha: {:?}, modulus: {:?}, exponent: {:?} }},",
            k.file, k.group, k.key_size, k.sha, k.modulus, k.exponent
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
            "    Case {{ key: {}, tc_id: {}, result: {:?}, flags: &[{}], comment: {:?}, msg: {:?}, sig: {:?} }},",
            c.key, c.tc_id, c.result, flags, c.comment, c.msg, c.sig
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}
