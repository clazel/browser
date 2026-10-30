//! NIST CAVP FIPS 186-4 `SigVer.rsp`: the P-384 sections, as a table of
//! (digest, key, r, s, expected result) cases.
//!
//! The file is a CRLF text file of `#` comments, section headers
//! `[<curve>,<hash>]` and blocks of
//!
//! ```text
//! Msg = <hex>
//! Qx = <hex>
//! Qy = <hex>
//! R = <hex>
//! S = <hex>
//! Result = P (0 )            or   F (<n> - <reason>)
//! ```
//!
//! in that order. Only the sections whose curve is `P-384` are kept. The
//! converter hashes `Msg` with the section's hash (see `hash.rs`), builds the
//! ECPoint `04 || Qx || Qy`, and checks that the number of blocks it kept
//! equals the number of `Result` lines it counted separately in those
//! sections.

use std::fmt::Write as _;
use std::path::Path;

use super::hash;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &["SigVer.rsp"];

struct Case {
    sha: String,
    digest: String,
    key: String,
    r: String,
    s: String,
    pass: bool,
    reason: String,
}

/// The value of `key = value`, if the line starts with `key = `.
fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    line.strip_prefix(key)?.strip_prefix(" = ")
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let path = dir.join("SigVer.rsp");
    let raw = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut cases: Vec<Case> = Vec::new();
    let mut section: Option<(String, String)> = None;
    let mut results_seen = 0usize;
    let mut sections_kept: Vec<String> = Vec::new();
    // Msg, Qx, Qy, R, S of the block being read.
    let mut block: Vec<String> = Vec::new();
    for (n, line) in raw.lines().enumerate() {
        let at = format!("SigVer.rsp:{}", n.saturating_add(1));
        let line = line.trim_end();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(head) = line.strip_prefix('[') {
            let head = head
                .strip_suffix(']')
                .ok_or_else(|| format!("{at}: unterminated section header"))?;
            let (curve, sha) = head
                .split_once(',')
                .ok_or_else(|| format!("{at}: section header without a comma"))?;
            if !block.is_empty() {
                return Err(format!("{at}: section starts inside a block"));
            }
            section = Some((curve.to_owned(), sha.to_owned()));
            if curve == "P-384" {
                sections_kept.push(sha.to_owned());
            }
            continue;
        }
        let Some((curve, sha)) = section.as_ref() else {
            return Err(format!("{at}: data before the first section"));
        };
        let keep = curve == "P-384";
        let order = ["Msg", "Qx", "Qy", "R", "S"];
        if let Some(value) = order.get(block.len()).and_then(|key| field(line, key)) {
            if !value.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err(format!("{at}: not hex: {value:?}"));
            }
            block.push(value.to_ascii_lowercase());
            continue;
        }
        let Some(result) = field(line, "Result") else {
            return Err(format!("{at}: unexpected line {line:?}"));
        };
        if block.len() != order.len() {
            return Err(format!("{at}: Result after {} of 5 fields", block.len()));
        }
        let (pass, reason) = match result.split_once(' ') {
            Some(("P", rest)) if rest.trim() == "(0 )" || rest.trim() == "(0)" => {
                (true, String::new())
            }
            Some(("F", rest)) => {
                let inner = rest
                    .trim()
                    .strip_prefix('(')
                    .and_then(|r| r.strip_suffix(')'))
                    .ok_or_else(|| format!("{at}: bad failure reason {rest:?}"))?;
                (false, inner.trim().to_owned())
            }
            _ => return Err(format!("{at}: unknown Result {result:?}")),
        };
        if keep {
            results_seen = results_seen.saturating_add(1);
            let [msg, qx, qy, r, s] = <[String; 5]>::try_from(std::mem::take(&mut block))
                .map_err(|_| format!("{at}: block is not five fields"))?;
            for (name, v) in [("Qx", &qx), ("Qy", &qy), ("R", &r), ("S", &s)] {
                if v.len() != 96 {
                    return Err(format!("{at}: {name} is {} hex digits, not 96", v.len()));
                }
            }
            let msg_octets = hash::from_hex(&msg).map_err(|e| format!("{at}: Msg: {e}"))?;
            cases.push(Case {
                sha: sha.clone(),
                digest: hash::to_hex(&hash::digest(sha, &msg_octets)?),
                key: format!("04{qx}{qy}"),
                r,
                s,
                pass,
                reason,
            });
        } else {
            block.clear();
        }
    }
    if !block.is_empty() {
        return Err("SigVer.rsp: ends inside a block".to_owned());
    }
    if sections_kept != ["SHA-1", "SHA-224", "SHA-256", "SHA-384", "SHA-512"] {
        return Err(format!("unexpected P-384 sections: {sections_kept:?}"));
    }
    if cases.len() != results_seen {
        return Err(format!(
            "kept {} cases but counted {results_seen} Result lines",
            cases.len()
        ));
    }
    render(&cases)
}

fn render(cases: &[Case]) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/nist-cavp-ecdsa-sigver/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/nist_cavp_sigver.rs) produces.\n\
         // Source and license: tests/data/nist-cavp-ecdsa-sigver/SOURCE.md.\n\
         // Octet strings are lower-case hex. `digest` is the hash of the\n\
         // case's `Msg` under its section's hash, computed by the converter;\n\
         // `key` is `04 || Qx || Qy`; `reason` is NIST's text after `F`.\n\
         const CASES: &[Case] = &[\n",
    );
    for c in cases {
        writeln!(
            out,
            "    Case {{ sha: {:?}, digest: {:?}, key: {:?}, r: {:?}, s: {:?}, pass: {}, reason: {:?} }},",
            c.sha, c.digest, c.key, c.r, c.s, c.pass, c.reason
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}
