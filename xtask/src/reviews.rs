//! Spec review log (Phase 0 item 0.8). The log is the table in
//! `docs/SPEC-REVIEWS.md`, which also documents the process.

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

use crate::workspace::{self, Crate};

pub const PATH: &str = "docs/SPEC-REVIEWS.md";
const BEGIN: &str = "<!-- BEGIN REVIEWS";
const END: &str = "<!-- END REVIEWS -->";

/// File names whose contents are trusted rather than proven.
pub const REVIEWABLE: &[&str] = &["spec.rs", "contract.rs", "axioms.rs", "mutations.json"];

/// One review row: the file path (relative to the repo root) and the
/// SHA-256 it had when reviewed.
#[derive(Debug)]
pub struct Row {
    pub file: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Current,
    Stale,
    Missing,
}

/// Review status of one reviewable file.
#[derive(Debug)]
pub struct FileStatus {
    pub file: String,
    pub sha256: String,
    pub status: Status,
}

/// Review status of each crate's reviewable files, keyed by crate name.
pub type ByCrate = BTreeMap<String, Vec<FileStatus>>;

/// Parse the review table between the markers.
pub fn parse(text: &str) -> Result<Vec<Row>, String> {
    let start = text
        .find(BEGIN)
        .ok_or_else(|| format!("{PATH}: no {BEGIN} marker"))?;
    let body = text.get(start..).unwrap_or_default();
    let end = body
        .find(END)
        .ok_or_else(|| format!("{PATH}: no {END} marker"))?;
    let mut rows: Vec<Row> = Vec::new();
    for line in body.get(..end).unwrap_or_default().lines().skip(1) {
        let line = line.trim();
        if !line.starts_with('|') {
            continue;
        }
        let cells: Vec<&str> = line.trim_matches('|').split('|').map(str::trim).collect();
        let [file, sha, reviewer, date, against] = cells.as_slice() else {
            return Err(format!("{PATH}: expected 5 columns in: {line}"));
        };
        if *file == "File" || file.chars().all(|c| c == '-') {
            continue;
        }
        let file = file.trim_matches('`');
        if !(sha.len() == 64 && sha.chars().all(|c| c.is_ascii_hexdigit())) {
            return Err(format!("{PATH}: {file}: SHA-256 must be 64 hex digits"));
        }
        if [reviewer, date, against].iter().any(|c| c.is_empty()) {
            return Err(format!(
                "{PATH}: {file}: reviewer, date and \"reviewed against\" are required"
            ));
        }
        if rows.iter().any(|r| r.file == file) {
            return Err(format!("{PATH}: {file} has more than one row"));
        }
        rows.push(Row {
            file: file.to_owned(),
            sha256: sha.to_ascii_lowercase(),
        });
    }
    Ok(rows)
}

/// SHA-256 of a file, via the system's `sha256sum` or `shasum`, or on Windows
/// `certutil -hashfile`.
pub fn sha256(path: &Path) -> Result<String, String> {
    if cfg!(windows)
        && let Ok(out) = Command::new("certutil")
            .arg("-hashfile")
            .arg(path)
            .arg("SHA256")
            .output()
        && out.status.success()
    {
        // Line 1 names the file, line 2 is the hash (older versions space
        // the bytes), line 3 is the status.
        let text = String::from_utf8_lossy(&out.stdout);
        if let Some(line) = text.lines().nth(1) {
            let hash: String = line.split_whitespace().collect();
            if hash.len() == 64 {
                return Ok(hash.to_ascii_lowercase());
            }
        }
    }
    let attempts: [(&str, &[&str]); 2] = [("sha256sum", &[]), ("shasum", &["-a", "256"])];
    for (tool, args) in attempts {
        if let Ok(out) = Command::new(tool).args(args).arg(path).output()
            && out.status.success()
        {
            let text = String::from_utf8_lossy(&out.stdout);
            if let Some(hash) = text.split_whitespace().next() {
                return Ok(hash.to_ascii_lowercase());
            }
        }
    }
    Err(format!(
        "cannot hash {} (need sha256sum or shasum)",
        path.display()
    ))
}

/// Reviewable files of one crate, as repo-relative paths.
pub fn reviewable_files(c: &Crate) -> Result<Vec<String>, String> {
    let mut files: Vec<String> = workspace::rust_files(&c.dir)?
        .into_iter()
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| REVIEWABLE.contains(&n))
        })
        .map(|p| workspace::relative(&p))
        .collect();
    let mutations = c.dir.join("mutations.json");
    if mutations.is_file() {
        files.push(workspace::relative(&mutations));
    }
    files.sort();
    Ok(files)
}

/// Review status of every reviewable file, per crate, plus problems with
/// the log itself (malformed rows, rows for files that do not exist).
pub fn status(crates: &[Crate]) -> Result<(ByCrate, Vec<String>), String> {
    let text = std::fs::read_to_string(PATH).map_err(|e| format!("{PATH}: {e}"))?;
    let rows = parse(&text)?;
    let mut per_crate = BTreeMap::new();
    let mut seen = Vec::new();
    for c in crates {
        let mut statuses = Vec::new();
        for file in reviewable_files(c)? {
            let hash = sha256(Path::new(&file))?;
            let status = match rows.iter().find(|r| r.file == file) {
                Some(r) if r.sha256 == hash => Status::Current,
                Some(_) => Status::Stale,
                None => Status::Missing,
            };
            seen.push(file.clone());
            statuses.push(FileStatus {
                file,
                sha256: hash,
                status,
            });
        }
        per_crate.insert(c.name.clone(), statuses);
    }
    let problems = rows
        .iter()
        .filter(|r| !seen.contains(&r.file))
        .map(|r| {
            format!(
                "{PATH}: {} is not a reviewable file in any crate (stale row)",
                r.file
            )
        })
        .collect();
    Ok((per_crate, problems))
}

#[cfg(test)]
mod tests {
    use super::parse;

    const SHA: &str = "83cafc50284caea07fa8762df04b00cc0af441f25cdf1631d6c30987c65af446";

    fn wrap(rows: &str) -> String {
        format!(
            "<!-- BEGIN REVIEWS -->\n| File | SHA-256 | Reviewer | Date | Reviewed against |\n\
             |---|---|---|---|---|\n{rows}\n<!-- END REVIEWS -->"
        )
    }

    #[test]
    fn parses_a_row() -> Result<(), String> {
        let rows = parse(&wrap(&format!(
            "| `a/spec.rs` | {SHA} | Ada | 2026-10-19 | Encoding @ dd79434 |"
        )))?;
        assert!(matches!(rows.as_slice(), [r] if r.file == "a/spec.rs" && r.sha256 == SHA));
        Ok(())
    }

    #[test]
    fn rejects_bad_rows() {
        assert!(parse(&wrap("| a | abc | Ada | 2026-10-19 | x |")).is_err());
        assert!(parse(&wrap(&format!("| a | {SHA} |  | 2026-10-19 | x |"))).is_err());
        assert!(
            parse(&wrap(&format!(
                "| a | {SHA} | Ada | d | x |\n| a | {SHA} | Bo | d | x |"
            )))
            .is_err()
        );
        assert!(parse(&wrap(&format!("| a | {SHA} | Ada | d |"))).is_err());
    }
}
