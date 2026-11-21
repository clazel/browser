//! `cargo xtask bindings`: the WebIDL parser and the generated interface
//! model of `clazel-webidl` (Phase 7 item 7.12, first slice).
//!
//! The vendored IDL of the DOM, HTML, Fetch, XHR, URL and Storage standards,
//! UI Events and CSSOM (`crates/clazel-webidl/tests/data/webref-idl/`, item
//! 7.1; its `SOURCE.md` names the upstream commit, and `cargo xtask
//! testdata` checks every file's size and SHA-256 against the inventory in
//! `tests/generated/webref_idl.rs`) is read by our own parser (`parser.rs`,
//! following the grammar of WebIDL §2), merged into one model (`resolve.rs`)
//! and written as plain Rust data into
//! `crates/clazel-webidl/src/generated/` (`emit.rs`). The data types are
//! `crates/clazel-webidl/src/model.rs`. Nothing there is engine code: the
//! item's binding glue (conversions, wrappers, overload resolution) comes
//! with `clazel-js`'s embedding API (7.8) and is generated from this model.
//!
//! `cargo xtask bindings` rewrites the files; `check` and `verify` fail if
//! a vendored file is missing from the inventory or differs from it, if any
//! file does not parse, if a reference does not resolve (`resolve.rs`), or
//! if a committed file differs from what this produces.
//!
//! The parser is build tooling, not shipped code, and proves nothing: Tier 0.
//! What it is checked against: the unit tests of `parser.rs` and `lexer.rs`,
//! the test here that every vendored file parses, and `clazel-webidl`'s tests
//! of the generated data.

mod emit;
mod lexer;
mod model;
mod parser;
mod resolve;

use std::path::{Path, PathBuf};

/// The vendored IDL directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-webidl/tests/data/webref-idl";
/// The generated directory, relative to the repository root.
const OUT_DIR: &str = "crates/clazel-webidl/src/generated";

/// Parse every `.idl` file of `dir`, in the order of their names, and merge
/// them.
fn load(dir: &Path) -> Result<resolve::Model, String> {
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(Result::ok)
        .filter_map(|e| e.file_name().into_string().ok())
        .filter(|n| n.ends_with(".idl"))
        .collect();
    names.sort();
    if names.is_empty() {
        return Err(format!("{}: no .idl files", dir.display()));
    }
    let mut files = Vec::new();
    for name in names {
        let path = dir.join(&name);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let defs = parser::parse(&text).map_err(|e| format!("{name}:{e}"))?;
        files.push((name, defs));
    }
    resolve::resolve(&files)
}

/// Compare (or, with `write`, rewrite) the generated files. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let mut notes = Vec::new();
    let model = match load(&PathBuf::from(DATA_DIR)) {
        Ok(m) => m,
        Err(e) => return (vec![format!("{DATA_DIR}: {e}")], notes),
    };
    notes.push(emit::summary(&model));
    let fresh = emit::files(&model);
    let mut problems = Vec::new();
    let out_dir = PathBuf::from(OUT_DIR);
    // A file in the directory that the generator no longer writes is stale.
    if let Ok(entries) = std::fs::read_dir(&out_dir) {
        for e in entries.filter_map(Result::ok) {
            let name = e.file_name().to_string_lossy().into_owned();
            if !fresh.iter().any(|(n, _)| *n == name) {
                let path = e.path();
                if write {
                    match std::fs::remove_file(&path) {
                        Ok(()) => notes.push(format!("{}: removed", path.display())),
                        Err(err) => problems.push(format!("{}: {err}", path.display())),
                    }
                } else {
                    problems.push(format!(
                        "{}: not written by xtask/src/bindings; run `cargo xtask bindings`",
                        path.display()
                    ));
                }
            }
        }
    }
    if write && let Err(e) = std::fs::create_dir_all(&out_dir) {
        problems.push(format!("{OUT_DIR}: {e}"));
        return (problems, notes);
    }
    for (name, text) in &fresh {
        let path = out_dir.join(name);
        let shown = format!("{OUT_DIR}/{name}");
        let current = std::fs::read_to_string(&path).ok();
        if current.as_deref() == Some(text.as_str()) {
            notes.push(format!("{shown}: up to date"));
        } else if write {
            match std::fs::write(&path, text) {
                Ok(()) => notes.push(format!("{shown}: written")),
                Err(e) => problems.push(format!("{shown}: {e}")),
            }
        } else if current.is_none() {
            problems.push(format!("{shown}: missing; run `cargo xtask bindings`"));
        } else {
            problems.push(format!(
                "{shown}: stale (differs from what xtask/src/bindings produces); \
                 run `cargo xtask bindings` and commit the result"
            ));
        }
    }
    (problems, notes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn data_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join(DATA_DIR)
    }

    /// Every vendored file parses on its own, and all of them resolve.
    #[test]
    fn every_vendored_file_parses() {
        let dir = data_dir();
        let mut count = 0usize;
        for e in std::fs::read_dir(&dir)
            .map(|r| r.filter_map(Result::ok).collect::<Vec<_>>())
            .unwrap_or_default()
        {
            let name = e.file_name().to_string_lossy().into_owned();
            if !name.ends_with(".idl") {
                continue;
            }
            let text = std::fs::read_to_string(e.path()).unwrap_or_default();
            let parsed = parser::parse(&text);
            assert!(parsed.is_ok(), "{name}: {:?}", parsed.err());
            assert!(
                parsed.map(|d| !d.is_empty()).unwrap_or(false),
                "{name}: nothing parsed"
            );
            count = count.saturating_add(1);
        }
        assert_eq!(count, 8);
        let model = load(&dir);
        assert!(model.is_ok(), "{:?}", model.err());
    }
}
