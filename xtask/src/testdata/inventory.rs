//! Phase 7 item 7.1: vendored files that later items read as files, not as
//! tables.
//!
//! Four suites need no parser yet, so each is converted into an inventory:
//! every file's path, size and SHA-256.
//!
//! - `wpt-web` (`clazel-web`): the WPT `testharness.js` tests the engine will
//!   run (item 7.15 onward). They are JavaScript, HTML and a few Python
//!   server handlers; the runner that reads them is the engine itself, so
//!   there is nothing to translate until it exists.
//! - `todomvc` (`clazel-web`): three applications that item 7.20 serves.
//! - `webref-idl` (`clazel-webidl`): the IDL that item 7.12's generator
//!   (`cargo xtask bindings`) parses with the IDL parser it will bring. It is
//!   not parsed here: a half-parser in a converter would be a second one to
//!   keep in step with the first.
//! - `ucd-regexp` (`clazel-js-regexp`): the Unicode Character Database files
//!   item 7.10's table generator will read, in the way `unicode.rs` reads the
//!   IDNA ones. This converter also checks them against `SOURCE.md` and
//!   against `clazel-idna`'s copy (see [`convert_ucd`]).
//!
//! The inventory is what makes the vendored tree safe to leave alone: a
//! file added, removed, edited or rewritten (a checkout that changes line
//! endings, say) makes the committed inventory stale, and `check` fails. A
//! suite directory is a tree here (`testdata.rs`'s `TREE_SUITES`): any
//! path may exist under the listed roots, and only the inventory says which
//! do.

use std::fmt::Write as _;
use std::path::Path;

use sha2::{Digest, Sha256};

use super::hash::to_hex;

/// The directories and files of the WPT checkout that exit criterion 2 of
/// phase-7.md lists, as paths from its root, plus `testharness.js`.
pub const WPT_WEB_ROOTS: &[&str] = &[
    "dom/nodes",
    "dom/events",
    "dom/collections",
    "html/webappapis/timers",
    "html/webappapis/microtask-queuing",
    "html/semantics/scripting-1",
    "fetch/api/basic",
    "fetch/api/cors",
    "xhr",
    "resources/testharness.js",
];

/// TodoMVC's three implementations and the behaviour spec they share.
pub const TODOMVC_ROOTS: &[&str] = &[
    "examples/javascript-es6",
    "examples/react",
    "examples/vue",
    "app-spec.md",
];

/// The WebIDL files, one per standard, extracted by Reffy into w3c/webref.
pub const WEBREF_IDL_FILES: &[&str] = &[
    "cssom.idl",
    "dom.idl",
    "fetch.idl",
    "html.idl",
    "storage.idl",
    "uievents.idl",
    "url.idl",
    "xhr.idl",
];

/// The Unicode Character Database files RegExp needs, by what they give it.
pub const UCD_FILES: &[&str] = &[
    // General_Category: `\p{Lu}`, `\p{Cn}` (UnicodeData.txt lists ranges by
    // their first and last code point; the derived file lists every one) and
    // the simple case mappings.
    "UnicodeData.txt",
    "DerivedGeneralCategory.txt",
    // The names, and the aliases `\p{Script=Latn}` and `\p{gc=Lu}` resolve.
    "PropertyAliases.txt",
    "PropertyValueAliases.txt",
    // Script and Script_Extensions: `\p{sc=..}`, `\p{scx=..}`.
    "Scripts.txt",
    "ScriptExtensions.txt",
    // The binary properties of ECMA-262 table 69.
    "PropList.txt",
    "DerivedCoreProperties.txt",
    "DerivedBinaryProperties.txt",
    "DerivedNormalizationProps.txt",
    "emoji-data.txt",
    // Case folding for `/iu` and `/iv` (Canonicalize, 22.2.2.7.3) and the
    // full upper-casing of `toUppercase` for `/i` without `u`.
    "CaseFolding.txt",
    "SpecialCasing.txt",
    // The properties of strings of `/v`: `\p{RGI_Emoji}` and its parts.
    "emoji-sequences.txt",
    "emoji-zwj-sequences.txt",
];

/// The files of `clazel-idna`'s Unicode data that `ucd-regexp` repeats, so
/// that the two crates cannot drift to different Unicode versions.
const IDNA_DATA: &str = "crates/clazel-idna/data/unicode-18.0.0";
const SHARED_WITH_IDNA: &[&str] = &["UnicodeData.txt", "DerivedNormalizationProps.txt"];

/// One vendored file.
struct Entry {
    path: String,
    size: usize,
    sha256: String,
}

/// Every file under `dir`, by path with `/` separators, sorted bytewise.
/// `SOURCE.md` at the root is the suite's own and is left out.
fn walk(dir: &Path, prefix: &str, out: &mut Vec<Entry>) -> Result<(), String> {
    let entries = std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("{}: {e}", dir.display()))?;
        let name = entry
            .file_name()
            .into_string()
            .map_err(|n| format!("{}: file name {n:?} is not UTF-8", dir.display()))?;
        let path = if prefix.is_empty() {
            name.clone()
        } else {
            format!("{prefix}/{name}")
        };
        let kind = entry.file_type().map_err(|e| format!("{path}: {e}"))?;
        if kind.is_dir() {
            walk(&entry.path(), &path, out)?;
        } else if kind.is_file() {
            if path == "SOURCE.md" {
                continue;
            }
            let bytes = std::fs::read(entry.path()).map_err(|e| format!("{path}: {e}"))?;
            out.push(Entry {
                size: bytes.len(),
                sha256: to_hex(&Sha256::digest(&bytes)),
                path,
            });
        } else {
            return Err(format!(
                "{path}: a link or special file; vendor regular files only"
            ));
        }
    }
    Ok(())
}

/// Whether `path` is `root` or lies under it.
fn under(path: &str, root: &str) -> bool {
    path == root
        || path
            .strip_prefix(root)
            .is_some_and(|rest| rest.starts_with('/'))
}

/// The inventory of `dir`, every file of which must lie under one of
/// `roots` (the suite's own `LICENSE.md` is always allowed). Every root must
/// hold at least one file.
fn inventory(dir: &Path, roots: &[&str]) -> Result<Vec<Entry>, String> {
    let mut files = Vec::new();
    walk(dir, "", &mut files)?;
    files.sort_by(|a, b| a.path.cmp(&b.path));
    for f in &files {
        if f.path != "LICENSE.md" && !roots.iter().any(|r| under(&f.path, r)) {
            return Err(format!(
                "{}: outside the roots this suite vendors ({}); remove it or add its root to xtask/src/testdata/inventory.rs",
                f.path,
                roots.join(", ")
            ));
        }
    }
    for r in roots {
        if !files.iter().any(|f| under(&f.path, r)) {
            return Err(format!(
                "{r}: listed in xtask/src/testdata/inventory.rs but not vendored"
            ));
        }
    }
    if !files.iter().any(|f| f.path == "LICENSE.md") {
        return Err("LICENSE.md: missing".to_owned());
    }
    Ok(files)
}

/// The generated Rust file for `files`.
fn render(suite: &str, converter: &str, what: &str, files: &[Entry]) -> Result<String, String> {
    let mut out = String::new();
    let total: usize = files.iter().map(|f| f.size).sum();
    let w = |r: std::fmt::Result| r.map_err(|e| e.to_string());
    w(write!(
        out,
        "// @generated by `cargo xtask testdata` from tests/data/{suite}/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/{converter}.rs) produces.\n\
         // Source, commit and license: tests/data/{suite}/SOURCE.md.\n\
         //\n\
         // {what}\n\
         // {} files, {total} bytes. Nothing here is parsed yet; see the converter's\n\
         // header for why. Paths are relative to tests/data/{suite}/.\n\
         \n\
         /// One vendored file.\n\
         #[derive(Debug, Clone, Copy, PartialEq, Eq)]\n\
         pub struct File {{\n\
         \x20   /// Its path under the suite directory, with `/` separators.\n\
         \x20   pub path: &'static str,\n\
         \x20   /// Its size in bytes.\n\
         \x20   pub size: u64,\n\
         \x20   /// Its SHA-256, in lower-case hex.\n\
         \x20   pub sha256: &'static str,\n\
         }}\n\
         \n\
         /// Every vendored file, sorted by path.\n\
         pub const FILES: &[File] = &[\n",
        files.len()
    ))?;
    for f in files {
        w(writeln!(
            out,
            "    File {{ path: {:?}, size: {}, sha256: \"{}\" }},",
            f.path, f.size, f.sha256
        ))?;
    }
    out.push_str("];\n");
    Ok(out)
}

/// `wpt-web`: the WPT tests, as an inventory.
pub fn convert_wpt_web(dir: &Path) -> Result<String, String> {
    let files = inventory(dir, WPT_WEB_ROOTS)?;
    render(
        "wpt-web",
        "inventory",
        "WPT testharness.js tests (phase-7.md exit criterion 2), run by the engine in items 7.15 onward.",
        &files,
    )
}

/// `todomvc`: the three applications, as an inventory.
pub fn convert_todomvc(dir: &Path) -> Result<String, String> {
    let files = inventory(dir, TODOMVC_ROOTS)?;
    render(
        "todomvc",
        "inventory",
        "TodoMVC's vanilla, React and Vue implementations, served by item 7.20's fixtures.",
        &files,
    )
}

/// `webref-idl`: the IDL files, as an inventory.
pub fn convert_webref_idl(dir: &Path) -> Result<String, String> {
    let files = inventory(dir, WEBREF_IDL_FILES)?;
    render(
        "webref-idl",
        "inventory",
        "WebIDL extracted from the standards, read by item 7.12's bindings generator.",
        &files,
    )
}

/// The `SHA-256: <hash> <file>` lines of a `SOURCE.md`, as (file, hash).
fn listed_hashes(source: &str) -> Vec<(String, String)> {
    source
        .lines()
        .filter_map(|l| {
            let rest = l.trim().strip_prefix("SHA-256:")?.trim();
            let (hash, name) = rest.split_once(char::is_whitespace)?;
            Some((
                name.trim().trim_matches('`').to_owned(),
                hash.to_ascii_lowercase(),
            ))
        })
        .collect()
}

/// `ucd-regexp`: the Unicode files, as an inventory, after checking that
///
/// - `SOURCE.md` lists each file with the SHA-256 it has (the hashes are
///   in `SOURCE.md` as well as in the table, as in `clazel-idna`'s data, so
///   that a reader of the directory sees them), and lists nothing else;
/// - each file says it is of Unicode 18.0 (its header names the version),
///   except `UnicodeData.txt`, which has no header and is covered next;
/// - `UnicodeData.txt` and `DerivedNormalizationProps.txt` are byte for byte
///   the ones `clazel-idna` vendors, so the two crates agree on the version.
pub fn convert_ucd(dir: &Path) -> Result<String, String> {
    let files = inventory(dir, UCD_FILES)?;
    let source =
        std::fs::read_to_string(dir.join("SOURCE.md")).map_err(|e| format!("SOURCE.md: {e}"))?;
    let listed = listed_hashes(&source);
    for f in files.iter().filter(|f| f.path != "LICENSE.md") {
        match listed.iter().find(|(n, _)| *n == f.path) {
            Some((_, h)) if *h == f.sha256 => {}
            Some((_, h)) => {
                return Err(format!(
                    "{}: SHA-256 {} differs from SOURCE.md ({h})",
                    f.path, f.sha256
                ));
            }
            None => return Err(format!("SOURCE.md: no \"SHA-256: <hash> {}\" line", f.path)),
        }
        if f.path != "UnicodeData.txt" {
            let text = std::fs::read_to_string(dir.join(&f.path))
                .map_err(|e| format!("{}: {e}", f.path))?;
            let head: String = text.lines().take(40).collect::<Vec<_>>().join("\n");
            if !(head.contains("18.0.0") || head.contains("Version: 18.0")) {
                return Err(format!("{}: its header does not say Unicode 18.0", f.path));
            }
        }
    }
    if let Some((n, _)) = listed
        .iter()
        .find(|(n, _)| !files.iter().any(|f| f.path == *n))
    {
        return Err(format!("SOURCE.md: lists {n}, which is not vendored"));
    }
    for name in SHARED_WITH_IDNA {
        let ours = files
            .iter()
            .find(|f| f.path == *name)
            .ok_or_else(|| format!("{name}: not vendored"))?;
        let theirs = std::fs::read(Path::new(IDNA_DATA).join(name))
            .map_err(|e| format!("{IDNA_DATA}/{name}: {e}"))?;
        if to_hex(&Sha256::digest(&theirs)) != ours.sha256 {
            return Err(format!(
                "{name}: differs from {IDNA_DATA}/{name}; the two crates must use one Unicode version"
            ));
        }
    }
    render(
        "ucd-regexp",
        "inventory",
        "Unicode 18.0.0 Character Database files for item 7.10's tables.",
        &files,
    )
}

#[cfg(test)]
mod tests {
    use super::{under, walk};

    #[test]
    fn roots_match_whole_path_segments() {
        assert!(under("xhr", "xhr"));
        assert!(under("xhr/a.html", "xhr"));
        assert!(!under("xhr-extra/a.html", "xhr"));
        assert!(!under("xh", "xhr"));
    }

    #[test]
    #[cfg_attr(miri, ignore = "creates and walks a temporary directory")]
    fn walk_lists_files_and_skips_source() {
        let dir =
            std::env::temp_dir().join(format!("clazel-inventory-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        assert!(std::fs::create_dir_all(dir.join("a")).is_ok());
        assert!(std::fs::write(dir.join("SOURCE.md"), b"x").is_ok());
        assert!(std::fs::write(dir.join("a").join("b.txt"), b"abc").is_ok());
        let mut out = Vec::new();
        let res = walk(&dir, "", &mut out);
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(res, Ok(()));
        assert_eq!(out.len(), 1);
        let first = out.first();
        assert_eq!(first.map(|e| e.path.as_str()), Some("a/b.txt"));
        assert_eq!(first.map(|e| e.size), Some(3));
        assert_eq!(
            first.map(|e| e.sha256.as_str()),
            Some("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
        );
    }
}
