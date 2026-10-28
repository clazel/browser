//! `--changed`: which crates a local run must check, given what differs from
//! the last commit CI verified.
//!
//! A crate is selected if a file under its directory changed, or if it
//! depends (directly or not, dev-dependencies included) on a selected crate,
//! because its proofs and tests may rest on the changed one. A change to any
//! file outside every crate and outside the list in [`is_inert`] selects
//! every crate: `Cargo.lock`, the workspace `Cargo.toml`, the toolchain
//! pins, `scripts/` and `xtask/` itself (which decides what passing means)
//! can change any crate's result.
//!
//! This narrows only what a local run checks. CI runs `cargo xtask verify`
//! in full on every push and pull request, and that run is the gate
//! (docs/VERIFICATION.md, "Local and CI runs").

use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

use crate::workspace::Crate;

/// The ref CI has verified, unless `--changed <ref>` names another.
pub const DEFAULT_BASE: &str = "origin/main";

/// What a `--changed` run checks.
#[derive(Debug, PartialEq, Eq)]
pub enum Selection {
    /// Every crate, and why.
    All(String),
    /// Only these crates (possibly none).
    Some(BTreeSet<String>),
}

/// Paths outside every crate whose changes cannot alter any crate's build,
/// proofs, tests or measurements. Everything they feed is re-checked by the
/// static checks, which `--changed` always runs in full: `docs/` holds the
/// dependency allowlist, spec reviews and `clazel-sys` audits, and
/// README.md's status table is compared row by row.
fn is_inert(path: &str) -> bool {
    path.starts_with("docs/")
        || path.starts_with(".github/")
        || path.starts_with(".claude/")
        || matches!(path, "README.md" | "CLAUDE.md" | "LICENSE" | ".gitignore")
}

/// The crates to check for `changed` paths (relative to the repository
/// root, `/`-separated).
pub fn select_paths(crates: &[Crate], root: &Path, changed: &[String]) -> Selection {
    let dirs: Vec<(String, String)> = crates
        .iter()
        .filter_map(|c| {
            let rel = c.dir.strip_prefix(root).ok()?.to_str()?.to_owned();
            Some((format!("{rel}/"), c.name.clone()))
        })
        .collect();
    let mut selected = BTreeSet::new();
    for path in changed {
        if is_inert(path) {
            continue;
        }
        match dirs.iter().find(|(dir, _)| path.starts_with(dir.as_str())) {
            Some((_, name)) if name != "xtask" => {
                selected.insert(name.clone());
            }
            Some(_) => {
                return Selection::All(format!("{path} changed (xtask decides what passes)"));
            }
            None => return Selection::All(format!("{path} changed (outside every crate)")),
        }
    }
    // Close over reverse dependencies.
    loop {
        let before = selected.len();
        for c in crates {
            if c.deps.iter().any(|(d, _)| selected.contains(d)) {
                selected.insert(c.name.clone());
            }
        }
        if selected.len() == before {
            return Selection::Some(selected);
        }
    }
}

/// Paths that differ between the merge base of HEAD and `base` and the
/// working tree: committed, staged, unstaged and untracked (not ignored).
fn changed_paths(base: &str) -> Result<(String, Vec<String>), String> {
    let git = |args: &[&str]| -> Result<String, String> {
        let out = Command::new("git")
            .args(args)
            .output()
            .map_err(|e| format!("cannot run git: {e}"))?;
        if out.status.success() {
            Ok(String::from_utf8_lossy(&out.stdout).into_owned())
        } else {
            Err(format!(
                "git {}: {}",
                args.join(" "),
                String::from_utf8_lossy(&out.stderr).trim()
            ))
        }
    };
    let merge_base = git(&["merge-base", "HEAD", base])?.trim().to_owned();
    let mut paths: BTreeSet<String> = BTreeSet::new();
    for out in [
        git(&["diff", "--name-only", "--no-renames", &merge_base])?,
        git(&["ls-files", "--others", "--exclude-standard"])?,
    ] {
        paths.extend(out.lines().map(str::to_owned));
    }
    Ok((merge_base, paths.into_iter().collect()))
}

/// The selection for this checkout against `base`, and the merge base used.
pub fn select(crates: &[Crate], root: &Path, base: &str) -> Result<(String, Selection), String> {
    let (merge_base, paths) = changed_paths(base)?;
    Ok((merge_base, select_paths(crates, root, &paths)))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{Selection, select_paths};
    use crate::workspace::Crate;

    fn krate(name: &str, deps: &[&str]) -> Crate {
        Crate {
            theorems: Vec::new(),
            name: name.to_owned(),
            dir: PathBuf::from(format!(
                "/r/{}",
                if name == "xtask" {
                    "xtask".to_owned()
                } else {
                    format!("crates/{name}")
                }
            )),
            manifest: PathBuf::new(),
            tier: None,
            target_tier: None,
            verus: false,
            tooling: false,
            deps: deps
                .iter()
                .map(|d| ((*d).to_owned(), String::new()))
                .collect(),
            dev_deps: Vec::new(),
        }
    }

    fn ws() -> Vec<Crate> {
        vec![
            krate("enc", &[]),
            krate("url", &["enc"]),
            krate("cookie", &["url"]),
            krate("ipc", &["enc"]),
            krate("sandbox", &[]),
            krate("xtask", &[]),
        ]
    }

    fn sel(paths: &[&str]) -> Selection {
        let paths: Vec<String> = paths.iter().map(|p| (*p).to_owned()).collect();
        select_paths(&ws(), std::path::Path::new("/r"), &paths)
    }

    fn some(names: &[&str]) -> Selection {
        Selection::Some(names.iter().map(|n| (*n).to_owned()).collect())
    }

    #[test]
    fn a_leaf_change_selects_only_that_crate() {
        assert_eq!(sel(&["crates/sandbox/src/lib.rs"]), some(&["sandbox"]));
        assert_eq!(sel(&["crates/cookie/tests/x.rs"]), some(&["cookie"]));
    }

    #[test]
    fn dependents_are_selected_transitively() {
        assert_eq!(
            sel(&["crates/enc/src/lib.rs"]),
            some(&["cookie", "enc", "ipc", "url"])
        );
        assert_eq!(sel(&["crates/url/Cargo.toml"]), some(&["cookie", "url"]));
    }

    #[test]
    fn docs_and_readme_select_nothing() {
        assert_eq!(
            sel(&["docs/ROADMAP.md", "README.md", ".github/workflows/ci.yml"]),
            some(&[])
        );
        assert_eq!(sel(&[]), some(&[]));
    }

    #[test]
    fn shared_inputs_select_everything() {
        for p in [
            "Cargo.lock",
            "Cargo.toml",
            "rust-toolchain.toml",
            "scripts/toolchains.env",
            "xtask/src/main.rs",
            "Dockerfile",
            ".cargo/config.toml",
        ] {
            assert!(
                matches!(sel(&["crates/enc/src/lib.rs", p]), Selection::All(_)),
                "{p}"
            );
        }
    }

    #[test]
    fn a_crate_name_prefix_is_not_its_directory() {
        // `crates/url-extra/` is not under `crates/url/`.
        assert!(matches!(
            sel(&["crates/url-extra/src/lib.rs"]),
            Selection::All(_)
        ));
    }
}
