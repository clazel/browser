//! `--changed`: which crates a local run must check, given what differs from
//! the last commit CI verified.
//!
//! A crate is selected if a file under its directory changed, or if it
//! depends (directly or not, dev-dependencies included) on a selected crate,
//! because its proofs and tests may rest on the changed one. A change to any
//! file outside every crate and outside the list in [`is_inert`] selects
//! every crate: `Cargo.lock`, the workspace `Cargo.toml`, the toolchain
//! pins, `scripts/`, `xtask/` itself (which decides what passing means) and
//! the CI workflow (which decides what CI runs) can change any crate's
//! result.
//!
//! So can a change to a crate's `tier` or `target-tier` (see
//! [`tier_lines_differ`]): CLAUDE.md rule 7 requires a tier raise to pass a
//! full verification on its pull request, so such a change selects every
//! crate, the safest choice.
//!
//! The same selection narrows a pull request's CI run (`cargo xtask crates
//! --changed`, `.github/workflows/ci.yml`). `main` is always verified in
//! full, and that run is the gate (docs/VERIFICATION.md, "Local and CI
//! runs").

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

/// The CI workflow. It decides what CI runs, so a change to it is a change
/// to everything: it is not inert.
const CI_WORKFLOW: &str = ".github/workflows/ci.yml";

/// Paths outside every crate whose changes cannot alter any crate's build,
/// proofs, tests or measurements. Everything they feed is re-checked by the
/// static checks, which `--changed` always runs in full: `docs/` holds the
/// dependency allowlist, spec reviews and `clazel-sys` audits, and
/// README.md's status table is compared row by row. The rest of `.github/`
/// is inert, but not [`CI_WORKFLOW`].
fn is_inert(path: &str) -> bool {
    path.starts_with("docs/")
        || (path.starts_with(".github/") && path != CI_WORKFLOW)
        || path.starts_with(".claude/")
        || matches!(path, "README.md" | "CLAUDE.md" | "LICENSE" | ".gitignore")
}

/// The lines of a manifest that mention a tier (`tier = 2`,
/// `target-tier = 2`, a dotted `metadata.clazel.tier = 2`, an inline table),
/// comments dropped and whitespace removed, sorted. Deliberately loose: it
/// can only over-report a change, which selects more, never less.
fn tier_lines(manifest: &str) -> Vec<String> {
    let mut lines: Vec<String> = manifest
        .lines()
        .map(|l| l.split('#').next().unwrap_or(""))
        .filter(|l| l.contains("tier"))
        .map(|l| l.split_whitespace().collect::<String>())
        .collect();
    lines.sort();
    lines
}

/// Whether the tier declarations differ between two versions of a crate's
/// `Cargo.toml` (`None`: the file did not exist).
pub fn tier_lines_differ(old: Option<&str>, new: Option<&str>) -> bool {
    old.map(tier_lines) != new.map(tier_lines)
}

/// The crates to check for `changed` paths (relative to the repository
/// root, `/`-separated). `tier_changed` are the crate manifests among them
/// whose tier declarations differ ([`tier_lines_differ`]); any selects
/// every crate.
pub fn select_paths(
    crates: &[Crate],
    root: &Path,
    changed: &[String],
    tier_changed: &[String],
) -> Selection {
    if let Some(path) = tier_changed.first() {
        return Selection::All(format!(
            "{path} changed its tier or target-tier (a tier change needs a full verification, CLAUDE.md rule 7)"
        ));
    }
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
fn changed_paths(base: &str) -> Result<(String, Vec<String>, Vec<String>), String> {
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
    // Crate manifests whose tier declarations changed (or that are new).
    let mut tier_changed = Vec::new();
    for path in paths.iter().filter(|p| p.ends_with("/Cargo.toml")) {
        let old = git(&["show", &format!("{merge_base}:{path}")]).ok();
        let new = std::fs::read_to_string(path).ok();
        if tier_lines_differ(old.as_deref(), new.as_deref()) {
            tier_changed.push(path.clone());
        }
    }
    Ok((merge_base, paths.into_iter().collect(), tier_changed))
}

/// The selection for this checkout against `base`, and the merge base used.
pub fn select(crates: &[Crate], root: &Path, base: &str) -> Result<(String, Selection), String> {
    let (merge_base, paths, tier_changed) = changed_paths(base)?;
    Ok((
        merge_base,
        select_paths(crates, root, &paths, &tier_changed),
    ))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{Selection, select_paths, tier_lines_differ};
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
        select_paths(&ws(), std::path::Path::new("/r"), &paths, &[])
    }

    fn sel_tier(paths: &[&str], tier_changed: &[&str]) -> Selection {
        let paths: Vec<String> = paths.iter().map(|p| (*p).to_owned()).collect();
        let tier: Vec<String> = tier_changed.iter().map(|p| (*p).to_owned()).collect();
        select_paths(&ws(), std::path::Path::new("/r"), &paths, &tier)
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
            sel(&[
                "docs/ROADMAP.md",
                "README.md",
                ".github/dependabot.yml",
                ".github/workflows/other.yml"
            ]),
            some(&[])
        );
        assert_eq!(sel(&[]), some(&[]));
    }

    #[test]
    fn a_change_to_the_ci_workflow_selects_everything() {
        for paths in [
            &[".github/workflows/ci.yml"][..],
            &["crates/sandbox/src/lib.rs", ".github/workflows/ci.yml"][..],
        ] {
            assert!(matches!(sel(paths), Selection::All(_)), "{paths:?}");
        }
    }

    #[test]
    fn a_tier_change_selects_everything() {
        // The manifest alone would select only `sandbox`.
        assert_eq!(sel(&["crates/sandbox/Cargo.toml"]), some(&["sandbox"]));
        assert!(matches!(
            sel_tier(
                &["crates/sandbox/Cargo.toml"],
                &["crates/sandbox/Cargo.toml"]
            ),
            Selection::All(_)
        ));
    }

    #[test]
    fn tier_declarations_are_compared_line_by_line() {
        let base =
            "[package]\nname = \"a\"\n[package.metadata.clazel]\ntier = 1 # now\ntarget-tier = 2\n";
        // Other edits, comments and spacing are not tier changes.
        let edited = "[package]\nname = \"a\"\nversion = \"0.1.0\"\n[package.metadata.clazel]\ntier=1\ntarget-tier = 2 # goal\n";
        assert!(!tier_lines_differ(Some(base), Some(edited)));
        assert!(!tier_lines_differ(None, None));
        // A raise, a lowered target, a dotted key, a new or removed manifest.
        assert!(tier_lines_differ(
            Some(base),
            Some(&base.replace("tier = 1", "tier = 2"))
        ));
        assert!(tier_lines_differ(
            Some(base),
            Some(&base.replace("target-tier = 2", "target-tier = 1"))
        ));
        assert!(tier_lines_differ(
            Some(base),
            Some(&format!("{base}metadata.clazel.tier = 2\n"))
        ));
        assert!(tier_lines_differ(None, Some(base)));
        assert!(tier_lines_differ(Some(base), None));
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
