//! `--changed`: which crates a local run must check, given what differs from
//! the last commit CI verified.
//!
//! A crate is selected if a file under its directory changed, or if it
//! depends (directly or not, dev-dependencies included) on a selected crate,
//! because its proofs and tests may rest on the changed one. A change to
//! `Cargo.lock` selects the crates whose locked packages changed: those whose
//! dependency closure in the lockfile (every package they reach, with its
//! version, source and checksum) differs between the two lockfiles
//! ([`lock_affected`]). A change to any other file outside every crate and
//! outside the list in [`is_inert`] selects every crate: the workspace
//! `Cargo.toml`, the toolchain pins, `scripts/` and `xtask/` itself (which
//! decides what passing means) can change any crate's result.
//!
//! A local `--changed` run and a pull request's CI run check only the
//! selection. The merge queue and every push to main run `cargo xtask
//! verify` in full, and that run is the gate before main (docs/VERIFICATION.md,
//! "Local and CI runs").

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
/// docs/STATUS.md's status table is compared row by row.
fn is_inert(path: &str) -> bool {
    path.starts_with("docs/")
        || path.starts_with(".github/")
        || path.starts_with(".claude/")
        || matches!(path, "README.md" | "CLAUDE.md" | "LICENSE" | ".gitignore")
}

/// The crates to check for `changed` paths (relative to the repository
/// root, `/`-separated). `lock` is what [`lock_affected`] found when
/// `Cargo.lock` is among them; without it, a changed `Cargo.lock` selects
/// every crate.
pub fn select_paths(
    crates: &[Crate],
    root: &Path,
    changed: &[String],
    lock: Option<&Result<BTreeSet<String>, String>>,
) -> Selection {
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
        if path == "Cargo.lock" {
            match lock {
                Some(Ok(names)) => {
                    selected.extend(names.iter().cloned());
                    continue;
                }
                Some(Err(e)) => {
                    return Selection::All(format!(
                        "Cargo.lock changed and its packages could not be compared ({e})"
                    ));
                }
                None => return Selection::All("Cargo.lock changed".to_owned()),
            }
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

/// A package of a `Cargo.lock`: its identity (`name version source
/// checksum`, the last two empty for a workspace crate), its name and
/// version, and its dependencies as the lockfile writes them (`name`,
/// `name version` or `name version (source)`).
struct Package {
    id: String,
    name: String,
    version: String,
    deps: Vec<String>,
}

/// The value of a `key = "value"` line.
fn quoted(line: &str) -> Option<&str> {
    line.split_once('=')?
        .1
        .trim()
        .strip_prefix('"')?
        .strip_suffix('"')
}

/// The packages of a lockfile (Cargo's version 3 and 4 formats: one
/// `[[package]]` table each, a `dependencies` array one string per line).
fn parse_lock(text: &str) -> Result<Vec<Package>, String> {
    struct Raw {
        name: String,
        version: String,
        source: String,
        checksum: String,
        deps: Vec<String>,
    }
    let mut raws: Vec<Raw> = Vec::new();
    // Inside a `[[package]]` table, and inside its `dependencies` array.
    let (mut in_pkg, mut in_deps) = (false, false);
    for line in text.lines() {
        let t = line.trim();
        if in_deps {
            let Some(raw) = raws.last_mut() else {
                return Err("a dependencies array outside a package".to_owned());
            };
            if t == "]" {
                in_deps = false;
            } else if let Some(dep) = t
                .trim_end_matches(',')
                .strip_prefix('"')
                .and_then(|d| d.strip_suffix('"'))
            {
                raw.deps.push(dep.to_owned());
            } else {
                return Err(format!("unexpected line in a dependencies array: {t:?}"));
            }
            continue;
        }
        if t.starts_with('[') {
            // `[[package]]` opens a package; any other table (`[metadata]`)
            // ends it.
            in_pkg = t == "[[package]]";
            if in_pkg {
                raws.push(Raw {
                    name: String::new(),
                    version: String::new(),
                    source: String::new(),
                    checksum: String::new(),
                    deps: Vec::new(),
                });
            }
            continue;
        }
        if !in_pkg {
            continue;
        }
        let Some(raw) = raws.last_mut() else {
            continue;
        };
        let key = t.split_once('=').map(|(k, _)| k.trim());
        match key {
            Some("name") => raw.name = quoted(t).ok_or("bad name line")?.to_owned(),
            Some("version") => raw.version = quoted(t).ok_or("bad version line")?.to_owned(),
            Some("source") => raw.source = quoted(t).ok_or("bad source line")?.to_owned(),
            Some("checksum") => raw.checksum = quoted(t).ok_or("bad checksum line")?.to_owned(),
            Some("dependencies") if t.ends_with("[]") => {}
            Some("dependencies") if t.ends_with('[') => in_deps = true,
            Some("dependencies") => return Err(format!("unexpected dependencies line: {t:?}")),
            _ => {}
        }
    }
    raws.into_iter()
        .map(|r| {
            if r.name.is_empty() || r.version.is_empty() {
                return Err("a package without a name or version".to_owned());
            }
            Ok(Package {
                id: format!("{} {} {} {}", r.name, r.version, r.source, r.checksum),
                name: r.name,
                version: r.version,
                deps: r.deps,
            })
        })
        .collect()
}

/// The index of the package a dependency string names.
fn resolve(pkgs: &[Package], dep: &str) -> Result<usize, String> {
    let mut words = dep.splitn(3, ' ');
    let name = words.next().unwrap_or_default();
    let version = words.next();
    let hits: Vec<usize> = pkgs
        .iter()
        .enumerate()
        .filter(|(_, p)| p.name == name && version.is_none_or(|v| p.version == v))
        .map(|(i, _)| i)
        .collect();
    match hits.as_slice() {
        [i] => Ok(*i),
        [] => Err(format!("dependency {dep:?} names no package")),
        _ => Err(format!("dependency {dep:?} names more than one package")),
    }
}

/// The identities of every package the workspace crate `name` reaches in
/// the lockfile, itself included, or `None` if it is not there.
fn closure(pkgs: &[Package], name: &str) -> Result<Option<BTreeSet<String>>, String> {
    let Some(start) = pkgs
        .iter()
        .position(|p| p.name == name && p.id.ends_with("  "))
    else {
        return Ok(None);
    };
    let mut seen = BTreeSet::new();
    let mut todo = vec![start];
    let mut ids = BTreeSet::new();
    while let Some(i) = todo.pop() {
        if !seen.insert(i) {
            continue;
        }
        let p = pkgs.get(i).ok_or("package index out of range")?;
        ids.insert(p.id.clone());
        for d in &p.deps {
            todo.push(resolve(pkgs, d)?);
        }
    }
    Ok(Some(ids))
}

/// The workspace crates whose locked packages differ between two lockfiles:
/// a crate new in `head`, or one whose dependency closure (dev-dependencies
/// included, as the lockfile records them) changed in any package's version,
/// source or checksum, or gained or lost a package.
pub fn lock_affected(crates: &[Crate], base: &str, head: &str) -> Result<BTreeSet<String>, String> {
    let (base, head) = (parse_lock(base)?, parse_lock(head)?);
    let mut affected = BTreeSet::new();
    for c in crates {
        let now = closure(&head, &c.name)?;
        if now.is_none() {
            return Err(format!("{} is not in Cargo.lock", c.name));
        }
        if closure(&base, &c.name)? != now {
            affected.insert(c.name.clone());
        }
    }
    Ok(affected)
}

fn git(args: &[&str]) -> Result<String, String> {
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
}

/// Paths that differ between the merge base of HEAD and `base` and the
/// working tree: committed, staged, unstaged and untracked (not ignored).
fn changed_paths(base: &str) -> Result<(String, Vec<String>), String> {
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
    let lock = paths.iter().any(|p| p == "Cargo.lock").then(|| {
        let old = git(&["show", &format!("{merge_base}:Cargo.lock")])?;
        let new = std::fs::read_to_string(root.join("Cargo.lock"))
            .map_err(|e| format!("Cargo.lock: {e}"))?;
        lock_affected(crates, &old, &new)
    });
    Ok((
        merge_base,
        select_paths(crates, root, &paths, lock.as_ref()),
    ))
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use std::collections::BTreeSet;

    use super::{Selection, lock_affected, select_paths};
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
        select_paths(&ws(), std::path::Path::new("/r"), &paths, None)
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

    const LOCK: &str = r#"# This file is automatically @generated by Cargo.
version = 4

[[package]]
name = "cookie"
version = "0.0.0"
dependencies = [
 "url",
]

[[package]]
name = "enc"
version = "0.0.0"

[[package]]
name = "ipc"
version = "0.0.0"
dependencies = [
 "enc",
 "serde 1.0.0",
]

[[package]]
name = "sandbox"
version = "0.0.0"
dependencies = []

[[package]]
name = "serde"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "aaaa"

[[package]]
name = "url"
version = "0.0.0"
dependencies = [
 "enc",
]

[[package]]
name = "xtask"
version = "0.0.0"
"#;

    fn names(v: &[&str]) -> BTreeSet<String> {
        v.iter().map(|n| (*n).to_owned()).collect()
    }

    #[test]
    fn an_unchanged_lock_affects_nothing() {
        assert_eq!(lock_affected(&ws(), LOCK, LOCK), Ok(names(&[])));
    }

    #[test]
    fn a_new_package_version_affects_only_the_crates_that_reach_it() {
        let bumped = LOCK.replace("checksum = \"aaaa\"", "checksum = \"bbbb\"");
        assert_eq!(lock_affected(&ws(), LOCK, &bumped), Ok(names(&["ipc"])));
    }

    #[test]
    fn a_new_dependency_affects_its_crate_and_its_dependents() {
        let added = LOCK.replace(
            "name = \"url\"\nversion = \"0.0.0\"\ndependencies = [\n \"enc\",\n",
            "name = \"url\"\nversion = \"0.0.0\"\ndependencies = [\n \"enc\",\n \"serde 1.0.0\",\n",
        );
        assert_ne!(added, LOCK);
        assert_eq!(
            lock_affected(&ws(), LOCK, &added),
            Ok(names(&["cookie", "url"]))
        );
    }

    #[test]
    fn a_lock_change_selects_what_it_affects() {
        let paths = vec!["Cargo.lock".to_owned()];
        let found = Ok(names(&["ipc"]));
        assert_eq!(
            select_paths(&ws(), std::path::Path::new("/r"), &paths, Some(&found)),
            some(&["ipc"])
        );
        let failed = Err("unreadable".to_owned());
        assert!(matches!(
            select_paths(&ws(), std::path::Path::new("/r"), &paths, Some(&failed)),
            Selection::All(_)
        ));
    }

    #[test]
    fn a_crate_missing_from_the_lock_is_an_error() {
        let gone = LOCK.replace("name = \"sandbox\"", "name = \"sandbox2\"");
        assert!(lock_affected(&ws(), LOCK, &gone).is_err());
    }
}
