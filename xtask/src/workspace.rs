//! Workspace facts: crates, their declared tiers, and their source files.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

use crate::scan::{self, Kind};
use crate::sys;

/// The highest tier in docs/VERIFICATION.md.
pub const MAX_TIER: u64 = 2;

/// One workspace crate.
#[derive(Debug, Clone)]
pub struct Crate {
    pub name: String,
    pub dir: PathBuf,
    pub manifest: PathBuf,
    /// `[package.metadata.clazel] tier`.
    pub tier: Option<u64>,
    /// `[package.metadata.clazel] target-tier`.
    pub target_tier: Option<u64>,
    /// `[package.metadata.verus] verify = true`.
    pub verus: bool,
    /// `[package.metadata.clazel] tooling = true`: build tooling, not browser.
    pub tooling: bool,
    /// `[package.metadata.clazel] theorems`: names of theorems the crate must
    /// define (as `proof fn`s), so one cannot be deleted quietly.
    pub theorems: Vec<String>,
    /// Direct dependencies as (name, version requirement).
    pub deps: Vec<(String, String)>,
    /// The subset of `deps` declared under `[dev-dependencies]`.
    pub dev_deps: Vec<(String, String)>,
}

/// Load every workspace member via `cargo metadata`.
pub fn load() -> Result<Vec<Crate>, String> {
    let out = Command::new("cargo")
        .args(["metadata", "--format-version", "1", "--no-deps", "--locked"])
        .output()
        .map_err(|e| format!("cannot run cargo metadata: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "cargo metadata failed:\n{}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let meta: Value = serde_json::from_slice(&out.stdout)
        .map_err(|e| format!("cargo metadata output is not JSON: {e}"))?;
    let packages = meta
        .get("packages")
        .and_then(Value::as_array)
        .ok_or("cargo metadata: no packages")?;
    packages.iter().map(parse_package).collect()
}

fn parse_package(p: &Value) -> Result<Crate, String> {
    let name = p
        .get("name")
        .and_then(Value::as_str)
        .ok_or("package without name")?
        .to_owned();
    let manifest = PathBuf::from(
        p.get("manifest_path")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{name}: no manifest_path"))?,
    );
    let dir = manifest
        .parent()
        .ok_or_else(|| format!("{name}: manifest has no parent"))?
        .to_path_buf();
    let meta = p.get("metadata");
    let clazel = meta.and_then(|m| m.get("clazel"));
    let deps_where = |dev_only: bool| -> Vec<(String, String)> {
        p.get("dependencies")
            .and_then(Value::as_array)
            .map(|ds| {
                ds.iter()
                    .filter(|d| !dev_only || d.get("kind").and_then(Value::as_str) == Some("dev"))
                    .filter_map(|d| {
                        let n = d.get("name")?.as_str()?;
                        let r = d.get("req")?.as_str()?;
                        Some((n.to_owned(), r.to_owned()))
                    })
                    .collect()
            })
            .unwrap_or_default()
    };
    let deps = deps_where(false);
    let dev_deps = deps_where(true);
    Ok(Crate {
        tier: clazel.and_then(|c| c.get("tier")).and_then(Value::as_u64),
        tooling: clazel
            .and_then(|c| c.get("tooling"))
            .and_then(Value::as_bool)
            .unwrap_or(false),
        target_tier: clazel
            .and_then(|c| c.get("target-tier"))
            .and_then(Value::as_u64),
        verus: meta
            .and_then(|m| m.get("verus"))
            .and_then(|v| v.get("verify"))
            .and_then(Value::as_bool)
            .unwrap_or(false),
        theorems: clazel
            .and_then(|c| c.get("theorems"))
            .and_then(Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(|v| v.as_str().map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default(),
        name,
        dir,
        manifest,
        deps,
        dev_deps,
    })
}

/// All `.rs` files under a crate, skipping build output and hidden dirs.
pub fn rust_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(d) = pending.pop() {
        let entries = std::fs::read_dir(&d).map_err(|e| format!("{}: {e}", d.display()))?;
        for entry in entries {
            let path = entry.map_err(|e| format!("{}: {e}", d.display()))?.path();
            let hidden_or_target = path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with('.') || n == "target");
            if hidden_or_target {
                continue;
            }
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                files.push(path);
            }
        }
    }
    files.sort();
    Ok(files)
}

/// The result of scanning a whole crate.
#[derive(Debug, Default)]
pub struct CrateScan {
    /// Violations, as "path:line: what".
    pub violations: Vec<String>,
    /// Escape hatches accepted because they are documented axioms.
    pub axioms: usize,
    pub kani_proofs: usize,
    /// `unsafe` blocks and the lines they cover (xtask/src/sys.rs).
    pub unsafe_blocks: usize,
    pub unsafe_lines: usize,
}

impl Crate {
    /// Direct dependencies that are not `[dev-dependencies]`.
    pub fn deps_normal(&self) -> Vec<(String, String)> {
        self.deps
            .iter()
            .filter(|d| !self.dev_deps.contains(d))
            .cloned()
            .collect()
    }

    /// The one crate allowed to contain `unsafe` (CLAUDE.md rule 1).
    pub fn is_sys(&self) -> bool {
        relative(&self.dir) == sys::CRATE_DIR
    }
}

/// Scan every source file of a crate.
///
/// Escape hatches are allowed only in files named `axioms.rs`, and only with
/// a `// AXIOM:` justification on one of the three lines above them.
pub fn scan_crate(c: &Crate) -> Result<CrateScan, String> {
    let mut result = CrateScan::default();
    for file in rust_files(&c.dir)? {
        let source =
            std::fs::read_to_string(&file).map_err(|e| format!("{}: {e}", file.display()))?;
        let scanned = scan::scan(&source).map_err(|e| format!("{}: {e}", file.display()))?;
        result.kani_proofs = result.kani_proofs.saturating_add(scanned.kani_proofs);
        for (first, last) in &scanned.unsafe_spans {
            result.unsafe_blocks = result.unsafe_blocks.saturating_add(1);
            result.unsafe_lines = result
                .unsafe_lines
                .saturating_add(last.saturating_sub(*first).saturating_add(1));
        }
        let sys_crate = c.is_sys();
        if sys_crate {
            let checked =
                sys::check_source(&source).map_err(|e| format!("{}: {e}", file.display()))?;
            for (line, what) in checked.violations {
                result.violations.push(format!(
                    "{}:{line}: unsafe policy (CLAUDE.md rule 1): {what}",
                    relative(&file)
                ));
            }
        }
        let in_axioms_file = file.file_name().is_some_and(|n| n == "axioms.rs");
        let lines: Vec<&str> = source.lines().collect();
        for f in scanned.findings {
            // In `clazel-sys`, `unsafe` is judged by sys::check_source.
            if sys_crate && f.kind == Kind::Unsafe {
                continue;
            }
            if f.kind == Kind::EscapeHatch && in_axioms_file && has_axiom_comment(&lines, f.line) {
                result.axioms = result.axioms.saturating_add(1);
                continue;
            }
            let rule = match f.kind {
                Kind::EscapeHatch => "proof escape hatch (CLAUDE.md rule 4)",
                Kind::LintOverride => "lint override (CLAUDE.md rule 2)",
                Kind::Unsafe => "unsafe (CLAUDE.md rule 1)",
            };
            result.violations.push(format!(
                "{}:{}: {rule}: {}",
                relative(&file),
                f.line,
                f.what
            ));
        }
    }
    Ok(result)
}

/// One of the three lines before 1-based `line` contains `// AXIOM:`.
fn has_axiom_comment(lines: &[&str], line: usize) -> bool {
    let end = line.saturating_sub(1);
    let start = end.saturating_sub(3);
    lines
        .get(start..end)
        .is_some_and(|ls| ls.iter().any(|l| l.contains("// AXIOM:")))
}

/// The manifest declares `[lints] workspace = true`. Cargo metadata does not
/// report lint settings, so this reads the manifest's `[lints]` table directly.
pub fn inherits_workspace_lints(c: &Crate) -> Result<bool, String> {
    let text = std::fs::read_to_string(&c.manifest)
        .map_err(|e| format!("{}: {e}", c.manifest.display()))?;
    let mut in_lints = false;
    for line in text.lines().map(str::trim) {
        if line.starts_with('[') {
            in_lints = line == "[lints]";
        } else if in_lints && line.replace(' ', "") == "workspace=true" {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Check declared tiers are present, in range, and backed by tooling.
/// Returns (violations, notes); notes are shortfalls that are allowed but
/// must be visible.
/// What backs a crate's declared tier.
pub struct TierEvidence {
    pub kani_proofs: usize,
    /// (mutations not certified `killed`, total), if the crate has any.
    pub mutations: Option<(usize, usize)>,
    /// The crate has `tests/conformance*.rs`.
    pub conformance_tests: bool,
    /// The crate has an `independent.rs` spec.
    pub independent_spec: bool,
}

/// Evidence files a crate has, for `TierEvidence`.
pub fn evidence_files(c: &Crate) -> Result<(bool, bool), String> {
    let files = rust_files(&c.dir)?;
    let named =
        |p: &Path, f: &dyn Fn(&str) -> bool| p.file_name().and_then(|n| n.to_str()).is_some_and(f);
    let conformance = files.iter().any(|p| {
        p.parent() == Some(&c.dir.join("tests")) && named(p, &|n| n.starts_with("conformance"))
    });
    let independent = files.iter().any(|p| named(p, &|n| n == "independent.rs"));
    Ok((conformance, independent))
}

pub fn check_tiers(c: &Crate, ev: &TierEvidence) -> (Vec<String>, Vec<String>) {
    let TierEvidence {
        kani_proofs,
        mutations,
        conformance_tests,
        independent_spec,
    } = *ev;
    let mut bad = Vec::new();
    let mut notes = Vec::new();
    let m = relative(&c.manifest);
    match (c.tier, c.target_tier) {
        (Some(t), Some(target)) if t <= MAX_TIER && target <= MAX_TIER => {
            if t >= 2 && !c.verus {
                bad.push(format!(
                    "{m}: tier {t} requires [package.metadata.verus] verify = true"
                ));
            }
            // Verus proves panic-freedom (overflow, bounds, unwrap) for the
            // code it verifies, so Kani is what backs Tier 1 only.
            if t == 1 && kani_proofs == 0 {
                bad.push(format!(
                    "{m}: tier {t} requires Kani harnesses (#[kani::proof]); found none"
                ));
            }
            // Tier 2 means the implementation is correct against its spec,
            // and that the spec matches the standard, all without a human
            // gate (docs/VERIFICATION.md, "Trust without reviewers"). No
            // deliberately broken spec may get past the proofs, and each kill
            // is certified by Verus (`verify` checks the certificates).
            if t >= 2 {
                match mutations {
                    None | Some((_, 0)) => bad.push(format!(
                        "{m}: tier {t} requires proof mutation tests (mutations.json)"
                    )),
                    Some((gaps, total)) if gaps > 0 => bad.push(format!(
                        "{m}: tier {t} requires every mutation to be a certified \"killed\"; \
                         {gaps} of {total} are not"
                    )),
                    Some(_) => {}
                }
                if !conformance_tests {
                    bad.push(format!(
                        "{m}: tier {t} requires conformance tests (tests/conformance*.rs) \
                         running the implementation against official suites and other engines"
                    ));
                }
                if !independent_spec {
                    bad.push(format!(
                        "{m}: tier {t} requires an independent transcription (independent.rs) \
                         proven equivalent to the spec"
                    ));
                }
            }
            if t < target {
                notes.push(format!(
                    "{}: tier {t}, below its target tier {target}",
                    c.name
                ));
            }
        }
        (Some(_), Some(_)) => bad.push(format!("{m}: tier and target-tier must be 0..={MAX_TIER}")),
        _ => bad.push(format!(
            "{m}: missing [package.metadata.clazel] tier / target-tier"
        )),
    }
    (bad, notes)
}

/// `path` relative to the current directory (the repo root), for messages.
pub fn relative(path: &Path) -> String {
    let rel = std::env::current_dir()
        .ok()
        .and_then(|cwd| path.strip_prefix(cwd).ok().map(Path::to_path_buf));
    let text = rel
        .unwrap_or_else(|| path.to_path_buf())
        .display()
        .to_string();
    // Repo-relative names are written with `/` on every platform: they are
    // hashed (the `clazel-sys` audit) and compared with the docs.
    if cfg!(windows) {
        text.replace('\\', "/")
    } else {
        text
    }
}

/// Theorems listed in `[package.metadata.clazel] theorems` that no `proof fn`
/// of the given sources defines. A name inside a comment or string does not
/// count (the scan is over tokens).
pub fn missing_theorems(listed: &[String], sources: &[String]) -> Result<Vec<String>, String> {
    let mut defined = std::collections::BTreeSet::new();
    for src in sources {
        defined.extend(scan::proof_fn_names(src)?);
    }
    Ok(listed
        .iter()
        .filter(|name| !defined.contains(*name))
        .cloned()
        .collect())
}

/// Check one crate's listed theorems against its sources.
pub fn check_theorems(c: &Crate) -> Result<Vec<String>, String> {
    if c.theorems.is_empty() {
        return Ok(Vec::new());
    }
    let mut sources = Vec::new();
    for f in rust_files(&c.dir)? {
        sources.push(std::fs::read_to_string(&f).map_err(|e| format!("{}: {e}", f.display()))?);
    }
    Ok(missing_theorems(&c.theorems, &sources)?
        .into_iter()
        .map(|t| {
            format!(
                "{}: listed theorem `{t}` is not defined as a `proof fn`",
                c.name
            )
        })
        .collect())
}

#[cfg(test)]
mod tests {
    use super::{has_axiom_comment, missing_theorems};

    fn names(v: &[&str]) -> Vec<String> {
        v.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn listed_theorems_must_be_defined() {
        let src = "verus! {\npub proof fn theorem_a(x: nat)\n    ensures true,\n{}\n\
                   pub proof fn theorem_b<A>(x: A) {}\n}";
        assert_eq!(
            missing_theorems(&names(&["theorem_a", "theorem_b"]), &[src.to_owned()]),
            Ok(Vec::new())
        );
    }

    #[test]
    fn planted_violation_theorem_without_definition() {
        let src = "pub proof fn theorem_a() {}\n// proof fn theorem_gone() {}\nconst S: &str = \"proof fn theorem_str() {}\";\n\
                   pub proof fn theorem_a_extended() {}";
        let missing = missing_theorems(
            &names(&["theorem_a", "theorem_gone", "theorem_str", "theorem_never"]),
            &[src.to_owned()],
        );
        assert_eq!(
            missing,
            Ok(names(&["theorem_gone", "theorem_str", "theorem_never"]))
        );
        // A prefix of a defined name is not a definition.
        assert_eq!(
            missing_theorems(&names(&["theorem_a_ext"]), &[src.to_owned()]),
            Ok(names(&["theorem_a_ext"]))
        );
    }

    #[test]
    fn axiom_comment_window() {
        let lines = ["// AXIOM: reason", "", "", "admit();", ""];
        assert!(has_axiom_comment(&lines, 4));
        assert!(!has_axiom_comment(&lines, 5));
        assert!(!has_axiom_comment(&lines, 1));
    }
}
