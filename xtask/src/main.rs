//! `cargo xtask`: runs and enforces every check in `docs/VERIFICATION.md`.
//!
//! - `cargo xtask verify`: everything, with fresh proof runs. Exit 0 only if
//!   every check ran and passed; 1 if any failed; 2 if none failed but some
//!   were skipped because a tool is missing (never report that as verified).
//! - `cargo xtask verify --changed [base]`: the same checks, but tests, Miri,
//!   Kani, Verus, mutations and conformance only for the crates that changed
//!   since `base` (default `origin/main`) and their dependents (`changed.rs`).
//!   Ends in `CHANGED CRATES PASSED`; CI's full run is the gate.
//! - `cargo xtask verify --part (base|crate <name> --metrics <dir>|assemble
//!   --metrics <dir> [--write])`: the same checks split into parts for
//!   separate CI jobs (`parts.rs`); `cargo xtask crates` lists the crates for
//!   them. `assemble --write` writes README.md's table from the parts, which
//!   CI does on main.
//! - `cargo xtask check`: only the fast static checks (no build, no proofs).
//! - `cargo xtask mutate`: only the proof mutation tests (also part of
//!   `verify`).
//! - `cargo xtask testdata`: regenerate the Rust tables converted from
//!   vendored conformance suites (`tests/generated/*.rs`). `check` and
//!   `verify` fail if a committed table is stale.
//! - `cargo xtask tables`: regenerate the Unicode tables generated from
//!   vendored Unicode data (`crates/clazel-idna/src/uts46/data.rs`), the
//!   Public Suffix List, and the root certificate table from NSS's
//!   `certdata.txt` (`crates/clazel-x509/src/roots/data.rs`).
//!   `check` and `verify` fail if they are stale or a data file's hash
//!   differs from its `SOURCE.md`.
//! - `cargo xtask report [--write] [--changed [base]]`: run the checks that produce the README
//!   status table (including each crate's conformance suites, see
//!   `conformance.rs`), print it, and with `--write` update README.md. A
//!   table that differs from what was measured is reported, not a failure:
//!   CI rewrites it on main.

mod changed;
mod conformance;
mod deps;
mod mutate;
mod parts;
mod pins;
mod psl;
mod report;
mod reviews;
mod roots;
mod scan;
mod sys;
mod testdata;
mod unicode;
mod verus;
mod workspace;

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use pins::Pins;
use workspace::Crate;

enum Outcome {
    Pass(Vec<String>),
    Fail(Vec<String>),
    Skip(String),
}

#[derive(Default)]
struct Runner {
    failed: bool,
    skipped: bool,
    /// What the checks measured, for the README status table.
    metrics: report::Table,
}

impl Runner {
    fn step(&mut self, name: &str, outcome: Outcome) {
        println!("==> {name}");
        match outcome {
            Outcome::Pass(details) => {
                print_details(&details);
                println!("    PASS  {name}");
            }
            Outcome::Fail(details) => {
                print_details(&details);
                println!("    FAIL  {name}");
                self.failed = true;
            }
            Outcome::Skip(why) => {
                println!("    SKIP  {name} ({why})");
                self.skipped = true;
            }
        }
    }
}

fn print_details(details: &[String]) {
    for d in details {
        for line in d.lines() {
            println!("    {line}");
        }
    }
}

/// Pass if `problems` is empty, showing `notes` either way.
fn outcome(problems: Vec<String>, notes: Vec<String>) -> Outcome {
    if problems.is_empty() {
        Outcome::Pass(notes)
    } else {
        Outcome::Fail(problems.into_iter().chain(notes).collect())
    }
}

fn from_result(r: Result<Vec<String>, String>) -> Outcome {
    match r {
        Ok(details) => Outcome::Pass(details),
        Err(e) => Outcome::Fail(vec![e]),
    }
}

/// Like [`run`], but every line is also printed as it arrives, indented,
/// so a long step (the tests, Miri) shows how far it got even when it
/// never returns, as when a CI runner dies under it. Prints `--> {name}`
/// first: a step's `==>` header comes only once it has finished.
fn run_streamed(name: &str, cmd: &mut Command) -> Result<String, String> {
    use std::io::{BufRead, BufReader};
    use std::process::Stdio;
    println!("--> {name}: started, output follows as it arrives");
    let shown = format!("{cmd:?}");
    let mut child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run {shown}: {e}"))?;
    let echo = |pipe: Option<Box<dyn std::io::Read + Send>>| {
        std::thread::spawn(move || {
            let mut kept = String::new();
            if let Some(p) = pipe {
                for line in BufReader::new(p).lines().map_while(Result::ok) {
                    println!("    | {line}");
                    kept.push_str(&line);
                    kept.push('\n');
                }
            }
            kept
        })
    };
    let out = echo(
        child
            .stdout
            .take()
            .map(|p| Box::new(p) as Box<dyn std::io::Read + Send>),
    );
    let err = echo(
        child
            .stderr
            .take()
            .map(|p| Box::new(p) as Box<dyn std::io::Read + Send>),
    );
    let status = child
        .wait()
        .map_err(|e| format!("cannot wait for {shown}: {e}"))?;
    let text = format!(
        "{}{}",
        out.join().unwrap_or_default(),
        err.join().unwrap_or_default()
    );
    if status.success() {
        Ok(text)
    } else {
        Err(format!("{shown} failed (its output is above)"))
    }
}

/// Run a command; Ok(stdout+stderr) on success, Err(stdout+stderr) otherwise.
fn run(cmd: &mut Command) -> Result<String, String> {
    let shown = format!("{cmd:?}");
    let out = cmd
        .output()
        .map_err(|e| format!("cannot run {shown}: {e}"))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    if out.status.success() {
        Ok(text)
    } else {
        Err(format!("{shown} failed:\n{text}"))
    }
}

fn on_path(bin: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|paths| std::env::split_paths(&paths).any(|d| d.join(bin).is_file()))
}

fn static_checks(r: &mut Runner, crates: &[Crate], pins: &Pins) {
    // Source scan and tier declarations share one pass over the sources.
    let mut violations = Vec::new();
    let mut decl_problems = Vec::new();
    let mut decl_notes = Vec::new();
    let mut axioms = 0usize;
    let (mut unsafe_blocks, mut unsafe_lines) = (0usize, 0usize);
    let workspace_manifest = std::fs::read_to_string("Cargo.toml").unwrap_or_default();
    let (review_status, review_problems) = match reviews::status(crates) {
        Ok(s) => s,
        Err(e) => (std::collections::BTreeMap::new(), vec![e]),
    };
    for c in crates {
        let files = review_status.get(&c.name).map_or(&[][..], Vec::as_slice);
        let current = files
            .iter()
            .filter(|f| f.status == reviews::Status::Current)
            .count();
        let m = r.metrics.entry(c.name.clone()).or_default();
        m.tier = c.tier;
        m.target_tier = c.target_tier;
        m.is_verus = c.verus;
        m.reviews = Some((current, files.len()));
        match workspace::scan_crate(c) {
            Ok(s) => {
                m.axioms = s.axioms;
                m.kani_harnesses = s.kani_proofs;
                m.unsafe_blocks = s.unsafe_blocks;
                m.unsafe_lines = s.unsafe_lines;
                unsafe_blocks = unsafe_blocks.saturating_add(s.unsafe_blocks);
                unsafe_lines = unsafe_lines.saturating_add(s.unsafe_lines);
                violations.extend(s.violations);
                axioms = axioms.saturating_add(s.axioms);
                let evidence = mutate::gaps(c).and_then(|mutations| {
                    let (conformance_tests, independent_spec) = workspace::evidence_files(c)?;
                    Ok(workspace::TierEvidence {
                        kani_proofs: s.kani_proofs,
                        mutations,
                        conformance_tests,
                        independent_spec,
                    })
                });
                let (bad, notes) = match evidence {
                    Ok(ev) => workspace::check_tiers(c, &ev),
                    Err(e) => (vec![e], Vec::new()),
                };
                decl_problems.extend(bad);
                decl_notes.extend(notes);
            }
            Err(e) => violations.push(e),
        }
        // Lints: every crate inherits the workspace's, except `clazel-sys`,
        // which lists them itself with `unsafe_code` allowed (sys.rs).
        let rel_dir = workspace::relative(&c.dir);
        match std::fs::read_to_string(&c.manifest) {
            Ok(text) => violations.extend(sys::lint_problems(&rel_dir, &text, &workspace_manifest)),
            Err(e) => violations.push(format!("{}: {e}", c.manifest.display())),
        }
        if c.is_sys() {
            violations.extend(sys::dependency_problems(&c.deps_normal(), &c.dev_deps));
            if c.dir.join("build.rs").exists() {
                violations.push(format!(
                    "{rel_dir}/build.rs: a build script could run anything"
                ));
            }
        } else if c.name == sys::CRATE_NAME {
            violations.push(format!(
                "{rel_dir}: a crate named {} must live in {}",
                sys::CRATE_NAME,
                sys::CRATE_DIR
            ));
        } else {
            match workspace::inherits_workspace_lints(c) {
                Ok(true) => {}
                Ok(false) => {
                    decl_problems.push(format!(
                        "{}: missing [lints] workspace = true",
                        workspace::relative(&c.manifest)
                    ));
                }
                Err(e) => decl_problems.push(e),
            }
        }
    }
    r.step(
        "no unsafe, lint overrides or proof escape hatches",
        outcome(
            violations,
            vec![
                format!("documented axioms: {axioms}"),
                format!("`unsafe` blocks: {unsafe_blocks} ({unsafe_lines} lines)"),
            ],
        ),
    );
    let mut theorem_problems = Vec::new();
    let mut theorem_count = 0usize;
    for c in crates {
        theorem_count = theorem_count.saturating_add(c.theorems.len());
        match workspace::check_theorems(c) {
            Ok(p) => theorem_problems.extend(p),
            Err(e) => theorem_problems.push(e),
        }
    }
    r.step(
        "listed theorems are defined",
        outcome(
            theorem_problems,
            vec![format!("listed theorems: {theorem_count}")],
        ),
    );
    r.step(
        "clazel-sys audit",
        sys_audit(crates.iter().find(|c| c.is_sys())),
    );
    r.step(
        "README unsafe claim",
        outcome(
            std::fs::read_to_string(report::README).map_or_else(
                |e| vec![format!("{}: {e}", report::README)],
                |t| sys::readme_problems(&t, unsafe_blocks, unsafe_lines),
            ),
            Vec::new(),
        ),
    );
    r.step(
        "crate tier declarations",
        outcome(decl_problems, decl_notes),
    );
    // Unreviewed specs are not a failure (agents must be able to edit
    // them), but every run lists them.
    let review_notes: Vec<String> = review_status
        .values()
        .flatten()
        .filter(|f| f.status != reviews::Status::Current)
        .map(|f| {
            let what = if f.status == reviews::Status::Stale {
                "stale     "
            } else {
                "unreviewed"
            };
            format!("{what} {}  sha256 {}", f.file, f.sha256)
        })
        .collect();
    let total: usize = review_status.values().map(Vec::len).sum();
    let mut notes = vec![format!(
        "{} of {total} spec files reviewed and current",
        total.saturating_sub(review_notes.len())
    )];
    notes.extend(review_notes);
    r.step("spec reviews", outcome(review_problems, notes));
    r.step("pinned versions", from_result(check_pins(crates, pins)));
    let (problems, notes) = testdata::run(crates, false);
    r.step("generated test data", outcome(problems, notes));
    let (problems, notes) = unicode::run(false);
    r.step("generated Unicode tables", outcome(problems, notes));
    let (problems, notes) = psl::run(false);
    r.step(
        "generated Public Suffix List tables",
        outcome(problems, notes),
    );
    let (problems, notes) = roots::run(false);
    r.step("generated root certificate table", outcome(problems, notes));
    let tooling = crates
        .iter()
        .filter(|c| c.tooling)
        .map(|c| c.name.clone())
        .collect();
    r.step(
        "dependency allowlist",
        match deps::check(&tooling) {
            Ok(summary) => Outcome::Pass(vec![summary]),
            Err(problems) => Outcome::Fail(problems),
        },
    );
}

/// The latest audit in `docs/SYS-AUDITS.md` covers the crate's current source.
fn sys_audit(sys_crate: Option<&Crate>) -> Outcome {
    let Some(c) = sys_crate else {
        return Outcome::Pass(vec![format!("{} does not exist yet", sys::CRATE_DIR)]);
    };
    let (hash, files) = match sys::source_hash(&c.dir) {
        Ok(h) => h,
        Err(e) => return Outcome::Fail(vec![e]),
    };
    let log = std::fs::read_to_string(sys::AUDITS)
        .map_err(|e| format!("{}: {e}", sys::AUDITS))
        .map(|text| sys::audit_problems(&text, &hash));
    let notes = vec![
        format!("source SHA-256 {hash}"),
        format!("covers {} files: {}", files.len(), files.join(", ")),
    ];
    match log {
        Ok(problems) => outcome(problems, notes),
        Err(e) => Outcome::Fail(vec![e]),
    }
}

const CHECKSUMS: &str = "scripts/checksums.txt";

fn check_pins(crates: &[Crate], pins: &Pins) -> Result<Vec<String>, String> {
    let rust = pins.get("RUST_TOOLCHAIN")?;
    let toolchain = std::fs::read_to_string("rust-toolchain.toml")
        .map_err(|e| format!("rust-toolchain.toml: {e}"))?;
    if !toolchain
        .lines()
        .any(|l| l.trim() == format!("channel = \"{rust}\""))
    {
        return Err(format!(
            "rust-toolchain.toml does not pin channel = \"{rust}\""
        ));
    }
    let vstd = format!("={}", pins.get("VSTD_VERSION")?);
    for c in crates.iter().filter(|c| c.verus) {
        let req = c
            .deps
            .iter()
            .find(|(n, _)| n == "vstd")
            .map(|(_, r)| r.as_str());
        if req != Some(vstd.as_str()) {
            return Err(format!(
                "{}: vstd must be pinned to \"{vstd}\", found {req:?}",
                c.name
            ));
        }
    }
    // Test-only engines are pinned exactly too, so a differential test
    // always compares against the version on the allowlist.
    for c in crates.iter().filter(|c| !c.tooling) {
        if let Some((n, req)) = c.dev_deps.iter().find(|(_, r)| !r.starts_with('=')) {
            return Err(format!(
                "{}: dev-dependency {n} must be pinned to an exact version (\"=x.y.z\"), found {req:?}",
                c.name
            ));
        }
    }
    // Every file setup.sh downloads for the pinned versions has a checksum.
    let verus_v = pins.get("VERUS_VERSION")?;
    let kani_v = pins.get("KANI_VERSION")?;
    let mut needed: Vec<String> = ["arm64-macos", "x86-macos", "x86-linux"]
        .iter()
        .map(|p| format!("verus-{verus_v}-{p}.zip"))
        .collect();
    needed.extend(
        [
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ]
        .iter()
        .map(|t| format!("kani-{kani_v}-{t}.tar.gz")),
    );
    // The Dockerfile's rustup.
    needed.push(format!(
        "rustup-init-{}-x86_64-unknown-linux-gnu",
        pins.get("RUSTUP_VERSION")?
    ));
    let sums = std::fs::read_to_string(CHECKSUMS).map_err(|e| format!("{CHECKSUMS}: {e}"))?;
    let listed: Vec<&str> = sums
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .filter_map(
            |l| match l.split_whitespace().collect::<Vec<_>>().as_slice() {
                [sum, name] if sum.len() == 64 && sum.chars().all(|c| c.is_ascii_hexdigit()) => {
                    Some(*name)
                }
                _ => None,
            },
        )
        .collect();
    let missing: Vec<&String> = needed
        .iter()
        .filter(|n| !listed.contains(&n.as_str()))
        .collect();
    if !missing.is_empty() {
        return Err(format!("{CHECKSUMS}: no SHA-256 for {missing:?}"));
    }
    Ok(vec![format!(
        "rust {rust}, vstd {vstd}, checksums for {} downloads",
        needed.len()
    )])
}

/// fmt and clippy over the workspace; tests for `only`'s crates, or for
/// every crate if `None`.
fn build_checks(r: &mut Runner, only: Option<&[Crate]>) {
    let cargo =
        |args: &[&str]| from_result(run(Command::new("cargo").args(args)).map(|_| Vec::new()));
    r.step("rustfmt", cargo(&["fmt", "--all", "--", "--check"]));
    r.step(
        "clippy",
        cargo(&[
            "clippy",
            "--workspace",
            "--all-targets",
            "--locked",
            "--",
            "-D",
            "warnings",
        ]),
    );
    // `--no-fail-fast`: run every test binary even after one fails, so a
    // single run (CI's especially) reports every failing test.
    // Not `--quiet`: the streamed output then names each test binary as it
    // starts and each test as it ends.
    let mut args = vec!["test", "--locked", "--no-fail-fast"];
    match only {
        None => args.push("--workspace"),
        Some([]) => {
            r.step(
                "tests",
                Outcome::Pass(vec!["no changed crate to test".into()]),
            );
            return;
        }
        Some(cs) => args.extend(cs.iter().flat_map(|c| ["-p", c.name.as_str()])),
    }
    // Streamed: a test that hangs or takes the machine down is then named
    // by the last lines printed.
    r.step(
        "tests",
        from_result(run_streamed("tests", Command::new("cargo").args(&args)).map(|_| Vec::new())),
    );
}

/// Run every test under Miri, which reports undefined behaviour (Tier 0).
/// Our code has no `unsafe`, so this mostly checks dependency code that the
/// tests execute, and it will check the audited `sys` crate once it exists.
fn miri(r: &mut Runner, pins: &Pins, only: Option<&[Crate]>) {
    const NAME: &str = "tests under Miri";
    let nightly = match pins.get("MIRI_NIGHTLY") {
        Ok(n) => format!("+{n}"),
        Err(e) => {
            r.step(NAME, Outcome::Fail(vec![e]));
            return;
        }
    };
    if run(Command::new("cargo").args([nightly.as_str(), "miri", "--version"])).is_err() {
        r.step(
            NAME,
            Outcome::Skip(format!(
                "Miri not installed on {}; run scripts/setup.sh",
                nightly.trim_start_matches('+')
            )),
        );
        return;
    }
    let mut args = vec![
        nightly.as_str(),
        "miri",
        "test",
        "--locked",
        "--no-fail-fast",
    ];
    match only {
        None => args.push("--workspace"),
        Some([]) => {
            r.step(NAME, Outcome::Pass(vec!["no changed crate to test".into()]));
            return;
        }
        Some(cs) => args.extend(cs.iter().flat_map(|c| ["-p", c.name.as_str()])),
    }
    let res = run_streamed(NAME, Command::new("cargo").args(&args)).map(|out| {
        let passed: u64 = out
            .lines()
            .filter_map(|l| l.strip_prefix("test result: ok. "))
            .filter_map(|l| l.split(' ').next()?.parse::<u64>().ok())
            .sum();
        vec![format!(
            "{passed} tests passed under Miri ({})",
            nightly.trim_start_matches('+')
        )]
    });
    r.step(NAME, from_result(res));
}

fn kani(r: &mut Runner, crates: &[Crate], pins: &Pins) {
    if !on_path("cargo-kani") {
        r.step("kani", Outcome::Skip("cargo-kani not installed".into()));
        return;
    }
    let version = pins.get("KANI_VERSION").map(str::to_owned);
    r.step(
        "kani version",
        from_result(version.and_then(|v| {
            let out = run(Command::new("cargo").args(["kani", "--version"]))?;
            if out.contains(&format!("Kani Rust Verifier {v} ")) {
                Ok(vec![v])
            } else {
                Err(format!("expected Kani {v}, got:\n{out}"))
            }
        })),
    );
    let mut any = false;
    for c in crates {
        let proofs = workspace::scan_crate(c).map(|s| s.kani_proofs).unwrap_or(0);
        if proofs == 0 {
            continue;
        }
        any = true;
        let res = run(Command::new("cargo").args(["kani", "-p", &c.name])).and_then(|out| {
            let summary = out
                .lines()
                .filter(|l| l.starts_with("Complete -"))
                .collect::<Vec<_>>()
                .join("\n");
            if summary.contains(" 0 failures") {
                Ok(vec![summary])
            } else {
                Err(format!("unexpected Kani summary:\n{out}"))
            }
        });
        if let Ok(lines) = &res {
            let summary = lines.join(" ");
            let summary = summary
                .trim_start_matches("Complete - ")
                .trim_end_matches('.');
            r.metrics.entry(c.name.clone()).or_default().kani = Some(summary.to_owned());
        }
        r.step(&format!("kani {}", c.name), from_result(res));
    }
    if !any {
        r.step(
            "kani",
            Outcome::Pass(vec!["no checked crate has Kani harnesses".into()]),
        );
    }
}

fn verus(r: &mut Runner, crates: &[Crate], pins: &Pins) {
    if !on_path("cargo-verus") || !on_path("verus") {
        r.step(
            "verus",
            Outcome::Skip("verus / cargo-verus not installed".into()),
        );
        return;
    }
    let version = pins.get("VERUS_VERSION").map(str::to_owned);
    r.step(
        "verus version",
        from_result(version.and_then(|v| {
            let out = run(Command::new("verus").arg("--version"))?;
            if out.lines().any(|l| l.trim() == format!("Version: {v}")) {
                Ok(vec![v])
            } else {
                Err(format!("expected Verus {v}, got:\n{out}"))
            }
        })),
    );
    for c in crates.iter().filter(|c| c.verus) {
        let res = verus_crate(&c.dir, &c.name);
        if let Ok(lines) = &res
            && let Some(summary) = lines.first()
        {
            let summary = summary.trim_start_matches("verification results:: ");
            r.metrics.entry(c.name.clone()).or_default().verus = Some(summary.to_owned());
        }
        r.step(&format!("verus {}", c.name), from_result(res));
        let counted = report::line_count(&c.dir);
        if let Ok(l) = &counted {
            r.metrics.entry(c.name.clone()).or_default().lines = Some(l.clone());
        }
        r.step(
            &format!("line count {}", c.name),
            from_result(counted.map(|l| {
                vec![format!(
                    "spec {}, proof {}, exec {}",
                    l.spec, l.proof, l.exec
                )]
            })),
        );
    }
}

fn verus_crate(dir: &Path, name: &str) -> Result<Vec<String>, String> {
    match verus::run(dir, name, true, None)? {
        verus::Run::Verified(s) => Ok(vec![s]),
        verus::Run::ProofFailed(s, out) => Err(format!("{s}\n{out}")),
        verus::Run::BuildFailed(out) => Err(format!("no verification results reported:\n{out}")),
        // Not reachable: the proof step runs without a time limit.
        verus::Run::TimedOut(t) => Err(format!("timed out after {}s", t.as_secs())),
    }
}

/// Mutation tests for every Verus crate, or only the one named `only`.
fn mutations(r: &mut Runner, crates: &[Crate], root: &Path, only: Option<&str>) {
    if !on_path("cargo-verus") || !on_path("verus") {
        r.step(
            "proof mutation tests",
            Outcome::Skip("verus / cargo-verus not installed".into()),
        );
        return;
    }
    for c in crates
        .iter()
        .filter(|c| c.verus && only.is_none_or(|n| n == c.name))
    {
        let name = format!("proof mutation tests {}", c.name);
        if !mutate::has_mutations(c) {
            // A Verus crate with no mutations has unchecked proofs.
            r.step(
                &name,
                Outcome::Fail(vec![format!(
                    "{}: Verus crate has no {}",
                    c.name,
                    mutate::FILE
                )]),
            );
            continue;
        }
        let outcome = match mutate::run(c, root) {
            Ok(rep) => {
                r.metrics.entry(c.name.clone()).or_default().mutations = Some(report::Mutations {
                    killed: rep.killed,
                    incidental: rep.incidental,
                    survived: rep.survived,
                    total: rep.total,
                });
                let mut lines = rep.lines;
                lines.push(format!(
                    "{} mutations: {} killed by a theorem, {} killed incidentally (not coverage), {} survived (known gaps)",
                    rep.total, rep.killed, rep.incidental, rep.survived
                ));
                outcome(rep.problems, lines)
            }
            Err(e) => Outcome::Fail(vec![e]),
        };
        r.step(&name, outcome);
    }
}

/// Run every crate's conformance tests and record the suites they report
/// (format: `conformance.rs`).
fn conformance_suites(r: &mut Runner, crates: &[Crate]) {
    for c in crates {
        let res = conformance::run(c);
        let outcome = match res {
            Ok(suites) if suites.is_empty() => {
                r.metrics.entry(c.name.clone()).or_default().conformance = Some(Vec::new());
                continue;
            }
            Ok(suites) => {
                let notes = suites
                    .iter()
                    .map(|s| {
                        format!(
                            "{}: {} pass, {} expected failures, {} fail, of {}",
                            s.name, s.pass, s.xfail, s.fail, s.total
                        )
                    })
                    .collect();
                r.metrics.entry(c.name.clone()).or_default().conformance = Some(suites);
                Outcome::Pass(notes)
            }
            Err(problems) => Outcome::Fail(problems),
        };
        r.step(&format!("conformance {}", c.name), outcome);
    }
}

/// Compare (or, with `write`, update) README.md's status table against what
/// this run measured. With `only` (a `--changed` run), the other crates'
/// proof and test columns are carried over from README.md's current table,
/// since their inputs did not change; CI's full run re-measures them all.
fn readme_table(r: &mut Runner, write: bool, only: Option<&[Crate]>) {
    const NAME: &str = "README status table";
    let host_shell_count = report::host_shell_lines(std::path::Path::new(report::HOST_SHELL_DIR));
    if let Some(counted) = host_shell_count.as_ref() {
        match counted {
            Ok(n) if *n < report::HOST_SHELL_LIMIT => {}
            Ok(n) => {
                let limit = report::HOST_SHELL_LIMIT;
                r.step(
                    "host shell size",
                    Outcome::Fail(vec![format!(
                        "{} is {n} lines, over the limit of {limit}",
                        report::HOST_SHELL_DIR
                    )]),
                );
            }
            Err(e) => r.step("host shell size", Outcome::Fail(vec![e.clone()])),
        }
    }
    let carried = match only {
        None => report::Rows::new(),
        Some(cs) => {
            let rows = std::fs::read_to_string(report::README)
                .map_err(|e| format!("{}: {e}", report::README))
                .and_then(|t| {
                    report::rows(report::current(&t).ok_or("README.md has no status table")?)
                });
            let rows = match rows {
                Ok(rows) => rows,
                Err(e) => {
                    r.step(NAME, Outcome::Fail(vec![e]));
                    return;
                }
            };
            let checked: Vec<&str> = cs.iter().map(|c| c.name.as_str()).collect();
            let missing: Vec<&String> = r
                .metrics
                .keys()
                .filter(|n| !checked.contains(&n.as_str()) && !rows.contains_key(*n))
                .collect();
            if !missing.is_empty() {
                r.step(
                    NAME,
                    Outcome::Fail(vec![format!(
                        "no committed row to carry over for {missing:?}; check them too (`--changed` with an older base, or the full report)"
                    )]),
                );
                return;
            }
            rows.into_iter()
                .filter(|(n, _)| !checked.contains(&n.as_str()))
                .collect()
        }
    };
    let incomplete: Vec<&String> = r
        .metrics
        .iter()
        .filter(|(n, m)| !carried.contains_key(*n) && !m.complete())
        .map(|(n, _)| n)
        .collect();
    if !incomplete.is_empty() {
        r.step(
            NAME,
            Outcome::Skip(format!("not all metrics were measured, for {incomplete:?}")),
        );
        return;
    }
    let block = report::render_with(&r.metrics, &carried, host_shell_count.and_then(Result::ok));
    let readme = match std::fs::read_to_string(report::README) {
        Ok(t) => t,
        Err(e) => {
            r.step(
                NAME,
                Outcome::Fail(vec![format!("{}: {e}", report::README)]),
            );
            return;
        }
    };
    if write {
        // Never publish numbers from a run where something failed.
        let outcome = if r.failed {
            Outcome::Fail(vec!["refusing to write: a check above failed".into()])
        } else {
            match report::splice(&readme, &block)
                .and_then(|new| std::fs::write(report::README, new).map_err(|e| e.to_string()))
            {
                Ok(()) => Outcome::Pass(vec![format!("wrote {}", report::README), block]),
                Err(e) => Outcome::Fail(vec![e]),
            }
        };
        r.step(NAME, outcome);
        return;
    }
    // A stale table is not a failure: CI rewrites it on main from the
    // measurements of a fully verified commit (the `table` job in
    // .github/workflows/ci.yml), so a change need not carry it.
    let outcome = match report::current(&readme) {
        Some(cur) if cur == block => Outcome::Pass(Vec::new()),
        Some(_) => Outcome::Pass(vec![
            "README.md's table differs from what this run measured; CI updates it on main. Measured:".into(),
            block,
        ]),
        None => Outcome::Fail(vec![format!(
            "{} has no {} … {} block",
            report::README,
            report::BEGIN,
            report::END
        )]),
    };
    r.step(NAME, outcome);
}

/// `cargo xtask testdata`: rewrite every stale generated table.
fn generate_testdata() -> ExitCode {
    let mut r = Runner::default();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent();
    if !root.is_some_and(|p| std::env::set_current_dir(p).is_ok()) {
        r.step(
            "find repository root",
            Outcome::Fail(vec!["cannot enter the repository root".into()]),
        );
        return ExitCode::from(1);
    }
    let res = workspace::load().map(|crates| testdata::run(&crates, true));
    match res {
        Ok((problems, notes)) => r.step("generate test data", outcome(problems, notes)),
        Err(e) => r.step("load workspace", Outcome::Fail(vec![e])),
    }
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else {
        println!("RESULT: TEST DATA UP TO DATE");
        ExitCode::SUCCESS
    }
}

/// `cargo xtask tables`: rewrite the generated Unicode tables if stale.
fn generate_tables() -> ExitCode {
    let mut r = Runner::default();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent();
    if !root.is_some_and(|p| std::env::set_current_dir(p).is_ok()) {
        r.step(
            "find repository root",
            Outcome::Fail(vec!["cannot enter the repository root".into()]),
        );
        return ExitCode::from(1);
    }
    let (problems, notes) = unicode::run(true);
    r.step("generate Unicode tables", outcome(problems, notes));
    let (problems, notes) = psl::run(true);
    r.step(
        "generate Public Suffix List tables",
        outcome(problems, notes),
    );
    let (problems, notes) = roots::run(true);
    r.step("generate root certificate table", outcome(problems, notes));
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else {
        println!("RESULT: UNICODE TABLES UP TO DATE");
        ExitCode::SUCCESS
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    // `verify --part ...` (parts.rs) and `crates` are handled apart.
    let part = match args.as_slice() {
        ["verify", "--part", "base"] => Some(Part::Base),
        ["verify", "--part", "miri"] => Some(Part::Miri),
        ["verify", "--part", "crate", names, "--metrics", dir] => Some(Part::Crate(
            names.split(',').map(str::to_owned).collect(),
            PathBuf::from(dir),
        )),
        ["verify", "--part", "assemble", "--metrics", dir] => {
            Some(Part::Assemble(PathBuf::from(dir), false))
        }
        ["verify", "--part", "assemble", "--metrics", dir, "--write"] => {
            Some(Part::Assemble(PathBuf::from(dir), true))
        }
        ["crates"] => Some(Part::ListCrates),
        _ => None,
    };
    let args = if part.is_some() { vec!["check"] } else { args };
    // `mutate <crate>` runs one crate's mutations, for iterating on them.
    let mut only_crate: Option<&str> = None;
    // `verify` and `report` take `--changed [<base>]` (changed.rs).
    let (args, base) = match args.iter().position(|a| *a == "--changed") {
        Some(i) => {
            let (head, tail) = args.split_at(i);
            match tail {
                [_] => (head, Some(changed::DEFAULT_BASE)),
                [_, b] if !b.starts_with('-') => (head, Some(*b)),
                _ => (&[][..], None),
            }
        }
        None => (args.as_slice(), None),
    };
    let (full, only_mutate, report_mode, write) = match (args, base) {
        (["testdata"], None) => return generate_testdata(),
        (["tables"], None) => return generate_tables(),
        (["verify"], _) => (true, false, false, false),
        (["check"], None) => (false, false, false, false),
        (["mutate"], None) => (false, true, false, false),
        (["mutate", name], None) => {
            only_crate = Some(name);
            (false, true, false, false)
        }
        (["report"], _) => (false, false, true, false),
        (["report", "--write"], _) => (false, false, true, true),
        _ => {
            eprintln!(
                "usage: cargo xtask <verify [--changed [base]]|verify --part (base|crate <name> --metrics <dir>|assemble --metrics <dir> [--write])|crates|check|mutate [crate]|testdata|tables|report [--write] [--changed [base]]>"
            );
            return ExitCode::from(64);
        }
    };
    let mut r = Runner::default();
    // Always work from the repository root, wherever cargo was invoked.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf);
    let Some(root) = root.filter(|p| std::env::set_current_dir(p).is_ok()) else {
        r.step(
            "find repository root",
            Outcome::Fail(vec!["cannot enter the repository root".into()]),
        );
        println!("RESULT: FAILED");
        return ExitCode::from(1);
    };
    let setup = workspace::load().and_then(|crates| Ok((crates, Pins::load()?)));
    let (crates, pins) = match setup {
        Ok(s) => s,
        Err(e) => {
            r.step("load workspace", Outcome::Fail(vec![e]));
            println!("RESULT: FAILED");
            return ExitCode::from(1);
        }
    };
    if let Some(part) = part {
        return run_part(&mut r, part, &crates, &pins, &root);
    }
    if only_mutate {
        if only_crate.is_some_and(|n| !crates.iter().any(|c| c.name == n)) {
            r.step(
                "select crate",
                Outcome::Fail(vec![format!("no workspace crate named {only_crate:?}")]),
            );
        }
        mutations(&mut r, &crates, &root, only_crate);
    } else {
        static_checks(&mut r, &crates, &pins);
    }
    // With `--changed`, the crates whose proofs and tests this run repeats;
    // `None` means every crate.
    let mut partial: Option<(String, Vec<Crate>)> = None;
    if let Some(base) = base {
        match changed::select(&crates, &root, base) {
            Ok((merge_base, changed::Selection::All(why))) => r.step(
                "select changed crates",
                Outcome::Pass(vec![format!(
                    "every crate is checked: {why} since {base} ({merge_base})"
                )]),
            ),
            Ok((merge_base, changed::Selection::Some(names))) => {
                let picked: Vec<Crate> = crates
                    .iter()
                    .filter(|c| names.contains(&c.name))
                    .cloned()
                    .collect();
                r.step(
                    "select changed crates",
                    Outcome::Pass(vec![format!(
                        "{} of {} crates changed since {base} ({merge_base}), or depend on one that did: {}",
                        picked.len(),
                        crates.len(),
                        if names.is_empty() {
                            "none".to_owned()
                        } else {
                            names.iter().cloned().collect::<Vec<_>>().join(", ")
                        }
                    )]),
                );
                partial = Some((merge_base, picked));
            }
            Err(e) => r.step("select changed crates", Outcome::Fail(vec![e])),
        }
    }
    let checked: &[Crate] = partial.as_ref().map_or(&crates, |(_, p)| p.as_slice());
    let only = partial.as_ref().map(|(_, p)| p.as_slice());
    if full {
        build_checks(&mut r, only);
        miri(&mut r, &pins, only);
    }
    if full || report_mode {
        kani(&mut r, checked, &pins);
        verus(&mut r, checked, &pins);
        mutations(&mut r, checked, &root, None);
        conformance_suites(&mut r, checked);
        readme_table(&mut r, write, only);
    }
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else if r.skipped {
        println!("RESULT: INCOMPLETE (checks skipped; not verified)");
        ExitCode::from(2)
    } else if let Some((merge_base, picked)) = &partial {
        // Never "ALL CHECKS PASSED": the other crates' proofs did not run.
        println!(
            "RESULT: CHANGED CRATES PASSED ({} of {} crates' proofs and tests run, against {merge_base}; CI's full `cargo xtask verify` is the gate)",
            picked.len(),
            crates.len()
        );
        ExitCode::SUCCESS
    } else if full {
        println!("RESULT: ALL CHECKS PASSED");
        ExitCode::SUCCESS
    } else if only_mutate {
        println!("RESULT: MUTATION TESTS PASSED (other checks not run)");
        ExitCode::SUCCESS
    } else if report_mode {
        println!("RESULT: REPORT CHECKS PASSED (fmt, clippy and tests not run)");
        ExitCode::SUCCESS
    } else {
        println!(
            "RESULT: STATIC CHECKS PASSED (no build, tests or proofs run; use `cargo xtask verify`)"
        );
        ExitCode::SUCCESS
    }
}

/// One part of a split verification (parts.rs).
enum Part {
    Base,
    Miri,
    /// One or more crates (comma-separated on the command line; CI groups
    /// the crates with no proofs into one job, see [`crate_groups`]).
    Crate(Vec<String>, PathBuf),
    /// The crate parts' directory, and whether to write README.md's table
    /// from them (CI does, on main, after every part passed).
    Assemble(PathBuf, bool),
    /// `cargo xtask crates`: the crate groups as a JSON array of
    /// comma-separated names, for CI's matrix of `crate` parts.
    ListCrates,
}

/// CI's crate parts: one per crate with proof work (Verus, Kani harnesses or
/// mutations), and one for all the others together, which finish in about
/// a minute each and would otherwise each hold a runner for its setup.
fn crate_groups(crates: &[Crate]) -> Vec<String> {
    let light = |c: &Crate| {
        !c.verus
            && !mutate::has_mutations(c)
            && workspace::scan_crate(c).map_or(1, |s| s.kani_proofs) == 0
    };
    let mut groups: Vec<String> = crates
        .iter()
        .filter(|c| !light(c))
        .map(|c| c.name.clone())
        .collect();
    let rest: Vec<&str> = crates
        .iter()
        .filter(|c| light(c))
        .map(|c| c.name.as_str())
        .collect();
    if !rest.is_empty() {
        groups.push(rest.join(","));
    }
    groups
}

fn run_part(r: &mut Runner, part: Part, crates: &[Crate], pins: &Pins, root: &Path) -> ExitCode {
    if let Part::ListCrates = part {
        println!("{}", serde_json::Value::from(crate_groups(crates)));
        return ExitCode::SUCCESS;
    }
    static_checks(r, crates, pins);
    let done = match part {
        Part::Base => {
            build_checks(r, None);
            "BASE PART PASSED (static checks, rustfmt, clippy and tests; Miri runs in the miri part, proofs in the crate parts)".to_owned()
        }
        Part::Miri => {
            miri(r, pins, None);
            "MIRI PART PASSED (static checks and the tests under Miri)".to_owned()
        }
        Part::Crate(names, dir) => {
            let mut selected: Vec<Crate> = Vec::new();
            for name in &names {
                match crates.iter().find(|c| &c.name == name) {
                    Some(c) => selected.push(c.clone()),
                    None => {
                        r.step(
                            "select crate",
                            Outcome::Fail(vec![format!("no workspace crate named {name:?}")]),
                        );
                        println!("RESULT: FAILED");
                        return ExitCode::from(1);
                    }
                }
            }
            kani(r, &selected, pins);
            verus(r, &selected, pins);
            mutations(r, &selected, root, None);
            conformance_suites(r, &selected);
            // Never record measurements from a run where something failed.
            if !r.failed && !r.skipped {
                for name in &names {
                    let m = r.metrics.get(name).cloned().unwrap_or_default();
                    let res =
                        parts::head().and_then(|commit| parts::write(&dir, name, &commit, &m));
                    r.step(
                        &format!("write crate measurements {name}"),
                        from_result(res.map(|path| vec![format!("wrote {path}")])),
                    );
                }
            }
            format!(
                "CRATE PART PASSED ({}: Kani, Verus, mutations and conformance)",
                names.join(", ")
            )
        }
        Part::Assemble(dir, write) => {
            let res = parts::head().and_then(|commit| {
                let mut problems = Vec::new();
                for c in crates {
                    let path = dir.join(format!("{}.json", c.name));
                    let entry = r.metrics.entry(c.name.clone()).or_default();
                    let read = std::fs::read_to_string(&path)
                        .map_err(|e| e.to_string())
                        .and_then(|text| parts::read_into(&text, &c.name, &commit, entry));
                    if let Err(e) = read {
                        problems.push(format!("{}: {e}", path.display()));
                    }
                }
                if problems.is_empty() {
                    Ok(vec![format!(
                        "{} crate parts, all from {commit}",
                        crates.len()
                    )])
                } else {
                    Err(problems.join("\n"))
                }
            });
            r.step("read crate parts", from_result(res));
            if !r.failed {
                readme_table(r, write, None);
            }
            "PARTS ASSEMBLED (every crate part present and from this commit; the gate is this and every part passing on the same commit)".to_owned()
        }
        Part::ListCrates => String::new(),
    };
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else if r.skipped {
        println!("RESULT: INCOMPLETE (checks skipped; not verified)");
        ExitCode::from(2)
    } else {
        println!("RESULT: {done}");
        ExitCode::SUCCESS
    }
}

#[cfg(test)]
mod tests {
    use std::process::Command;

    /// A streamed run keeps both pipes' output and reports failure.
    #[cfg(unix)]
    #[test]
    #[cfg_attr(miri, ignore = "spawns processes")]
    fn a_streamed_run_keeps_its_output() {
        let ok = super::run_streamed("t", Command::new("sh").args(["-c", "echo a; echo b >&2"]));
        assert_eq!(ok.as_deref(), Ok("a\nb\n"));
        let failed = super::run_streamed("t", Command::new("sh").args(["-c", "exit 3"]));
        assert!(failed.is_err());
    }
}
