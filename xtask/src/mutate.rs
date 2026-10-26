//! Proof mutation testing (Phase 0 item 0.6).
//!
//! A proof that passes whatever the spec says proves nothing. Each Verus
//! crate may list mutations in `mutations.json`: a small edit to a spec, and
//! whether the proofs are expected to catch it. Every mutation is applied
//! to a copy of the crate in `target/xtask-mutate/`, never to the working
//! tree, so an interrupted run cannot leave a broken spec behind.
//!
//! ```json
//! { "mutations": [ {
//!     "id": "ed-upper-boundary",
//!     "file": "src/utf8/spec.rs",
//!     "find": "if byte == 0xED { 0x9F }",
//!     "replace": "if byte == 0xED { 0xBF }",
//!     "expect": "killed",
//!     "reason": "admits surrogates; lemma_output_scalar_values must fail"
//! } ] }
//! ```
//!
//! `expect` is one of:
//! - `"killed"`: the proofs must fail, *because a proven theorem is false
//!   for the mutant*. This is real coverage, and it must be **certified**
//!   (below), so the claim is checked by Verus, not by a reviewer.
//! - `"killed-incidentally"`: the proofs must fail, but every theorem still
//!   holds for the mutant; only the proof script (an invariant, a case
//!   split) breaks. Not counted as coverage. The reason says which part.
//! - `"survives"`: a known gap. The reason says what will cover it.
//!
//! A mutation whose result does not match `expect` fails the run.
//!
//! ## Kill certificates
//!
//! A `killed` mutation carries a certificate: a concrete `witness` (a Verus
//! boolean expression over a concrete input; one comparison is enough) and a
//! `lemma` call at that
//! input. The tool adds this function to `file`:
//!
//! ```text
//! proof fn __clazel_kill_certificate() {
//!     assert(WITNESS) by (compute_only);  // what the spec computes
//!     LEMMA;                              // a proven theorem, instantiated
//!     assert(false);                      // ...contradicts it
//! }
//! ```
//!
//! and requires that it **verifies in the mutant** (the theorem really is
//! false there) and **fails on the real spec**. Verus evaluates the witness
//! itself, so nobody has to judge it. (`by (compute)` would allow
//! quantifiers, but it crashes Verus 0.2026.10.04 here; `compute_only`
//! needs quantifier-free witnesses, e.g. one concrete output element.)
//!
//! A certificate may also list `reveal`: paths of opaque spec items (for
//! example generated table constants) that the witness evaluates through.
//! Each becomes `reveal(PATH);` before the witness. Only paths are
//! accepted, so a certificate cannot add an assumption this way.
//!
//! A mutation may name a `module` (e.g. `"uts46::process"`): the run that
//! must fail for `killed` and `killed-incidentally` (or pass for
//! `survives`) then verifies only that module, instead of the whole
//! crate. Use it for crates whose full run is slow; the certificate is
//! checked exactly as without it.
//!
//! `killed-incidentally` and `survives` need no certificate: they claim no
//! coverage, so a wrong label can only understate it.

use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::verus::{self, Run};
use crate::workspace::Crate;

pub const FILE: &str = "mutations.json";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expect {
    Killed,
    KilledIncidentally,
    Survives,
}

/// Machine-checkable evidence that a mutant violates a proven theorem.
struct Certificate {
    /// File (relative to the crate) that the certificate function is added to.
    file: String,
    /// Lemma call at the concrete input, e.g. `lemma_hooks_scalar(seq![0xEDu8])`.
    lemma: String,
    /// Quantifier-free fact about the concrete input that contradicts the lemma.
    witness: String,
    /// Opaque items to reveal before the witness (paths only).
    reveal: Vec<String>,
}

/// `a::b::C`: identifiers separated by `::`, nothing else.
fn is_path(s: &str) -> bool {
    !s.is_empty()
        && s.split("::").all(|part| {
            let mut chars = part.chars();
            chars
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}

const CERTIFICATE_FN: &str = "__clazel_kill_certificate";

struct Mutation {
    id: String,
    /// Verify only this module in the mutant's run (see the module docs).
    module: Option<String>,
    certificate: Option<Certificate>,
    file: String,
    find: String,
    replace: String,
    expect: Expect,
    reason: String,
}

/// Outcome of mutation testing one crate.
pub struct Report {
    /// One line per mutation.
    pub lines: Vec<String>,
    /// Mutations whose result did not match `expect`, or that are invalid.
    pub problems: Vec<String>,
    /// Killed because a theorem is false for the mutant.
    pub killed: usize,
    /// Killed, but only by the proof script.
    pub incidental: usize,
    pub survived: usize,
    pub total: usize,
}

/// The crate has a mutations file.
pub fn has_mutations(c: &Crate) -> bool {
    c.dir.join(FILE).is_file()
}

/// For the tier check: (mutations not expected to be `killed`, total), or
/// `None` if the crate has no mutations file.
pub fn gaps(c: &Crate) -> Result<Option<(usize, usize)>, String> {
    if !has_mutations(c) {
        return Ok(None);
    }
    let all = load(c)?;
    let gaps = all
        .iter()
        .filter(|m| m.expect != Expect::Killed || m.certificate.is_none())
        .count();
    Ok(Some((gaps, all.len())))
}

fn load(c: &Crate) -> Result<Vec<Mutation>, String> {
    let path = c.dir.join(FILE);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let json: Value =
        serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    let list = json
        .get("mutations")
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{}: expected {{\"mutations\": [...]}}", path.display()))?;
    list.iter()
        .map(|m| {
            let field = |k: &str| {
                m.get(k)
                    .and_then(Value::as_str)
                    .map(str::to_owned)
                    .ok_or_else(|| {
                        format!("{}: mutation missing string field {k:?}", path.display())
                    })
            };
            let id = field("id")?;
            let expect = match field("expect")?.as_str() {
                "killed" => Expect::Killed,
                "killed-incidentally" => Expect::KilledIncidentally,
                "survives" => Expect::Survives,
                other => {
                    return Err(format!(
                        "{}: {id}: expect must be \"killed\", \"killed-incidentally\" or \"survives\", not {other:?}",
                        path.display()
                    ));
                }
            };
            let certificate = match m.get("certificate") {
                None => None,
                Some(c) => {
                    let f = |k: &str| {
                        c.get(k).and_then(Value::as_str).map(str::to_owned).ok_or_else(|| {
                            format!("{}: {id}: certificate missing string field {k:?}", path.display())
                        })
                    };
                    Some(Certificate {
                        file: f("file")?,
                        lemma: f("lemma")?,
                        witness: f("witness")?,
                        reveal: match c.get("reveal") {
                            None => Vec::new(),
                            Some(list) => list
                                .as_array()
                                .ok_or(format!("{}: {id}: reveal must be an array", path.display()))?
                                .iter()
                                .map(|v| match v.as_str() {
                                    Some(p) if is_path(p) => Ok(p.to_owned()),
                                    _ => Err(format!(
                                        "{}: {id}: reveal entries must be paths, not {v}",
                                        path.display()
                                    )),
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        },
                    })
                }
            };
            let module = match m.get("module") {
                None => None,
                Some(v) => match v.as_str() {
                    Some(p) if is_path(p) => Some(p.to_owned()),
                    _ => {
                        return Err(format!(
                            "{}: {id}: module must be a module path",
                            path.display()
                        ));
                    }
                },
            };
            Ok(Mutation {
                module,
                certificate,
                file: field("file")?,
                find: field("find")?,
                replace: field("replace")?,
                reason: field("reason")?,
                expect,
                id,
            })
        })
        .collect()
}

/// What one mutation's runs showed, before it is counted in a [`Report`].
enum Outcome {
    Killed(String),
    Incidental(String),
    Survived(String),
    Problem(String),
}

/// How many mutants run at once: `CLAZEL_MUTANT_JOBS` if set, otherwise
/// one per available core, at most 4. Each worker has its own sandbox, so
/// runs never share files; more workers than cores only slows each run.
fn workers() -> usize {
    if let Some(n) = std::env::var("CLAZEL_MUTANT_JOBS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|n| *n > 0)
    {
        return n;
    }
    std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .min(4)
}

/// Run every mutation for one crate, several at a time ([`workers`]). The
/// report lists them in the order of `mutations.json`, whatever order they
/// finished in.
pub fn run(c: &Crate, root: &Path) -> Result<Report, String> {
    let mutations = load(c)?;
    let sandbox = make_sandbox(c, root)?;
    let crate_dir = sandbox.join("crates").join(&c.name);
    let mut report = Report {
        lines: Vec::new(),
        problems: Vec::new(),
        killed: 0,
        incidental: 0,
        survived: 0,
        total: 0,
    };

    // Baseline: the unmutated copy must verify, or every mutation would
    // look "killed" for the wrong reason. Its time sets each mutant's limit.
    let started = std::time::Instant::now();
    match verus::run(&crate_dir, &c.name, false, None)? {
        Run::Verified(s) => report.lines.push(format!("baseline   {s}")),
        Run::ProofFailed(s, _) => return Err(format!("unmutated copy does not verify: {s}")),
        Run::BuildFailed(out) => return Err(format!("unmutated copy does not build:\n{out}")),
        Run::TimedOut(_) => return Err("unmutated copy timed out".into()),
    }
    let limit = mutant_limit(started.elapsed());
    let count = workers().min(mutations.len()).max(1);
    report.lines.push(format!(
        "time limit {}s per mutant run, {count} at a time",
        limit.as_secs()
    ));

    // One sandbox per worker: the first is the baseline's; the others are
    // copies of it, build output included, so no worker starts cold.
    let mut dirs = vec![crate_dir.clone()];
    for k in 1..count {
        let copy = sandbox.with_file_name(format!("{}.w{k}", c.name));
        if copy.exists() {
            std::fs::remove_dir_all(&copy).map_err(|e| format!("{}: {e}", copy.display()))?;
        }
        copy_tree(&sandbox, &copy)?;
        dirs.push(copy.join("crates").join(&c.name));
    }

    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: Vec<(usize, Result<Outcome, String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = dirs
            .iter()
            .map(|dir| {
                let (next, mutations, name) = (&next, &mutations, &c.name);
                scope.spawn(move || {
                    let mut done = Vec::new();
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(m) = mutations.get(i) else { break };
                        done.push((i, evaluate(dir, name, m, limit)));
                    }
                    done
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let mut results = results;
    results.sort_by_key(|(i, _)| *i);
    if results.len() != mutations.len() {
        return Err(format!(
            "{} of {} mutations ran (a worker stopped early)",
            results.len(),
            mutations.len()
        ));
    }
    for (_, result) in results {
        report.total = report.total.saturating_add(1);
        match result? {
            Outcome::Killed(line) => {
                report.killed = report.killed.saturating_add(1);
                report.lines.push(line);
            }
            Outcome::Incidental(line) => {
                report.incidental = report.incidental.saturating_add(1);
                report.lines.push(line);
            }
            Outcome::Survived(line) => {
                report.survived = report.survived.saturating_add(1);
                report.lines.push(line);
            }
            Outcome::Problem(p) => report.problems.push(p),
        }
    }
    Ok(report)
}

/// Apply one mutation in `crate_dir`, run it, restore the file, and judge
/// the result against `expect`. `Err` only for I/O failures.
fn evaluate(
    crate_dir: &Path,
    name: &str,
    m: &Mutation,
    limit: std::time::Duration,
) -> Result<Outcome, String> {
    let target = crate_dir.join(&m.file);
    let original =
        std::fs::read_to_string(&target).map_err(|e| format!("{}: {e}", target.display()))?;
    let hits = original.matches(&m.find).count();
    if hits != 1 {
        return Ok(Outcome::Problem(format!(
            "{}: `find` occurs {hits} times in {} (must be exactly once; the mutation is stale)",
            m.id, m.file
        )));
    }
    let mutated = original.replacen(&m.find, &m.replace, 1);
    std::fs::write(&target, mutated).map_err(|e| format!("{}: {e}", target.display()))?;
    let result = match &m.module {
        Some(module) => verus::module(crate_dir, name, module, Some(limit)),
        None => verus::run(crate_dir, name, false, Some(limit)),
    };
    std::fs::write(&target, &original).map_err(|e| format!("{}: {e}", target.display()))?;
    Ok(match (result?, m.expect) {
        (Run::TimedOut(t), _) => Outcome::Problem(format!(
            "{}: TIMED OUT after {}s and was stopped: the mutant makes Verus run \
             without end (for example `compute_only` evaluating a sequence index \
             out of range); rewrite the mutation so the examples stay evaluable",
            m.id,
            t.as_secs()
        )),
        (Run::ProofFailed(_, out), Expect::Killed) => {
            match check_certificate(crate_dir, name, m, &original, limit) {
                Ok(lemma) => Outcome::Killed(format!(
                    "killed     {}  (certified: violates {lemma}; first failure: {})",
                    m.id,
                    first_failure(&out)
                )),
                Err(e) => Outcome::Problem(format!("{}: {e}", m.id)),
            }
        }
        (Run::ProofFailed(_, out), Expect::KilledIncidentally) => Outcome::Incidental(format!(
            "incidental {}  (first failure: {}; {})",
            m.id,
            first_failure(&out),
            m.reason
        )),
        (Run::ProofFailed(s, out), Expect::Survives) => Outcome::Problem(format!(
            "{}: expected to survive but was killed ({s}; first failure: {}); \
             find out why before changing expect",
            m.id,
            first_failure(&out)
        )),
        (Run::Verified(_), Expect::Survives) => {
            Outcome::Survived(format!("survives   {}  (known gap: {})", m.id, m.reason))
        }
        (Run::Verified(_), Expect::Killed | Expect::KilledIncidentally) => Outcome::Problem(
            format!("{}: SURVIVED, but must be killed: {}", m.id, m.reason),
        ),
        (Run::BuildFailed(out), _) => Outcome::Problem(format!(
            "{}: mutated crate does not build, so it tests nothing:\n{out}",
            m.id
        )),
    })
}

/// How long one mutant (or certificate) run may take: five times the
/// crate's baseline verification, and at least ten minutes, unless
/// `CLAZEL_MUTANT_TIMEOUT_SECS` sets it. A mutant that runs longer is
/// stopped and fails the run, so a hang costs minutes, not CI's six hours.
fn mutant_limit(baseline: std::time::Duration) -> std::time::Duration {
    if let Some(secs) = std::env::var("CLAZEL_MUTANT_TIMEOUT_SECS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
    {
        return std::time::Duration::from_secs(secs);
    }
    baseline
        .saturating_mul(5)
        .max(std::time::Duration::from_secs(600))
}

/// Check a `killed` mutation's certificate: it must verify with the mutation
/// applied and fail without it. Returns the lemma's name. `original` is the
/// unmutated text of the mutated file; every file is restored before return.
fn check_certificate(
    crate_dir: &Path,
    name: &str,
    m: &Mutation,
    original: &str,
    limit: std::time::Duration,
) -> Result<String, String> {
    let cert = m
        .certificate
        .as_ref()
        .ok_or("expect \"killed\" requires a certificate (see xtask/src/mutate.rs)")?;
    let module = module_path(&cert.file)?;
    let target = crate_dir.join(&m.file);
    let cert_path = crate_dir.join(&cert.file);
    let cert_original =
        std::fs::read_to_string(&cert_path).map_err(|e| format!("{}: {e}", cert_path.display()))?;
    let reveals: String = cert
        .reveal
        .iter()
        .map(|p| format!("    reveal({p});\n"))
        .collect();
    let code = format!(
        "\n\nverus! {{\nproof fn {CERTIFICATE_FN}() {{\n{reveals}    assert({}) by (compute_only);\n    {};\n    assert(false);\n}}\n}} // verus!\n",
        cert.witness, cert.lemma
    );
    let mutated = original.replacen(&m.find, &m.replace, 1);
    let same_file = target == cert_path;
    // Run the certificate against one version of the mutated file.
    let attempt = |spec_text: &str| -> Result<Run, String> {
        std::fs::write(&target, spec_text).map_err(|e| e.to_string())?;
        let base = if same_file {
            spec_text
        } else {
            cert_original.as_str()
        };
        std::fs::write(&cert_path, format!("{base}{code}")).map_err(|e| e.to_string())?;
        verus::focus(crate_dir, name, &module, CERTIFICATE_FN, Some(limit))
    };
    let in_mutant = attempt(&mutated);
    let in_original = attempt(original);
    // Restore both files before judging anything.
    std::fs::write(&target, original).map_err(|e| e.to_string())?;
    if !same_file {
        std::fs::write(&cert_path, &cert_original).map_err(|e| e.to_string())?;
    }
    match in_mutant? {
        Run::Verified(_) => {}
        Run::ProofFailed(s, _) => {
            return Err(format!(
                "certificate does not verify in the mutant ({s}): either the witness \
                 is wrong or the theorem still holds (then it is killed-incidentally)"
            ));
        }
        Run::BuildFailed(out) => return Err(format!("certificate does not build:\n{out}")),
        Run::TimedOut(t) => {
            return Err(format!(
                "certificate TIMED OUT in the mutant after {}s and was stopped",
                t.as_secs()
            ));
        }
    }
    match in_original? {
        Run::ProofFailed(..) => {}
        Run::Verified(_) => {
            return Err(
                "certificate also verifies on the real spec, so it proves nothing \
                        about the mutation"
                    .into(),
            );
        }
        Run::BuildFailed(out) => {
            return Err(format!(
                "certificate does not build on the real spec:\n{out}"
            ));
        }
        Run::TimedOut(t) => {
            return Err(format!(
                "certificate TIMED OUT on the real spec after {}s and was stopped",
                t.as_secs()
            ));
        }
    }
    Ok(cert
        .lemma
        .split('(')
        .next()
        .unwrap_or(&cert.lemma)
        .trim()
        .to_owned())
}

/// `src/utf8/lemmas.rs` -> `utf8::lemmas`.
fn module_path(file: &str) -> Result<String, String> {
    let inner = file
        .strip_prefix("src/")
        .and_then(|f| f.strip_suffix(".rs"))
        .ok_or_else(|| format!("certificate file {file:?} must be src/<module>.rs"))?;
    let inner = inner.strip_suffix("/mod").unwrap_or(inner);
    if inner == "lib" || inner.is_empty() {
        return Err("certificate file must be a module, not the crate root".into());
    }
    Ok(inner.replace('/', "::"))
}

/// The first error message and its location in Verus output, e.g.
/// "postcondition not satisfied at src/utf8/lemmas.rs:182:1".
fn first_failure(out: &str) -> String {
    let mut lines = out.lines();
    while let Some(l) = lines.next() {
        if let Some(msg) = l.strip_prefix("error: ") {
            let loc = lines
                .find_map(|l| l.trim_start().strip_prefix("--> "))
                .map(|loc| loc.rsplit_once("crates/").map_or(loc, |(_, rest)| rest))
                .and_then(|loc| loc.split_once('/').map(|(_, path)| path))
                .unwrap_or("unknown location");
            return format!("{msg} at {loc}");
        }
    }
    "no error message found".into()
}

/// A one-crate copy of the workspace under `target/xtask-mutate/<crate>/`,
/// plus the workspace crates it depends on.
/// Its own target directory keeps dependency builds warm between runs.
fn make_sandbox(c: &Crate, root: &Path) -> Result<PathBuf, String> {
    let sandbox = root.join("target").join("xtask-mutate").join(&c.name);
    let crate_copy = sandbox.join("crates").join(&c.name);
    if crate_copy.exists() {
        std::fs::remove_dir_all(&crate_copy)
            .map_err(|e| format!("{}: {e}", crate_copy.display()))?;
    }
    copy_dir(&c.dir, &crate_copy)?;
    // Workspace crates it depends on (e.g. `clazel-percent` on
    // `clazel-encoding`), so path dependencies resolve. They are only
    // built, never mutated; Cargo makes them members implicitly.
    // Transitive ones too (`clazel-cookie` on `clazel-url` on
    // `clazel-encoding`): follow `path = "../<crate>"` lines.
    let mut pending: Vec<String> = c.deps.iter().map(|(d, _)| d.clone()).collect();
    let mut seen: Vec<String> = Vec::new();
    while let Some(dep) = pending.pop() {
        if seen.contains(&dep) {
            continue;
        }
        seen.push(dep.clone());
        let from = root.join("crates").join(&dep);
        if !from.join("Cargo.toml").is_file() {
            continue;
        }
        if let Ok(text) = std::fs::read_to_string(from.join("Cargo.toml")) {
            for line in text.lines() {
                if let Some(rest) = line.split("path = \"../").nth(1)
                    && let Some(name) = rest.split('"').next()
                {
                    pending.push(name.to_owned());
                }
            }
        }
        let to = sandbox.join("crates").join(dep);
        if to.exists() {
            std::fs::remove_dir_all(&to).map_err(|e| format!("{}: {e}", to.display()))?;
        }
        copy_dir(&from, &to)?;
    }
    for f in ["Cargo.lock", "rust-toolchain.toml"] {
        std::fs::copy(root.join(f), sandbox.join(f)).map_err(|e| format!("copy {f}: {e}"))?;
    }
    // The workspace manifest, with only this crate as a member.
    let manifest =
        std::fs::read_to_string(root.join("Cargo.toml")).map_err(|e| format!("Cargo.toml: {e}"))?;
    let members = format!("members = [\"crates/{}\"]", c.name);
    let mut replaced = false;
    let rewritten: Vec<String> = manifest
        .lines()
        .map(|l| {
            if l.trim_start().starts_with("members =") {
                replaced = true;
                members.clone()
            } else {
                l.to_owned()
            }
        })
        .collect();
    if !replaced {
        return Err("Cargo.toml: no `members = [...]` line to rewrite".into());
    }
    std::fs::write(sandbox.join("Cargo.toml"), rewritten.join("\n"))
        .map_err(|e| format!("sandbox Cargo.toml: {e}"))?;
    Ok(sandbox)
}

/// Copy a whole sandbox, its build output included.
fn copy_tree(from: &Path, to: &Path) -> Result<(), String> {
    copy_entries(from, to, true)
}

fn copy_dir(from: &Path, to: &Path) -> Result<(), String> {
    copy_entries(from, to, false)
}

/// Copy `from` to `to`; `target` directories only if `with_target`.
fn copy_entries(from: &Path, to: &Path, with_target: bool) -> Result<(), String> {
    std::fs::create_dir_all(to).map_err(|e| format!("{}: {e}", to.display()))?;
    let entries = std::fs::read_dir(from).map_err(|e| format!("{}: {e}", from.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("{}: {e}", from.display()))?;
        let path = entry.path();
        if !with_target && path.file_name().is_some_and(|n| n == "target") {
            continue;
        }
        let dest = to.join(entry.file_name());
        if path.is_dir() {
            copy_entries(&path, &dest, with_target)?;
        } else {
            std::fs::copy(&path, &dest).map_err(|e| format!("{}: {e}", path.display()))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn reveal_entries_are_paths() {
        assert!(super::is_path("super::data::IDNA_MAPPING_0"));
        assert!(super::is_path("T"));
        assert!(!super::is_path("assume(false)"));
        assert!(!super::is_path("a::"));
        assert!(!super::is_path("a; admit()"));
        assert!(!super::is_path(""));
    }
}
