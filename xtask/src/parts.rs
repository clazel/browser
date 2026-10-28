//! `verify --part`: the full verification split into parts that run on
//! separate machines (CI runs one job per part; `.github/workflows/ci.yml`).
//!
//! - `base`: static checks, rustfmt, clippy and tests, workspace-wide.
//! - `miri [<names>]`: static checks and the tests under Miri, workspace-wide
//!   or for the named crates only (comma-separated). CI's macOS job names
//!   `clazel-sys`: it is the one crate with code that compiles only there and
//!   has tests Miri can run, and every other crate's tests are the same
//!   portable Rust the Linux job runs.
//! - `crate <names>`: static checks, then Kani, Verus, line counts,
//!   mutations and conformance for one crate or several (comma-separated).
//!   On success it writes what it measured to `<dir>/<name>.json` for each,
//!   tagged with the commit it ran on.
//! - `assemble`: static checks, then the README table built from every
//!   crate's file. It fails if a workspace crate has no file, or a file is
//!   from another commit, so a part that did not run, or ran on other
//!   code, cannot be counted.
//!
//! Together the parts run exactly the checks of a single `cargo xtask
//! verify`. Each part passing says only that part passed: the gate is all of
//! them passing on the same commit, which CI expresses by making `assemble`
//! depend on the others (docs/VERIFICATION.md, "Local and CI runs").

use std::path::Path;
use std::process::Command;

use serde_json::{Value, json};

use crate::conformance::Suite;
use crate::report::{Lines, Metrics, Mutations};

/// The commit being verified, so parts from different commits never mix.
/// With uncommitted changes to tracked files it ends in `+dirty`, so a
/// local run is never recorded as the commit itself (CI's checkouts are
/// clean).
pub fn head() -> Result<String, String> {
    let git = |args: &[&str]| -> Result<String, String> {
        let out = Command::new("git")
            .args(args)
            .output()
            .map_err(|e| format!("cannot run git: {e}"))?;
        if out.status.success() {
            Ok(String::from_utf8_lossy(&out.stdout).trim().to_owned())
        } else {
            Err(format!(
                "git {}: {}",
                args.join(" "),
                String::from_utf8_lossy(&out.stderr).trim()
            ))
        }
    };
    let commit = git(&["rev-parse", "HEAD"])?;
    let dirty = !git(&["status", "--porcelain", "--untracked-files=no"])?.is_empty();
    Ok(if dirty {
        format!("{commit}+dirty")
    } else {
        commit
    })
}

/// The measurements a `crate` part made, as JSON.
pub fn to_json(name: &str, commit: &str, m: &Metrics) -> String {
    let v = json!({
        "crate": name,
        "commit": commit,
        "verus": m.verus,
        "kani": m.kani,
        "lines": m.lines.as_ref().map(|l| json!({"spec": l.spec, "proof": l.proof, "exec": l.exec})),
        "mutations": m.mutations.as_ref().map(|x| json!({
            "killed": x.killed, "incidental": x.incidental, "survived": x.survived, "total": x.total,
        })),
        "conformance": m.conformance.as_ref().map(|suites| suites.iter().map(|s| json!({
            "name": s.name, "pass": s.pass, "xfail": s.xfail, "fail": s.fail, "total": s.total,
        })).collect::<Vec<_>>()),
    });
    format!("{v:#}\n")
}

/// Write a `crate` part's file.
pub fn write(dir: &Path, name: &str, commit: &str, m: &Metrics) -> Result<String, String> {
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let path = dir.join(format!("{name}.json"));
    std::fs::write(&path, to_json(name, commit, m))
        .map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(path.display().to_string())
}

fn num(v: &Value, k: &str) -> Result<u64, String> {
    v.get(k)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("missing number {k:?}"))
}

fn usize_of(v: &Value, k: &str) -> Result<usize, String> {
    usize::try_from(num(v, k)?).map_err(|e| format!("{k}: {e}"))
}

fn opt_str(v: &Value, k: &str) -> Result<Option<String>, String> {
    match v.get(k) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(s)) => Ok(Some(s.clone())),
        Some(_) => Err(format!("{k:?} is not a string")),
    }
}

fn present<'a>(v: &'a Value, k: &str) -> Option<&'a Value> {
    v.get(k).filter(|x| !x.is_null())
}

/// Read a `crate` part's file into the measured fields of `into`, checking
/// it is for `name` at `commit`.
pub fn read_into(text: &str, name: &str, commit: &str, into: &mut Metrics) -> Result<(), String> {
    let v: Value = serde_json::from_str(text).map_err(|e| format!("not JSON: {e}"))?;
    if v.get("crate").and_then(Value::as_str) != Some(name) {
        return Err(format!("is not for crate {name}"));
    }
    match v.get("commit").and_then(Value::as_str) {
        Some(c) if c == commit => {}
        other => return Err(format!("is from commit {other:?}, not {commit}")),
    }
    into.verus = opt_str(&v, "verus")?;
    into.kani = opt_str(&v, "kani")?;
    into.lines = present(&v, "lines")
        .map(|l| -> Result<Lines, String> {
            Ok(Lines {
                spec: num(l, "spec")?,
                proof: num(l, "proof")?,
                exec: num(l, "exec")?,
            })
        })
        .transpose()?;
    into.mutations = present(&v, "mutations")
        .map(|x| -> Result<Mutations, String> {
            Ok(Mutations {
                killed: usize_of(x, "killed")?,
                incidental: usize_of(x, "incidental")?,
                survived: usize_of(x, "survived")?,
                total: usize_of(x, "total")?,
            })
        })
        .transpose()?;
    into.conformance = present(&v, "conformance")
        .map(|c| -> Result<Vec<Suite>, String> {
            c.as_array()
                .ok_or("\"conformance\" is not an array")?
                .iter()
                .map(|s| {
                    Ok(Suite {
                        name: s
                            .get("name")
                            .and_then(Value::as_str)
                            .ok_or("suite without a name")?
                            .to_owned(),
                        pass: num(s, "pass")?,
                        xfail: num(s, "xfail")?,
                        fail: num(s, "fail")?,
                        total: num(s, "total")?,
                    })
                })
                .collect()
        })
        .transpose()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{read_into, to_json};
    use crate::conformance::Suite;
    use crate::report::{Lines, Metrics, Mutations};

    fn measured() -> Metrics {
        Metrics {
            verus: Some("5 verified, 0 errors".into()),
            kani: Some("2 successfully verified harnesses, 0 failures, 2 total".into()),
            lines: Some(Lines {
                spec: 1,
                proof: 2,
                exec: 3,
            }),
            mutations: Some(Mutations {
                killed: 4,
                incidental: 1,
                survived: 0,
                total: 5,
            }),
            conformance: Some(vec![Suite {
                name: "WPT x".into(),
                pass: 9,
                xfail: 1,
                fail: 0,
                total: 10,
            }]),
            ..Metrics::default()
        }
    }

    #[test]
    fn round_trip() -> Result<(), String> {
        let m = measured();
        let mut back = Metrics::default();
        read_into(&to_json("a", "c0ffee", &m), "a", "c0ffee", &mut back)?;
        assert_eq!(back.verus, m.verus);
        assert_eq!(back.kani, m.kani);
        assert_eq!(back.lines, m.lines);
        assert_eq!(back.mutations, m.mutations);
        assert_eq!(
            back.conformance.map(|s| s.len()),
            m.conformance.map(|s| s.len())
        );
        Ok(())
    }

    #[test]
    fn unmeasured_fields_stay_unmeasured() -> Result<(), String> {
        let mut back = Metrics::default();
        read_into(&to_json("a", "c", &Metrics::default()), "a", "c", &mut back)?;
        assert!(back.verus.is_none() && back.lines.is_none() && back.conformance.is_none());
        Ok(())
    }

    #[test]
    fn another_crate_or_commit_is_refused() {
        let text = to_json("a", "c1", &measured());
        assert!(read_into(&text, "b", "c1", &mut Metrics::default()).is_err());
        assert!(read_into(&text, "a", "c2", &mut Metrics::default()).is_err());
    }
}
