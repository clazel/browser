//! The vendored WPT `dom/` tests (`tests/data/wpt-web/dom/nodes/`,
//! `collections/`), run through the page's bindings with a stand-in for
//! `testharness.js` (`tests/support/standin-dom-harness.js`, which says why
//! the real one cannot be used yet).
//!
//! For each test file: the HTML is parsed with `clazel-treebuilder`, the
//! stand-in is run, then each `<script>` in document order (the harness
//! scripts are skipped; another `src` is read from the vendored tree, and a
//! file that is not there makes the whole test *blocked*, named). A subtest
//! is a pass only if its function ran and every assertion held; an
//! `async_test` or `promise_test` is *skipped*, never a pass.
//!
//! `tests/wpt_dom_expected.txt` is the committed result, one line per
//! file: `pass fail skip blocked path`. The test fails if any line differs
//! (a regression, or an improvement that has not been written down). To
//! write it after a change: `CLAZEL_WPT_DOM_BLESS=1 cargo test -p
//! clazel-web --test wpt_dom`. With `--nocapture` it prints every failing
//! subtest and why.
//!
//! Not run: the `.xhtml`, `.svg` and `.xml` tests (there is no XML parser in
//! the page), files of other directories than the three, and the
//! `dom/events` tests, which `tests/events.rs` and `tests/bindings.rs` cover
//! with transcriptions.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use clazel_dom::exec::{Arena, ExecKind};
use clazel_js::{Config, Key, Limits, Realm, Runtime};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::page::{HookCall, LogLevel, NoHooks, Page, run_script};

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

const HARNESS: &str = include_str!("support/standin-dom-harness.js");
const DIRS: &[&str] = &["dom/nodes", "dom/collections"];

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/wpt-web")
}

fn points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn text(v: &[u32]) -> String {
    v.iter().filter_map(|&c| char::from_u32(c)).collect()
}

/// The `<script>` elements of the document, in tree order: `src` and the
/// inline text.
fn scripts(arena: &Arena) -> Vec<(Option<String>, String)> {
    let mut out = Vec::new();
    let mut stack = vec![0usize];
    while let Some(n) = stack.pop() {
        if let ExecKind::Element {
            local_name,
            attributes,
            ..
        } = arena.kind(n)
            && text(local_name) == "script"
        {
            let src = attributes
                .iter()
                .find(|a| text(&a.local_name) == "src")
                .map(|a| text(&a.value));
            let mut body = String::new();
            for &c in arena.children(n) {
                if let ExecKind::Text { data } = arena.kind(c) {
                    body.push_str(&text(data));
                }
            }
            out.push((src, body));
        }
        stack.extend(arena.children(n).iter().rev().copied());
    }
    out
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Outcome {
    pass: u32,
    fail: u32,
    skip: u32,
    blocked: Option<String>,
    details: String,
}

fn limits() -> Limits {
    Limits {
        heap_bytes: 512 << 20,
        value_stack_bytes: 8 << 20,
        native_depth: 400,
        nesting_depth: 1000,
        ..Limits::unlimited()
    }
}

fn run_in(rt: &mut Runtime, realm: &Realm, name: &str, source: &str, details: &mut String) {
    if let Err(e) = run_script(rt, realm, name, source) {
        let last = rt
            .scope(|scope| -> clazel_js::Result<Option<String>> {
                Ok(scope
                    .host_mut::<Page>()?
                    .hook_calls()
                    .iter()
                    .rev()
                    .find_map(|c| match c {
                        HookCall::Log(LogLevel::Error, t) => Some(t.clone()),
                        _ => None,
                    }))
            })
            .ok()
            .flatten();
        let _ = writeln!(
            details,
            "SCRIPT ERROR in {name}: {}",
            last.unwrap_or_else(|| format!("{e:?}"))
        );
    }
}

fn run_file(rel: &str) -> Outcome {
    let path = root().join(rel);
    let Ok(source) = std::fs::read_to_string(&path) else {
        return Outcome {
            blocked: Some(format!("cannot read {rel}")),
            ..Outcome::default()
        };
    };
    let is_js = rel.ends_with(".js");
    let mut scripts_to_run: Vec<(String, String)> = Vec::new();
    let html: String;
    if is_js {
        // `.window.js` and `.any.js`: the test is the script; META lines
        // name more scripts.
        html = "<!DOCTYPE html><html><head><title>t</title></head><body></body></html>".to_owned();
        for line in source.lines() {
            if let Some(m) = line.strip_prefix("// META: script=") {
                if m.contains("testharness") {
                    continue;
                }
                let dep = if let Some(abs) = m.strip_prefix('/') {
                    root().join(abs)
                } else {
                    path.parent().unwrap_or(&path).join(m)
                };
                match std::fs::read_to_string(&dep) {
                    Ok(t) => scripts_to_run.push((m.to_owned(), t)),
                    Err(_) => {
                        return Outcome {
                            blocked: Some(format!("needs {m}")),
                            ..Outcome::default()
                        };
                    }
                }
            }
        }
        scripts_to_run.push((rel.to_owned(), source));
    } else {
        html = source;
    }
    let input = points(&html);
    let (parsed, _) = parse_real(
        &NoEnc,
        &input,
        points("https://wpt.test/dom/x.html"),
        true,
        false,
    );
    if !is_js {
        for (src, body) in scripts(&parsed.arena) {
            match src {
                Some(s) if s.contains("testharness") => {}
                Some(s) => {
                    let dep = if let Some(abs) = s.strip_prefix('/') {
                        root().join(abs)
                    } else {
                        path.parent().unwrap_or(&path).join(&s)
                    };
                    match std::fs::read_to_string(&dep) {
                        Ok(t) => scripts_to_run.push((s, t)),
                        Err(_) => {
                            return Outcome {
                                blocked: Some(format!("needs {s}")),
                                ..Outcome::default()
                            };
                        }
                    }
                }
                None => scripts_to_run.push((format!("{rel} (inline)"), body)),
            }
        }
    }
    let Ok((mut rt, realm)) = Page::new(
        parsed.arena,
        "https://wpt.test/dom/x.html",
        Box::new(NoHooks),
    )
    .into_runtime(Config::new(limits())) else {
        return Outcome {
            blocked: Some("the runtime did not start".to_owned()),
            ..Outcome::default()
        };
    };
    let mut details = String::new();
    run_in(
        &mut rt,
        &realm,
        "standin-dom-harness.js",
        HARNESS,
        &mut details,
    );
    for (name, body) in scripts_to_run {
        run_in(&mut rt, &realm, &name, &body, &mut details);
    }
    run_in(
        &mut rt,
        &realm,
        "summary",
        "var r = __summary();",
        &mut details,
    );
    let summary = rt
        .scope(|scope| -> clazel_js::Result<String> {
            let g = scope.global(&realm)?;
            let r = scope.get(g, Key::Str("r"))?;
            let s = scope.to_string(r)?;
            scope.string_to_string_lossy(s)
        })
        .unwrap_or_default();
    let (head, rest) = summary.split_once('\n').unwrap_or((&summary, ""));
    let mut it = head.split('|').map(|n| n.parse::<u32>().unwrap_or(0));
    let (pass, fail, skip) = (
        it.next().unwrap_or(0),
        it.next().unwrap_or(0),
        it.next().unwrap_or(0),
    );
    details.push_str(rest);
    Outcome {
        pass,
        fail,
        skip,
        blocked: None,
        details,
    }
}

fn files() -> Vec<String> {
    let mut out = Vec::new();
    for dir in DIRS {
        let Ok(rd) = std::fs::read_dir(root().join(dir)) else {
            continue;
        };
        for e in rd.flatten() {
            let name = e.file_name().to_string_lossy().into_owned();
            let ok = name.ends_with(".html")
                || name.ends_with(".window.js")
                || name.ends_with(".any.js");
            if ok {
                out.push(format!("{dir}/{name}"));
            }
        }
    }
    out.sort();
    out
}

#[test]
#[cfg_attr(
    miri,
    ignore = "reads the vendored WPT files, which Miri's isolation forbids"
)]
fn wpt_dom_tests_through_the_bindings() {
    let mut table = String::new();
    let (mut pass, mut fail, mut skip, mut blocked, mut total_files) = (0, 0, 0, 0, 0);
    for rel in files() {
        total_files += 1;
        let o = run_file(&rel);
        pass += o.pass;
        fail += o.fail;
        skip += o.skip;
        let b = match &o.blocked {
            Some(why) => {
                blocked += 1;
                why.as_str()
            }
            None => "-",
        };
        let _ = writeln!(
            table,
            "{} {} {} {} {rel}",
            o.pass,
            o.fail,
            o.skip,
            b.replace(' ', "_")
        );
        if !o.details.is_empty() {
            eprintln!("== {rel}\n{}", o.details.trim_end());
        }
    }
    eprintln!(
        "wpt-dom: {total_files} files, {blocked} blocked; subtests: {pass} passed, {fail} failed, {skip} skipped"
    );
    let expected_path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/wpt_dom_expected.txt");
    if std::env::var_os("CLAZEL_WPT_DOM_BLESS").is_some() {
        assert!(
            std::fs::write(&expected_path, &table).is_ok(),
            "write the expected results"
        );
        return;
    }
    let expected = std::fs::read_to_string(&expected_path).unwrap_or_default();
    assert_eq!(
        table, expected,
        "the WPT dom results changed: write them with CLAZEL_WPT_DOM_BLESS=1"
    );
}
