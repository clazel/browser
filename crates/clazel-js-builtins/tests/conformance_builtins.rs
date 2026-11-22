//! Test262 through the interpreter with the built-ins of `clazel-js-builtins`
//! installed: the scripts the compiler accepts, run in a fresh [`Vm`] each,
//! with a minimal native harness (item 7.9, first group). It is the runner of
//! `clazel-js-vm`'s `conformance_interp.rs` with `install` called first, so
//! the two counts compare; the difference is what the built-ins unlock.
//!
//! The suite is every row of the generated Test262 table (the same table the
//! compiler's test reads), and each test lands in exactly one class:
//!
//! - **pass**: it ran in every mode it asks for (sloppy and strict, or the one
//!   its flags name) and finished without throwing, or threw the error type
//!   its `negative:` block names;
//! - **xfail**, an expected failure with a named reason (printed, with the
//!   count of each): the test needs something this slice does not have; or
//! - **fail**: it ran and went wrong (an assertion failed, an exception other
//!   than the expected one, the VM reported an internal error or ran out of
//!   its step budget). This must be zero, and `cargo xtask verify` fails the
//!   run otherwise.
//!
//! The harness is native, as phase-7.md asks of the shell's `$262` ("built
//! from public calls only"): `assert`, `assert.sameValue`,
//! `assert.notSameValue`, `assert.throws` (which compares `thrown.constructor`
//! with the expected constructor, as `assert.js` does), and a `$262` object
//! with `global` and `gc`; its other members report "not yet" when called. A
//! test that includes any other harness file (`propertyHelper.js`,
//! `compareArray.js`, ...) is an expected failure: they need `Array`,
//! `Symbol` or accessor properties, later groups of 7.9.
//!
//! A script that throws an uncaught `ReferenceError` for a name that is not
//! defined is classed by the name ("global X is missing"): the built-ins
//! (`Object`, `Array`, `Symbol`, ...) are 7.9, and a test that reaches one is
//! waiting for it. A test that catches the error itself is judged on what it
//! does next.
//!
//! The counts are in units of tests, not runs.

use clazel_js_heap::value::{Decoded, Value};
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::Program;
use clazel_js_vm::compile::{CompileError, compile_script};
use clazel_js_vm::interp::{Abrupt, Config, Vm};
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

/// A test's row in the generated table.
struct Case {
    path: &'static str,
    flags: &'static [&'static str],
    features: &'static [&'static str],
    includes: &'static [&'static str],
    negative: Option<(&'static str, &'static str)>,
    expect: Expect,
}

/// Whether a test is expected to pass, and if not why.
enum Expect {
    Run,
    Fail(&'static str),
}

include!("../../clazel-js-lexer/tests/generated/test262.rs");

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../clazel-js-lexer/tests/data/test262/test")
}

/// The most steps (back-edges and calls) one test run may take.
const BUDGET: u64 = 2_000_000;

// -----------------------------------------------------------------------
// The native harness
// -----------------------------------------------------------------------

/// Throws what a failed assertion throws: an object with `name`
/// `Test262Error` and the message.
fn test262_error(vm: &mut Vm, msg: &str) -> Abrupt {
    let make = |vm: &mut Vm| -> Result<Value, Abrupt> {
        let o = vm.new_object()?;
        let n = vm.new_string("Test262Error")?;
        let m = vm.new_string(msg)?;
        vm.define_property(o, "name", n)?;
        vm.define_property(o, "message", m)?;
        Ok(o)
    };
    match make(vm) {
        Ok(o) => Abrupt::Throw(o),
        Err(e) => e,
    }
}

/// The message argument of an assertion, as text.
fn message(vm: &mut Vm, v: Option<&Value>) -> String {
    match v {
        Some(v) if *v != Value::UNDEFINED => vm.describe(*v),
        _ => String::new(),
    }
}

/// SameValue, §7.2.10 (strings by content, Numbers by value with NaN equal to
/// NaN and `+0` distinct from `-0`).
fn same_value(vm: &Vm, a: Value, b: Value) -> bool {
    use clazel_js_vm::numeric::num;
    if let (Some(x), Some(y)) = (num(a), num(b)) {
        let (x, y) = (x.to_f64(), y.to_f64());
        return if x.is_nan() || y.is_nan() {
            x.is_nan() && y.is_nan()
        } else {
            x.to_bits() == y.to_bits()
        };
    }
    if let (Some(x), Some(y)) = (vm.heap().string(a), vm.heap().string(b)) {
        return x == y;
    }
    a == b
}

fn assert_true(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    if args.first() == Some(&Value::TRUE) {
        return Ok(Value::UNDEFINED);
    }
    let m = message(vm, args.get(1));
    Err(test262_error(
        vm,
        &format!("Expected true but got something else. {m}"),
    ))
}

fn assert_same_value(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (a, b) = (
        args.first().copied().unwrap_or(Value::UNDEFINED),
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    );
    if same_value(vm, a, b) {
        return Ok(Value::UNDEFINED);
    }
    let (da, db) = (vm.describe(a), vm.describe(b));
    let m = message(vm, args.get(2));
    Err(test262_error(
        vm,
        &format!("Expected SameValue({da}, {db}) to be true. {m}"),
    ))
}

fn assert_not_same_value(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let (a, b) = (
        args.first().copied().unwrap_or(Value::UNDEFINED),
        args.get(1).copied().unwrap_or(Value::UNDEFINED),
    );
    if !same_value(vm, a, b) {
        return Ok(Value::UNDEFINED);
    }
    let da = vm.describe(a);
    let m = message(vm, args.get(2));
    Err(test262_error(
        vm,
        &format!("Expected SameValue({da}, {da}) to be false. {m}"),
    ))
}

fn assert_throws(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let ctor = args.first().copied().unwrap_or(Value::UNDEFINED);
    let f = args.get(1).copied().unwrap_or(Value::UNDEFINED);
    match vm.call(f, Value::UNDEFINED, &[]) {
        Ok(_) => Err(test262_error(
            vm,
            "Expected an exception, but none was thrown",
        )),
        Err(Abrupt::Throw(e)) => {
            // assert.js: `thrown.constructor !== expectedErrorConstructor`.
            let same_ctor = vm.get_named(e, "constructor")? == ctor && ctor != Value::UNDEFINED;
            if same_ctor {
                Ok(Value::UNDEFINED)
            } else {
                let d = vm.describe(e);
                Err(test262_error(
                    vm,
                    &format!("Expected a different error, got {d}"),
                ))
            }
        }
        Err(other) => Err(other),
    }
}

fn not_yet(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Err(Abrupt::NotYet("$262 member".into()))
}

fn ignore(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    Ok(Value::UNDEFINED)
}

/// `harness/sta.js`, compiled once: it defines `Test262Error`.
fn sta_program() -> Option<&'static Program> {
    static STA: OnceLock<Option<Program>> = OnceLock::new();
    STA.get_or_init(|| {
        let path = root().join("../harness/sta.js");
        let text = std::fs::read_to_string(path).ok()?;
        let src: Vec<u32> = text.chars().map(u32::from).collect();
        let ast = parse(&src, SourceGoal::Script).ok()?;
        compile_script(&ast, &src).ok()
    })
    .as_ref()
}

/// Installs `assert` (unless `raw`), `print` and `$262`, and runs the real
/// `sta.js` (unless `raw`).
fn install_harness(vm: &mut Vm, raw: bool) -> Result<(), Abrupt> {
    if !raw {
        let sta = sta_program().ok_or(Abrupt::Internal("sta.js does not compile"))?;
        let script = vm.load(sta)?;
        vm.run(&script)?;
        let assert = vm.new_native("assert", 2, assert_true)?;
        for (name, len, f) in [
            (
                "sameValue",
                3,
                assert_same_value as clazel_js_vm::interp::NativeFn,
            ),
            ("notSameValue", 3, assert_not_same_value),
            ("throws", 3, assert_throws),
        ] {
            let n = vm.new_native(name, len, f)?;
            vm.define_property(assert, name, n)?;
        }
        vm.define_global("assert", assert)?;
    }
    let print = vm.new_native("print", 1, ignore)?;
    vm.define_global("print", print)?;
    let host = vm.new_object()?;
    let g = vm.global();
    vm.define_property(host, "global", g)?;
    for name in ["gc", "createRealm", "evalScript", "detachArrayBuffer"] {
        let f = vm.new_native(name, 0, if name == "gc" { ignore } else { not_yet })?;
        vm.define_property(host, name, f)?;
    }
    vm.define_global("$262", host)
}

// -----------------------------------------------------------------------
// Running and classifying
// -----------------------------------------------------------------------

/// What happened to one run of a test.
enum Outcome {
    Pass,
    /// An expected failure, with its category.
    Xfail(String),
    /// An unexpected failure, with what happened.
    Fail(String),
}

/// The text of a thrown error's `name` and `message`, if it is an object.
fn thrown(vm: &mut Vm, v: Value) -> (Option<String>, Option<String>) {
    if !matches!(v.decode(), Decoded::Ref(_)) {
        return (None, None);
    }
    let name = vm.get_named(v, "name").ok().and_then(|n| vm.string_text(n));
    // An error made by `new Test262Error` has no own `name`: its constructor's
    // name stands for it.
    let name = name.or_else(|| {
        let c = vm.get_named(v, "constructor").ok()?;
        let n = vm.get_named(c, "name").ok()?;
        vm.string_text(n)
    });
    let msg = vm
        .get_named(v, "message")
        .ok()
        .and_then(|n| vm.string_text(n));
    (name, msg)
}

/// Runs one source in a new VM and classifies the result.
fn run_one(case: &Case, src: &[u32], goal: SourceGoal) -> Outcome {
    let Ok(ast) = parse(src, goal) else {
        return Outcome::Fail("does not parse".into());
    };
    let program = match compile_script(&ast, src) {
        Ok(p) => p,
        Err(CompileError::NotYetCompiled { feature, .. }) => {
            return Outcome::Xfail(format!("the compiler does not yet compile {feature}"));
        }
        Err(e) => return Outcome::Fail(format!("compile error: {e}")),
    };
    let Ok(mut vm) = Vm::new(Config::default()) else {
        return Outcome::Fail("could not make a VM".into());
    };
    if let Err(e) = clazel_js_builtins::install(&mut vm) {
        return Outcome::Fail(format!("install: {e:?}"));
    }
    if let Err(e) = install_harness(&mut vm, case.flags.contains(&"raw")) {
        return Outcome::Fail(format!("harness: {e:?}"));
    }
    let script = match vm.load(&program) {
        Ok(s) => s,
        Err(Abrupt::NotYet(what)) => {
            return Outcome::Xfail(format!("the VM does not yet load {what}"));
        }
        Err(e) => return Outcome::Fail(format!("load: {e:?}")),
    };
    vm.set_budget(BUDGET);
    let result = vm.run(&script);
    let negative = case.negative.filter(|(phase, _)| *phase == "runtime");
    match result {
        Ok(_) => match negative {
            None => Outcome::Pass,
            Some((_, ty)) => Outcome::Fail(format!("expected {ty}, nothing was thrown")),
        },
        Err(Abrupt::NotYet(what)) => {
            Outcome::Xfail(format!("the VM does not yet implement {what}"))
        }
        Err(Abrupt::Throw(e)) => {
            let (name, msg) = thrown(&mut vm, e);
            if let Some((_, ty)) = negative
                && name.as_deref() == Some(ty)
            {
                return Outcome::Pass;
            }
            if name.as_deref() == Some("ReferenceError")
                && let Some(m) = &msg
                && let Some(var) = m.strip_suffix(" is not defined")
            {
                return Outcome::Xfail(format!("global {var} is missing (a built-in, 7.9)"));
            }
            // `assert.throws` reports a missing global the same way, inside
            // its own error: "Expected a different error, got ReferenceError:
            // eval is not defined" (the compiler's third slice, #230, compiles
            // the RegExp literal tests that reach `eval` this way).
            if name.as_deref() == Some("Test262Error")
                && let Some(m) = &msg
                && let Some((_, got)) = m.split_once("got ReferenceError: ")
                && let Some(var) = got.strip_suffix(" is not defined")
            {
                return Outcome::Xfail(format!("global {var} is missing (a built-in, 7.9)"));
            }
            if name.as_deref() == Some("TypeError")
                && let Some(m) = &msg
                && m == "undefined is not a function"
            {
                return Outcome::Xfail(
                    "calls a method that is not there (a built-in of 7.9: Function.prototype.call, Object.prototype.toString, ...)"
                        .into(),
                );
            }
            match negative {
                Some((_, ty)) => Outcome::Fail(format!("expected {ty}, got {}", vm.describe(e))),
                None => Outcome::Fail(vm.describe(e)),
            }
        }
        Err(Abrupt::Terminated) => Outcome::Fail("step budget exhausted".into()),
        Err(e) => Outcome::Fail(format!("{e:?}")),
    }
}

fn bump(m: &mut BTreeMap<String, usize>, k: String) {
    let e = m.entry(k).or_insert(0);
    *e = e.saturating_add(1);
}

/// The runs of a test: its goal and whether to prefix a Use Strict Directive.
fn runs(case: &Case) -> Vec<(SourceGoal, bool)> {
    let has = |f: &str| case.flags.contains(&f);
    if has("raw") || has("noStrict") {
        vec![(SourceGoal::Script, false)]
    } else if has("onlyStrict") {
        vec![(SourceGoal::Script, true)]
    } else {
        vec![(SourceGoal::Script, false), (SourceGoal::Script, true)]
    }
}

/// The harness files the native harness stands in for.
const NATIVE_INCLUDES: [&str; 2] = ["assert.js", "sta.js"];

/// Tests that run and give a different result for a known reason, each with
/// its reason: expected failures.
const KNOWN_GAPS: &[(&str, &str)] = &[(
    "language/identifier-resolution/assign-to-global-undefined.js",
    "strict assignment to an unresolvable reference throws before the right-hand side runs (§13.15.2 step 1.a, ResolveBinding first); SetGlobal checks when it runs, after it, and the op list has no resolve-first op",
)];

/// Classifies a test that is not run, or `None` if it should be.
fn not_run(case: &Case) -> Option<String> {
    if let Some((_, why)) = KNOWN_GAPS.iter().find(|(p, _)| *p == case.path) {
        return Some((*why).to_string());
    }
    if let Expect::Fail(reason) = case.expect {
        return Some(format!("expected failure of the table: {reason}"));
    }
    if matches!(case.negative, Some((phase, _)) if phase == "parse" || phase == "early" || phase == "resolution")
    {
        return Some("negative parse/early test (the parser's evidence, not run)".into());
    }
    if case.flags.contains(&"module") {
        return Some("module (the compiler's third slice, an open pull request)".into());
    }
    if case.flags.contains(&"async") {
        return Some("async test (Promises and the job queue, 7.9)".into());
    }
    if case.path.starts_with("harness/") {
        return Some("test of the real harness files (replaced by the native harness)".into());
    }
    case.includes
        .iter()
        .find(|i| !NATIVE_INCLUDES.contains(i))
        .map(|i| format!("includes {i} (needs built-ins of later groups of 7.9)"))
}

#[test]
#[cfg_attr(miri, ignore = "reads files; Miri runs the other tests")]
fn test262_through_the_interpreter() -> Result<(), String> {
    assert_eq!(TREE_SHA256.len(), 64);
    let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
    let mut categories: BTreeMap<String, usize> = BTreeMap::new();
    let mut failures: Vec<String> = Vec::new();
    for case in TEST262 {
        if let Some(reason) = not_run(case) {
            xfail = xfail.saturating_add(1);
            bump(&mut categories, reason);
            continue;
        }
        let text = std::fs::read_to_string(root().join(case.path))
            .map_err(|e| format!("{}: {e}", case.path))?;
        let body: Vec<u32> = text.chars().map(u32::from).collect();
        let mut worst = Outcome::Pass;
        for (goal, strict) in runs(case) {
            let mut src: Vec<u32> = Vec::new();
            if strict {
                src.extend("\"use strict\";\n".chars().map(u32::from));
            }
            src.extend(body.iter().copied());
            let out = run_one(case, &src, goal);
            let mode = if strict { "strict" } else { "sloppy" };
            worst = match (worst, out) {
                (Outcome::Fail(m), _) => Outcome::Fail(m),
                (_, Outcome::Fail(m)) => Outcome::Fail(format!("{mode}: {m}")),
                (Outcome::Xfail(m), _) => Outcome::Xfail(m),
                (_, Outcome::Xfail(m)) => Outcome::Xfail(m),
                (Outcome::Pass, Outcome::Pass) => Outcome::Pass,
            };
        }
        match worst {
            Outcome::Pass => pass = pass.saturating_add(1),
            Outcome::Xfail(reason) => {
                xfail = xfail.saturating_add(1);
                bump(&mut categories, reason);
            }
            Outcome::Fail(m) => {
                fail = fail.saturating_add(1);
                failures.push(format!("{} {:?}: {m}", case.path, case.features));
            }
        }
    }
    let total = TEST262.len();
    println!(
        "clazel-conformance: suite=\"Test262 through the interpreter with the first built-ins\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
    // Group the categories by their stem, so the print stays readable.
    let mut stems: BTreeMap<String, usize> = BTreeMap::new();
    for (reason, n) in &categories {
        let stem = if reason.starts_with("global ") {
            "a global that is a built-in is missing (7.9)".to_string()
        } else {
            reason.clone()
        };
        let e = stems.entry(stem).or_insert(0);
        *e = e.saturating_add(*n);
    }
    let mut by_count: Vec<_> = stems.iter().collect();
    by_count.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (reason, n) in by_count {
        println!("  expected failure: {n:6}  {reason}");
    }
    let mut globals: Vec<_> = categories
        .iter()
        .filter(|(r, _)| r.starts_with("global "))
        .collect();
    globals.sort_by(|a, b| b.1.cmp(a.1));
    for (reason, n) in globals.into_iter().take(15) {
        println!("    {n:6}  {reason}");
    }
    for f in failures.iter().take(60) {
        println!("  FAIL {f}");
    }
    assert_eq!(pass.saturating_add(xfail).saturating_add(fail), total);
    assert!(pass > 0);
    assert_eq!(fail, 0, "{fail} tests failed unexpectedly");
    Ok(())
}
