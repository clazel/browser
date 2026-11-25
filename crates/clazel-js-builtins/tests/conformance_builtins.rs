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
//! with `global` and `gc`; its other members report "not yet" when called;
//! `assert.compareArray`, which tests call without including a file, is a
//! few lines of JS after `assert.js`'s contract (`ASSERT_EXTRAS`). The real
//! `sta.js` runs before every test, and so do the harness files of
//! `RUN_INCLUDES` that a test includes (`propertyHelper.js`,
//! `compareArray.js`, `asyncHelpers.js`, `isConstructor.js`); a test that
//! includes any other harness file is an expected failure.
//!
//! An `async` test (its `flags` say so) runs with the real
//! `doneprintHandle.js`: after the script the job queue runs to empty, as a
//! host's microtask checkpoint does, and the test passes if `$DONE` printed
//! `Test262:AsyncTestComplete`; a printed `Test262:AsyncTestFailure` is
//! classed as the error it names, and a test that never calls `$DONE` fails.
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

/// The harness files this runner runs as they are, before a test that
/// includes them: `sta.js` (always), `doneprintHandle.js` (for an `async`
/// test) and the includes the tests of generators and async functions use.
/// Each is compiled once.
const RUN_INCLUDES: [&str; 6] = [
    "sta.js",
    "doneprintHandle.js",
    "asyncHelpers.js",
    "compareArray.js",
    "propertyHelper.js",
    "isConstructor.js",
];

/// The harness file `name` of [`RUN_INCLUDES`], compiled once.
fn harness_program(name: &str) -> Option<&'static Program> {
    static PROGRAMS: OnceLock<Vec<Option<Program>>> = OnceLock::new();
    let all = PROGRAMS.get_or_init(|| {
        RUN_INCLUDES
            .iter()
            .map(|n| {
                let text = std::fs::read_to_string(root().join("../harness").join(n)).ok()?;
                let src: Vec<u32> = text.chars().map(u32::from).collect();
                let ast = parse(&src, SourceGoal::Script).ok()?;
                compile_script(&ast, &src).ok()
            })
            .collect()
    });
    let i = RUN_INCLUDES.iter().position(|n| *n == name)?;
    all.get(i)?.as_ref()
}

/// Runs the harness file `name`.
fn run_harness_file(vm: &mut Vm, name: &'static str) -> Result<(), Abrupt> {
    let p = harness_program(name).ok_or(Abrupt::Internal("a harness file does not compile"))?;
    let script = vm.load(p)?;
    vm.run(&script)?;
    Ok(())
}

/// `print`, as `doneprintHandle.js` calls it: the text is appended to the
/// global `__clazel_printed`, which the runner reads after an `async` test.
fn print(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let line = match args.first() {
        Some(v) => vm.to_js_string(*v)?.to_string_lossy(),
        None => String::new(),
    };
    let g = vm.global();
    let old = vm.get_named(g, PRINTED)?;
    let old = vm.string_text(old).unwrap_or_default();
    let all = vm.new_string(&format!("{old}{line}\n"))?;
    vm.define_property(g, PRINTED, all)?;
    Ok(Value::UNDEFINED)
}

/// The members of the real `assert.js` that tests call besides the native
/// ones: `assert.compareArray` and the `assert._isSameValue` it uses, written
/// here after `assert.js`'s contract (SameValue of each element, a
/// Test262Error naming both lists otherwise).
const ASSERT_EXTRAS: &str = r#"
assert._isSameValue = function (a, b) {
  if (a === b) return a !== 0 || 1 / a === 1 / b;
  return a !== a && b !== b;
};
assert.compareArray = function (actual, expected, message) {
  message = message === undefined ? '' : String(message);
  var primitive = function (v) { return !v || (typeof v !== 'object' && typeof v !== 'function'); };
  if (primitive(actual)) throw new Test262Error('Actual argument shouldn\'t be primitive. ' + message);
  if (primitive(expected)) throw new Test262Error('Expected argument shouldn\'t be primitive. ' + message);
  if (actual.length === expected.length) {
    var same = true;
    for (var i = 0; i < actual.length; i++) {
      if (!assert._isSameValue(expected[i], actual[i])) { same = false; break; }
    }
    if (same) return;
  }
  var format = function (a) { return '[' + Array.prototype.map.call(a, String).join(', ') + ']'; };
  throw new Test262Error('Actual ' + format(actual) + ' and expected ' + format(expected) + ' should have the same contents. ' + message);
};
"#;

/// [`ASSERT_EXTRAS`], compiled once.
fn assert_extras() -> Option<&'static Program> {
    static EXTRAS: OnceLock<Option<Program>> = OnceLock::new();
    EXTRAS
        .get_or_init(|| {
            let src: Vec<u32> = ASSERT_EXTRAS.chars().map(u32::from).collect();
            let ast = parse(&src, SourceGoal::Script).ok()?;
            compile_script(&ast, &src).ok()
        })
        .as_ref()
}

/// The global that collects what `print` printed.
const PRINTED: &str = "__clazel_printed";

/// Installs `assert` (unless `raw`), `print` and `$262`, and runs the real
/// `sta.js` (unless `raw`), `doneprintHandle.js` for an `async` test and the
/// test's includes of [`RUN_INCLUDES`].
fn install_harness(vm: &mut Vm, case: &Case) -> Result<(), Abrupt> {
    let raw = case.flags.contains(&"raw");
    let print = vm.new_native("print", 1, print)?;
    vm.define_global("print", print)?;
    if !raw {
        run_harness_file(vm, "sta.js")?;
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
        let extras = assert_extras().ok_or(Abrupt::Internal("ASSERT_EXTRAS does not compile"))?;
        let script = vm.load(extras)?;
        vm.run(&script)?;
    }
    let host = vm.new_object()?;
    let g = vm.global();
    vm.define_property(host, "global", g)?;
    for name in ["gc", "createRealm", "evalScript", "detachArrayBuffer"] {
        let f = vm.new_native(name, 0, if name == "gc" { ignore } else { not_yet })?;
        vm.define_property(host, name, f)?;
    }
    vm.define_global("$262", host)?;
    if raw {
        return Ok(());
    }
    if case.flags.contains(&"async") {
        run_harness_file(vm, "doneprintHandle.js")?;
    }
    for name in RUN_INCLUDES {
        if case.includes.contains(&name) && name != "sta.js" && name != "doneprintHandle.js" {
            run_harness_file(vm, name)?;
        }
    }
    Ok(())
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
    if let Err(e) = install_harness(&mut vm, case) {
        return match e {
            Abrupt::Throw(v) => Outcome::Fail(format!("harness: {}", vm.describe(v))),
            Abrupt::NotYet(what) => Outcome::Xfail(format!(
                "the VM does not yet implement {what} (in a harness file)"
            )),
            other => Outcome::Fail(format!("harness: {other:?}")),
        };
    }
    let script = match vm.load(&program) {
        Ok(s) => s,
        Err(Abrupt::NotYet(what)) => {
            return Outcome::Xfail(format!("the VM does not yet load {what}"));
        }
        Err(e) => return Outcome::Fail(format!("load: {e:?}")),
    };
    vm.set_budget(BUDGET);
    let mut result = vm.run(&script);
    let negative = case.negative.filter(|(phase, _)| *phase == "runtime");
    if result.is_ok() && case.flags.contains(&"async") {
        // An `async` test reports through `$DONE` (doneprintHandle.js), from
        // a job: run the job queue to empty, as a host's microtask
        // checkpoint does, then read what it printed.
        if let Err(e) = vm.run_jobs() {
            result = Err(e);
        } else {
            let g = vm.global();
            let printed = vm
                .get_named(g, PRINTED)
                .ok()
                .and_then(|v| vm.string_text(v))
                .unwrap_or_default();
            if let Some(rest) = printed
                .lines()
                .find_map(|l| l.strip_prefix("Test262:AsyncTestFailure:"))
            {
                let (name, msg) = rest.split_once(": ").unwrap_or((rest, ""));
                return classify(Some(name), Some(msg), negative, rest.to_string());
            }
            if !printed.lines().any(|l| l == "Test262:AsyncTestComplete") {
                return Outcome::Fail("the async test did not call $DONE".into());
            }
        }
    }
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
            let d = vm.describe(e);
            classify(name.as_deref(), msg.as_deref(), negative, d)
        }
        Err(Abrupt::Terminated) => Outcome::Fail("step budget exhausted".into()),
        Err(e) => Outcome::Fail(format!("{e:?}")),
    }
}

/// Classifies a thrown error by its `name` and `message` (`described` is
/// how a failure reports it).
fn classify(
    name: Option<&str>,
    msg: Option<&str>,
    negative: Option<(&str, &str)>,
    described: String,
) -> Outcome {
    let name = name.map(str::to_string);
    let msg = msg.map(str::to_string);
    {
        {
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
            // the RegExp literal tests that reach `eval` this way); so do the
            // tests that catch the error and throw their own Test262Error
            // with it in the message ("... Actual: ReferenceError: eval is not
            // defined", reached since `instanceof` runs).
            if name.as_deref() == Some("Test262Error")
                && let Some(m) = &msg
                && let Some((_, got)) = m.rsplit_once("ReferenceError: ")
                && let Some(var) = got.strip_suffix(" is not defined")
            {
                return Outcome::Xfail(format!("global {var} is missing (a built-in, 7.9)"));
            }
            // A test that catches the ReferenceError itself and reports it
            // in its own message, "... is incorrect. Actual: ReferenceError:
            // eval is not defined" (reached since `instanceof` runs, item
            // 7.12).
            if name.as_deref() == Some("Test262Error")
                && let Some(m) = &msg
                && let Some((_, got)) = m.split_once("Actual: ReferenceError: ")
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
                Some((_, ty)) => Outcome::Fail(format!("expected {ty}, got {described}")),
                None => Outcome::Fail(described),
            }
        }
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

/// The directories of generators and async functions (items 7.7 to 7.9), and
/// of `eval`, `with` and the `Function` constructors, whose counts are printed
/// each on its own.
const SUSPEND_DIRS: [&str; 17] = [
    "language/statements/generators",
    "language/statements/async-function",
    "language/statements/async-generator",
    "language/expressions/generators",
    "language/expressions/async-function",
    "language/expressions/async-arrow-function",
    "language/expressions/async-generator",
    "language/expressions/await",
    "language/expressions/yield",
    "built-ins/AsyncFromSyncIteratorPrototype",
    "built-ins/eval",
    "language/eval-code",
    "language/statements/with",
    "built-ins/Function",
    "built-ins/GeneratorFunction",
    "built-ins/AsyncFunction",
    "built-ins/AsyncGeneratorFunction",
];

/// Tests that run and give a different result for a known reason, each with
/// its reason: expected failures.
const KNOWN_GAPS: &[(&str, &str)] = &[
    (
        "language/identifier-resolution/assign-to-global-undefined.js",
        "strict assignment to an unresolvable reference throws before the right-hand side runs (§13.15.2 step 1.a, ResolveBinding first); SetGlobal checks when it runs, after it, and the op list has no resolve-first op",
    ),
    (
        "language/expressions/yield/formal-parameters-after-reassignment-non-strict.js",
        "a sloppy function's arguments object has no parameter map (CreateMappedArgumentsObject §10.4.4.7† is not yet mapped, `clazel_js_vm::host`), so `arguments[0] = v` does not change the parameter",
    ),
    (
        "language/statements/async-function/evaluation-mapped-arguments.js",
        "a sloppy function's arguments object has no parameter map (CreateMappedArgumentsObject §10.4.4.7† is not yet mapped, `clazel_js_vm::host`), so `arguments[0] = v` does not change the parameter",
    ),
    (
        "language/statements/generators/restricted-properties.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
];

/// `Function` tests (vendored with the `Function` constructors) that run and
/// fail for a known difference of `%Function.prototype%`, each with its reason:
/// expected failures.
const FUNCTION_PROTOTYPE_GAPS: &[(&str, &str)] = &[
    (
        "built-ins/Function/15.3.5-1gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5-2gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-11gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-13gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-15gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-17gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-19gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-1gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-21gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-22gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-23gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-24gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-25gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-26gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-27gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-28gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-29gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-3gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-48gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-50gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-52gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-54gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-5gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-7gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/15.3.5.4_2-9gs.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/StrictFunction_restricted-properties.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/S15.3.3.1_A1.js",
        "%Function.prototype% is an ordinary object, not a built-in function that accepts any arguments and returns undefined (§20.2.3†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/S15.3.4_A1.js",
        "%Function.prototype% is an ordinary object, not a built-in function that accepts any arguments and returns undefined (§20.2.3†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/S15.3.4_A2_T1.js",
        "%Function.prototype% is an ordinary object, not a built-in function that accepts any arguments and returns undefined (§20.2.3†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/S15.3.4_A2_T2.js",
        "%Function.prototype% is an ordinary object, not a built-in function that accepts any arguments and returns undefined (§20.2.3†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/S15.3.4_A2_T3.js",
        "%Function.prototype% is an ordinary object, not a built-in function that accepts any arguments and returns undefined (§20.2.3†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/15.3.4.5-20-2.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/15.3.4.5-20-3.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/15.3.4.5-21-2.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/15.3.4.5-21-3.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/BoundFunction_restricted-properties.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/S15.3.4.5_A1.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/bind/S15.3.4.5_A2.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/caller-arguments/accessor-properties.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
    (
        "built-ins/Function/prototype/toString/S15.3.4.2_A12.js",
        "`Function.prototype.toString` (§20.2.3.5) is not installed yet, so `Object.prototype.toString` answers for it and throws no TypeError for a `this` that is not callable",
    ),
    (
        "built-ins/Function/prototype/toString/S15.3.4.2_A13.js",
        "`Function.prototype.toString` (§20.2.3.5) is not installed yet, so `Object.prototype.toString` answers for it and throws no TypeError for a `this` that is not callable",
    ),
    (
        "built-ins/Function/prototype/toString/S15.3.4.2_A14.js",
        "`Function.prototype.toString` (§20.2.3.5) is not installed yet, so `Object.prototype.toString` answers for it and throws no TypeError for a `this` that is not callable",
    ),
    (
        "built-ins/Function/prototype/toString/S15.3.4.2_A16.js",
        "`Function.prototype.toString` (§20.2.3.5) is not installed yet, so `Object.prototype.toString` answers for it and throws no TypeError for a `this` that is not callable",
    ),
    (
        "built-ins/GeneratorFunction/instance-restricted-properties.js",
        "%Function.prototype% is an ordinary object without the `caller` and `arguments` accessors of AddRestrictedFunctionProperties (§10.2.4†), a listed difference of the built-ins",
    ),
];

/// Classifies a test that is not run, or `None` if it should be.
fn not_run(case: &Case) -> Option<String> {
    if let Some((_, why)) = KNOWN_GAPS
        .iter()
        .chain(FUNCTION_PROTOTYPE_GAPS)
        .find(|(p, _)| *p == case.path)
    {
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
    if case.path.starts_with("harness/") {
        return Some("test of the real harness files (replaced by the native harness)".into());
    }
    case.includes
        .iter()
        .find(|i| !NATIVE_INCLUDES.contains(i) && !RUN_INCLUDES.contains(i))
        .map(|i| format!("includes {i} (needs built-ins of later groups of 7.9)"))
}

#[test]
#[cfg_attr(miri, ignore = "reads files; Miri runs the other tests")]
fn test262_through_the_interpreter() -> Result<(), String> {
    assert_eq!(TREE_SHA256.len(), 64);
    let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
    let mut categories: BTreeMap<String, usize> = BTreeMap::new();
    let mut failures: Vec<String> = Vec::new();
    // Pass, expected failure and failure per directory (two path components,
    // and `language/literals/regexp`, which RegExp (7.10) unlocked).
    let mut dirs: BTreeMap<String, [usize; 3]> = BTreeMap::new();
    let mut tally = |path: &str, which: usize| {
        let parts: Vec<&str> = path.split('/').collect();
        let mut keys = vec![parts.iter().take(2).copied().collect::<Vec<_>>().join("/")];
        if path.starts_with("language/literals/regexp/") {
            keys.push("language/literals/regexp".to_string());
        }
        if let Some(d) = SUSPEND_DIRS
            .iter()
            .find(|d| path.starts_with(&format!("{d}/")))
            && !keys.iter().any(|k| k == d)
        {
            keys.push((*d).to_string());
        }
        for k in keys {
            let e = dirs.entry(k).or_insert([0; 3]);
            if let Some(n) = e.get_mut(which) {
                *n = n.saturating_add(1);
            }
        }
    };
    for case in TEST262 {
        if let Some(reason) = not_run(case) {
            xfail = xfail.saturating_add(1);
            tally(case.path, 1);
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
            Outcome::Pass => {
                pass = pass.saturating_add(1);
                tally(case.path, 0);
            }
            Outcome::Xfail(reason) => {
                xfail = xfail.saturating_add(1);
                tally(case.path, 1);
                bump(&mut categories, reason);
            }
            Outcome::Fail(m) => {
                fail = fail.saturating_add(1);
                tally(case.path, 2);
                failures.push(format!("{} {:?}: {m}", case.path, case.features));
            }
        }
    }
    let total = TEST262.len();
    println!(
        "clazel-conformance: suite=\"Test262 through the interpreter with the first built-ins\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
    for (dir, [p, x, f]) in &dirs {
        println!("  directory {dir}: pass={p} xfail={x} fail={f}");
    }
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
