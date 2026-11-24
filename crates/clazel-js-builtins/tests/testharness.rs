//! The vendored `testharness.js` (WPT's `resources/testharness.js`, vendored
//! for `clazel-web`) loads in the engine and runs trivial tests: the check
//! that the engine has what real WPT pages need of it (`try`/`catch`/`finally`,
//! `RegExp`, `Promise`, the job queue). It runs in the harness's shell
//! environment (no `document`), with a `print` that collects what the harness
//! reports.

use clazel_js_heap::value::Value;
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Abrupt, Config, Vm};
use std::path::PathBuf;

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

fn harness_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../clazel-web/tests/data/wpt-web/resources/testharness.js")
}

fn print(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    let line = match args.first() {
        Some(v) => vm.to_js_string(*v)?.to_string_lossy(),
        None => String::new(),
    };
    let g = vm.global();
    let old = vm.get_named(g, "printed")?;
    let old = vm.string_text(old).unwrap_or_default();
    let all = vm.new_string(&format!("{old}{line}\n"))?;
    vm.define_property(g, "printed", all)?;
    Ok(Value::UNDEFINED)
}

/// Runs `body` after the harness; returns what was printed.
fn run_with_harness(body: &str) -> Result<String, String> {
    let text = std::fs::read_to_string(harness_path()).map_err(|e| format!("harness: {e}"))?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("install: {e:?}"))?;
    let g = vm.global();
    vm.define_global("self", g).map_err(|e| format!("{e:?}"))?;
    let empty = vm.new_string("").map_err(|e| format!("{e:?}"))?;
    vm.define_global("printed", empty)
        .map_err(|e| format!("{e:?}"))?;
    let p = vm
        .new_native("print", 1, print)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("print", p).map_err(|e| format!("{e:?}"))?;
    vm.set_budget(500_000_000);
    for (name, src) in [("testharness.js", text.as_str()), ("test", body)] {
        let c = cps(src);
        let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("{name} does not parse"))?;
        let program = compile_script(&ast, &c).map_err(|e| format!("{name}: {e}"))?;
        let script = vm.load(&program).map_err(|e| format!("{name}: {e:?}"))?;
        if let Err(e) = vm.run(&script) {
            let d = match e {
                Abrupt::Throw(v) => vm.describe(v),
                other => format!("{other:?}"),
            };
            return Err(format!("{name}: {d}"));
        }
    }
    vm.run_jobs().map_err(|e| format!("jobs: {e:?}"))?;
    let printed = vm.get_named(g, "printed").map_err(|e| format!("{e:?}"))?;
    Ok(vm.string_text(printed).unwrap_or_default())
}

#[test]
#[cfg_attr(miri, ignore = "reads files; Miri runs the other tests")]
fn testharness_loads_and_runs_a_trivial_test() -> Result<(), String> {
    let out = run_with_harness(
        "var result_lines = [];\n\
         add_result_callback(function (t) { result_lines.push(t.name + '=' + t.status + ':' + t.message); });\n\
         add_completion_callback(function (tests, status) { print(result_lines.join(',') + ';' + status.status); });\n\
         test(function () { assert_equals(1 + 1, 2); assert_true(/a+/.test('caat')); }, 'passes');\n\
         test(function () { assert_equals(1, 2); }, 'fails');\n\
         test(function () { throw 'boom'; }, 'throws');\n\
         promise_test(function () { return Promise.resolve(3).then(function (v) { assert_equals(v, 3); }); }, 'promise');\n\
         done();\n",
    )?;
    // Statuses: 0 pass, 1 fail; the completion status 0 is "OK".
    assert_eq!(
        out,
        "passes=0:null,fails=1:assert_equals: expected 2 but got 1,throws=1:boom,promise=0:null;0\n"
    );
    Ok(())
}
