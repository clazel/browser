//! Tests of the interpreter's generators (`clazel_js_vm::suspend`) without the
//! built-ins: a script makes generator objects, and the test resumes them
//! with [`Vm::generator_resume`], which is what `%GeneratorPrototype%.next`,
//! `return` and `throw` call. Each expectation is what ECMA-262's
//! GeneratorResume (§27.5.3.3†) and GeneratorResumeAbrupt (§27.5.3.4†) say.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_heap::value::Value;
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Abrupt, Config, Vm};
use clazel_js_vm::suspend::ResumeMode;

fn config() -> Config {
    if cfg!(miri) {
        Config {
            region_slots: 1 << 12,
            heap_cells: 1 << 14,
        }
    } else {
        Config::default()
    }
}

/// A VM that has run `src`.
fn run(src: &str) -> Result<Vm, String> {
    let c: Vec<u32> = src.chars().map(u32::from).collect();
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.set_budget(1_000_000);
    vm.run(&script).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(vm)
}

fn global(vm: &mut Vm, name: &str) -> Result<Value, String> {
    let g = vm.global();
    vm.get_named(g, name).map_err(|e| format!("{e:?}"))
}

/// An iterator result's `value` (described) and `done`.
fn result(vm: &mut Vm, r: Result<Value, Abrupt>) -> Result<(String, bool), String> {
    let r = r.map_err(|e| match e {
        Abrupt::Throw(v) => format!("threw {}", vm.describe(v)),
        other => format!("{other:?}"),
    })?;
    let v = vm.get_named(r, "value").map_err(|e| format!("{e:?}"))?;
    let d = vm.get_named(r, "done").map_err(|e| format!("{e:?}"))?;
    Ok((vm.describe(v), d == Value::TRUE))
}

fn next(vm: &mut Vm, g: Value, v: Value) -> Result<(String, bool), String> {
    let r = vm.generator_resume(g, v, ResumeMode::Next);
    result(vm, r)
}

#[test]
fn yields_values_and_receives_them() -> Result<(), String> {
    let mut vm = run(
        "function* g(a) { var x = yield a; var y = yield x * 2; return x + y; } var it = g(5);",
    )?;
    let it = global(&mut vm, "it")?;
    assert_eq!(next(&mut vm, it, Value::int32(99))?, ("5".into(), false));
    assert_eq!(next(&mut vm, it, Value::int32(3))?, ("6".into(), false));
    assert_eq!(next(&mut vm, it, Value::int32(4))?, ("7".into(), true));
    // GeneratorResume step 2: a completed generator gives { undefined, true }.
    assert_eq!(
        next(&mut vm, it, Value::UNDEFINED)?,
        ("undefined".into(), true)
    );
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "one VM per test; the first covers Miri")]
fn return_runs_finally_and_completes() -> Result<(), String> {
    let mut vm = run(
        "var log = ''; function* g() { try { yield 1; yield 2; } finally { log = 'f'; } } var it = g();",
    )?;
    let it = global(&mut vm, "it")?;
    assert_eq!(next(&mut vm, it, Value::UNDEFINED)?, ("1".into(), false));
    let r = vm.generator_resume(it, Value::int32(7), ResumeMode::Return);
    assert_eq!(result(&mut vm, r)?, ("7".into(), true));
    let log = global(&mut vm, "log")?;
    assert_eq!(vm.string_text(log).as_deref(), Some("f"));
    assert_eq!(
        next(&mut vm, it, Value::UNDEFINED)?,
        ("undefined".into(), true)
    );
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "one VM per test; the first covers Miri")]
fn throw_is_caught_at_the_yield_or_completes() -> Result<(), String> {
    let mut vm = run(
        "function* g() { try { yield 1; } catch (e) { yield e + 1; } } var it = g(); var it2 = g();",
    )?;
    let it = global(&mut vm, "it")?;
    assert_eq!(next(&mut vm, it, Value::UNDEFINED)?, ("1".into(), false));
    let r = vm.generator_resume(it, Value::int32(41), ResumeMode::Throw);
    assert_eq!(result(&mut vm, r)?, ("42".into(), false));
    // GeneratorResumeAbrupt steps 2 and 3: a throw before the start
    // completes the generator and throws.
    let it2 = global(&mut vm, "it2")?;
    let r = vm.generator_resume(it2, Value::int32(1), ResumeMode::Throw);
    assert_eq!(r, Err(Abrupt::Throw(Value::int32(1))));
    assert_eq!(
        next(&mut vm, it2, Value::UNDEFINED)?,
        ("undefined".into(), true)
    );
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "one VM per test; the first covers Miri")]
fn errors_complete_the_generator() -> Result<(), String> {
    let mut vm = run("function* g() { yield 1; throw 'boom'; } var it = g(); var o = {};")?;
    let it = global(&mut vm, "it")?;
    assert_eq!(next(&mut vm, it, Value::UNDEFINED)?, ("1".into(), false));
    let r = vm.generator_resume(it, Value::UNDEFINED, ResumeMode::Next);
    assert!(matches!(r, Err(Abrupt::Throw(_))));
    assert_eq!(
        next(&mut vm, it, Value::UNDEFINED)?,
        ("undefined".into(), true)
    );
    // GeneratorValidate step 1: not a generator object.
    let o = global(&mut vm, "o")?;
    let r = vm.generator_resume(o, Value::UNDEFINED, ResumeMode::Next);
    assert!(matches!(r, Err(Abrupt::Throw(_))));
    Ok(())
}

/// Without the built-ins there is no `Promise`, so an async function's call
/// reports that it is not implemented, never a panic or a wrong result.
#[test]
#[cfg_attr(miri, ignore = "one VM per test; the first covers Miri")]
fn async_without_promises_is_not_yet() -> Result<(), String> {
    let c: Vec<u32> = "async function f() { await 1; } f();"
        .chars()
        .map(u32::from)
        .collect();
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "does not parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    assert!(matches!(vm.run(&script), Err(Abrupt::NotYet(_))));
    Ok(())
}
