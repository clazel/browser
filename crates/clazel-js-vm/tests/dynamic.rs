//! Tests of the host compile paths without the built-ins: `with`, direct and
//! indirect eval (PerformEval §19.2.1.1, EvalDeclarationInstantiation
//! §19.2.1.3) and CreateDynamicFunction (§20.2.1.1.1), through
//! `compile::compile_eval`, `compile::compile_dynamic_function` and the VM.
//! The `eval` function is a native installed here as `%eval%`, which calls
//! [`Vm::perform_eval`], as `clazel-js-builtins`' does. Each expectation is
//! what ECMA-262 says, written by hand.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_heap::value::Value;
use clazel_js_syntax::exec::{EvalContext, parse, parse_eval};
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::{Const, EvalScopeInfo, EvalScopeKind};
use clazel_js_vm::compile::{compile_eval, compile_script};
use clazel_js_vm::eval::DynamicKind;
use clazel_js_vm::interp::{Abrupt, Config, Intrinsic, Vm};

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

fn eval_native(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.perform_eval(args.first().copied().unwrap_or(Value::UNDEFINED))
}

fn function_native(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
    vm.create_dynamic_function(DynamicKind::Normal, args)
}

/// Runs `src` in a new VM with `eval` and `Function` installed, and returns
/// the global `r`.
fn global_r(src: &str) -> Result<(Vm, Value), String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let e = vm
        .new_native("eval", 1, eval_native)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("eval", e).map_err(|e| format!("{e:?}"))?;
    vm.set_intrinsic(Intrinsic::Eval, e);
    let f = vm
        .new_native_constructor("Function", 1, function_native)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("Function", f)
        .map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    if let Err(e) = vm.run(&script) {
        let d = match e {
            Abrupt::Throw(v) => vm.describe(v),
            other => format!("{other:?}"),
        };
        return Err(format!("{src}: {d}"));
    }
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    Ok((vm, r))
}

fn expect_int(src: &str, n: i32) -> Result<(), String> {
    let (_, r) = global_r(src)?;
    if r == Value::int32(n) {
        Ok(())
    } else {
        Err(format!("{src}: expected {n}, got {:?}", r.decode()))
    }
}

fn expect_str(src: &str, s: &str) -> Result<(), String> {
    let (vm, r) = global_r(src)?;
    match vm.string_text(r) {
        Some(t) if t == s => Ok(()),
        other => Err(format!("{src}: expected {s:?}, got {other:?}")),
    }
}

#[test]
fn with_reads_and_writes_the_object() -> Result<(), String> {
    expect_int(
        "var o = { x: 1 }; var r; with (o) { x = x + 41; r = o.x; }",
        42,
    )?;
    expect_str("var y = 'outer'; var r; with ({}) { r = y; }", "outer")
}

#[test]
fn direct_eval_sees_and_declares() -> Result<(), String> {
    expect_int(
        "function f(a) { eval('var b = a + 1'); return b; } var r = f(41);",
        42,
    )?;
    // The completion value; a strict eval keeps its `var`s.
    expect_int("var r = eval('1; if (false) {} 7;');", 7)?;
    expect_str(
        "function f() { 'use strict'; eval('var v = 1'); return typeof v; } var r = f();",
        "undefined",
    )
}

#[test]
fn indirect_eval_is_global() -> Result<(), String> {
    expect_str(
        "var x = 'g'; function f() { var x = 'l'; var e = eval; return e('x'); } var r = f();",
        "g",
    )
}

#[test]
fn dynamic_functions() -> Result<(), String> {
    expect_int("var r = Function('a', 'b', 'return a * b')(6, 7);", 42)?;
    expect_str(
        "var r; try { Function('/*', '*/){'); } catch (e) { r = 'threw'; }",
        "threw",
    )
}

/// The record of a direct eval's call, as the compiler leaves it in the
/// caller's constant pool.
fn eval_record(src: &str) -> Result<EvalScopeInfo, String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    p.functions
        .iter()
        .flat_map(|f| f.consts.iter())
        .find_map(|k| match k {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .ok_or_else(|| format!("{src}: no direct eval"))
}

fn eval_decls(caller: &str, code: &str) -> Result<clazel_js_vm::compile::EvalDecls, String> {
    let info = eval_record(caller)?;
    let c = cps(code);
    let ast = parse_eval(&c, &EvalContext::default()).map_err(|_| format!("{code}: no parse"))?;
    let p = compile_eval(&ast, &c, &info).map_err(|e| format!("{code}: {e}"))?;
    Ok(p.decls)
}

#[test]
fn eval_declarations() -> Result<(), String> {
    let units = |s: &str| s.encode_utf16().collect::<Vec<u16>>();
    // A sloppy function's eval: its `var`s and functions, less the ones the
    // function binds (the parameter `a`).
    let d = eval_decls(
        "function f(a) { eval(s); }",
        "var a, b; function g() {} function g() {}",
    )?;
    assert!(!d.strict);
    assert_eq!(d.vars, vec![units("b")]);
    assert_eq!(d.functions, vec![units("g")]);
    assert_eq!(d.conflict, None);
    // A `let` between the call and the function (step 3.d).
    let d = eval_decls("function f() { let x; { eval(s); } }", "var x;")?;
    assert_eq!(d.conflict, Some(units("x")));
    // ... but not a `catch` parameter (the web-compatibility step).
    let d = eval_decls("function f() { try {} catch (x) { eval(s); } }", "var x;")?;
    assert_eq!(d.conflict, None);
    // A call in a parameter expression: the parameters are between the call
    // and varEnv (§10.2.11 step 20).
    let info = eval_record("function f(a, p = eval(s)) {}")?;
    assert_eq!(
        info.scopes.first().map(|s| s.kind),
        Some(EvalScopeKind::Parameters)
    );
    let d = eval_decls("function f(a, p = eval(s)) {}", "var a;")?;
    assert_eq!(d.conflict, Some(units("a")));
    // Strict eval code declares nothing in varEnv.
    let d = eval_decls("function f() { eval(s); }", "'use strict'; var q;")?;
    assert!(d.strict);
    assert!(d.vars.is_empty());
    Ok(())
}

#[test]
fn eval_parse_context() {
    let c = cps("new.target");
    assert!(parse_eval(&c, &EvalContext::default()).is_err());
    let cx = EvalContext {
        in_function: true,
        ..EvalContext::default()
    };
    assert!(parse_eval(&c, &cx).is_ok());
    let c = cps("arguments");
    let cx = EvalContext {
        in_function: true,
        in_class_field_initializer: true,
        ..EvalContext::default()
    };
    assert!(parse_eval(&c, &cx).is_err());
    // A strict caller makes the code strict: `with` is an early error.
    let c = cps("with ({}) {}");
    let cx = EvalContext {
        strict: true,
        ..EvalContext::default()
    };
    assert!(parse_eval(&c, &cx).is_err());
}
