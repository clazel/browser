//! Tests of `eval` (direct and indirect, §19.2.1), `with` (§14.11), `delete`
//! of a variable, and the `Function` constructors (CreateDynamicFunction,
//! §20.2.1.1.1), as small scripts run with the built-ins installed. Each
//! expectation is what ECMA-262 says, written by hand: the script runs, then
//! the job queue is run to empty, and the result is the global `r` as its
//! ToString. No files are read; under Miri, where one VM with the built-ins
//! costs about 40 s, each group runs its first case and the rest are left to
//! the native run.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Abrupt, Config, Vm};

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

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

fn r_of(src: &str) -> Result<String, String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("install: {e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.set_budget(5_000_000);
    let run = |vm: &mut Vm, e: Abrupt| {
        let d = match e {
            Abrupt::Throw(v) => vm.describe(v),
            other => format!("{other:?}"),
        };
        format!("{src}: {d}")
    };
    if let Err(e) = vm.run(&script) {
        return Err(run(&mut vm, e));
    }
    if let Err(e) = vm.run_jobs() {
        return Err(run(&mut vm, e));
    }
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    let s = vm.to_js_string(r).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(s.to_string_lossy())
}

fn check(cases: &[(&str, &str)]) -> Result<(), String> {
    let n = if cfg!(miri) { 1 } else { cases.len() };
    let mut failures = Vec::new();
    for (src, want) in cases.iter().take(n) {
        match r_of(src) {
            Ok(got) if got == *want => {}
            Ok(got) => failures.push(format!("{src}: expected {want:?}, got {got:?}")),
            Err(e) => failures.push(e),
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("\n"))
    }
}

#[test]
fn indirect_eval() -> Result<(), String> {
    check(&[
        // §19.2.1.1 step 2: a value that is not a String is the result.
        (
            "var e = eval; var r = [e(1 + 1), e('1 + 1'), typeof e({})].join();",
            "2,2,object",
        ),
        // The completion value: the last expression statement's.
        (
            "var r = (0, eval)('var x = 1; x + 1; if (true) {}');",
            "undefined",
        ),
        ("var r = (0, eval)('1; { 2; } var y;');", "2"),
        ("var r = (0, eval)('1; try { 2 } finally { 3 }');", "2"),
        (
            "var r = (0, eval)('1; do { 4; break; } while (false)');",
            "4",
        ),
        // An indirect eval's declarations are the global object's, and
        // configurable (CreateGlobalVarBinding(vn, true)).
        (
            "(0, eval)('var g1 = 5; function g2() { return 6; }'); var d = Object.getOwnPropertyDescriptor(globalThis, 'g1'); var r = [g1, g2(), d.configurable, delete globalThis.g1, typeof g1].join();",
            "5,6,true,true,undefined",
        ),
        // An indirect eval inside a function sees the global scope only.
        (
            "var x = 'global'; function f() { var x = 'local'; return (0, eval)('x'); } var r = f();",
            "global",
        ),
        // `let` of eval code is its own.
        ("(0, eval)('let z = 1;'); var r = typeof z;", "undefined"),
        // A syntax error is a SyntaxError.
        (
            "var r; try { eval('a b'); } catch (e) { r = e instanceof SyntaxError; }",
            "true",
        ),
        // Strict eval code keeps its vars.
        (
            "(0, eval)('\"use strict\"; var s1 = 1;'); var r = typeof s1;",
            "undefined",
        ),
        // A global lexical declaration of a var name is a SyntaxError.
        (
            "let q = 1; var r; try { (0, eval)('var q;'); } catch (e) { r = e.constructor.name; }",
            "SyntaxError",
        ),
    ])
}

#[test]
fn direct_eval() -> Result<(), String> {
    check(&[
        // The caller's bindings, read and written.
        (
            "function f(a) { var b = 2; eval('a = a + b'); return a; } var r = f(1);",
            "3",
        ),
        // Sloppy eval code's `var` is the function's.
        (
            "function f() { eval('var v = 7'); return v; } var r = f();",
            "7",
        ),
        (
            "function f() { eval('var v = 7'); return delete v; } var r = f();",
            "true",
        ),
        (
            "function f() { eval('function h() { return 8; }'); return h(); } var r = f();",
            "8",
        ),
        // A strict caller's eval keeps its vars.
        (
            "function f() { 'use strict'; eval('var v = 7'); return typeof v; } var r = f();",
            "undefined",
        ),
        // `this`, `arguments` and `new.target` are the caller's.
        (
            "var o = { m() { return eval('this') === o; } }; var r = o.m();",
            "true",
        ),
        (
            "function f() { return eval('arguments.length'); } var r = f(1, 2, 3);",
            "3",
        ),
        (
            "function F() { this.t = eval('new.target') === F; } var r = new F().t;",
            "true",
        ),
        // `super` in a method.
        (
            "var p = { x: 'px' }; var o = { __proto__: p, m() { return eval('super.x'); } }; var r = o.m();",
            "px",
        ),
        // A var name that a `let` between the call and the function binds.
        (
            "function f() { let x; { var r; try { eval('var x;'); } catch (e) { r = e.constructor.name; } return r; } } var r = f();",
            "SyntaxError",
        ),
        // At the top level, a direct eval's var is a global.
        ("eval('var top1 = 3;'); var r = globalThis.top1;", "3"),
        // Closures made by eval code see its scope.
        (
            "function f() { eval('var k = 1; var g = function () { return k; };'); k = 2; return g(); } var r = f();",
            "2",
        ),
        // `eval` called another way is an ordinary call.
        ("var r = eval.call(null, '1 + 2');", "3"),
        // Nested direct eval.
        (
            "function f(a) { return eval('eval(\"a * 2\")'); } var r = f(21);",
            "42",
        ),
        // `new.target` outside a function is a SyntaxError.
        (
            "var r; try { eval('new.target'); } catch (e) { r = e.constructor.name; }",
            "SyntaxError",
        ),
        // A spread argument.
        ("var a = ['1 + 1']; var r = eval(...a);", "2"),
        // Arrow functions in eval code read the caller's `this`.
        (
            "var o = { m() { return eval('(() => this)()') === o; } }; var r = o.m();",
            "true",
        ),
    ])
}

#[test]
fn with_statement() -> Result<(), String> {
    check(&[
        ("var o = { x: 1 }; var r; with (o) { r = x; }", "1"),
        ("var o = { x: 1 }; with (o) { x = 2; } var r = o.x;", "2"),
        // A name the object does not have is the outer binding.
        (
            "var y = 'outer'; var o = {}; var r; with (o) { r = y; }",
            "outer",
        ),
        // @@unscopables hides a property.
        (
            "var x = 'outer'; var o = { x: 'inner' }; o[Symbol.unscopables] = { x: true }; var r; with (o) { r = x; }",
            "outer",
        ),
        // A call through a `with` object has it as `this`.
        (
            "var o = { f() { return this === o; } }; var r; with (o) { r = f(); }",
            "true",
        ),
        // `var` inside `with` assigns the object's property.
        (
            "var o = { v: 1 }; with (o) { var v = 2; } var r = [o.v, typeof v].join();",
            "2,undefined",
        ),
        // A primitive becomes its wrapper object.
        ("var r; with ('abc') { r = length; }", "3"),
        // `delete` of a name through the object.
        (
            "var o = { d: 1 }; with (o) { delete d; } var r = 'd' in o;",
            "false",
        ),
        // eval inside `with`.
        ("var o = { w: 5 }; var r; with (o) { r = eval('w'); }", "5"),
    ])
}

#[test]
fn delete_variable() -> Result<(), String> {
    check(&[
        (
            "globalThis.g = 1; var r = [delete g, typeof g].join();",
            "true,undefined",
        ),
        ("var v = 1; var r = delete v;", "false"),
        ("var r = delete notDefinedAnywhere;", "true"),
    ])
}

#[test]
fn function_constructors() -> Result<(), String> {
    check(&[
        (
            "var f = Function('a', 'b', 'return a + b'); var r = f(1, 2);",
            "3",
        ),
        (
            "var f = new Function('a, b', 'return a * b'); var r = [f(3, 4), f.name, f.length].join();",
            "12,anonymous,2",
        ),
        ("var r = Function()();", "undefined"),
        // The function's name binds nothing.
        (
            "var r = Function('return typeof anonymous')();",
            "undefined",
        ),
        // It runs in the global scope.
        (
            "var gx = 'g'; function f() { var gx = 'l'; return Function('return gx')(); } var r = f();",
            "g",
        ),
        // Text that is not the function is a SyntaxError.
        (
            "var r; try { Function('/*', '*/){'); } catch (e) { r = e.constructor.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { Function('a){ return 1; }; (function(b', ''); } catch (e) { r = e.constructor.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { Function('}'); } catch (e) { r = e.constructor.name; }",
            "SyntaxError",
        ),
        // A comment at the end of the parameters ends at the line feed.
        ("var r = Function('a //', 'return a')(9);", "9"),
        // Generator, async and async generator functions.
        (
            "var GF = Object.getPrototypeOf(function* () {}).constructor; var g = GF('a', 'yield a; yield a + 1'); var it = g(5); var r = [it.next().value, it.next().value, Object.getPrototypeOf(g) === GF.prototype].join();",
            "5,6,true",
        ),
        (
            "var AF = Object.getPrototypeOf(async function () {}).constructor; var r; AF('return await 7')().then(v => { r = v; });",
            "7",
        ),
        (
            "var AGF = Object.getPrototypeOf(async function* () {}).constructor; var r; AGF('yield 8')().next().then(v => { r = v.value; });",
            "8",
        ),
        // `prototype`: a normal function is a constructor, an async one not.
        (
            "var AF = Object.getPrototypeOf(async function () {}).constructor; var r = [typeof Function('').prototype, 'prototype' in AF('')].join();",
            "object,false",
        ),
        // Subclassing: the prototype comes from NewTarget.
        (
            "class MyF extends Function {} var f = new MyF('return 1'); var r = [f(), f instanceof MyF].join();",
            "1,true",
        ),
    ])
}
