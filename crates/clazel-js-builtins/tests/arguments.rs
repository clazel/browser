//! Tests of the arguments object, rest parameters and exceptions
//! (`try`/`catch`/`finally`, `throw`): the VM compiles and runs them, and the
//! built-ins make the errors. Each expectation is what ECMA-262 says, written
//! by hand; the result is the global `r` as its ToString. No files are read,
//! so these run under Miri too (every eighth case).

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
    if let Err(e) = vm.run(&script) {
        let d = match e {
            Abrupt::Throw(v) => vm.describe(v),
            other => format!("{other:?}"),
        };
        return Err(format!("{src}: {d}"));
    }
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    let s = vm.to_js_string(r).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(s.to_string_lossy())
}

fn check(cases: &[(&str, &str)]) -> Result<(), String> {
    let stride = if cfg!(miri) { 8 } else { 1 };
    for (src, want) in cases.iter().step_by(stride) {
        let got = r_of(src)?;
        if got != *want {
            return Err(format!("{src}: expected {want:?}, got {got:?}"));
        }
    }
    Ok(())
}

#[test]
fn arguments_object() -> Result<(), String> {
    check(&[
        (
            "function f() { return arguments.length; } var r = f(1, 2, 3);",
            "3",
        ),
        (
            "function f(a) { return arguments[2]; } var r = f(1, 2, 3);",
            "3",
        ),
        (
            "function f(a, b) { return arguments.length; } var r = f(1);",
            "1",
        ),
        (
            "function f() { return Array.prototype.slice.call(arguments, 1).join(); } var r = f(1, 2, 3);",
            "2,3",
        ),
        (
            "function f() { return Object.prototype.toString.call(arguments); } var r = f();",
            "[object Arguments]",
        ),
        (
            "function f() { var n = 0; for (var x of arguments) n += x; return n; } var r = f(1, 2, 3);",
            "6",
        ),
        (
            "function f() { 'use strict'; return arguments.length; } var r = f(1, 2);",
            "2",
        ),
        (
            "function f() { return arguments.callee === f; } var r = f();",
            "true",
        ),
        // Each call has its own arguments, nested calls included.
        (
            "function g() { return arguments.length; } function f() { var a = arguments.length; return a + ':' + g(1, 2, 3, 4) + ':' + arguments.length; } var r = f(1);",
            "1:4:1",
        ),
        (
            "function f(a, b) { return arguments.length; } var r = f.apply(null, [1, 2, 3, 4]);",
            "4",
        ),
    ])
}

#[test]
fn rest_parameters() -> Result<(), String> {
    check(&[
        (
            "function f(a, ...r) { return r.length + ':' + r.join(); } var r = f(1, 2, 3);",
            "2:2,3",
        ),
        ("function f(...r) { return r.length; } var r = f();", "0"),
        (
            "function f(a, ...r) { return Array.isArray(r); } var r = f(1);",
            "true",
        ),
        ("var f = (...r) => r.length; var r = f(1, 2, 3, 4);", "4"),
        (
            "function f(...[a, b]) { return a + b; } var r = f(1, 2, 3);",
            "3",
        ),
        (
            "var r = ((a, b, ...c) => c.join())(1, 2, 3, 4, 5);",
            "3,4,5",
        ),
    ])
}

#[test]
fn try_catch_finally_and_throw() -> Result<(), String> {
    check(&[
        ("var r; try { throw 1; } catch (e) { r = e + 1; }", "2"),
        ("var r = ''; try { r += 'a'; } finally { r += 'f'; }", "af"),
        (
            "var r = ''; try { throw 'x'; } catch (e) { r += e; } finally { r += 'f'; }",
            "xf",
        ),
        (
            "function f() { try { return 'try'; } finally { r = 'fin'; } } var r; f();",
            "fin",
        ),
        (
            "function f() { try { throw 1; } catch (e) { return 'c'; } finally { return 'f'; } } var r = f();",
            "f",
        ),
        (
            "function f() { for (var i = 0; i < 3; i++) { try { if (i == 1) continue; } finally { r += i; } } } var r = ''; f();",
            "012",
        ),
        (
            "var r; try { null.x; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { undefinedVariable; } catch (e) { r = e.name; }",
            "ReferenceError",
        ),
        (
            "var r; try { try { throw 1; } finally { r = 'inner'; } } catch (e) { r += e; }",
            "inner1",
        ),
        (
            "var r; try { throw new Error('m'); } catch ({ message }) { r = message; }",
            "m",
        ),
        (
            "var r; try { new RegExp('('); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { throw 1; } catch { r = 'no binding'; }",
            "no binding",
        ),
    ])
}
