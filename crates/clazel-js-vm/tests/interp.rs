//! Unit tests of the interpreter: small scripts compiled by `compile_script`
//! and run, their results read from global variables. Each expectation is
//! what ECMA-262 says of the script, written by hand.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_heap::value::{Decoded, Value};
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Abrupt, Config, Vm};

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

/// Compiles and runs `src` in a new VM; the VM and the result.
fn run(src: &str) -> Result<(Vm, Result<Value, Abrupt>), String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    let r = vm.run(&script);
    Ok((vm, r))
}

/// Runs `src` and returns the global `r`.
fn global_r(src: &str) -> Result<(Vm, Value), String> {
    let (mut vm, res) = run(src)?;
    res.map_err(|e| format!("{src}: {e:?}"))?;
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    Ok((vm, r))
}

/// Expects `r` to be the int32 `n`.
fn expect_int(src: &str, n: i32) -> Result<(), String> {
    let (_, r) = global_r(src)?;
    if r == Value::int32(n) {
        Ok(())
    } else {
        Err(format!("{src}: expected {n}, got {:?}", r.decode()))
    }
}

/// Expects `r` to be the double `d` (NaN equal to NaN, -0 distinct from +0).
fn expect_double(src: &str, d: f64) -> Result<(), String> {
    let (_, r) = global_r(src)?;
    if r == Value::double(d) {
        Ok(())
    } else {
        Err(format!("{src}: expected {d:?}, got {:?}", r.decode()))
    }
}

/// Expects `r` to be the string `s`.
fn expect_str(src: &str, s: &str) -> Result<(), String> {
    let (vm, r) = global_r(src)?;
    match vm.string_text(r) {
        Some(t) if t == s => Ok(()),
        other => Err(format!(
            "{src}: expected {s:?}, got {other:?} ({:?})",
            r.decode()
        )),
    }
}

fn expect_bool(src: &str, b: bool) -> Result<(), String> {
    let (_, r) = global_r(src)?;
    if r == Value::boolean(b) {
        Ok(())
    } else {
        Err(format!("{src}: expected {b}, got {:?}", r.decode()))
    }
}

#[test]
fn arithmetic() -> Result<(), String> {
    expect_int("var r = 1 + 2;", 3)?;
    expect_int("var r = 7 * 6 - 2;", 40)?;
    expect_int("var r = 17 % 5;", 2)?;
    expect_double("var r = 1 / 4;", 0.25)?;
    expect_double("var r = 2147483647 + 1;", 2_147_483_648.0)?;
    expect_double("var r = -2147483648 - 1;", -2_147_483_649.0)?;
    expect_double("var r = 0 * -1;", -0.0)?;
    expect_double("var r = -0 + 0;", 0.0)?;
    // Miri deliberately perturbs libm results such as powf, so the exact
    // value is checked only natively.
    if !cfg!(miri) {
        expect_double("var r = 2 ** 10;", 1024.0)?;
    }
    expect_int("var r = 5 & 3;", 1)?;
    expect_int("var r = 5 | 3;", 7)?;
    expect_int("var r = 5 ^ 3;", 6)?;
    expect_int("var r = 1 << 31 >> 31;", -1)?;
    expect_double("var r = -1 >>> 0;", 4_294_967_295.0)?;
    expect_int("var r = ~5;", -6)?;
    expect_int("var r = -(-5);", 5)?;
    expect_double("var r = 0.1 + 0.2;", 0.1 + 0.2)?;
    expect_double("var r = 0 / 0;", f64::NAN)
}

#[test]
fn comparisons_and_equality() -> Result<(), String> {
    expect_bool("var r = 1 < 2;", true)?;
    expect_bool("var r = 2 <= 1;", false)?;
    expect_bool("var n = 0 / 0; var r = n === n;", false)?;
    expect_bool("var r = NaN === NaN;", false)?;
    expect_bool("var r = 1 === 1.0;", true)?;
    expect_bool("var r = 1 !== 2;", true)?;
    expect_bool("var r = 'a' === 'a';", true)?;
    expect_bool("var r = 'a' < 'b';", true)?;
    expect_bool("var r = '10' < '9';", true)?;
    expect_bool("var r = 10 < '9';", false)?;
    expect_bool("var r = null == undefined;", true)?;
    expect_bool("var r = null == 0;", false)?;
    expect_bool("var r = '1' == 1;", true)?;
    expect_bool("var r = true == 1;", true)?;
    expect_bool("var r = 'a' != 'b';", true)?;
    expect_bool("var r = !0;", true)?;
    expect_bool("var r = !'';", true)?;
    expect_bool("var r = !'x';", false)
}

#[test]
fn control_flow() -> Result<(), String> {
    expect_int("var r = 0; for (var i = 0; i < 10; i++) { r += i; }", 45)?;
    expect_int("var r = 1; while (r < 100) r = r * 2;", 128)?;
    expect_int("var r; if (1 < 2) r = 1; else r = 2;", 1)?;
    expect_int("var r = 0 || 5;", 5)?;
    expect_int("var r = 3 && 4;", 4)?;
    expect_int("var r = null ?? 7;", 7)?;
    expect_int("var r = 1 ? 10 : 20;", 10)?;
    expect_int("var r = 0; do { r++; if (r == 3) break; } while (true);", 3)
}

#[test]
fn strings_and_conversions() -> Result<(), String> {
    expect_str("var r = 'a' + 'b';", "ab")?;
    expect_str("var r = 'x' + 1;", "x1")?;
    expect_str("var r = 1 + 'x';", "1x")?;
    expect_str("var r = 1.5 + '';", "1.5")?;
    expect_str("var r = 1e21 + '';", "1e+21")?;
    expect_str("var r = 0.000001 + '';", "0.000001")?;
    expect_str("var r = 1e-7 + '';", "1e-7")?;
    expect_str("var r = -0 + '';", "0")?;
    expect_str("var r = (0 / 0) + '';", "NaN")?;
    expect_str("var r = null + 'x';", "nullx")?;
    expect_str("var r = undefined + 'x';", "undefinedx")?;
    expect_str("var r = true + 'x';", "truex")?;
    expect_int("var r = '5' * '4';", 20)?;
    expect_int("var r = '5' - 2;", 3)?;
    expect_int("var r = +'0x10';", 16)?;
    expect_double("var r = +'abc';", f64::NAN)?;
    expect_int("var r = +true;", 1)?;
    expect_int("var r = 'abc'.length;", 3)?;
    expect_str("var r = 'abc'[1];", "b")?;
    expect_str("var r = `a${1 + 1}b`;", "a2b")
}

#[test]
fn typeof_operator() -> Result<(), String> {
    expect_str("var r = typeof 1;", "number")?;
    expect_str("var r = typeof 'x';", "string")?;
    expect_str("var r = typeof true;", "boolean")?;
    expect_str("var r = typeof undefined;", "undefined")?;
    expect_str("var r = typeof null;", "object")?;
    expect_str("var r = typeof {};", "object")?;
    expect_str("var r = typeof function () {};", "function")?;
    expect_str("var r = typeof notDefinedAnywhere;", "undefined")
}

#[test]
fn objects_and_properties() -> Result<(), String> {
    expect_int("var o = { a: 1, b: 2 }; var r = o.a + o.b;", 3)?;
    expect_int("var o = {}; o.x = 5; var r = o.x;", 5)?;
    expect_int("var o = { a: 1 }; o.a = 9; var r = o.a;", 9)?;
    expect_int(
        "var o = { a: 1 }; var p = { __proto__: o }; var r = p.a;",
        1,
    )?;
    expect_int(
        "var o = { a: 1 }; var p = { __proto__: o }; p.a = 2; var r = o.a * 10 + p.a;",
        12,
    )?;
    expect_bool("var o = { a: 1 }; var r = 'a' in o;", true)?;
    expect_bool("var o = { a: 1 }; var r = 'b' in o;", false)?;
    expect_int("var o = { 'k': 3 }; var r = o['k'];", 3)?;
    expect_int("var k = 'z'; var o = { [k]: 4 }; var r = o.z;", 4)?;
    expect_undefined("var o = {}; var r = o.missing;")
}

fn expect_undefined(src: &str) -> Result<(), String> {
    let (_, r) = global_r(src)?;
    if r == Value::UNDEFINED {
        Ok(())
    } else {
        Err(format!("{src}: expected undefined, got {:?}", r.decode()))
    }
}

#[test]
fn an_inline_cache_hits_across_objects_of_one_shape() -> Result<(), String> {
    // One site, many objects of one shape, then one of another shape.
    expect_int(
        "function get(o) { return o.v; }
         var a = { v: 1 }, b = { v: 2 }, c = { w: 0, v: 3 };
         var r = get(a) * 100 + get(b) * 10 + get(c);",
        123,
    )?;
    expect_int(
        "function set(o, x) { o.v = x; }
         var a = { v: 1 }; set(a, 5); set(a, 6);
         var r = a.v;",
        6,
    )
}

#[test]
fn functions_and_calls() -> Result<(), String> {
    expect_int("function f(a, b) { return a + b; } var r = f(1, 2);", 3)?;
    expect_int("function f(a, b) { return a; } var r = f(7);", 7)?;
    expect_undefined("function f(a, b) { return b; } var r = f(7);")?;
    expect_int("function f(a) { return a; } var r = f(1, 2, 3);", 1)?;
    expect_int(
        "function fact(n) { return n < 2 ? 1 : n * fact(n - 1); } var r = fact(10);",
        3_628_800,
    )?;
    expect_int("var f = function () { return 5; }; var r = f();", 5)?;
    expect_int("var r = (function () { return 6; })();", 6)?;
    expect_int("var r = ((a) => a * 2)(4);", 8)?;
    expect_int(
        "function mk(n) { return function () { return n++; }; }
         var c = mk(10); c(); c();
         var r = c();",
        12,
    )?;
    expect_int(
        "function f() { return arguments_count_; } var arguments_count_ = 4; var r = f();",
        4,
    )?;
    expect_int("function f() { return 1; } var r = f.length + 10;", 10)?;
    expect_str("function foo() {} var r = foo.name;", "foo")?;
    expect_int("function f(a, b, c) {} var r = f.length;", 3)?;
    expect_int(
        "var o = { m() { return this.v; }, v: 8 }; var r = o.m();",
        8,
    )
}

#[test]
fn this_in_sloppy_and_strict_functions() -> Result<(), String> {
    expect_bool("function f() { return this; } var r = f() === this;", true)?;
    expect_undefined("function f() { 'use strict'; return this; } var r = f();")
}

#[test]
fn exceptions() -> Result<(), String> {
    expect_int("var r; try { throw 5; } catch (e) { r = e; }", 5)?;
    expect_int("var r = 0; try { r = 1; } finally { r = r + 10; }", 11)?;
    expect_int(
        "var r = 0; try { try { throw 1; } finally { r += 10; } } catch (e) { r += e; }",
        11,
    )?;
    expect_int(
        "function f() { throw 4; } var r; try { f(); } catch (e) { r = e + 1; }",
        5,
    )?;
    expect_int(
        "function g() { throw 2; } function f() { g(); return 0; }
         var r; try { f(); } catch (e) { r = e; }",
        2,
    )?;
    expect_int(
        "function f() { try { return 1; } finally { r = 9; } } var r = 0; var v = f(); r = r * 10 + v;",
        91,
    )?;
    expect_int("var r; try { null.x; } catch (e) { r = 1; }", 1)?;
    expect_str(
        "var r; try { undefinedName; } catch (e) { r = e.name; }",
        "ReferenceError",
    )?;
    expect_str(
        "var r; try { null.x; } catch (e) { r = e.name; }",
        "TypeError",
    )?;
    expect_str(
        "var r; try { var f = 1; f(); } catch (e) { r = e.name; }",
        "TypeError",
    )?;
    expect_str(
        "var r; try { let x = x; } catch (e) { r = e.name; }",
        "ReferenceError",
    )?;
    expect_str(
        "var r; try { const c = 1; c = 2; } catch (e) { r = e.name; }",
        "TypeError",
    )
}

#[test]
fn an_uncaught_throw_is_the_result() -> Result<(), String> {
    let (vm, r) = run("throw 42;")?;
    match r {
        Err(Abrupt::Throw(v)) => {
            assert_eq!(v, Value::int32(42));
            Ok(())
        }
        other => {
            let _ = vm.heap();
            Err(format!("{other:?}"))
        }
    }
}

#[test]
fn global_declarations() -> Result<(), String> {
    expect_int("var r = 1; var r;", 1)?;
    expect_int("let a = 2; const b = 3; var r = a * b;", 6)?;
    expect_int("function f() { return 1; } var f; var r = f();", 1)?;
    expect_str(
        "var r; try { g = 1; r = 'no'; } catch (e) { r = e.name; } var g;",
        "no",
    )?;
    expect_str(
        "'use strict'; var r; try { nope = 1; } catch (e) { r = e.name; }",
        "ReferenceError",
    )?;
    expect_int("undeclared = 5; var r = undeclared;", 5)?;
    expect_bool("var r = this.hasOwn_ === undefined; var hasOwn_;", true)
}

#[test]
fn a_redeclaration_is_a_syntax_error_before_anything_runs() -> Result<(), String> {
    // Two scripts in one VM: the second redeclares the first's `let`.
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let load = |vm: &mut Vm, src: &str| -> Result<_, String> {
        let c = cps(src);
        let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
        let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
        vm.load(&p).map_err(|e| format!("{e:?}"))
    };
    let first = load(&mut vm, "let a = 1;")?;
    vm.run(&first).map_err(|e| format!("{e:?}"))?;
    let second = load(&mut vm, "var marker = 1; var a;")?;
    match vm.run(&second) {
        Err(Abrupt::Throw(e)) => {
            let n = vm.get_named(e, "name").map_err(|e| format!("{e:?}"))?;
            assert_eq!(vm.string_text(n).as_deref(), Some("SyntaxError"));
            let g = vm.global();
            let m = vm.get_named(g, "marker").map_err(|e| format!("{e:?}"))?;
            assert_eq!(
                m,
                Value::UNDEFINED,
                "no binding is made after a failed check"
            );
            Ok(())
        }
        other => Err(format!("{other:?}")),
    }
}

#[test]
fn what_is_not_implemented_is_an_error_not_a_panic() -> Result<(), String> {
    for src in [
        "var a = [1, 2];",
        "var o = new Object();",
        "var r = delete this.x;",
        "var x = 10n;",
        "function* g() {}",
    ] {
        let c = cps(src);
        let Ok(ast) = parse(&c, SourceGoal::Script) else {
            return Err(format!("does not parse: {src}"));
        };
        let Ok(p) = compile_script(&ast, &c) else {
            continue; // The compiler does not accept it yet either.
        };
        let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
        let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
        match vm.run(&s) {
            Err(Abrupt::NotYet(_) | Abrupt::Throw(_)) | Ok(_) => {}
            Err(e) => return Err(format!("{src}: {e:?}")),
        }
    }
    // Spread needs iterators (GetIterator), which are not implemented.
    let (_, r) = run("var a = [...[1, 2]];")?;
    assert!(matches!(r, Err(Abrupt::NotYet(_))), "{r:?}");
    Ok(())
}

#[test]
fn a_loop_that_never_ends_is_ended_by_the_terminator() -> Result<(), String> {
    let src = "while (true) {}";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.terminator().terminate();
    assert_eq!(vm.run(&s), Err(Abrupt::Terminated));
    vm.terminator().reset();
    vm.set_budget(1000);
    assert_eq!(vm.run(&s), Err(Abrupt::Terminated));
    Ok(())
}

#[test]
fn the_terminator_is_checked_at_calls_and_not_catchable() -> Result<(), String> {
    let src = "function f() { return 1; } try { f(); } catch (e) { var caught = 1; }";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.terminator().terminate();
    assert_eq!(vm.run(&s), Err(Abrupt::Terminated));
    let g = vm.global();
    let caught = vm.get_named(g, "caught").map_err(|e| format!("{e:?}"))?;
    assert_eq!(caught, Value::UNDEFINED);
    Ok(())
}

#[test]
fn the_counters_count_entries_and_back_edges() -> Result<(), String> {
    let src = "function f() { return 1; } for (var i = 0; i < 5; i++) { f(); }";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&s).map_err(|e| format!("{e:?}"))?;
    assert_eq!(vm.entries(s.main), Some(1));
    assert_eq!(vm.back_edges(s.main), Some(5));
    let f = s.main.checked_add(1).ok_or("overflow")?;
    assert_eq!(vm.entries(f), Some(5));
    assert_eq!(vm.back_edges(f), Some(0));
    Ok(())
}

#[test]
fn deep_recursion_is_a_range_error_not_a_crash() -> Result<(), String> {
    // A small region under Miri, so the overflow is reached in few steps.
    let src = "function f() { return f(); } var r; try { f(); } catch (e) { r = e.name; }";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let config = Config {
        region_slots: if cfg!(miri) { 1 << 9 } else { 1 << 18 },
        ..Config::default()
    };
    let mut vm = Vm::new(config).map_err(|e| format!("{e:?}"))?;
    let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&s).map_err(|e| format!("{e:?}"))?;
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    assert_eq!(vm.string_text(r).as_deref(), Some("RangeError"));
    Ok(())
}

#[test]
fn a_native_function_is_called_and_may_call_back() -> Result<(), String> {
    fn twice(vm: &mut Vm, _this: Value, args: &[Value]) -> Result<Value, Abrupt> {
        let f = args.first().copied().unwrap_or(Value::UNDEFINED);
        let x = args.get(1).copied().unwrap_or(Value::UNDEFINED);
        let once = vm.call(f, Value::UNDEFINED, &[x])?;
        vm.call(f, Value::UNDEFINED, &[once])
    }
    let src = "var r = twice(function (n) { return n * 3; }, 2);";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let native = vm
        .new_native("twice", 2, twice)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("twice", native)
        .map_err(|e| format!("{e:?}"))?;
    let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&s).map_err(|e| format!("{e:?}"))?;
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    assert_eq!(r.decode(), Decoded::Int32(18));
    Ok(())
}

#[test]
fn an_exception_thrown_in_a_native_called_from_js_is_caught_by_js() -> Result<(), String> {
    fn boom(_vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
        Err(Abrupt::Throw(Value::int32(77)))
    }
    let src = "var r; try { boom(); } catch (e) { r = e; }";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let native = vm
        .new_native("boom", 0, boom)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("boom", native)
        .map_err(|e| format!("{e:?}"))?;
    let s = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&s).map_err(|e| format!("{e:?}"))?;
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    assert_eq!(r, Value::int32(77));
    Ok(())
}

#[test]
fn constructors_and_prototypes() -> Result<(), String> {
    expect_int(
        "function F() { this.a = 1; } var o = new F(); var r = o.a;",
        1,
    )?;
    expect_int(
        "function F(x) { this.x = x; } F.prototype.get = function () { return this.x; };
         var r = new F(7).get();",
        7,
    )?;
    expect_int("function F() { return { z: 5 }; } var r = new F().z;", 5)?;
    expect_int(
        "function F() { this.q = 2; return 3; } var r = new F().q;",
        2,
    )?;
    expect_bool(
        "function F() {} var o = new F(); var r = o.constructor === F;",
        true,
    )?;
    expect_bool(
        "function F() {} var r = F.prototype.constructor === F;",
        true,
    )?;
    expect_str(
        "var r; try { new (() => 1)(); } catch (e) { r = e.name; }",
        "TypeError",
    )?;
    expect_str(
        "var r; try { new 1; } catch (e) { r = e.name; }",
        "TypeError",
    )
}

fn make_native_object(vm: &mut Vm, _this: Value, _args: &[Value]) -> Result<Value, Abrupt> {
    // A constructor sees `new_target` set; a call sees `undefined`.
    let o = vm.new_object()?;
    let called_as_new = vm.new_target() != Value::UNDEFINED;
    vm.define_property(o, "viaNew", Value::boolean(called_as_new))?;
    let me = vm.active_function();
    vm.define_property(o, "me", me)?;
    Ok(o)
}

#[test]
fn native_constructors_and_bound_functions() -> Result<(), String> {
    let c = cps("var a = new Ctor(); var b = Ctor();
         var e = ''; try { new Plain(); } catch (x) { e = x.name; }
         var made = new BoundCtor();");
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    let ctor = vm
        .new_native_constructor("Ctor", 0, make_native_object)
        .map_err(|e| format!("{e:?}"))?;
    let plain = vm
        .new_native("Plain", 0, make_native_object)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("Ctor", ctor)
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("Plain", plain)
        .map_err(|e| format!("{e:?}"))?;
    let bound_ctor = vm
        .new_bound_function(ctor, Value::UNDEFINED, Vec::new())
        .map_err(|e| format!("{e:?}"))?;
    vm.define_global("BoundCtor", bound_ctor)
        .map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&script).map_err(|e| format!("{e:?}"))?;
    let g = vm.global();
    let get = |vm: &mut Vm, o: Value, n: &str| vm.get_named(o, n).map_err(|e| format!("{e:?}"));
    let (a, b) = (get(&mut vm, g, "a")?, get(&mut vm, g, "b")?);
    assert_eq!(get(&mut vm, a, "viaNew")?, Value::TRUE);
    assert_eq!(get(&mut vm, a, "me")?, ctor);
    assert_eq!(get(&mut vm, b, "viaNew")?, Value::FALSE);
    // `new` of a native without [[Construct]] is a TypeError.
    let e = get(&mut vm, g, "e")?;
    assert_eq!(vm.string_text(e).as_deref(), Some("TypeError"));
    // A bound native constructor constructs its target.
    let made = get(&mut vm, g, "made")?;
    assert_eq!(get(&mut vm, made, "viaNew")?, Value::TRUE);
    // The embedding entry points agree with the ops.
    let direct = vm
        .construct_value(ctor, &[])
        .map_err(|e| format!("{e:?}"))?;
    assert_eq!(get(&mut vm, direct, "viaNew")?, Value::TRUE);
    assert!(vm.is_constructor(ctor) && !vm.is_constructor(plain));
    assert!(vm.is_constructor(bound_ctor));
    Ok(())
}
