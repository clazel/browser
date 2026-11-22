//! Tests of the built-ins: small scripts compiled by `compile_script` and run
//! in a VM with the built-ins installed, the result read from the global `r`
//! as its ToString. Each expectation is what ECMA-262 says, written by hand.
//!
//! These tests read no files, so they also run under Miri.

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

/// Runs `src` with the built-ins; the VM and the result.
fn run(src: &str) -> Result<(Vm, Result<clazel_js_heap::value::Value, Abrupt>), String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("install: {e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    let r = vm.run(&script);
    Ok((vm, r))
}

/// The ToString of the global `r` after running `src`.
fn r_of(src: &str) -> Result<String, String> {
    let (mut vm, res) = run(src)?;
    res.map_err(|e| format!("{src}: {e:?}"))?;
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    let s = vm.to_js_string(r).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(s.to_string_lossy())
}

/// Runs each `(script, expected ToString of r)`.
fn check(cases: &[(&str, &str)]) -> Result<(), String> {
    for (src, want) in cases {
        let got = r_of(src)?;
        if got != *want {
            return Err(format!("{src}: expected {want:?}, got {got:?}"));
        }
    }
    Ok(())
}

#[test]
fn objects_reach_to_primitive() -> Result<(), String> {
    check(&[
        // §7.1.1.1 OrdinaryToPrimitive: `valueOf` first for hint number and
        // default, `toString` first for hint string.
        (
            "var o = { valueOf: function () { return 6; } }; var r = o * 7;",
            "42",
        ),
        (
            "var o = { valueOf: function () { return 6; } }; var r = o + 1;",
            "7",
        ),
        (
            "var o = { toString: function () { return 'x'; } }; var r = o + 'y';",
            "xy",
        ),
        (
            "var o = { toString: function () { return 'x'; }, valueOf: function () { return 1; } }; var r = '' + o;",
            "1",
        ),
        (
            "var o = { toString: function () { return '5'; } }; var r = o * 2;",
            "10",
        ),
        // A `valueOf` that returns an object is skipped for `toString`.
        (
            "var o = { valueOf: function () { return {}; }, toString: function () { return '3'; } }; var r = +o;",
            "3",
        ),
        (
            "var a = { valueOf: function () { return 1; } }, b = { valueOf: function () { return 2; } }; var r = a < b;",
            "true",
        ),
        (
            "var o = { valueOf: function () { return 3; } }; var r = o == 3;",
            "true",
        ),
        ("var r = {} + '';", "[object Object]"),
        ("var r = String({});", "[object Object]"),
        // Neither method gives a primitive: a TypeError.
        (
            "var o = { valueOf: function () { return {}; }, toString: function () { return {}; } }; var r; try { o + 1; } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
    ])
}

#[test]
fn errors_are_constructed_by_the_constructors() -> Result<(), String> {
    check(&[
        ("var e = new Error('boom'); var r = e.message;", "boom"),
        ("var e = Error('boom'); var r = e.message;", "boom"),
        ("var r = new Error().hasOwnProperty('message');", "false"),
        ("var r = new Error('').hasOwnProperty('message');", "true"),
        ("var r = new Error('m').toString();", "Error: m"),
        ("var r = new TypeError('m').toString();", "TypeError: m"),
        ("var r = new RangeError().toString();", "RangeError"),
        ("var r = new SyntaxError('s').name;", "SyntaxError"),
        ("var r = new ReferenceError('s').name;", "ReferenceError"),
        (
            "var r = Object.getPrototypeOf(new TypeError()) === TypeError.prototype;",
            "true",
        ),
        (
            "var r = Object.getPrototypeOf(TypeError.prototype) === Error.prototype;",
            "true",
        ),
        (
            "var r = Object.getPrototypeOf(TypeError) === Error;",
            "true",
        ),
        (
            "var r = TypeError.prototype.constructor === TypeError;",
            "true",
        ),
        (
            "var r = Object.prototype.toString.call(new Error());",
            "[object Error]",
        ),
        (
            "var r = Error.prototype.toString.call({ name: 'N', message: 'M' });",
            "N: M",
        ),
        (
            "var r = Error.prototype.toString.call({ name: '', message: 'M' });",
            "M",
        ),
        ("var r = Error.prototype.toString.call({});", "Error"),
        ("var r = new Error('m', { cause: 7 }).cause;", "7"),
        (
            "var r = new Error('m', {}).hasOwnProperty('cause');",
            "false",
        ),
        (
            "var r = Error.length + ',' + TypeError.name;",
            "1,TypeError",
        ),
        // The errors the VM throws are the same objects.
        (
            "var r; try { null.x; } catch (e) { r = (e.constructor === TypeError) + ',' + (Object.getPrototypeOf(e) === TypeError.prototype) + ',' + e.hasOwnProperty('name'); }",
            "true,true,false",
        ),
        (
            "var r; try { undefinedName; } catch (e) { r = e.constructor === ReferenceError; }",
            "true",
        ),
        (
            "var r; try { new Error('a', 1); Error.prototype.toString.call(1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var r = Object.prototype.toString.call((function () { try { null.x; } catch (e) { return e; } })());",
            "[object Error]",
        ),
    ])
}

#[test]
fn object_constructor_and_prototype() -> Result<(), String> {
    check(&[
        ("var r = typeof Object();", "object"),
        ("var o = {}; var r = Object(o) === o;", "true"),
        ("var r = typeof Object(1) + (Object(1) + 1);", "object2"),
        ("var r = Object('ab').length;", "2"),
        (
            "var r = Object(null) !== null && typeof Object(undefined);",
            "object",
        ),
        ("var r = typeof new Object(5);", "object"),
        ("var r = new Object(true).valueOf();", "true"),
        (
            "var r = Object.prototype.toString.call(undefined);",
            "[object Undefined]",
        ),
        (
            "var r = Object.prototype.toString.call(null);",
            "[object Null]",
        ),
        (
            "var r = Object.prototype.toString.call(1);",
            "[object Number]",
        ),
        (
            "var r = Object.prototype.toString.call('s');",
            "[object String]",
        ),
        (
            "var r = Object.prototype.toString.call(true);",
            "[object Boolean]",
        ),
        (
            "var r = Object.prototype.toString.call(function () {});",
            "[object Function]",
        ),
        (
            "var r = Object.prototype.toString.call({});",
            "[object Object]",
        ),
        ("var r = ({}).hasOwnProperty('a');", "false"),
        ("var r = ({ a: 1 }).hasOwnProperty('a');", "true"),
        ("var r = ({ a: 1 }).hasOwnProperty('toString');", "false"),
        // ToObject('abc') is a String object with an own `length`.
        (
            "var r = Object.prototype.hasOwnProperty.call('abc', 'length');",
            "true",
        ),
        (
            "var r = Object.prototype.hasOwnProperty.call(new String('abc'), 'length');",
            "true",
        ),
        ("var o = {}; var r = o.valueOf() === o;", "true"),
        ("var r = typeof Object.prototype.valueOf.call(2);", "object"),
        (
            "var r; try { Object.prototype.valueOf.call(null); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        ("var r = Object.prototype.constructor === Object;", "true"),
        (
            "var r = Object.getPrototypeOf({}) === Object.prototype;",
            "true",
        ),
        ("var r = Object.getPrototypeOf(Object.prototype);", "null"),
        (
            "var r = Object.getPrototypeOf(1) === Number.prototype;",
            "true",
        ),
        (
            "var r = Object.getPrototypeOf('s') === String.prototype;",
            "true",
        ),
        (
            "var r; try { Object.getPrototypeOf(null); } catch (e) { r = e.name; }",
            "TypeError",
        ),
    ])
}

#[test]
fn object_keys_create_and_define_property() -> Result<(), String> {
    check(&[
        (
            "var k = Object.keys({ b: 1, a: 2 }); var r = k.length + k[0] + k[1];",
            "2ba",
        ),
        // Integer keys come first, ascending.
        (
            "var k = Object.keys({ b: 1, 10: 2, a: 3, 2: 4 }); var r = k[0] + k[1] + k[2] + k[3];",
            "210ba",
        ),
        ("var r = Object.keys('ab').length;", "0"),
        (
            "var o = Object.create({ p: 1 }); o.q = 2; var k = Object.keys(o); var r = k.length + k[0];",
            "1q",
        ),
        (
            "var p = {}; var o = Object.create(p); var r = Object.getPrototypeOf(o) === p;",
            "true",
        ),
        (
            "var o = Object.create(null); var r = Object.getPrototypeOf(o);",
            "null",
        ),
        (
            "var r; try { Object.create(1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var o = Object.create({}, { a: { value: 1, enumerable: true }, b: { value: 2 } }); var k = Object.keys(o); var r = o.a + o.b + k.length;",
            "4",
        ),
        // A new property takes `false` for each absent attribute.
        (
            "var o = {}; Object.defineProperty(o, 'x', { value: 5 }); o.x = 6; var r = o.x + ',' + Object.keys(o).length + ',' + o.hasOwnProperty('x');",
            "5,0,true",
        ),
        (
            "var o = {}; var r = Object.defineProperty(o, 'x', { value: 1 }) === o;",
            "true",
        ),
        (
            "'use strict'; var o = {}; Object.defineProperty(o, 'x', { value: 5 }); var r; try { o.x = 6; } catch (e) { r = e.name + o.x; }",
            "TypeError5",
        ),
        (
            "var o = {}; Object.defineProperty(o, 'x', { value: 1, writable: true, configurable: true, enumerable: true }); Object.defineProperty(o, 'x', { writable: false }); o.x = 2; var r = o.x + ',' + Object.keys(o)[0];",
            "1,x",
        ),
        // A configurable property may be redefined, even to a new value.
        (
            "var o = { a: 1 }; Object.defineProperty(o, 'a', { value: 9, enumerable: false }); var r = o.a + ',' + Object.keys(o).length;",
            "9,0",
        ),
        // A non-configurable one may not change.
        (
            "var o = {}; Object.defineProperty(o, 'x', { value: 1 }); var r; try { Object.defineProperty(o, 'x', { value: 2 }); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var o = {}; Object.defineProperty(o, 'x', { value: 1 }); var r; try { Object.defineProperty(o, 'x', { configurable: true }); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        // The same value is not a change.
        (
            "var o = {}; Object.defineProperty(o, 'x', { value: 1 }); Object.defineProperty(o, 'x', { value: 1 }); var r = o.x;",
            "1",
        ),
        (
            "var r; try { Object.defineProperty(1, 'x', {}); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var r; try { Object.defineProperty({}, 'x', 1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
    ])
}

#[test]
fn function_prototype_call_apply_bind() -> Result<(), String> {
    check(&[
        (
            "function f(a, b) { return this.k + a + b; } var r = f.call({ k: 1 }, 2, 3);",
            "6",
        ),
        (
            "function f() { return typeof this; } var r = f.call(1);",
            "object",
        ),
        (
            "function f() { 'use strict'; return typeof this; } var r = f.call(1);",
            "number",
        ),
        (
            "function f() { 'use strict'; return this; } var r = f.call(undefined);",
            "undefined",
        ),
        (
            "var r; try { Function.prototype.call.call({}); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "function f(a, b) { return a * b; } var r = f.apply(null, { length: 2, 0: 6, 1: 7 });",
            "42",
        ),
        (
            "function f(a, b) { return a - b; } var r = f.apply(null, { length: 2, 0: 10, 1: 4 });",
            "6",
        ),
        (
            "function f() { return 1; } var r = f.apply(null) + f.apply(null, undefined) + f.apply(null, null);",
            "3",
        ),
        (
            "function f() { return 1; } var r; try { f.apply(null, 1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "function f(a, b) { return this.k + a + b; } var g = f.bind({ k: 1 }, 2); var r = g(3);",
            "6",
        ),
        (
            "function f(a, b, c) { return a + b + c; } var g = f.bind(null, 1).bind(null, 2); var r = g(3);",
            "6",
        ),
        (
            "function f(a, b, c) {} var r = f.bind(null, 1).length;",
            "2",
        ),
        (
            "function f(a) {} var r = f.bind(null, 1, 2, 3).length;",
            "0",
        ),
        ("function foo() {} var r = foo.bind().name;", "bound foo"),
        ("var r = (function () {}).bind().name;", "bound "),
        (
            "function F(x) { this.x = x; } var B = F.bind(null, 5); var o = new B(); var r = o.x + ',' + (Object.getPrototypeOf(o) === F.prototype);",
            "5,true",
        ),
        (
            "function f() { return this; } var r = f.bind(1)() == 1;",
            "true",
        ),
        (
            "var r; try { Function.prototype.bind.call(1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        ("var r = typeof Function;", "function"),
        (
            "var r = Function.prototype.call.length + ',' + Function.prototype.apply.length + ',' + Function.prototype.bind.length;",
            "1,2,1",
        ),
        (
            "function f() {} var r = Object.getPrototypeOf(f) === Function.prototype;",
            "true",
        ),
    ])
}

#[test]
fn boolean_builtin() -> Result<(), String> {
    check(&[
        (
            "var r = Boolean(0) + ',' + Boolean('x') + ',' + Boolean() + ',' + Boolean({});",
            "false,true,false,true",
        ),
        ("var r = typeof new Boolean(false);", "object"),
        ("var r = new Boolean(false) ? 'truthy' : 'falsy';", "truthy"),
        ("var r = new Boolean(true).valueOf();", "true"),
        ("var r = new Boolean(0).toString();", "false"),
        ("var r = true.toString();", "true"),
        ("var r = Boolean.prototype.valueOf.call(false);", "false"),
        (
            "var r; try { Boolean.prototype.toString.call(1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        ("var r = Boolean.prototype.valueOf();", "false"),
        (
            "var r = Object.prototype.toString.call(new Boolean(true));",
            "[object Boolean]",
        ),
        ("var r = new Boolean(1) + 1;", "2"),
    ])
}

#[test]
fn number_builtin() -> Result<(), String> {
    check(&[
        (
            "var r = Number('42') + ',' + Number('') + ',' + Number() + ',' + Number(null) + ',' + Number(undefined);",
            "42,0,0,0,NaN",
        ),
        (
            "var r = Number({ valueOf: function () { return 4; } });",
            "4",
        ),
        ("var r = typeof new Number(1) + new Number(2);", "object2"),
        ("var r = new Number(3).valueOf();", "3"),
        (
            "var r = (255).toString(16) + ',' + (255).toString(2) + ',' + (-255).toString(36) + ',' + (0.5).toString(2);",
            "ff,11111111,-73,0.1",
        ),
        (
            "var r = (1e21).toString() + ',' + (123.456).toString() + ',' + (-0).toString();",
            "1e+21,123.456,0",
        ),
        ("var r = (35).toString(36) + (10).toString(10);", "z10"),
        (
            "var r; try { (1).toString(1); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        (
            "var r; try { (1).toString(37); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        (
            "var r = (1.005).toFixed(2) + ',' + (123.456).toFixed(1) + ',' + (0).toFixed(2) + ',' + (1e21).toFixed(2) + ',' + (2.5).toFixed();",
            "1.00,123.5,0.00,1e+21,3",
        ),
        (
            "var r = NaN.toFixed(2) + ',' + (-1.5).toFixed(0);",
            "NaN,-2",
        ),
        (
            "var r; try { (1).toFixed(101); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        (
            "var r; try { (1).toFixed(-1); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        (
            "var r; try { Number.prototype.toString.call('1'); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var r = Number.MAX_SAFE_INTEGER + ',' + Number.MIN_SAFE_INTEGER + ',' + Number.EPSILON;",
            "9007199254740991,-9007199254740991,2.220446049250313e-16",
        ),
        (
            "var r = Number.MAX_VALUE + ',' + Number.MIN_VALUE;",
            "1.7976931348623157e+308,5e-324",
        ),
        (
            "var r = Number.POSITIVE_INFINITY + ',' + Number.NEGATIVE_INFINITY + ',' + Number.NaN;",
            "Infinity,-Infinity,NaN",
        ),
        (
            "Number.MAX_VALUE = 1; var r = Number.MAX_VALUE > 1;",
            "true",
        ),
        (
            "var r = Number.isInteger(5) + ',' + Number.isInteger(5.5) + ',' + Number.isInteger('5') + ',' + Number.isInteger(Infinity);",
            "true,false,false,false",
        ),
        (
            "var r = Number.isNaN(NaN) + ',' + Number.isNaN('x') + ',' + Number.isFinite(1) + ',' + Number.isFinite('1');",
            "true,false,true,false",
        ),
        (
            "var r = Number.isSafeInteger(9007199254740991) + ',' + Number.isSafeInteger(9007199254740992);",
            "true,false",
        ),
        ("var r = Number.parseFloat === parseFloat;", "true"),
        ("var r = Number.parseInt === parseInt;", "true"),
        ("var r = (5).constructor === Number;", "true"),
        ("var r = Number.prototype.valueOf();", "0"),
    ])
}

#[test]
fn string_builtin() -> Result<(), String> {
    check(&[
        (
            "var r = String(123) + String(true) + String(null) + String(undefined) + String();",
            "123truenullundefined",
        ),
        (
            "var r = String({ toString: function () { return 'T'; } });",
            "T",
        ),
        (
            "var r = typeof new String('a') + new String('bc').length;",
            "object2",
        ),
        ("var r = new String('a') + 'b';", "ab"),
        (
            "var r = new String('xy').valueOf() + new String('z').toString();",
            "xyz",
        ),
        (
            "var r = 'abc'.charAt(1) + '|' + 'abc'.charAt(5) + '|' + 'abc'.charAt(-1) + '|' + 'abc'.charAt();",
            "b|||a",
        ),
        (
            "var r = 'abc'.charCodeAt(1) + ',' + 'abc'.charCodeAt(3) + ',' + 'abc'.charCodeAt(-1);",
            "98,NaN,NaN",
        ),
        (
            "var r = 'hello'.indexOf('l') + ',' + 'hello'.indexOf('l', 3) + ',' + 'hello'.indexOf('z') + ',' + 'hello'.indexOf('') + ',' + 'hello'.indexOf('', 9) + ',' + 'hello'.indexOf('lo');",
            "2,3,-1,0,5,3",
        ),
        (
            "var r = 'hello'.indexOf('hello!') + ',' + 'hello'.indexOf('o', -5) + ',' + 'abc'.indexOf(undefined);",
            "-1,4,-1",
        ),
        (
            "var r = 'hello'.slice(1, 3) + '|' + 'hello'.slice(-3) + '|' + 'hello'.slice(2, -1) + '|' + 'hello'.slice(3, 1) + '|' + 'hello'.slice();",
            "el|llo|ll||hello",
        ),
        (
            "var r = 'hello'.substring(1, 3) + '|' + 'hello'.substring(3, 1) + '|' + 'hello'.substring(-2, 2) + '|' + 'hello'.substring(2) + '|' + 'hello'.substring(NaN, 2);",
            "el|el|he|llo|he",
        ),
        (
            "var r = (123).toString().charAt(1) + true.toString().charAt(0);",
            "2t",
        ),
        (
            "var r = String.fromCharCode(72, 105) + String.fromCharCode(65601).charCodeAt(0);",
            "Hi65",
        ),
        (
            "var r; try { String.prototype.charAt.call(null, 0); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        ("var r = String.prototype.charAt.call(12, 1);", "2"),
        (
            "var r; try { String.prototype.toString.call(1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var r = Object.prototype.toString.call(new String('a'));",
            "[object String]",
        ),
        ("var r = 'abc'.length + 'abc'[1];", "3b"),
        ("var r = ''.constructor === String;", "true"),
        ("var r = 'a' < new String('b');", "true"),
        ("var r = String.prototype.toString();", ""),
    ])
}

#[test]
fn math_builtin() -> Result<(), String> {
    check(&[
        (
            "var r = Math.abs(-3) + ',' + Math.abs('-2.5') + ',' + 1 / Math.abs(-0) + ',' + Math.abs(NaN);",
            "3,2.5,Infinity,NaN",
        ),
        (
            "var r = Math.floor(1.5) + ',' + Math.floor(-1.5) + ',' + Math.ceil(1.2) + ',' + Math.ceil(-1.2) + ',' + 1 / Math.ceil(-0.5);",
            "1,-2,2,-1,-Infinity",
        ),
        (
            "var r = Math.trunc(1.9) + ',' + Math.trunc(-1.9) + ',' + 1 / Math.trunc(-0.9);",
            "1,-1,-Infinity",
        ),
        (
            "var r = Math.round(2.5) + ',' + Math.round(-2.5) + ',' + Math.round(2.4) + ',' + Math.round(-2.6) + ',' + Math.round(0.49999999999999994) + ',' + 1 / Math.round(-0.4) + ',' + 1 / Math.round(-0.5) + ',' + Math.round(1e308 * 10);",
            "3,-2,2,-3,0,-Infinity,-Infinity,Infinity",
        ),
        (
            "var r = Math.round(4503599627370495.5) + ',' + Math.round(-4503599627370495.5);",
            "4503599627370496,-4503599627370495",
        ),
        (
            "var r = Math.sign(-5) + ',' + Math.sign(5) + ',' + 1 / Math.sign(-0) + ',' + Math.sign(0) + ',' + Math.sign(NaN);",
            "-1,1,-Infinity,0,NaN",
        ),
        (
            "var r = Math.min() + ',' + Math.max() + ',' + Math.min(3, 1, 2) + ',' + Math.max(3, 1, 2) + ',' + Math.max(1, NaN) + ',' + Math.min(NaN, 1);",
            "Infinity,-Infinity,1,3,NaN,NaN",
        ),
        (
            "var r = 1 / Math.min(0, -0) + ',' + 1 / Math.min(-0, 0) + ',' + 1 / Math.max(0, -0) + ',' + 1 / Math.max(-0, 0) + ',' + 1 / Math.max(-0, -0);",
            "-Infinity,-Infinity,Infinity,Infinity,-Infinity",
        ),
        (
            "var r = Math.max('7', 3) + ',' + Math.min({ valueOf: function () { return 2; } }, 5);",
            "7,2",
        ),
        (
            "var r = Math.pow(2, 10) + ',' + Math.pow(2, -1) + ',' + Math.pow(NaN, 0) + ',' + Math.pow(1, Infinity) + ',' + Math.pow(-8, 1 / 3) + ',' + Math.pow(0, -1);",
            "1024,0.5,1,NaN,NaN,Infinity",
        ),
        (
            "var r = Math.sqrt(16) + ',' + Math.sqrt(2) + ',' + Math.sqrt(-1) + ',' + 1 / Math.sqrt(-0) + ',' + Math.sqrt(Infinity);",
            "4,1.4142135623730951,NaN,-Infinity,Infinity",
        ),
        (
            "var r = Math.PI + ',' + Math.E + ',' + Math.SQRT2 + ',' + Math.LN2;",
            "3.141592653589793,2.718281828459045,1.4142135623730951,0.6931471805599453",
        ),
        ("Math.PI = 3; var r = Math.PI > 3.14;", "true"),
        (
            "var r = Object.prototype.toString.call(Math);",
            "[object Object]",
        ),
        (
            "var r = Math.max.length + ',' + Math.pow.length + ',' + Math.abs.length;",
            "2,2,1",
        ),
    ])
}

#[test]
fn global_functions() -> Result<(), String> {
    check(&[
        ("var r = globalThis === this;", "true"),
        ("var r = typeof globalThis.Math;", "object"),
        (
            "var r = isNaN('x') + ',' + isNaN('1') + ',' + isNaN(undefined) + ',' + isNaN({}) + ',' + isNaN(null);",
            "true,false,true,true,false",
        ),
        (
            "var r = isFinite('1') + ',' + isFinite(Infinity) + ',' + isFinite(NaN) + ',' + isFinite('x');",
            "true,false,false,false",
        ),
        (
            "var r = parseFloat('3.14abc') + ',' + parseFloat('  -1e3x') + ',' + parseFloat('.5') + ',' + parseFloat('5.') + ',' + parseFloat('abc') + ',' + parseFloat('Infinityx') + ',' + parseFloat('-Infinity');",
            "3.14,-1000,0.5,5,NaN,Infinity,-Infinity",
        ),
        (
            "var r = parseFloat('1e') + ',' + parseFloat('1e+') + ',' + parseFloat('1e+2') + ',' + 1 / parseFloat('-0') + ',' + parseFloat('0x10') + ',' + parseFloat('+.') + ',' + parseFloat('');",
            "1,1,100,-Infinity,0,NaN,NaN",
        ),
        (
            "var r = parseInt('42px') + ',' + parseInt('  -7') + ',' + parseInt('+8') + ',' + parseInt('0x1F') + ',' + parseInt('12', 8) + ',' + parseInt('z', 36) + ',' + parseInt('') + ',' + parseInt('x');",
            "42,-7,8,31,10,35,NaN,NaN",
        ),
        (
            "var r = parseInt('0x10', 16) + ',' + parseInt('0x10', 10) + ',' + parseInt('11', 2) + ',' + parseInt('11', 1) + ',' + parseInt('11', 37) + ',' + parseInt('10', 0) + ',' + parseInt('0X', 16);",
            "16,0,3,NaN,NaN,10,NaN",
        ),
        (
            "var r = 1 / parseInt('-0') + ',' + parseInt('9007199254740993') + ',' + parseInt('123456789012345678901234567890') + ',' + parseInt(0.0000005) + ',' + parseInt('ff', 16.9);",
            "-Infinity,9007199254740992,1.2345678901234568e+29,5,255",
        ),
        (
            "var r = parseInt('ffffffffffffffffffffffffffffffffff', 16) > 1e40;",
            "true",
        ),
    ])
}

#[test]
fn wrapper_objects_and_sloppy_this() -> Result<(), String> {
    check(&[
        (
            "function f() { return typeof this; } var r = f.call('s') + f.call(true) + f.call(1);",
            "objectobjectobject",
        ),
        (
            "function f() { return this.length; } var r = f.call('abc');",
            "3",
        ),
        (
            "String.prototype.twice = function () { return this + this; }; var r = 'ab'.twice();",
            "abab",
        ),
        (
            "Number.prototype.inc = function () { return this + 1; }; var r = (4).inc();",
            "5",
        ),
        (
            "Boolean.prototype.yes = function () { return typeof this; }; var r = true.yes();",
            "object",
        ),
        ("var r = 'abc'.nothing;", "undefined"),
        ("var r = (5).nothing + true.nothing;", "NaN"),
    ])
}

#[test]
fn natives_work_without_the_builtins_installed() -> Result<(), String> {
    // The VM alone still throws plain errors with `name` and `message`.
    let c = cps("var r; try { null.x; } catch (e) { r = e.name + ':' + e.constructor; }");
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| e.to_string())?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&script).map_err(|e| format!("{e:?}"))?;
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    assert_eq!(vm.string_text(r).as_deref(), Some("TypeError:undefined"));
    Ok(())
}
