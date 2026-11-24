//! Tests of `Object` (§20.1†) and `Object.prototype`, as small scripts run with
//! the built-ins installed. Each expectation is what ECMA-262 says, written by
//! hand: the script runs and the result is the global `r` as its ToString. No
//! files are read, so these run under Miri too (every eighth case).

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
fn descriptors() -> Result<(), String> {
    check(&[
        (
            "var d = Object.getOwnPropertyDescriptor({a: 1}, 'a'); var r = [d.value, d.writable, d.enumerable, d.configurable].join();",
            "1,true,true,true",
        ),
        (
            "var o = {}; Object.defineProperty(o, 'x', {get: function () { return 7; }, configurable: true}); var d = Object.getOwnPropertyDescriptor(o, 'x'); var r = [typeof d.get, d.set, d.enumerable, 'value' in d].join();",
            "function,,false,false",
        ),
        (
            "var r = Object.getOwnPropertyDescriptor({}, 'x');",
            "undefined",
        ),
        (
            "var o = {a: 1}; Object.defineProperties(o, {b: {value: 2, enumerable: true}, c: {value: 3}}); var r = Object.keys(o).join() + o.c;",
            "a,b3",
        ),
        (
            "var ds = Object.getOwnPropertyDescriptors({a: 1, get b() { return 2; }}); var r = Object.keys(ds).join() + ds.a.value + typeof ds.b.get;",
            "a,b1function",
        ),
        (
            "var r; try { Object.defineProperty(1, 'x', {}); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var r; try { Object.defineProperty({}, 'x', {get: 1}); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var r; try { Object.defineProperty({}, 'x', {get: function () {}, value: 1}); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        // An accessor becomes a data property again (§10.1.6.3 step 6.b).
        (
            "var o = {}; Object.defineProperty(o, 'x', {get: function () { return 1; }, configurable: true}); Object.defineProperty(o, 'x', {value: 5}); var d = Object.getOwnPropertyDescriptor(o, 'x'); var r = [d.value, d.writable, d.configurable].join();",
            "5,false,true",
        ),
    ])
}

#[test]
fn own_keys_and_enumeration() -> Result<(), String> {
    check(&[
        (
            "var o = {b: 1, 2: 1, a: 1, 1: 1}; var r = Object.getOwnPropertyNames(o).join();",
            "1,2,b,a",
        ),
        (
            "var s = Symbol('s'); var o = {a: 1}; o[s] = 2; var r = Object.getOwnPropertySymbols(o).length + ':' + Object.getOwnPropertyNames(o).join() + ':' + Object.keys(o).join();",
            "1:a:a",
        ),
        (
            "var r = Object.getOwnPropertyNames([1, 2]).join();",
            "0,1,length",
        ),
        (
            "var o = {a: 1, b: 2}; Object.defineProperty(o, 'h', {value: 3}); var r = Object.entries(o).join('|') + ';' + Object.values(o).join();",
            "a,1|b,2;1,2",
        ),
        (
            "var r = Object.keys('ab').length + ',' + Object.values({x: 1}).length;",
            "0,1",
        ),
        (
            "var r; try { Object.keys(null); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var o = Object.assign({a: 1}, {b: 2}, null, {a: 3}); var r = o.a + ',' + o.b;",
            "3,2",
        ),
        (
            "var s = Symbol(); var src = {}; src[s] = 1; var t = Object.assign({}, src); var r = t[s];",
            "1",
        ),
        (
            "var e = Object.fromEntries([['a', 1], ['b', 2]]); var r = e.a + e.b;",
            "3",
        ),
        (
            "var r; try { Object.fromEntries([1]); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var g = Object.groupBy([1, 2, 3, 4], function (x) { return x % 2 ? 'odd' : 'even'; }); var r = g.odd.join() + ';' + g.even.join() + ';' + Object.getPrototypeOf(g);",
            "1,3;2,4;null",
        ),
        (
            "var r = Object.is(NaN, NaN) + ',' + Object.is(0, -0) + ',' + Object.is('a', 'a');",
            "true,false,true",
        ),
        (
            "var r = Object.hasOwn({a: 1}, 'a') + ',' + Object.hasOwn({}, 'toString');",
            "true,false",
        ),
    ])
}

#[test]
fn integrity_levels_and_extensibility() -> Result<(), String> {
    check(&[
        (
            "'use strict'; var o = Object.freeze({a: 1}); var r; try { o.a = 2; } catch (e) { r = e.constructor === TypeError; } r = r + ',' + o.a + ',' + Object.isFrozen(o);",
            "true,1,true",
        ),
        (
            "'use strict'; var o = Object.preventExtensions({a: 1}); var r; try { o.b = 2; } catch (e) { r = e.constructor === TypeError; } r = r + ',' + ('b' in o) + ',' + Object.isExtensible(o);",
            "true,false,false",
        ),
        (
            "var o = Object.seal({a: 1}); o.a = 2; delete o.a; o.b = 3; var r = o.a + ',' + o.b + ',' + Object.isSealed(o) + ',' + Object.isFrozen(o);",
            "2,undefined,true,false",
        ),
        (
            "var o = Object.freeze([1, 2]); var r; try { o.push(3); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var r = Object.isFrozen(1) + ',' + Object.isExtensible(1) + ',' + Object.freeze(1);",
            "true,false,1",
        ),
        (
            "var r = Object.isFrozen(Object.preventExtensions({}));",
            "true",
        ),
        (
            "var o = Object.preventExtensions({}); var r; try { Object.defineProperty(o, 'x', {value: 1}); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var o = Object.freeze({get a() { return 1; }}); var d = Object.getOwnPropertyDescriptor(o, 'a'); var r = d.configurable + ',' + typeof d.get;",
            "false,function",
        ),
    ])
}

#[test]
fn prototypes() -> Result<(), String> {
    check(&[
        (
            "var p = {x: 1}; var o = {}; Object.setPrototypeOf(o, p); var r = o.x + ',' + (Object.getPrototypeOf(o) === p) + ',' + p.isPrototypeOf(o) + ',' + Object.prototype.isPrototypeOf(o);",
            "1,true,true,true",
        ),
        (
            "var a = {}; var b = Object.create(a); var r; try { Object.setPrototypeOf(a, b); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var o = Object.preventExtensions({}); var r; try { Object.setPrototypeOf(o, {}); } catch (e) { r = e.constructor === TypeError; } r = r + ',' + (Object.setPrototypeOf(o, Object.prototype) === o);",
            "true,true",
        ),
        (
            "var r; try { Object.setPrototypeOf({}, 1); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        ("var r = Object.setPrototypeOf(1, null);", "1"),
        (
            "var o = {}; o.__proto__ = {y: 2}; var r = o.y + ',' + (Object.getPrototypeOf(o.__proto__) === Object.prototype);",
            "2,true",
        ),
        (
            "var o = {}; o.__defineGetter__('g', function () { return 4; }); o.__defineSetter__('g', function (v) { this.s = v; }); o.g = 9; var r = o.g + ',' + o.s + ',' + typeof o.__lookupGetter__('g') + ',' + typeof o.__lookupSetter__('g') + ',' + o.__lookupGetter__('nope');",
            "4,9,function,function,undefined",
        ),
        (
            "var o = {a: 1}; Object.defineProperty(o, 'h', {value: 1}); var r = o.propertyIsEnumerable('a') + ',' + o.propertyIsEnumerable('h') + ',' + o.propertyIsEnumerable('z');",
            "true,false,false",
        ),
    ])
}

#[test]
fn spread_rest_and_assignment_failures() -> Result<(), String> {
    let readonly = "'use strict'; var r; try { Object.assign(Object.freeze({a: 1}), {a: 2}); } catch (e) { r = e.constructor === TypeError; }";
    let sealed = "var r; try { Object.assign(Object.seal({}), {a: 2}); } catch (e) { r = e.constructor === TypeError; }";
    let frozen_field = "class A { x = 1; constructor(o) { return o; } } class B extends A { y = 2; } var r; try { new B(Object.freeze({})); } catch (e) { r = e.constructor === TypeError; }";
    let static_proto = "var r; try { class A { static ['prototype'] = 1; } } catch (e) { r = e.constructor === TypeError; }";
    check(&[
        (
            "var s = Symbol('s'); var src = {a: 1, [s]: 2}; Object.defineProperty(src, 'h', {value: 3}); var o = {z: 0, ...src, ...null, ...'xy'}; var r = Object.keys(o).join() + o[s];",
            "z,a2",
        ),
        (
            "var {a, ...rest} = {a: 1, b: 2, c: 3}; var r = a + ',' + Object.keys(rest).join();",
            "1,b,c",
        ),
        (
            "var k = 'b'; var {[k]: v, ...rest} = {a: 1, b: 2}; var r = v + ',' + Object.keys(rest).join();",
            "2,a",
        ),
        (
            "var src = {get a() { return 'got'; }}; var o = {...src}; var d = Object.getOwnPropertyDescriptor(o, 'a'); var r = d.value + d.writable + d.enumerable + d.configurable;",
            "gottruetruetrue",
        ),
        (readonly, "true"),
        (sealed, "true"),
        (frozen_field, "true"),
        (static_proto, "true"),
    ])
}
