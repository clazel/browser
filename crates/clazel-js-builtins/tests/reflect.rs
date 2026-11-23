//! Tests of `Reflect` (§28.1†) with the built-ins installed, as small scripts
//! whose result is the global `r` as its ToString. No files are read, so these
//! run under Miri too (every eighth case).

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

/// `r` is true when the body throws an instance of `ctor`.
fn throws(ctor: &str, body: &str) -> String {
    format!("var r; try {{ {body}; r = 'no throw'; }} catch (e) {{ r = e instanceof {ctor}; }}")
}

#[test]
fn reflect() -> Result<(), String> {
    let apply_bad = throws("TypeError", "Reflect.apply(1, null, [])");
    let apply_args = throws("TypeError", "Reflect.apply(function () {}, null, 1)");
    let construct_bad = throws("TypeError", "Reflect.construct(function () {}, [], 1)");
    let construct_arrow = throws("TypeError", "Reflect.construct(() => {}, [])");
    let non_object = throws("TypeError", "Reflect.getPrototypeOf(1)");
    check(&[
        (
            "var r = Reflect.apply(Math.max, null, [1, 5, 2]) + ',' + Reflect.apply(function (a) { return this.x + a; }, {x: 1}, [2]);",
            "5,3",
        ),
        (
            "function F(a) { this.a = a; this.nt = new.target; } function G() {} var o = Reflect.construct(F, [1], G); var r = o.a + ',' + (o.nt === G) + ',' + (Object.getPrototypeOf(o) === G.prototype) + ',' + (new F(2).nt === F);",
            "1,true,true,true",
        ),
        (
            "class A { constructor() { this.nt = new.target.name; } } class B {} var r = Reflect.construct(A, [], B).nt + ',' + (Reflect.construct(Array, [3]).length);",
            "B,3",
        ),
        (
            "class A {} function F() {} var o = Reflect.construct(A, [], F); var r = (Object.getPrototypeOf(o) === F.prototype);",
            "true",
        ),
        (
            "var o = {}; var a = Reflect.defineProperty(o, 'x', {value: 1}); var b = Reflect.defineProperty(o, 'x', {value: 2}); var r = a + ',' + b + ',' + o.x;",
            "true,false,1",
        ),
        (
            "var o = {a: 1}; Object.defineProperty(o, 'f', {value: 1}); var r = Reflect.deleteProperty(o, 'a') + ',' + Reflect.deleteProperty(o, 'f') + ',' + ('a' in o);",
            "true,false,false",
        ),
        (
            "var o = {get x() { return this.y; }, y: 1}; var r = Reflect.get(o, 'x') + ',' + Reflect.get(o, 'x', {y: 2}) + ',' + Reflect.get(o, 'nope');",
            "1,2,undefined",
        ),
        (
            "var o = {set x(v) { this.y = v; }}; var t = {}; var ok = Reflect.set(o, 'x', 5, t); var r = ok + ',' + t.y + ',' + o.y + ',' + Reflect.set(Object.freeze({a: 1}), 'a', 2) + ',' + Reflect.set({}, 'k', 1);",
            "true,5,undefined,false,true",
        ),
        (
            "var a = []; Reflect.set(a, 0, 'x'); Reflect.set(a, 'length', 3); var r = a.length + a[0];",
            "3x",
        ),
        (
            "var d = Reflect.getOwnPropertyDescriptor({a: 1}, 'a'); var r = d.value + ',' + d.enumerable + ',' + Reflect.getOwnPropertyDescriptor({}, 'a');",
            "1,true,undefined",
        ),
        (
            "var p = {}; var o = Object.create(p); var r = (Reflect.getPrototypeOf(o) === p) + ',' + Reflect.setPrototypeOf(o, null) + ',' + Reflect.getPrototypeOf(o) + ',' + Reflect.setPrototypeOf(Object.preventExtensions({}), {});",
            "true,true,null,false",
        ),
        (
            "var o = {a: 1}; var r = Reflect.has(o, 'a') + ',' + Reflect.has(o, 'toString') + ',' + Reflect.has(o, 'zz');",
            "true,true,false",
        ),
        (
            "var o = {}; var r = Reflect.isExtensible(o) + ',' + Reflect.preventExtensions(o) + ',' + Reflect.isExtensible(o);",
            "true,true,false",
        ),
        (
            "var s = Symbol('s'); var o = {b: 1, 1: 1, a: 1}; o[s] = 1; var k = Reflect.ownKeys(o); var r = k.length + ',' + k.slice(0, 3).join() + ',' + (k[3] === s);",
            "4,1,b,a,true",
        ),
        (
            "var r = Object.prototype.toString.call(Reflect) + typeof Reflect;",
            "[object Reflect]object",
        ),
        (&apply_bad, "true"),
        (&apply_args, "true"),
        (&construct_bad, "true"),
        (&construct_arrow, "true"),
        (&non_object, "true"),
    ])
}
