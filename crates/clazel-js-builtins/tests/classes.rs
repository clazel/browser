//! Tests of classes (§15.7†) through the interpreter with the built-ins
//! installed: constructors, methods, accessors, `extends` and `super`, fields,
//! static blocks and private names. Each expectation is what ECMA-262 says,
//! written by hand: the script runs and the result is the global `r` as its
//! ToString. No files are read, so these run under Miri too (every eighth
//! case).

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
fn constructors_methods_and_accessors() -> Result<(), String> {
    let call = throws("TypeError", "class A {} ; A()");
    check(&[
        (
            "class A { constructor(x) { this.x = x; } get double() { return this.x * 2; } set double(v) { this.x = v / 2; } m() { return 'm' + this.x; } static s() { return 's'; } }; var a = new A(4); a.double = 10; var r = a.x + ',' + a.double + ',' + a.m() + ',' + A.s();",
            "5,10,m5,s",
        ),
        (&call, "true"),
        (
            "class A {} var d = Object.getOwnPropertyDescriptor(A, 'prototype'); var r = [d.writable, d.enumerable, d.configurable].join() + ',' + (A.prototype.constructor === A) + ',' + A.name + ',' + typeof A;",
            "false,false,false,true,A,function",
        ),
        (
            "class A { m() {} } var d = Object.getOwnPropertyDescriptor(A.prototype, 'm'); var r = [d.writable, d.enumerable, d.configurable].join() + ',' + d.value.name;",
            "true,false,true,m",
        ),
        (
            "var s = Symbol('k'); class A { [s]() {} get [Symbol.toStringTag]() { return 'T'; } static [Symbol.iterator]() {} }; var r = A.prototype[s].name + ',' + A[Symbol.iterator].name;",
            "[k],[Symbol.iterator]",
        ),
        (
            "class A { get x() { return 1; } } var d = Object.getOwnPropertyDescriptor(A.prototype, 'x'); var r = d.get.name + ',' + d.enumerable + ',' + typeof d.set;",
            "get x,false,undefined",
        ),
        (
            "var C = class {}; var D = class Named {}; var r = C.name + ',' + D.name;",
            "C,Named",
        ),
        (
            "class A { constructor() { return {z: 1}; } } var r = new A().z;",
            "1",
        ),
    ])
}

#[test]
fn inheritance_and_super() -> Result<(), String> {
    let nothing = throws(
        "ReferenceError",
        "class B extends Object { constructor() { } } new B()",
    );
    let twice = throws(
        "ReferenceError",
        "class B extends Object { constructor() { super(); super(); } } new B()",
    );
    let not_ctor = throws("TypeError", "class B extends 1 {}");
    let bad_return = throws(
        "TypeError",
        "class B extends Object { constructor() { super(); return 1; } } new B()",
    );
    check(&[
        (
            "class A { constructor(x) { this.x = x; } m() { return 'A' + this.x; } static s() { return 'sA'; } } class B extends A { constructor(x) { super(x + 1); } m() { return 'B' + super.m(); } static s() { return 'sB' + super.s(); } } var b = new B(1); var r = b.x + ',' + b.m() + ',' + B.s() + ',' + (b instanceof A) + ',' + (Object.getPrototypeOf(B) === A);",
            "2,BA2,sBsA,true,true",
        ),
        (
            "class A {} class B extends A {} class C extends B {} var c = new C(); var r = (c instanceof A) + ',' + (c.constructor === C);",
            "true,true",
        ),
        (
            "class A { constructor() { this.nt = new.target === B; } } class B extends A {} var r = new B().nt + ',' + new A().nt;",
            "true,false",
        ),
        (
            "class A { constructor(a, b) { this.s = a + b; } } class B extends A {} var r = new B(1, 2).s;",
            "3",
        ),
        (
            "class B extends null {} var r = Object.getPrototypeOf(B.prototype) + ',' + (Object.getPrototypeOf(B) === Function.prototype);",
            "null,true",
        ),
        (&nothing, "true"),
        (&twice, "true"),
        (&not_ctor, "true"),
        (&bad_return, "true"),
        (
            "class A { get v() { return this.w; } set v(x) { this.w = x; } } class B extends A { f() { super.v = 3; return super.v; } } var b = new B(); var r = b.f() + ',' + b.w + ',' + b.hasOwnProperty('v');",
            "3,3,false",
        ),
        (
            "var o = { m() { return 'o'; } }; var p = { __proto__: o, m() { return 'p' + super.m(); } }; var r = p.m();",
            "po",
        ),
        // Built-ins can be extended: new.target's prototype is used.
        (
            "class E extends Error { constructor(m) { super(m); this.k = 1; } } var e = new E('boom'); var r = e.message + ',' + (e instanceof Error) + ',' + (e instanceof E) + ',' + e.k;",
            "boom,true,true,1",
        ),
        (
            "class A extends Array { } var a = new A(); a.push(1, 2); var r = a.length + ',' + (a instanceof A) + ',' + Array.isArray(a);",
            "2,true,true",
        ),
        (
            "class P extends Promise {} var p = P.resolve(1); var r = (p instanceof P) + ',' + (p.then(function () {}) instanceof P);",
            "true,true",
        ),
    ])
}

#[test]
fn fields_statics_and_private_names() -> Result<(), String> {
    let wrong_object = throws(
        "TypeError",
        "class A { #x = 1; static g(o) { return o.#x; } } A.g({})",
    );
    let method_write = throws(
        "TypeError",
        "class A { #m() {} w() { this.#m = 1; } } new A().w()",
    );
    check(&[
        (
            "class A { x = 1; y = this.x + 1; static z = 5; 'q' = 3; ['c' + 1] = 4; } var a = new A(); var r = a.x + ',' + a.y + ',' + A.z + ',' + a.q + ',' + a.c1;",
            "1,2,5,3,4",
        ),
        (
            "var log = []; class A { static a = log.push('a'); static { log.push('b'); } static c = log.push('c'); } var r = log.join();",
            "a,b,c",
        ),
        (
            "class A { #p = 7; get() { return this.#p; } set(v) { this.#p = v; } static has(o) { return #p in o; } } var a = new A(); a.set(9); var r = a.get() + ',' + A.has(a) + ',' + A.has({});",
            "9,true,false",
        ),
        (
            "class A { #m() { return 'pm'; } get #g() { return 'pg'; } set #g(v) { this.s = v; } t() { this.#g = 1; return this.#m() + this.#g + this.s; } } var r = new A().t();",
            "pmpg1",
        ),
        (
            "class A { static #sp = 'sp'; static #sm() { return 'sm'; } static t() { return A.#sp + A.#sm(); } } var r = A.t();",
            "spsm",
        ),
        (&wrong_object, "true"),
        (&method_write, "true"),
        (
            "class A { #x = 1; static eq(a, b) { return a.#x === b.#x; } } var r = A.eq(new A(), new A());",
            "true",
        ),
        (
            "class A { x = 1; } class B extends A { y = this.x + 1; constructor() { super(); this.z = this.y + 1; } } var b = new B(); var r = b.x + ',' + b.y + ',' + b.z;",
            "1,2,3",
        ),
        (
            "class A { f = () => this; } var a = new A(); var r = a.f() === a;",
            "true",
        ),
        (
            "class A { #x; constructor(v) { this.#x = v; } static read(o) { return o.#x; } } var r = A.read(new A(3)) + ',' + Object.getOwnPropertyNames(new A(1)).length;",
            "3,0",
        ),
    ])
}
