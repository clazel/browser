//! Tests of `Map`, `Set`, `WeakMap` and `WeakSet` (§24†) with the built-ins
//! installed, as small scripts whose result is the global `r` as its ToString.
//! No files are read, so these run under Miri too (every eighth case).

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
fn map() -> Result<(), String> {
    let no_new = throws("TypeError", "Map()");
    let bad_entry = throws("TypeError", "new Map([1])");
    let bad_this = throws("TypeError", "Map.prototype.get.call({}, 1)");
    check(&[
        (
            "var m = new Map([[1, 'a'], ['k', 'b']]); m.set(NaN, 'n').set(-0, 'z'); var r = m.size + ',' + m.get(1) + m.get('k') + m.get(NaN) + m.get(0) + ',' + m.has(2) + m.has(+0);",
            "4,abnz,falsetrue",
        ),
        (
            "var m = new Map(); m.set('a', 1); m.set('b', 2); m.delete('a'); m.set('a', 3); var r = Array.from(m.keys()).join() + ';' + Array.from(m.values()).join() + ';' + Array.from(m).join('|');",
            "b,a;2,3;b,2|a,3",
        ),
        (
            "var m = new Map([[1, 1]]); var seen = []; m.forEach(function (v, k, mm) { seen.push(k); if (k < 3) mm.set(k + 1, 1); }); var r = seen.join();",
            "1,2,3",
        ),
        (
            "var m = new Map([[1, 1], [2, 2], [3, 3]]); var it = m.entries(); it.next(); m.delete(2); var r = JSON.stringify(it.next().value) + JSON.stringify(it.next().done);",
            "[3,3]true",
        ),
        (
            "var m = new Map([[1, 1]]); m.clear(); var r = m.size + ',' + m.has(1);",
            "0,false",
        ),
        (
            "var o = {}; var m = new Map([[o, 1]]); var r = m.get(o) + ',' + m.get({});",
            "1,undefined",
        ),
        (
            "var r = Object.prototype.toString.call(new Map()) + Object.prototype.toString.call(new Map().keys()) + (Map.prototype[Symbol.iterator] === Map.prototype.entries) + Map.name + Map.length + Map[Symbol.species] === Map;",
            "false",
        ),
        (
            "var r = (Map.prototype[Symbol.iterator] === Map.prototype.entries) + ',' + Map.length + ',' + Object.prototype.toString.call(new Map()) + ',' + Object.prototype.toString.call(new Map().keys());",
            "true,0,[object Map],[object Map Iterator]",
        ),
        (
            "var g = Map.groupBy([1, 2, 3], function (x) { return x % 2; }); var r = g.get(1).join() + ';' + g.get(0).join() + ';' + g.size;",
            "1,3;2;2",
        ),
        (
            "var d = Object.getOwnPropertyDescriptor(Map.prototype, 'size'); var r = typeof d.get + ',' + d.set;",
            "function,undefined",
        ),
        (
            "class M extends Map { constructor(x) { super(x); this.tag = 1; } } var m = new M([[1, 2]]); var r = (m instanceof Map) + ',' + m.get(1) + ',' + m.tag;",
            "true,2,1",
        ),
        (
            "var added = []; class M extends Map { set(k, v) { added.push(k); return super.set(k, v); } } new M([[1, 2], [3, 4]]); var r = added.join();",
            "1,3",
        ),
        (&no_new, "true"),
        (&bad_entry, "true"),
        (&bad_this, "true"),
    ])
}

#[test]
fn set() -> Result<(), String> {
    let no_new = throws("TypeError", "Set()");
    let bad_size = throws(
        "TypeError",
        "new Set([1]).union({size: NaN, has: function () {}, keys: function () {}})",
    );
    let neg_size = throws(
        "RangeError",
        "new Set([1]).union({size: -1, has: function () {}, keys: function () {}})",
    );
    check(&[
        (
            "var s = new Set([1, 2, 2, 3, NaN, NaN, -0, 0]); var r = s.size + ',' + Array.from(s).join() + ',' + s.has(NaN) + s.has(+0);",
            "5,1,2,3,NaN,0,truetrue",
        ),
        (
            "var s = new Set([1, 2, 3]); s.delete(2); s.add(4); var r = Array.from(s.values()).join() + ';' + (Set.prototype.keys === Set.prototype.values) + (Set.prototype[Symbol.iterator] === Set.prototype.values);",
            "1,3,4;truetrue",
        ),
        (
            "var s = new Set(['a']); var e = Array.from(s.entries())[0]; var r = e.join() + ',' + e.length;",
            "a,a,2",
        ),
        (
            "var s = new Set([1, 2]); var seen = []; s.forEach(function (v, k, ss) { seen.push(v + ':' + k); if (v < 3) ss.add(v + 1); }); var r = seen.join();",
            "1:1,2:2,3:3",
        ),
        (
            "var a = new Set([1, 2, 3]), b = new Set([3, 4]); var r = Array.from(a.union(b)).join() + ';' + Array.from(a.intersection(b)).join() + ';' + Array.from(a.difference(b)).join() + ';' + Array.from(a.symmetricDifference(b)).join();",
            "1,2,3,4;3;1,2;1,2,4",
        ),
        (
            "var a = new Set([1, 2]), b = new Set([1, 2, 3]); var r = a.isSubsetOf(b) + ',' + b.isSupersetOf(a) + ',' + a.isDisjointFrom(new Set([5])) + ',' + a.isDisjointFrom(b) + ',' + b.isSubsetOf(a);",
            "true,true,true,false,false",
        ),
        (
            "var big = new Set([1, 2, 3, 4]); var small = new Set([2, 9]); var r = Array.from(big.intersection(small)).join() + ';' + Array.from(big.difference(small)).join() + ';' + small.isSubsetOf(big);",
            "2;1,3,4;false",
        ),
        (
            "var other = {size: 1, has: function (x) { return x === 1; }, keys: function () { return [1][Symbol.iterator](); }}; var r = Array.from(new Set([1, 2]).intersection(other)).join() + ',' + Array.from(new Set([1, 2]).union(other)).join();",
            "1,1,2",
        ),
        (&no_new, "true"),
        (&bad_size, "true"),
        (&neg_size, "true"),
    ])
}

#[test]
fn weak_collections() -> Result<(), String> {
    let bad_key = throws("TypeError", "new WeakMap().set(1, 1)");
    let bad_value = throws("TypeError", "new WeakSet().add('x')");
    let registered = throws("TypeError", "new WeakSet().add(Symbol.for('r'))");
    check(&[
        (
            "var o = {}, p = {}; var w = new WeakMap([[o, 1]]); w.set(p, 2); var r = w.get(o) + ',' + w.get(p) + ',' + w.has(o) + ',' + w.delete(o) + ',' + w.has(o) + ',' + w.get(1) + ',' + w.delete(1);",
            "1,2,true,true,false,undefined,false",
        ),
        (
            "var o = {}; var s = new WeakSet([o]); var sym = Symbol('w'); s.add(sym); var r = s.has(o) + ',' + s.has({}) + ',' + s.has(sym) + ',' + s.delete(o) + ',' + s.has(o);",
            "true,false,true,true,false",
        ),
        (&bad_key, "true"),
        (&bad_value, "true"),
        (&registered, "true"),
        (
            "var r = Object.prototype.toString.call(new WeakMap()) + Object.prototype.toString.call(new WeakSet()) + ('size' in WeakMap.prototype) + ('forEach' in WeakSet.prototype);",
            "[object WeakMap][object WeakSet]falsefalse",
        ),
    ])
}
