//! Tests of arrays: the Array exotic object (§10.4.2†) and the `Array`
//! built-in, as small scripts run with the built-ins installed. Each
//! expectation is what ECMA-262 says, written by hand; the result is the
//! global `r` as its ToString. No files are read, so these run under Miri
//! too (with every eighth case, as the other built-in tests do).

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Config, Vm};

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
    vm.run(&script).map_err(|e| format!("{src}: {e:?}"))?;
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
fn array_exotic_objects() -> Result<(), String> {
    check(&[
        // §10.4.2.1 step 2.h: an index at or above `length` grows it.
        ("var a = []; a[4] = 1; var r = a.length;", "5"),
        ("var a = [1, 2, 3]; var r = a.length;", "3"),
        (
            "var a = [1, , 3]; var r = a.length + ',' + (1 in a);",
            "3,false",
        ),
        ("var a = [1, 2, ,]; var r = a.length;", "3"),
        // A key that is not a canonical index does not.
        ("var a = []; a['01'] = 1; a.x = 2; var r = a.length;", "0"),
        (
            "var a = []; a[4294967294] = 1; var r = a.length;",
            "4294967295",
        ),
        ("var a = []; a[4294967295] = 1; var r = a.length;", "0"),
        // ArraySetLength truncates, §10.4.2.4.
        (
            "var a = [1, 2, 3, 4]; a.length = 2; var r = a + ',' + a.length;",
            "1,2,2",
        ),
        (
            "var a = [1, 2]; a.length = 5; var r = a.length + ',' + (3 in a);",
            "5,false",
        ),
        (
            "var a = [1, 2, 3]; a.length = 0; var r = a.length + ',' + (0 in a);",
            "0,false",
        ),
        // Step 5: a RangeError for a length that is not a Uint32.
        (
            "var r; try { [].length = -1; } catch (e) { r = e.name; }",
            "RangeError",
        ),
        (
            "var r; try { [].length = 1.5; } catch (e) { r = e.name; }",
            "RangeError",
        ),
        ("var a = []; a.length = '3'; var r = a.length;", "3"),
        // A non-configurable element stops the truncation (step 16.b).
        (
            "var a = [1, 2]; Object.defineProperty(a, 2, { value: 5 }); a.length = 0; var r = a.length + ',' + a[0] + ',' + a[2];",
            "3,1,5",
        ),
        // `length` is not enumerable, writable, not configurable.
        (
            "var a = [1]; var r = Object.keys(a).join() + '|' + a.hasOwnProperty('length');",
            "0|true",
        ),
        (
            "var a = [1, 2]; Object.defineProperty(a, 'length', { writable: false }); a[2] = 3; var r = a.length + ',' + (2 in a);",
            "2,false",
        ),
        (
            "'use strict'; var a = [1]; Object.defineProperty(a, 'length', { writable: false }); var r; try { a.push(2); } catch (e) { r = e.name + a.length; }",
            "TypeError1",
        ),
        // Array.prototype is an array, Object.prototype.toString says so.
        (
            "var r = Array.isArray(Array.prototype) + ',' + Object.prototype.toString.call([]);",
            "true,[object Array]",
        ),
        (
            "var r = Array.isArray({ length: 0 }) + ',' + Array.isArray([]);",
            "false,true",
        ),
        (
            "var r = Object.getPrototypeOf([]) === Array.prototype;",
            "true",
        ),
        // Object.keys returns an array now.
        ("var r = Array.isArray(Object.keys({ a: 1 }));", "true"),
        (
            "var a = [3, 4]; var r = delete a[0]; r = r + ',' + a.length + ',' + (0 in a);",
            "true,2,false",
        ),
    ])
}

#[test]
fn array_constructor_and_statics() -> Result<(), String> {
    check(&[
        ("var r = new Array().length;", "0"),
        (
            "var r = new Array(3).length + ',' + (0 in new Array(3));",
            "3,false",
        ),
        ("var r = Array(1, 2, 3).join();", "1,2,3"),
        ("var r = Array('a').join() + new Array('a').length;", "a1"),
        (
            "var r; try { new Array(-1); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        (
            "var r; try { new Array(1.5); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        ("var r = new Array(4294967295).length;", "4294967295"),
        (
            "var r = Array.of(7, 8, 9).join('-') + Array.of(3).length;",
            "7-8-91",
        ),
        ("var r = Array.of().length;", "0"),
        (
            "var r = Array.length + Array.name + Array.prototype.constructor.name;",
            "1ArrayArray",
        ),
        (
            "var r = Array.prototype.push.length + Array.prototype.splice.length;",
            "3",
        ),
        ("var r = Array.isArray(new Array(2));", "true"),
    ])
}

#[test]
fn array_mutators() -> Result<(), String> {
    check(&[
        (
            "var a = [1]; var n = a.push(2, 3); var r = n + ',' + a;",
            "3,1,2,3",
        ),
        (
            "var a = [1, 2, 3]; var x = a.pop(); var r = x + ',' + a;",
            "3,1,2",
        ),
        (
            "var a = []; var r = a.pop() + ',' + a.length;",
            "undefined,0",
        ),
        (
            "var a = [1, 2, 3]; var x = a.shift(); var r = x + ',' + a + ',' + a.length;",
            "1,2,3,2",
        ),
        (
            "var a = [1, , 3]; a.shift(); var r = a.length + ',' + (0 in a) + ',' + a[1];",
            "2,false,3",
        ),
        (
            "var a = [3]; var n = a.unshift(1, 2); var r = n + ',' + a;",
            "3,1,2,3",
        ),
        (
            "var a = [1, 2, 3, 4, 5]; var d = a.splice(1, 2); var r = d + '|' + a;",
            "2,3|1,4,5",
        ),
        (
            "var a = [1, 2, 3]; var d = a.splice(1, 0, 'x', 'y'); var r = d.length + '|' + a;",
            "0|1,x,y,2,3",
        ),
        (
            "var a = [1, 2, 3]; var d = a.splice(1); var r = d + '|' + a;",
            "2,3|1",
        ),
        (
            "var a = [1, 2, 3]; var d = a.splice(-1, 1, 9); var r = d + '|' + a;",
            "3|1,2,9",
        ),
        (
            "var a = [1, 2, 3]; var d = a.splice(); var r = d.length + '|' + a;",
            "0|1,2,3",
        ),
        (
            "var a = [1, 2, 3]; var d = a.splice(0, 3, 'a'); var r = d + '|' + a;",
            "1,2,3|a",
        ),
        ("var a = [1, 2, 3]; a.reverse(); var r = a.join();", "3,2,1"),
        (
            "var a = [1, 2, 3, 4]; a.reverse(); var r = a.join();",
            "4,3,2,1",
        ),
        (
            "var a = [1, , 3]; a.reverse(); var r = a.join() + ',' + (1 in a);",
            "3,,1,false",
        ),
        (
            "var a = [1, , 3, 4]; a.reverse(); var r = (2 in a) + ',' + a[3];",
            "false,1",
        ),
        (
            "var a = [1, 2, 3, 4]; a.fill(0, 1, 3); var r = a.join();",
            "1,0,0,4",
        ),
        ("var a = [1, 2, 3]; a.fill(7); var r = a.join();", "7,7,7"),
        (
            "var a = [1, 2, 3]; a.fill(7, -1); var r = a.join();",
            "1,2,7",
        ),
        // Generic: an array-like object.
        (
            "var o = { length: 2, 0: 'a', 1: 'b' }; Array.prototype.push.call(o, 'c'); var r = o.length + o[2];",
            "3c",
        ),
        (
            "var o = { length: 3, 0: 'a', 1: 'b', 2: 'c' }; Array.prototype.reverse.call(o); var r = o[0] + o[1] + o[2];",
            "cba",
        ),
        (
            "var o = { length: 9007199254740991 }; var r; try { Array.prototype.push.call(o, 1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
    ])
}

#[test]
fn array_accessors() -> Result<(), String> {
    check(&[
        ("var r = [1, 2, 3, 4].slice(1, 3).join();", "2,3"),
        ("var r = [1, 2, 3, 4].slice(-2).join();", "3,4"),
        ("var r = [1, 2, 3, 4].slice().join();", "1,2,3,4"),
        ("var r = [1, 2, 3].slice(2, 1).length;", "0"),
        (
            "var s = [1, , 3].slice(0); var r = s.length + ',' + (1 in s);",
            "3,false",
        ),
        ("var r = [1, 2].concat([3, 4], 5, [[6]]).length;", "6"),
        ("var r = [1].concat([2], [3, [4]]).join();", "1,2,3,4"),
        (
            "var c = [1, , 3].concat([4]); var r = c.length + ',' + (1 in c);",
            "4,false",
        ),
        ("var r = [1, 2, 3].join('-');", "1-2-3"),
        ("var r = [1, null, undefined, 4].join();", "1,,,4"),
        ("var r = [].join() + '|' + [5].join('x');", "|5"),
        ("var r = [[1, 2], [3]].join(';');", "1,2;3"),
        ("var r = String([1, [2, 3]]);", "1,2,3"),
        (
            "var r = [1, 2, 3, 2].indexOf(2) + ',' + [1, 2, 3, 2].indexOf(2, 2) + ',' + [1].indexOf(5);",
            "1,3,-1",
        ),
        (
            "var r = [1, 2, 3, 2].indexOf(2, -1) + ',' + [NaN].indexOf(NaN);",
            "3,-1",
        ),
        (
            "var r = [1, 2, 3, 2].lastIndexOf(2) + ',' + [1, 2, 3, 2].lastIndexOf(2, 2) + ',' + [1].lastIndexOf(5);",
            "3,1,-1",
        ),
        ("var r = [1, 2, 3].lastIndexOf(3, -2);", "-1"),
        (
            "var r = [1, NaN].includes(NaN) + ',' + [1, 2].includes(3) + ',' + [1, 2].includes(1, 1);",
            "true,false,false",
        ),
        (
            "var r = [, 1].includes(undefined) + ',' + [, 1].indexOf(undefined);",
            "true,-1",
        ),
        (
            "var r = [0].includes(-0) + ',' + [-0].indexOf(0);",
            "true,0",
        ),
    ])
}

#[test]
fn array_callbacks() -> Result<(), String> {
    check(&[
        (
            "var s = 0; [1, 2, 3].forEach(function (v) { s += v; }); var r = s;",
            "6",
        ),
        (
            "var s = 0; [1, , 3].forEach(function (v) { s += 1; }); var r = s;",
            "2",
        ),
        (
            "var o = {}; [1].forEach(function (v, i, a) { o.x = this === o && v === 1 && i === 0 && a.length === 1; }, o); var r = o.x;",
            "true",
        ),
        (
            "var r = [1, 2, 3].map(function (v) { return v * 2; }).join();",
            "2,4,6",
        ),
        (
            "var m = [1, , 3].map(function (v) { return v; }); var r = m.length + ',' + (1 in m);",
            "3,false",
        ),
        (
            "var r = [1, 2, 3, 4].filter(function (v) { return v % 2 === 0; }).join();",
            "2,4",
        ),
        (
            "var r = [1, 2, 3].some(function (v) { return v > 2; }) + ',' + [1, 2].some(function (v) { return v > 2; });",
            "true,false",
        ),
        (
            "var r = [1, 2, 3].every(function (v) { return v > 0; }) + ',' + [1, 2].every(function (v) { return v > 1; }) + ',' + [].every(function () { return false; });",
            "true,false,true",
        ),
        (
            "var r = [1, 2, 3].reduce(function (a, v) { return a + v; }) + ',' + [1, 2, 3].reduce(function (a, v) { return a + v; }, 10);",
            "6,16",
        ),
        (
            "var r = ['a', 'b', 'c'].reduceRight(function (a, v) { return a + v; }) + ',' + [1].reduceRight(function (a, v) { return a + v; }, 5);",
            "cba,6",
        ),
        (
            "var r; try { [].reduce(function () {}); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var r; try { [1].map(3); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var r = [1, 2, 3].find(function (v) { return v > 1; }) + ',' + [1, 2, 3].findIndex(function (v) { return v > 1; }) + ',' + [1].find(function (v) { return v > 1; }) + ',' + [1].findIndex(function (v) { return v > 1; });",
            "2,1,undefined,-1",
        ),
        // find visits holes as undefined (no HasProperty).
        (
            "var n = 0; [, ,].find(function (v) { n++; return false; }); var r = n;",
            "2",
        ),
        // The length is read once: an element pushed during forEach is not visited.
        (
            "var a = [1, 2]; var n = 0; a.forEach(function (v) { n++; a.push(9); }); var r = n + ',' + a.length;",
            "2,4",
        ),
    ])
}

#[test]
fn array_sort() -> Result<(), String> {
    check(&[
        ("var r = [3, 1, 2].sort().join();", "1,2,3"),
        // The default order is by string: "10" < "9".
        ("var r = [9, 10, 1].sort().join();", "1,10,9"),
        (
            "var r = [3, 1, 2].sort(function (a, b) { return b - a; }).join();",
            "3,2,1",
        ),
        // undefined last, holes after them.
        (
            "var a = [3, undefined, 1, , 2]; a.sort(); var r = a.length + ',' + a.join() + ',' + (4 in a) + ',' + (3 in a);",
            "5,1,2,3,,,false,true",
        ),
        // Stable.
        (
            "var a = [{ k: 1, v: 'a' }, { k: 0, v: 'b' }, { k: 1, v: 'c' }, { k: 0, v: 'd' }]; a.sort(function (x, y) { return x.k - y.k; }); var r = a.map(function (e) { return e.v; }).join('');",
            "bdac",
        ),
        (
            "var r; try { [1].sort(1); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        // An exception from the comparator ends the sort and propagates.
        (
            "var r; try { [2, 1].sort(function () { throw 7; }); } catch (e) { r = e; }",
            "7",
        ),
        (
            "var a = []; for (var i = 0; i < 50; i++) a.push((i * 37) % 50); a.sort(function (x, y) { return x - y; }); var ok = true; for (var j = 0; j < 50; j++) if (a[j] !== j) ok = false; var r = ok;",
            "true",
        ),
        // NaN from the comparator is +0.
        (
            "var r = [2, 1].sort(function () { return NaN; }).join();",
            "2,1",
        ),
    ])
}

#[test]
fn array_species_and_recursion_bounds() -> Result<(), String> {
    check(&[
        // A cyclic join recurses through natives until the bound, a RangeError.
        (
            "var a = []; a[0] = a; var r; try { a.join(); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        // A `constructor` that is not a constructor is a TypeError
        // (§10.4.2.3 step 6).
        (
            "var a = [1]; a.constructor = 1; var r; try { a.map(function (v) { return v; }); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var a = [1]; a.constructor = undefined; var r = a.map(function (v) { return v + 1; }).join();",
            "2",
        ),
    ])
}
