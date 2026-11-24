//! Tests of Symbols and iteration: the iterator protocol run by the
//! interpreter's `GetIterator`, `IterNext` and `IterClose` (spread,
//! `for`-`of`, destructuring), the Array and String iterators, `Symbol`,
//! `instanceof` and `for`-`in`, as small scripts run with the built-ins
//! installed. Each expectation is what ECMA-262 says, written by hand; the
//! result is the global `r` as its ToString. No files are read, so these
//! run under Miri too (with every eighth case, as the other built-in tests
//! do).

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
    if let Err(e) = vm.run(&script) {
        let d = match e {
            clazel_js_vm::interp::Abrupt::Throw(v) => vm.describe(v),
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
fn symbols() -> Result<(), String> {
    check(&[
        ("var r = typeof Symbol();", "symbol"),
        ("var r = typeof Symbol.iterator;", "symbol"),
        ("var r = Symbol('x').toString();", "Symbol(x)"),
        ("var r = String(Symbol('y'));", "Symbol(y)"),
        ("var r = String(Symbol());", "Symbol()"),
        (
            "var r = Symbol.iterator.toString();",
            "Symbol(Symbol.iterator)",
        ),
        // Each call makes a new Symbol; Symbol.for shares one per key.
        ("var r = Symbol('a') === Symbol('a');", "false"),
        ("var r = Symbol.for('a') === Symbol.for('a');", "true"),
        ("var r = Symbol.keyFor(Symbol.for('k'));", "k"),
        ("var r = Symbol.keyFor(Symbol('k'));", "undefined"),
        ("var r = Symbol.keyFor(Symbol.iterator);", "undefined"),
        // §20.4.1.1 step 1: not a constructor.
        (
            "var r; try { new Symbol(); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        // §7.1.17 step 2 and §7.1.4 step 2: no implicit conversion.
        (
            "var r; try { Symbol() + ''; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { +Symbol(); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        // Symbols as property keys: not strings, not enumerated.
        (
            "var s = Symbol('p'); var o = {}; o[s] = 1; o.p = 2; var r = o[s] + ',' + o.p + ',' + Object.keys(o).length;",
            "1,2,1",
        ),
        ("var s = Symbol(); var o = { [s]: 5 }; var r = o[s];", "5"),
        (
            "var s = Symbol('m'); var o = { [s]() { return 3; } }; var r = o[s]() + o[s].name;",
            "3[m]",
        ),
        (
            "var s = Symbol(); var o = { [s]: 1 }; var r = s in o;",
            "true",
        ),
        (
            "var s = Symbol(); var r = ''; for (var k in { [s]: 1, a: 2 }) r += k;",
            "a",
        ),
        ("var s = Symbol(); var r = s == s;", "true"),
        ("var r = Symbol() == 1;", "false"),
        (
            "var r = Object(Symbol.iterator) == Symbol.iterator;",
            "true",
        ),
        ("var r = typeof Object(Symbol());", "object"),
        (
            "var r = Object.prototype.toString.call(Symbol());",
            "[object Symbol]",
        ),
        ("var r = Symbol().valueOf() !== undefined;", "true"),
        // @@toPrimitive is consulted first (§7.1.1 step 1.b).
        (
            "var o = { [Symbol.toPrimitive](h) { return h; } }; var r = (o + '') + ',' + `${o}` + ',' + (o * 1);",
            "default,string,NaN",
        ),
        (
            "var r; try { ({ [Symbol.toPrimitive]: 1 }) + ''; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
    ])
}

#[test]
fn instanceof() -> Result<(), String> {
    check(&[
        ("function F() {} var r = new F() instanceof F;", "true"),
        ("function F() {} var r = {} instanceof F;", "false"),
        ("var r = [] instanceof Array;", "true"),
        ("var r = [] instanceof Object;", "true"),
        ("var r = 1 instanceof Object;", "false"),
        ("var r = new TypeError('x') instanceof Error;", "true"),
        (
            "function F() {} var B = F.bind(null); var r = new F() instanceof B;",
            "true",
        ),
        (
            "var C = { [Symbol.hasInstance](v) { return v === 1; } }; var r = 1 instanceof C;",
            "true",
        ),
        (
            "var r; try { ({}) instanceof {}; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r = Function.prototype[Symbol.hasInstance].call(Array, []);",
            "true",
        ),
    ])
}

#[test]
fn spread_for_of_and_destructuring() -> Result<(), String> {
    check(&[
        ("var r = [...[1, 2, 3]].join();", "1,2,3"),
        (
            "var a = [1, 2]; var r = [0, ...a, 3, ...a].join();",
            "0,1,2,3,1,2",
        ),
        ("var r = [...'ab'].join('|');", "a|b"),
        // A surrogate pair is one code point (§22.1.3.36).
        ("var r = [...'a\\uD83D\\uDE00b'].length;", "3"),
        ("var r = [...'\\uD83Dx'].length;", "2"),
        (
            "function f(a, b, c) { return a + b + c; } var r = f(...[1, 2, 3]);",
            "6",
        ),
        (
            "function f(a, b) { return a + b; } var r = f(1, ...[2]);",
            "3",
        ),
        (
            "function F(a, b) { this.v = a * b; } var r = new F(...[6, 7]).v;",
            "42",
        ),
        ("var r = Math.max(...[1, 9, 4]);", "9"),
        ("var r = 0; for (var x of [1, 2, 3]) r += x;", "6"),
        ("var r = ''; for (const c of 'xyz') r = c + r;", "zyx"),
        (
            "var r = 0; for (let [k, v] of [[1, 2], [3, 4]]) r += k * v;",
            "14",
        ),
        (
            "var r = ''; for (var [i, v] of ['a', 'b'].entries()) r += i + v;",
            "0a1b",
        ),
        ("var r = ''; for (var k of ['a', 'b'].keys()) r += k;", "01"),
        ("var [a, b] = [1, 2]; var r = a + b;", "3"),
        ("var [a, , b] = [1, 2, 3]; var r = a + b;", "4"),
        ("var [a, ...b] = [1, 2, 3]; var r = b.join();", "2,3"),
        ("var [a = 5, b = 6] = [1]; var r = a + b;", "7"),
        (
            "var a = 1, b = 2; [a, b] = [b, a]; var r = a + ',' + b;",
            "2,1",
        ),
        // The value of an assignment pattern is its right-hand side.
        (
            "var a, b; [a, b] = [b, a] = [1, 2]; var r = a + ',' + b;",
            "1,2",
        ),
        ("var [x, y] = 'hi'; var r = y + x;", "ih"),
        (
            "function f([a, b]) { return a * b; } var r = f([3, 4]);",
            "12",
        ),
        // Holes read as undefined through the iterator.
        ("var r = [...[, 1]][0];", "undefined"),
        // An array that grows while it is iterated is seen to grow.
        (
            "var a = [1]; var r = 0; for (var x of a) { if (a.length < 3) a.push(x + 1); r += x; }",
            "6",
        ),
        // Not iterable: a TypeError.
        (
            "var r; try { [...{}]; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { for (var x of 5) {} } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { var [a] = null; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
    ])
}

#[test]
fn user_iterators_and_closing() -> Result<(), String> {
    // An iterable whose `return` records that it was called.
    let it = "var log = []; function mk(n) { var i = 0; return { [Symbol.iterator]() { return { next() { i++; return { value: i, done: i > n }; }, return() { log.push('ret'); return {}; } }; } }; }";
    let cases = [
        format!("{it} var r = [...mk(3)].join() + log.length;"),
        format!("{it} for (var x of mk(5)) {{ if (x === 2) break; }} var r = log.join();"),
        format!(
            "{it} try {{ for (var x of mk(5)) {{ throw 1; }} }} catch (e) {{}} var r = log.join();"
        ),
        format!("{it} var [a, b] = mk(5); var r = a + b + log.join();"),
        format!("{it} var [a, b] = mk(1); var r = String(b) + log.length;"),
        format!("{it} function f() {{ for (var x of mk(5)) return x; }} var r = f() + log.join();"),
        format!("{it} var r = Array.from(mk(2)).join();"),
    ];
    let want = ["1,2,30", "ret", "ret", "3ret", "undefined0", "1ret", "1,2"];
    let stride = if cfg!(miri) { 8 } else { 1 };
    for (src, w) in cases.iter().zip(want).step_by(stride) {
        let got = r_of(src)?;
        if got != w {
            return Err(format!("{src}: expected {w:?}, got {got:?}"));
        }
    }
    check(&[
        // `next` returning a non-object is a TypeError (§7.4.5 step 3).
        (
            "var o = { [Symbol.iterator]() { return { next() { return 1; } }; } }; var r; try { [...o]; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        // @@iterator returning a non-object (§7.4.3 step 2).
        (
            "var o = { [Symbol.iterator]() { return 1; } }; var r; try { [...o]; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        // A throw from the loop body wins over a throw from `return`.
        (
            "var o = { [Symbol.iterator]() { return { next() { return { done: false }; }, return() { throw 2; } }; } }; var r; try { for (var x of o) throw 1; } catch (e) { r = e; }",
            "1",
        ),
        // A `break` reports a throw from `return`.
        (
            "var o = { [Symbol.iterator]() { return { next() { return { done: false }; }, return() { throw 2; } }; } }; var r; try { for (var x of o) break; } catch (e) { r = e; }",
            "2",
        ),
        // `return` giving a non-object on a normal exit is a TypeError.
        (
            "var o = { [Symbol.iterator]() { return { next() { return { done: false }; }, return() { return 1; } }; } }; var r; try { for (var x of o) break; } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
    ])
}

#[test]
fn array_and_string_iterators() -> Result<(), String> {
    check(&[
        (
            "var r = Array.prototype[Symbol.iterator] === Array.prototype.values;",
            "true",
        ),
        (
            "var it = [7][Symbol.iterator](); var a = it.next(); var b = it.next(); var r = a.value + ',' + a.done + ',' + b.value + ',' + b.done;",
            "7,false,undefined,true",
        ),
        // Done stays done (§23.1.5.1: the closure has returned).
        (
            "var a = []; var it = a.values(); it.next(); a.push(1); var r = it.next().done;",
            "true",
        ),
        (
            "var it = [].values(); var r = it[Symbol.iterator]() === it;",
            "true",
        ),
        (
            "var r = Object.getPrototypeOf(Object.getPrototypeOf([].values())) === Object.getPrototypeOf(Object.getPrototypeOf(''[Symbol.iterator]()));",
            "true",
        ),
        (
            "var r = Object.prototype.toString.call([].values());",
            "[object Array Iterator]",
        ),
        (
            "var r = Object.prototype.toString.call(''[Symbol.iterator]());",
            "[object String Iterator]",
        ),
        (
            "var r; try { [].values().next.call({}); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        // Generic over array-likes.
        (
            "var r = [...Array.prototype.values.call({ length: 2, 0: 'a', 1: 'b' })].join();",
            "a,b",
        ),
        ("var r = [...[5, 6].entries()].join('|');", "0,5|1,6"),
        ("var r = Array.from('abc').join();", "a,b,c"),
        (
            "var r = Array.from({ length: 3 }, function (v, i) { return i * 2; }).join();",
            "0,2,4",
        ),
        (
            "var r = Array.from([1, 2], function (v) { return v + this.d; }, { d: 10 }).join();",
            "11,12",
        ),
        ("var r = Array.isArray(Array.from([]));", "true"),
        (
            "function C() {} var r = Array.from.call(C, [1]) instanceof C;",
            "true",
        ),
    ])
}

#[test]
fn for_in() -> Result<(), String> {
    check(&[
        ("var r = ''; for (var k in { a: 1, b: 2 }) r += k;", "ab"),
        ("var r = ''; for (var k in [5, 6]) r += k;", "01"),
        ("var r = ''; for (var k in 'xy') r += k;", "01"),
        (
            "var r = 0; for (var k in null) r++; for (var k in undefined) r++;",
            "0",
        ),
        // Inherited enumerable keys, each once; shadowed ones not twice.
        (
            "var p = { a: 1, b: 2 }; var o = Object.create(p); o.b = 3; o.c = 4; var r = ''; for (var k in o) r += k;",
            "bca",
        ),
        // A key deleted before it is reached is not visited.
        (
            "var o = { a: 1, b: 2 }; var r = ''; for (var k in o) { delete o.b; r += k; }",
            "a",
        ),
        // Non-enumerable built-ins are not visited.
        ("var r = ''; for (var k in []) r += k;", ""),
    ])
}
