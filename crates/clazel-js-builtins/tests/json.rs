//! Tests of `JSON.parse` and `JSON.stringify`: scripts run with the built-ins
//! installed, each expectation what ECMA-262 §25.5† says, written by hand.
//! The result is the global `r` as its ToString. No files are read, so these
//! run under Miri too (every fourth case).

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Config, Vm};

fn r_of(src: &str) -> Result<String, String> {
    let c: Vec<u32> = src.chars().map(u32::from).collect();
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let cfg = if cfg!(miri) {
        Config {
            region_slots: 1 << 12,
            heap_cells: 1 << 14,
        }
    } else {
        Config::default()
    };
    let mut vm = Vm::new(cfg).map_err(|e| format!("{e:?}"))?;
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
    let stride = if cfg!(miri) { 4 } else { 1 };
    for (src, want) in cases.iter().step_by(stride) {
        let got = r_of(src)?;
        if got != *want {
            return Err(format!("{src}: expected {want:?}, got {got:?}"));
        }
    }
    Ok(())
}

#[test]
fn json_parse() -> Result<(), String> {
    check(&[
        ("var r = JSON.parse('1') + JSON.parse(' 2.5e1 ');", "26"),
        ("var r = JSON.parse('null') === null;", "true"),
        (
            "var r = JSON.parse('true') && !JSON.parse('false');",
            "true",
        ),
        ("var r = JSON.parse('\"a\\\\nb\"').length;", "3"),
        ("var r = JSON.parse('\"\\\\u0041\"');", "A"),
        ("var r = JSON.parse('[1,2,[3]]').join();", "1,2,3"),
        ("var r = Array.isArray(JSON.parse('[]'));", "true"),
        (
            "var o = JSON.parse('{\"a\":1,\"b\":{\"c\":2}}'); var r = o.a + o.b.c;",
            "3",
        ),
        // A duplicate name takes the later value.
        ("var r = JSON.parse('{\"a\":1,\"a\":2}').a;", "2"),
        // Numbers: -0 and big exponents.
        ("var r = 1 / JSON.parse('-0');", "-Infinity"),
        ("var r = JSON.parse('1e400');", "Infinity"),
        // SyntaxErrors.
        (
            "var r; try { JSON.parse('{a:1}'); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { JSON.parse(''); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { JSON.parse('[1,]'); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { JSON.parse('01'); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { JSON.parse(\"'a'\"); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var r; try { JSON.parse(undefined); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        // The nesting bound: 600 levels is a SyntaxError, 100 is fine.
        (
            "var s = ''; for (var i = 0; i < 600; i++) s += '['; for (var i = 0; i < 600; i++) s += ']'; var r; try { JSON.parse(s); } catch (e) { r = e.name; }",
            "SyntaxError",
        ),
        (
            "var s = ''; for (var i = 0; i < 100; i++) s += '['; for (var i = 0; i < 100; i++) s += ']'; var r = Array.isArray(JSON.parse(s));",
            "true",
        ),
        // The deepest text the parser takes, revived.
        (
            "var s = ''; for (var i = 0; i < 500; i++) s += '['; for (var i = 0; i < 500; i++) s += ']'; var n = 0; JSON.parse(s, function (k, v) { n++; return v; }); var r = n;",
            "500",
        ),
        // The reviver, §25.5.1.1: bottom-up, holder as this, deletes on undefined.
        (
            "var log = ''; JSON.parse('{\"a\":[1,2],\"b\":3}', function (k, v) { log += k + ';'; return v; }); var r = log;",
            "0;1;a;b;;",
        ),
        (
            "var r = JSON.parse('[1,2,3]', function (k, v) { return typeof v === 'number' ? v * 2 : v; }).join();",
            "2,4,6",
        ),
        (
            "var o = JSON.parse('{\"a\":1,\"b\":2}', function (k, v) { return k === 'a' ? undefined : v; }); var r = ('a' in o) + ',' + o.b;",
            "false,2",
        ),
        (
            "var holder; JSON.parse('{\"x\":1}', function (k, v) { if (k === 'x') holder = this; return v; }); var r = holder.x;",
            "1",
        ),
        (
            "var r = JSON.parse('5', function (k, v) { return k === '' ? v + 1 : v; });",
            "6",
        ),
        ("var r = JSON.parse('[1]', 5).length;", "1"),
    ])
}

#[test]
fn json_stringify() -> Result<(), String> {
    check(&[
        (
            "var r = JSON.stringify(1) + JSON.stringify('a\"b') + JSON.stringify(null);",
            "1\"a\\\"b\"null",
        ),
        (
            "var r = JSON.stringify(true) + JSON.stringify(false);",
            "truefalse",
        ),
        (
            "var r = JSON.stringify(NaN) + JSON.stringify(Infinity) + JSON.stringify(-0);",
            "nullnull0",
        ),
        ("var r = JSON.stringify(undefined);", "undefined"),
        ("var r = JSON.stringify(function () {});", "undefined"),
        (
            "var r = JSON.stringify([1, 'a', null, undefined, function () {}]);",
            "[1,\"a\",null,null,null]",
        ),
        (
            "var r = JSON.stringify({ a: 1, b: undefined, c: function () {}, d: [2] });",
            "{\"a\":1,\"d\":[2]}",
        ),
        ("var r = JSON.stringify({});", "{}"),
        ("var r = JSON.stringify([]);", "[]"),
        (
            "var r = JSON.stringify({ 2: 'x', 1: 'y', b: 0 });",
            "{\"1\":\"y\",\"2\":\"x\",\"b\":0}",
        ),
        // Wrapper objects unwrap.
        (
            "var r = JSON.stringify([new Number(3), new String('s'), new Boolean(false)]);",
            "[3,\"s\",false]",
        ),
        // Quoting: control characters and lone surrogates.
        (
            "var r = JSON.stringify('\\u0001\\n\\ud800');",
            "\"\\u0001\\n\\ud800\"",
        ),
        // toJSON, §25.5.2.2 step 2.
        (
            "var r = JSON.stringify({ toJSON: function (k) { return 'k=' + k; } });",
            "\"k=\"",
        ),
        (
            "var r = JSON.stringify({ a: { toJSON: function (k) { return k + '!'; } } });",
            "{\"a\":\"a!\"}",
        ),
        // The replacer function: holder as this, key and value.
        (
            "var r = JSON.stringify({ a: 1, b: 2 }, function (k, v) { return k === 'a' ? undefined : v; });",
            "{\"b\":2}",
        ),
        (
            "var r = JSON.stringify(1, function (k, v) { return k === '' ? v + 1 : v; });",
            "2",
        ),
        // The replacer array: a property list, in its order, no duplicates.
        (
            "var r = JSON.stringify({ a: 1, b: 2, c: 3 }, ['c', 'a', 'c', 5]);",
            "{\"c\":3,\"a\":1}",
        ),
        (
            "var r = JSON.stringify({ 1: 'x', a: 'y' }, [1, new String('a')]);",
            "{\"1\":\"x\",\"a\":\"y\"}",
        ),
        // The gap: a number (at most 10), a string (first 10 units), wrappers.
        (
            "var r = JSON.stringify({ a: [1, { b: 2 }] }, null, 2);",
            "{\n  \"a\": [\n    1,\n    {\n      \"b\": 2\n    }\n  ]\n}",
        ),
        ("var r = JSON.stringify([1], null, '--');", "[\n--1\n]"),
        (
            "var r = JSON.stringify([1], null, 'abcdefghijklmnop');",
            "[\nabcdefghij1\n]",
        ),
        ("var r = JSON.stringify([1], null, 20).length;", "15"),
        ("var r = JSON.stringify([1], null, 0.9);", "[1]"),
        (
            "var r = JSON.stringify({ a: 1 }, null, new Number(1));",
            "{\n \"a\": 1\n}",
        ),
        (
            "var r = JSON.stringify([], null, 2) + JSON.stringify({}, null, 2);",
            "[]{}",
        ),
        // Cycles are a TypeError, §25.5.2.4 step 1.
        (
            "var a = {}; a.self = a; var r; try { JSON.stringify(a); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        (
            "var a = []; a[0] = [a]; var r; try { JSON.stringify(a); } catch (e) { r = e.name; }",
            "TypeError",
        ),
        // The same object twice (not a cycle) is fine.
        ("var x = {}; var r = JSON.stringify([x, x]);", "[{},{}]"),
        // Depth past the bound is a RangeError.
        (
            "var a = []; for (var i = 0; i < 200; i++) a = [a]; var r; try { JSON.stringify(a); } catch (e) { r = e.name; }",
            "RangeError",
        ),
        // Round trip.
        (
            "var s = '{\"a\":[1,2,{\"b\":null}],\"c\":\"x\"}'; var r = JSON.stringify(JSON.parse(s)) === s;",
            "true",
        ),
    ])
}
