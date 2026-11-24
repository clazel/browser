//! Tests of `String`, `Number` and `Boolean` (§22.1†, §21.1†, §20.3†) and
//! the rest of `Array.prototype`, as small scripts run with the built-ins
//! installed. Each expectation is what ECMA-262 says, written by hand; the
//! result is the global `r` as its ToString. No files are read, so these
//! run under Miri too (with every eighth case, as the other built-in tests
//! do).

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

/// `r` is true when `f` throws an instance of `ctor`.
fn throws(ctor: &str, body: &str) -> String {
    format!("var r; try {{ {body}; r = 'no throw'; }} catch (e) {{ r = e instanceof {ctor}; }}")
}

#[test]
fn string_statics() -> Result<(), String> {
    let t1 = throws("RangeError", "String.fromCodePoint(1.5)");
    let t2 = throws("RangeError", "String.fromCodePoint(0x110000)");
    check(&[
        ("var r = String.fromCharCode(104, 105, 65536 + 33);", "hi!"),
        ("var r = String.fromCodePoint(0x1F600).length;", "2"),
        (
            "var r = String.fromCodePoint(0x1F600).codePointAt(0);",
            "128512",
        ),
        ("var r = String.fromCodePoint(97, 98);", "ab"),
        (&t1, "true"),
        (&t2, "true"),
        (
            "var r = String.raw({ raw: ['a', 'b', 'c'] }, 1, 2, 3);",
            "a1b2c",
        ),
        ("var r = String.raw({ raw: { length: 0 } }, 1);", ""),
        (
            "var r = String.raw({ raw: ['x', 'y', 'z'] }, '-', '+');",
            "x-y+z",
        ),
    ])
}

#[test]
fn string_search_methods() -> Result<(), String> {
    let t = throws("TypeError", "'a'.startsWith({ [Symbol.match]: true })");
    check(&[
        ("var r = 'abcabc'.lastIndexOf('c');", "5"),
        ("var r = 'abcabc'.lastIndexOf('c', 4);", "2"),
        ("var r = 'abc'.lastIndexOf('');", "3"),
        ("var r = 'abc'.lastIndexOf('', 1);", "1"),
        ("var r = 'abc'.lastIndexOf('abcd');", "-1"),
        ("var r = 'abc'.lastIndexOf('a', -Infinity);", "0"),
        ("var r = 'hello'.includes('ell');", "true"),
        ("var r = 'hello'.includes('ell', 2);", "false"),
        ("var r = 'hello'.startsWith('he');", "true"),
        ("var r = 'hello'.startsWith('ll', 2);", "true"),
        ("var r = 'hello'.endsWith('lo');", "true"),
        ("var r = 'hello'.endsWith('el', 3);", "true"),
        ("var r = 'hello'.endsWith('hello!');", "false"),
        ("var r = ''.startsWith('');", "true"),
        (&t, "true"),
        // An object with @@match false is not a RegExp (§7.2.8 step 3).
        (
            "var o = { [Symbol.match]: false, toString() { return 'a'; } }; var r = 'abc'.startsWith(o);",
            "true",
        ),
        (
            "var r = 'abc'.at(-1) + 'abc'.at(0) + 'abc'.at(5);",
            "caundefined",
        ),
        ("var r = 'a\\uD83D\\uDE00'.codePointAt(1);", "128512"),
        ("var r = 'a\\uD83D\\uDE00'.codePointAt(2);", "56832"),
        ("var r = 'a'.codePointAt(1);", "undefined"),
        ("var r = 'a'.concat(1, null, [2, 3]);", "a1null2,3"),
        (
            "var r = 'b'.localeCompare('a') + 'a'.localeCompare('a');",
            "1",
        ),
    ])
}

#[test]
fn string_transformations() -> Result<(), String> {
    let rep_inf = throws("RangeError", "'a'.repeat(Infinity)");
    let rep_neg = throws("RangeError", "'a'.repeat(-1)");
    let too_long = throws("RangeError", "'ab'.repeat(2 ** 30)");
    check(&[
        ("var r = 'abc'.padStart(6, '12');", "121abc"),
        ("var r = 'abc'.padEnd(6, '12');", "abc121"),
        ("var r = 'abc'.padStart(5);", "  abc"),
        ("var r = 'abc'.padStart(5, '');", "abc"),
        ("var r = 'abc'.padEnd(2, 'x');", "abc"),
        ("var r = 'ab'.repeat(3);", "ababab"),
        ("var r = 'ab'.repeat(0);", ""),
        (&rep_inf, "true"),
        (&rep_neg, "true"),
        (&too_long, "true"),
        ("var r = '  a b \\n\\t'.trim() + '|';", "a b|"),
        ("var r = '\\uFEFF\\u00A0x\\u3000'.trim().length;", "1"),
        ("var r = '  a  '.trimStart() + '|';", "a  |"),
        ("var r = '  a  '.trimEnd() + '|';", "  a|"),
        (
            "var r = String.prototype.trimLeft === String.prototype.trimStart && String.prototype.trimRight === String.prototype.trimEnd;",
            "true",
        ),
        (
            "var r = 'AbC'.toLowerCase() + 'AbC'.toUpperCase();",
            "abcABC",
        ),
        // SpecialCasing: ß uppercases to SS; final sigma lowercases to ς.
        ("var r = 'ß'.toUpperCase();", "SS"),
        ("var r = 'ΑΣ'.toLowerCase();", "ας"),
        ("var r = 'İ'.toLowerCase().length;", "2"),
        ("var r = 'a\\uD800b'.toUpperCase() === 'A\\uD800B';", "true"),
        ("var r = 'abcdef'.substr(2, 3);", "cde"),
        ("var r = 'abcdef'.substr(-2);", "ef"),
        ("var r = 'abc'.substr(1, -1);", ""),
        (
            "var r = 'a\\uD800'.isWellFormed() + ',' + 'ab'.isWellFormed();",
            "false,true",
        ),
        (
            "var r = 'a\\uDC00b'.toWellFormed() === 'a\\uFFFDb';",
            "true",
        ),
    ])
}

#[test]
fn string_replace_and_split() -> Result<(), String> {
    check(&[
        ("var r = 'aXbX'.replace('X', '-');", "a-bX"),
        ("var r = 'aXbX'.replaceAll('X', '-');", "a-b-"),
        ("var r = 'abc'.replace('', '-');", "-abc"),
        ("var r = 'abc'.replaceAll('', '-');", "-a-b-c-"),
        ("var r = 'abc'.replace('z', '-');", "abc"),
        // GetSubstitution: $$, $&, $`, $', and $1 with no captures.
        ("var r = 'abc'.replace('b', '[$&]');", "a[b]c"),
        ("var r = 'abc'.replace('b', '[$`]');", "a[a]c"),
        ("var r = 'abc'.replace('b', \"[$']\");", "a[c]c"),
        ("var r = 'abc'.replace('b', '$$');", "a$c"),
        ("var r = 'abc'.replace('b', '$1$<x>$');", "a$1$<x>$c"),
        (
            "var r = 'abcb'.replace('b', function (m, p, s) { return '(' + m + p + s.length + ')'; });",
            "a(b14)cb",
        ),
        (
            "var r = 'xbxb'.replaceAll('b', function (m, p) { return p; });",
            "x1x3",
        ),
        // A pattern with @@replace is called (§22.1.3.19 step 2).
        (
            "var p = { [Symbol.replace](s, v) { return s + v; } }; var r = 'a'.replace(p, 'b');",
            "ab",
        ),
        ("var r = 'a,b,,c'.split(',').length;", "4"),
        ("var r = 'a,b,c'.split(',', 2).join('|');", "a|b"),
        ("var r = 'abc'.split('').join('|');", "a|b|c"),
        ("var r = 'abc'.split('', 2).join('|');", "a|b"),
        (
            "var r = 'abc'.split().length + ',' + 'abc'.split()[0];",
            "1,abc",
        ),
        ("var r = ''.split(',').length;", "1"),
        ("var r = ''.split('').length;", "0"),
        ("var r = 'abc'.split('b', 0).length;", "0"),
        (
            "var p = { [Symbol.split](s, l) { return [s, l]; } }; var r = 'q'.split(p, 3).join();",
            "q,3",
        ),
        (
            "var p = { [Symbol.search](s) { return 7; } }; var r = 'q'.search(p);",
            "7",
        ),
        (
            "var p = { [Symbol.match](s) { return 'm' + s; } }; var r = 'q'.match(p);",
            "mq",
        ),
    ])
}

#[test]
fn number_and_boolean() -> Result<(), String> {
    let rp = throws("RangeError", "(1).toPrecision(0)");
    let re = throws("RangeError", "(1).toExponential(101)");
    check(&[
        ("var r = (123.456).toPrecision(4);", "123.5"),
        ("var r = (0.000123).toPrecision(2);", "0.00012"),
        ("var r = (123456).toPrecision(2);", "1.2e+5"),
        ("var r = (1.5).toPrecision();", "1.5"),
        ("var r = NaN.toPrecision(3);", "NaN"),
        (&rp, "true"),
        ("var r = (123.456).toExponential(2);", "1.23e+2"),
        ("var r = (0).toExponential();", "0e+0"),
        ("var r = (-1.5).toExponential(3);", "-1.500e+0"),
        ("var r = Infinity.toExponential(2);", "Infinity"),
        (&re, "true"),
        ("var r = (1234.5).toLocaleString();", "1234.5"),
        ("var r = Number.parseInt === parseInt;", "true"),
        ("var r = new Number(5) + 1;", "6"),
        ("var r = (255).toString(16);", "ff"),
        ("var r = (1e21).toFixed(2);", "1e+21"),
        (
            "var r = true.toString() + new Boolean(false).valueOf();",
            "truefalse",
        ),
        ("var r = typeof new Boolean(false);", "object"),
        ("var r = !!new Boolean(false);", "true"),
    ])
}

#[test]
fn more_array_methods() -> Result<(), String> {
    let with_range = throws("RangeError", "[1].with(1, 0)");
    check(&[
        ("var r = [1, 2, 3].at(-1);", "3"),
        ("var r = [1, 2, 3].at(3);", "undefined"),
        (
            "var r = [1, 2, 3, 4, 5].copyWithin(0, 3).join();",
            "4,5,3,4,5",
        ),
        (
            "var r = [1, 2, 3, 4, 5].copyWithin(1, 0, 3).join();",
            "1,1,2,3,5",
        ),
        (
            "var r = [1, 2, 3, 4, 5].copyWithin(-2, -3, -1).join();",
            "1,2,3,3,4",
        ),
        ("var r = [1, [2, [3, [4]]]].flat().length;", "3"),
        (
            "var r = [1, [2, [3, [4]]]].flat(Infinity).join();",
            "1,2,3,4",
        ),
        ("var r = [1, , [2, , 3]].flat().length;", "3"),
        (
            "var r = [1, 2].flatMap(function (x) { return [x, x * 10]; }).join();",
            "1,10,2,20",
        ),
        (
            "var r = [1, 2].flatMap(function (x) { return [[x]]; })[0].length;",
            "1",
        ),
        (
            "var r = [1, 2, 3, 4].findLast(function (x) { return x % 2; });",
            "3",
        ),
        (
            "var r = [1, 2, 3, 4].findLastIndex(function (x) { return x > 5; });",
            "-1",
        ),
        (
            "var a = [1, 2, 3]; var b = a.toReversed(); var r = a.join() + '|' + b.join();",
            "1,2,3|3,2,1",
        ),
        (
            "var a = [3, 1, 2]; var b = a.toSorted(); var r = a.join() + '|' + b.join();",
            "3,1,2|1,2,3",
        ),
        (
            "var r = [, 1].toSorted().length + ',' + (0 in [, 1].toSorted());",
            "2,true",
        ),
        (
            "var r = [1, 2, 3].toSpliced(1, 1, 'a', 'b').join();",
            "1,a,b,3",
        ),
        ("var r = [1, 2, 3].toSpliced(1).join();", "1"),
        ("var r = [1, 2, 3].toSpliced().join();", "1,2,3"),
        ("var r = [1, 2, 3].with(-1, 9).join();", "1,2,9"),
        (&with_range, "true"),
        ("var r = [1, 'a', null].toLocaleString();", "1,a,"),
        (
            "var u = Array.prototype[Symbol.unscopables]; var r = Object.getPrototypeOf(u) === null && u.flat && !u.map;",
            "true",
        ),
        // @@isConcatSpreadable (§23.1.3.2.1).
        (
            "var o = { length: 2, 0: 'x', 1: 'y', [Symbol.isConcatSpreadable]: true }; var r = [1].concat(o).join();",
            "1,x,y",
        ),
        (
            "var a = [1, 2]; a[Symbol.isConcatSpreadable] = false; var r = [].concat(a).length;",
            "1",
        ),
        // @@species (§10.4.2.3 step 4).
        (
            "var a = [1, 2]; a.constructor = { [Symbol.species]: function (n) { return { length: 0, tag: 's' }; } }; var r = a.map(function (x) { return x; }).tag;",
            "s",
        ),
        (
            "var a = [1]; a.constructor = { [Symbol.species]: null }; var r = Array.isArray(a.map(function (x) { return x; }));",
            "true",
        ),
    ])
}
