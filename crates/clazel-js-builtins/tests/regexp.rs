//! Tests of `RegExp` (§22.2†) and the String methods that use it
//! (§22.1.3†), as small scripts run with the built-ins installed. Each
//! expectation is what ECMA-262 says, written by hand; the result is the
//! global `r` as its ToString. No files are read, so these run under Miri too
//! (every eighth case).

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
            heap_cells: 1 << 15,
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

/// `r` is true when the body throws an instance of `ctor`.
fn throws(ctor: &str, body: &str) -> String {
    format!("var r; try {{ {body}; r = 'no throw'; }} catch (e) {{ r = e instanceof {ctor}; }}")
}

#[test]
fn literals_and_the_constructor() -> Result<(), String> {
    let bad_flags = throws("SyntaxError", "new RegExp('a', 'gg')");
    let bad_flag = throws("SyntaxError", "new RegExp('a', 'x')");
    let bad_pattern = throws("SyntaxError", "new RegExp('(')");
    let uv = throws("SyntaxError", "new RegExp('a', 'uv')");
    check(&[
        ("var r = /ab+c/.test('xabbbcx');", "true"),
        ("var r = /ab+c/.test('ac');", "false"),
        ("var r = typeof /a/;", "object"),
        ("var r = /a/ instanceof RegExp;", "true"),
        (
            "var r = new RegExp('a+', 'g').source + new RegExp('a+', 'gi').flags;",
            "a+gi",
        ),
        ("var r = /a\\/b/.source;", "a\\/b"),
        ("var r = new RegExp('/').source;", "\\/"),
        ("var r = new RegExp('[/]').source;", "[/]"),
        ("var r = new RegExp('').source;", "(?:)"),
        ("var r = new RegExp('\\n').source;", "\\n"),
        ("var r = String(/a(b)/gimsuy);", "/a(b)/gimsuy"),
        ("var r = /a/dgimsy.flags;", "dgimsy"),
        (
            "var r = /a/v.unicodeSets + ':' + /a/.unicode;",
            "true:false",
        ),
        (
            "var r = /a/g.global + ':' + /a/.global + ':' + /a/y.sticky;",
            "true:false:true",
        ),
        ("var r = /a/.lastIndex;", "0"),
        // RegExp(pattern) with a RegExp and no flags returns it.
        ("var a = /x/g; var r = RegExp(a) === a;", "true"),
        ("var a = /x/g; var r = new RegExp(a) === a;", "false"),
        (
            "var a = /x/g; var r = new RegExp(a).flags + new RegExp(a, 'i').flags;",
            "gi",
        ),
        ("var r = RegExp('a', 'g').global;", "true"),
        ("var r = RegExp.length + ':' + RegExp.name;", "2:RegExp"),
        ("var r = RegExp.prototype.constructor === RegExp;", "true"),
        ("var r = RegExp[Symbol.species] === RegExp;", "true"),
        (&bad_flags, "true"),
        (&bad_flag, "true"),
        (&bad_pattern, "true"),
        (&uv, "true"),
        // A literal makes a new object each time it runs.
        (
            "function f() { return /a/; } var r = (f() === f()) + ':' + (f().source === f().source);",
            "false:true",
        ),
        (
            "var r = Object.prototype.toString.call(/a/);",
            "[object RegExp]",
        ),
    ])
}

#[test]
fn exec_and_test() -> Result<(), String> {
    let nonmatch = throws("TypeError", "RegExp.prototype.exec.call({}, 'a')");
    check(&[
        (
            "var m = /b(c)(d)?/.exec('abcx'); var r = m.index + ':' + m[0] + ':' + m[1] + ':' + m[2] + ':' + m.length + ':' + m.input;",
            "1:bc:c:undefined:3:abcx",
        ),
        ("var r = /z/.exec('abc');", "null"),
        ("var r = Array.isArray(/a/.exec('a'));", "true"),
        // lastIndex with g
        (
            "var re = /a/g; var s = 'aXa'; var r = re.test(s) + ':' + re.lastIndex + ':' + re.test(s) + ':' + re.lastIndex + ':' + re.test(s) + ':' + re.lastIndex;",
            "true:1:true:3:false:0",
        ),
        // lastIndex is ignored without g or y
        (
            "var re = /a/; re.lastIndex = 5; var r = re.test('a') + ':' + re.lastIndex;",
            "true:5",
        ),
        // sticky
        (
            "var re = /a/y; var r = re.test('ba') + ':' + re.lastIndex; re.lastIndex = 1; r += ':' + re.test('ba') + ':' + re.lastIndex;",
            "false:0:true:2",
        ),
        // lastIndex beyond the string
        (
            "var re = /a/g; re.lastIndex = 10; var r = re.exec('a') + ':' + re.lastIndex;",
            "null:0",
        ),
        // named groups
        (
            "var m = /(?<y>\\d{4})-(?<m>\\d\\d)/.exec('on 2024-05'); var r = m.groups.y + m.groups.m + ':' + Object.getPrototypeOf(m.groups);",
            "202405:null",
        ),
        ("var r = /a/.exec('a').groups;", "undefined"),
        // d flag: indices
        (
            "var m = /b(c)?(?<n>x)?/d.exec('abc'); var r = m.indices[0] + ':' + m.indices[1] + ':' + m.indices[2] + ':' + m.indices.groups.n;",
            "1,3:2,3:undefined:undefined",
        ),
        ("var r = /a/.exec('a').indices;", "undefined"),
        // case-insensitive, multiline, dotAll
        ("var r = /ABC/i.test('xabcx');", "true"),
        (
            "var r = /^b/m.test('a\\nb') + ':' + /^b/.test('a\\nb');",
            "true:false",
        ),
        (
            "var r = /a.b/s.test('a\\nb') + ':' + /a.b/.test('a\\nb');",
            "true:false",
        ),
        // unicode mode
        (
            "var r = /^.$/u.test('\\u{1F600}') + ':' + /^.$/.test('\\u{1F600}');",
            "true:false",
        ),
        ("var r = /\\u{1F600}/u.test('\\u{1F600}');", "true"),
        ("var r = /\\p{Lu}/u.test('aB');", "true"),
        // lookbehind, backreferences
        (
            "var r = /(?<=a)b/.exec('ab')[0] + ':' + /(a)\\1/.test('aa');",
            "b:true",
        ),
        // exec on a non-RegExp is a TypeError
        (&nonmatch, "true"),
        // exec coerces its argument
        ("var r = /1/.exec(1)[0];", "1"),
        ("var r = /undefined/.test();", "true"),
        // a user exec override is used by test
        (
            "var re = /a/; re.exec = function () { return null; }; var r = re.test('a');",
            "false",
        ),
        (
            "var re = /a/; re.exec = function () { return 5; }; try { re.test('a'); } catch (e) { var r = e instanceof TypeError; }",
            "true",
        ),
    ])
}

#[test]
fn string_match_and_match_all() -> Result<(), String> {
    check(&[
        ("var r = 'abcabc'.match(/b/).index;", "1"),
        ("var r = 'abcabc'.match(/b/g).join();", "b,b"),
        ("var r = 'abc'.match(/x/g);", "null"),
        ("var r = 'abc'.match(/x/);", "null"),
        ("var r = 'aXbxc'.match(/x/gi).length;", "2"),
        // match with a string makes a RegExp
        ("var r = 'a.c'.match('.')[0];", "a"),
        ("var r = 'abc'.match()[0] === '';", "true"),
        // empty matches advance
        ("var r = 'abc'.match(/(?:)/g).length;", "4"),
        ("var r = '\\u{1F600}'.match(/(?:)/gu).length;", "2"),
        ("var r = '\\u{1F600}'.match(/(?:)/g).length;", "3"),
        // matchAll
        (
            "var r = Array.from('a1b2'.matchAll(/\\d/g)).map(function (m) { return m[0] + m.index; }).join();",
            "11,23",
        ),
        (
            "var it = 'abc'.matchAll(/./g); var r = Object.prototype.toString.call(it) + (it[Symbol.iterator]() === it);",
            "[object RegExp String Iterator]true",
        ),
        (
            "try { 'a'.matchAll(/a/); } catch (e) { var r = e instanceof TypeError; }",
            "true",
        ),
        ("var r = Array.from('aa'.matchAll('a')).length;", "2"),
    ])
}

#[test]
fn string_search_and_split() -> Result<(), String> {
    check(&[
        // search
        (
            "var r = 'abc'.search(/c/) + ':' + 'abc'.search(/x/) + ':' + 'abc'.search('b');",
            "2:-1:1",
        ),
        (
            "var re = /b/g; re.lastIndex = 2; var r = 'abc'.search(re) + ':' + re.lastIndex;",
            "1:2",
        ),
        // split
        ("var r = 'a1b22c'.split(/\\d+/).join('|');", "a|b|c"),
        ("var r = 'a1b2c'.split(/(\\d)/).join('|');", "a|1|b|2|c"),
        ("var r = 'abc'.split(/(?:)/).join('|');", "a|b|c"),
        ("var r = 'abc'.split(/b/, 1).join('|');", "a"),
        (
            "var r = ''.split(/x/).length + ':' + ''.split(/(?:)/).length;",
            "1:0",
        ),
        ("var r = 'abc'.split(/x/).join('|');", "abc"),
        ("var r = 'test'.split(/(?:)/, 2).join('|');", "t|e"),
        ("var r = 'a b  c'.split(/\\s/).length;", "4"),
        (
            "var r = '\\u{1F600}x'.split(/(?:)/u).length + ':' + '\\u{1F600}x'.split(/(?:)/).length;",
            "2:3",
        ),
    ])
}

#[test]
fn string_replace_and_replace_all() -> Result<(), String> {
    check(&[
        // replace
        ("var r = 'abc'.replace(/b/, 'X');", "aXc"),
        ("var r = 'abab'.replace(/b/g, 'X');", "aXaX"),
        ("var r = 'abc'.replace(/(b)/, '[$1]');", "a[b]c"),
        ("var r = 'abc'.replace(/b/, \"[$`|$&|$']\");", "a[a|b|c]c"),
        ("var r = 'abc'.replace(/b/, '$$');", "a$c"),
        ("var r = 'abc'.replace(/(b)/, '$2$0$01');", "a$2$0bc"),
        ("var r = 'abc'.replace(/(?<x>b)/, '[$<x>]');", "a[b]c"),
        ("var r = 'abc'.replace(/(b)/, '[$<x>]');", "a[$<x>]c"),
        ("var r = 'abc'.replace(/(?<x>b)/, '[$<y>]');", "a[]c"),
        (
            "var r = 'abc'.replace(/(b)(x)?/, function (m, p1, p2, off, s) { return [m, p1, p2, off, s].join('-'); });",
            "ab-b--1-abcc",
        ),
        (
            "var r = 'abc'.replace(/(?<n>b)/, function (m, p1, off, str, groups) { return typeof groups + typeof str; });",
            "aobjectstringc",
        ),
        (
            "var r = 'aaa'.replace(/a/g, function (m, off) { return off; });",
            "012",
        ),
        ("var r = 'abc'.replace(/x/, 'y');", "abc"),
        ("var r = 'abc'.replace(/(?:)/g, '-');", "-a-b-c-"),
        (
            "var r = '\\u{1F600}'.replace(/(?:)/gu, '-');",
            "-\\u{1F600}-".replace("\\u{1F600}", "\u{1F600}").as_str(),
        ),
        ("var r = 'ab'.replace(/(?:)/y, '-');", "-ab"),
        // replaceAll
        ("var r = 'abab'.replaceAll(/b/g, 'X');", "aXaX"),
        (
            "try { 'a'.replaceAll(/a/, 'b'); } catch (e) { var r = e instanceof TypeError; }",
            "true",
        ),
        ("var r = 'a.b.c'.replaceAll('.', '-');", "a-b-c"),
        // lastIndex is reset by global replace
        (
            "var re = /a/g; re.lastIndex = 3; var r = 'aa'.replace(re, 'b') + ':' + re.lastIndex;",
            "bb:0",
        ),
    ])
}

#[test]
fn symbol_methods_and_protocol() -> Result<(), String> {
    check(&[
        (
            "var r = typeof RegExp.prototype[Symbol.replace];",
            "function",
        ),
        (
            "var r = RegExp.prototype[Symbol.replace].name;",
            "[Symbol.replace]",
        ),
        (
            "var re = /b/; var r = re[Symbol.match]('abc')[0] + re[Symbol.search]('abc') + re[Symbol.split]('abc').join();",
            "b1a,c",
        ),
        ("var r = /a/[Symbol.replace]('aaa', 'x');", "xaa"),
        // IsRegExp: a regex is rejected by startsWith, an object with a falsy @@match is not
        (
            "try { 'a'.startsWith(/a/); } catch (e) { var r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var re = /a/; re[Symbol.match] = false; var r = 'a/a/'.includes(re);",
            "true",
        ),
        // species: split uses a constructor from `constructor[@@species]`
        (
            "var re = /b/; var called = 0; function C(p, f) { called++; return new RegExp(p, f); } C[Symbol.species] = C; re.constructor = C; var r = 'abc'.split(re).join() + called;",
            "a,c1",
        ),
        // toString is generic
        (
            "var r = RegExp.prototype.toString.call({ source: 'a', flags: 'g' });",
            "/a/g",
        ),
        // compile (Annex B)
        (
            "var re = /a/g; re.compile('b', 'i'); var r = re.source + re.flags + re.test('B');",
            "bitrue",
        ),
        // lastIndex is own and not configurable
        (
            "var d = Object.getOwnPropertyDescriptor ? 1 : 0; var r = Object.keys(/a/g).length;",
            "0",
        ),
        // RegExp.escape
        ("var r = RegExp.escape('a.b');", "\\x61\\.b"),
        ("var r = RegExp.escape('1+1=2');", "\\x31\\+1\\x3d2"),
        ("var r = RegExp.escape(' -');", "\\x20\\x2d"),
        ("var r = RegExp.escape('\\n/');", "\\n\\/"),
        (
            "try { RegExp.escape(1); } catch (e) { var r = e instanceof TypeError; }",
            "true",
        ),
    ])
}

#[test]
fn limits_and_hostile_patterns() -> Result<(), String> {
    // A match that needs more than the backtrack stack's bound ends in a
    // RangeError (phase-7.md item 7.10's listed deviation), not in a crash.
    if cfg!(miri) {
        return Ok(());
    }
    check(&[(
        "var r; try { /^(?:a|b)*c/.exec('ab'.repeat(700000)); r = 'done'; } catch (e) { r = e instanceof RangeError; }",
        "true",
    )])?;
    // Catastrophic backtracking runs until the host's termination flag, and
    // that ends it.
    let src = "/(a*)*b/.exec('aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa');";
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "does not parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{e}"))?;
    let mut vm = Vm::new(Config::default()).map_err(|e| format!("{e:?}"))?;
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    let t = vm.terminator();
    let stopper = std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(500));
        t.terminate();
    });
    let result = vm.run(&script);
    stopper.join().map_err(|_| "thread".to_string())?;
    match result {
        Err(Abrupt::Terminated) => Ok(()),
        other => Err(format!("expected Terminated, got {other:?}")),
    }
}

/// The flag properties and `@@species` are the standard's accessors
/// (§22.2.6†, §22.2.5.2†): on `RegExp.prototype`, not on each instance, and
/// `flags` follows what `Get` sees.
#[test]
fn flag_accessors_and_species() -> Result<(), String> {
    let bad_this = throws(
        "TypeError",
        "Object.getOwnPropertyDescriptor(RegExp.prototype, 'global').get.call({})",
    );
    let non_object = throws(
        "TypeError",
        "Object.getOwnPropertyDescriptor(RegExp.prototype, 'flags').get.call(1)",
    );
    check(&[
        (
            "var d = Object.getOwnPropertyDescriptor(RegExp.prototype, 'global'); var r = typeof d.get + ',' + d.set + ',' + d.enumerable + ',' + d.configurable + ',' + d.get.name;",
            "function,undefined,false,true,get global",
        ),
        (
            "var r = Object.getOwnPropertyNames(/a/g).join();",
            "lastIndex",
        ),
        (
            "var r = RegExp.prototype.global + ',' + RegExp.prototype.flags + ',' + RegExp.prototype.source;",
            "undefined,,(?:)",
        ),
        ("var r = /a/dgimsuy.flags + /a/v.flags;", "dgimsuyv"),
        (
            "var r = /a/g.global + ',' + /a/.global + ',' + /a/y.sticky + ',' + /a/u.unicode;",
            "true,false,true,true",
        ),
        // `flags` reads the other accessors with Get, so an own property wins.
        (
            "var x = /a/; Object.defineProperty(x, 'global', {value: true}); var r = x.flags;",
            "g",
        ),
        ("var r = RegExp[Symbol.species] === RegExp;", "true"),
        (
            "var d = Object.getOwnPropertyDescriptor(RegExp, Symbol.species); var r = typeof d.get + ',' + d.get.name + ',' + d.set;",
            "function,get [Symbol.species],undefined",
        ),
        ("var r = Promise[Symbol.species] === Promise;", "true"),
        ("var r = Array[Symbol.species] === Array;", "true"),
        (
            "var r = Symbol('d').description + ',' + Symbol().description;",
            "d,undefined",
        ),
        (&bad_this, "true"),
        (&non_object, "true"),
    ])
}
