//! The proven check of the whole arena against the tokens
//! ([`clazel_js_syntax::arena_d`]): which programs it covers, that it never
//! finds a covered node the parser built wrongly, and what it costs.

use clazel_js_syntax::arena_d::Derivation;
use clazel_js_syntax::exec::parse_checked;
use clazel_js_syntax::spec::SourceGoal;
use std::time::Instant;

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn derivation(s: &str, goal: SourceGoal) -> Option<Derivation> {
    parse_checked(&cps(s), goal).ok().map(|(_, d)| d)
}

#[test]
fn covered_programs_are_verified() {
    for s in [
        "",
        ";",
        ";;",
        "1;",
        "1\n2\n3",
        "1 + 2 * 3;",
        "(1 + 2) * 3\n4 < 5 > 6",
        "'a'; ; /re/;",
        "((1));",
        "1 - 2 - 3 / 4 % 5;",
        "2 ** 3 ** 2;",
        "1 << 2 >> 3 >>> 4;",
        "1 == 2 != 3 === 4 !== 5;",
        "1 & 2 ^ 3 | 4;",
        "1 && 2 || 3 && 4;",
        "1 ?? 2 ?? 3;",
        "1 <= 2 >= 3 < 4;",
        "1 in 2 instanceof 3;",
        "-1; !2; ~3; +4; typeof 5; void 6; delete (7).a;",
        "- -1 + +2;",
        "1 ? 2 : 3 ? 4 : 5;",
        "(1).a;",
        "(1).a.b.c;",
        "(1).a = 2;",
        "(1).a += 2 ** 3;",
        "(1).a &&= (1).b ||= 3;",
        "a;",
        "{}",
        "{ a; b = 1; { ; } }",
        "if (a) b; else c;",
        "if (a) { var x = 1; } else if (b) ; else { let y = 2 }",
        "if (a) b
else c",
        "var a = 1, b;",
        "let x = a + 1;
const y = f(2), z = (3);",
        "var a
var b = 2
var c;",
        "f(1);",
        "f(a, ...b,);",
        "f();",
        "(1, 2, 3);",
        "a.b(c)(d, e);",
        "this; null; true; false;",
        "f(g(h(1)), 2) + (a, b);",
        "a + b * c;",
        "a.b.c = d ? e : f;",
        "typeof a === 'x';",
        "function f() {}",
        "function f(a, b) { return a + b; }",
        "function f(a, b = 1, ...c) { return; }",
        "function f(a,) { return\nx }",
        "(function () { return 1 })();",
        "(function g(a) { return g })",
        "function* g() { yield; yield 1; yield * 2; }",
        "async function h() { await 1; }",
        "async function* k() { yield await 1; }",
        "(a => a + 1);",
        "(() => { return 1 });",
        "((a, b) => a);",
        "(async a => await a);",
        "(async (a) => 1);",
        "function f() { function g() { return 1 } return g }",
        "`a`;",
        "`a${b}c`;",
        "`${a}${b}`;",
        "`a${b}c${d + 1}e${`n${f}`}`;",
        "f`x${y}z`;",
        "a.b`c`.d;",
        "class A {}",
        "class A extends B { }",
        "class A { m() {} static s(a) { return a } get g() { return 1 } set g(v) {} }",
        "class A { *gen() { yield 1 } async am() { await 1 } async *ag() { yield 1 } }",
        "class A { x; y = 1; static z = 2; 'q' = 3; [k] = 4; }",
        "class A { #p = 1; #m() {} static #s; get #g() { return 1 } }",
        "class A { ; ; m() {} ; }",
        "class A { static { a; } static { var x = 1; } }",
        "(class {}); (class B extends C {});",
        "x = {m() {}, get a() { return 1 }, set a(v) {}, *g() {}, async f() {}, [k]() {}};",
        "a++; b--; ++c; --d.e;",
        "x = a[0] + b[c][d];",
        "new a;",
        "new a();",
        "new a.b(1, 2);",
        "new new a()();",
        "new (f())();",
        "[a] = b;",
        "[a, , b = 1, ...c.d] = e;",
        "({a} = b);",
        "({a = 1, b: c, d: [e], f: {g}, ...h} = i);",
        "[a.b, c.d] = d;",
        "var [a] = 1;",
        "var [a, , b = 2, ...c] = d;",
        "var {a, b: c, d = 3, ...e} = f;",
        "let {a: {b}, c: [d, e]} = g;",
        "const [x, [y, z], {w}] = h;",
        "function f({a, b}, [c], d = 1, ...[e, f]) {}",
        "function g(...{length}) {}",
        "try { a } catch ({message}) { b }",
        "[];",
        "[1, 2, 3];",
        "[1, 2,];",
        "[,];",
        "[, , 1, , 2, ,];",
        "[...a, b, ...c];",
        "[[1], [2, [3]]];",
        "({});",
        "({a});",
        "({a: 1, b: 2,});",
        "({'a': 1, 2: 3, [k]: 4, ...r});",
        "({a, b: [1], c: {d: e}});",
        "var o = {x: 1}, p = [o];",
        "for (var k of [1, 2]) ;",
        "for (;;) ;",
        "for (;;) { break; }",
        "for (a = 0; a < 10; a = a + 1) b;",
        "for (var i = 0, n = 5; i < n; i = i + 1) { c }",
        "for (let i = 0; i < n; i = i + 1) c;",
        "for (const i = 0;;) c;",
        "for (var i = 0 + 1 * 2;;) ;",
        "for (x of y) z;",
        
        "for (let x in o) z;",
        "for (x in o) ;",
        "for (const a of b.c) { d }",
        "for (var i in a, b) ;",
        "for (a in b) for (c of d) e;",
        "while (a) b;",
        "while (a) { b; c }",
        "do a; while (b)",
        "do { a } while (b);",
        "do a; while (b) c;",
        "throw a;",
        "throw a\nx",
        "debugger;",
        "debugger\nx",
        "a: b;",
        "a: b: c;",
        "a: while (x) { break a; continue a; break; continue; }",
        "while (1) { break\nx }",
        "try { a } catch (e) { b }",
        "try { a } catch { b }",
        "try { a } finally { b }",
        "try { a } catch (e) { b } finally { c }",
        "switch (a) {}",
        "switch (a) { case 1: b; c; case 2: default: d; }",
        "switch (a) { default: case 1: }",
        "a in b;",
        "// c\n 1 /* d */ + 2 ;;",
    ] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Verified),
            "{s}"
        );
        assert!(
            derivation(s, SourceGoal::Module) == Some(Derivation::Verified),
            "{s}"
        );
    }
}

#[test]
fn other_programs_are_unsupported_not_failed() {
    for s in ["for (a, b;;) ;", "a?.b;"] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Unsupported),
            "{s}"
        );
    }
}

#[test]
fn errors_are_still_errors() {
    for s in ["1 +", "(", "1 2", ")"] {
        assert!(derivation(s, SourceGoal::Script).is_none(), "{s}");
    }
}

/// The cost of the check: the same program of covered nodes, parsed with the
/// check running to the end and with an uncovered node first, which stops it at
/// once (the parse and the other checks of `parse` are the same).
#[test]
fn what_the_check_costs() {
    let body = "(1 + 2 * 3) < 4 - 5 / 6 % 7;\n".repeat(60_000);
    let covered = cps(&body);
    let stopped = cps(&format!("a?.b;\n{body}"));
    let time = |src: &[u32]| {
        let t = Instant::now();
        let r = parse_checked(src, SourceGoal::Script);
        (t.elapsed(), r.map(|(_, d)| d).ok())
    };
    let (_, d0) = time(&covered);
    assert!(d0 == Some(Derivation::Verified));
    let (_, d1) = time(&stopped);
    assert!(d1 == Some(Derivation::Unsupported));
    let best = |src: &[u32]| (0..3).map(|_| time(src).0).min().unwrap_or_default();
    let with = best(&covered);
    let without = best(&stopped);
    println!(
        "covered, checked to the end: {with:?}; same size, check stopped at once: {without:?}"
    );
}
