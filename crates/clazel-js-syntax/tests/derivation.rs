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
        "class A { #p = 1; #m() {} static #s; get #g() { return this.#p } m(o) { return o.#p.x } }",
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

/// The remaining script syntax: optional chains, `super`, `new.target`, `import()`,
/// `import.meta`, `for await`, Annex B's `for (var x = 1 in o)` and function declarations
/// as statement bodies, patterns as `for` heads, and operands of `[~In]` heads.
#[test]
fn remaining_script_syntax_is_verified() {
    for s in [
        "a?.b;",
        "a?.[b];",
        "a?.();",
        "a?.b.c(d)?.[e];",
        "a?.b\n.c?.d(e)\n[f];",
        "class A extends B { constructor() { super(); super(1, ...a); } m() { super.x; super[x](); } }",
        "x = { m() { return super.m; } };",
        "function f() { new.target; new.target.x; }",
        "function f() { return a?.b?.(c)?.[d]; }",
        "class A { #x; m() { return this?.#x; } }",
        "import('a');",
        "import('a', {});",
        "import('a',);",
        "import('a', b,);",
        "async function f() { for await (x of y) ; }",
        "async function f() { for await (const [a, b] of c) d; }",
        "for (var x = 1 in o) ;",
        "if (a) function f() {} else function g() {}",
        "l: function f() {}",
        "for (let [a, b] of o) ;",
        "for (const {a, b: [c = 1]} of o) ;",
        "for (var [a] in o) ;",
        "for ([a, b = 1, ...c] of o) ;",
        "for ({a, b: c = 2, ...d} in o) ;",
        "for (a.b[c] of d) ;",
        "for (f().x of y) ;",
        "for (let [a = (1, 2)] of b) ;",
        "for (a, b;;) ;",
        "for (i = 0, j = 1; i < j; i++) ;",
        "for (var i = a ? b : c; ;) ;",
        "for (var i = f(1), j = new A(2); ;) ;",
        "for (var i = a.b[c]; ;) ;",
        "for (var i = (1, 2); ;) ;",
        "for (var i = [1, ...a]; ;) ;",
        "for (var i = {a: 1, ...b, [c]: 2, m() {}}; ;) ;",
        "for (var i = `a${b}`; ;) ;",
        "for (var i = a`x`; ;) ;",
        "for (var i = a?.b; ;) ;",
        "for (var i = ({a} = b); ;) ;",
        "for (var i = 0, j = (1, 2); i < j; i++) ;",
    ] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Verified),
            "{s}"
        );
    }
}

/// `import.meta` is in a `Module` only.
#[test]
fn import_meta_is_verified_in_a_module() {
    for s in ["import.meta;", "import.meta.url;", "f(import.meta);"] {
        assert!(
            derivation(s, SourceGoal::Module) == Some(Derivation::Verified),
            "{s}"
        );
        assert!(derivation(s, SourceGoal::Script).is_none(), "{s}");
    }
}

/// Every form of `import` and `export` (§16.2).
#[test]
fn module_items_are_verified() {
    for s in [
        "import a from 'b';",
        "import 'b';",
        "import * as ns from 'b';",
        "import a, * as ns from 'b';",
        "import a, { b, c as d } from 'b';",
        "import { } from 'b';",
        "import { a, } from 'b'\nx",
        "import { \"str\" as s } from 'b';",
        "import { default as x } from 'b';",
        "import a from 'b' with { type: 'json' };",
        "import 'b' with { };",
        "import a from 'b' with { 'type': 'json', };",
        "export default 1;",
        "export default function () {}",
        "export default function f() {}",
        "export default async function () {}",
        "export default function* () {}",
        "export default class {}",
        "export default class A { m() {} static s() {} }",
        "export default a + b",
        "export { };",
        "var a; export { a as \"b\", a as c, };",
        "export { a } from 'b';",
        "export { a as b } from 'b' with { type: 'json' };",
        "export * from 'b';",
        "export * as ns from 'b';",
        "export * as \"x y\" from 'b' with { a: 'b' };",
        "export const x = 1, y = 2;",
        "export let z;",
        "export var v;",
        "export function f() {}",
        "export async function f() {}",
        "export class A {}",
        "import.meta; await 1; export default await 1;",
    ] {
        assert!(
            derivation(s, SourceGoal::Module) == Some(Derivation::Verified),
            "{s}"
        );
    }
}

/// The last gaps of the script grammar: `let` as an identifier head, and `await`, `yield`
/// and classes in `[~In]` heads.
#[test]
fn leftover_script_gaps_are_verified() {
    for s in [
        "for (let in o) ;",
        "for (var i = class {}; ;) ;",
        "for (var i = class A extends B { m() {} }; ;) ;",
        "async function f() { for (var i = await x; ;) ; }",
        "function* g() { for (var i = yield x; ;) ; }",
    ] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Verified),
            "{s}"
        );
    }
}

fn early(s: &str) -> Option<Derivation> {
    clazel_js_syntax::exec::parse_checked_early(&cps(s), SourceGoal::Script)
        .ok()
        .map(|(_, _, e)| e)
}

/// The early rules the proven check covers.
#[test]
fn covered_early_rules_are_verified() {
    for s in [
        "",
        "1 + 2;",
        "a = b; a.c = d; a[0]++; ++a.b;",
        "010; '\\07';",
        "yield = 1; var await = 2; let = 3;",
        "`a${b}c`; f`\\u{`;",
        "if (a) b; else c;",
        "while (a) { b; if (c) break; else continue; }",
        "do { break; } while (a);",
        "for (;;) { break; }",
        "for (var i = 0; i < n; i++) { continue; }",
        "switch_ = 1; with (a) b;",
        "a?.b?.[c]?.(d);",
        "delete a.b; typeof a; void 0; a in b; a instanceof b;",
        "{ a; { b; } }",
        "var a; var a;",
        "new.target",
    ] {
        let r = early(s);
        if s == "new.target" {
            assert!(r.is_none(), "{s}");
        } else {
            assert!(r == Some(Derivation::Verified), "{s}");
        }
    }
}

/// What the proven early-error check leaves alone.
#[test]
fn other_early_rules_are_unsupported_not_failed() {
    for s in [
        "'use strict'; a = 1;",
        "let a;",
        "a: b;",
        "(function () {})",
        "class A {}",
        "for (a in b) ;",
        "/a/;",
        "a.#b;",
        "try {} catch (e) {}",
        "switch (a) { case 1: }",
    ] {
        let r = early(s);
        assert!(r != Some(Derivation::Verified) && r != Some(Derivation::Failed), "{s}");
    }
}

/// Productions only a sloppy-mode `Script` has.
#[test]
fn covered_sloppy_programs_are_verified() {
    for s in [
        "with (a) b;",
        "with (a) { b = 1; }",
        "for (a.b of c) ;",
        "for (a.b.c in d) ;",
        "for (x of y) with (x) z;",
    ] {
        assert!(
            derivation(s, SourceGoal::Script) == Some(Derivation::Verified),
            "{s}"
        );
    }
}

#[test]
fn other_programs_are_unsupported_not_failed() {
    for s in ["for (var i = class { x = 1 };;) ;", "for (var i = class { #p; };;) ;"] {
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
#[cfg_attr(miri, ignore = "times two parses of 1.7 million characters")]
fn what_the_check_costs() {
    let body = "(1 + 2 * 3) < 4 - 5 / 6 % 7;\n".repeat(60_000);
    let covered = cps(&body);
    let stopped = cps(&format!("for (var i = class {{ x = 1 }};;) ;\n{body}"));
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
