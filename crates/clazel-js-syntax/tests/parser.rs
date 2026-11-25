//! Unit tests of the parser: small programs it must accept, and ones it must
//! reject.

use clazel_js_syntax::api::ParseError;
use clazel_js_syntax::ast::{Ast, NodeKind};
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn script(s: &str) -> Result<Ast, ParseError> {
    parse(&cps(s), SourceGoal::Script)
}

fn module(s: &str) -> Result<Ast, ParseError> {
    parse(&cps(s), SourceGoal::Module)
}

fn ok(s: &str) {
    assert!(script(s).is_ok(), "should parse: {s}");
}

fn bad(s: &str) {
    assert!(
        matches!(script(s), Err(ParseError::Syntax)),
        "should be a syntax error: {s}"
    );
}

#[test]
fn empty_and_simple() {
    ok("");
    ok(";");
    ok("var a = 1, b;");
    ok("let x = 1; const y = 2;");
    ok("a + b * c - d / e");
    ok("if (a) b; else c");
    ok("for (var i = 0; i < 10; i++) { continue; }");
    ok("for (const x of y) ;");
    ok("for (x in y) ;");
    ok("function f(a, b = 1, ...c) { return a; }");
    ok("a => a; (a, b) => a + b; async x => x; async (x) => x;");
    ok(
        "class A extends B { constructor() { super(); } static x = 1; #p = 2; get a() { return 1; } static { } }",
    );
    ok("x = `a${b}c${d}e`; tag`x`;");
    ok("var re = /ab+c/gi; a = b / c / d;");
    ok("a?.b?.[c]?.(d)");
    ok("({a, b: c, ...d} = e); [a, , b = 1, ...c] = d;");
    ok("label: for (;;) break label;");
    ok("switch (a) { case 1: break; default: }");
    ok("try { } catch ({a}) { } finally { }");
    ok("a\nb");
    ok("return_ = 1");
}

#[test]
fn asi() {
    ok("a = 1\nb = 2");
    ok("do ; while (0) x");
    ok("var a = 1\n++b");
    bad("a b");
    bad("if (a) b else c");
}

#[test]
fn syntax_errors() {
    bad("var");
    bad("a +");
    bad("(");
    bad("1 = 2");
    bad("({a = 1})");
    bad("a ?? b || c");
    bad("-a ** b");
    bad("return");
    bad("let [a];");
    bad("class A { constructor() {} constructor() {} }");
    bad("`\\u{`");
    bad("function* g() { yield\n* 1 }");
}

#[test]
fn modules() {
    assert!(
        module("import a, {b as c} from 'm'; export default a; export {c}; export * from 'x';")
            .is_ok()
    );
    assert!(module("await 1").is_ok());
    assert!(module("export default class {}").is_ok());
    assert!(script("import a from 'm'").is_err());
}

#[test]
fn root_and_spans() {
    let r = script("a;\n b;");
    assert!(r.is_ok());
    if let Ok(ast) = r {
        let root = ast.nodes.get(ast.root as usize);
        assert!(root.is_some_and(|n| n.kind == NodeKind::Script && n.start == 0 && n.end == 6));
    }
}

#[test]
fn depth_limit() {
    let deep = format!("{}1{}", "(".repeat(1500), ")".repeat(1500));
    assert!(matches!(script(&deep), Err(ParseError::TooDeep)));
    let ok_deep = format!("{}1{}", "(".repeat(500), ")".repeat(500));
    assert!(script(&ok_deep).is_ok());
}

/// Eval code (PerformEval §19.2.1.1 steps 11.e to 11.h and 12): what its
/// caller allows.
#[test]
fn eval_code_and_its_caller() {
    use clazel_js_syntax::early::private_name_at;
    use clazel_js_syntax::exec::{EvalContext, parse_eval};
    let none = EvalContext::default();
    let all = EvalContext {
        in_function: true,
        in_method: true,
        in_derived_constructor: true,
        ..EvalContext::default()
    };
    for s in ["new.target", "super.x", "super()"] {
        assert!(parse_eval(&cps(s), &none).is_err(), "{s} needs a caller");
        assert!(parse_eval(&cps(s), &all).is_ok(), "{s} with its caller");
    }
    // Not `arguments` in a class field initializer, even in an arrow.
    let field = EvalContext {
        in_class_field_initializer: true,
        ..all.clone()
    };
    assert!(parse_eval(&cps("() => arguments"), &field).is_err());
    assert!(parse_eval(&cps("function f() { arguments }"), &field).is_ok());
    // A strict caller makes the code strict.
    let strict = EvalContext {
        strict: true,
        ..EvalContext::default()
    };
    assert!(parse_eval(&cps("var eval;"), &none).is_ok());
    assert!(parse_eval(&cps("var eval;"), &strict).is_err());
    // A private name of a class around the call.
    let src = cps("class C { #p; m() { this.#p } }");
    let at = src.iter().position(|&c| c == u32::from(b'#')).unwrap_or(0);
    let named = EvalContext {
        private_names: vec![private_name_at(&src, at)],
        ..EvalContext::default()
    };
    assert!(parse_eval(&cps("o.#p"), &none).is_err());
    assert!(parse_eval(&cps("o.#p"), &named).is_ok());
}
