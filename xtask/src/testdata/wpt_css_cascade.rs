//! WPT `css/css-cascade/` (phase-5.md item 5.7): the testharness.js pages whose tests read
//! computed values.
//!
//! Each `test(...)` call of a page's scripts is read statement by statement. A test is a
//! case when its body holds only these statements, in any order:
//!
//! - `X.offsetTop;` or `X.offsetLeft;` (which only force a style update);
//! - `let NAME = getComputedStyle(TARGET).PROPERTY;` (or `const`);
//! - `assert_equals(A, B, ...)` and `assert_not_equals(A, B, ...)`, where `A` and `B` are
//!   each `getComputedStyle(TARGET).PROPERTY`, a `NAME` bound above, or a string literal,
//!   and anything after `B` is a message.
//!
//! `TARGET` is an identifier, which names the element with that `id` (the page relies on
//! the window's named properties), or `document.documentElement`. A property's camel-case
//! name becomes its CSS name (`marginTop` is `margin-top`). Every other test (mutating the
//! DOM or the style, animations, loops, `all`) is listed by line, with the first statement
//! it could not read, as not run.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Parser, find_all, scalars};

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "important-vs-inline-001.html",
    "important-vs-inline-002.html",
    "inherit-initial.html",
    "presentational-hints-cascade.html",
    "revert-val-005.html",
    "revert-val-006.html",
    "revert-val-011.html",
];

/// A value an assertion compares.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    /// `getComputedStyle(target).property`; an empty target is the root element.
    Computed { target: String, property: String },
    /// A string literal.
    Literal(String),
}

/// One assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Assertion {
    equal: bool,
    left: Value,
    right: Value,
}

/// `marginTop` as `margin-top`.
fn css_name(camel: &str) -> String {
    let mut out = String::new();
    for c in camel.chars() {
        if c.is_ascii_uppercase() {
            out.push('-');
            out.push(c.to_ascii_lowercase());
        } else {
            out.push(c);
        }
    }
    out
}

/// A string literal's value.
fn string(p: &mut Parser) -> Result<String, String> {
    let node = p.literal()?;
    let units = node.str_units()?;
    let cps = scalars(units)?;
    Ok(cps.iter().filter_map(|&c| char::from_u32(c)).collect())
}

/// `getComputedStyle(TARGET).PROPERTY`, after its first word.
fn computed(p: &mut Parser) -> Result<Value, String> {
    p.expect("(")?;
    let first = p.ident()?;
    let target = if first == "document" {
        p.expect(".")?;
        let d = p.ident()?;
        if d != "documentElement" {
            return p.err("expected documentElement");
        }
        String::new()
    } else {
        first
    };
    p.expect(")")?;
    p.expect(".")?;
    let property = css_name(&p.ident()?);
    Ok(Value::Computed { target, property })
}

/// One operand of an assertion.
fn operand(p: &mut Parser, names: &[(String, Value)]) -> Result<Value, String> {
    if p.next_is('"') || p.next_is('\'') {
        return Ok(Value::Literal(string(p)?));
    }
    let word = p.ident()?;
    if word == "getComputedStyle" {
        return computed(p);
    }
    names
        .iter()
        .rev()
        .find(|(n, _)| *n == word)
        .map(|(_, v)| v.clone())
        .ok_or_else(|| format!("line {}: {word} is not a name bound above", p.line()))
}

/// The body of a test, from after its `{` to its `}`: the assertions, or why it is not read.
fn body(p: &mut Parser) -> Result<Vec<Assertion>, String> {
    let mut names: Vec<(String, Value)> = Vec::new();
    let mut out = Vec::new();
    for _ in 0..1000 {
        if p.eat("}") {
            return Ok(out);
        }
        let line = p.line();
        let word = p
            .ident()
            .map_err(|_| format!("line {line}: a statement not read"))?;
        match word.as_str() {
            "let" | "const" => {
                let name = p.ident()?;
                p.expect("=")?;
                if p.ident()? != "getComputedStyle" {
                    return Err(format!(
                        "line {line}: a binding other than getComputedStyle"
                    ));
                }
                let v = computed(p)?;
                names.push((name, v));
            }
            "assert_equals" | "assert_not_equals" => {
                p.expect("(")?;
                let left = operand(p, &names)?;
                p.expect(",")?;
                let right = operand(p, &names)?;
                if p.eat(",") {
                    let _ = string(p)?;
                }
                p.expect(")")?;
                out.push(Assertion {
                    equal: word == "assert_equals",
                    left,
                    right,
                });
            }
            _ => {
                p.expect(".")?;
                let member = p.ident()?;
                if member != "offsetTop" && member != "offsetLeft" {
                    return Err(format!("line {line}: `{word}.{member}`, not read"));
                }
            }
        }
        p.expect(";")?;
    }
    p.err("a test body too long")
}

/// One `test(` call at char offset `at` (after `test(`): its assertions and name, or why it
/// is not read.
fn test_call(text: &str, at: usize) -> Result<(Vec<Assertion>, String), String> {
    let mut p = Parser::at(text, at);
    if p.eat("function") {
        p.expect("(")?;
        p.expect(")")?;
    } else {
        p.expect("(")?;
        p.expect(")")?;
        p.expect("=>")?;
    }
    p.expect("{")?;
    let assertions = body(&mut p)?;
    let name = if p.eat(",") {
        string(&mut p)?
    } else {
        String::new()
    };
    p.expect(")")?;
    Ok((assertions, name))
}

fn value_rust(v: &Value) -> String {
    match v {
        Value::Computed { target, property } => {
            format!("Value::Computed {{ target: {target:?}, property: {property:?} }}")
        }
        Value::Literal(s) => format!("Value::Literal({s:?})"),
    }
}

/// The generated file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let mut cases = String::new();
    let mut not_run = String::new();
    let mut pages = String::new();
    let (mut n_cases, mut n_not_run) = (0usize, 0usize);
    for file in FILES {
        let text = std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))?;
        let _ = writeln!(
            pages,
            "    ({file:?}, include_str!(\"../data/wpt-css-cascade/{file}\")),"
        );
        for at in find_all(&text, "test(") {
            // Only a call of `test` itself, not of `promise_test` and the like.
            let before = text.chars().nth(at.saturating_sub(6));
            if before.is_some_and(|c| c.is_ascii_alphanumeric() || c == '_') {
                continue;
            }
            let line = Parser::at(&text, at).line();
            match test_call(&text, at) {
                Ok((assertions, name)) if !assertions.is_empty() => {
                    let list: Vec<String> = assertions
                        .iter()
                        .map(|a| {
                            format!(
                                "Assertion {{ equal: {}, left: {}, right: {} }}",
                                a.equal,
                                value_rust(&a.left),
                                value_rust(&a.right)
                            )
                        })
                        .collect();
                    let _ = writeln!(
                        cases,
                        "    Case {{ page: {file:?}, line: {line}, name: {name:?}, assertions: &[{}] }},",
                        list.join(", ")
                    );
                    n_cases = n_cases.saturating_add(1);
                }
                Ok(_) => {
                    let _ = writeln!(not_run, "    ({file:?}, {line}, \"no assertion\"),");
                    n_not_run = n_not_run.saturating_add(1);
                }
                Err(why) => {
                    let _ = writeln!(not_run, "    ({file:?}, {line}, {why:?}),");
                    n_not_run = n_not_run.saturating_add(1);
                }
            }
        }
    }
    if n_cases == 0 {
        return Err("no case read".into());
    }
    Ok(format!(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-css-cascade/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_css_cascade.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-css-cascade/SOURCE.md.\n\
         \n\
         // The pages, whose documents the cases style.\n\
         const PAGES: &[(&str, &str)] = &[\n{pages}];\n\
         \n\
         // The tests read: {n_cases}.\n\
         const CASES: &[Case] = &[\n{cases}];\n\
         \n\
         // The tests not read, by page and line, with why: {n_not_run}.\n\
         const NOT_RUN: &[(&str, usize, &str)] = &[\n{not_run}];\n"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_simple_tests_and_lists_the_rest() {
        let page = "<script>\ntest(() => {\n  el.offsetTop;\n  \
                    assert_equals(getComputedStyle(el).lineHeight, \"36px\", \"m\");\n});\n\
                    test(function() {\n  let a = getComputedStyle(x).marginTop;\n  \
                    let b = getComputedStyle(document.documentElement).marginTop;\n  \
                    assert_not_equals(b, '0px');\n  assert_equals(a, b);\n}, 'n');\n\
                    test(() => {\n  el.style.opacity = 0.75;\n});\n</script>";
        let starts = find_all(page, "test(");
        let first = starts.first().map(|&a| test_call(page, a));
        assert_eq!(
            first,
            Some(Ok((
                vec![Assertion {
                    equal: true,
                    left: Value::Computed {
                        target: "el".into(),
                        property: "line-height".into()
                    },
                    right: Value::Literal("36px".into()),
                }],
                String::new()
            )))
        );
        let second = starts.get(1).map(|&a| test_call(page, a));
        assert_eq!(
            second.and_then(Result::ok).map(|(a, n)| (a.len(), n)),
            Some((2, "n".to_owned()))
        );
        let third = starts.get(2).map(|&a| test_call(page, a));
        assert!(third.is_some_and(|r| r.is_err()));
    }
}
