//! In every parse, the children of a node are in source order and do not
//! overlap, and no non-empty node starts or ends in white space: the spans are
//! those of tokens (the first token's start to the last token's end). The
//! verified check ([`clazel_js_syntax::check::finish`]) proves only that a
//! child is inside its parent.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;

fn check_ordered(src: &str, goal: SourceGoal) -> Result<(), String> {
    let cps: Vec<u32> = src.chars().map(u32::from).collect();
    let Ok(ast) = parse(&cps, goal) else {
        return Ok(());
    };
    for (i, n) in ast.nodes.iter().enumerate() {
        let mut prev_end = n.start;
        for c in &n.children {
            let Some(cn) = ast.nodes.get(*c as usize) else {
                return Err(format!("node {i}: no child {c}"));
            };
            if cn.start < prev_end {
                return Err(format!(
                    "node {i}: child {c} starts at {} before {prev_end}",
                    cn.start
                ));
            }
            prev_end = cn.end;
        }
        if n.start < n.end {
            let first = cps.get(n.start).copied().unwrap_or(0);
            let last = cps.get(n.end.saturating_sub(1)).copied().unwrap_or(0);
            let is_space =
                |c: u32| char::from_u32(c).is_some_and(char::is_whitespace) || c == 0xFEFF;
            if is_space(first) || is_space(last) {
                return Err(format!(
                    "node {i} {}..{} starts or ends in white space",
                    n.start, n.end
                ));
            }
        }
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn children_are_ordered_and_spans_are_tokens() -> Result<(), String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clazel-js-lexer/tests/data/test262/harness");
    let mut n = 0;
    for entry in std::fs::read_dir(root).map_err(|e| e.to_string())? {
        let p = entry.map_err(|e| e.to_string())?.path();
        if p.extension().is_some_and(|x| x == "js") {
            let text = std::fs::read_to_string(&p).map_err(|e| e.to_string())?;
            check_ordered(&text, SourceGoal::Script)
                .map_err(|e| format!("{}: {e}", p.display()))?;
            n += 1;
        }
    }
    assert!(n > 20);
    Ok(())
}

/// The same property on inline sources, so that it also runs under Miri.
#[test]
fn inline_children_are_ordered_and_spans_are_tokens() -> Result<(), String> {
    for s in [
        "a = b ? (c, d) : e; for (var a of b) ; ({ a = 1 } = b); (a, [b] = c) => d; class A { static x = 1; #y; m() {} }",
        "export default class {}; import a, { b as c } from 'm'",
        "async function* f() { for await (const [a, ...b] of c) { yield* d; } } label: while (1) { break label }",
        "x = `a${b}c${`d${e}`}f`; tag`x`; a?.b?.[c]?.(d); new a.b(c)(d); y = a ?? b",
    ] {
        check_ordered(s, SourceGoal::Script)?;
        check_ordered(s, SourceGoal::Module)?;
    }
    Ok(())
}
