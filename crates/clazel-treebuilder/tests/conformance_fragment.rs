//! The fragment parsing algorithm (HTML §13.4, Phase 7 item 7.13):
//! the `#document-fragment` cases of the html5lib tree-construction suite
//! (`tests/data/wpt-tree-construction/`, the same `CASES` as
//! `conformance_tree_construction.rs`), through `exec::driver::parse_fragment_real`.
//!
//! What this adds to `conformance_tree_construction.rs`, which already runs
//! these cases once each:
//! - the suite's format says a case with neither `#script-on` nor
//!   `#script-off` holds for both settings of the scripting flag, so each
//!   such case runs twice here, with the flag off and on; a case that names
//!   a flag runs once with it;
//! - the context element's namespace and name set the tokenizer state
//!   (step 10), the stack of open elements holds an `html` root (step 13)
//!   and `template` contexts push "in template" (step 16); the cases name
//!   a context in every one of those groups, and the test counts the
//!   groups it saw;
//! - the form element pointer (step 19) when the context is in a form: the
//!   suite has no such case (a context carries no ancestors), so the tests
//!   below give `ExecContext::in_form` by hand.
//!
//! A case whose tree differs is an expected failure only if listed by name
//! in [`KNOWN_MISMATCHES`] with its cause; none is. Units: runs (a case
//! with its flag). Under Miri every 8th case runs.

#[path = "support/dump.rs"]
mod dump;

use clazel_dom::exec::ExecAttr;
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_treebuilder::exec::driver::parse_fragment_real;
use clazel_treebuilder::exec::step::ExecContext;
use clazel_treebuilder::exec::types::EncFnsExec;

include!("generated/wpt_tree_construction.rs");

/// Fragment runs whose tree differs from the expected one, as
/// `file:index:scripting`, with the cause.
const KNOWN_MISMATCHES: &[(&str, &str)] = &[];

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn u32s(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

fn context(ns: Namespace, name: &str, in_form: bool) -> ExecContext {
    ExecContext {
        ns,
        name: u32s(name),
        attrs: Vec::<ExecAttr>::new(),
        mode: DocumentMode::NoQuirks,
        in_form,
    }
}

fn context_of(ctx: &str) -> Option<ExecContext> {
    match ctx.split_once(' ') {
        Some(("svg", n)) => Some(context(Namespace::Svg, n, false)),
        Some(("math", n)) => Some(context(Namespace::MathMl, n, false)),
        Some(_) => None,
        None => Some(context(Namespace::Html, ctx, false)),
    }
}

/// The tree a fragment parse builds, printed as the suite does.
fn parse(input: &str, ctx: ExecContext, scripting: bool) -> String {
    let (p, root, _) = parse_fragment_real(&NoEnc, &u32s(input), ctx, scripting);
    let tree = dump::dump_children(&p.arena, root);
    tree.strip_suffix('\n').map_or(tree.clone(), str::to_owned)
}

#[test]
fn wpt_tree_construction_fragments() {
    let stride = if cfg!(miri) { 8 } else { 1 };
    let (mut pass, mut xfail, mut total) = (0usize, 0usize, 0usize);
    let mut failed: Vec<String> = Vec::new();
    let mut stale: Vec<&str> = Vec::new();
    // The context groups of §13.4 steps 10, 13 and 16 the cases cover.
    let (mut rcdata, mut rawtext, mut script, mut plaintext, mut template, mut foreign) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
    let (mut on_only, mut off_only, mut both) = (0usize, 0usize, 0usize);
    for case in CASES.iter().step_by(stride) {
        let Some(ctx) = case.fragment else { continue };
        match ctx {
            "title" | "textarea" => rcdata = rcdata.saturating_add(1),
            "style" | "xmp" | "iframe" | "noembed" | "noframes" => {
                rawtext = rawtext.saturating_add(1)
            }
            "script" => script = script.saturating_add(1),
            "plaintext" => plaintext = plaintext.saturating_add(1),
            "template" => template = template.saturating_add(1),
            c if c.contains(' ') => foreign = foreign.saturating_add(1),
            _ => {}
        }
        let flags: &[bool] = match case.scripting {
            Some(true) => {
                on_only = on_only.saturating_add(1);
                &[true]
            }
            Some(false) => {
                off_only = off_only.saturating_add(1);
                &[false]
            }
            None => {
                both = both.saturating_add(1);
                &[false, true]
            }
        };
        for &scripting in flags {
            let id = format!("{}:{}:{}", case.file, case.index, scripting);
            total = total.saturating_add(1);
            // An unknown context prints as a tree that matches nothing.
            let tree = match context_of(ctx) {
                Some(c) => parse(case.data, c, scripting),
                None => format!("#unknown context {ctx:?}"),
            };
            let known = KNOWN_MISMATCHES.iter().find(|(k, _)| *k == id);
            if tree == case.document {
                pass = pass.saturating_add(1);
                if let Some((k, _)) = known {
                    stale.push(k);
                }
            } else if known.is_some() {
                xfail = xfail.saturating_add(1);
            } else {
                failed.push(format!(
                    "{id} context={ctx:?} data={:?}\n--- expected\n{}\n--- actual\n{tree}",
                    case.data, case.document
                ));
            }
        }
    }
    for f in &failed {
        println!("MISMATCH {f}\n");
    }
    assert!(
        stale.is_empty(),
        "listed as mismatches but now pass: {stale:?}"
    );
    assert!(failed.is_empty(), "{} unexpected mismatches", failed.len());
    assert_eq!(pass.saturating_add(xfail), total);
    if cfg!(miri) {
        return;
    }
    println!(
        "fragments: contexts by group: rcdata {rcdata}, rawtext {rawtext}, script {script}, plaintext {plaintext}, template {template}, foreign {foreign}"
    );
    println!(
        "fragments: cases naming #script-on only {on_only}, #script-off only {off_only}, neither (run both ways) {both}"
    );
    for (name, n) in [
        ("rcdata", rcdata),
        ("rawtext", rawtext),
        ("script", script),
        ("plaintext", plaintext),
        ("template", template),
        ("foreign", foreign),
    ] {
        assert!(n > 0, "no fragment case has a {name} context");
    }
    println!(
        "clazel-conformance: suite=\"html5lib tree construction fragments (WPT)\" pass={pass} xfail={xfail} fail={} total={total}",
        failed.len()
    );
}

/// §13.4 step 19: "Set the HTML parser's form element pointer to the
/// nearest node to context that is a form element". With the pointer set,
/// "in body"'s `form` start tag is ignored ("If the form element pointer is
/// not null, and there is no template element on the stack of open
/// elements, then this is a parse error; ignore the token"), so a `form` in
/// the input of a context in a form is dropped and its children stay.
#[test]
fn form_element_pointer() {
    let input = "<form><input></form><p>x";
    let outside = parse(input, context(Namespace::Html, "div", false), false);
    assert_eq!(
        outside, "| <form>\n|   <input>\n| <p>\n|   \"x\"",
        "no form among the context's ancestors"
    );
    let inside = parse(input, context(Namespace::Html, "div", true), false);
    assert_eq!(
        inside, "| <input>\n| <p>\n|   \"x\"",
        "the context is in a form: the start tag is ignored, and so is the end tag"
    );
    // The context is itself a form: the pointer is set whatever `in_form`
    // says (step 19 includes "the element itself").
    let itself = parse(input, context(Namespace::Html, "form", false), false);
    assert_eq!(itself, inside);
    // In "in table", the `form` start tag is ignored the same way.
    let table = parse(
        "<form></form><tr>",
        context(Namespace::Html, "table", true),
        false,
    );
    assert!(!table.contains("<form>"), "{table}");
    let table_free = parse(
        "<form></form><tr>",
        context(Namespace::Html, "table", false),
        false,
    );
    assert!(table_free.contains("<form>"), "{table_free}");
}

/// Step 16: "If context is a template element, then push "in template" onto
/// the stack of template insertion modes", so a `tr` is kept in the
/// template's contents (it would be dropped in "in body").
#[test]
fn template_context() {
    let tree = parse(
        "<tr><td>x",
        context(Namespace::Html, "template", false),
        false,
    );
    assert_eq!(tree, "| <tr>\n|   <td>\n|     \"x\"");
    let body = parse("<tr><td>x", context(Namespace::Html, "div", false), false);
    assert_eq!(body, "| \"x\"");
}

/// Step 10: the tokenizer state follows the context element: RCDATA for
/// `title` and `textarea`, RAWTEXT for `style`, `xmp`, `iframe`, `noembed`
/// and `noframes`, script data for `script`, PLAINTEXT for `plaintext`, and
/// RAWTEXT for `noscript` only when the scripting flag is on.
#[test]
fn tokenizer_state_from_the_context() {
    let ctx = |n: &str| context(Namespace::Html, n, false);
    assert_eq!(parse("<b>&amp;</b>", ctx("title"), false), "| \"<b>&</b>\"");
    assert_eq!(
        parse("<b>&amp;</b>", ctx("style"), false),
        "| \"<b>&amp;</b>\""
    );
    assert_eq!(
        parse("<b>&amp;</b>", ctx("script"), false),
        "| \"<b>&amp;</b>\""
    );
    assert_eq!(
        parse("<b>&amp;</b>", ctx("plaintext"), false),
        "| \"<b>&amp;</b>\""
    );
    assert_eq!(parse("<b>x</b>", ctx("noscript"), true), "| \"<b>x</b>\"");
    assert_eq!(
        parse("<b>x</b>", ctx("noscript"), false),
        "| <b>\n|   \"x\""
    );
    // A foreign context has no such state: its content is markup.
    assert_eq!(
        parse("<b>x</b>", context(Namespace::Svg, "title", false), false),
        "| <b>\n|   \"x\""
    );
}
