//! Tree-construction conformance (Phase 4 item 4.11): the html5lib
//! tree-construction tests vendored from WPT (`tests/data/wpt-tree-construction/`,
//! converted by `cargo xtask testdata` into `tests/generated/`), run through
//! the executable tree builder.
//!
//! Each case is parsed by the driver that joins `clazel-html`'s proven
//! tokenizer to the proven step (`exec::driver`): a document case by
//! `parse_real`, a `#document-fragment` case by `parse_fragment_real` (a
//! context `"td"` is an HTML element, `"svg path"` and `"math mi"` are SVG
//! and MathML ones). The driver preprocesses the input, feeds every token
//! to `step`, applies the tokenizer switches and the foreign-content flag
//! the step leaves, and ends after end of file or when the parser stops.
//! The tree (the document's children, or the fragment's) is printed in the
//! suite's format by `support/dump.rs` and compared byte for byte with the
//! case's `#document`. Parse errors are not compared (the converter drops
//! them).
//!
//! Scripting: `#script-on` and `#script-off` set the flag; a case with
//! neither runs once, with scripting **off**, the browser's setting (this
//! browser runs no scripts). Its scripting-on reading is not checked.
//!
//! A case whose tree differs is a bug in the tree builder's spec, the
//! tokenizer's spec (each exec is proven equal to its spec), the driver or
//! the support code, and is an expected failure only if listed by name in
//! [`KNOWN_MISMATCHES`] with its cause.
//!
//! Units: cases. `total` is the length of `CASES` (every case of every
//! non-scripted `.dat` file). The `scripted_*.dat` cases need a script
//! engine; they are not in `total` and are reported on a separate line.

#[path = "support/dump.rs"]
mod dump;

use clazel_dom::exec::ExecAttr;
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_treebuilder::exec::driver::{parse_fragment_real, parse_real};
use clazel_treebuilder::exec::step::ExecContext;
use clazel_treebuilder::exec::types::EncFnsExec;

include!("generated/wpt_tree_construction.rs");

/// Cases whose tree differs from the expected one, by `file:index`, with
/// the cause. Today these are only the stated restriction of
/// `src/spec/mod.rs` (hooks outside §13.2 that run when an element is
/// popped are not modelled); anything else would be a bug to fix.
const KNOWN_MISMATCHES: &[(&str, &str)] = &[
    (
        "webkit02.dat:44",
        "restriction (src/spec/mod.rs): HTML §4.10.10 \"When an option element option is popped off the stack of open elements of an HTML parser … update descendant selectedcontent elements for an option\" is not modelled, so <selectedcontent> stays empty",
    ),
    (
        "webkit02.dat:45",
        "restriction: as webkit02.dat:44 (option popped off the stack does not clone into selectedcontent)",
    ),
    (
        "webkit02.dat:46",
        "restriction: as webkit02.dat:44 (option popped off the stack does not clone into selectedcontent)",
    ),
    (
        "webkit02.dat:47",
        "restriction: as webkit02.dat:44 (option popped off the stack does not clone into selectedcontent)",
    ),
];

/// The encoding functions the tree builder calls for `<meta charset>`. The
/// documents here are parsed with a certain encoding (not tentative), so
/// the result never changes the tree.
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

/// The context element of a `#document-fragment` line: `name` is an HTML
/// element, `svg name` and `math name` SVG and MathML ones; `None` for any
/// other prefix.
fn context_of(ctx: &str) -> Option<ExecContext> {
    let (ns, name) = match ctx.split_once(' ') {
        Some(("svg", n)) => (Namespace::Svg, n),
        Some(("math", n)) => (Namespace::MathMl, n),
        Some(_) => return None,
        None => (Namespace::Html, ctx),
    };
    Some(ExecContext {
        ns,
        name: u32s(name),
        attrs: Vec::<ExecAttr>::new(),
        mode: DocumentMode::NoQuirks,
    })
}

fn run(case: &Case, scripting: bool) -> String {
    let input = u32s(case.data);
    match case.fragment {
        None => {
            let (p, _) = parse_real(&NoEnc, &input, Vec::new(), scripting, false);
            dump::dump_children(&p.arena, 0)
        }
        Some(ctx) => {
            // An unknown context prints as a tree that matches nothing, so
            // the case fails.
            let Some(context) = context_of(ctx) else {
                return format!("#unknown context {ctx:?}");
            };
            let (p, root, _) = parse_fragment_real(&NoEnc, &input, context, scripting);
            dump::dump_children(&p.arena, root)
        }
    }
}

#[test]
fn wpt_tree_construction() {
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut failed: Vec<String> = Vec::new();
    let mut known_hit: Vec<&str> = Vec::new();
    let mut stale: Vec<&str> = Vec::new();
    let mut default_scripting = 0usize;
    // Miri runs every 40th case (50 of 1,968; the whole suite took over
    // 300 s there): it looks for undefined behaviour in the paths the cases
    // exercise, and the full suite runs in the normal test job.
    let stride = if cfg!(miri) { 40 } else { 1 };
    let mut run_count = 0usize;
    for case in CASES.iter().step_by(stride) {
        run_count = run_count.saturating_add(1);
        let id = format!("{}:{}", case.file, case.index);
        if case.scripting.is_none() {
            default_scripting += 1;
        }
        let known = KNOWN_MISMATCHES.iter().find(|(k, _)| *k == id);
        let tree = run(case, case.scripting.unwrap_or(false));
        let tree = tree.strip_suffix('\n').unwrap_or(&tree);
        if tree == case.document {
            pass += 1;
            if let Some((k, _)) = known {
                stale.push(k);
            }
        } else if let Some((k, _)) = known {
            known_hit.push(k);
            xfail += 1;
        } else {
            failed.push(format!(
                "{id} data={:?} fragment={:?} scripting={:?}\n--- expected\n{}\n--- actual\n{}",
                case.data, case.fragment, case.scripting, case.document, tree
            ));
        }
    }
    if cfg!(miri) {
        for f in &failed {
            println!("MISMATCH {f}\n");
        }
        assert!(
            stale.is_empty(),
            "listed as mismatches but now pass: {stale:?}"
        );
        assert!(failed.is_empty(), "{} unexpected mismatches", failed.len());
        assert_eq!(pass + xfail + failed.len(), run_count);
        return;
    }
    println!(
        "tree construction: {} cases run with scripting off (no #script-on/#script-off)",
        default_scripting
    );
    println!(
        "tree construction: {} known mismatches (see KNOWN_MISMATCHES):",
        known_hit.len()
    );
    for k in &known_hit {
        let why = KNOWN_MISMATCHES
            .iter()
            .find(|(n, _)| n == k)
            .map_or("", |(_, w)| w);
        println!("  {k}: {why}");
    }
    for f in &failed {
        println!("MISMATCH {f}\n");
    }
    println!(
        "tree construction: scripted_*.dat cases not run (need a script engine, not in total): {}",
        SCRIPTED_NOT_RUN
    );
    println!(
        "clazel-conformance: suite=\"html5lib tree construction (WPT)\" pass={pass} xfail={xfail} fail={} total={}",
        failed.len(),
        CASES.len()
    );
    assert!(
        stale.is_empty(),
        "listed as mismatches but now pass: {stale:?}"
    );
    assert!(failed.is_empty(), "{} unexpected mismatches", failed.len());
    assert_eq!(pass + xfail + failed.len(), CASES.len());
}
