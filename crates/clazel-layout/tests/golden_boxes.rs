//! The golden box tree dumps (phase-5.md item 5.13: "golden box tree dumps
//! for the html5lib tree-construction documents of 4.1 under the UA sheet,
//! reviewed as fixtures"; decision 5.0(g): this replaces `clazel-text`'s
//! golden test when that crate is deleted after item 5.26).
//!
//! Every document case of the html5lib tree-construction suite vendored in
//! `clazel-treebuilder` (read through the table `cargo xtask testdata`
//! generates from it, as `clazel-text`'s and `clazel-style`'s golden tests
//! do) is parsed with scripting off, its style sources collected (its
//! `style` elements and attributes; no linked sheet is fetched), cascaded
//! in an 800 by 600 viewport with `clazel_style::cascade` (item 5.7), and
//! built into a box tree with `clazel_layout::boxes::build`. Each tree is
//! printed with `boxes::dump::dump`. The output of each `.dat` file is
//! compared byte for byte with `tests/golden/boxes/<file>.txt`; any
//! difference fails the test.
//!
//! The cascade uses the user agent sheets cut to the rules that can match
//! the document (`clazel_style::cascade::ua::Sheets::for_document`), which
//! give the same computed values as the whole sheets: `clazel-style`'s own
//! golden test checks that on every one of these documents. The box tree
//! does not depend on which is used.
//!
//! Not built: the `#document-fragment` cases (the box tree takes a
//! document) and the `scripted_*.dat` cases, which the generated table only
//! counts.
//!
//! To regenerate the fixtures after a deliberate change, run
//! `CLAZEL_BLESS=1 cargo test -p clazel-layout --test golden_boxes` and
//! review the diff before committing it.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;

use clazel_dom::exec::Arena;
use clazel_layout::boxes::dump::dump;
use clazel_layout::boxes::{BoxKind, build};
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

include!("../../clazel-treebuilder/tests/generated/wpt_tree_construction.rs");

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn parse(html: &str) -> Arena {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena
}

/// Counts of the boxes the golden documents produce, by what made them.
#[derive(Default)]
struct Counts {
    boxes: usize,
    anonymous: usize,
    fragments: usize,
    text_runs: usize,
}

/// One document's box tree, printed.
fn print_document(out: &mut String, case: &Case, counts: &mut Counts) {
    let arena = parse(case.data);
    let sources = collect(&arena);
    let device = Device::screen(800, 600);
    let sheets = ua::sheets().for_document(&arena);
    let table = cascade_with(&sheets, &arena, &sources, device);
    let tree = build(&arena, &table);
    for b in &tree.boxes {
        counts.boxes = counts.boxes.saturating_add(1);
        if b.node.is_none() && b.kind != BoxKind::Root {
            counts.anonymous = counts.anonymous.saturating_add(1);
        }
        match &b.kind {
            BoxKind::Inline(f) if !(f.first && f.last) => {
                counts.fragments = counts.fragments.saturating_add(1);
            }
            BoxKind::Text(_) => counts.text_runs = counts.text_runs.saturating_add(1),
            _ => {}
        }
    }
    let _ = writeln!(out, "#case {}", case.index);
    let _ = writeln!(out, "#data {:?}", case.data);
    out.push_str(&dump(&tree, &arena));
    out.push('\n');
}

#[test]
fn golden_box_trees() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/boxes");
    let bless = std::env::var_os("CLAZEL_BLESS").is_some_and(|v| v == "1");
    let mut files: BTreeMap<&str, String> = BTreeMap::new();
    let mut built = 0usize;
    let mut fragments = 0usize;
    let mut counts = Counts::default();
    // Under Miri only case 0, a document (an adoption agency case). Parsing
    // the user agent sheets takes Miri about 73 s per process and each
    // document's cascade about a minute more (`clazel-style`'s golden
    // test), and a test must stay under 300 s; Miri checks for undefined
    // behaviour, not coverage, which the native run gives. The box tree's
    // own code runs under Miri in the unit tests as well.
    let stride = if cfg!(miri) { CASES.len().max(1) } else { 1 };
    for case in CASES.iter().step_by(stride) {
        let out = files.entry(case.file).or_default();
        if case.fragment.is_some() {
            fragments = fragments.saturating_add(1);
            continue;
        }
        print_document(out, case, &mut counts);
        built = built.saturating_add(1);
    }
    // Miri's isolation forbids opening the fixtures, and a sample cannot
    // match a whole file; the comparison runs in the normal test job.
    let compared = if cfg!(miri) { BTreeMap::new() } else { files };
    let mut differ: Vec<String> = Vec::new();
    for (file, text) in &compared {
        if text.is_empty() {
            continue;
        }
        let path = dir.join(file.replace(".dat", ".txt"));
        if bless {
            if let Err(e) = std::fs::create_dir_all(&dir).and_then(|()| std::fs::write(&path, text))
            {
                differ.push(format!("{}: cannot write: {e}", path.display()));
            }
            continue;
        }
        match std::fs::read_to_string(&path) {
            Ok(expected) if expected == *text => {}
            Ok(_) => differ.push(format!(
                "{} differs (CLAZEL_BLESS=1 to regenerate)",
                path.display()
            )),
            Err(e) => differ.push(format!("{}: {e}", path.display())),
        }
    }
    println!(
        "golden: {built} document cases built ({} boxes: {} anonymous, {} split inline fragments, {} text runs); {fragments} fragment cases and {SCRIPTED_NOT_RUN} scripted cases not built",
        counts.boxes, counts.anonymous, counts.fragments, counts.text_runs
    );
    assert!(differ.is_empty(), "golden fixtures: {differ:#?}");
}
