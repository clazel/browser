//! The golden test (Phase 4 item 4.14): every document case of the
//! html5lib tree-construction suite vendored in `clazel-treebuilder`
//! (`crates/clazel-treebuilder/tests/data/wpt-tree-construction/`, read
//! through the table `cargo xtask testdata` generates from it,
//! `crates/clazel-treebuilder/tests/generated/wpt_tree_construction.rs`,
//! as that crate's conformance test does) is parsed by
//! `exec::driver::parse_real` with scripting off (the browser's setting,
//! also for `#script-on` cases), laid out at width [`WIDTH`] with
//! [`clazel_text::layout`], and printed. The output of each `.dat` file is
//! compared byte for byte with `tests/golden/<file>.txt`; any difference
//! fails the test.
//!
//! Not laid out: the `#document-fragment` cases (the layout takes a
//! document, not a fragment; they are counted and reported), and the
//! `scripted_*.dat` cases, which the generated table only counts.
//!
//! The bound of the crate docs is checked on every case too.
//!
//! To regenerate the fixtures after a deliberate change, run
//! `CLAZEL_BLESS=1 cargo test -p clazel-text --test golden` and review the
//! diff before committing it.

mod support;

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;

include!("../../clazel-treebuilder/tests/generated/wpt_tree_construction.rs");

/// The width of the golden layouts.
const WIDTH: usize = 80;

/// One case's printed layout.
fn print_case(out: &mut String, case: &Case, page: &clazel_text::Page) {
    let _ = writeln!(out, "#case {}", case.index);
    let _ = writeln!(out, "#data {:?}", case.data);
    let _ = writeln!(out, "#title {:?}", page.title);
    let _ = writeln!(out, "#lines {}", page.lines.len());
    for l in &page.lines {
        let _ = writeln!(out, "{l:?}");
    }
    let _ = writeln!(out, "#links {}", page.links.len());
    for (i, l) in page.links.iter().enumerate() {
        let _ = writeln!(out, "{} {l:?}", i.saturating_add(1));
    }
    out.push('\n');
}

#[test]
fn golden_layouts() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    let bless = std::env::var_os("CLAZEL_BLESS").is_some_and(|v| v == "1");
    let mut files: BTreeMap<&str, String> = BTreeMap::new();
    let mut laid_out = 0usize;
    let mut fragments = 0usize;
    let mut bound_failures: Vec<String> = Vec::new();
    for case in CASES {
        let out = files.entry(case.file).or_default();
        if case.fragment.is_some() {
            fragments = fragments.saturating_add(1);
            continue;
        }
        let doc = support::parse(case.data);
        let page = clazel_text::layout(&doc, WIDTH);
        if let Err(e) = support::check_bound(&doc, &page, WIDTH) {
            bound_failures.push(format!("{}:{} {e}", case.file, case.index));
        }
        print_case(out, case, &page);
        laid_out = laid_out.saturating_add(1);
    }
    let mut differ: Vec<String> = Vec::new();
    for (file, text) in &files {
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
        "golden: {laid_out} document cases laid out at width {WIDTH}; {fragments} fragment cases and {SCRIPTED_NOT_RUN} scripted cases not laid out"
    );
    assert!(
        bound_failures.is_empty(),
        "bound fails: {bound_failures:#?}"
    );
    assert!(differ.is_empty(), "golden fixtures: {differ:#?}");
}
