//! The golden display list dumps (phase-5.md item 5.16), made the way item
//! 5.14's golden fragment trees are (`tests/golden_flow.rs`), from the same
//! documents laid out the same way, then painted at scale 1 with links
//! resolved against `http://example.com/dir/page`.
//!
//! Every document case of the html5lib tree-construction suite vendored in
//! `clazel-treebuilder`, and the pages of `tests/golden/flow/pages/` (our
//! own: an HN-shaped table page in quirks mode, and a page of margins,
//! lists and lines in no-quirks mode), is parsed with scripting off,
//! cascaded in an 800 by 600 viewport with `clazel_style::cascade` (item
//! 5.7) under the user agent sheets, built into a box tree (item 5.13) and
//! laid out with `clazel_layout::flow::layout` in real fonts: the TrueType
//! faces item 5.9 vendored in `clazel-font` (DejaVu Serif and Source Serif
//! 4), matched by item 5.10 with Linux's generic families (so `serif` is
//! DejaVu Serif on every OS, and a family the table lacks falls back to the
//! table's first face) and shaped by item 5.11. Each display list is
//! printed with `paint::dump::dump`; the output of each `.dat` file and each
//! page is compared byte for byte with `tests/golden/paint/<name>.txt`.
//!
//! Not laid out: the `#document-fragment` cases and the `scripted_*.dat`
//! cases, as for the box trees.
//!
//! To regenerate the fixtures after a deliberate change, run
//! `CLAZEL_BLESS=1 cargo test -p clazel-layout --test golden_paint` and
//! review the diff before committing it.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;

use clazel_dom::exec::Arena;
use clazel_font::Face;
use clazel_layout::boxes::build;
use clazel_layout::flow::{FaceFonts, Viewport, layout};
use clazel_layout::fonts::{FaceInfo, FontTable, Generics, Os};
use clazel_layout::paint::dump::dump;
use clazel_layout::paint::paint;
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

include!("../../clazel-treebuilder/tests/generated/wpt_tree_construction.rs");

const DEJAVU_SERIF: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf");
const SOURCE_SERIF: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-source-serif/SourceSerif4-Regular.ttf");

/// Our own pages, by name.
const PAGES: &[(&str, &str)] = &[
    (
        "table-news",
        include_str!("golden/flow/pages/table-news.html"),
    ),
    ("margins", include_str!("golden/flow/pages/margins.html")),
];

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

/// Counts of what the documents produce.
#[derive(Default)]
struct Counts {
    items: usize,
    texts: usize,
    hits: usize,
}

/// One document's fragment tree, printed.
fn print_document(
    out: &mut String,
    html: &str,
    faces: &[Face<'_>],
    table: &FontTable,
    counts: &mut Counts,
) {
    let arena = parse(html);
    let sources = collect(&arena);
    let device = Device::screen(800, 600);
    let sheets = ua::sheets().for_document(&arena);
    let computed = cascade_with(&sheets, &arena, &sources, device);
    let tree = build(&arena, &computed);
    let generics = Generics::for_os(Os::Linux);
    let fonts = FaceFonts {
        table,
        generics: &generics,
        faces,
        families: &computed.families,
    };
    let f = layout(&tree, &arena, &computed, &fonts, Viewport::px(800, 600));
    let url: Vec<u32> = "http://example.com/dir/page"
        .chars()
        .map(u32::from)
        .collect();
    let base = clazel_url::url::parse::basic_url_parser(&url, None);
    let list = paint(&f, &tree, &arena, &computed, &fonts, base.as_ref(), 1);
    counts.items = counts.items.saturating_add(list.items.len());
    counts.texts = counts.texts.saturating_add(
        list.items
            .iter()
            .filter(|i| matches!(i, clazel_layout::paint::Item::Text { .. }))
            .count(),
    );
    counts.hits = counts.hits.saturating_add(list.hits.len());
    out.push_str(&dump(&list));
}

#[test]
fn golden_display_lists() -> Result<(), clazel_font::Error> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/paint");
    let bless = std::env::var_os("CLAZEL_BLESS").is_some_and(|v| v == "1");
    let faces = [Face::parse(DEJAVU_SERIF, 0)?, Face::parse(SOURCE_SERIF, 0)?];
    let mut table = FontTable::new();
    for f in &faces {
        table.push(FaceInfo::from_face(f).ok_or(clazel_font::Error::Truncated)?);
    }
    let mut files: BTreeMap<String, String> = BTreeMap::new();
    let mut built = 0usize;
    let mut counts = Counts::default();
    // Under Miri only case 0 and no page: parsing the user agent sheets and
    // one cascade take Miri about two minutes (item 5.13's golden test), and
    // a test must stay under 300 s. Miri looks for undefined behaviour; the
    // native run gives the coverage, and the unit tests run the layout
    // under Miri as well.
    let stride = if cfg!(miri) { CASES.len().max(1) } else { 1 };
    for case in CASES.iter().step_by(stride) {
        let out = files.entry(case.file.replace(".dat", ".txt")).or_default();
        if case.fragment.is_some() {
            continue;
        }
        let _ = writeln!(out, "#case {}", case.index);
        let _ = writeln!(out, "#data {:?}", case.data);
        print_document(out, case.data, &faces, &table, &mut counts);
        out.push('\n');
        built = built.saturating_add(1);
    }
    let pages = if cfg!(miri) { &[][..] } else { PAGES };
    for (name, html) in pages {
        let out = files.entry(format!("page-{name}.txt")).or_default();
        print_document(out, html, &faces, &table, &mut counts);
        built = built.saturating_add(1);
    }
    // Miri's isolation forbids opening the fixtures; the comparison runs in
    // the normal test job.
    let compared = if cfg!(miri) { BTreeMap::new() } else { files };
    let mut differ: Vec<String> = Vec::new();
    for (file, text) in &compared {
        if text.is_empty() {
            continue;
        }
        let path = dir.join(file);
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
        "golden: {built} documents painted ({} items, {} text items, {} hit regions)",
        counts.items, counts.texts, counts.hits
    );
    assert!(differ.is_empty(), "golden fixtures: {differ:#?}");
    Ok(())
}
