//! The golden table of computed values (phase-5.md item 5.7: "a golden table of computed
//! values for 4.1's vendored documents under the UA sheet, reviewed as fixtures").
//!
//! Every document case of the html5lib tree-construction suite vendored in
//! `clazel-treebuilder` (read through the table `cargo xtask testdata` generates from it, as
//! `clazel-text`'s golden test does) is parsed with scripting off, its style sources
//! collected (its `style` elements and attributes; no linked sheet is fetched) and cascaded
//! in an 800 by 600 viewport. Each element is printed in tree order, indented by depth,
//! with the computed values that differ from what it would have with no declarations at all:
//! for an inherited property, its parent's value; for any other, the initial value. That is
//! what the user agent sheet, the presentational hints and the documents' own style did.
//! The output of each `.dat` file is compared byte for byte with
//! `tests/golden/cascade/<file>.txt`; any difference fails the test.
//!
//! Each document is cascaded with the user agent sheets cut to the rules that can match it
//! (`clazel_style::cascade::ua::Sheets::for_document`), and, except under Miri, also with
//! the whole sheets, and the two tables must be equal.
//!
//! Not cascaded: the `#document-fragment` cases (the cascade takes a document) and the
//! `scripted_*.dat` cases, which the generated table only counts.
//!
//! To regenerate the fixtures after a deliberate change, run
//! `CLAZEL_BLESS=1 cargo test -p clazel-style --test golden_cascade` and review the diff
//! before committing it.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::{
    ComputedStyle, Family, LineHeight, ListStyleType, Lp, MaxSize, Size, VerticalAlign,
};
use clazel_style::cascade::{ComputedTable, cascade, cascade_with, tree_order, ua};
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

fn text(s: &[u32]) -> String {
    s.iter().filter_map(|&c| char::from_u32(c)).collect()
}

fn px(v: i32) -> String {
    let n = f64::from(v) / 64.0;
    let s = format!("{n:.4}");
    let s = s.trim_end_matches('0').trim_end_matches('.');
    format!("{s}px")
}

fn num(millionths: i64) -> String {
    let s = format!("{:.6}", millionths as f64 / 1e6);
    s.trim_end_matches('0').trim_end_matches('.').to_owned()
}

fn lp(v: Lp) -> String {
    match v {
        Lp::Px64(p) => px(p),
        Lp::Percent(n) => format!("{}%", num(n.millionths)),
    }
}

fn size(v: Size) -> String {
    match v {
        Size::Auto => "auto".into(),
        Size::Lp(l) => lp(l),
    }
}

fn rgba(c: [u8; 4]) -> String {
    let [r, g, b, a] = c;
    format!("#{r:02x}{g:02x}{b:02x}{a:02x}")
}

/// Every applied property of `s`, by name, with whether it is inherited.
fn describe(s: &ComputedStyle, table: &ComputedTable) -> Vec<(String, String, bool)> {
    let mut out: Vec<(String, String, bool)> = vec![
        ("color".into(), rgba(s.color), true),
        ("background-color".into(), rgba(s.background_color), false),
    ];
    let sides = ["top", "right", "bottom", "left"];
    for ((((side, m), p), w), (st, c)) in sides
        .iter()
        .zip(s.margin)
        .zip(s.padding)
        .zip(s.border_width)
        .zip(s.border_style.iter().zip(s.border_color))
    {
        out.push((format!("margin-{side}"), size(m), false));
        out.push((format!("padding-{side}"), lp(p), false));
        out.push((format!("border-{side}-width"), px(w), false));
        out.push((format!("border-{side}-style"), format!("{st:?}"), false));
        out.push((format!("border-{side}-color"), rgba(c), false));
    }
    let max = |m: MaxSize| match m {
        MaxSize::None => "none".to_owned(),
        MaxSize::Lp(l) => lp(l),
    };
    let families: Vec<String> = table
        .family(s)
        .iter()
        .map(|f| match f {
            Family::Name(n) => format!("{:?}", text(n)),
            Family::Generic(g) => (*g).to_owned(),
        })
        .collect();
    let [spacing_h, spacing_v] = s.border_spacing;
    let rest: Vec<(&str, String, bool)> = vec![
        ("width", size(s.width), false),
        ("height", size(s.height), false),
        ("min-width", size(s.min_width), false),
        ("min-height", size(s.min_height), false),
        ("max-width", max(s.max_width), false),
        ("max-height", max(s.max_height), false),
        ("display", format!("{:?}", s.display), false),
        ("overflow-x", format!("{:?}", s.overflow_x), false),
        ("overflow-y", format!("{:?}", s.overflow_y), false),
        ("visibility", format!("{:?}", s.visibility), true),
        ("font-family", families.join(", "), true),
        ("font-size", px(s.font_size), true),
        ("font-weight", num(s.font_weight.millionths), true),
        ("font-style", format!("{:?}", s.font_style), true),
        (
            "line-height",
            match s.line_height {
                LineHeight::Normal => "normal".to_owned(),
                LineHeight::Number(n) => num(n.millionths),
                LineHeight::Px64(p) => px(p),
            },
            true,
        ),
        (
            "vertical-align",
            match s.vertical_align {
                VerticalAlign::Lp(l) => lp(l),
                v => format!("{v:?}"),
            },
            false,
        ),
        ("text-align", format!("{:?}", s.text_align), true),
        (
            "text-decoration-line",
            format!("{:?}", s.text_decoration_line),
            false,
        ),
        (
            "text-decoration-style",
            format!("{:?}", s.text_decoration_style),
            false,
        ),
        (
            "text-decoration-color",
            rgba(s.text_decoration_color),
            false,
        ),
        ("text-indent", format!("{:?}", s.text_indent), true),
        ("white-space", format!("{:?}", s.white_space), true),
        ("overflow-wrap", format!("{:?}", s.overflow_wrap), true),
        ("word-break", format!("{:?}", s.word_break), true),
        (
            "border-spacing",
            format!("{} {}", px(spacing_h), px(spacing_v)),
            true,
        ),
        ("border-collapse", format!("{}", s.border_collapse), true),
        (
            "table-layout-fixed",
            format!("{}", s.table_layout_fixed),
            false,
        ),
        (
            "list-style-type",
            match &s.list_style_type {
                ListStyleType::None => "none".to_owned(),
                ListStyleType::Named(n) => (*n).to_owned(),
                ListStyleType::Custom(n) => text(n),
                ListStyleType::String(t) => format!("{:?}", text(t)),
            },
            true,
        ),
        (
            "align-descendants",
            format!("{:?}", s.align_descendants),
            false,
        ),
    ];
    out.extend(rest.into_iter().map(|(n, v, i)| (n.to_owned(), v, i)));
    out
}

/// The element's computed values that differ from its unstyled ones.
fn differences(s: &ComputedStyle, parent: &ComputedStyle, table: &ComputedTable) -> Vec<String> {
    let mut initial = ComputedStyle::initial();
    // `currentcolor`'s initial values are the element's own colour.
    initial.border_color = [s.color; 4];
    initial.text_decoration_color = s.color;
    let own = describe(s, table);
    let from_parent = describe(parent, table);
    let from_initial = describe(&initial, table);
    own.iter()
        .zip(from_parent.iter().zip(&from_initial))
        .filter(
            |((_, v, inherited), ((_, p, _), (_, i, _)))| {
                if *inherited { v != p } else { v != i }
            },
        )
        .map(|((name, v, _), _)| format!("{name}={v}"))
        .collect()
}

/// One document's computed values, printed.
fn print_document(out: &mut String, case: &Case) {
    let arena = parse(case.data);
    let sources = collect(&arena);
    let device = Device::screen(800, 600);
    // The user agent sheets cut to the rules that can match the document
    // (`ua::Sheets::for_document`) give the same table as the whole sheets: checked here,
    // natively, on every document. Under Miri only the cut sheets are used.
    let small = ua::sheets().for_document(&arena);
    let table = cascade_with(&small, &arena, &sources, device);
    if !cfg!(miri) {
        assert!(
            table == cascade(&arena, &sources, device),
            "case {}: the cut sheets give another table",
            case.index
        );
    }
    let _ = writeln!(out, "#case {}", case.index);
    let _ = writeln!(out, "#data {:?}", case.data);
    let initial = ComputedStyle::initial();
    for n in tree_order(&arena) {
        let ExecKind::Element { local_name, .. } = arena.kind(n) else {
            continue;
        };
        let Some(style) = table.get(n) else { continue };
        let mut depth = 0usize;
        let mut p = arena.parent(n);
        let mut parent_style = None;
        while let Some(id) = p {
            if parent_style.is_none() {
                parent_style = table.get(id);
            }
            depth = depth.saturating_add(1);
            p = arena.parent(id);
        }
        let parent = parent_style.unwrap_or(&initial);
        let diffs = differences(style, parent, &table);
        let indent = "  ".repeat(depth.saturating_sub(1));
        let _ = write!(out, "{indent}<{}>", text(local_name));
        for d in diffs {
            let _ = write!(out, " {d}");
        }
        out.push('\n');
    }
    out.push('\n');
}

#[test]
fn golden_computed_values() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/golden/cascade");
    let bless = std::env::var_os("CLAZEL_BLESS").is_some_and(|v| v == "1");
    let mut files: BTreeMap<&str, String> = BTreeMap::new();
    let mut cascaded = 0usize;
    let mut fragments = 0usize;
    // Under Miri every 900th case: cases 0 and 900 are documents (an adoption agency case,
    // and a table of links), 1800 a fragment. Each document costs Miri about a minute
    // (preparing the cut user agent sheets' selectors and matching them), on top of the 73 s
    // the process spends parsing the sheets, and a test must stay under 300 s; Miri checks
    // for undefined behaviour, not coverage, which the native run gives.
    let stride = if cfg!(miri) { 900 } else { 1 };
    for case in CASES.iter().step_by(stride) {
        let out = files.entry(case.file).or_default();
        if case.fragment.is_some() {
            fragments = fragments.saturating_add(1);
            continue;
        }
        print_document(out, case);
        cascaded = cascaded.saturating_add(1);
    }
    // Miri's isolation forbids opening the fixtures, and a sample cannot match a whole
    // file; the comparison runs in the normal test job.
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
        "golden: {cascaded} document cases cascaded; {fragments} fragment cases and {SCRIPTED_NOT_RUN} scripted cases not cascaded"
    );
    assert!(differ.is_empty(), "golden fixtures: {differ:#?}");
}
