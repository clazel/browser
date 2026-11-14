//! Conformance of the cascade (phase-5.md item 5.7) against WPT `css/css-cascade/`, at the
//! commit `tests/data/wpt-css-cascade/SOURCE.md` names.
//!
//! Each case is one `test()` of a testharness.js page that only reads computed values
//! (`xtask/src/testdata/wpt_css_cascade.rs` says which): the page is parsed by
//! `clazel-treebuilder` (its scripts do not run), its style sources collected and cascaded
//! in WPT's 800 by 600 viewport, and each assertion compares the values
//! `getComputedStyle` would give, serialized as CSSOM does (`serialize`, below), with a
//! literal or with another element's. A case passes when every assertion holds.
//!
//! What `getComputedStyle` gives for `width` and `height` of a rendered element is the used
//! value (CSSOM §9†, "resolved value"), which is layout's; the cases here set them in
//! pixels, where the used value is the computed one.
//!
//! The expected failures, each with its reason, are the cases on properties outside the
//! subset ([`OUTSIDE`]) and those in [`EXPECTED`].

use clazel_dom::exec::{Arena, ExecKind};
use clazel_style::cascade::computed::{
    ComputedStyle, Display, LineHeight, Lp, MaxSize, Overflow, Size, TextAlign, VerticalAlign,
    WhiteSpace,
};
use clazel_style::cascade::{ComputedTable, cascade, cascade_unindexed, cascade_with, hints, ua};
use clazel_style::sources::{Device, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

/// A value an assertion compares.
#[derive(Debug)]
enum Value {
    /// `getComputedStyle(target).property`; an empty target is the root element.
    Computed {
        target: &'static str,
        property: &'static str,
    },
    /// A string literal.
    Literal(&'static str),
}

/// `assert_equals` (`equal`) or `assert_not_equals`.
#[derive(Debug)]
struct Assertion {
    equal: bool,
    left: Value,
    right: Value,
}

/// One `test()`.
#[derive(Debug)]
struct Case {
    page: &'static str,
    line: usize,
    name: &'static str,
    assertions: &'static [Assertion],
}

include!("generated/wpt_css_cascade.rs");

/// Properties `getComputedStyle` is asked for that are not in the subset (phase-5.md
/// 5.0(b)): their cases are expected failures.
const OUTSIDE: &[&str] = &["opacity", "z-index", "position", "left"];

/// Other expected failures, by page and line, with why.
const EXPECTED: &[(&str, usize, &str)] = &[
    (
        "presentational-hints-cascade.html",
        36,
        "`@layer` (CSS Cascade 5) is not in the subset: the layered rule is dropped, so the \
         hint applies",
    ),
    (
        "revert-val-006.html",
        20,
        "CSS Animations are not in the subset: `@keyframes` and `animation` are dropped, so \
         `margin-top: 0px` applies",
    ),
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
    let url: Vec<u32> = "http://web-platform.test/".chars().map(u32::from).collect();
    parse_real(&NoEncodings, &input, url, false, false).0.arena
}

/// The element named by a target: its `id`, or the root element for "".
fn element(arena: &Arena, target: &str) -> Option<usize> {
    if target.is_empty() {
        return arena
            .children(0)
            .iter()
            .copied()
            .find(|&c| matches!(arena.kind(c), ExecKind::Element { .. }));
    }
    (0..arena.len()).find(|&n| match arena.kind(n) {
        ExecKind::Element { attributes, .. } => hints::attribute(attributes, "id")
            .is_some_and(|v| v.iter().copied().eq(target.chars().map(u32::from))),
        _ => false,
    })
}

/// A length in 1/64 px as CSSOM serializes a `px` value.
fn px(v: i32) -> String {
    let n = f64::from(v) / 64.0;
    let mut s = format!("{n:.6}");
    while s.ends_with('0') {
        s.pop();
    }
    if s.ends_with('.') {
        s.pop();
    }
    format!("{s}px")
}

fn rgba(c: [u8; 4]) -> String {
    let [r, g, b, a] = c;
    if a == 255 {
        format!("rgb({r}, {g}, {b})")
    } else {
        let alpha = f64::from(a) / 255.0;
        let mut s = format!("{alpha:.3}");
        while s.ends_with('0') {
            s.pop();
        }
        if s.ends_with('.') {
            s.pop();
        }
        format!("rgba({r}, {g}, {b}, {s})")
    }
}

fn lp(v: Lp) -> String {
    match v {
        Lp::Px64(p) => px(p),
        Lp::Percent(n) => {
            let mut s = format!("{:.6}", n.millionths as f64 / 1e6);
            while s.ends_with('0') {
                s.pop();
            }
            if s.ends_with('.') {
                s.pop();
            }
            format!("{s}%")
        }
    }
}

fn size(v: Size) -> String {
    match v {
        Size::Auto => "auto".into(),
        Size::Lp(l) => lp(l),
    }
}

fn keyword<T: std::fmt::Debug>(v: T) -> String {
    let d = format!("{v:?}");
    let mut out = String::new();
    for (i, c) in d.chars().enumerate() {
        if c.is_ascii_uppercase() {
            if i > 0 {
                out.push('-');
            }
            out.push(c.to_ascii_lowercase());
        } else {
            out.push(c);
        }
    }
    out
}

/// `getComputedStyle(element)[property]` for the properties of the subset the cases read;
/// `None` for others.
fn serialize(s: &ComputedStyle, property: &str) -> Option<String> {
    let side = |i: usize| i;
    Some(match property {
        "color" => rgba(s.color),
        "background-color" => rgba(s.background_color),
        "line-height" => match s.line_height {
            LineHeight::Normal => "normal".into(),
            LineHeight::Number(n) => {
                let mut t = format!("{:.6}", n.millionths as f64 / 1e6);
                while t.ends_with('0') {
                    t.pop();
                }
                if t.ends_with('.') {
                    t.pop();
                }
                t
            }
            LineHeight::Px64(p) => px(p),
        },
        "font-size" => px(s.font_size),
        "width" => size(s.width),
        "height" => size(s.height),
        "max-width" => match s.max_width {
            MaxSize::None => "none".into(),
            MaxSize::Lp(l) => lp(l),
        },
        "margin-top" => size(*s.margin.get(side(0))?),
        "margin-right" => size(*s.margin.get(side(1))?),
        "margin-bottom" => size(*s.margin.get(side(2))?),
        "margin-left" => size(*s.margin.get(side(3))?),
        "padding-top" => lp(*s.padding.first()?),
        "overflow" => {
            if s.overflow_x == s.overflow_y {
                keyword::<Overflow>(s.overflow_x)
            } else {
                format!("{} {}", keyword(s.overflow_x), keyword(s.overflow_y))
            }
        }
        "display" => match s.display {
            Display::InlineBlock => "inline-block".into(),
            d => keyword(d),
        },
        "text-align" => keyword::<TextAlign>(s.text_align),
        "vertical-align" => match s.vertical_align {
            VerticalAlign::Lp(l) => lp(l),
            v => keyword(v),
        },
        "white-space" => keyword::<WhiteSpace>(s.white_space),
        _ => return None,
    })
}

/// A value of the page cascaded into `table`, or why not.
fn value(arena: &Arena, table: &ComputedTable, v: &Value) -> Result<String, String> {
    match v {
        Value::Literal(s) => Ok((*s).to_owned()),
        Value::Computed { target, property } => {
            let e = element(arena, target).ok_or_else(|| format!("no element {target:?}"))?;
            let style = table
                .get(e)
                .ok_or_else(|| format!("{target:?} has no computed style"))?;
            serialize(style, property).ok_or_else(|| format!("{property} is not serialized"))
        }
    }
}

#[test]
fn wpt_css_cascade() {
    let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
    let mut failures = Vec::new();
    // Under Miri every fourth page (the first and fifth of seven) runs: each page costs Miri
    // about a minute, on top of the 73 s the process spends parsing the user agent sheets,
    // and a test must stay under 300 s. The pages run with the sheets cut to the rules that
    // can match them (`ua::Sheets::for_document`), which give the same table (checked
    // natively here and in the golden test). The counts below are checked natively only.
    let stride = if cfg!(miri) { 4 } else { 1 };
    for (page, html) in PAGES.iter().step_by(stride) {
        let arena = parse(html);
        let sources = collect(&arena);
        let device = Device::screen(800, 600);
        let table = if cfg!(miri) {
            cascade_with(&ua::sheets().for_document(&arena), &arena, &sources, device)
        } else {
            let table = cascade(&arena, &sources, device);
            let small = ua::sheets().for_document(&arena);
            assert!(
                table == cascade_with(&small, &arena, &sources, device),
                "{page}: the cut sheets give another table"
            );
            assert!(
                table == cascade_unindexed(&arena, &sources, device),
                "{page}: the rule index gives another table"
            );
            table
        };
        for case in CASES.iter().filter(|c| c.page == *page) {
            let outside = case.assertions.iter().find_map(|a| {
                [&a.left, &a.right].into_iter().find_map(|v| match v {
                    Value::Computed { property, .. } if OUTSIDE.contains(property) => {
                        Some(*property)
                    }
                    _ => None,
                })
            });
            let listed = EXPECTED
                .iter()
                .find(|(p, l, _)| p == page && *l == case.line)
                .map(|(_, _, why)| *why);
            let mut ok = true;
            let mut why = String::new();
            for a in case.assertions {
                let (l, r) = (
                    value(&arena, &table, &a.left),
                    value(&arena, &table, &a.right),
                );
                let holds = match (&l, &r) {
                    (Ok(l), Ok(r)) => (l == r) == a.equal,
                    _ => false,
                };
                if !holds {
                    ok = false;
                    why = format!(
                        "{} {l:?} {} {r:?}",
                        if a.equal { "want" } else { "want not" },
                        if a.equal { "==" } else { "!=" }
                    );
                    break;
                }
            }
            let label = format!("{page}:{} {:?}", case.line, case.name);
            match (ok, outside, listed) {
                (true, None, None) => pass = pass.saturating_add(1),
                (true, _, _) => {
                    fail = fail.saturating_add(1);
                    failures.push(format!(
                        "{label}: passes, but is listed as an expected failure"
                    ));
                }
                (false, Some(p), _) => {
                    xfail = xfail.saturating_add(1);
                    println!("expected failure: {label}: `{p}` is not in the subset");
                }
                (false, None, Some(reason)) => {
                    xfail = xfail.saturating_add(1);
                    println!("expected failure: {label}: {reason}");
                }
                (false, None, None) => {
                    fail = fail.saturating_add(1);
                    failures.push(format!("{label}: {why}"));
                }
            }
        }
    }
    for (page, line, why) in NOT_RUN {
        println!("not run: {page}:{line}: {why}");
    }
    println!(
        "clazel-conformance: suite=\"WPT css-cascade/ computed values\" pass={pass} xfail={xfail} fail={fail} total={}",
        CASES.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
    if !cfg!(miri) {
        assert_eq!(pass.saturating_add(xfail).saturating_add(fail), CASES.len());
    }
}
