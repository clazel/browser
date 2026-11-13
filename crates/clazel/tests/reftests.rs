//! The reftest runner's pure parts (phase-5.md item 5.25), tested on their
//! own: the reftests themselves wait for `browse --headless` (item 5.23's
//! headless mode) and the vendored WPT directories (item 5.1), so no WPT test
//! is run here and none is counted.

mod reftest;

use reftest::classify::{NotRun, classify};
use reftest::meta::{Fuzzy, MetaError, Reference, Relation, parse_fuzzy, read, resolve};
use reftest::pixels::{Image, differences, equal, passes};
use reftest::runner::{Outcome, Render, run};

fn image(w: u32, h: u32, rgba: [u8; 4]) -> Image {
    Image {
        width: w,
        height: h,
        rgba: rgba.repeat(usize::try_from(w.saturating_mul(h)).unwrap_or(0)),
    }
}

fn set(i: &mut Image, x: u32, y: u32, rgba: [u8; 4]) {
    let at = y
        .saturating_mul(i.width)
        .saturating_add(x)
        .saturating_mul(4);
    let at = usize::try_from(at).unwrap_or(usize::MAX);
    if let Some(p) = i.rgba.get_mut(at..at.saturating_add(4)) {
        p.copy_from_slice(&rgba);
    }
}

// ---- meta ----

/// `<link rel=match|mismatch>` in document order, `href`s stripped and
/// resolved against the test's directory; other `rel`s ignored (WPT matches
/// the attribute's whole value).
#[test]
fn references_are_found() {
    let page = b"<!DOCTYPE html><link rel=help href=x><link rel=match href=' ref/a-ref.html '>\
                 <link rel=mismatch href='../b-notref.html'><link rel='match stylesheet' href=c.html>";
    let meta = read("css/CSS2/box/t.html", page);
    assert_eq!(
        meta.map(|m| m.references),
        Ok(vec![
            Reference {
                path: "css/CSS2/box/ref/a-ref.html".to_owned(),
                relation: Relation::Match
            },
            Reference {
                path: "css/CSS2/b-notref.html".to_owned(),
                relation: Relation::Mismatch
            },
        ])
    );
    assert_eq!(resolve("a/b/c.html", "/x/y.html#f"), "x/y.html");
}

/// WPT's `fuzzy` forms: named or positional, `N` (exactly) or `N-M`, and a
/// reference key before the last `:`.
#[test]
fn fuzzy_forms() {
    let f = |a: (u64, u64), b: (u64, u64)| Fuzzy {
        max_difference: a,
        total_pixels: b,
    };
    assert_eq!(
        parse_fuzzy("maxDifference=15;totalPixels=300"),
        Ok((None, f((15, 15), (300, 300))))
    );
    assert_eq!(parse_fuzzy("15;300"), Ok((None, f((15, 15), (300, 300)))));
    assert_eq!(
        parse_fuzzy("10-15;200-300"),
        Ok((None, f((10, 15), (200, 300))))
    );
    assert_eq!(
        parse_fuzzy("totalPixels=200-300;maxDifference=10-15"),
        Ok((None, f((10, 15), (200, 300))))
    );
    assert_eq!(
        parse_fuzzy("option1-ref.html:10-15;200-300"),
        Ok((Some("option1-ref.html".to_owned()), f((10, 15), (200, 300))))
    );
    assert!(matches!(parse_fuzzy("15"), Err(MetaError::Malformed(_))));
    assert!(matches!(
        parse_fuzzy("size=1;2"),
        Err(MetaError::Malformed(_))
    ));
    assert!(matches!(
        parse_fuzzy("maxDifference=1;maxDifference=2"),
        Err(MetaError::Malformed(_))
    ));
}

/// A keyed `fuzzy` applies to its reference, an unkeyed one to the others;
/// a key naming no reference is an error.
#[test]
fn fuzzy_per_reference() {
    let page = b"<link rel=match href=a.html><link rel=match href=b.html>\
                 <meta name=fuzzy content='a.html:0-2;0-10'><meta name=fuzzy content='5;6'>";
    let meta = read("t/x.html", page);
    let get = |p: &str| meta.as_ref().ok().and_then(|m| m.fuzzy_for(p));
    assert_eq!(get("t/a.html").map(|f| f.max_difference), Some((0, 2)));
    assert_eq!(get("t/b.html").map(|f| f.max_difference), Some((5, 5)));
    let bad = read(
        "t/x.html",
        b"<link rel=match href=a.html><meta name=fuzzy content='z.html:1;1'>",
    );
    assert!(matches!(bad, Err(MetaError::UnknownReference(_))));
}

// ---- pixels ----

/// wptrunner's difference: only pixels whose difference has a luminance
/// above 0 count, and alpha is ignored; a red difference of 1 alone has
/// luminance (19595 + 0x8000) >> 16 = 0, a green one of 1 has 1.
#[test]
fn the_difference_is_wptrunners() {
    let a = image(3, 2, [10, 10, 10, 255]);
    let mut b = a.clone();
    set(&mut b, 0, 0, [11, 10, 10, 255]);
    set(&mut b, 1, 0, [10, 11, 10, 255]);
    set(&mut b, 2, 1, [10, 10, 40, 0]);
    // (1,0,0): luminance 0, not counted; (0,1,0): counted, max 1;
    // (0,0,30): luminance (30·7471 + 0x8000) >> 16 = 3, counted, max 30.
    assert_eq!(differences(&a, &b), Some((30, 2)));
    assert_eq!(differences(&a, &image(2, 3, [0; 4])), None);
}

/// `check_pass`'s rule: exact without fuzziness; inclusive ranges with it,
/// with its two shortcuts for a zero lower bound.
#[test]
fn the_fuzzy_rule() {
    let f = |a: (u64, u64), b: (u64, u64)| {
        Some(Fuzzy {
            max_difference: a,
            total_pixels: b,
        })
    };
    assert!(equal(0, 0, None));
    assert!(!equal(1, 1, None));
    assert!(!equal(1, 1, f((0, 0), (0, 0))));
    assert!(equal(15, 300, f((15, 15), (300, 300))));
    assert!(!equal(14, 300, f((15, 15), (300, 300))));
    assert!(equal(12, 250, f((10, 15), (200, 300))));
    assert!(!equal(12, 301, f((10, 15), (200, 300))));
    // "(pixels_different == 0 and allowed_different[0] == 0)": identical
    // images pass a range starting at 0.
    assert!(equal(0, 0, f((1, 5), (0, 10))));
    // A range that excludes 0 fails identical images.
    assert!(!equal(0, 0, f((1, 5), (1, 10))));
    let a = image(2, 2, [0, 0, 0, 255]);
    let mut b = a.clone();
    set(&mut b, 0, 0, [0, 40, 0, 255]);
    assert!(passes(&a, &a, Relation::Match, None));
    assert!(!passes(&a, &b, Relation::Match, None));
    assert!(passes(&a, &b, Relation::Mismatch, None));
    assert!(passes(&a, &b, Relation::Match, f((0, 40), (0, 1))));
}

// ---- classify ----

/// Not run, by reason, in order: print, XHTML, script, images, outside the subset.
#[test]
fn not_run_by_reason() {
    let c = |path: &str, html: &str| classify(path, html.as_bytes());
    assert_eq!(c("css/CSS2/a-print.html", "<p>x"), Some(NotRun::Print));
    assert_eq!(c("css/a.xht", "<p>x"), Some(NotRun::Xhtml));
    assert_eq!(c("css/a-print.xht", "<p>x"), Some(NotRun::Print));
    assert_eq!(
        c("css/a.html", "<script>1</script><img src=x>"),
        Some(NotRun::Script)
    );
    assert_eq!(
        c("css/a.html", "<html class='reftest-wait'><p>x"),
        Some(NotRun::Script)
    );
    assert_eq!(
        c("css/a.html", "<img src=a.png>"),
        Some(NotRun::Images("img".to_owned()))
    );
    assert_eq!(
        c("css/a.html", "<div style='background: url(a.png)'>x</div>"),
        Some(NotRun::Images("url( in a style attribute".to_owned()))
    );
    assert_eq!(
        c("css/a.html", "<style>div { float: left }</style>"),
        Some(NotRun::OutsideSubset("float".to_owned()))
    );
    assert_eq!(
        c("css/a.html", "<div style='transform: rotate(1deg)'>x</div>"),
        Some(NotRun::OutsideSubset("transform".to_owned()))
    );
    assert_eq!(
        c("css/a.html", "<style>div { display: flex }</style>"),
        Some(NotRun::OutsideSubset("display: a value".to_owned()))
    );
    assert!(matches!(
        c("css/a.html", "<style>@font-face { font-family: x }</style>"),
        Some(NotRun::OutsideSubset(_))
    ));
    // In the subset: a table, a background colour, margins.
    assert_eq!(
        c(
            "css/a.html",
            "<style>td { background: green; margin: 1px } table { border-spacing: 2px }</style><table><td>x</table>"
        ),
        None
    );
}

// ---- the runner, with a renderer given as a parameter ----

/// A renderer whose screenshots are given per path.
struct Fake(Vec<(String, Image)>);

impl Render for Fake {
    fn render(&mut self, path: &str, _bytes: &[u8]) -> Result<Image, String> {
        self.0
            .iter()
            .find(|(p, _)| p == path)
            .map(|(_, i)| i.clone())
            .ok_or_else(|| format!("{path}: no screenshot"))
    }
}

/// The multiple references rule: at least one match must match, every
/// mismatch must mismatch; and not run, missing files and non-reftests.
#[test]
fn the_runner() {
    let green = image(4, 4, [0, 128, 0, 255]);
    let red = image(4, 4, [255, 0, 0, 255]);
    let files: Vec<(&str, &str)> = vec![
        ("t/one.html", "<link rel=match href=green.html><p>"),
        (
            "t/two.html",
            "<link rel=match href=red.html><link rel=match href=green.html><p>",
        ),
        (
            "t/three.html",
            "<link rel=match href=green.html><link rel=mismatch href=green2.html><p>",
        ),
        ("t/four.html", "<link rel=match href=red.html><p>"),
        ("t/five.html", "<link rel=match href=script.html><p>"),
        ("t/six.html", "<p>no reference"),
        ("t/green.html", "<p>"),
        ("t/green2.html", "<p>"),
        ("t/red.html", "<p>"),
        ("t/script.html", "<script></script>"),
    ];
    let read_file = |p: &str| {
        files
            .iter()
            .find(|(q, _)| *q == p)
            .map(|(_, b)| b.as_bytes().to_vec())
    };
    let mut fake = Fake(
        [
            ("t/one.html", &green),
            ("t/two.html", &green),
            ("t/three.html", &green),
            ("t/four.html", &green),
            ("t/green.html", &green),
            ("t/green2.html", &green),
            ("t/red.html", &red),
        ]
        .iter()
        .map(|(p, i)| ((*p).to_owned(), (*i).clone()))
        .collect(),
    );
    assert_eq!(run("t/one.html", &read_file, &mut fake), Outcome::Pass);
    // One of two matches suffices.
    assert_eq!(run("t/two.html", &read_file, &mut fake), Outcome::Pass);
    // A mismatch that matches fails the test.
    assert!(matches!(
        run("t/three.html", &read_file, &mut fake),
        Outcome::Fail { .. }
    ));
    assert_eq!(
        run("t/four.html", &read_file, &mut fake),
        Outcome::Fail {
            reference: "t/red.html".to_owned(),
            difference: Some((255, 16)),
        }
    );
    assert_eq!(
        run("t/five.html", &read_file, &mut fake),
        Outcome::NotRun(NotRun::Script)
    );
    assert_eq!(
        run("t/six.html", &read_file, &mut fake),
        Outcome::NotAReftest
    );
    assert!(matches!(
        run("t/none.html", &read_file, &mut fake),
        Outcome::Error(_)
    ));
}
