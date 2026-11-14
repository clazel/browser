//! Media queries against WPT `css/mediaqueries/` (phase-5.md item 5.8).
//!
//! **`test_media_queries.html`.** Each unit is one helper call the converter read, run as the
//! page's helpers run it, on a screen whose viewport is the page's iframe at that point:
//!
//! - `query_applies(q)` sets `q` as a `style` element's `media` attribute, so it is HTML's
//!   "matches the environment" ([`matches_environment`]);
//! - `query_is_parseable(q)` parses the sheet `@media screen, q {}`, which must give one
//!   `@media` rule, and asks that its media list not serialize as `screen, not all`;
//! - `expression_is_known(e)` is `query_applies("(e), not all and (e)")`, which is true
//!   exactly when `(e)` is true or false rather than unknown;
//! - `should_apply`, `should_not_apply`, `query_should_be_parseable`,
//!   `query_should_not_be_parseable` and `expression_should_be_known` assert one of these,
//!   and `expression_should_be_unknown` asserts both that `(e)` is parseable and that it is
//!   not known (two WPT tests, one unit here).
//!
//! **`match-media-parsing.html`.** Each unit is one `test_parsing(query, expected)`: the list
//! parsed and serialized must be `expected`.
//!
//! **Reftests.** Each unit is one `@media` rule of a page: the page's `style` elements are
//! parsed as sheets, and each `@media` rule must be active in WPT's 800 by 600 viewport
//! exactly when its block paints green (see the converter and `SOURCE.md`).
//!
//! A unit that fails is an expected failure only if its query names a media feature or a
//! unit outside the subset (the table below gives the reason); any other failure fails the
//! test. Calls the converter did not read are listed, not counted.

use clazel_style::sources::media::{Device, matches_environment, serialize};
use clazel_style::sources::sheet::StyleSheet;

/// One helper call of `test_media_queries.html`.
struct Case {
    line: usize,
    helper: &'static str,
    input: &'static str,
    width: u32,
    height: u32,
}

/// One `test_parsing` call of `match-media-parsing.html`.
struct Parsing {
    line: usize,
    query: &'static str,
    expected: &'static str,
}

/// One reftest page.
struct Page {
    file: &'static str,
    sheets: &'static [&'static str],
    media: &'static [(usize, bool)],
}

include!("generated/wpt_mediaqueries.rs");

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Media features and units the queries name that are outside the subset (phase-5.md item
/// 5.8: `width`, `height`, their `min-` and `max-` forms, and `orientation`), so that this
/// implementation reads them as unknown, which makes the query false and the feature "not
/// known". Matched as a feature name after `(` (with any `min-` or `max-`), or as a unit
/// after a digit.
const OUTSIDE_FEATURES: &[&str] = &[
    "any-hover",
    "any-pointer",
    "aspect-ratio",
    "color-index",
    "color",
    "device-aspect-ratio",
    "device-height",
    "device-width",
    "grid",
    "hover",
    "monochrome",
    "overflow-block",
    "overflow-inline",
    "pointer",
    "resolution",
    "scan",
    "update",
];

/// Length units outside `values/`'s subset.
const OUTSIDE_UNITS: &[&str] = &["ch", "ic", "vw", "vh", "vmin", "vmax"];

/// Why a failing unit on `query` is expected, if it is.
fn reason(query: &str) -> Option<String> {
    let lower = query.to_ascii_lowercase();
    let bytes = lower.as_bytes();
    // Feature names: an identifier after `(` and optional whitespace, or the start of an
    // expression helper's argument.
    let mut names: Vec<&str> = Vec::new();
    let is_name = |b: u8| b.is_ascii_alphanumeric() || b == b'-';
    let mut i = 0usize;
    while i < bytes.len() {
        let starts = i == 0 || bytes.get(i.wrapping_sub(1)).is_some_and(|&b| !is_name(b));
        if starts && bytes.get(i).is_some_and(|&b| is_name(b)) {
            let mut j = i;
            while bytes.get(j).is_some_and(|&b| is_name(b)) {
                j = j.saturating_add(1);
            }
            if let Some(w) = lower.get(i..j) {
                names.push(w);
            }
            i = j;
        } else {
            i = i.saturating_add(1);
        }
    }
    for w in &names {
        let bare = w
            .strip_prefix("min-")
            .or_else(|| w.strip_prefix("max-"))
            .unwrap_or(w);
        if OUTSIDE_FEATURES.contains(&bare) {
            return Some(format!(
                "the media feature `{bare}` is outside the subset (phase-5.md item 5.8), so it is unknown"
            ));
        }
        let unit = w.trim_start_matches(|c: char| c.is_ascii_digit() || c == '.');
        if unit.len() < w.len() && OUTSIDE_UNITS.contains(&unit) {
            return Some(format!(
                "the unit `{unit}` is outside the subset (item 5.6)"
            ));
        }
    }
    None
}

/// The tally of one suite.
#[derive(Default)]
struct Tally {
    pass: usize,
    xfail: Vec<String>,
    failures: Vec<String>,
}

impl Tally {
    fn record(&mut self, ok: bool, query: &str, what: String) {
        if ok {
            self.pass = self.pass.saturating_add(1);
        } else if let Some(why) = reason(query) {
            self.xfail.push(format!("{what}: {why}"));
        } else {
            self.failures.push(what);
        }
    }

    fn report(&self, suite: &str, total: usize) {
        for x in &self.xfail {
            println!("expected failure: {x}");
        }
        println!(
            "clazel-conformance: suite=\"{suite}\" pass={} xfail={} fail={} total={total}",
            self.pass,
            self.xfail.len(),
            self.failures.len(),
        );
    }

    fn assert_clean(&self) {
        assert!(
            self.failures.is_empty(),
            "{} unexpected failures:\n{}",
            self.failures.len(),
            self.failures.join("\n")
        );
    }
}

/// `query_applies(q)` on a `width` by `height` iframe.
fn query_applies(q: &str, width: u32, height: u32) -> bool {
    matches_environment(&cps(q), Device::screen(width, height))
}

/// `query_is_parseable(q)`: `None` where the page would `assert_unreached`.
fn query_is_parseable(q: &str) -> Option<bool> {
    let sheet = StyleSheet::parse(&cps(&format!("@media screen, {q} {{}}")));
    match sheet.media.as_slice() {
        [only] => Some(serialize(&only.queries) != "screen, not all"),
        _ => None,
    }
}

fn expression_is_known(e: &str, width: u32, height: u32) -> bool {
    query_applies(&format!("({e}), not all and ({e})"), width, height)
}

fn run_case(c: &Case) -> Option<bool> {
    let (w, h) = (c.width, c.height);
    Some(match c.helper {
        "should_apply" => query_applies(c.input, w, h),
        "should_not_apply" => !query_applies(c.input, w, h),
        "query_should_be_parseable" => query_is_parseable(c.input)?,
        "query_should_not_be_parseable" => !query_is_parseable(c.input)?,
        "expression_should_be_known" => expression_is_known(c.input, w, h),
        "expression_should_be_unknown" => {
            query_is_parseable(&format!("({})", c.input))? && !expression_is_known(c.input, w, h)
        }
        _ => return None,
    })
}

#[test]
fn wpt_test_media_queries() {
    // Under Miri a stride of the cases, to finish in about a minute (docs/VERIFICATION.md):
    // each case tokenizes and parses one or two short strings, which Miri runs about a
    // thousand times slower than native code.
    let stride = if cfg!(miri) { 4 } else { 1 };
    let mut t = Tally::default();
    let mut ran = 0usize;
    for c in EVAL.iter().step_by(stride) {
        ran = ran.saturating_add(1);
        let ok = run_case(c).unwrap_or(false);
        let what = format!(
            "test_media_queries.html:{} {}({:?}) at {}x{}",
            c.line, c.helper, c.input, c.width, c.height
        );
        t.record(ok, c.input, what);
    }
    for (line, helper, why) in EVAL_NOT_RUN {
        println!("not run: test_media_queries.html:{line} {helper}: {why}");
    }
    t.report("WPT mediaqueries/ test_media_queries.html", ran);
    t.assert_clean();
}

#[test]
fn wpt_match_media_parsing() {
    let mut t = Tally::default();
    for c in PARSING {
        let got = serialize(&clazel_style::sources::media::parse(&cps(c.query)));
        let what = format!(
            "match-media-parsing.html:{} {:?}: got {got:?}, want {:?}",
            c.line, c.query, c.expected
        );
        t.record(got == c.expected, c.query, what);
    }
    for (line, helper, why) in PARSING_NOT_RUN {
        println!("not run: match-media-parsing.html:{line} {helper}: {why}");
    }
    t.report("WPT mediaqueries/ match-media-parsing.html", PARSING.len());
    t.assert_clean();
}

#[test]
fn wpt_media_reftests() {
    let device = Device::screen(800, 600);
    let mut t = Tally::default();
    let mut total = 0usize;
    for page in PAGES {
        // The @media rules of every sheet of the page, in order, with their preludes as
        // text for the reasons.
        let mut active = Vec::new();
        let mut preludes = Vec::new();
        for css in page.sheets {
            let sheet = StyleSheet::parse(&cps(css));
            active.extend(sheet.active_media(device));
            let mut rest = *css;
            while let Some(at) = rest.to_ascii_lowercase().find("@media") {
                let after = rest.get(at.saturating_add(6)..).unwrap_or_default();
                let end = after.find('{').unwrap_or(after.len());
                preludes.push(after.get(..end).unwrap_or_default().trim().to_owned());
                rest = after.get(end..).unwrap_or_default();
            }
        }
        for (k, (line, want)) in page.media.iter().enumerate() {
            total = total.saturating_add(1);
            let prelude = preludes.get(k).cloned().unwrap_or_default();
            let got = active.get(k).copied();
            let what = format!(
                "{}:{line} @media {prelude:?}: active {got:?}, want {want}",
                page.file
            );
            t.record(
                got == Some(*want) && active.len() == page.media.len(),
                &prelude,
                what,
            );
        }
    }
    t.report("WPT mediaqueries/ reftests", total);
    t.assert_clean();
}
