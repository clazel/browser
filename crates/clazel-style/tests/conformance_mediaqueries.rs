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
//! **`@media` block activation (green/red proxy).** This suite renders nothing. Each unit is
//! one `@media` rule of a reftest page: the converter scanned the block for the words
//! `green` and `red` and took "green" to mean "the rule applies"; the page's `style` elements
//! are parsed as sheets, and `StyleSheet::active_media` in WPT's 800 by 600 viewport must
//! agree. It evidences the media query evaluator only, not painting (see the converter and
//! `SOURCE.md`).
//!
//! **Expected failures are per case.** A case that names a media feature or a unit outside
//! the subset is listed by `file:line` in [`EXPECTED_FAIL`] and must still fail: it fails the
//! test if it passes (the list is stale) or if a listed case is not run. A case that is not
//! listed must pass, whatever it names. A case that names an unsupported feature and
//! evaluates (`should_apply`, `should_not_apply`, `expression_should_be_known`,
//! `expression_should_be_unknown`, and the reftest blocks) but passes only because an unknown
//! feature evaluates false is not a pass of the supported subset: it is tallied with the
//! expected failures, as "passes only because unknown". Parsing helpers do not depend on the
//! feature being known, so a pass there is a pass. The totals are asserted. Calls the
//! converter did not read are listed, not counted.

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

/// The cases that must fail, each by `file:line`: every one names a media feature or a
/// unit outside the subset (phase-5.md item 5.8: `width`, `height`, their `min-` and `max-`
/// forms, and `orientation`; units of `values/`'s subset), so this implementation reads the
/// feature as unknown and the WPT expectation, which needs the feature's value, is not met.
/// A case in this list that passes, or is not run, fails the test.
const EXPECTED_FAIL: &[&str] = &[
    "media-queries-003.xht:9",
    "media-queries-003.xht:10",
    "media-queries-003.xht:11",
    "mq-negative-range-001.html:16",
    "mq-negative-range-002.html:16",
    "negation-001.html:18",
    "negation-001.html:21",
    "negation-001.html:24",
    "negation-002.html:16",
    "relative-units-004.html:29",
    "test_media_queries.html:277",
    "test_media_queries.html:278",
    "test_media_queries.html:314",
    "test_media_queries.html:319",
    "test_media_queries.html:320",
    "test_media_queries.html:321",
    "test_media_queries.html:326",
    "test_media_queries.html:328",
    "test_media_queries.html:329",
    "test_media_queries.html:330",
    "test_media_queries.html:335",
    "test_media_queries.html:338",
    "test_media_queries.html:339",
    "test_media_queries.html:352",
    "test_media_queries.html:444",
    "test_media_queries.html:446",
    "test_media_queries.html:448",
    "test_media_queries.html:449",
    "test_media_queries.html:450",
    "test_media_queries.html:519",
    "test_media_queries.html:520",
    "test_media_queries.html:521",
    "test_media_queries.html:530",
    "test_media_queries.html:531",
    "test_media_queries.html:532",
    "test_media_queries.html:534",
    "test_media_queries.html:535",
    "test_media_queries.html:536",
    "test_media_queries.html:545",
    "test_media_queries.html:559",
    "test_media_queries.html:589",
    "test_media_queries.html:590",
    "test_media_queries.html:591",
    "test_media_queries.html:592",
    "test_media_queries.html:606",
    "test_media_queries.html:607",
    "test_media_queries.html:608",
    "test_media_queries.html:619",
    "test_media_queries.html:620",
    "test_media_queries.html:621",
    "test_media_queries.html:622",
    "test_media_queries.html:633",
    "test_media_queries.html:634",
    "test_media_queries.html:635",
    "test_media_queries.html:636",
    "test_media_queries.html:637",
    "test_media_queries.html:638",
    "test_media_queries.html:656",
    "test_media_queries.html:657",
    "test_media_queries.html:658",
    "test_media_queries.html:659",
    "test_media_queries.html:660",
    "test_media_queries.html:661",
    "test_media_queries.html:662",
    "test_media_queries.html:663",
];

/// Whether a helper evaluates a query (its result depends on a feature being known), as
/// opposed to a parsing helper.
fn evaluates(helper: &str) -> bool {
    matches!(
        helper,
        "should_apply"
            | "should_not_apply"
            | "expression_should_be_known"
            | "expression_should_be_unknown"
    )
}

/// The tally of one suite.
#[derive(Default)]
struct Tally {
    pass: usize,
    xfail: Vec<String>,
    failures: Vec<String>,
    seen: Vec<String>,
}

impl Tally {
    /// One case: its key (`file:line`), whether it evaluates, whether it passed, the text
    /// of its query for [`reason`], and its description.
    fn record(&mut self, key: &str, evaluating: bool, ok: bool, query: &str, what: String) {
        let listed = EXPECTED_FAIL.iter().find(|k| **k == key).copied();
        if let Some(k) = listed {
            self.seen.push((*k).to_owned());
        }
        match (listed.is_some(), ok) {
            (true, true) => self.failures.push(format!(
                "{what}: passes, but is listed in EXPECTED_FAIL (stale entry)"
            )),
            (true, false) => {
                let why = reason(query).unwrap_or_else(|| {
                    "listed, but names no feature outside the subset".to_owned()
                });
                self.xfail.push(format!("{what}: {why}"));
            }
            (false, false) => self.failures.push(what),
            (false, true) => match reason(query).filter(|_| evaluating) {
                Some(why) => self
                    .xfail
                    .push(format!("{what}: passes only because unknown; {why}")),
                None => self.pass = self.pass.saturating_add(1),
            },
        }
    }

    /// Every listed key of `file` was run (unless a stride skipped some).
    fn check_stale(&mut self, file: &str, complete: bool) {
        if !complete {
            return;
        }
        let prefix = format!("{file}:");
        for k in EXPECTED_FAIL.iter().filter(|k| k.starts_with(&prefix)) {
            if !self.seen.iter().any(|s| s == k) {
                self.failures
                    .push(format!("{k}: listed in EXPECTED_FAIL but not run"));
            }
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

    /// The suite's fixed totals, which a change of the data or the code must update.
    fn assert_totals(&self, pass: usize, xfail: usize) {
        assert_eq!((self.pass, self.xfail.len()), (pass, xfail), "pass, xfail");
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
        let key = format!("test_media_queries.html:{}", c.line);
        t.record(&key, evaluates(c.helper), ok, c.input, what);
    }
    t.check_stale("test_media_queries.html", stride == 1);
    for (line, helper, why) in EVAL_NOT_RUN {
        println!("not run: test_media_queries.html:{line} {helper}: {why}");
    }
    t.report("WPT mediaqueries/ test_media_queries.html", ran);
    t.assert_clean();
    if stride == 1 {
        t.assert_totals(110, 104);
        assert_eq!(ran, EVAL.len());
    }
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
        // Parsing and serialization do not depend on a feature being known.
        let key = format!("match-media-parsing.html:{}", c.line);
        t.record(&key, false, got == c.expected, c.query, what);
    }
    for (line, helper, why) in PARSING_NOT_RUN {
        println!("not run: match-media-parsing.html:{line} {helper}: {why}");
    }
    t.report("WPT mediaqueries/ match-media-parsing.html", PARSING.len());
    t.assert_clean();
    t.assert_totals(PARSING.len(), 0);
}

#[test]
fn wpt_media_block_activation() {
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
            let key = format!("{}:{line}", page.file);
            t.record(
                &key,
                true,
                got == Some(*want) && active.len() == page.media.len(),
                &prelude,
                what,
            );
        }
    }
    for page in PAGES {
        t.check_stale(page.file, true);
    }
    t.report(
        "WPT mediaqueries/ @media block activation (green/red proxy)",
        total,
    );
    t.assert_clean();
    t.assert_totals(39, 18);
}
