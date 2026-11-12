//! UAX #14's own test file through the line breaking rules
//! (`clazel_layout::text`, phase-5.md item 5.12).
//!
//! `LineBreakTest.txt` (Unicode 18.0.0, "Default Line_Break Test",
//! vendored under `crates/clazel-layout/data/unicode-18.0.0/` with its
//! SHA-256 in `SOURCE.md`) gives, per line, a string of code points with
//! `÷` wherever there is a break opportunity and `×` wherever there is not,
//! including after the last character (always `÷`, LB3). The file does not
//! tell a mandatory break from an allowed one, so `÷` matches both.
//!
//! Two suites, each printing one `clazel-conformance:` line
//! (`xtask/src/conformance.rs`). A unit is one line of the file: it passes
//! if the break after every one of its characters is as the file says.
//!
//! - **default rules**: every line through [`Props::of`] (LB1's default
//!   resolution) and [`breaks`]. No expected differences.
//! - **with CSS Text 3's tailorings**: the same lines through
//!   [`Props::css`], the resolution `text::wrap` uses. A line that then
//!   differs is an expected difference if it holds a character that a
//!   tailoring changes, named by the first that applies:
//!   - `SA as ID`: an SA character that is not Mn or Mc. CSS Text 3 §5.5
//!     requires a soft wrap opportunity between the letters of a script
//!     needing lexical analysis that the UA cannot do; LB1's default makes
//!     them AL, which never breaks between them.
//!   - `control as So`: a control character (Cc) of class CM. CSS Text 3
//!     §4 treats it "as any other character of the Other Symbols (So)
//!     general category", which we resolve to AL; LB1 keeps it CM.
//!
//! Under Miri every [`MIRI_STRIDE`]th line runs (Miri runs this code
//! thousands of times slower, and CI fails any test that takes 300 s).

use clazel_layout::text::classes::{Gc, Lb, general_category, line_break};
use clazel_layout::text::{Break, Props, breaks_with_rules};

/// The test file, as vendored.
const TEST_FILE: &str = include_str!("../data/unicode-18.0.0/LineBreakTest.txt");

/// Under Miri, run one line in this many (measured: README, "Miri").
const MIRI_STRIDE: usize = 20;

/// One line of the test file: the code points and, after each, whether
/// there is a break opportunity.
struct Case {
    line: usize,
    text: Vec<char>,
    expected: Vec<bool>,
}

/// The test file's cases, in order, or the first line that does not have
/// the documented form.
fn cases() -> Result<Vec<Case>, String> {
    let mut out = Vec::new();
    for (line, l) in (1usize..).zip(TEST_FILE.lines()) {
        let data = l.split('#').next().unwrap_or("").trim();
        if data.is_empty() {
            continue;
        }
        let mut tokens = data.split_whitespace();
        if tokens.next() != Some("×") {
            return Err(format!("line {line}: no × at the start"));
        }
        let mut text = Vec::new();
        let mut expected = Vec::new();
        while let Some(cp) = tokens.next() {
            let c = u32::from_str_radix(cp, 16)
                .ok()
                .and_then(char::from_u32)
                .ok_or(format!("line {line}: bad code point {cp}"))?;
            text.push(c);
            match tokens.next() {
                Some("÷") => expected.push(true),
                Some("×") => expected.push(false),
                other => return Err(format!("line {line}: expected ÷ or ×, got {other:?}")),
            }
        }
        out.push(Case {
            line,
            text,
            expected,
        });
    }
    Ok(out)
}

/// The breaks our rules give `case` with `props`, as the file writes them,
/// and a description of the first difference, if any.
fn run(case: &Case, props: impl Fn(char) -> Props) -> Option<String> {
    let p: Vec<Props> = case.text.iter().map(|&c| props(c)).collect();
    let got = breaks_with_rules(&p);
    for (k, ((b, rule), want)) in got.iter().zip(&case.expected).enumerate() {
        let is_break = *b != Break::Prohibited;
        if is_break != *want {
            let cps: Vec<String> = case
                .text
                .iter()
                .map(|c| format!("{:04X}", u32::from(*c)))
                .collect();
            return Some(format!(
                "line {}: [{}] after character {k}: expected {}, got {b:?} by {rule:?}",
                case.line,
                cps.join(" "),
                if *want { "÷" } else { "×" },
            ));
        }
    }
    (got.len() != case.expected.len()).then(|| format!("line {}: wrong length", case.line))
}

/// The tailoring that explains a difference under [`Props::css`], if any.
fn tailoring(case: &Case) -> Option<&'static str> {
    let sa = case
        .text
        .iter()
        .any(|&c| line_break(c) == Lb::SA && !matches!(general_category(c), Some(Gc::Mn | Gc::Mc)));
    if sa {
        return Some("SA as ID");
    }
    let cc = case
        .text
        .iter()
        .any(|&c| line_break(c) == Lb::CM && general_category(c) == Some(Gc::Cc));
    cc.then_some("control as So")
}

#[test]
fn line_break_test() {
    let stride = if cfg!(miri) { MIRI_STRIDE } else { 1 };
    let all = match cases() {
        Ok(all) => all,
        Err(e) => {
            assert!(e.is_empty(), "LineBreakTest.txt: {e}");
            Vec::new()
        }
    };
    // The file's own count ("# Lines: 19346").
    let stated = TEST_FILE
        .lines()
        .find_map(|l| l.strip_prefix("# Lines: "))
        .and_then(|n| n.trim().parse::<usize>().ok());
    assert_eq!(Some(all.len()), stated, "the file's line count");

    let mut default = (0u64, 0u64, Vec::new());
    let mut css = (0u64, 0u64, Vec::new());
    let mut css_xfail: std::collections::BTreeMap<&str, u64> = Default::default();
    for case in all.iter().step_by(stride) {
        match run(case, Props::of) {
            None => default.0 = default.0.saturating_add(1),
            Some(m) => {
                default.1 = default.1.saturating_add(1);
                default.2.push(m);
            }
        }
        match run(case, |c| Props::css(c, false)) {
            None => css.0 = css.0.saturating_add(1),
            Some(m) => match tailoring(case) {
                Some(t) => {
                    let n = css_xfail.entry(t).or_default();
                    *n = n.saturating_add(1);
                }
                None => {
                    css.1 = css.1.saturating_add(1);
                    css.2.push(m);
                }
            },
        }
    }
    let run_count = default.0.saturating_add(default.1);
    println!(
        "clazel-conformance: suite=\"Unicode 18.0.0 LineBreakTest.txt\" pass={} xfail=0 fail={} total={run_count}",
        default.0, default.1
    );
    let xfail: u64 = css_xfail.values().sum();
    println!(
        "clazel-conformance: suite=\"LineBreakTest.txt with CSS Text 3 tailorings\" pass={} xfail={xfail} fail={} total={run_count}",
        css.0, css.1
    );
    for (k, n) in &css_xfail {
        println!("  expected difference {k}: {n}");
    }
    for m in default.2.iter().chain(&css.2).take(40) {
        println!("FAIL {m}");
    }
    assert_eq!(default.1, 0, "lines failing the default rules");
    assert_eq!(css.1, 0, "unexpected differences with CSS's tailorings");
}
