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
//!   differs is an expected difference only if every break opportunity on
//!   which it differs from the file is adjacent to a character that a
//!   tailoring changes (the break before it, the break after it, and the
//!   breaks inside the run of combining marks that follows it, which LB9
//!   attaches to it), named by the first tailoring that explains all of
//!   them. The number of such lines and their split between the two
//!   tailorings are pinned ([`PINNED_SA`], [`PINNED_CONTROL`]): a line
//!   that no longer differs, or moves between them, fails.
//!   - `SA as ID`: an SA character that is not Mn or Mc. CSS Text 3 §5.5
//!     requires a soft wrap opportunity between the letters of a script
//!     needing lexical analysis that the UA cannot do; LB1's default makes
//!     them AL, which never breaks between them.
//!   - `control as So`: a control character (Cc) of class CM. CSS Text 3
//!     §4 treats it "as any other character of the Other Symbols (So)
//!     general category", which we resolve to AL; LB1 keeps it CM.
//!
//! A third check runs `word-break: break-all` ([`Props::css`] with
//! `break_all`) over the file against CSS Text 3 §5.2 (see [`break_all`]).
//! It is a one-directional property, not a full oracle: a full oracle would
//! have to re-derive which rules still hold between ideographs, which is
//! the implementation again.
//!
//! Under Miri only [`MIRI_SAMPLES`] lines run, taken at evenly spaced byte
//! offsets of the file (the first whole line after each offset), and the
//! file's own line count is not checked. Miri runs this code thousands of
//! times slower, and CI fails any test that takes 300 s: even reading the
//! 3 MB file line by line, before running any rule, took more than ten
//! minutes, so the input is reduced by sampling rather than by a stride over
//! parsed lines.

use clazel_layout::text::classes::{Gc, Lb, general_category, line_break};
use clazel_layout::text::{Break, Props, breaks_with_rules};

/// The test file, as vendored.
const TEST_FILE: &str = include_str!("../data/unicode-18.0.0/LineBreakTest.txt");

/// Under Miri, the number of evenly spaced samples of the file (measured:
/// README).
const MIRI_SAMPLES: usize = 100;

/// One line of the test file: the code points and, after each, whether
/// there is a break opportunity.
struct Case {
    /// Where it is: "line N", or "byte N" for a sample under Miri.
    line: String,
    text: Vec<char>,
    expected: Vec<bool>,
    /// The rule number the file's comment gives for each gap: `rules[k]` is
    /// the rule of the gap after character `k` ("28.0" for `× [28.0]`).
    rules: Vec<String>,
}

/// The lines to run, each with where it is: every line natively; under
/// Miri, the first whole line after each of [`MIRI_SAMPLES`] evenly spaced
/// byte offsets.
fn lines_to_run() -> Vec<(String, &'static str)> {
    if !cfg!(miri) {
        return (1usize..)
            .zip(TEST_FILE.lines())
            .map(|(n, l)| (format!("line {n}"), l))
            .collect();
    }
    let bytes = TEST_FILE.as_bytes();
    let step = bytes.len() / MIRI_SAMPLES;
    let newline_after = |from: usize| {
        bytes
            .get(from..)
            .and_then(|b| b.iter().position(|&c| c == b'\n'))
            .map(|p| from.saturating_add(p))
    };
    let mut out = Vec::new();
    for k in 0..MIRI_SAMPLES {
        let Some(start) = newline_after(step.saturating_mul(k)).map(|p| p.saturating_add(1)) else {
            continue;
        };
        let end = newline_after(start).unwrap_or(bytes.len());
        if let Some(l) = TEST_FILE.get(start..end) {
            out.push((format!("byte {start}"), l));
        }
    }
    out
}

/// The cases of `lines`, in order, or the first line that does not have
/// the documented form.
fn cases(lines: &[(String, &str)]) -> Result<Vec<Case>, String> {
    let mut out = Vec::new();
    for (line, l) in lines {
        let mut parts = l.splitn(2, '#');
        let data = parts.next().unwrap_or("").trim();
        // The comment: `× [2.0] NAME (...) × [28.0] NAME (...) ÷ [3.0]`; the
        // bracketed numbers in order are the rules of the gaps, the first
        // being the gap before the first character.
        let gap_rules: Vec<String> = parts
            .next()
            .unwrap_or("")
            .split('[')
            .skip(1)
            .filter_map(|r| r.split(']').next().map(str::to_owned))
            .collect();
        if data.is_empty() {
            continue;
        }
        let mut tokens = data.split_whitespace();
        if tokens.next() != Some("×") {
            return Err(format!("{line}: no × at the start"));
        }
        let mut text = Vec::new();
        let mut expected = Vec::new();
        while let Some(cp) = tokens.next() {
            let c = u32::from_str_radix(cp, 16)
                .ok()
                .and_then(char::from_u32)
                .ok_or(format!("{line}: bad code point {cp}"))?;
            text.push(c);
            match tokens.next() {
                Some("÷") => expected.push(true),
                Some("×") => expected.push(false),
                other => return Err(format!("{line}: expected ÷ or ×, got {other:?}")),
            }
        }
        let rules: Vec<String> = gap_rules.into_iter().skip(1).collect();
        if rules.len() != text.len() {
            return Err(format!("{line}: {} rules for {} characters", rules.len(), text.len()));
        }
        out.push(Case {
            line: line.clone(),
            text,
            expected,
            rules,
        });
    }
    Ok(out)
}

/// The break positions (after character `k`) on which our rules with
/// `props` differ from `case`, and a description of the first difference;
/// `None` if there is none.
fn run(case: &Case, props: impl Fn(char) -> Props) -> Option<(Vec<usize>, String)> {
    let p: Vec<Props> = case.text.iter().map(|&c| props(c)).collect();
    let got = breaks_with_rules(&p);
    let mut positions = Vec::new();
    let mut first = None;
    for (k, ((b, rule), want)) in got.iter().zip(&case.expected).enumerate() {
        let is_break = *b != Break::Prohibited;
        if is_break != *want {
            positions.push(k);
            if first.is_none() {
                let cps: Vec<String> = case
                    .text
                    .iter()
                    .map(|c| format!("{:04X}", u32::from(*c)))
                    .collect();
                first = Some(format!(
                    "{}: [{}] after character {k}: expected {}, got {b:?} by {rule:?}",
                    case.line,
                    cps.join(" "),
                    if *want { "÷" } else { "×" },
                ));
            }
        }
    }
    if got.len() != case.expected.len() {
        positions.push(usize::MAX);
        first.get_or_insert_with(|| format!("{}: wrong length", case.line));
    }
    first.map(|m| (positions, m))
}

/// The indices of the characters of `case` that `tailoring` changes.
fn tailored(case: &Case, tailoring: &str) -> Vec<usize> {
    case.text
        .iter()
        .enumerate()
        .filter(|&(_, &c)| match tailoring {
            "SA as ID" => {
                line_break(c) == Lb::SA && !matches!(general_category(c), Some(Gc::Mn | Gc::Mc))
            }
            _ => line_break(c) == Lb::CM && general_category(c) == Some(Gc::Cc),
        })
        .map(|(i, _)| i)
        .collect()
}

/// The tailoring that explains a difference under [`Props::css`], if any:
/// the first whose changed characters have every differing break
/// opportunity (`positions`) next to one. A break after character `k` is
/// next to a changed character `j` if `j - 1 <= k <= j + m`, `m` being the
/// length of the run of combining marks and ZWJ after `j` (LB9 attaches
/// them to it, so changing `j`'s class changes how the run breaks).
fn tailoring(case: &Case, positions: &[usize]) -> Option<&'static str> {
    ["SA as ID", "control as So"].into_iter().find(|t| {
        let js = tailored(case, t);
        !js.is_empty()
            && positions.iter().all(|&k| {
                js.iter().any(|&j| {
                    let m = case
                        .text
                        .iter()
                        .skip(j.saturating_add(1))
                        .take_while(|&&c| matches!(line_break(c), Lb::CM | Lb::ZWJ))
                        .count();
                    k.saturating_add(1) >= j && k <= j.saturating_add(m)
                })
            })
    })
}

/// CSS Text 3 §5.2, `word-break: break-all`: "Breaking is allowed within
/// 'words'", and the typographic letter units of the classes AL, HL and NU
/// "are instead treated as ID". So wherever the file forbids a break
/// between two such characters only by a rule that is about letters
/// following letters (LB23 AL/HL and NU, LB25 NU and NU, LB28 AL/HL and
/// AL/HL), `break-all` must allow it: two ideographs may be separated
/// (LB31). Returns the number of such gaps checked and those where
/// `break-all` still forbids the break, and the number of lines in which
/// `break-all` differs at all from the plain tailored rules (to show the
/// check is not blind).
fn break_all(all: &[Case]) -> (usize, Vec<String>, usize) {
    let letter = |c: char| matches!(Props::css(c, false).class, Lb::AL | Lb::HL | Lb::NU);
    let mut checked = 0usize;
    let mut bad = Vec::new();
    let mut changed = 0usize;
    for case in all {
        let p: Vec<Props> = case.text.iter().map(|&c| Props::css(c, true)).collect();
        let got = breaks_with_rules(&p);
        for (k, (b, _)) in got.iter().enumerate() {
            // The gap after character `k`, before character `k + 1`.
            let (Some(&a), Some(&n), Some(rule)) = (
                case.text.get(k),
                case.text.get(k.saturating_add(1)),
                case.rules.get(k),
            ) else {
                continue;
            };
            let major = rule.split('.').next().unwrap_or("");
            let by_letter_rule = matches!(major, "23" | "25" | "28");
            let file_forbids = case.expected.get(k) == Some(&false);
            if file_forbids && by_letter_rule && letter(a) && letter(n) {
                checked = checked.saturating_add(1);
                if *b == Break::Prohibited {
                    bad.push(format!("{} after character {k} ({rule})", case.line));
                }
            }
        }
        let q: Vec<Props> = case.text.iter().map(|&c| Props::css(c, false)).collect();
        let plain = breaks_with_rules(&q);
        if got.iter().map(|x| x.0).ne(plain.iter().map(|x| x.0)) {
            changed = changed.saturating_add(1);
        }
    }
    (checked, bad, changed)
}

/// Lines of the file that differ from it under [`Props::css`] because of
/// SA characters other than Mn and Mc (measured on Unicode 18.0.0's file;
/// every differing break is next to such a character).
const PINNED_SA: u64 = 75;
/// And because of class CM control characters.
const PINNED_CONTROL: u64 = 62;

#[test]
fn line_break_test() {
    let all = match cases(&lines_to_run()) {
        Ok(all) => all,
        Err(e) => {
            assert!(e.is_empty(), "LineBreakTest.txt: {e}");
            Vec::new()
        }
    };
    if !cfg!(miri) {
        // The file's own count ("# Lines: 19346").
        let stated = TEST_FILE
            .lines()
            .find_map(|l| l.strip_prefix("# Lines: "))
            .and_then(|n| n.trim().parse::<usize>().ok());
        assert_eq!(Some(all.len()), stated, "the file's line count");
    }

    let mut default = (0u64, 0u64, Vec::new());
    let mut css = (0u64, 0u64, Vec::new());
    let mut css_xfail: std::collections::BTreeMap<&str, u64> = Default::default();
    for case in &all {
        match run(case, Props::of) {
            None => default.0 = default.0.saturating_add(1),
            Some((_, m)) => {
                default.1 = default.1.saturating_add(1);
                default.2.push(m);
            }
        }
        match run(case, |c| Props::css(c, false)) {
            None => css.0 = css.0.saturating_add(1),
            Some((positions, m)) => match tailoring(case, &positions) {
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
    let (checked, bad, changed) = break_all(&all);
    println!(
        "break-all: {checked} letter-letter gaps checked, {} still prohibited, \
         {changed} lines differ from the plain tailored rules",
        bad.len()
    );
    assert!(
        bad.is_empty(),
        "break-all prohibits a break between two letters (CSS Text 3 §5.2): {bad:?}"
    );
    assert!(checked > 0, "no letter-letter gap checked: the check is blind");
    assert!(changed > 0, "break-all changed no line: the check is blind");
    if !cfg!(miri) {
        assert_eq!(
            (
                css_xfail.get("SA as ID").copied(),
                css_xfail.get("control as So").copied()
            ),
            (Some(PINNED_SA), Some(PINNED_CONTROL)),
            "the split of expected differences between the tailorings"
        );
        assert_eq!(
            xfail,
            PINNED_SA.saturating_add(PINNED_CONTROL),
            "expected differences in total"
        );
        assert_eq!(run_count, 19346, "lines run");
    }
}
