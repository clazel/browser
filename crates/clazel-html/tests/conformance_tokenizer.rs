//! html5lib-tests `tokenizer/*.test` through the proven tokenizer.
//!
//! Each case's input is preprocessed (§13.2.3.5, `preprocess_exec`, as the
//! suite's README requires) and tokenized by `tokenize` once for each of
//! its initial states, with its last start tag; a unit of the suite is one
//! (case, initial state) run. The output is compared with the case's
//! tokens as the suite states them: adjacent character tokens coalesced,
//! the end-of-file token dropped, an end tag's attributes and self-closing
//! flag not compared (the suite's end tag is its name), and attributes
//! compared as a map (the suite's format cannot hold duplicates, and the
//! tokenizer has removed them). Parse errors are not modelled, so `errors`
//! was not converted.
//!
//! A second suite is a differential test against `html5gum` (0.8.4, an
//! independent tokenizer written from the standard), on every html5lib
//! input, on each of them mutated, and on random inputs over an alphabet
//! of the characters the states switch on: both outputs are compared as
//! above, with html5gum's parse-error tokens dropped and its DOCTYPE name
//! (a string, empty when missing) compared with ours (missing is empty).
//! Expected differences, never counted as passes: inputs containing `<?`
//! (html5gum predates the standard's processing instruction states and
//! makes a bogus comment of them) and inputs that are not scalar value
//! strings (html5gum reads UTF-8). The last start tag is set only in debug
//! builds, where html5gum allows it; release builds run the text states
//! without one, for both.
//!
//! Expected failures: the four cases of `xmlViolation.test`, which expect
//! the output after "coercing an HTML DOM into an infoset", a step after
//! tokenization that this crate does not implement; they are run, and
//! counted as passes only if their output matches anyway.

use clazel_html::tokenizer::buffer::{ExecAttribute, ExecToken};
use clazel_html::tokenizer::machine::{preprocess_exec, tokenize};
use clazel_html::tokenizer::spec::State;

/// A token as the suite writes it.
#[derive(Debug)]
enum T {
    Doctype(
        Option<&'static [u32]>,
        Option<&'static [u32]>,
        Option<&'static [u32]>,
        bool,
    ),
    Start(
        &'static [u32],
        &'static [(&'static [u32], &'static [u32])],
        bool,
    ),
    End(&'static [u32]),
    Comment(&'static [u32]),
    Pi(&'static [u32], &'static [u32]),
    Chars(&'static [u32]),
}

/// The suite's initial states.
#[derive(Debug, Clone, Copy)]
enum S {
    Data,
    Plaintext,
    Rcdata,
    Rawtext,
    ScriptData,
    CdataSection,
}

struct Case {
    file: &'static str,
    index: usize,
    description: &'static str,
    input: &'static [u32],
    states: &'static [S],
    last_start_tag: Option<&'static [u32]>,
    output: &'static [T],
    xml_violation: bool,
}

include!("generated/html5lib_tokenizer.rs");

/// A token in a form both sides convert to.
#[derive(Debug, PartialEq, Eq)]
enum N {
    Doctype(Option<Vec<u32>>, Option<Vec<u32>>, Option<Vec<u32>>, bool),
    Start(Vec<u32>, Vec<(Vec<u32>, Vec<u32>)>, bool),
    End(Vec<u32>),
    Comment(Vec<u32>),
    Pi(Vec<u32>, Vec<u32>),
    Chars(Vec<u32>),
}

fn state(s: S) -> State {
    match s {
        S::Data => State::Data,
        S::Plaintext => State::Plaintext,
        S::Rcdata => State::Rcdata,
        S::Rawtext => State::Rawtext,
        S::ScriptData => State::ScriptData,
        S::CdataSection => State::CdataSection,
    }
}

fn expected(tokens: &[T]) -> Vec<N> {
    let mut out: Vec<N> = Vec::new();
    for t in tokens {
        let n = match t {
            T::Doctype(n, p, s, correct) => N::Doctype(
                n.map(<[u32]>::to_vec),
                p.map(<[u32]>::to_vec),
                s.map(<[u32]>::to_vec),
                !correct,
            ),
            T::Start(name, attrs, sc) => {
                let mut a: Vec<(Vec<u32>, Vec<u32>)> = attrs
                    .iter()
                    .map(|(k, v)| (k.to_vec(), v.to_vec()))
                    .collect();
                a.sort();
                N::Start(name.to_vec(), a, *sc)
            }
            T::End(name) => N::End(name.to_vec()),
            T::Comment(d) => N::Comment(d.to_vec()),
            T::Pi(t, d) => N::Pi(t.to_vec(), d.to_vec()),
            T::Chars(c) => N::Chars(c.to_vec()),
        };
        push(&mut out, n);
    }
    out
}

/// Push, coalescing adjacent character data.
fn push(out: &mut Vec<N>, n: N) {
    if let N::Chars(more) = &n
        && let Some(N::Chars(prev)) = out.last_mut()
    {
        prev.extend_from_slice(more);
        return;
    }
    out.push(n);
}

fn attrs(v: &[ExecAttribute]) -> Vec<(Vec<u32>, Vec<u32>)> {
    let mut a: Vec<(Vec<u32>, Vec<u32>)> = v
        .iter()
        .map(|a| (a.name.clone(), a.value.clone()))
        .collect();
    a.sort();
    a
}

fn actual(tokens: Vec<ExecToken>) -> Vec<N> {
    let mut out: Vec<N> = Vec::new();
    for t in tokens {
        let n = match t {
            ExecToken::Doctype {
                name,
                public_identifier,
                system_identifier,
                force_quirks,
            } => N::Doctype(name, public_identifier, system_identifier, force_quirks),
            ExecToken::StartTag {
                tag_name,
                self_closing,
                attributes,
            } => N::Start(tag_name, attrs(&attributes), self_closing),
            ExecToken::EndTag { tag_name, .. } => N::End(tag_name),
            ExecToken::Comment { data } => N::Comment(data),
            ExecToken::ProcessingInstruction { target, data } => N::Pi(target, data),
            ExecToken::Character(c) => N::Chars(vec![c]),
            ExecToken::EndOfFile => continue,
        };
        push(&mut out, n);
    }
    out
}

fn text(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

#[test]
fn html5lib_tokenizer() {
    let mut pass = 0u64;
    let mut xfail = 0u64;
    let mut fail = 0u64;
    let mut total = 0u64;
    let mut failures: Vec<String> = Vec::new();
    for case in HTML5LIB {
        let input = preprocess_exec(case.input);
        let want = expected(case.output);
        for &s in case.states {
            total = total.saturating_add(1);
            let got = actual(tokenize(
                &input,
                state(s),
                case.last_start_tag.map(<[u32]>::to_vec),
            ));
            if got == want {
                pass = pass.saturating_add(1);
            } else if case.xml_violation {
                xfail = xfail.saturating_add(1);
            } else {
                fail = fail.saturating_add(1);
                if failures.len() < 40 {
                    failures.push(format!(
                        "{}[{}] {:?} in {:?}: input {:?}\n  want {:?}\n  got  {:?}",
                        case.file,
                        case.index,
                        case.description,
                        s,
                        text(case.input),
                        want,
                        got
                    ));
                }
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"html5lib-tests tokenizer\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
    assert!(
        failures.is_empty(),
        "{} failures, first ones:\n{}",
        fail,
        failures.join("\n")
    );
}

/// html5gum's tokens, in our comparable form.
fn reference(input: &str, s: S, last: Option<&str>) -> Vec<N> {
    let mut tok = html5gum::Tokenizer::new(input);
    tok.set_state(match s {
        S::Data => html5gum::State::Data,
        S::Plaintext => html5gum::State::PlainText,
        S::Rcdata => html5gum::State::RcData,
        S::Rawtext => html5gum::State::RawText,
        S::ScriptData => html5gum::State::ScriptData,
        S::CdataSection => html5gum::State::CdataSection,
    });
    set_last(&mut tok, last);
    let cps =
        |b: &[u8]| -> Vec<u32> { String::from_utf8_lossy(b).chars().map(u32::from).collect() };
    let mut out = Vec::new();
    for t in tok {
        let Ok(t) = t;
        let n = match t {
            html5gum::Token::StartTag(t) => {
                let mut a: Vec<(Vec<u32>, Vec<u32>)> = t
                    .attributes
                    .iter()
                    .map(|(k, v)| (cps(k), cps(&v.value)))
                    .collect();
                a.sort();
                N::Start(cps(&t.name), a, t.self_closing)
            }
            html5gum::Token::EndTag(t) => N::End(cps(&t.name)),
            html5gum::Token::String(s) => N::Chars(cps(&s.value)),
            html5gum::Token::Comment(c) => N::Comment(cps(&c.value)),
            html5gum::Token::Doctype(d) => N::Doctype(
                Some(cps(&d.value.name)),
                d.value.public_identifier.as_deref().map(|v| cps(v)),
                d.value.system_identifier.as_deref().map(|v| cps(v)),
                d.value.force_quirks,
            ),
            html5gum::Token::Error(_) => continue,
        };
        if matches!(&n, N::Chars(c) if c.is_empty()) {
            continue;
        }
        push(&mut out, n);
    }
    out
}

#[cfg(debug_assertions)]
fn set_last<R: html5gum::Reader, E: html5gum::Emitter>(
    tok: &mut html5gum::Tokenizer<R, E>,
    last: Option<&str>,
) {
    tok.set_last_start_tag(last);
}

#[cfg(not(debug_assertions))]
fn set_last<R: html5gum::Reader, E: html5gum::Emitter>(
    _tok: &mut html5gum::Tokenizer<R, E>,
    _last: Option<&str>,
) {
}

/// Ours, with a missing DOCTYPE name as empty, as html5gum has it.
fn ours_for_diff(input: &[u32], s: S, last: Option<&str>) -> Vec<N> {
    let last = if cfg!(debug_assertions) { last } else { None };
    actual(tokenize(
        input,
        state(s),
        last.map(|l| l.chars().map(u32::from).collect()),
    ))
    .into_iter()
    .map(|n| match n {
        N::Doctype(None, p, sys, q) => N::Doctype(Some(Vec::new()), p, sys, q),
        other => other,
    })
    .collect()
}

/// A small deterministic generator (xorshift64*), so runs are repeatable.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn pick<T: Copy>(&mut self, from: &[T], fallback: T) -> T {
        let i = self.below(from.len());
        from.get(i).copied().unwrap_or(fallback)
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }
}

/// Pieces random inputs are made of: the characters the states switch on,
/// and words they look for.
const PIECES: &[&str] = &[
    "<",
    ">",
    "/",
    "!",
    "-",
    "--",
    "&",
    "#",
    "x",
    "X",
    ";",
    "=",
    "\"",
    "'",
    " ",
    "\t",
    "\n",
    "\u{c}",
    "a",
    "b",
    "z",
    "A",
    "Z",
    "0",
    "9",
    "\0",
    "]",
    "]]",
    "[CDATA[",
    "DOCTYPE",
    "doctype",
    "PUBLIC",
    "system",
    "script",
    "SCRIPT",
    "title",
    "amp",
    "amp;",
    "notin",
    "not",
    "lt",
    "#x41",
    "#65",
    "#x80",
    "#0",
    "#x110000",
    "`",
    "\u{e9}",
    "\u{1F600}",
    "\u{FFFD}",
];

/// A comparable input: a scalar value string with no `<?`.
fn comparable(input: &[u32]) -> Option<String> {
    let s: Option<String> = input.iter().map(|&c| char::from_u32(c)).collect();
    s.filter(|s| !s.contains("<?"))
}

#[test]
fn html5gum_differential() {
    let mut inputs: Vec<(Vec<u32>, S, Option<String>)> = Vec::new();
    let mut rng = Rng(0x0C1A_2E10_4D5E_7A11);
    for case in HTML5LIB {
        let input = preprocess_exec(case.input);
        let last: Option<String> = case.last_start_tag.map(text);
        for &s in case.states {
            inputs.push((input.clone(), s, last.clone()));
        }
        // The same input with one code point replaced by a random piece.
        if !input.is_empty() {
            let mut m = input.clone();
            let at = rng.below(m.len());
            let piece: Vec<u32> = rng.pick(PIECES, "").chars().map(u32::from).collect();
            m.splice(at..=at, piece);
            inputs.push((preprocess_exec(&m), S::Data, None));
        }
    }
    let states = [S::Data, S::Rcdata, S::Rawtext, S::ScriptData, S::Plaintext];
    let lasts = [None, Some("title"), Some("script"), Some("textarea")];
    for _ in 0..20_000 {
        let mut s = String::new();
        for _ in 0..rng.below(24) {
            s.push_str(rng.pick(PIECES, ""));
        }
        let st = if rng.below(4) == 0 {
            rng.pick(&states, S::Data)
        } else {
            S::Data
        };
        let last = rng.pick(&lasts, None).map(str::to_owned);
        inputs.push((
            preprocess_exec(&s.chars().map(u32::from).collect::<Vec<u32>>()),
            st,
            last,
        ));
    }
    let (mut pass, mut xfail, mut fail) = (0u64, 0u64, 0u64);
    let mut failures = Vec::new();
    for (input, s, last) in &inputs {
        let Some(text_input) = comparable(input) else {
            xfail = xfail.saturating_add(1);
            continue;
        };
        let theirs = reference(&text_input, *s, last.as_deref());
        let ours = ours_for_diff(input, *s, last.as_deref());
        if ours == theirs {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            if failures.len() < 20 {
                failures.push(format!("{text_input:?} in {s:?} (last {last:?})\n  ours {ours:?}\n  html5gum {theirs:?}"));
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"html5gum differential\" pass={pass} xfail={xfail} fail={fail} total={}",
        inputs.len()
    );
    assert!(
        failures.is_empty(),
        "{fail} differences, first ones:\n{}",
        failures.join("\n")
    );
}
