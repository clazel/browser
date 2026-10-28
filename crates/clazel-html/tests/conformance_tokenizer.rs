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
            total += 1;
            let got = actual(tokenize(
                &input,
                state(s),
                case.last_start_tag.map(<[u32]>::to_vec),
            ));
            if got == want {
                pass += 1;
            } else if case.xml_violation {
                xfail += 1;
            } else {
                fail += 1;
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
