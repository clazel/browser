//! Tree-construction conformance (Phase 4 item 4.11): the html5lib
//! tree-construction tests vendored from WPT (`tests/data/wpt-tree-construction/`,
//! converted by `cargo xtask testdata` into `tests/generated/`), run through
//! the executable tree builder.
//!
//! Each case is parsed by `exec::step`: a document case starts from
//! `new_parser_exec`, a `#document-fragment` case from
//! `fragment_parser_exec` (a context `"td"` is an HTML element, `"svg path"`
//! and `"math mi"` are SVG and MathML ones). Every token goes through
//! `step`, the tokenizer is switched whenever the step asks for it, and the
//! run ends after end of file or when the parser stops. The tree (the
//! document's children, or the fragment's) is printed in the suite's format
//! by `support/dump.rs` and compared byte for byte with the case's
//! `#document`. Parse errors are not compared (the converter drops them).
//!
//! Scripting: `#script-on` and `#script-off` set the flag; a case with
//! neither runs once, with scripting **off**, the browser's setting (this
//! browser runs no scripts). Its scripting-on reading is not checked.
//!
//! The tokenizer is `support/standin.rs`, a test-only stand-in that accepts
//! an unambiguous subset of the input language and refuses (`None`) the
//! rest. A case it refuses is an expected failure counted under the reason
//! it was refused, below; those cases run after the join with
//! `clazel-html`'s tokenizer. A case whose tree differs is a bug in the
//! spec (the exec is proven equal to it) or in the support code, and is an
//! expected failure only if listed by name in [`KNOWN_MISMATCHES`] with its
//! cause.
//!
//! Units: cases. `total` is the length of `CASES` (every case of every
//! non-scripted `.dat` file). The `scripted_*.dat` cases need a script
//! engine; they are not in `total` and are reported on a separate line.

#[path = "support/dump.rs"]
mod dump;
#[path = "support/standin.rs"]
mod standin;

use std::collections::BTreeMap;

use clazel_dom::exec::ExecAttr;
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_treebuilder::exec::step::{ExecContext, fragment_parser_exec, new_parser_exec, step};
use clazel_treebuilder::exec::types::{EncFnsExec, ExecTokAttr, ExecToken, ParserBuf};
use clazel_treebuilder::spec::TokenizerState;
use standin::{StandIn, State, Tok};

include!("generated/wpt_tree_construction.rs");

/// Cases whose tree differs from the expected one, by `file:index`, with
/// the cause. Each is a bug to fix, not an accepted difference.
const KNOWN_MISMATCHES: &[(&str, &str)] = &[
    (
        "webkit02.dat:44",
        "spec bug: HTML §4.10.10 \"When an option element option is popped off the stack of open elements of an HTML parser … update descendant selectedcontent elements for an option\" is not modelled (nor listed as a restriction in src/spec/mod.rs), so <selectedcontent> stays empty",
    ),
    (
        "webkit02.dat:45",
        "spec bug: as webkit02.dat:44 (option popped off the stack does not clone into selectedcontent)",
    ),
    (
        "webkit02.dat:46",
        "spec bug: as webkit02.dat:44 (option popped off the stack does not clone into selectedcontent)",
    ),
    (
        "webkit02.dat:47",
        "spec bug: as webkit02.dat:44 (option popped off the stack does not clone into selectedcontent)",
    ),
];

/// The encoding functions the tree builder calls for `<meta charset>`. The
/// documents here are parsed with a certain encoding (not tentative), so
/// the result never changes the tree.
struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn u32s(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

fn state_of(t: &TokenizerState) -> State {
    match t {
        TokenizerState::Data => State::Data,
        TokenizerState::Rcdata => State::Rcdata,
        TokenizerState::Rawtext => State::Rawtext,
        TokenizerState::ScriptData => State::ScriptData,
        TokenizerState::Plaintext => State::Plaintext,
    }
}

fn exec_token(t: Tok) -> ExecToken {
    match t {
        Tok::Doctype(name) => ExecToken::Doctype {
            name: Some(name),
            public_id: None,
            system_id: None,
            force_quirks: false,
        },
        Tok::Start(name, attrs, self_closing) => ExecToken::StartTag {
            name,
            attrs: attrs
                .into_iter()
                .map(|(name, value)| ExecTokAttr { name, value })
                .collect(),
            self_closing,
        },
        Tok::End(name) => ExecToken::EndTag {
            name,
            attrs: Vec::new(),
            self_closing: false,
        },
        Tok::Comment(data) => ExecToken::Comment { data },
        Tok::Char(c) => ExecToken::Character { c },
        Tok::Eof => ExecToken::Eof,
    }
}

/// Why the stand-in refused an input: the construct at the position where
/// it stopped.
fn refusal_reason(input: &[u32], pos: usize, state: State) -> &'static str {
    let tail = input.get(pos..).unwrap_or(&[]);
    let at = |i: usize| tail.get(i).copied();
    let rest: String = tail.iter().filter_map(|&c| char::from_u32(c)).collect();
    let has_gt = rest.contains('>');
    let tag = rest.split('>').next().unwrap_or("");
    let reference = tag
        .as_bytes()
        .windows(2)
        .any(|w| matches!(w, [b'&', n] if n.is_ascii_alphanumeric() || *n == b'#'));
    match state {
        State::Rawtext | State::ScriptData if rest.starts_with("<!") => {
            return "script data escape (`<!--` in script data)";
        }
        State::Rcdata | State::Rawtext | State::ScriptData if rest.starts_with("</") => {
            return "appropriate end tag followed by whitespace or `/` in a text state";
        }
        _ => {}
    }
    match at(0) {
        Some(0x26) => "character reference (`&` then an alphanumeric or `#`)",
        Some(0x3C) => match at(1) {
            Some(0x3F) => "`<?` (processing instruction or bogus comment)",
            Some(0x21) => {
                let low = rest.to_ascii_lowercase();
                if low.starts_with("<![cdata[") {
                    "CDATA section"
                } else if low.starts_with("<!--") {
                    "comment outside the grammar (abrupt `<!-->`/`<!--->`, `--!`, nested `<!--`, `-` before `-->`, or end of file)"
                } else if low.starts_with("<!doctype") {
                    "DOCTYPE outside the grammar (identifiers, no name, space before `>`, or end of file)"
                } else {
                    "bogus comment (`<!` not followed by `--` or DOCTYPE)"
                }
            }
            Some(0x2F) => match at(2) {
                Some(c) if ascii_alpha(c) => {
                    if has_gt {
                        "end tag outside the grammar (quotes, `<`, `=`, `&` or a stray `/` in it)"
                    } else {
                        "end of file inside a tag"
                    }
                }
                _ => "`</` not followed by a letter (`</>`, bogus comment or end of file)",
            },
            _ => {
                if !has_gt {
                    "end of file inside a tag"
                } else if reference {
                    "character reference in an attribute value"
                } else {
                    "start tag outside the grammar (quotes, `<` or `=` in a name or unquoted value, a stray `/`, `=` without a value)"
                }
            }
        },
        _ => "other",
    }
}

fn ascii_alpha(c: u32) -> bool {
    char::from_u32(c).is_some_and(|c| c.is_ascii_alphabetic())
}

enum Outcome {
    /// The tree as printed.
    Tree(String),
    /// The stand-in refused the input, for this reason.
    Refused(&'static str),
}

/// The context element of a `#document-fragment` line: `name` is an HTML
/// element, `svg name` and `math name` SVG and MathML ones; `None` for any
/// other prefix.
fn context_of(ctx: &str) -> Option<ExecContext> {
    let (ns, name) = match ctx.split_once(' ') {
        Some(("svg", n)) => (Namespace::Svg, n),
        Some(("math", n)) => (Namespace::MathMl, n),
        Some(_) => return None,
        None => (Namespace::Html, ctx),
    };
    Some(ExecContext {
        ns,
        name: u32s(name),
        attrs: Vec::<ExecAttr>::new(),
        mode: DocumentMode::NoQuirks,
    })
}

fn run(case: &Case, scripting: bool) -> Outcome {
    let (mut p, root, start): (ParserBuf, usize, State) = match case.fragment {
        None => (
            new_parser_exec(Vec::new(), scripting, false),
            0,
            State::Data,
        ),
        Some(ctx) => {
            // An unknown context prints as a tree that matches nothing, so
            // the case fails.
            let Some(context) = context_of(ctx) else {
                return Outcome::Tree(format!("#unknown context {ctx:?}"));
            };
            let (p, frag, st) = fragment_parser_exec(context, scripting);
            (p, frag, st.as_ref().map_or(State::Data, state_of))
        }
    };
    let Some(mut tok) = StandIn::new(case.data, start) else {
        return Outcome::Refused("U+0000 in the input");
    };
    let mut state = start;
    loop {
        let Some(t) = tok.next() else {
            return Outcome::Refused(refusal_reason(tok.input(), tok.pos(), state));
        };
        let eof = t == Tok::Eof;
        step(&mut p, &NoEnc, exec_token(t));
        if let Some(s) = &p.tokenizer {
            state = state_of(s);
            tok.set_state(state);
        } else {
            state = tok.state();
        }
        if eof || p.stopped {
            break;
        }
    }
    Outcome::Tree(dump::dump_children(&p.arena, root))
}

#[test]
fn wpt_tree_construction() {
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut failed: Vec<String> = Vec::new();
    let mut refused: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut known_hit: Vec<&str> = Vec::new();
    let mut stale: Vec<&str> = Vec::new();
    let mut default_scripting = 0usize;
    for case in CASES {
        let id = format!("{}:{}", case.file, case.index);
        if case.scripting.is_none() {
            default_scripting += 1;
        }
        let known = KNOWN_MISMATCHES.iter().find(|(k, _)| *k == id);
        match run(case, case.scripting.unwrap_or(false)) {
            Outcome::Refused(reason) => {
                *refused.entry(reason).or_default() += 1;
                xfail += 1;
            }
            Outcome::Tree(tree) => {
                let tree = tree.strip_suffix('\n').unwrap_or(&tree);
                if tree == case.document {
                    pass += 1;
                    if let Some((k, _)) = known {
                        stale.push(k);
                    }
                } else if let Some((k, _)) = known {
                    known_hit.push(k);
                    xfail += 1;
                } else {
                    failed.push(format!(
                        "{id} data={:?} fragment={:?} scripting={:?}\n--- expected\n{}\n--- actual\n{}",
                        case.data, case.fragment, case.scripting, case.document, tree
                    ));
                }
            }
        }
    }
    println!(
        "tree construction: {} cases run with scripting off (no #script-on/#script-off)",
        default_scripting
    );
    println!(
        "tree construction: stand-in tokenizer refused {} cases:",
        refused.values().sum::<usize>()
    );
    for (reason, n) in &refused {
        println!("  {n:5}  {reason}");
    }
    println!(
        "tree construction: {} known mismatches (spec bugs, see KNOWN_MISMATCHES):",
        known_hit.len()
    );
    for k in &known_hit {
        let why = KNOWN_MISMATCHES
            .iter()
            .find(|(n, _)| n == k)
            .map_or("", |(_, w)| w);
        println!("  {k}: {why}");
    }
    for f in &failed {
        println!("MISMATCH {f}\n");
    }
    println!(
        "tree construction: scripted_*.dat cases not run (need a script engine, not in total): {}",
        SCRIPTED_NOT_RUN
    );
    println!(
        "clazel-conformance: suite=\"html5lib tree construction (WPT)\" pass={pass} xfail={xfail} fail={} total={}",
        failed.len(),
        CASES.len()
    );
    assert!(
        stale.is_empty(),
        "listed as mismatches but now pass: {stale:?}"
    );
    assert!(failed.is_empty(), "{} unexpected mismatches", failed.len());
    assert_eq!(pass + xfail + failed.len(), CASES.len());
}
