//! Tree-construction differential against `html5ever` (Phase 4 items 4.0
//! and 4.11): Servo's HTML parser, with `markup5ever_rcdom` for its tree,
//! as a second engine written from the standard by an independent team.
//!
//! Inputs:
//! 1. every case of the WPT tree-construction suite
//!    (`tests/data/wpt-tree-construction/`, the same `CASES` as
//!    `conformance_tree_construction.rs`), documents and fragments, each
//!    with the scripting flag it names; a case naming neither runs twice,
//!    once with scripting off and once on (the suite's format says such a
//!    case holds for both, and both engines take the flag);
//! 2. 10,000 random tag soup inputs from a deterministic generator (below:
//!    start and end tags of the names the insertion modes switch on, a few
//!    attributes, text, comments, CDATA, DOCTYPEs), each parsed once, as a
//!    document or (one in four) as a fragment in one of 13 contexts, with a
//!    random scripting flag.
//!
//! Ours is the driver of `conformance_tree_construction.rs`
//! (`exec::driver::parse_real` and `parse_fragment_real`, proven equal to
//! the spec's `parse` and `parse_fragment` with `clazel-html`'s tokenizer);
//! html5ever's is `parse_document` / `parse_fragment` into an `RcDom`. Both
//! trees are printed in the suite's format (`support/dump.rs` for ours, the
//! same rules here for html5ever's) and compared byte for byte. A panic in
//! html5ever is caught and is a failure.
//!
//! A difference is never skipped. Each known cause is a [`Class`], with a
//! rule over the input that must hold for it. A suite case's difference is
//! known only if the case is listed in [`KNOWN_SUITE`] with its class, the
//! class's rule applies, and our tree is the suite's expected tree; a
//! listed case where the engines agree fails the test (stale). A random
//! input's difference is known if a class's rule applies ([`classify`]).
//! Anything else is a failure, labelled with whether ours, html5ever or
//! neither matches the suite (html5ever matching and ours not would be a
//! bug in ours; none was found).
//!
//! The four `selectedcontent` cases that `conformance_tree_construction.rs`
//! lists as our restriction (`webkit02.dat` 44 to 47) are agreements here:
//! html5ever's `RcDom` leaves `<selectedcontent>` empty in them too.
//!
//! Units: parses (one input, one context, one scripting flag). Under Miri
//! the test is skipped, as other crates' differentials are.

#[path = "support/dump.rs"]
mod dump;

use std::panic::{AssertUnwindSafe, catch_unwind};

use clazel_dom::exec::ExecAttr;
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_treebuilder::exec::driver::{parse_fragment_real, parse_real};
use clazel_treebuilder::exec::step::ExecContext;
use clazel_treebuilder::exec::types::EncFnsExec;
use html5ever::tendril::TendrilSink;
use html5ever::{ParseOpts, QualName};
use markup5ever_rcdom::{Handle, NodeData, RcDom};

include!("generated/wpt_tree_construction.rs");

const HTML_NS: &str = "http://www.w3.org/1999/xhtml";
const SVG_NS: &str = "http://www.w3.org/2000/svg";
const MATHML_NS: &str = "http://www.w3.org/1998/Math/MathML";
const XLINK_NS: &str = "http://www.w3.org/1999/xlink";
const XML_NS: &str = "http://www.w3.org/XML/1998/namespace";
const XMLNS_NS: &str = "http://www.w3.org/2000/xmlns/";

// ---------------------------------------------------------------------------
// Ours (as in conformance_tree_construction.rs).

/// The encoding functions for `<meta charset>`: the inputs are parsed with
/// a certain encoding, so the result never changes the tree.
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
    s.chars().map(u32::from).collect()
}

/// A fragment context as the suite writes it: `name` (HTML), `svg name`,
/// `math name`. `None` for any other prefix.
fn split_context(ctx: &str) -> Option<(Namespace, &str)> {
    match ctx.split_once(' ') {
        Some(("svg", n)) => Some((Namespace::Svg, n)),
        Some(("math", n)) => Some((Namespace::MathMl, n)),
        Some(_) => None,
        None => Some((Namespace::Html, ctx)),
    }
}

fn ours(input: &str, fragment: Option<&str>, scripting: bool) -> String {
    let input = u32s(input);
    match fragment {
        None => {
            let (p, _) = parse_real(&NoEnc, &input, Vec::new(), scripting, false);
            dump::dump_children(&p.arena, 0)
        }
        Some(ctx) => {
            let Some((ns, name)) = split_context(ctx) else {
                return format!("#unknown context {ctx:?}");
            };
            let context = ExecContext {
                ns,
                name: u32s(name),
                attrs: Vec::<ExecAttr>::new(),
                mode: DocumentMode::NoQuirks,
            };
            let (p, root, _) = parse_fragment_real(&NoEnc, &input, context, scripting);
            dump::dump_children(&p.arena, root)
        }
    }
}

// ---------------------------------------------------------------------------
// html5ever's.

fn opts(scripting: bool) -> ParseOpts {
    let mut o = ParseOpts::default();
    o.tree_builder.scripting_enabled = scripting;
    o
}

/// html5ever's tree in the suite's format; `Err` if it panicked.
fn theirs(input: &str, fragment: Option<&str>, scripting: bool) -> Result<String, String> {
    let run = || -> String {
        match fragment {
            None => {
                let dom = html5ever::parse_document(RcDom::default(), opts(scripting)).one(input);
                dump_rcdom(&dom.document)
            }
            Some(ctx) => {
                let Some((ns, name)) = split_context(ctx) else {
                    return format!("#unknown context {ctx:?}");
                };
                let ns = match ns {
                    Namespace::Svg => SVG_NS,
                    Namespace::MathMl => MATHML_NS,
                    _ => HTML_NS,
                };
                let qual = QualName::new(None, ns.into(), name.into());
                let dom = html5ever::parse_fragment(
                    RcDom::default(),
                    opts(scripting),
                    qual,
                    Vec::new(),
                    scripting,
                )
                .one(input);
                // The fragment's nodes are the children of the `html`
                // element html5ever makes the document's only child.
                let root = dom.document.children.borrow().first().cloned();
                match root {
                    Some(r) => dump_rcdom(&r),
                    None => "#no root".to_owned(),
                }
            }
        }
    };
    catch_unwind(AssertUnwindSafe(run)).map_err(|e| {
        e.downcast_ref::<&str>()
            .map(|s| (*s).to_owned())
            .or_else(|| e.downcast_ref::<String>().cloned())
            .unwrap_or_default()
    })
}

fn line(out: &mut String, depth: usize, text: &str) {
    out.push_str("| ");
    for _ in 0..depth {
        out.push_str("  ");
    }
    out.push_str(text);
    out.push('\n');
}

/// The children of `root` in the suite's format, by the rules of
/// `support/dump.rs`. Iterative, like it.
fn dump_rcdom(root: &Handle) -> String {
    enum Item {
        Node(Handle, usize),
        Content(Handle, usize),
    }
    let mut out = String::new();
    let mut stack: Vec<Item> = root
        .children
        .borrow()
        .iter()
        .rev()
        .map(|c| Item::Node(c.clone(), 0))
        .collect();
    while let Some(item) = stack.pop() {
        match item {
            Item::Content(frag, depth) => {
                line(&mut out, depth, "content");
                for c in frag.children.borrow().iter().rev() {
                    stack.push(Item::Node(c.clone(), depth.saturating_add(1)));
                }
            }
            Item::Node(n, depth) => match &n.data {
                NodeData::Doctype {
                    name,
                    public_id,
                    system_id,
                } => {
                    if public_id.is_empty() && system_id.is_empty() {
                        line(&mut out, depth, &format!("<!DOCTYPE {}>", &**name));
                    } else {
                        line(
                            &mut out,
                            depth,
                            &format!(
                                "<!DOCTYPE {} \"{}\" \"{}\">",
                                &**name, &**public_id, &**system_id
                            ),
                        );
                    }
                }
                NodeData::Element {
                    name,
                    attrs,
                    template_contents,
                    ..
                } => {
                    let prefix = match &*name.ns {
                        SVG_NS => "svg ",
                        MATHML_NS => "math ",
                        _ => "",
                    };
                    line(&mut out, depth, &format!("<{}{}>", prefix, &*name.local));
                    let mut a: Vec<(String, String)> = attrs
                        .borrow()
                        .iter()
                        .map(|at| {
                            let local: &str = &at.name.local;
                            let printed = match &*at.name.ns {
                                XLINK_NS => format!("xlink {local}"),
                                XML_NS => format!("xml {local}"),
                                XMLNS_NS => format!("xmlns {local}"),
                                _ => local.to_owned(),
                            };
                            (printed, String::from(&*at.value))
                        })
                        .collect();
                    a.sort();
                    for (k, v) in a {
                        line(&mut out, depth.saturating_add(1), &format!("{k}=\"{v}\""));
                    }
                    for c in n.children.borrow().iter().rev() {
                        stack.push(Item::Node(c.clone(), depth.saturating_add(1)));
                    }
                    if &*name.ns == HTML_NS
                        && let Some(f) = template_contents.borrow().as_ref()
                    {
                        stack.push(Item::Content(f.clone(), depth.saturating_add(1)));
                    }
                }
                NodeData::Text { contents } => {
                    line(&mut out, depth, &format!("\"{}\"", &**contents.borrow()));
                }
                NodeData::Comment { contents } => {
                    line(&mut out, depth, &format!("<!-- {} -->", &**contents));
                }
                NodeData::ProcessingInstruction { target, contents } => {
                    line(
                        &mut out,
                        depth,
                        &format!("<?{} {}?>", &**target, &**contents),
                    );
                }
                NodeData::Document => line(&mut out, depth, "#unexpected"),
            },
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Known divergences.

/// Why the two engines' trees differ, when the cause is known. Each class
/// is a place where html5ever 0.39.0 follows an older text of the standard
/// than our pinned one (`939677714d`, `src/spec/mod.rs`), or departs from
/// the text it implements; in every suite case of every class our tree is
/// the suite's expected tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Class {
    /// The standard's processing instructions: the tokenizer's processing
    /// instruction states (§13.2.5) emit a processing instruction token for
    /// `<?target data?>`, which the tree builder inserts as a
    /// `ProcessingInstruction` node (a bare `<?` at the end of the input
    /// gives nothing). html5ever's tokenizer predates
    /// them and still has the old "unexpected question mark instead of tag
    /// name" rule: a bogus comment `<!-- ?… -->`. Rule: the input contains
    /// `<?`.
    ProcessingInstruction,
    /// `search` is in the *special* category (§13.2.4.2) since the element
    /// was added (2023); html5ever's `special_tag` set lacks it. The
    /// category decides the adoption agency's furthest block, the `li` /
    /// `dd` / `dt` start tag loops of "in body" and "any other end tag", so
    /// html5ever reparents or closes across a `search` where the standard
    /// stops at it. Rule: the input contains `<search`.
    SearchSpecial,
    /// "after head", anything else: "Insert an HTML element for a "body"
    /// start tag token with no attributes. Set the frameset-ok flag to
    /// "ok". ..." (§13.2.6.4.6). The middle step is newer than html5ever,
    /// which keeps the flag as the "in head" `template` start tag left it
    /// ("not ok"), so a later `<frameset>` is ignored where the standard
    /// replaces the body. Rule: the input contains `<template` and
    /// `<frameset`.
    FramesetOkAfterHead,
    /// The standard's "parsing template contents" (a `template` element on
    /// the stack of open elements, or a `template` fragment context) decides
    /// the `form` start tag rules of "in body" and "in table" and the `form`
    /// end tag rule of "in body": while parsing template contents a nested
    /// `form` is inserted, "in table" inserts a `form` too, the form element
    /// pointer is not set, and `</form>` pops to the `form` by name.
    /// html5ever checks only for a `template` on the stack (so a `template`
    /// fragment context does not count: it sets the pointer, ignores the
    /// nested `form` and closes `</form>` through the pointer), and its "in
    /// table" rule ignores the `form` whenever a `template` is on the stack.
    /// Rule: the input contains `<form` and either `<template` or the
    /// fragment context is `template`.
    TemplateContentsForm,
    /// "in body", an `input` start tag: "If the parser's fragment context
    /// element is a select element (fragment case): Parse error. Ignore the
    /// token. Return." html5ever 0.39.0 has the check but only reports the
    /// error (no return), then inserts the `input`: a bug in html5ever
    /// against the text it implements. Rule: the fragment context is
    /// `select` and the input contains `<input`.
    SelectFragmentInput,
    /// "in table body", a `caption`, `col`, `colgroup`, `tbody`, `tfoot` or
    /// `thead` start tag or a `table` end tag: "If the stack of open
    /// elements does not have a tbody, thead, or tfoot element in table
    /// scope, this is a parse error; ignore the token." html5ever's set for
    /// this test is `table`, `tbody`, `tfoot` (no `thead`): a bug in
    /// html5ever, visible only when no `table` is open above the `thead`,
    /// i.e. inside a `template`'s contents (in a document a `thead` always
    /// has its `table` below it). html5ever then ignores the token where the
    /// standard closes the `thead`. Found by the random inputs only. Rule:
    /// the input contains `<thead` and either `<template` or the fragment
    /// context is `template`.
    TableBodyScopeThead,
}

impl Class {
    fn reason(self) -> &'static str {
        match self {
            Class::ProcessingInstruction => {
                "the standard's processing instruction states and nodes; html5ever predates them and makes a bogus comment of <?...>"
            }
            Class::SearchSpecial => {
                "search is in the special category (2023); html5ever's special_tag set lacks it"
            }
            Class::FramesetOkAfterHead => {
                "\"after head\" anything else sets frameset-ok to \"ok\" in the standard; html5ever keeps \"not ok\" from an earlier template"
            }
            Class::TemplateContentsForm => {
                "the standard's \"parsing template contents\" (template on the stack or template context) governs form in \"in body\" and \"in table\"; html5ever checks only the stack, and ignores form in \"in table\" inside a template"
            }
            Class::SelectFragmentInput => {
                "\"in body\" input start tag in a select fragment: the standard ignores it; html5ever reports the error but inserts it (missing return)"
            }
            Class::TableBodyScopeThead => {
                "\"in table body\": the standard's tbody/thead/tfoot-in-table-scope test; html5ever tests table/tbody/tfoot, so a thead with no table above it (template contents) blocks"
            }
        }
    }

    /// The class's rule: the input (and context) can show the cause.
    fn applies(self, input: &str, fragment: Option<&str>) -> bool {
        let l = input.to_ascii_lowercase();
        match self {
            Class::ProcessingInstruction => l.contains("<?"),
            Class::SearchSpecial => l.contains("<search"),
            Class::FramesetOkAfterHead => l.contains("<template") && l.contains("<frameset"),
            Class::TemplateContentsForm => {
                l.contains("<form") && (l.contains("<template") || fragment == Some("template"))
            }
            Class::SelectFragmentInput => fragment == Some("select") && l.contains("<input"),
            Class::TableBodyScopeThead => {
                l.contains("<thead") && (l.contains("<template") || fragment == Some("template"))
            }
        }
    }
}

/// Every class, in the order [`classify`] tries them.
const CLASSES: &[Class] = &[
    Class::ProcessingInstruction,
    Class::SearchSpecial,
    Class::FramesetOkAfterHead,
    Class::TemplateContentsForm,
    Class::SelectFragmentInput,
    Class::TableBodyScopeThead,
];

/// The suite cases that differ, by file and index, with their class. A
/// listed case must differ in every scripting run, its class's rule must
/// apply to it, and our tree must be the suite's; otherwise the test fails.
const KNOWN_SUITE: &[(&str, &[usize], Class)] = &[
    (
        "processing-instructions.dat",
        &[
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
            46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 100, 101,
            102, 103, 104, 105, 107, 108, 109, 110, 113, 114, 115, 116, 117, 118, 119, 122, 123,
        ],
        Class::ProcessingInstruction,
    ),
    ("tests1.dat", &[39, 43, 46], Class::ProcessingInstruction),
    ("html5test-com.dat", &[11], Class::ProcessingInstruction),
    ("search-element.dat", &[3, 4, 5, 6, 7], Class::SearchSpecial),
    ("template.dat", &[43, 44, 45], Class::FramesetOkAfterHead),
    (
        "template.dat",
        &[116, 119, 123],
        Class::TemplateContentsForm,
    ),
    ("tests_innerHTML_1.dat", &[75], Class::SelectFragmentInput),
];

fn known_suite(file: &str, index: usize) -> Option<Class> {
    KNOWN_SUITE
        .iter()
        .find(|(f, ix, _)| *f == file && ix.contains(&index))
        .map(|(_, _, c)| *c)
}

/// The class of a difference on a generated input (no expected tree): the
/// first class whose rule applies; `None` makes it a failure.
fn classify(input: &str, fragment: Option<&str>) -> Option<Class> {
    CLASSES.iter().copied().find(|c| c.applies(input, fragment))
}

// ---------------------------------------------------------------------------
// Random inputs.

/// A small deterministic generator (xorshift64*), so runs are repeatable.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }
    fn pick<T: Copy>(&mut self, from: &[T], fallback: T) -> T {
        let i = self.below(from.len());
        from.get(i).copied().unwrap_or(fallback)
    }
}

/// Tag names the insertion modes switch on: the special elements, the
/// formatting elements, tables, select, template, frameset, foreign content
/// and its breakouts and integration points, raw text elements, and an
/// unknown name.
const TAGS: &[&str] = &[
    "html",
    "head",
    "body",
    "title",
    "meta",
    "base",
    "link",
    "style",
    "script",
    "noscript",
    "template",
    "frameset",
    "frame",
    "noframes",
    "p",
    "div",
    "span",
    "a",
    "b",
    "i",
    "em",
    "strong",
    "font",
    "nobr",
    "s",
    "u",
    "code",
    "big",
    "small",
    "tt",
    "strike",
    "table",
    "caption",
    "colgroup",
    "col",
    "tbody",
    "thead",
    "tfoot",
    "tr",
    "td",
    "th",
    "select",
    "option",
    "optgroup",
    "hr",
    "input",
    "keygen",
    "textarea",
    "button",
    "form",
    "li",
    "ul",
    "ol",
    "dd",
    "dt",
    "dl",
    "h1",
    "h2",
    "pre",
    "listing",
    "plaintext",
    "xmp",
    "iframe",
    "noembed",
    "image",
    "img",
    "br",
    "applet",
    "marquee",
    "object",
    "math",
    "svg",
    "mi",
    "mo",
    "mtext",
    "annotation-xml",
    "foreignObject",
    "desc",
    "rb",
    "rt",
    "rp",
    "rtc",
    "ruby",
    "address",
    "menu",
    "search",
    "hgroup",
    "summary",
    "details",
    "main",
    "area",
    "wbr",
    "embed",
    "param",
    "source",
    "track",
    "selectedcontent",
    "frameset",
    "foo",
];

const ATTRS: &[&str] = &[
    " id=x",
    " class=\"a b\"",
    " type=hidden",
    " type=text",
    " encoding=\"text/html\"",
    " xlink:href=u",
    " xml:lang=en",
    " xmlns=\"http://www.w3.org/2000/svg\"",
    " definitionurl=d",
    " viewbox=\"0 0 1 1\"",
    " color=red",
    " size=2",
    " face=f",
];

const TEXT: &[&str] = &[
    "x", " ", "\n", "\t", "ab", "&amp;", "&lt", "\0", "\r\n", "\u{e9}", "  y  ",
];

/// One random input: tags, end tags, text, comments and a DOCTYPE, mixed
/// so that most insertion modes are reached.
fn soup(rng: &mut Rng) -> String {
    let mut s = String::new();
    if rng.below(3) == 0 {
        s.push_str(rng.pick(
            &[
                "<!DOCTYPE html>",
                "<!doctype html public \"-//W3C//DTD HTML 4.01//EN\">",
                "<!DOCTYPE foo>",
            ],
            "",
        ));
    }
    let n = rng.below(14).saturating_add(1);
    for _ in 0..n {
        match rng.below(10) {
            0..=3 => {
                s.push('<');
                s.push_str(rng.pick(TAGS, "p"));
                if rng.below(3) == 0 {
                    s.push_str(rng.pick(ATTRS, ""));
                }
                if rng.below(8) == 0 {
                    s.push('/');
                }
                s.push('>');
            }
            4..=6 => {
                s.push_str("</");
                s.push_str(rng.pick(TAGS, "p"));
                s.push('>');
            }
            7 | 8 => s.push_str(rng.pick(TEXT, "x")),
            // No `<?`: every input with one differs (the processing
            // instruction class), which would hide any other cause in it;
            // the suite's 175 runs with `<?` cover that class.
            _ => s.push_str(rng.pick(&["<!--c-->", "<![CDATA[d]]>", "<!x>", "</>", "<"], "")),
        }
    }
    s
}

/// Contexts random fragments are parsed in.
const CONTEXTS: &[&str] = &[
    "div", "body", "td", "tr", "table", "select", "template", "html", "svg path", "math mi",
    "textarea", "title", "noscript",
];

// ---------------------------------------------------------------------------

#[derive(Default)]
struct Tally {
    pass: u64,
    xfail: u64,
    fail: u64,
    total: u64,
    known: Vec<(Class, String)>,
    failures: Vec<String>,
}

impl Tally {
    fn record(&mut self, id: &str, outcome: Outcome) {
        self.total = self.total.saturating_add(1);
        match outcome {
            Outcome::Agree => self.pass = self.pass.saturating_add(1),
            Outcome::Known(c) => {
                self.xfail = self.xfail.saturating_add(1);
                self.known.push((c, id.to_owned()));
            }
            Outcome::Fail(msg) => {
                self.fail = self.fail.saturating_add(1);
                if self.failures.len() < 40 {
                    self.failures.push(format!("{id}: {msg}"));
                }
            }
        }
    }

    fn print(&self, suite: &str) {
        let mut classes: Vec<Class> = self.known.iter().map(|(c, _)| *c).collect();
        classes.sort();
        classes.dedup();
        for c in classes {
            let ids: Vec<&str> = self
                .known
                .iter()
                .filter(|(k, _)| *k == c)
                .map(|(_, id)| id.as_str())
                .collect();
            println!(
                "{suite}: {} known divergences {c:?} ({}): {}",
                ids.len(),
                c.reason(),
                ids.iter().take(12).copied().collect::<Vec<_>>().join(", ")
            );
        }
        for f in &self.failures {
            println!("DIVERGENCE {f}\n");
        }
        println!(
            "clazel-conformance: suite=\"{suite}\" pass={} xfail={} fail={} total={}",
            self.pass, self.xfail, self.fail, self.total
        );
    }
}

enum Outcome {
    Agree,
    Known(Class),
    Fail(String),
}

/// Both trees, without the final line feed; `Err` if html5ever panicked.
fn both(input: &str, fragment: Option<&str>, scripting: bool) -> Result<(String, String), String> {
    let mut a = ours(input, fragment, scripting);
    let mut b = theirs(input, fragment, scripting).map_err(|p| {
        format!("html5ever panicked ({p}) on {input:?} fragment={fragment:?} scripting={scripting}")
    })?;
    if a.ends_with('\n') {
        a.pop();
    }
    if b.ends_with('\n') {
        b.pop();
    }
    Ok((a, b))
}

fn show(input: &str, fragment: Option<&str>, scripting: bool, a: &str, b: &str) -> String {
    format!(
        "data={input:?} fragment={fragment:?} scripting={scripting}\n--- ours\n{a}\n--- html5ever\n{b}"
    )
}

/// A suite case: a difference is known only if the case is listed, its
/// class's rule applies, and our tree is the suite's.
fn compare_suite(case: &Case, scripting: bool, listed: Option<Class>) -> Outcome {
    let (a, b) = match both(case.data, case.fragment, scripting) {
        Ok(t) => t,
        Err(e) => return Outcome::Fail(e),
    };
    if a == b {
        return Outcome::Agree;
    }
    let verdict = if a == case.document {
        "ours matches the suite"
    } else if b == case.document {
        "html5ever matches the suite: BUG IN OURS"
    } else {
        "neither matches the suite"
    };
    let applies = listed.is_some_and(|c| c.applies(case.data, case.fragment));
    match listed {
        Some(c) if applies && a == case.document => Outcome::Known(c),
        Some(c) => Outcome::Fail(format!(
            "listed as {c:?} but {}; {verdict}; {}",
            if applies {
                "ours is not the suite's tree"
            } else {
                "its rule does not apply"
            },
            show(case.data, case.fragment, scripting, &a, &b)
        )),
        None => Outcome::Fail(format!(
            "{verdict}; {}",
            show(case.data, case.fragment, scripting, &a, &b)
        )),
    }
}

/// A generated input: a difference is known if a class's rule applies.
fn compare_random(input: &str, fragment: Option<&str>, scripting: bool) -> Outcome {
    let (a, b) = match both(input, fragment, scripting) {
        Ok(t) => t,
        Err(e) => return Outcome::Fail(e),
    };
    if a == b {
        return Outcome::Agree;
    }
    match classify(input, fragment) {
        Some(c) => Outcome::Known(c),
        None => Outcome::Fail(format!(
            "no class applies; {}",
            show(input, fragment, scripting, &a, &b)
        )),
    }
}

/// Random inputs generated (each parsed once).
const RANDOM_INPUTS: u32 = 10_000;

#[test]
#[cfg_attr(miri, ignore)]
fn html5ever_differential() {
    // Suite inputs.
    let mut suite = Tally::default();
    let mut stale: Vec<String> = Vec::new();
    for case in CASES {
        let flags: &[bool] = match case.scripting {
            Some(true) => &[true],
            Some(false) => &[false],
            None => &[false, true],
        };
        let listed = known_suite(case.file, case.index);
        for &scripting in flags {
            let id = format!(
                "{}:{}/{}",
                case.file,
                case.index,
                if scripting { "on" } else { "off" }
            );
            let outcome = compare_suite(case, scripting, listed);
            if let (Some(_), Outcome::Agree) = (listed, &outcome) {
                stale.push(id.clone());
            }
            suite.record(&id, outcome);
        }
    }
    suite.print("html5ever 0.39.0 differential, WPT tree-construction inputs");

    // Random inputs.
    let mut random = Tally::default();
    let mut rng = Rng(0x0C1A_2E1B_0D5E_4711);
    for i in 0..RANDOM_INPUTS {
        let input = soup(&mut rng);
        let fragment = if rng.below(4) == 0 {
            Some(rng.pick(CONTEXTS, "div"))
        } else {
            None
        };
        let scripting = rng.below(2) == 0;
        random.record(
            &format!("random:{i}"),
            compare_random(&input, fragment, scripting),
        );
    }
    random.print("html5ever 0.39.0 differential, random tag soup");

    assert!(
        stale.is_empty(),
        "listed as divergences but the engines agree: {stale:?}"
    );
    assert_eq!(
        suite.fail, 0,
        "{} unexplained divergences on suite inputs",
        suite.fail
    );
    assert_eq!(
        random.fail, 0,
        "{} unexplained divergences on random inputs",
        random.fail
    );
}
