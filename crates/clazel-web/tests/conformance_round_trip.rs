//! `innerHTML` round trips (Phase 7 item 7.13): for every element of every
//! tree the html5lib tree-construction suite builds, serialize its children
//! with `clazel_web::serialize` and fragment-parse the result with that
//! element as the context, through `clazel-treebuilder`'s proven driver.
//! The new children must print as the old ones did.
//!
//! The standard does not promise this round trip, and the suite's trees hold
//! the cases where it fails: trees whose shape no markup produces. Each
//! difference must fall in a [`Class`] below, whose rule is a predicate over
//! the tree and the serialization; a difference outside every class fails
//! the test, and a class that never applies fails too, so no class is left
//! over. The classes are narrow so that a serializer bug does not hide in
//! one: every context outside them must round trip exactly.
//!
//! Units: contexts (one element of one tree, with the tree's scripting
//! flag). A case naming no scripting flag runs with scripting off. Under
//! Miri the test runs every 100th case and at most 2 elements of each.

#[path = "../../clazel-treebuilder/tests/support/dump.rs"]
mod dump;

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_treebuilder::exec::driver::{parse_fragment_real, parse_real};
use clazel_treebuilder::exec::step::ExecContext;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::serialize::serialize_fragment;

include!("../../clazel-treebuilder/tests/generated/wpt_tree_construction.rs");

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

fn context_of(ctx: &str) -> Option<(Namespace, Vec<u32>)> {
    match ctx.split_once(' ') {
        Some(("svg", n)) => Some((Namespace::Svg, u32s(n))),
        Some(("math", n)) => Some((Namespace::MathMl, u32s(n))),
        Some(_) => None,
        None => Some((Namespace::Html, u32s(ctx))),
    }
}

fn is_html(ns: &Option<Namespace>, name: &[u32], s: &str) -> bool {
    matches!(ns, Some(Namespace::Html)) && name == u32s(s).as_slice()
}

fn copy_ns(ns: &Namespace) -> Namespace {
    match ns {
        Namespace::Html => Namespace::Html,
        Namespace::MathMl => Namespace::MathMl,
        Namespace::Svg => Namespace::Svg,
        Namespace::XLink => Namespace::XLink,
        Namespace::Xml => Namespace::Xml,
        Namespace::Xmlns => Namespace::Xmlns,
    }
}

fn doc_mode(arena: &Arena) -> DocumentMode {
    match arena.kind(0) {
        ExecKind::Document { mode, .. } => match mode {
            DocumentMode::NoQuirks => DocumentMode::NoQuirks,
            DocumentMode::Quirks => DocumentMode::Quirks,
            DocumentMode::LimitedQuirks => DocumentMode::LimitedQuirks,
        },
        _ => DocumentMode::NoQuirks,
    }
}

/// The parsed tree of a case: its arena and the node whose children the
/// suite prints.
fn parse_case(case: &Case, scripting: bool) -> Option<(Arena, usize)> {
    let input = u32s(case.data);
    match case.fragment {
        None => {
            let (p, _) = parse_real(&NoEnc, &input, Vec::new(), scripting, false);
            Some((p.arena, 0))
        }
        Some(ctx) => {
            let (ns, name) = context_of(ctx)?;
            let context = ExecContext {
                ns,
                name,
                attrs: Vec::<ExecAttr>::new(),
                mode: DocumentMode::NoQuirks,
                in_form: false,
            };
            let (p, root, _) = parse_fragment_real(&NoEnc, &input, context, scripting);
            Some((p.arena, root))
        }
    }
}

/// The elements under `root` (template contents included), each with
/// whether it has a form element among its ancestors or is one.
fn elements(arena: &Arena, root: usize) -> Vec<(usize, bool)> {
    let mut out = Vec::new();
    let mut stack = vec![(root, false)];
    while let Some((n, in_form)) = stack.pop() {
        let mut in_form = in_form;
        if let ExecKind::Element {
            namespace,
            local_name,
            template_contents,
            ..
        } = arena.kind(n)
        {
            in_form = in_form || is_html(namespace, local_name, "form");
            out.push((n, in_form));
            if let Some(c) = template_contents {
                stack.push((*c, in_form));
            }
        }
        for &c in arena.children(n).iter().rev() {
            stack.push((c, in_form));
        }
    }
    out
}

/// A reason why serializing and re-parsing cannot give the tree back.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    /// A carriage return in the data: the serializer writes it as is, and
    /// the parser's input preprocessing (HTML §13.2.3.5) turns it into a
    /// line feed.
    CarriageReturn,
    /// A processing instruction: its serialization ends at the first `>`,
    /// whatever the data holds.
    ProcessingInstruction,
    /// A `plaintext` element: no markup ends it, so what follows it in the
    /// serialization (its end tag, its parents' end tags) becomes its text.
    Plaintext,
    /// A `script` element whose text has `<!--` and `<script`: the script
    /// data double escaped state swallows the end tag the serializer writes.
    ScriptDoubleEscape,
    /// An `a`, `nobr`, `p` or `form` element inside another of the same
    /// name: the parser never nests them directly (the adoption agency
    /// algorithm, "in body"'s implied end tags and the form element
    /// pointer), so re-parsing flattens the tree.
    Nested,
    /// A `form` element under a context that is in a form: the form element
    /// pointer (§13.4 step 19) makes the parser ignore its start tag.
    FormInForm,
}

const CLASSES: [(Class, &str); 6] = [
    (Class::CarriageReturn, "carriage return in the data"),
    (Class::ProcessingInstruction, "processing instruction"),
    (Class::Plaintext, "plaintext element"),
    (
        Class::ScriptDoubleEscape,
        "script text with <!-- and <script",
    ),
    (Class::Nested, "a, nobr, p or form nested in its own name"),
    (Class::FormInForm, "form element under a form context"),
];

/// Whether `hay` has `needle` (lower case ASCII) in it, ignoring ASCII case.
fn contains(hay: &[u32], needle: &str) -> bool {
    let n = u32s(needle);
    let lower: Vec<u32> = hay
        .iter()
        .map(|&c| match char::from_u32(c) {
            Some(ch) => u32::from(ch.to_ascii_lowercase()),
            None => c,
        })
        .collect();
    !n.is_empty() && lower.windows(n.len()).any(|w| w == n.as_slice())
}

/// The classes a context falls in: `e` is the context element, `container`
/// the node whose children were serialized, `html` what was written.
fn classes_of(
    arena: &Arena,
    e: usize,
    container: usize,
    in_form: bool,
    html: &[u32],
) -> Vec<Class> {
    let mut found: Vec<Class> = Vec::new();
    if html.contains(&0x0D) {
        found.push(Class::CarriageReturn);
    }
    if let ExecKind::Element {
        namespace,
        local_name,
        ..
    } = arena.kind(e)
        && is_html(namespace, local_name, "plaintext")
    {
        found.push(Class::Plaintext);
    }
    // Walk the subtree, with a bit for each of the names above it.
    const NAMES: [&str; 4] = ["a", "nobr", "p", "form"];
    let mut stack: Vec<(usize, u8)> = vec![(container, 0)];
    while let Some((n, above)) = stack.pop() {
        let mut here = above;
        match arena.kind(n) {
            ExecKind::ProcessingInstruction { .. } => found.push(Class::ProcessingInstruction),
            ExecKind::Element {
                namespace,
                local_name,
                template_contents,
                ..
            } => {
                if is_html(namespace, local_name, "plaintext") {
                    found.push(Class::Plaintext);
                }
                if is_html(namespace, local_name, "script") {
                    let text: Vec<u32> = arena
                        .children(n)
                        .iter()
                        .filter_map(|&c| match arena.kind(c) {
                            ExecKind::Text { data } => Some(data.clone()),
                            _ => None,
                        })
                        .flatten()
                        .collect();
                    if contains(&text, "<!--") && contains(&text, "<script") {
                        found.push(Class::ScriptDoubleEscape);
                    }
                }
                if in_form && is_html(namespace, local_name, "form") {
                    found.push(Class::FormInForm);
                }
                for (i, name) in NAMES.iter().enumerate() {
                    if is_html(namespace, local_name, name) {
                        let bit = 1u8 << i;
                        if above & bit != 0 {
                            found.push(Class::Nested);
                        }
                        here |= bit;
                    }
                }
                if let Some(c) = template_contents {
                    stack.push((*c, here));
                }
            }
            _ => {}
        }
        for &c in arena.children(n) {
            stack.push((c, here));
        }
    }
    found
}

fn s(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

#[test]
fn inner_html_round_trip() {
    let stride = if cfg!(miri) { 100 } else { 1 };
    let per_case = if cfg!(miri) { 2 } else { usize::MAX };
    let mut total = 0usize;
    let mut pass = 0usize;
    let mut by_class: Vec<usize> = CLASSES.iter().map(|_| 0).collect();
    let mut xfail = 0usize;
    let mut failed: Vec<String> = Vec::new();
    for case in CASES.iter().step_by(stride) {
        let scripting = case.scripting.unwrap_or(false);
        let Some((arena, root)) = parse_case(case, scripting) else {
            continue;
        };
        for (e, in_form) in elements(&arena, root).into_iter().take(per_case) {
            let ExecKind::Element {
                namespace,
                local_name,
                attributes,
                template_contents,
                ..
            } = arena.kind(e)
            else {
                continue;
            };
            let Some(ns) = namespace.as_ref().map(copy_ns) else {
                continue;
            };
            let html = serialize_fragment(&arena, e, scripting);
            let container = match template_contents {
                Some(c) if is_html(namespace, local_name, "template") => *c,
                _ => e,
            };
            let expected = dump::dump_children(&arena, container);
            let context = ExecContext {
                ns,
                name: local_name.clone(),
                attrs: attributes
                    .iter()
                    .map(|a| ExecAttr {
                        namespace: a.namespace.as_ref().map(copy_ns),
                        prefix: a.prefix.clone(),
                        local_name: a.local_name.clone(),
                        value: a.value.clone(),
                    })
                    .collect(),
                mode: doc_mode(&arena),
                in_form,
            };
            let (p, r2, _) = parse_fragment_real(&NoEnc, &html, context, scripting);
            let actual = dump::dump_children(&p.arena, r2);
            total = total.saturating_add(1);
            if actual == expected {
                pass = pass.saturating_add(1);
                continue;
            }
            let found = classes_of(&arena, e, container, in_form, &html);
            if found.is_empty() {
                failed.push(format!(
                    "{}:{} context={} in_form={in_form} html={:?}\n--- expected\n{expected}\n--- actual\n{actual}",
                    case.file,
                    case.index,
                    s(local_name),
                    s(&html),
                ));
            } else {
                xfail = xfail.saturating_add(1);
                for ((c, _), n) in CLASSES.iter().zip(by_class.iter_mut()) {
                    if found.contains(c) {
                        *n = n.saturating_add(1);
                    }
                }
            }
        }
    }
    for f in &failed {
        println!("MISMATCH {f}\n");
    }
    assert!(
        failed.is_empty(),
        "{} unexplained differences",
        failed.len()
    );
    assert_eq!(pass.saturating_add(xfail), total);
    if cfg!(miri) {
        return;
    }
    println!("innerHTML round trip: expected failures by class (a context can be in several):");
    for ((c, why), n) in CLASSES.iter().zip(by_class.iter()) {
        println!("  {c:?}: {why}: {n}");
        assert!(*n > 0, "class {c:?} applies to nothing: remove it");
    }
    println!(
        "clazel-conformance: suite=\"innerHTML round trip (html5lib trees)\" pass={pass} xfail={xfail} fail=0 total={total}"
    );
}

/// Parse `html` as a fragment in a context element named `name` and
/// serialize the result, then check that parsing that again gives the same
/// tree.
fn through(ns: Namespace, name: &str, html: &str, scripting: bool) -> String {
    let make = |ns: Namespace| ExecContext {
        ns,
        name: u32s(name),
        attrs: Vec::<ExecAttr>::new(),
        mode: DocumentMode::NoQuirks,
        in_form: false,
    };
    let (p, root, _) = parse_fragment_real(&NoEnc, &u32s(html), make(copy_ns(&ns)), scripting);
    let out = serialize_fragment(&p.arena, root, scripting);
    let (p2, root2, _) = parse_fragment_real(&NoEnc, &out, make(ns), scripting);
    assert_eq!(
        dump::dump_children(&p.arena, root),
        dump::dump_children(&p2.arena, root2),
        "re-parsing {:?}",
        s(&out)
    );
    s(&out)
}

/// Inputs written the way the serializer writes them come back unchanged,
/// and the tree survives the round trip.
#[test]
fn canonical_html_is_a_fixed_point() {
    let div = |h: &str| through(Namespace::Html, "div", h, false);
    for h in [
        "<p class=\"a&amp;b\">x &lt; y&nbsp;z</p><br><img src=\"x\">",
        "<pre>\n\nfoo</pre>",
        "<textarea>\n\nfoo &amp; bar</textarea>",
        "<listing>\n\nfoo</listing>",
        "<template><b>x</b></template>",
        "<script>if(a<b&&c>d){}</script>",
        "<style>a>b{}</style><xmp><b>&amp;</b></xmp>",
        "<!--a--><p>b</p><!---->",
        "<a title=\"&quot;q&quot; &lt;&gt;\">x</a>",
        "<table><tbody><tr><td>x</td></tr></tbody></table>",
        "<svg viewBox=\"0 0 1 1\"><use xlink:href=\"#a\"></use></svg>",
        "<math><mi>x</mi></math>",
    ] {
        assert_eq!(div(h), h, "input {h:?}");
    }
    // Not canonical: the parser drops one line feed after `pre`, so the
    // tree has none, and the serializer writes none.
    assert_eq!(div("<pre>\nfoo</pre>"), "<pre>foo</pre>");
    // Nested templates, and end tags and quotes the parser supplies.
    assert_eq!(
        div("<template><b>x</b><template><i>y</i></template></template>"),
        "<template><b>x</b><template><i>y</i></template></template>"
    );
    assert_eq!(
        div("<ul><li>1<li>2</ul><img src=x>"),
        "<ul><li>1</li><li>2</li></ul><img src=\"x\">"
    );
}

/// The scripting flag decides how a `noscript` is parsed (as text with the
/// flag on, as markup with it off) and how it is serialized (literally with
/// it on, escaped with it off); the round trip holds for each setting.
#[test]
fn noscript_round_trips_with_the_flag() {
    for scripting in [false, true] {
        assert_eq!(
            through(
                Namespace::Html,
                "div",
                "<noscript><p>x</p></noscript>",
                scripting
            ),
            "<noscript><p>x</p></noscript>"
        );
    }
}
