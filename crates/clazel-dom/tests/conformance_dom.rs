//! `clazel-dom` conformance (Phase 4 item 4.11): the arena's public
//! operations against official data and against an independent engine.
//! Two suites, reported by one `clazel-conformance:` line each.
//!
//! # Suite 1: html5lib tree-construction trees (official data)
//!
//! The expected trees of the html5lib tree-construction tests vendored from
//! WPT for `clazel-treebuilder`
//! (`../clazel-treebuilder/tests/data/wpt-tree-construction/`, converted by
//! `cargo xtask testdata` into `generated/wpt_tree_construction.rs`). The
//! generated table is shared by `include!` with a relative path, never
//! copied, and so is the suite-format printer (`support/dump.rs`).
//! `clazel-treebuilder` is not a dev-dependency here: it depends on this
//! crate, and a dev-dependency cycle would build the crate twice with
//! incompatible types.
//!
//! For each case, the expected tree (`#document`: indentation is depth,
//! `<tag>`, `<svg tag>`, `<math tag>`, `name="value"` lines, `"text"`,
//! `<!-- comment -->`, `<!DOCTYPE ...>`, `<?target data?>`, `content` for a
//! template's contents) is **read back into an arena using only `clazel-dom`'s
//! own operations** (`Arena::new`, `create`, `create_template_contents`,
//! `append`, `append_attribute`), then printed again by a walk over the
//! arena's readers (`children`, `kind`; `support/dump.rs`) and compared byte
//! for byte with the original text. A `#document-fragment` case builds under
//! a parentless `DocumentFragment`, as the fragment algorithm's root. The
//! well-formedness predicate `wf` of `src/spec.rs` is a ghost predicate and
//! cannot be called; its executable statement is [`check_wf`] below, which
//! re-checks, on every tree built, through the readers, each clause the
//! proofs establish (parent/child agreement, no duplicate children, only
//! documents, elements and fragments have children, node 0 the only document
//! and parentless, template contents a parentless fragment hosted by its
//! template, acyclicity, `previous_sibling`, `last_child`, `has_child` and
//! `is_inclusive_ancestor` agreeing with the children lists).
//!
//! A case passes if it builds, [`check_wf`] holds and the printout equals
//! the expected text. Units: cases. `total` is the length of `CASES`
//! (every case of every non-scripted `.dat` file; the scripted ones are not
//! trees to build and are counted on a separate line). The trees are the
//! parser's outputs, so this suite shows that every tree shape the standard
//! expects of an HTML parser is representable in, and read back from, the
//! arena. [`KNOWN_MISMATCHES`] lists, by name with a cause, the cases that
//! are expected not to round-trip (none today).
//!
//! # Suite 2: differential against `markup5ever_rcdom` 0.39.0
//!
//! Random sequences of tree operations from a seeded PRNG (`SplitMix64`,
//! written here, no `rand`), applied to both the arena and an `RcDom`
//! (html5ever's tree, written by an independent team). Operations: create
//! (element in the HTML, SVG or MathML namespace with attributes of the
//! no-namespace, XLink, XML and XMLNS kinds; a `template` gets its
//! contents; text; comment; doctype; processing instruction), append,
//! insert-before, remove, **moving a subtree** (append or insert-before of a
//! node that has a parent, under the same or another parent, including a
//! template's contents), move-all-children (`reparent_children`), append to a
//! text node's data, append an attribute and set the document's mode.
//! Every node carries a unique id in its text, name or a `u` attribute, so
//! two trees print equal only if each node is at the same place.
//!
//! After every operation, both whole trees (the document and every
//! detached subtree, in the suite's format) and the document's mode are
//! printed and compared, and [`check_wf`] runs on the arena (so the
//! invariants the arena proves, no cycles and parent/child agreement among
//! them, are also checked on every state reached). A sequence agrees if
//! every operation does. Units: sequences, `agreed / total`.
//!
//! The preconditions of the arena's operations are the parser's class of
//! calls (`insert_requires`); the generator makes only such calls. Its
//! cycle check is **host-including** (a template's contents lead back to its
//! template), which is stricter than the spec's `is_inclusive_ancestor`
//! (`spec.rs` leaves that to the parser, which never inserts a template into
//! its own contents); the test also checks the arena's reader never says "no
//! cycle" where this one says "cycle".
//!
//! One deliberate difference in how the oracle is driven: `RcDom`'s
//! `append_before_sibling` computes the reference child's index *before* it
//! detaches the node, so moving a node to just before a later sibling of its
//! own parent lands one place late (DOM's "pre-insert" adopts first). The
//! test therefore always calls `remove_from_parent` itself first, as DOM's
//! "insert" does (§4.2.3 step 7.1, "adopt"), and `RcDom` then does what the
//! standard says.
//!
//! Under Miri both suites run on a stride of the inputs (`cfg!(miri)`), the
//! summary lines are not printed (they would report a sample as a total),
//! and the generated table is read at compile time, so Miri's isolation is
//! not involved.

#[path = "../../clazel-treebuilder/tests/support/dump.rs"]
mod dump;

use std::cell::RefCell;

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use html5ever::tendril::StrTendril;
use html5ever::tree_builder::{ElementFlags, NodeOrText, QuirksMode, TreeSink};
use html5ever::{Attribute, LocalName, Prefix, QualName};
use markup5ever_rcdom::{Handle, Node, NodeData, RcDom};

include!("../../clazel-treebuilder/tests/generated/wpt_tree_construction.rs");

/// Cases whose expected tree does not round-trip through the arena, by
/// `file:index`, with the cause. None today.
const KNOWN_MISMATCHES: &[(&str, &str)] = &[];

fn u32s(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn create(a: &mut Arena, kind: ExecKind) -> Result<usize, String> {
    a.create(kind)
        .ok_or_else(|| "the node limit is far away".to_owned())
}

fn may_have_children(k: &ExecKind) -> bool {
    matches!(
        k,
        ExecKind::Document { .. } | ExecKind::Element { .. } | ExecKind::DocumentFragment { .. }
    )
}

// ---------------------------------------------------------------------------
// The executable statement of `wf`.

/// Every clause of `wf` (`src/spec.rs`) that the readers can see, plus the
/// readers' agreement with the children lists. `Err` names the first clause
/// that fails.
fn check_wf(a: &Arena) -> Result<(), String> {
    let n = a.len();
    if !matches!(a.kind(0), ExecKind::Document { .. }) {
        return Err("node 0 is not the document".to_owned());
    }
    if a.parent(0).is_some() {
        return Err("the document has a parent".to_owned());
    }
    for id in 0..n {
        let kind = a.kind(id);
        if id != 0 && matches!(kind, ExecKind::Document { .. }) {
            return Err(format!("node {id} is a second document"));
        }
        if a.wrapper(id).is_some() {
            return Err(format!("node {id} has a wrapper in Phase 4"));
        }
        let kids = a.children(id);
        if !kids.is_empty() && !may_have_children(kind) {
            return Err(format!("node {id} has children but cannot"));
        }
        if a.has_child(id) == kids.is_empty() {
            return Err(format!("has_child({id}) disagrees with children"));
        }
        if a.last_child(id) != kids.last().copied() {
            return Err(format!("last_child({id}) disagrees with children"));
        }
        for (i, &c) in kids.iter().enumerate() {
            if c >= n {
                return Err(format!("child {c} of {id} is out of range"));
            }
            if a.parent(c) != Some(id) {
                return Err(format!("child {c} of {id} has parent {:?}", a.parent(c)));
            }
            if kids.iter().filter(|&&x| x == c).count() != 1 {
                return Err(format!("child {c} is listed twice by {id}"));
            }
            let want = i.checked_sub(1).and_then(|j| kids.get(j)).copied();
            if a.previous_sibling(c) != want {
                return Err(format!("previous_sibling({c}) is wrong"));
            }
        }
        match a.parent(id) {
            Some(p) => {
                if p >= n {
                    return Err(format!("parent {p} of {id} is out of range"));
                }
                if a.children(p).iter().filter(|&&x| x == id).count() != 1 {
                    return Err(format!("{id} is not listed exactly once by its parent {p}"));
                }
                if !a.is_inclusive_ancestor(p, id) || a.is_inclusive_ancestor(id, p) {
                    return Err(format!("is_inclusive_ancestor wrong for {id} and {p}"));
                }
            }
            None => {
                if a.previous_sibling(id).is_some() {
                    return Err(format!("parentless {id} has a previous sibling"));
                }
            }
        }
        if !a.is_inclusive_ancestor(id, id) {
            return Err(format!("{id} is not its own inclusive ancestor"));
        }
        let mut cur = id;
        let mut steps = 0usize;
        while let Some(p) = a.parent(cur) {
            cur = p;
            steps = steps.saturating_add(1);
            if steps > n {
                return Err(format!("the parent chain of {id} cycles"));
            }
        }
        match kind {
            ExecKind::Element {
                template_contents: Some(f),
                ..
            } => {
                let f = *f;
                if f >= n {
                    return Err(format!("template contents {f} of {id} out of range"));
                }
                if !matches!(a.kind(f), ExecKind::DocumentFragment { host: Some(h) } if *h == id) {
                    return Err(format!(
                        "contents {f} of {id} is not a fragment hosted by it"
                    ));
                }
                if a.parent(f).is_some() {
                    return Err(format!("template contents {f} has a parent"));
                }
                let claims = (0..n)
                    .filter(|&e| {
                        matches!(
                            a.kind(e),
                            ExecKind::Element { template_contents: Some(g), .. } if *g == f
                        )
                    })
                    .count();
                if claims != 1 {
                    return Err(format!("contents {f} is claimed by {claims} elements"));
                }
            }
            ExecKind::DocumentFragment { host: Some(h) }
                if !matches!(
                    a.kind(*h),
                    ExecKind::Element { template_contents: Some(g), .. } if *g == id
                ) =>
            {
                return Err(format!("fragment {id} is not the contents of its host {h}"));
            }
            _ => {}
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Suite 1: read an expected tree into an arena.

/// The `| ` records of an expected tree: a physical line starting with
/// `| ` begins a record, any other line continues the previous one (text,
/// attribute values and comments may contain line feeds).
fn records(text: &str) -> Result<Vec<String>, String> {
    let mut out: Vec<String> = Vec::new();
    for l in text.split('\n') {
        if let Some(rest) = l.strip_prefix("| ") {
            out.push(rest.to_owned());
        } else if let Some(last) = out.last_mut() {
            last.push('\n');
            last.push_str(l);
        } else if !l.is_empty() {
            return Err(format!("line before the first record: {l:?}"));
        }
    }
    Ok(out)
}

/// An attribute line's name as the suite prints it: `xlink href`,
/// `xml lang`, `xmlns xlink`, or a plain name.
fn attr_of(name: &str, value: &str) -> ExecAttr {
    let (namespace, prefix, local) = match name.split_once(' ') {
        Some(("xlink", l)) => (Some(Namespace::XLink), Some(u32s("xlink")), l),
        Some(("xml", l)) => (Some(Namespace::Xml), Some(u32s("xml")), l),
        Some(("xmlns", l)) => (Some(Namespace::Xmlns), Some(u32s("xmlns")), l),
        _ => (None, None, name),
    };
    ExecAttr {
        namespace,
        prefix,
        local_name: u32s(local),
        value: u32s(value),
    }
}

/// The tree of `expected` in a new arena, built with the arena's own
/// operations; returns it with the node whose children are the tree (the
/// document, or for a fragment case a parentless `DocumentFragment`).
fn build(expected: &str, fragment: bool) -> Result<(Arena, usize), String> {
    let mut a = Arena::new(u32s("about:blank"));
    let root = if fragment {
        create(&mut a, ExecKind::DocumentFragment { host: None })?
    } else {
        0
    };
    // (depth of the children it takes, node)
    let mut stack: Vec<(usize, usize)> = vec![(0, root)];
    for rec in records(expected)? {
        let indent = rec.chars().take_while(|&c| c == ' ').count();
        if indent % 2 != 0 {
            return Err(format!("odd indentation in {rec:?}"));
        }
        let depth = indent / 2;
        let body = rec.get(indent..).unwrap_or_default();
        while stack.last().is_some_and(|&(l, _)| l > depth) {
            stack.pop();
        }
        let Some(&(level, parent)) = stack.last() else {
            return Err("empty stack".to_owned());
        };
        if level != depth {
            return Err(format!("indentation of {rec:?} fits no parent"));
        }
        // Elements, comments, doctypes and processing instructions end in `>`,
        // text starts with a quote, so an attribute is the rest (its name may
        // even start with `<`, as in `<img <="" FAIL>`).
        let is_attr = !body.starts_with('"') && body.ends_with('"') && body.contains("=\"");
        if is_attr {
            let (name, rest) = body.split_once("=\"").unwrap_or_default();
            let value = rest
                .strip_suffix('"')
                .ok_or("attribute without end quote")?;
            if !matches!(a.kind(parent), ExecKind::Element { .. }) {
                return Err(format!("attribute {name:?} outside an element"));
            }
            a.append_attribute(parent, attr_of(name, value));
            continue;
        }
        if body == "content" {
            let is_template = matches!(
                a.kind(parent),
                ExecKind::Element {
                    namespace: Some(Namespace::Html),
                    local_name,
                    template_contents: None,
                    ..
                } if *local_name == u32s("template")
            );
            if !is_template {
                return Err("content outside an HTML template".to_owned());
            }
            let f = a
                .create_template_contents(parent)
                .ok_or("the node limit is far away")?;
            stack.push((depth.saturating_add(1), f));
            continue;
        }
        let (kind, container) = if let Some(inner) = body
            .strip_prefix("<!DOCTYPE ")
            .and_then(|r| r.strip_suffix('>'))
        {
            let (name, public_id, system_id) = match inner.split_once(" \"") {
                Some((name, rest)) => {
                    let ids = rest
                        .strip_suffix('"')
                        .ok_or("doctype ids without end quote")?;
                    let (p, s) = ids.split_once("\" \"").ok_or("doctype ids malformed")?;
                    (name, p, s)
                }
                None => (inner, "", ""),
            };
            (
                ExecKind::DocumentType {
                    name: u32s(name),
                    public_id: u32s(public_id),
                    system_id: u32s(system_id),
                },
                false,
            )
        } else if let Some(data) = body
            .strip_prefix("<!-- ")
            .and_then(|r| r.strip_suffix(" -->"))
        {
            (ExecKind::Comment { data: u32s(data) }, false)
        } else if let Some(inner) = body.strip_prefix("<?").and_then(|r| r.strip_suffix("?>")) {
            let (target, data) = inner.split_once(' ').unwrap_or((inner, ""));
            (
                ExecKind::ProcessingInstruction {
                    target: u32s(target),
                    data: u32s(data),
                },
                false,
            )
        } else if let Some(tag) = body.strip_prefix('<').and_then(|r| r.strip_suffix('>')) {
            let (ns, name) = match tag.split_once(' ') {
                Some(("svg", n)) => (Namespace::Svg, n),
                Some(("math", n)) => (Namespace::MathMl, n),
                _ => (Namespace::Html, tag),
            };
            (
                ExecKind::Element {
                    namespace: Some(ns),
                    prefix: None,
                    local_name: u32s(name),
                    attributes: Vec::new(),
                    template_contents: None,
                    form_owner: None,
                },
                true,
            )
        } else if let Some(data) = body.strip_prefix('"').and_then(|r| r.strip_suffix('"')) {
            (ExecKind::Text { data: u32s(data) }, false)
        } else {
            return Err(format!("unrecognised line {body:?}"));
        };
        if !may_have_children(a.kind(parent)) {
            return Err(format!("{body:?} under a node that cannot have children"));
        }
        let id = create(&mut a, kind)?;
        a.append(parent, id);
        if container {
            stack.push((depth.saturating_add(1), id));
        }
    }
    Ok((a, root))
}

/// One case: build, check `wf`, print, compare.
fn round_trip(case: &Case) -> Result<(), String> {
    let (a, root) = build(case.document, case.fragment.is_some())?;
    check_wf(&a)?;
    let printed = dump::dump_children(&a, root);
    let printed = printed.strip_suffix('\n').unwrap_or(&printed);
    if printed == case.document {
        Ok(())
    } else {
        Err(format!(
            "--- expected\n{}\n--- printed\n{printed}",
            case.document
        ))
    }
}

#[test]
fn html5lib_tree_construction_trees() {
    let stride = if cfg!(miri) { 97 } else { 1 };
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut failed: Vec<String> = Vec::new();
    let mut known_hit: Vec<&str> = Vec::new();
    let mut stale: Vec<&str> = Vec::new();
    let mut fragments = 0usize;
    let mut scripted = 0usize;
    for case in CASES.iter().step_by(stride) {
        let id = format!("{}:{}", case.file, case.index);
        if case.fragment.is_some() {
            fragments = fragments.saturating_add(1);
        }
        if case.scripting.is_some() && !case.data.is_empty() {
            scripted = scripted.saturating_add(1);
        }
        let known = KNOWN_MISMATCHES.iter().find(|(k, _)| *k == id);
        match (round_trip(case), known) {
            (Ok(()), None) => pass = pass.saturating_add(1),
            (Ok(()), Some((k, _))) => {
                pass = pass.saturating_add(1);
                stale.push(k);
            }
            (Err(_), Some((k, _))) => {
                xfail = xfail.saturating_add(1);
                known_hit.push(k);
            }
            (Err(e), None) => failed.push(format!("{id} data={:?}\n{e}", case.data)),
        }
    }
    if !cfg!(miri) {
        println!(
            "dom trees: {fragments} fragment cases; {scripted} name a scripting flag (the tree is built once); \
             scripted_*.dat cases not trees to build (not in total): {SCRIPTED_NOT_RUN}"
        );
        for f in &failed {
            println!("MISMATCH {f}\n");
        }
        println!(
            "clazel-conformance: suite=\"html5lib tree-construction trees (WPT)\" pass={pass} xfail={xfail} fail={} total={}",
            failed.len(),
            CASES.len()
        );
    }
    assert!(
        stale.is_empty(),
        "listed as mismatches but now pass: {stale:?}"
    );
    assert!(
        failed.is_empty(),
        "{} trees do not round-trip",
        failed.len()
    );
    assert_eq!(
        pass.saturating_add(xfail),
        CASES.iter().step_by(stride).count()
    );
}

// ---------------------------------------------------------------------------
// Suite 2: differential against markup5ever_rcdom.

const HTML_NS: &str = "http://www.w3.org/1999/xhtml";
const SVG_NS: &str = "http://www.w3.org/2000/svg";
const MATHML_NS: &str = "http://www.w3.org/1998/Math/MathML";
const XLINK_NS: &str = "http://www.w3.org/1999/xlink";
const XML_NS: &str = "http://www.w3.org/XML/1998/namespace";
const XMLNS_NS: &str = "http://www.w3.org/2000/xmlns/";

/// `SplitMix64`.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform-enough in `0..n` (`0` for `n == 0`).
    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(u64::MAX);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> Option<&'a T> {
        items.get(self.below(items.len()))
    }
}

/// The arena and the `RcDom` that every operation is applied to; `h[i]` is
/// the `RcDom` node of arena id `i`.
struct Pair {
    a: Arena,
    dom: RcDom,
    h: Vec<Handle>,
}

#[derive(Default)]
struct Stats {
    created: usize,
    appended: usize,
    inserted_before: usize,
    moved: usize,
    moved_to_other_parent: usize,
    removed: usize,
    reparented: usize,
    data: usize,
    attrs: usize,
    modes: usize,
    templates: usize,
}

fn rc_str(s: &str) -> StrTendril {
    StrTendril::from_slice(s)
}

/// The text a random string takes: letters, quotes, newlines and non-ASCII.
fn random_text(rng: &mut Rng) -> String {
    const PIECES: &[&str] = &[
        "a",
        "b",
        "xy",
        " ",
        "\"",
        "\n",
        "é",
        "\u{1F600}",
        "<",
        "&",
        "-",
    ];
    let n = rng.below(4);
    let mut s = String::new();
    for _ in 0..=n {
        if let Some(p) = rng.pick(PIECES) {
            s.push_str(p);
        }
    }
    s
}

/// An attribute of the given kind: 0 plain, 1 `xlink href`, 2 `xml lang`,
/// 3 `xmlns xlink`.
fn attr_pair(kind: usize, plain: &str, value: &str) -> (ExecAttr, Attribute) {
    let (ns_a, ns_uri, prefix, local) = match kind {
        1 => (Some(Namespace::XLink), XLINK_NS, Some("xlink"), "href"),
        2 => (Some(Namespace::Xml), XML_NS, Some("xml"), "lang"),
        3 => (Some(Namespace::Xmlns), XMLNS_NS, Some("xmlns"), "xlink"),
        _ => (None, "", None, plain),
    };
    let ours = ExecAttr {
        namespace: ns_a,
        prefix: prefix.map(u32s),
        local_name: u32s(local),
        value: u32s(value),
    };
    let theirs = Attribute {
        name: QualName::new(
            prefix.map(Prefix::from),
            html5ever::Namespace::from(ns_uri),
            LocalName::from(local),
        ),
        value: rc_str(value),
    };
    (ours, theirs)
}

fn random_attr(rng: &mut Rng) -> (ExecAttr, Attribute) {
    const PLAIN: &[&str] = &["class", "id", "x", "href", "title"];
    let kind = rng.below(4);
    let plain = rng.pick(PLAIN).copied().unwrap_or("x");
    let value = random_text(rng);
    attr_pair(kind, plain, &value)
}

/// Create a random node in both trees (a `template` gets its contents,
/// which take the next id); returns its id. Every node carries its id.
fn create_random(p: &mut Pair, rng: &mut Rng, stats: &mut Stats) -> Result<usize, String> {
    const NAMES: &[&str] = &[
        "div",
        "p",
        "template",
        "a",
        "svg",
        "foreignObject",
        "mi",
        "b",
    ];
    let id = p.a.len();
    stats.created = stats.created.saturating_add(1);
    let (kind, handle) = match rng.below(10) {
        0..=4 => {
            let (ns, uri) = match rng.below(4) {
                0 => (Namespace::Svg, SVG_NS),
                1 => (Namespace::MathMl, MATHML_NS),
                _ => (Namespace::Html, HTML_NS),
            };
            let name = rng.pick(NAMES).copied().unwrap_or("div");
            let is_template = matches!(ns, Namespace::Html) && name == "template";
            let mut ours = vec![ExecAttr {
                namespace: None,
                prefix: None,
                local_name: u32s("u"),
                value: u32s(&id.to_string()),
            }];
            let mut theirs = vec![Attribute {
                name: QualName::new(None, html5ever::Namespace::from(""), LocalName::from("u")),
                value: rc_str(&id.to_string()),
            }];
            for _ in 0..rng.below(3) {
                let (o, t) = random_attr(rng);
                ours.push(o);
                theirs.push(t);
            }
            let mut flags = ElementFlags::default();
            flags.template = is_template;
            let el = p.dom.create_element(
                QualName::new(None, html5ever::Namespace::from(uri), LocalName::from(name)),
                theirs,
                flags,
            );
            (
                ExecKind::Element {
                    namespace: Some(ns),
                    prefix: None,
                    local_name: u32s(name),
                    attributes: ours,
                    template_contents: None,
                    form_owner: None,
                },
                el,
            )
        }
        5 | 6 => {
            let text = format!("{id}:{}", random_text(rng));
            (
                ExecKind::Text { data: u32s(&text) },
                Node::new(NodeData::Text {
                    contents: RefCell::new(rc_str(&text)),
                }),
            )
        }
        7 => {
            let text = format!("{id}:{}", random_text(rng));
            (
                ExecKind::Comment { data: u32s(&text) },
                p.dom.create_comment(rc_str(&text)),
            )
        }
        8 => {
            let name = format!("d{id}");
            let public_id = random_text(rng);
            (
                ExecKind::DocumentType {
                    name: u32s(&name),
                    public_id: u32s(&public_id),
                    system_id: Vec::new(),
                },
                Node::new(NodeData::Doctype {
                    name: rc_str(&name),
                    public_id: rc_str(&public_id),
                    system_id: rc_str(""),
                }),
            )
        }
        _ => {
            let target = format!("t{id}");
            let data = random_text(rng);
            (
                ExecKind::ProcessingInstruction {
                    target: u32s(&target),
                    data: u32s(&data),
                },
                p.dom.create_pi(rc_str(&target), rc_str(&data)),
            )
        }
    };
    let is_template_el = matches!(
        &kind,
        ExecKind::Element { namespace: Some(Namespace::Html), local_name, .. }
            if *local_name == u32s("template")
    );
    let got = create(&mut p.a, kind)?;
    if got != id {
        return Err(format!("created id {got}, expected {id}"));
    }
    p.h.push(handle.clone());
    if is_template_el {
        stats.templates = stats.templates.saturating_add(1);
        let f =
            p.a.create_template_contents(id)
                .ok_or("the node limit is far away")?;
        if f != p.a.len().saturating_sub(1) || f != p.h.len() {
            return Err(format!("template contents got id {f}"));
        }
        p.h.push(p.dom.get_template_contents(&handle));
    }
    Ok(id)
}

/// `node` is `x` or an ancestor of it, where a template's contents lead
/// back to the template (DOM's "host-including inclusive ancestor").
fn host_including(a: &Arena, node: usize, x: usize) -> bool {
    let mut cur = x;
    for _ in 0..a.len().saturating_mul(2).saturating_add(2) {
        if cur == node {
            return true;
        }
        if let Some(p) = a.parent(cur) {
            cur = p;
        } else if let ExecKind::DocumentFragment { host: Some(h) } = a.kind(cur) {
            cur = *h;
        } else {
            return false;
        }
    }
    true
}

fn ns_prefix(uri: &str) -> &'static str {
    match uri {
        SVG_NS => "svg ",
        MATHML_NS => "math ",
        _ => "",
    }
}

fn fmt_attrs(mut attrs: Vec<(String, String)>) -> Vec<String> {
    attrs.sort();
    attrs
        .into_iter()
        .map(|(k, v)| format!("{k}=\"{v}\""))
        .collect()
}

fn pad(out: &mut String, depth: usize, text: &str) {
    for _ in 0..depth {
        out.push_str("  ");
    }
    out.push_str(text);
    out.push('\n');
}

fn lossy(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// Every tree of the arena: the document, and every detached subtree
/// (a parentless node other than a template's contents), by arena walk.
fn dump_arena(a: &Arena) -> String {
    enum Item {
        Node(usize, usize),
        Content(usize, usize),
    }
    let mut out = String::new();
    if let ExecKind::Document { mode, .. } = a.kind(0) {
        let m = match mode {
            DocumentMode::NoQuirks => "no-quirks",
            DocumentMode::Quirks => "quirks",
            DocumentMode::LimitedQuirks => "limited-quirks",
        };
        pad(&mut out, 0, &format!("#mode {m}"));
    }
    for root in 0..a.len() {
        if a.parent(root).is_some() {
            continue;
        }
        if root != 0 && matches!(a.kind(root), ExecKind::DocumentFragment { .. }) {
            continue;
        }
        pad(&mut out, 0, &format!("#root {root}"));
        let mut stack: Vec<Item> = if root == 0 {
            a.children(0)
                .iter()
                .rev()
                .map(|&c| Item::Node(c, 1))
                .collect()
        } else {
            vec![Item::Node(root, 1)]
        };
        while let Some(item) = stack.pop() {
            match item {
                Item::Content(f, d) => {
                    pad(&mut out, d, "content");
                    for &c in a.children(f).iter().rev() {
                        stack.push(Item::Node(c, d.saturating_add(1)));
                    }
                }
                Item::Node(n, d) => match a.kind(n) {
                    ExecKind::DocumentType {
                        name,
                        public_id,
                        system_id,
                    } => pad(
                        &mut out,
                        d,
                        &format!(
                            "<!DOCTYPE {} \"{}\" \"{}\">",
                            lossy(name),
                            lossy(public_id),
                            lossy(system_id)
                        ),
                    ),
                    ExecKind::Element {
                        namespace,
                        local_name,
                        attributes,
                        template_contents,
                        ..
                    } => {
                        let uri = match namespace {
                            Some(Namespace::Svg) => SVG_NS,
                            Some(Namespace::MathMl) => MATHML_NS,
                            _ => HTML_NS,
                        };
                        pad(
                            &mut out,
                            d,
                            &format!("<{}{}>", ns_prefix(uri), lossy(local_name)),
                        );
                        let attrs = attributes
                            .iter()
                            .map(|at| {
                                let l = lossy(&at.local_name);
                                let name = match at.namespace {
                                    Some(Namespace::XLink) => format!("xlink {l}"),
                                    Some(Namespace::Xml) => format!("xml {l}"),
                                    Some(Namespace::Xmlns) => format!("xmlns {l}"),
                                    _ => l,
                                };
                                (name, lossy(&at.value))
                            })
                            .collect();
                        for line in fmt_attrs(attrs) {
                            pad(&mut out, d.saturating_add(1), &line);
                        }
                        for &c in a.children(n).iter().rev() {
                            stack.push(Item::Node(c, d.saturating_add(1)));
                        }
                        if let (Some(f), Some(Namespace::Html)) = (template_contents, namespace) {
                            stack.push(Item::Content(*f, d.saturating_add(1)));
                        }
                    }
                    ExecKind::Text { data } => pad(&mut out, d, &format!("\"{}\"", lossy(data))),
                    ExecKind::Comment { data } => {
                        pad(&mut out, d, &format!("<!-- {} -->", lossy(data)));
                    }
                    ExecKind::ProcessingInstruction { target, data } => {
                        pad(
                            &mut out,
                            d,
                            &format!("<?{} {}?>", lossy(target), lossy(data)),
                        );
                    }
                    ExecKind::Document { .. } | ExecKind::DocumentFragment { .. } => {
                        pad(&mut out, d, "#unexpected");
                    }
                },
            }
        }
    }
    out
}

/// The same printout from the `RcDom`, by `RcDom`'s own parent links (the
/// roots are the nodes whose own parent cell is empty).
fn dump_rc(p: &Pair) -> String {
    enum Item {
        Node(Handle, usize),
        Content(Handle, usize),
    }
    let mut out = String::new();
    let m = match p.dom.quirks_mode.get() {
        QuirksMode::NoQuirks => "no-quirks",
        QuirksMode::Quirks => "quirks",
        QuirksMode::LimitedQuirks => "limited-quirks",
    };
    pad(&mut out, 0, &format!("#mode {m}"));
    for (root, h) in p.h.iter().enumerate() {
        let parent = h.parent.take();
        let parentless = parent.is_none();
        h.parent.set(parent);
        if !parentless {
            continue;
        }
        if root != 0 && matches!(h.data, NodeData::Document) {
            continue;
        }
        pad(&mut out, 0, &format!("#root {root}"));
        let mut stack: Vec<Item> = if root == 0 {
            h.children
                .borrow()
                .iter()
                .rev()
                .map(|c| Item::Node(c.clone(), 1))
                .collect()
        } else {
            vec![Item::Node(h.clone(), 1)]
        };
        while let Some(item) = stack.pop() {
            match item {
                Item::Content(f, d) => {
                    pad(&mut out, d, "content");
                    for c in f.children.borrow().iter().rev() {
                        stack.push(Item::Node(c.clone(), d.saturating_add(1)));
                    }
                }
                Item::Node(n, d) => match &n.data {
                    NodeData::Doctype {
                        name,
                        public_id,
                        system_id,
                    } => pad(
                        &mut out,
                        d,
                        &format!(
                            "<!DOCTYPE {} \"{}\" \"{}\">",
                            &**name, &**public_id, &**system_id
                        ),
                    ),
                    NodeData::Element {
                        name,
                        attrs,
                        template_contents,
                        ..
                    } => {
                        pad(
                            &mut out,
                            d,
                            &format!("<{}{}>", ns_prefix(&name.ns), &*name.local),
                        );
                        let list = attrs
                            .borrow()
                            .iter()
                            .map(|at| {
                                let l: &str = &at.name.local;
                                let printed = match &*at.name.ns {
                                    XLINK_NS => format!("xlink {l}"),
                                    XML_NS => format!("xml {l}"),
                                    XMLNS_NS => format!("xmlns {l}"),
                                    _ => l.to_owned(),
                                };
                                (printed, String::from(&*at.value))
                            })
                            .collect();
                        for line in fmt_attrs(list) {
                            pad(&mut out, d.saturating_add(1), &line);
                        }
                        for c in n.children.borrow().iter().rev() {
                            stack.push(Item::Node(c.clone(), d.saturating_add(1)));
                        }
                        if &*name.ns == HTML_NS
                            && let Some(f) = template_contents.borrow().as_ref()
                        {
                            stack.push(Item::Content(f.clone(), d.saturating_add(1)));
                        }
                    }
                    NodeData::Text { contents } => {
                        pad(&mut out, d, &format!("\"{}\"", &**contents.borrow()));
                    }
                    NodeData::Comment { contents } => {
                        pad(&mut out, d, &format!("<!-- {} -->", &**contents));
                    }
                    NodeData::ProcessingInstruction { target, contents } => {
                        pad(&mut out, d, &format!("<?{} {}?>", &**target, &**contents));
                    }
                    NodeData::Document => pad(&mut out, d, "#unexpected"),
                },
            }
        }
    }
    out
}

/// One random operation on both trees. `Ok(())` also when the random
/// choice found nothing to do.
fn step(p: &mut Pair, rng: &mut Rng, stats: &mut Stats) -> Result<(), String> {
    let n = p.a.len();
    let containers: Vec<usize> = (0..n).filter(|&i| may_have_children(p.a.kind(i))).collect();
    let nodes: Vec<usize> = (0..n)
        .filter(|&i| {
            !matches!(
                p.a.kind(i),
                ExecKind::Document { .. } | ExecKind::DocumentFragment { .. }
            )
        })
        .collect();
    let roll = rng.below(100);
    match roll {
        0..=17 => {
            if n < 60 {
                let id = create_random(p, rng, stats)?;
                // Half the time, attach it right away.
                if rng.below(2) == 0
                    && let Some(&parent) = rng.pick(&containers)
                {
                    place(p, id, parent, None, stats)?;
                }
            }
        }
        18..=64 => {
            let (Some(&node), Some(&parent)) = (rng.pick(&nodes), rng.pick(&containers)) else {
                return Ok(());
            };
            let before = if roll >= 45 {
                let kids: Vec<usize> = p.a.children(parent).to_vec();
                rng.pick(&kids).copied()
            } else {
                None
            };
            place(p, node, parent, before, stats)?;
        }
        65..=76 => {
            let attached: Vec<usize> = nodes
                .iter()
                .copied()
                .filter(|&i| p.a.parent(i).is_some())
                .collect();
            if let Some(&node) = rng.pick(&attached) {
                stats.removed = stats.removed.saturating_add(1);
                p.a.remove(node);
                if let Some(h) = p.h.get(node) {
                    p.dom.remove_from_parent(h);
                }
            }
        }
        77..=84 => {
            let (Some(&from), Some(&to)) = (rng.pick(&containers), rng.pick(&containers)) else {
                return Ok(());
            };
            if from != to && !host_including(&p.a, from, to) {
                check_reader_agrees(&p.a, from, to)?;
                stats.reparented = stats.reparented.saturating_add(1);
                p.a.reparent_children(from, to);
                if let (Some(f), Some(t)) = (p.h.get(from), p.h.get(to)) {
                    p.dom.reparent_children(f, t);
                }
            }
        }
        85..=90 => {
            let texts: Vec<usize> = nodes
                .iter()
                .copied()
                .filter(|&i| matches!(p.a.kind(i), ExecKind::Text { .. }))
                .collect();
            if let Some(&t) = rng.pick(&texts) {
                let more = random_text(rng);
                stats.data = stats.data.saturating_add(1);
                p.a.append_data(t, &u32s(&more));
                if let Some(h) = p.h.get(t)
                    && let NodeData::Text { contents } = &h.data
                {
                    contents.borrow_mut().push_slice(&more);
                }
            }
        }
        91..=95 => {
            let els: Vec<usize> = nodes
                .iter()
                .copied()
                .filter(|&i| matches!(p.a.kind(i), ExecKind::Element { .. }))
                .collect();
            if let Some(&e) = rng.pick(&els) {
                let (ours, theirs) = random_attr(rng);
                stats.attrs = stats.attrs.saturating_add(1);
                p.a.append_attribute(e, ours);
                if let Some(h) = p.h.get(e)
                    && let NodeData::Element { attrs, .. } = &h.data
                {
                    attrs.borrow_mut().push(theirs);
                }
            }
        }
        _ => {
            let (mode, q) = match rng.below(3) {
                0 => (DocumentMode::Quirks, QuirksMode::Quirks),
                1 => (DocumentMode::LimitedQuirks, QuirksMode::LimitedQuirks),
                _ => (DocumentMode::NoQuirks, QuirksMode::NoQuirks),
            };
            stats.modes = stats.modes.saturating_add(1);
            p.a.set_mode(mode);
            p.dom.set_quirks_mode(q);
        }
    }
    Ok(())
}

/// The arena's `is_inclusive_ancestor` reader must never say "no" where
/// the host-including walk says "yes, a cycle" would be avoided: if the
/// test's walk found no cycle, the arena's reader must find none either.
fn check_reader_agrees(a: &Arena, node: usize, parent: usize) -> Result<(), String> {
    if a.is_inclusive_ancestor(node, parent) && !host_including(a, node, parent) {
        return Err(format!(
            "is_inclusive_ancestor({node}, {parent}) holds but the host-including walk says it does not"
        ));
    }
    Ok(())
}

/// Insert `node` into `parent` before `before` (append when `None`), in
/// both trees, if that is a call the arena's contract allows; this is also
/// how a subtree is moved.
fn place(
    p: &mut Pair,
    node: usize,
    parent: usize,
    before: Option<usize>,
    stats: &mut Stats,
) -> Result<(), String> {
    if host_including(&p.a, node, parent) || before == Some(node) {
        return Ok(());
    }
    check_reader_agrees(&p.a, node, parent)?;
    let old_parent = p.a.parent(node);
    if old_parent.is_some() {
        stats.moved = stats.moved.saturating_add(1);
        if old_parent != Some(parent) {
            stats.moved_to_other_parent = stats.moved_to_other_parent.saturating_add(1);
        }
    }
    let (Some(hn), Some(hp)) = (p.h.get(node).cloned(), p.h.get(parent).cloned()) else {
        return Err("no handle".to_owned());
    };
    // DOM "insert" step 7.1 "adopt": detach first (see the module doc).
    p.dom.remove_from_parent(&hn);
    match before {
        None => {
            stats.appended = stats.appended.saturating_add(1);
            p.a.append(parent, node);
            p.dom.append(&hp, NodeOrText::AppendNode(hn));
        }
        Some(c) => {
            stats.inserted_before = stats.inserted_before.saturating_add(1);
            let Some(hc) = p.h.get(c).cloned() else {
                return Err("no handle".to_owned());
            };
            p.a.insert_before(parent, node, c);
            p.dom.append_before_sibling(&hc, NodeOrText::AppendNode(hn));
        }
    }
    Ok(())
}

/// One sequence of operations; `Err` says where the engines or the
/// invariants disagree.
fn sequence(seed: u64, ops: usize, stats: &mut Stats) -> Result<(), String> {
    let mut rng = Rng(seed);
    let dom = RcDom::default();
    let h0 = dom.document.clone();
    let mut p = Pair {
        a: Arena::new(u32s("about:blank")),
        dom,
        h: vec![h0],
    };
    // A few nodes first, so the early operations have something to move.
    for _ in 0..6 {
        create_random(&mut p, &mut rng, stats)?;
    }
    for i in 0..ops {
        let len_before = p.a.len();
        step(&mut p, &mut rng, stats)?;
        if p.a.len() < len_before {
            return Err(format!("op {i}: the arena shrank (ids are stable)"));
        }
        if p.h.len() != p.a.len() {
            return Err(format!("op {i}: handles and ids diverged"));
        }
        check_wf(&p.a).map_err(|e| format!("op {i}: wf: {e}"))?;
        let (ours, theirs) = (dump_arena(&p.a), dump_rc(&p));
        if ours != theirs {
            return Err(format!(
                "op {i}: trees differ\n--- arena\n{ours}\n--- rcdom\n{theirs}"
            ));
        }
    }
    Ok(())
}

/// Sequences per run, and operations per sequence.
const SEQUENCES: usize = 3000;
const OPS: usize = 40;

#[test]
fn rcdom_differential() {
    let stride = if cfg!(miri) { 750 } else { 1 };
    let ops = if cfg!(miri) { 12 } else { OPS };
    let mut agreed = 0usize;
    let mut failures: Vec<String> = Vec::new();
    let mut stats = Stats::default();
    let mut ran = 0usize;
    for i in (0..SEQUENCES).step_by(stride) {
        ran = ran.saturating_add(1);
        let seed =
            0xC1A2_E100_0D0D_0000u64 ^ u64::try_from(i).unwrap_or(0).wrapping_mul(0x9E37_79B9);
        match sequence(seed, ops, &mut stats) {
            Ok(()) => agreed = agreed.saturating_add(1),
            Err(e) => failures.push(format!("sequence {i} (seed {seed:#x}): {e}")),
        }
    }
    if !cfg!(miri) {
        println!(
            "dom differential: {} nodes created, {} appends, {} insert-befores, {} subtree moves ({} to another parent), \
             {} removes, {} move-all-children, {} text appends, {} attributes, {} mode changes, {} templates",
            stats.created,
            stats.appended,
            stats.inserted_before,
            stats.moved,
            stats.moved_to_other_parent,
            stats.removed,
            stats.reparented,
            stats.data,
            stats.attrs,
            stats.modes,
            stats.templates
        );
        for f in failures.iter().take(3) {
            println!("DISAGREE {f}\n");
        }
        println!(
            "clazel-conformance: suite=\"markup5ever_rcdom 0.39.0 differential (random operation sequences)\" pass={agreed} xfail=0 fail={} total={SEQUENCES}",
            failures.len()
        );
        assert!(
            stats.moved > 0 && stats.moved_to_other_parent > 0 && stats.reparented > 0,
            "the generator must exercise moves"
        );
    }
    assert!(failures.is_empty(), "{} sequences disagree", failures.len());
    assert_eq!(agreed, ran);
}
