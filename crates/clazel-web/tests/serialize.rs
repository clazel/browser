//! The HTML serialization algorithm (HTML §13.3†) on trees built by hand:
//! each test names the step it covers.

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_web::serialize::{serialize_fragment, serialize_outer};

fn u(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn text(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn attr(ns: Option<Namespace>, prefix: Option<&str>, local: &str, value: &str) -> ExecAttr {
    ExecAttr {
        namespace: ns,
        prefix: prefix.map(u),
        local_name: u(local),
        value: u(value),
    }
}

/// A tree under construction.
struct Tree {
    arena: Arena,
}

impl Tree {
    fn new() -> Tree {
        Tree {
            arena: Arena::new(Vec::new()),
        }
    }

    fn make(&mut self, kind: ExecKind) -> usize {
        match self.arena.create(kind) {
            Some(n) => n,
            None => unreachable!("node limit"),
        }
    }

    fn element_in(
        &mut self,
        ns: Option<Namespace>,
        prefix: Option<&str>,
        name: &str,
        attrs: Vec<ExecAttr>,
    ) -> usize {
        self.make(ExecKind::Element {
            namespace: ns,
            prefix: prefix.map(u),
            local_name: u(name),
            attributes: attrs,
            template_contents: None,
            form_owner: None,
        })
    }

    fn html(&mut self, name: &str) -> usize {
        self.element_in(Some(Namespace::Html), None, name, Vec::new())
    }

    fn html_attrs(&mut self, name: &str, attrs: Vec<ExecAttr>) -> usize {
        self.element_in(Some(Namespace::Html), None, name, attrs)
    }

    fn text(&mut self, data: &str) -> usize {
        self.make(ExecKind::Text { data: u(data) })
    }

    fn contents(&mut self, template: usize) -> usize {
        match self.arena.create_template_contents(template) {
            Some(n) => n,
            None => unreachable!("node limit"),
        }
    }

    fn add(&mut self, parent: usize, child: usize) {
        self.arena.append(parent, child);
    }

    fn with_text(&mut self, name: &str, data: &str) -> usize {
        let e = self.html(name);
        let t = self.text(data);
        self.add(e, t);
        e
    }

    fn inner(&self, n: usize, scripting: bool) -> String {
        text(&serialize_fragment(&self.arena, n, scripting))
    }

    fn outer(&self, n: usize, scripting: bool) -> String {
        text(&serialize_outer(&self.arena, n, scripting))
    }
}

/// Step 3.2, Text: "escaped as described below": `&`, U+00A0, `<` and `>`;
/// `"` is left alone outside attribute mode.
#[test]
fn text_is_escaped() {
    let mut t = Tree::new();
    let div = t.with_text("div", "a&b\u{a0}<c>\"d\"");
    assert_eq!(t.inner(div, false), "a&amp;b&nbsp;&lt;c&gt;\"d\"");
}

/// Step 3.2, Element: attribute values are escaped in attribute mode, which
/// also replaces `"`; the tag name and attribute order are kept.
#[test]
fn attributes_are_escaped_and_quoted() {
    let mut t = Tree::new();
    let a = t.html_attrs(
        "a",
        vec![
            attr(None, None, "href", "x?a=1&b=\"2\"\u{a0}<>"),
            attr(None, None, "data-empty", ""),
        ],
    );
    assert_eq!(
        t.outer(a, false),
        "<a href=\"x?a=1&amp;b=&quot;2&quot;&nbsp;&lt;&gt;\" data-empty=\"\"></a>"
    );
}

/// Step 3.2, Element, "serializes as void": no children and no end tag, the
/// listed legacy names included; a non-void element gets both.
#[test]
fn void_elements() {
    for name in [
        "area", "base", "basefont", "bgsound", "br", "col", "embed", "frame", "hr", "img", "input",
        "keygen", "link", "meta", "param", "source", "track", "wbr",
    ] {
        let mut t = Tree::new();
        let e = t.html(name);
        assert_eq!(t.outer(e, false), format!("<{name}>"), "{name}");
    }
    let mut t = Tree::new();
    let e = t.html("span");
    assert_eq!(t.outer(e, false), "<span></span>");
    // A void name in another namespace is not void.
    let m = t.element_in(Some(Namespace::Svg), None, "link", Vec::new());
    assert_eq!(t.outer(m, false), "<link></link>");
}

/// Step 3.2, Element, children: recursion in tree order.
#[test]
fn nesting_and_order() {
    let mut t = Tree::new();
    let ul = t.html("ul");
    for i in 0..3 {
        let li = t.with_text("li", &format!("item {i}"));
        t.add(ul, li);
    }
    let p = t.html("p");
    let b = t.with_text("b", "bold");
    let after = t.text(" after");
    t.add(p, b);
    t.add(p, after);
    t.add(ul, p);
    assert_eq!(
        t.inner(ul, false),
        "<li>item 0</li><li>item 1</li><li>item 2</li><p><b>bold</b> after</p>"
    );
    assert_eq!(
        t.outer(ul, false).len(),
        t.inner(ul, false).len().saturating_add(9)
    );
}

/// Step 3.2, Text, "parent … style, script, xmp, iframe, noembed, noframes,
/// or plaintext": the data is appended literally.
#[test]
fn raw_text_parents() {
    for name in [
        "style",
        "script",
        "xmp",
        "iframe",
        "noembed",
        "noframes",
        "plaintext",
    ] {
        let mut t = Tree::new();
        let e = t.with_text(name, "a<b>&amp;\u{a0}");
        assert_eq!(t.inner(e, false), "a<b>&amp;\u{a0}", "{name}");
        // The same text under a `p` is escaped.
        let p = t.with_text("p", "a<b>");
        assert_eq!(t.inner(p, false), "a&lt;b&gt;");
    }
}

/// Step 3.2, Text: "a noscript element and scripting is enabled for the
/// node" is raw; with scripting off it is escaped.
#[test]
fn noscript_follows_the_scripting_flag() {
    let mut t = Tree::new();
    let e = t.with_text("noscript", "<p>x</p>");
    assert_eq!(t.inner(e, true), "<p>x</p>");
    assert_eq!(t.inner(e, false), "&lt;p&gt;x&lt;/p&gt;");
}

/// The raw-text rule is about the parent's namespace: an SVG `style` is not
/// an HTML one.
#[test]
fn raw_text_needs_the_html_namespace() {
    let mut t = Tree::new();
    let e = t.element_in(Some(Namespace::Svg), None, "style", Vec::new());
    let x = t.text("a<b");
    t.add(e, x);
    assert_eq!(t.inner(e, false), "a&lt;b");
}

/// Step 3.2, Comment, ProcessingInstruction and DocumentType.
#[test]
fn comments_instructions_and_doctypes() {
    let mut t = Tree::new();
    let div = t.html("div");
    let c = t.make(ExecKind::Comment { data: u(" hi -- ") });
    let pi = t.make(ExecKind::ProcessingInstruction {
        target: u("php"),
        data: u("echo 1;"),
    });
    t.add(div, c);
    t.add(div, pi);
    assert_eq!(t.inner(div, false), "<!-- hi -- --><?php echo 1;>");
    let dt = t.make(ExecKind::DocumentType {
        name: u("html"),
        public_id: u("-//W3C//DTD HTML 4.01//EN"),
        system_id: u("http://example.com/x.dtd"),
    });
    // Only the name is serialized.
    assert_eq!(t.outer(dt, false), "<!DOCTYPE html>");
}

/// Step 3.2, Element, "an attribute's serialized name".
#[test]
fn attribute_names_by_namespace() {
    let mut t = Tree::new();
    let e = t.element_in(
        Some(Namespace::Svg),
        None,
        "use",
        vec![
            attr(Some(Namespace::XLink), Some("xlink"), "href", "#a"),
            attr(Some(Namespace::Xml), Some("xml"), "lang", "en"),
            attr(Some(Namespace::Xmlns), None, "xmlns", "u"),
            attr(Some(Namespace::Xmlns), Some("xmlns"), "xlink", "v"),
            attr(Some(Namespace::MathMl), Some("m"), "other", "o"),
            attr(Some(Namespace::MathMl), None, "bare", "p"),
        ],
    );
    assert_eq!(
        t.outer(e, false),
        "<use xlink:href=\"#a\" xml:lang=\"en\" xmlns=\"u\" xmlns:xlink=\"v\" m:other=\"o\" bare=\"p\"></use>"
    );
}

/// Step 3.2, Element: an element in the HTML, MathML or SVG namespace is
/// written with its local name, any other with its qualified name.
#[test]
fn tag_names_by_namespace() {
    let mut t = Tree::new();
    let svg = t.element_in(Some(Namespace::Svg), Some("s"), "g", Vec::new());
    assert_eq!(t.outer(svg, false), "<g></g>");
    let math = t.element_in(Some(Namespace::MathMl), None, "mi", Vec::new());
    assert_eq!(t.outer(math, false), "<mi></mi>");
    let other = t.element_in(Some(Namespace::XLink), Some("x"), "item", Vec::new());
    assert_eq!(t.outer(other, false), "<x:item></x:item>");
    let none = t.element_in(None, None, "plain", Vec::new());
    assert_eq!(t.outer(none, false), "<plain></plain>");
}

/// Step 2: "If the node is a template element, then let the node instead be
/// the template element's template contents": the content is serialized,
/// and `outerHTML` shows it between the tags.
#[test]
fn template_contents() {
    let mut t = Tree::new();
    let tpl = t.html("template");
    let frag = t.contents(tpl);
    let b = t.with_text("b", "in");
    t.add(frag, b);
    // A real child of the template is not part of its contents.
    let stray = t.with_text("i", "stray");
    t.add(tpl, stray);
    assert_eq!(t.inner(tpl, false), "<b>in</b>");
    assert_eq!(t.outer(tpl, false), "<template><b>in</b></template>");
    // Template contents are a fragment, not a raw text parent.
    let tpl2 = t.html("template");
    let frag2 = t.contents(tpl2);
    let x = t.text("a<b");
    t.add(frag2, x);
    assert_eq!(t.inner(tpl2, false), "a&lt;b");
}

/// The leading line feed of `pre`, `textarea` and `listing` (see the module
/// comment of `serialize.rs`).
#[test]
fn leading_newline() {
    for name in ["pre", "textarea", "listing"] {
        let mut t = Tree::new();
        let e = t.with_text(name, "\nfoo");
        assert_eq!(t.outer(e, false), format!("<{name}>\n\nfoo</{name}>"));
        let plain = t.with_text(name, "foo\n");
        assert_eq!(t.outer(plain, false), format!("<{name}>foo\n</{name}>"));
        let empty = t.html(name);
        assert_eq!(t.outer(empty, false), format!("<{name}></{name}>"));
        // Not for other elements.
        let other = t.with_text("div", "\nfoo");
        assert_eq!(t.outer(other, false), "<div>\nfoo</div>");
    }
}

/// `serialize_fragment` on a document or fragment node has no tags of its
/// own, and a node id outside the arena is the empty string.
#[test]
fn containers_and_bad_ids() {
    let mut t = Tree::new();
    let d = t.html("div");
    t.add(0, d);
    let ht = t.make(ExecKind::DocumentType {
        name: u("html"),
        public_id: Vec::new(),
        system_id: Vec::new(),
    });
    t.add(0, ht);
    assert_eq!(t.inner(0, false), "<div></div><!DOCTYPE html>");
    assert_eq!(t.inner(9999, false), "");
    assert_eq!(t.outer(9999, false), "");
}

/// A tree 100,000 deep does not overflow the stack (the walk is iterative).
#[test]
fn deep_trees() {
    let mut t = Tree::new();
    let depth: usize = if cfg!(miri) { 500 } else { 100_000 };
    let root = t.html("div");
    let mut parent = root;
    for _ in 0..depth {
        let c = t.html("b");
        t.add(parent, c);
        parent = c;
    }
    let s = t.inner(root, false);
    assert_eq!(s.len(), depth.saturating_mul(7));
}
