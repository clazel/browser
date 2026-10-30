//! The text layout (Phase 4 item 4.14): a parsed document
//! ([`clazel_dom::exec::Arena`]) to a [`Page`]: its title, its text as lines
//! of at most `width` columns, and the list of the links the text numbers.
//!
//! Tier 0 (tests only), the policy's tier for layout; Phase 5 replaces this
//! crate with CSS. Only which elements are hidden, which are blocks and
//! which keep their whitespace comes from a standard (HTML §15.3, the
//! user agent style sheet:
//! <https://html.spec.whatwg.org/multipage/rendering.html#the-css-user-agent-style-sheet-and-presentational-hints>);
//! every other rule is ours and is marked so where it is applied.
//!
//! # Links: the href choice
//!
//! Item 4.13 resolves `<a href>` and `<iframe src>` against the document
//! base URL, and a value that does not parse is not a link. The layout
//! takes that resolver as a parameter: [`layout_with`] calls
//! `resolve(value)` on each attribute value, in tree order, and an element
//! is a link (numbered and listed) only when it returns `Some(url)`; the
//! URL it returns is what `links` holds. [`layout`] is [`layout_with`] with
//! the resolver that accepts every value as it is (the raw attribute
//! value, as a string). The crate itself parses no URL.
//!
//! # Modelling choices and simplifications
//!
//! - **The input** is the arena the tree builder builds, read from node 0
//!   (the document). Only the reading methods of `Arena` are used. A node
//!   id that is not in the arena is skipped, and the walk visits at most
//!   `arena.len()` nodes, so even an arena that broke `wf` (which the DOM
//!   crate proves it never does) cannot make the layout loop or panic.
//! - **Names** are matched on HTML-namespace elements only, as the user
//!   agent style sheet's `@namespace "http://www.w3.org/1999/xhtml"` does
//!   (§15.3.1), with one addition (ours): `script` and `style` in any
//!   namespace are hidden (SVG's are never rendered either). Every other
//!   foreign (SVG, MathML) element is inline and its text is shown.
//! - **Scripting is off**: `noscript` is shown (§15.3.1 hides it only
//!   `@media (scripting)`).
//! - **`hidden`**: any element with a `hidden` attribute shows nothing.
//!   §15.3.1 makes `hidden=until-found` `content-visibility: hidden` and
//!   `embed[hidden]` a 0×0 box; neither shows any text, so the layout does
//!   not distinguish them (ours).
//! - **Blocks** become line breaks, nothing else: no margins, no
//!   indentation, no box widths (ours). The one vertical space is one empty
//!   line around `p` and `h1` to `h6` (ours), never at the top of the page
//!   nor after an empty line. Empty lines at the end of the page are
//!   dropped (ours); `br` and preformatted line feeds may still give
//!   several empty lines in a row.
//! - **Whitespace** in normal text: runs of ASCII whitespace (Infra: TAB,
//!   LF, FF, CR, SPACE) collapse to one space, dropped at line edges (the
//!   effect of CSS `white-space: normal`; ours, since CSS is Phase 5). In
//!   preformatted text every character is kept, LF ends the line, and TAB,
//!   FF and CR are one space each (ours: one column per scalar value).
//! - **Columns**: every scalar value is one column. East Asian width,
//!   combining marks and bidirectional text are Phase 5.
//! - **Unsafe characters** (ours): a code point that is not a Unicode scalar
//!   value (a surrogate), a C0 control other than the ASCII whitespace
//!   above, DEL, or a C1 control becomes U+FFFD in the text, the title and
//!   the raw link values, so the output can be printed to a terminal.
//! - **Width**: lines are wrapped at `width` columns on spaces; a word longer
//!   than `width` is broken every `width` columns; preformatted text is
//!   broken at `width` columns wherever it is. **`width == 0` means no
//!   wrapping**: each line is as long as its content (ours; useful when the
//!   output is piped).
//! - **`hr`** is a line of `min(width, 80)` hyphens, 80 when `width == 0`
//!   ([`HR_MAX`]; ours). The cap keeps the per-element constant of the bound
//!   independent of the width.
//! - **Lists**: an `li` starts with `* `, or with `N. ` when its nearest
//!   enclosing list (`ol`, `ul`, `menu`, `dir`) is an `ol`, `N` counting the
//!   `li`s of that `ol` from 1 (ours). The `start`, `value` and `reversed`
//!   attributes are not read. A block at the start of an `li` stays on the
//!   marker's line.
//! - **Tables**: `table`, `caption` and `tr` are blocks; within a row, each
//!   `td` or `th` after the first is preceded by two spaces (ours, as Lynx).
//!   Columns are not aligned.
//! - **Links**: an `a` with an `href` that resolves is followed by `[n]`,
//!   `n` its 1-based index in `links`; an `iframe` with a `src` that resolves
//!   is `[n]` and its children are not shown (ours, as Lynx; nested browsing
//!   contexts are Phase 5).
//! - **Images**: an `img` with a non-empty `alt` is `[alt]`, one without an
//!   `alt` is `[image]`, and one with `alt=""` (a decorative image, HTML
//!   §4.8.4.4) shows nothing (ours; images are Phase 6).
//! - **The title** is HTML's `document.title` (§3.1.3): the first `title`
//!   element in the HTML namespace in tree order, its `Text` children
//!   concatenated, with ASCII whitespace stripped and collapsed. Template
//!   contents are not children, so a `title` there is not the title.
//!
//! # The bound
//!
//! Let `T` be the number of code points in the data of every `Text` node of
//! the arena, `A` that in every `img`'s `alt` value, and `N` the number of
//! nodes (`arena.len()`). Then for every width:
//!
//! - **characters**: `title + Σ line ≤ T + A + PER_NODE_CHARS · N`
//!   ([`PER_NODE_CHARS`] = 80), counted in scalar values;
//! - **lines**: `lines.len() ≤ T + A + PER_NODE_LINES · N`
//!   ([`PER_NODE_LINES`] = 82);
//!
//! so the text joined with one line feed per line is at most
//! `2 · (T + A) + 162 · N` scalar values. The argument: a shown text
//! character gives at most one character (collapsing only removes), or, if
//! it is a preformatted LF, at most one line; wrapping adds lines but no
//! characters. The text of each node is shown at most once (the walk is a
//! tree walk, and the title's text is inside a hidden `title`). What an
//! element adds is at most 80 characters (an `hr`; otherwise a list marker
//! `N. ` or a link marker `[n]` of at most 22 with `n ≤ usize::MAX`,
//! `[image]`, the brackets around an `alt`, or a cell's two spaces), and
//! at most two empty lines (a `br`, or the empty line before and after a
//! `p` or heading). A non-empty line holds at least one character. The
//! tests check both inequalities on every golden input and on generated
//! documents (`tests/golden.rs`, `tests/bound.rs`). The link list has at
//! most one entry per element, each what the resolver returned (with
//! [`layout`]'s, the attribute value itself).

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;

/// The length of an `hr`'s line when the width is 0 (no wrapping), and its
/// cap otherwise (ours).
pub const HR_MAX: usize = 80;

/// The characters an element may add to the page beyond the document's
/// text and `alt` values (the bound's constant; see the crate docs).
pub const PER_NODE_CHARS: usize = 80;

/// The lines a node may add beyond one per character (the bound's constant
/// for lines; see the crate docs).
pub const PER_NODE_LINES: usize = 82;

/// The laid out document.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Page {
    /// HTML §3.1.3 `document.title`; empty if there is no `title`.
    pub title: String,
    /// The text, one string per line, none longer than the width (unless
    /// the width is 0); no line ends in a line feed.
    pub lines: Vec<String>,
    /// The links, in the order their `[n]` markers appear: `links[n - 1]`
    /// is link `n`.
    pub links: Vec<String>,
}

/// Lay `doc` out at `width` columns (0: no wrapping), recording each
/// `href` and `src` value as it is (see the crate docs).
pub fn layout(doc: &Arena, width: usize) -> Page {
    layout_with(doc, width, |v| Some(string_of(v)))
}

/// Lay `doc` out at `width` columns (0: no wrapping); an `a href` or
/// `iframe src` value `v` is a link exactly when `resolve(v)` is
/// `Some(url)`, and `url` is what [`Page::links`] lists for it. `resolve`
/// is called once per such attribute, in tree order.
pub fn layout_with<F>(doc: &Arena, width: usize, resolve: F) -> Page
where
    F: FnMut(&[u32]) -> Option<String>,
{
    let title = title_of(doc);
    let mut walk = Walk {
        doc,
        out: Writer::new(width),
        links: Vec::new(),
        resolve,
        pre: 0,
        lists: Vec::new(),
        rows: Vec::new(),
    };
    walk.run();
    Page {
        title,
        lines: walk.out.finish(),
        links: walk.links,
    }
}

// ---------------------------------------------------------------------
// Element classes (HTML §15.3)

/// HTML §15.3.1 "Hidden elements":
/// "area, base, basefont, datalist, head, link, meta, noembed, noframes,
/// param, rp, script, style, template, title { display: none; }".
/// `noscript` is not here: "@media (scripting) { noscript { display: none
/// !important; } }", and scripting is off.
const HIDDEN: &[&str] = &[
    "area", "base", "basefont", "datalist", "head", "link", "meta", "noembed", "noframes", "param",
    "rp", "script", "style", "template", "title",
];

/// The elements that render as blocks, each starting a new line:
/// - §15.3.2 "The page": "html, body { display: block; }";
/// - §15.3.3 "Flow content": "address, blockquote, center, dialog, div,
///   figure, figcaption, footer, form, header, hr, legend, listing, main, p,
///   plaintext, pre, search, xmp { display: block; }" (§15.3.11 "The hr
///   element" styles `hr` further but sets no `display`);
/// - §15.3.6 "Sections and headings": "article, aside, :heading, hgroup,
///   nav, section { display: block; }" (`:heading` is `h1` to `h6`);
/// - §15.3.7 "Lists": "dir, dd, dl, dt, menu, ol, ul { display: block; }"
///   and "li { display: list-item; }";
/// - §15.3.8 "Tables": "table { display: table; }", "caption { display:
///   table-caption; }", "tr { display: table-row; }": a table, its caption
///   and each row start a new line (ours, as Lynx; cells are inline).
const BLOCKS: &[&str] = &[
    "html",
    "body",
    "address",
    "blockquote",
    "center",
    "dialog",
    "div",
    "figure",
    "figcaption",
    "footer",
    "form",
    "header",
    "hr",
    "legend",
    "listing",
    "main",
    "p",
    "plaintext",
    "pre",
    "search",
    "xmp",
    "article",
    "aside",
    "h1",
    "h2",
    "h3",
    "h4",
    "h5",
    "h6",
    "hgroup",
    "nav",
    "section",
    "dir",
    "dd",
    "dl",
    "dt",
    "menu",
    "ol",
    "ul",
    "li",
    "table",
    "caption",
    "tr",
];

/// The blocks with one empty line before and after (ours).
const SPACED: &[&str] = &["p", "h1", "h2", "h3", "h4", "h5", "h6"];

/// Preformatted text: §15.3.3 "listing, plaintext, pre, xmp { white-space:
/// pre; }" and §15.3.10 "textarea { white-space: pre-wrap; }" (pre-wrap is
/// laid out as pre, broken at the width like all preformatted text; ours).
/// `white-space` is inherited, so their descendants are preformatted too.
const PREFORMATTED: &[&str] = &["listing", "plaintext", "pre", "xmp", "textarea"];

/// `name` (code points) equals the ASCII string `s`.
fn is(name: &[u32], s: &str) -> bool {
    name.len() == s.len() && name.iter().zip(s.bytes()).all(|(a, b)| *a == u32::from(b))
}

/// `name` is one of `set`.
fn one_of(name: &[u32], set: &[&str]) -> bool {
    set.iter().any(|s| is(name, s))
}

/// The value of the attribute `name` (no namespace), if present.
fn attr<'a>(attrs: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attrs
        .iter()
        .find(|a| a.namespace.is_none() && is(&a.local_name, name))
        .map(|a| a.value.as_slice())
}

/// `v` is ASCII case-insensitively `s` (lowercase).
fn is_ascii_ci(v: &[u32], s: &str) -> bool {
    v.len() == s.len()
        && v.iter().zip(s.bytes()).all(|(a, b)| {
            let lower = if (0x41..=0x5A).contains(a) {
                a.saturating_add(0x20)
            } else {
                *a
            };
            lower == u32::from(b)
        })
}

/// Infra "ASCII whitespace": U+0009 TAB, U+000A LF, U+000C FF, U+000D CR,
/// U+0020 SPACE.
fn is_ascii_whitespace(c: u32) -> bool {
    matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20)
}

/// A code point as a printable character (ours): non-scalar values and
/// controls other than ASCII whitespace become U+FFFD.
fn printable(c: u32) -> char {
    let control = (c < 0x20 && !is_ascii_whitespace(c)) || (0x7F..=0x9F).contains(&c);
    if control {
        return char::REPLACEMENT_CHARACTER;
    }
    char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER)
}

/// Code points to a string of printable characters; ASCII whitespace other
/// than SPACE becomes SPACE (a link value is one line).
fn string_of(v: &[u32]) -> String {
    v.iter()
        .map(|c| {
            if is_ascii_whitespace(*c) {
                ' '
            } else {
                printable(*c)
            }
        })
        .collect()
}

/// `n` in decimal.
fn decimal(n: usize) -> String {
    n.to_string()
}

// ---------------------------------------------------------------------
// The title

/// HTML §3.1.3 "document.title" getter, for an HTML document: "the title
/// element is the first title element in the document (in tree order), if
/// there is one"; step 2 "Otherwise, let value be the child text content of
/// the title element, or the empty string if the title element is null";
/// step 3 "Strip and collapse ASCII whitespace in value". (The SVG-root
/// case of step 1 is not modelled: the parser's documents have an `html`
/// root.) The walk is iterative and visits each node at most once.
fn title_of(doc: &Arena) -> String {
    let n = doc.len();
    let mut stack: Vec<usize> = vec![0];
    let mut budget = n;
    while let Some(id) = stack.pop() {
        if id >= n || budget == 0 {
            continue;
        }
        budget = budget.saturating_sub(1);
        if let ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            ..
        } = doc.kind(id)
            && is(local_name, "title")
        {
            return child_text(doc, id);
        }
        // Push the children last first, so the first is visited first.
        stack.extend(doc.children(id).iter().rev());
    }
    String::new()
}

/// DOM "child text content" of `id`, stripped and collapsed (Infra "strip
/// and collapse ASCII whitespace").
fn child_text(doc: &Arena, id: usize) -> String {
    let mut s = String::new();
    let mut space = false;
    for &c in doc.children(id) {
        if c >= doc.len() {
            continue;
        }
        if let ExecKind::Text { data } = doc.kind(c) {
            for &cp in data {
                if is_ascii_whitespace(cp) {
                    space = true;
                } else {
                    if space && !s.is_empty() {
                        s.push(' ');
                    }
                    space = false;
                    s.push(printable(cp));
                }
            }
        }
    }
    s
}

// ---------------------------------------------------------------------
// The walk

/// What to do when leaving an element.
#[derive(Default, Clone, Copy)]
struct Exit {
    /// It is a block: end the line.
    block: bool,
    /// It is a paragraph or heading: an empty line after it.
    spaced: bool,
    /// It is a link: append `[n]`.
    link: Option<usize>,
    /// It pushed a list on `lists`.
    list: bool,
    /// It pushed a row on `rows`.
    row: bool,
    /// It is preformatted: leave `pre`.
    pre: bool,
}

/// One element being walked: its id, the next child's index, and what its
/// end does.
struct Frame {
    id: usize,
    next: usize,
    exit: Exit,
}

struct Walk<'a, F> {
    doc: &'a Arena,
    out: Writer,
    links: Vec<String>,
    resolve: F,
    /// How many preformatted elements enclose the current node.
    pre: usize,
    /// The enclosing lists, innermost last: `Some(count)` for an `ol` (the
    /// `li`s numbered so far), `None` for the others.
    lists: Vec<Option<usize>>,
    /// The enclosing rows, innermost last: the cells seen so far.
    rows: Vec<usize>,
}

impl<F> Walk<'_, F>
where
    F: FnMut(&[u32]) -> Option<String>,
{
    /// The walk over the tree in order, with an explicit stack (no
    /// recursion, so a deep tree cannot overflow the call stack). Each node
    /// is entered at most once, and at most `doc.len()` nodes are entered.
    fn run(&mut self) {
        let doc = self.doc;
        let mut budget = doc.len();
        let mut stack: Vec<Frame> = Vec::new();
        if budget == 0 {
            return;
        }
        budget = budget.saturating_sub(1);
        stack.push(Frame {
            id: 0,
            next: 0,
            exit: Exit::default(),
        });
        while let Some(top) = stack.last_mut() {
            let child = doc.children(top.id).get(top.next).copied();
            top.next = top.next.saturating_add(1);
            match child {
                Some(c) => {
                    if c >= doc.len() || budget == 0 {
                        continue;
                    }
                    budget = budget.saturating_sub(1);
                    if let Some(exit) = self.enter(c) {
                        stack.push(Frame {
                            id: c,
                            next: 0,
                            exit,
                        });
                    }
                }
                None => {
                    let exit = top.exit;
                    stack.pop();
                    self.leave(exit);
                }
            }
        }
    }

    /// Lay out the start of node `id`; `Some(exit)` if its children are to
    /// be walked, with what its end does.
    fn enter(&mut self, id: usize) -> Option<Exit> {
        let doc = self.doc;
        match doc.kind(id) {
            ExecKind::Text { data } => {
                let pre = self.pre > 0;
                for &c in data {
                    self.out.text(c, pre);
                }
                None
            }
            ExecKind::Element {
                namespace,
                local_name,
                attributes,
                ..
            } => {
                let html = matches!(namespace, Some(Namespace::Html));
                self.element(html, local_name, attributes)
            }
            // Comments, doctypes and processing instructions are not
            // rendered; a document or fragment is never a child.
            _ => None,
        }
    }

    fn element(&mut self, html: bool, name: &[u32], attrs: &[ExecAttr]) -> Option<Exit> {
        // Ours: script and style are never rendered, in any namespace.
        if is(name, "script") || is(name, "style") {
            return None;
        }
        if !html {
            return Some(Exit::default());
        }
        // §15.3.1: the hidden elements, "[hidden]" (see the crate docs for
        // until-found and embed), "input[type=hidden i] { display: none
        // !important; }"; §15.3.3: "dialog:not([open]) { display: none; }".
        let hidden = one_of(name, HIDDEN)
            || attr(attrs, "hidden").is_some()
            || (is(name, "input") && attr(attrs, "type").is_some_and(|t| is_ascii_ci(t, "hidden")))
            || (is(name, "dialog") && attr(attrs, "open").is_none());
        if hidden {
            return None;
        }
        // Ours: an iframe is a link to its src, and its children (the
        // parser's raw text) are not shown.
        if is(name, "iframe") {
            if let Some(src) = attr(attrs, "src")
                && let Some(n) = self.link(src)
            {
                self.out.attach(&marker(n));
            }
            return None;
        }
        let mut exit = Exit::default();
        if one_of(name, BLOCKS) {
            self.out.block();
            exit.block = true;
            if one_of(name, SPACED) {
                self.out.want_blank = true;
                exit.spaced = true;
            }
        }
        if is(name, "br") {
            // §15.3.3 renders br as a forced line break.
            self.out.line_break();
        } else if is(name, "hr") {
            self.out.rule();
        } else if is(name, "li") {
            self.list_item();
        } else if is(name, "img") {
            self.image(attrs);
        } else if is(name, "ol") || is(name, "ul") || is(name, "menu") || is(name, "dir") {
            self.lists.push(if is(name, "ol") { Some(0) } else { None });
            exit.list = true;
        } else if is(name, "tr") {
            self.rows.push(0);
            exit.row = true;
        } else if is(name, "td") || is(name, "th") {
            self.cell();
        } else if is(name, "a")
            && let Some(href) = attr(attrs, "href")
        {
            exit.link = self.link(href);
        }
        if one_of(name, PREFORMATTED) {
            self.pre = self.pre.saturating_add(1);
            exit.pre = true;
        }
        Some(exit)
    }

    fn leave(&mut self, exit: Exit) {
        if let Some(n) = exit.link {
            self.out.attach(&marker(n));
        }
        if exit.pre {
            self.pre = self.pre.saturating_sub(1);
        }
        if exit.list {
            self.lists.pop();
        }
        if exit.row {
            self.rows.pop();
        }
        if exit.block {
            self.out.block();
        }
        if exit.spaced {
            self.out.want_blank = true;
        }
    }

    /// Resolve a link value; its 1-based number if it is a link.
    fn link(&mut self, value: &[u32]) -> Option<usize> {
        let url = (self.resolve)(value)?;
        self.links.push(url);
        Some(self.links.len())
    }

    /// Ours: `* `, or `N. ` in an `ol`.
    fn list_item(&mut self) {
        let mark = match self.lists.last_mut() {
            Some(Some(count)) => {
                *count = count.saturating_add(1);
                let mut m = decimal(*count);
                m.push('.');
                m
            }
            _ => String::from("*"),
        };
        self.out.marker(&mark);
    }

    /// Ours: `[alt]`, `[image]`, or nothing for `alt=""`.
    fn image(&mut self, attrs: &[ExecAttr]) {
        let pre = self.pre > 0;
        match attr(attrs, "alt") {
            Some([]) => {}
            Some(alt) => {
                self.out.text(u32::from('['), pre);
                for &c in alt {
                    self.out.text(c, pre);
                }
                self.out.text(u32::from(']'), pre);
            }
            None => {
                for c in "[image]".chars() {
                    self.out.text(u32::from(c), pre);
                }
            }
        }
    }

    /// Ours: two spaces before each cell of a row but the first.
    fn cell(&mut self) {
        if let Some(count) = self.rows.last_mut() {
            if *count > 0 {
                self.out.separator();
            }
            *count = count.saturating_add(1);
        }
    }
}

/// A link marker, `[n]` (ours, as Lynx).
fn marker(n: usize) -> String {
    let mut s = String::from("[");
    s.push_str(&decimal(n));
    s.push(']');
    s
}

// ---------------------------------------------------------------------
// The line writer

/// Builds the lines: words are collected and placed on the current line
/// when they end, wrapping at `width` (0: never).
struct Writer {
    width: usize,
    lines: Vec<String>,
    /// The current line and its length in scalar values.
    line: String,
    line_len: usize,
    /// The word being collected (normal text) and its length.
    word: String,
    word_len: usize,
    /// A collapsible space is pending before the next content.
    space: bool,
    /// An empty line is wanted before the next content (ours).
    want_blank: bool,
    /// The current line holds only a list marker.
    marker_only: bool,
}

impl Writer {
    fn new(width: usize) -> Self {
        Writer {
            width,
            lines: Vec::new(),
            line: String::new(),
            line_len: 0,
            word: String::new(),
            word_len: 0,
            space: false,
            want_blank: false,
            marker_only: false,
        }
    }

    /// `n` columns fit on a line.
    fn fits(&self, n: usize) -> bool {
        self.width == 0 || n <= self.width
    }

    /// One code point of text, normal or preformatted.
    fn text(&mut self, c: u32, pre: bool) {
        if !pre {
            if is_ascii_whitespace(c) {
                self.end_word();
                self.space = true;
            } else {
                self.word.push(printable(c));
                self.word_len = self.word_len.saturating_add(1);
            }
            return;
        }
        self.end_word();
        self.before_content();
        if c == 0x0A {
            self.space = false;
            self.emit();
            return;
        }
        if self.space && self.line_len > 0 {
            self.put_hard(' ');
        }
        self.space = false;
        let ch = if is_ascii_whitespace(c) {
            ' '
        } else {
            printable(c)
        };
        self.put_hard(ch);
        self.marker_only = false;
    }

    /// Put one character on the line, breaking the line first if it is
    /// full.
    fn put_hard(&mut self, ch: char) {
        if !self.fits(self.line_len.saturating_add(1)) && self.line_len > 0 {
            self.emit();
        }
        self.line.push(ch);
        self.line_len = self.line_len.saturating_add(1);
    }

    /// Append `s` to the word being collected (no break before it).
    fn attach(&mut self, s: &str) {
        for ch in s.chars() {
            self.word.push(ch);
            self.word_len = self.word_len.saturating_add(1);
        }
    }

    /// The empty line before content, if one is wanted (ours).
    fn before_content(&mut self) {
        if self.want_blank && self.line_len == 0 && self.lines.last().is_some_and(|l| !l.is_empty())
        {
            self.lines.push(String::new());
        }
        self.want_blank = false;
    }

    /// Place the collected word on the line: after a space if one is
    /// pending and the line is not empty; on a new line if it does not fit;
    /// broken every `width` columns if it is longer than the width.
    fn end_word(&mut self) {
        if self.word_len == 0 {
            return;
        }
        self.before_content();
        let gap = usize::from(self.space && self.line_len > 0);
        let need = self
            .line_len
            .saturating_add(gap)
            .saturating_add(self.word_len);
        if self.line_len > 0 && !self.fits(need) {
            self.emit();
        } else if gap == 1 {
            self.line.push(' ');
            self.line_len = self.line_len.saturating_add(1);
        }
        self.space = false;
        let word = std::mem::take(&mut self.word);
        self.word_len = 0;
        for ch in word.chars() {
            self.put_hard(ch);
        }
        self.marker_only = false;
    }

    /// End the current line.
    fn emit(&mut self) {
        self.lines.push(std::mem::take(&mut self.line));
        self.line_len = 0;
        self.space = false;
        self.marker_only = false;
    }

    /// A block starts or ends: a new line, unless the line is empty or holds
    /// only a list marker.
    fn block(&mut self) {
        self.end_word();
        if self.marker_only {
            return;
        }
        if self.line_len > 0 {
            self.emit();
        }
        self.space = false;
    }

    /// `br`: end the line, even if empty.
    fn line_break(&mut self) {
        self.end_word();
        self.before_content();
        self.emit();
    }

    /// `hr` (ours): a line of `min(width, HR_MAX)` hyphens, `HR_MAX` if the
    /// width is 0, on a line of its own (after `block`, the line is empty
    /// unless it holds a list marker).
    fn rule(&mut self) {
        if self.line_len > 0 {
            self.emit();
        }
        self.before_content();
        let n = if self.width == 0 {
            HR_MAX
        } else {
            self.width.min(HR_MAX)
        };
        for _ in 0..n {
            self.line.push('-');
        }
        self.line_len = n;
        self.emit();
    }

    /// A list marker (ours): the word `mark`, then a space; a block right
    /// after it stays on its line.
    fn marker(&mut self, mark: &str) {
        self.end_word();
        self.attach(mark);
        self.end_word();
        self.space = true;
        self.marker_only = true;
    }

    /// Two spaces between table cells (ours), unless at the start of a line.
    fn separator(&mut self) {
        self.end_word();
        self.space = false;
        if self.line_len == 0 {
            return;
        }
        if !self.fits(self.line_len.saturating_add(2)) {
            self.emit();
            return;
        }
        self.line.push_str("  ");
        self.line_len = self.line_len.saturating_add(2);
    }

    /// The lines, without trailing empty ones.
    fn finish(mut self) -> Vec<String> {
        self.end_word();
        if self.line_len > 0 {
            self.emit();
        }
        while self.lines.last().is_some_and(String::is_empty) {
            self.lines.pop();
        }
        self.lines
    }
}

#[cfg(test)]
mod tests;
