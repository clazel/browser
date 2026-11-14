//! Style sources (phase-5.md item 5.8): what style sheets a document has, in order, which of
//! them apply, and each element's `style` attribute.
//!
//! The standards, read on 2026-11-11 at these versions:
//!
//! - HTML, Living Standard last updated 11 November 2026,
//!   <https://html.spec.whatwg.org/multipage/>: §4.2.6 the `style` element and its "update a
//!   style block" algorithm; §4.2.4 the `link` element, §4.2.4.1 its `media` attribute,
//!   §4.2.4.2 its `type` attribute and §4.2.4.3 "fetch and process the linked resource";
//!   §4.6.8.23 the link type "stylesheet", with its quirk and its "process this type of
//!   linked resource" steps; §2.3.10 "matches the environment"; §3.2.6.5 the `style`
//!   attribute.
//! - CSSOM, Editor's Draft of 13 October 2026, <https://drafts.csswg.org/cssom/>: §6.2 "add
//!   a CSS style sheet" (which sheets a title disables) and the document's list of CSS style
//!   sheets "in tree order".
//! - CSS Style Attributes, Editor's Draft of 15 October 2026,
//!   <https://drafts.csswg.org/css-style-attr/>: §3 and §4.
//! - Media Queries Level 4 ([`media`]).
//!
//! [`collect`] reads a document's arena once, in tree order, and gives its [`Sources`]: each
//! `<style>` element's sheet, parsed; each `<link rel=stylesheet>` to be fetched, with what
//! its processing needs; and each element's `style` attribute, parsed. The fetches are 5.19's
//! and the renderer's use of all this (render-blocking, re-evaluating `media` on a new
//! viewport, the cascade's input) is 5.20's: here a fetched sheet comes in as bytes with its
//! response's facts ([`Sources::link_loaded`]), and [`Sources::rules_for`] gives the style
//! rules that apply on a [`Device`], in the cascade's order of appearance.
//!
//! # Modelling choices
//!
//! - **One static pass.** HTML runs "update a style block" when a `style` element is popped
//!   off the stack of open elements, and fetches a link when it becomes connected; this
//!   reads the finished tree, so each `style` and `link` element in the document tree is
//!   seen once, in tree order. Elements inside a `template`'s contents are not in the tree
//!   (`clazel-dom` keeps them in a separate fragment) and are not read.
//! - **Content Security Policy** is not implemented: step 5 of "update a style block" never
//!   blocks.
//! - **Titles and alternate sheets** follow CSSOM's "add a CSS style sheet" with each sheet
//!   added in tree order (the order a parser adds `style` sheets; a link's sheet is added
//!   when it loads, and 5.20 waits for every link before the first render). No style sheet
//!   set is ever selected, so the "last CSS style sheet set name" stays null.
//! - **Which links are fetched**: rel's tokens include `stylesheet` (ASCII
//!   case-insensitively), `href` is present and not empty, `disabled` is absent (the
//!   "linked resource fetch setup steps" return false otherwise), and `type`, if present,
//!   is a MIME type whose essence is `text/css` (§4.2.4.2: a UA "should not fetch" a type
//!   it does not support). `crossorigin`, `integrity`, `referrerpolicy` and the rest of the
//!   request are 5.19's. Whether a link whose `media` does not match is fetched at all is
//!   the renderer's choice (HTML allows fetching only "when ... needed", §4.2.4.3).
//! - **Same origin** is a fact the caller gives with the response ([`Response`]), since the
//!   origins are the kernel's and the renderer's to compare.
//! - Only HTML's `style` and `link` elements are read; SVG's `style` element is not.

pub mod media;
pub mod sheet;
pub mod tokens;

#[cfg(kani)]
mod proofs;

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::{DocumentMode, Namespace};
use clazel_encoding::labels::exec::get_an_encoding;
use clazel_encoding::labels::spec::Encoding;
use clazel_mime::mime_type::parse::parse_from_bytes;
use clazel_mime::mime_type::record::MimeType;

pub use media::{Device, Medium};
use media::{MediaQueryList, evaluate};
pub use sheet::{Declaration, StyleRule, StyleSheet};

use crate::values::items::eq_ignore_case;

/// What owns a style sheet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Owner {
    /// A `style` element.
    Style,
    /// A `link` element with the `stylesheet` keyword.
    Link(Link),
}

/// Where a link's sheet is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkState {
    /// Not fetched yet.
    Pending,
    /// Fetched and processed: the sheet is in [`SheetSource::sheet`].
    Loaded,
    /// Fetched, but `success` was false: no sheet.
    Failed,
}

/// What a `link` element's sheet needs to be fetched and processed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Link {
    /// The `href` attribute's value, not yet resolved (the request is 5.19's).
    pub href: Vec<u32>,
    /// The `charset` attribute's value, if any: the first choice of the CSS environment
    /// encoding (§4.6.8.23).
    pub charset: Option<Vec<u32>>,
    /// True if rel's tokens also include `alternate`: "the link is an alternative style
    /// sheet", whose CSS style sheet has its alternate flag set (§4.6.8.23).
    pub alternate: bool,
    /// Where its sheet is.
    pub state: LinkState,
}

/// One of the document's CSS style sheets (CSSOM §6.2), in tree order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SheetSource {
    /// The owner node, an id in the arena.
    pub node: usize,
    /// What owns it.
    pub owner: Owner,
    /// Its `media` attribute, parsed; absent is the empty list, "all" (§4.2.6, §4.2.4.1).
    pub media: MediaQueryList,
    /// Its `title` attribute, or the empty string.
    pub title: Vec<u32>,
    /// CSSOM's disabled flag, as "add a CSS style sheet" leaves it.
    pub disabled: bool,
    /// The sheet: a `style` element's always, a link's once loaded.
    pub sheet: Option<StyleSheet>,
}

/// One element's `style` attribute (CSS Style Attributes §4: its declarations "apply to the
/// element to which the attribute belongs", with author origin and "a specificity higher
/// than any selector").
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AttributeStyle {
    /// The element, an id in the arena.
    pub node: usize,
    /// Its declarations, in order.
    pub declarations: Vec<Declaration>,
}

/// A document's style sources.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Sources {
    /// The document or shadow root CSS style sheets, in tree order (CSSOM §6.2).
    pub sheets: Vec<SheetSource>,
    /// The `style` attributes, in tree order.
    pub attributes: Vec<AttributeStyle>,
    /// True if the document is in quirks mode (DOM §4.5), which the stylesheet link quirk
    /// and the property values read.
    pub quirks: bool,
}

/// A link's response, as the kernel delivers it (5.19).
#[derive(Debug, Clone, Copy)]
pub struct Response<'a> {
    /// The `Content-Type` header's value, if any.
    pub content_type: Option<&'a [u8]>,
    /// True if the response's URL has the document's origin.
    pub same_origin: bool,
    /// HTML §4.2.4.3's `success`: the body was read and the status was an ok status.
    pub ok: bool,
    /// The body.
    pub body: &'a [u8],
}

fn is(s: &[u32], target: &str) -> bool {
    s.iter().copied().eq(target.chars().map(u32::from))
}

/// The value of the attribute `name` (no namespace) of an element, the first if repeated.
fn attribute<'a>(attributes: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attributes
        .iter()
        .find(|a| a.namespace.is_none() && is(&a.local_name, name))
        .map(|a| a.value.as_slice())
}

/// ASCII whitespace (Infra §4.6†): TAB, LF, FF, CR, SPACE.
fn is_ascii_whitespace(c: u32) -> bool {
    matches!(c, 0x09 | 0x0A | 0x0C | 0x0D | 0x20)
}

/// True if the set of space-separated tokens `value` (HTML §2.3.8†, "split on ASCII
/// whitespace") holds `token`, ASCII case-insensitively, as rel's keywords are (§4.6.1†:
/// "Link types are always ASCII case-insensitive").
fn has_token(value: &[u32], token: &str) -> bool {
    value
        .split(|&c| is_ascii_whitespace(c))
        .any(|t| eq_ignore_case(t, token))
}

/// A string's code points as bytes, if all are ASCII.
fn ascii_bytes(s: &[u32]) -> Option<Vec<u8>> {
    s.iter()
        .map(|&c| u8::try_from(c).ok().filter(u8::is_ascii))
        .collect()
}

fn is_text_css(m: &MimeType) -> bool {
    is(&m.type_, "text") && is(&m.subtype, "css")
}

/// The CSS style sheets "in tree order" (CSSOM §6.2) and the `style` attributes of the
/// document in `arena` (node 0, the document). Iterative; visits each node at most once.
pub fn collect(arena: &Arena) -> Sources {
    let mut out = Sources {
        quirks: matches!(
            arena.kind(0),
            ExecKind::Document {
                mode: DocumentMode::Quirks,
                ..
            }
        ),
        ..Sources::default()
    };
    let n = arena.len();
    let mut stack: Vec<usize> = vec![0];
    for _ in 0..n.saturating_add(1) {
        let Some(id) = stack.pop() else { break };
        if id >= n {
            continue;
        }
        if let ExecKind::Element {
            namespace,
            local_name,
            attributes,
            ..
        } = arena.kind(id)
        {
            // HTML §3.2.6.5, CSS Style Attributes §3: every element's `style` attribute.
            if let Some(v) = attribute(attributes, "style") {
                out.attributes.push(AttributeStyle {
                    node: id,
                    declarations: sheet::style_attribute(v),
                });
            }
            if matches!(namespace, Some(Namespace::Html)) {
                if is(local_name, "style") {
                    if let Some(s) = style_block(arena, id, attributes) {
                        out.sheets.push(s);
                    }
                } else if is(local_name, "link")
                    && let Some(s) = stylesheet_link(id, attributes)
                {
                    out.sheets.push(s);
                }
            }
        }
        stack.extend(arena.children(id).iter().rev());
    }
    out.add_style_sheets();
    out
}

/// HTML §4.2.6 "update a style block", for a `style` element in the document tree.
fn style_block(arena: &Arena, id: usize, attributes: &[ExecAttr]) -> Option<SheetSource> {
    // 1. "Let element be the style element."
    // 2. "If element has an associated CSS style sheet, remove the CSS style sheet in
    // question." (None yet: one pass.)
    // 3. "If element is not connected, then return." (It is: it was reached from the
    // document.)
    // 4. "If element's type attribute is present and its value is neither the empty string
    // nor an ASCII case-insensitive match for "text/css", then return."
    if let Some(t) = attribute(attributes, "type")
        && !t.is_empty()
        && !eq_ignore_case(t, "text/css")
    {
        return None;
    }
    // 5. Content Security Policy: not implemented, so never "Blocked".
    // 6. "Create a CSS style sheet with the following properties": its rules from the
    // element's child text content (the issue the step notes, #2997, says so), its media
    // and title the attributes' ("the empty string" if absent; a `style` element in the
    // tree is in a document tree), alternate flag unset.
    let mut text = Vec::new();
    for &c in arena.children(id) {
        if let ExecKind::Text { data } = arena.kind(c) {
            text.extend_from_slice(data);
        }
    }
    // 7. and 8. (script-blocking and render-blocking) are 5.20's.
    Some(SheetSource {
        node: id,
        owner: Owner::Style,
        media: media::parse(attribute(attributes, "media").unwrap_or_default()),
        title: attribute(attributes, "title").unwrap_or_default().to_vec(),
        disabled: false,
        sheet: Some(StyleSheet::parse(&text)),
    })
}

/// A `link` element that "creates an external resource link that contributes to the
/// styling processing model" (§4.6.8.23) and would be fetched: see the module's modelling
/// choices.
fn stylesheet_link(id: usize, attributes: &[ExecAttr]) -> Option<SheetSource> {
    let rel = attribute(attributes, "rel")?;
    if !has_token(rel, "stylesheet") {
        return None;
    }
    // §4.2.4: "If both the href and imagesrcset attributes are absent, then the element does
    // not define a link"; "create a link request" asserts the href is not empty.
    let href = attribute(attributes, "href")?;
    if href.is_empty() {
        return None;
    }
    // The stylesheet "linked resource fetch setup steps": "1. If el's disabled attribute is
    // set, then return false."
    if attribute(attributes, "disabled").is_some() {
        return None;
    }
    // §4.2.4.2: "If the type attribute is present, then the user agent must assume that the
    // resource is of the given type (even if that is not a valid MIME type string ...). ...
    // If the UA does not support the given MIME type for the given link relationship, then
    // the UA should not fetch and process the linked resource."
    if let Some(t) = attribute(attributes, "type") {
        let supported = ascii_bytes(t)
            .and_then(|b| parse_from_bytes(&b))
            .is_some_and(|m| is_text_css(&m));
        if !supported {
            return None;
        }
    }
    Some(SheetSource {
        node: id,
        owner: Owner::Link(Link {
            href: href.to_vec(),
            charset: attribute(attributes, "charset").map(<[u32]>::to_vec),
            alternate: has_token(rel, "alternate"),
            state: LinkState::Pending,
        }),
        media: media::parse(attribute(attributes, "media").unwrap_or_default()),
        title: attribute(attributes, "title").unwrap_or_default().to_vec(),
        disabled: false,
        sheet: None,
    })
}

impl Sources {
    /// CSSOM §6.2 "add a CSS style sheet", steps 3 to 6 (the disabled flag), for every sheet
    /// in tree order, with the "preferred CSS style sheet set name" starting empty and the
    /// "last CSS style sheet set name" null throughout.
    fn add_style_sheets(&mut self) {
        let mut preferred: Vec<u32> = Vec::new();
        for i in 0..self.sheets.len() {
            let Some(s) = self.sheets.get(i) else { break };
            let alternate = matches!(&s.owner, Owner::Link(l) if l.alternate);
            let title = s.title.clone();
            // 3. "If the disabled flag is set, then return." (It starts unset.)
            // 4. "If the title is not the empty string, the alternate flag is unset, and
            // preferred CSS style sheet set name is the empty string change the preferred
            // CSS style sheet set name to the title."
            if !title.is_empty() && !alternate && preferred.is_empty() {
                // "change the preferred CSS style sheet set name": 1. "Let current be the
                // preferred CSS style sheet set name." 2. "Set preferred ... to name." 3. "If
                // name is not a case-sensitive match for current and last CSS style sheet
                // set name is null enable a CSS style sheet set with name name."
                let current = std::mem::replace(&mut preferred, title.clone());
                if title != current {
                    // "enable a CSS style sheet set": "Unset the disabled flag for each CSS
                    // style sheet in a CSS style sheet set whose CSS style sheet set name is
                    // a case-sensitive match for name and set it for all other CSS style
                    // sheets in a CSS style sheet set." (Only those added so far.)
                    for t in self.sheets.iter_mut().take(i) {
                        if !t.title.is_empty() {
                            t.disabled = t.title != title;
                        }
                    }
                }
            }
            // 5. "If any of the following is true, then unset the disabled flag and return:
            // The title is the empty string. The last CSS style sheet set name is null and
            // the title is a case-sensitive match for the preferred CSS style sheet set
            // name. [The last name is never set.]"
            // 6. "Set the disabled flag."
            let disabled = !(title.is_empty() || title == preferred);
            if let Some(s) = self.sheets.get_mut(i) {
                s.disabled = disabled;
            }
        }
    }

    /// The indices of the links still to fetch, in tree order.
    pub fn pending_links(&self) -> Vec<usize> {
        self.sheets
            .iter()
            .enumerate()
            .filter(|(_, s)| matches!(&s.owner, Owner::Link(l) if l.state == LinkState::Pending))
            .map(|(i, _)| i)
            .collect()
    }

    /// HTML §4.6.8.23 "process this type of linked resource" for the link at `index` of
    /// [`Sources::sheets`], given its response; `document_encoding` is the document's
    /// character encoding. Nothing happens if `index` is not a link.
    pub fn link_loaded(
        &mut self,
        index: usize,
        response: Response<'_>,
        document_encoding: Encoding,
    ) {
        let quirks = self.quirks;
        let Some(s) = self.sheets.get_mut(index) else {
            return;
        };
        let Owner::Link(link) = &mut s.owner else {
            return;
        };
        let mime = response.content_type.and_then(parse_from_bytes);
        let is_css = mime.as_ref().is_some_and(is_text_css);
        // The quirk: "If the document has been set to quirks mode, has the same origin as the
        // URL of the external resource, and the Content-Type metadata of the external
        // resource is not a supported style sheet type, the user agent must instead assume
        // it to be text/css."
        let assumed_css = is_css || (quirks && response.same_origin);
        // 1. "If the resource's Content-Type metadata is not text/css, then set success to
        // false."
        let success = response.ok && assumed_css;
        // 2. (No longer a stylesheet link, or due to be fetched again: not in one pass.)
        // 3. "If el has an associated CSS style sheet, remove the CSS style sheet."
        s.sheet = None;
        // 4. "If success is true: Create a CSS style sheet with the following properties",
        // its rules from the body (the issue the step notes, #2997, says so), decoded with
        // the protocol's charset (CSS Syntax 3 §3.2) and "the CSS environment encoding ...
        // 1. If el has a charset attribute, get an encoding from that attribute's value. If
        // that succeeds, return the resulting encoding. 2. Otherwise, return the document's
        // character encoding."
        if !success {
            link.state = LinkState::Failed;
            return;
        }
        let protocol: Option<Vec<u32>> = if is_css {
            mime.as_ref().and_then(|m| {
                m.parameters
                    .iter()
                    .find(|(k, _)| is(k, "charset"))
                    .map(|(_, v)| v.clone())
            })
        } else {
            None
        };
        let environment = link
            .charset
            .as_deref()
            .and_then(get_an_encoding)
            .unwrap_or(document_encoding);
        match StyleSheet::from_bytes(response.body, protocol.as_deref(), Some(environment)) {
            Some(sheet) => {
                s.sheet = Some(sheet);
                link.state = LinkState::Loaded;
            }
            None => link.state = LinkState::Failed,
        }
    }

    /// The style rules that apply on `device`, in the cascade's order of appearance: the
    /// rules of each sheet that is enabled, has a sheet and whose `media` matches (HTML
    /// §4.2.6, §4.2.4.1: "must apply ... when the media attribute's value matches the
    /// environment ... and must not apply them otherwise"), in tree order, each sheet's in
    /// its order and filtered by its `@media` rules.
    pub fn rules_for(&self, device: Device) -> Vec<(usize, &StyleRule)> {
        let mut out = Vec::new();
        for (i, s) in self.sheets.iter().enumerate() {
            let Some(sheet) = &s.sheet else { continue };
            if s.disabled || !evaluate(&s.media, device) {
                continue;
            }
            out.extend(sheet.rules_for(device).into_iter().map(|r| (i, r)));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clazel_dom::exec::ExecAttr;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    /// A small document builder: element `name` with `attrs` under `parent`.
    struct Doc {
        arena: Arena,
    }

    impl Doc {
        fn new(quirks: bool) -> Doc {
            let mut arena = Arena::new(u("http://example.com/"));
            if quirks {
                arena.set_mode(DocumentMode::Quirks);
            }
            Doc { arena }
        }

        fn element(&mut self, parent: usize, name: &str, attrs: &[(&str, &str)]) -> usize {
            let attributes = attrs
                .iter()
                .map(|(k, v)| ExecAttr {
                    namespace: None,
                    prefix: None,
                    local_name: u(k),
                    value: u(v),
                })
                .collect();
            let id = self
                .arena
                .create(ExecKind::Element {
                    namespace: Some(Namespace::Html),
                    prefix: None,
                    local_name: u(name),
                    attributes,
                    template_contents: None,
                    form_owner: None,
                })
                .unwrap_or(0);
            self.arena.append(parent, id);
            id
        }

        fn text(&mut self, parent: usize, data: &str) {
            let id = self
                .arena
                .create(ExecKind::Text { data: u(data) })
                .unwrap_or(0);
            self.arena.append(parent, id);
        }
    }

    fn selectors(src: &Sources, w: u32, h: u32) -> Vec<String> {
        src.rules_for(Device::screen(w, h))
            .iter()
            .map(|(_, r)| s(&r.selectors).trim().to_owned())
            .collect()
    }

    #[test]
    fn style_elements_in_tree_order() {
        let mut d = Doc::new(false);
        let html = d.element(0, "html", &[]);
        let head = d.element(html, "head", &[]);
        let st = d.element(head, "style", &[]);
        d.text(st, "a{}");
        d.text(st, " b{}");
        let st2 = d.element(head, "style", &[("type", "TEXT/CSS"), ("media", "print")]);
        d.text(st2, "c{}");
        let st3 = d.element(head, "style", &[("type", "text/plain")]);
        d.text(st3, "x{}");
        let st4 = d.element(head, "style", &[("type", "text/css; charset=utf-8")]);
        d.text(st4, "y{}");
        let body = d.element(html, "body", &[]);
        let st5 = d.element(body, "style", &[("media", "screen and (max-width: 600px)")]);
        d.text(st5, "e{}");
        let src = collect(&d.arena);
        assert_eq!(src.sheets.len(), 3);
        assert_eq!(selectors(&src, 500, 500), ["a", "b", "e"]);
        assert_eq!(selectors(&src, 700, 500), ["a", "b"]);
        let print = Device {
            medium: Medium::Print,
            ..Device::screen(500, 500)
        };
        let names: Vec<String> = src
            .rules_for(print)
            .iter()
            .map(|(_, r)| s(&r.selectors).trim().to_owned())
            .collect();
        assert_eq!(names, ["a", "b", "c"]);
    }

    #[test]
    fn links_and_the_quirk() {
        for quirks in [false, true] {
            let mut d = Doc::new(quirks);
            let html = d.element(0, "html", &[]);
            let head = d.element(html, "head", &[]);
            d.element(
                head,
                "link",
                &[
                    ("rel", "stylesheet"),
                    ("type", "text/css"),
                    ("href", "news.css?x"),
                ],
            );
            d.element(
                head,
                "link",
                &[("rel", "Next StyleSheet"), ("href", "b.css")],
            );
            d.element(head, "link", &[("rel", "stylesheet"), ("href", "c.css")]);
            d.element(head, "link", &[("rel", "stylesheet"), ("href", "d.css")]);
            // Not fetched: no stylesheet keyword, empty href, disabled, unsupported type.
            d.element(head, "link", &[("rel", "icon"), ("href", "x")]);
            d.element(head, "link", &[("rel", "stylesheet"), ("href", "")]);
            d.element(
                head,
                "link",
                &[("rel", "stylesheet"), ("href", "x"), ("disabled", "")],
            );
            d.element(
                head,
                "link",
                &[("rel", "stylesheet"), ("href", "x"), ("type", "text/plain")],
            );
            d.element(
                head,
                "link",
                &[("rel", "stylesheet"), ("href", "x"), ("type", "")],
            );
            let mut src = collect(&d.arena);
            assert_eq!(src.quirks, quirks);
            assert_eq!(src.pending_links(), [0, 1, 2, 3]);
            let hrefs: Vec<String> = src
                .sheets
                .iter()
                .filter_map(|s| match &s.owner {
                    Owner::Link(l) => Some(s_of(&l.href)),
                    Owner::Style => None,
                })
                .collect();
            assert_eq!(hrefs, ["news.css?x", "b.css", "c.css", "d.css"]);
            let ok = |content_type: Option<&'static [u8]>,
                      same_origin: bool,
                      body: &'static [u8]| Response {
                content_type,
                same_origin,
                ok: true,
                body,
            };
            src.link_loaded(
                0,
                ok(Some(b"text/css; charset=utf-8"), true, b"a{}"),
                Encoding::Utf8,
            );
            // Same origin, wrong type: used only in quirks mode.
            src.link_loaded(1, ok(Some(b"text/plain"), true, b"b{}"), Encoding::Utf8);
            // Cross origin, wrong type: never.
            src.link_loaded(2, ok(None, false, b"c{}"), Encoding::Utf8);
            // A failed fetch: never.
            src.link_loaded(
                3,
                Response {
                    ok: false,
                    ..ok(Some(b"text/css"), true, b"d{}")
                },
                Encoding::Utf8,
            );
            let want: &[&str] = if quirks { &["a", "b"] } else { &["a"] };
            assert_eq!(selectors(&src, 1, 1), want, "quirks {quirks}");
            assert!(src.pending_links().is_empty());
        }
    }

    fn s_of(v: &[u32]) -> String {
        s(v)
    }

    #[test]
    fn titles_and_alternates() {
        let mut d = Doc::new(false);
        let html = d.element(0, "html", &[]);
        let head = d.element(html, "head", &[]);
        let alt = d.element(head, "style", &[("title", "B")]);
        d.text(alt, "x{}");
        let persistent = d.element(head, "style", &[]);
        d.text(persistent, "a{}");
        let a1 = d.element(head, "style", &[("title", "A")]);
        d.text(a1, "b{}");
        let a2 = d.element(head, "style", &[("title", "A")]);
        d.text(a2, "c{}");
        let b2 = d.element(head, "style", &[("title", "B")]);
        d.text(b2, "y{}");
        let src = collect(&d.arena);
        // The first titled sheet ("B") sets the preferred set, so the "A" sheets are
        // disabled.
        assert_eq!(selectors(&src, 1, 1), ["x", "a", "y"]);

        let mut d = Doc::new(false);
        let html = d.element(0, "html", &[]);
        let head = d.element(html, "head", &[]);
        d.element(
            head,
            "link",
            &[
                ("rel", "alternate stylesheet"),
                ("title", "Big"),
                ("href", "big.css"),
            ],
        );
        d.element(
            head,
            "link",
            &[
                ("rel", "stylesheet"),
                ("title", "Small"),
                ("href", "small.css"),
            ],
        );
        d.element(head, "link", &[("rel", "stylesheet"), ("href", "base.css")]);
        let mut src = collect(&d.arena);
        for (i, body) in [(0usize, &b"big{}"[..]), (1, b"small{}"), (2, b"base{}")] {
            let r = Response {
                content_type: Some(b"text/css"),
                same_origin: true,
                ok: true,
                body,
            };
            src.link_loaded(i, r, Encoding::Utf8);
        }
        assert_eq!(selectors(&src, 1, 1), ["small", "base"]);
    }

    #[test]
    fn style_attributes_in_tree_order() {
        let mut d = Doc::new(true);
        let html = d.element(0, "html", &[]);
        let body = d.element(html, "body", &[("style", "margin:0")]);
        let tr = d.element(body, "tr", &[("style", "height:5px")]);
        d.element(tr, "td", &[("class", "x")]);
        d.element(body, "div", &[("style", "")]);
        let src = collect(&d.arena);
        let nodes: Vec<usize> = src.attributes.iter().map(|a| a.node).collect();
        assert_eq!(nodes, [body, tr, tr + 2]);
        let names: Vec<Vec<String>> = src
            .attributes
            .iter()
            .map(|a| a.declarations.iter().map(|d| s(&d.name)).collect())
            .collect();
        assert_eq!(
            names,
            [vec!["margin".to_owned()], vec!["height".to_owned()], vec![]]
        );
    }

    #[test]
    fn charset_attribute_and_document_encoding() {
        let mut d = Doc::new(false);
        let html = d.element(0, "html", &[]);
        d.element(
            html,
            "link",
            &[
                ("rel", "stylesheet"),
                ("href", "a.css"),
                ("charset", "iso-8859-1"),
            ],
        );
        let mut src = collect(&d.arena);
        let r = Response {
            content_type: Some(b"text/css"),
            same_origin: true,
            ok: true,
            body: b".\xe9{}",
        };
        src.link_loaded(0, r, Encoding::Utf8);
        assert_eq!(selectors(&src, 1, 1), [".\u{e9}"]);
    }
}
