//! HTML §13.2.4.2 the stack of open elements (the current node, the
//! scopes, popping) and §13.2.4.1 "reset the insertion mode
//! appropriately", over [`ParserBuf`]. Each function is proven equal to the
//! spec function of `spec/base/state.rs` it names, and to keep
//! [`parser_inv`].
//!
//! The spec's helpers that take a predicate (`in_scope_from`,
//! `last_index_where`, `pop_while`) take an [`ElemPred`] here, the exec
//! form of the predicates the rules use, with the spec predicate as a ghost
//! argument `f` that must agree with it ([`pred_spec`]).

#[cfg(verus_only)]
use super::frame::*;
use super::names::*;
#[allow(unused_imports)]
use super::spec::*;
use super::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Predicates on element records

/// The predicates on element records the rules use.
pub enum ElemPred<'a> {
    /// `is_html(e, tag)`.
    HtmlTag(Tag),
    /// `e.id == id`.
    Id(usize),
    /// `is_heading(e)`: HTML h1 to h6.
    Heading,
    /// `e.ns == Html && e.name == name` (`is_html_named`).
    HtmlName(&'a [u32]),
    /// `is_html(e, Template) || is_html(e, Table)`.
    TemplateOrTable,
    /// `is_html(e, Tbody) || is_html(e, Thead) || is_html(e, Tfoot)`.
    TableSection,
    /// `implied_end_tag(e) && !(except is Some && e.tag == except)`
    /// ("generate implied end tags", except for `except`).
    ImpliedEnd(Option<Tag>),
    /// The list of "generate all implied end tags thoroughly".
    Thoroughly,
    /// `!(is_html(e, Table) || is_html(e, Template) || is_html(e, Html))`
    /// ("clear the stack back to a table context").
    NotTableContext,
    /// `!(is_html(e, Tbody) || … Tfoot || … Thead || … Template || …
    /// Html)` ("clear the stack back to a table body context").
    NotTableBodyContext,
    /// `!(is_html(e, Tr) || is_html(e, Template) || is_html(e, Html))`
    /// ("clear the stack back to a table row context").
    NotRowContext,
    /// `!(is_mathml_text_integration_point(e) ||
    /// is_html_integration_point(e) || e.ns == Html)` (foreign content's
    /// breakout rule).
    NotHtmlContent,
}

/// The "thoroughly" list of §13.2.6.3.
pub open spec fn thoroughly(e: Elem) -> bool {
    e.ns == Namespace::Html && match e.tag {
        Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb | Tag::Rp
        | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr => true,
        _ => false,
    }
}

/// The spec predicate of an [`ElemPred`].
pub open spec fn pred_spec(pr: &ElemPred, e: Elem) -> bool {
    match pr {
        ElemPred::HtmlTag(t) => is_html(e, *t),
        ElemPred::Id(id) => e.id == *id,
        ElemPred::Heading => is_heading(e),
        ElemPred::HtmlName(n) => e.ns == Namespace::Html && e.name == n@,
        ElemPred::TemplateOrTable => is_html(e, Tag::Template) || is_html(e, Tag::Table),
        ElemPred::TableSection => is_html(e, Tag::Tbody) || is_html(e, Tag::Thead) || is_html(e, Tag::Tfoot),
        ElemPred::ImpliedEnd(except) => implied_end_tag(e) && !(except is Some && e.tag == except->Some_0),
        ElemPred::Thoroughly => thoroughly(e),
        ElemPred::NotTableContext => !(is_html(e, Tag::Table) || is_html(e, Tag::Template) || is_html(e, Tag::Html)),
        ElemPred::NotTableBodyContext => !(is_html(e, Tag::Tbody) || is_html(e, Tag::Tfoot) || is_html(e, Tag::Thead) || is_html(
            e,
            Tag::Template,
        ) || is_html(e, Tag::Html)),
        ElemPred::NotRowContext => !(is_html(e, Tag::Tr) || is_html(e, Tag::Template) || is_html(e, Tag::Html)),
        ElemPred::NotHtmlContent => !(is_mathml_text_integration_point(e) || is_html_integration_point(e) || e.ns
            == Namespace::Html),
    }
}

/// `f` is the spec predicate of `pr`.
pub open spec fn pred_is(pr: &ElemPred, f: spec_fn(Elem) -> bool) -> bool {
    forall|e: Elem| #[trigger] f(e) == pred_spec(pr, e)
}

/// The element is an HTML element.
pub fn is_html_ns(e: &ExecElem) -> (r: bool)
    ensures
        r == (e@.ns == Namespace::Html),
{
    matches!(e.ns, Namespace::Html)
}

/// [`is_html`] with a fixed tag.
pub fn is_html_exec(e: &ExecElem, tag: &Tag) -> (r: bool)
    ensures
        r == is_html(e@, *tag),
{
    is_html_ns(e) && tag_eq(&e.tag, tag)
}

/// [`is_heading`].
pub fn is_heading_exec(e: &ExecElem) -> (r: bool)
    ensures
        r == is_heading(e@),
{
    is_html_ns(e) && matches!(e.tag, Tag::H1 | Tag::H2 | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6)
}

/// [`implied_end_tag`].
pub fn implied_end_tag_exec(e: &ExecElem) -> (r: bool)
    ensures
        r == implied_end_tag(e@),
{
    is_html_ns(e) && matches!(
        e.tag,
        Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb | Tag::Rp | Tag::Rt | Tag::Rtc
    )
}

/// [`is_mathml_text_integration_point`].
pub fn is_mathml_text_integration_point_exec(e: &ExecElem) -> (r: bool)
    ensures
        r == is_mathml_text_integration_point(e@),
{
    matches!(e.ns, Namespace::MathMl) && matches!(e.tag, Tag::Mi | Tag::Mo | Tag::Mn | Tag::Ms | Tag::Mtext)
}

/// [`is_html_integration_point`].
pub fn is_html_integration_point_exec(e: &ExecElem) -> (r: bool)
    ensures
        r == is_html_integration_point(e@),
{
    (matches!(e.ns, Namespace::MathMl) && matches!(e.tag, Tag::AnnotationXml) && e.annotation_html) || (matches!(
        e.ns,
        Namespace::Svg
    ) && matches!(e.tag, Tag::Foreignobject | Tag::Desc | Tag::Title))
}

/// [`pred_spec`].
pub fn pred_exec(pr: &ElemPred, e: &ExecElem) -> (r: bool)
    ensures
        r == pred_spec(pr, e@),
{
    let html = is_html_ns(e);
    match pr {
        ElemPred::HtmlTag(t) => html && tag_eq(&e.tag, t),
        ElemPred::Id(id) => e.id == *id,
        ElemPred::Heading => is_heading_exec(e),
        ElemPred::HtmlName(n) => html && u32s_eq(e.name.as_slice(), n),
        ElemPred::TemplateOrTable => html && matches!(e.tag, Tag::Template | Tag::Table),
        ElemPred::TableSection => html && matches!(e.tag, Tag::Tbody | Tag::Thead | Tag::Tfoot),
        ElemPred::ImpliedEnd(except) => implied_end_tag_exec(e) && !match except {
            Some(x) => tag_eq(&e.tag, x),
            None => false,
        },
        ElemPred::Thoroughly => html && matches!(
            e.tag,
            Tag::Caption | Tag::Colgroup | Tag::Dd | Tag::Dt | Tag::Li | Tag::Optgroup | Tag::Option | Tag::P | Tag::Rb | Tag::Rp
                | Tag::Rt | Tag::Rtc | Tag::Tbody | Tag::Td | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Tr
        ),
        ElemPred::NotTableContext => !(html && matches!(e.tag, Tag::Table | Tag::Template | Tag::Html)),
        ElemPred::NotTableBodyContext => !(html && matches!(
            e.tag,
            Tag::Tbody | Tag::Tfoot | Tag::Thead | Tag::Template | Tag::Html
        )),
        ElemPred::NotRowContext => !(html && matches!(e.tag, Tag::Tr | Tag::Template | Tag::Html)),
        ElemPred::NotHtmlContent => !(is_mathml_text_integration_point_exec(e) || is_html_integration_point_exec(e) || html),
    }
}

// ---------------------------------------------------------------------
// The current node and the categories

/// [`current_node`].
pub fn current_node_exec(p: &ParserBuf) -> (r: &ExecElem)
    requires
        p@.open.len() > 0,
    ensures
        r@ == current_node(p@),
{
    let n = p.open.len();
    match p.open.get(n.saturating_sub(1)) {
        Some(e) => e,
        None => vstd::pervasive::unreached(),
    }
}

/// [`adjusted_current_node`].
pub fn adjusted_current_node_exec(p: &ParserBuf) -> (r: &ExecElem)
    requires
        p@.open.len() > 0,
    ensures
        r@ == adjusted_current_node(p@),
{
    match &p.context {
        Some(c) if p.open.len() == 1 => return c,
        _ => {},
    }
    current_node_exec(p)
}

/// [`is_special`].
pub fn is_special_exec(e: &ExecElem) -> (r: bool)
    ensures
        r == is_special(e@),
{
    match e.ns {
        Namespace::Html => matches!(
            e.tag,
            Tag::Address | Tag::Applet | Tag::Area | Tag::Article | Tag::Aside | Tag::Base | Tag::Basefont | Tag::Bgsound
                | Tag::Blockquote | Tag::Body | Tag::Br | Tag::Button | Tag::Caption | Tag::Center | Tag::Col | Tag::Colgroup
                | Tag::Dd | Tag::Details | Tag::Dir | Tag::Div | Tag::Dl | Tag::Dt | Tag::Embed | Tag::Fieldset
                | Tag::Figcaption | Tag::Figure | Tag::Footer | Tag::Form | Tag::Frame | Tag::Frameset | Tag::H1 | Tag::H2
                | Tag::H3 | Tag::H4 | Tag::H5 | Tag::H6 | Tag::Head | Tag::Header | Tag::Hgroup | Tag::Hr | Tag::Html
                | Tag::Iframe | Tag::Img | Tag::Input | Tag::Keygen | Tag::Li | Tag::Link | Tag::Listing | Tag::Main
                | Tag::Marquee | Tag::Menu | Tag::Meta | Tag::Nav | Tag::Noembed | Tag::Noframes | Tag::Noscript | Tag::Object
                | Tag::Ol | Tag::P | Tag::Param | Tag::Plaintext | Tag::Pre | Tag::Script | Tag::Search | Tag::Section
                | Tag::Select | Tag::Source | Tag::Style | Tag::Summary | Tag::Table | Tag::Tbody | Tag::Td | Tag::Template
                | Tag::Textarea | Tag::Tfoot | Tag::Th | Tag::Thead | Tag::Title | Tag::Tr | Tag::Track | Tag::Ul | Tag::Wbr
                | Tag::Xmp
        ),
        Namespace::MathMl => matches!(e.tag, Tag::Mi | Tag::Mo | Tag::Mn | Tag::Ms | Tag::Mtext | Tag::AnnotationXml),
        Namespace::Svg => matches!(e.tag, Tag::Foreignobject | Tag::Desc | Tag::Title),
        _ => false,
    }
}

/// [`is_formatting_tag`].
pub fn is_formatting_tag_exec(t: &Tag) -> (r: bool)
    ensures
        r == is_formatting_tag(*t),
{
    matches!(
        t,
        Tag::A | Tag::B | Tag::Big | Tag::Code | Tag::Em | Tag::Font | Tag::I | Tag::Nobr | Tag::S | Tag::Small | Tag::Strike
            | Tag::Strong | Tag::Tt | Tag::U
    )
}

/// [`in_scope_list`].
pub fn in_scope_list_exec(e: &ExecElem, s: &Scope) -> (r: bool)
    ensures
        r == in_scope_list(e@, *s),
{
    let default = match e.ns {
        Namespace::Html => matches!(
            e.tag,
            Tag::Applet | Tag::Caption | Tag::Html | Tag::Table | Tag::Td | Tag::Th | Tag::Marquee | Tag::Object | Tag::Select
                | Tag::Template
        ),
        Namespace::MathMl => matches!(e.tag, Tag::Mi | Tag::Mo | Tag::Mn | Tag::Ms | Tag::Mtext | Tag::AnnotationXml),
        Namespace::Svg => matches!(e.tag, Tag::Foreignobject | Tag::Desc | Tag::Title),
        _ => false,
    };
    let html = is_html_ns(e);
    match s {
        Scope::Default => default,
        Scope::ListItem => default || (html && matches!(e.tag, Tag::Ol | Tag::Ul)),
        Scope::Button => default || (html && matches!(e.tag, Tag::Button)),
        Scope::Table => html && matches!(e.tag, Tag::Html | Tag::Table | Tag::Template),
    }
}

// ---------------------------------------------------------------------
// Scopes and searches

/// [`in_scope_from`] over the whole stack, for the target `pr`.
pub fn in_scope_exec(p: &ParserBuf, pr: &ElemPred, Ghost(f): Ghost<spec_fn(Elem) -> bool>, s: &Scope) -> (r: bool)
    requires
        pred_is(pr, f),
    ensures
        r == in_scope_from(p@.open, p@.open.len() as int, f, *s),
{
    let ghost o = p@.open;
    let mut i = p.open.len();
    while i > 0
        invariant
            o == p@.open,
            i <= o.len(),
            pred_is(pr, f),
            in_scope_from(o, o.len() as int, f, *s) == in_scope_from(o, i as int, f, *s),
        decreases i,
    {
        let e = match p.open.get(i.saturating_sub(1)) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(e@ == o[i - 1]);
        }
        if pred_exec(pr, e) {
            return true;
        }
        if in_scope_list_exec(e, s) {
            return false;
        }
        i = i.saturating_sub(1);
    }
    false
}

/// [`has_in_scope`].
pub fn has_in_scope_exec(p: &ParserBuf, tag: Tag, s: &Scope) -> (r: bool)
    ensures
        r == has_in_scope(p@, tag, *s),
{
    let ghost f = |e: Elem| is_html(e, tag);
    let pr = ElemPred::HtmlTag(tag);
    in_scope_exec(p, &pr, Ghost(f), s)
}

/// [`has_node_in_scope`].
pub fn has_node_in_scope_exec(p: &ParserBuf, id: usize, s: &Scope) -> (r: bool)
    ensures
        r == has_node_in_scope(p@, id, *s),
{
    let ghost f = |e: Elem| e.id == id;
    in_scope_exec(p, &ElemPred::Id(id), Ghost(f), s)
}

/// [`has_heading_in_scope`].
pub fn has_heading_in_scope_exec(p: &ParserBuf) -> (r: bool)
    ensures
        r == has_heading_in_scope(p@),
{
    let ghost f = |e: Elem|
        e.ns == Namespace::Html && (e.tag == Tag::H1 || e.tag == Tag::H2 || e.tag == Tag::H3 || e.tag == Tag::H4 || e.tag
            == Tag::H5 || e.tag == Tag::H6);
    in_scope_exec(p, &ElemPred::Heading, Ghost(f), &Scope::Default)
}

/// [`last_index_where`] over the first `i` records of `open`: `Some` of the
/// index, or `None` for -1.
pub fn last_index_where_exec(open: &[ExecElem], i: usize, pr: &ElemPred, Ghost(f): Ghost<spec_fn(Elem) -> bool>) -> (r:
    Option<usize>)
    requires
        i <= open@.len(),
        pred_is(pr, f),
    ensures
        match r {
            Some(k) => k < i && k as int == last_index_where(elems_view(open@), i as int, f),
            None => last_index_where(elems_view(open@), i as int, f) == -1,
        },
{
    let ghost o = elems_view(open@);
    let mut j = i;
    while j > 0
        invariant
            j <= i,
            i <= open@.len(),
            o == elems_view(open@),
            pred_is(pr, f),
            last_index_where(o, i as int, f) == last_index_where(o, j as int, f),
        decreases j,
    {
        let e = match open.get(j.saturating_sub(1)) {
            Some(e) => e,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(e@ == o[j - 1]);
        }
        if pred_exec(pr, e) {
            return Some(j.saturating_sub(1));
        }
        j = j.saturating_sub(1);
    }
    None
}

/// [`last_index_where`] finds a satisfying entry if there is one.
pub proof fn lemma_last_index_where_found(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, k: int)
    requires
        0 <= k < i <= open.len(),
        f(open[k]),
    ensures
        k <= last_index_where(open, i, f) < i,
        f(open[last_index_where(open, i, f)]),
    decreases i,
{
    if !f(open[i - 1]) {
        lemma_last_index_where_found(open, i - 1, f, k);
    }
}

/// [`last_index_where`] is -1 or an index below `i` satisfying `f`, with
/// none after it.
pub proof fn lemma_last_index_where(open: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= i <= open.len(),
    ensures
        -1 <= last_index_where(open, i, f) < i,
        last_index_where(open, i, f) >= 0 ==> f(open[last_index_where(open, i, f)]),
        forall|j: int| last_index_where(open, i, f) < j < i ==> !f(#[trigger] open[j]),
    decreases i,
{
    if i > 0 && !f(open[i - 1]) {
        lemma_last_index_where(open, i - 1, f);
    }
}

/// [`open_has`].
pub fn open_has_exec(p: &ParserBuf, pr: &ElemPred, Ghost(f): Ghost<spec_fn(Elem) -> bool>) -> (r: bool)
    requires
        pred_is(pr, f),
    ensures
        r == open_has(p@, f),
{
    last_index_where_exec(p.open.as_slice(), p.open.len(), pr, Ghost(f)).is_some()
}

/// [`open_has_html`].
pub fn open_has_html_exec(p: &ParserBuf, tag: Tag) -> (r: bool)
    ensures
        r == open_has_html(p@, tag),
{
    let ghost f = |e: Elem| is_html(e, tag);
    open_has_exec(p, &ElemPred::HtmlTag(tag), Ghost(f))
}

/// [`open_index_of`]: `Some` of the index, or `None` for -1.
pub fn open_index_of_exec(p: &ParserBuf, id: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < p@.open.len() && k as int == open_index_of(p@, id),
            None => open_index_of(p@, id) == -1,
        },
{
    let ghost f = |e: Elem| e.id == id;
    last_index_where_exec(p.open.as_slice(), p.open.len(), &ElemPred::Id(id), Ghost(f))
}

/// [`parsing_template_contents`].
pub fn parsing_template_contents_exec(p: &ParserBuf) -> (r: bool)
    ensures
        r == parsing_template_contents(p@),
{
    if open_has_html_exec(p, Tag::Template) {
        return true;
    }
    match &p.context {
        Some(c) => is_html_ns(c) && matches!(c.tag, Tag::Template),
        None => false,
    }
}

/// [`in_foreign_content`].
pub fn in_foreign_content_exec(p: &ParserBuf) -> (r: bool)
    ensures
        r == in_foreign_content(p@),
{
    !p.open.is_empty() && !is_html_ns(adjusted_current_node_exec(p))
}

// ---------------------------------------------------------------------
// Popping and pushing

/// The parser with the stack `o` and everything else of `p`.
pub open spec fn with_open(p: Parser, o: Seq<Elem>) -> Parser {
    Parser { open: o, ..p }
}

/// Pop the stack in place: `p@` becomes [`pop`] of it.
proof fn lemma_pop_view(v: Seq<ExecElem>)
    requires
        v.len() > 0,
    ensures
        elems_view(v.drop_last()) == elems_view(v).drop_last(),
{
    assert(elems_view(v.drop_last()) =~= elems_view(v).drop_last());
}

/// Popping keeps [`parser_inv`].
pub proof fn lemma_pop_inv(p: Parser)
    requires
        parser_inv(p),
    ensures
        parser_inv(pop(p)),
{
    if p.open.len() > 0 {
        lemma_inv_iff(p);
        lemma_inv_iff(pop(p));
        lemma_open_drop_last(p.doc, p.open);
        crate::termination::helpers_ranking::lemma_pop(p);
    }
}

/// Removing entry `i` of a stack removes at most one `template` element.
pub proof fn lemma_tcount_remove(o: Seq<Elem>, i: int)
    requires
        0 <= i < o.len(),
    ensures
        crate::termination::helpers_ranking::tcount(o.remove(i)) <= crate::termination::helpers_ranking::tcount(o),
{
    let r = o.remove(i);
    crate::termination::helpers_ranking::lemma_templates_in_same(r, o, i);
    lemma_templates_in_remove_from(o, i, o.len() as int);
}

/// Above the removed entry, the counts differ by that entry's.
proof fn lemma_templates_in_remove_from(o: Seq<Elem>, i: int, k: int)
    requires
        0 <= i < k <= o.len(),
        crate::termination::templates_in(o.remove(i), i) == crate::termination::templates_in(o, i),
    ensures
        crate::termination::templates_in(o.remove(i), k - 1) + (if is_html(o[i], Tag::Template) {
            1nat
        } else {
            0nat
        }) == crate::termination::templates_in(o, k),
    decreases k,
{
    if k > i + 1 {
        lemma_templates_in_remove_from(o, i, k - 1);
        assert(o.remove(i)[k - 2] == o[k - 1]);
    }
}

/// Pushing a record adds at most one `template` element, and none if it is
/// not one.
pub proof fn lemma_tcount_push(o: Seq<Elem>, e: Elem)
    ensures
        crate::termination::helpers_ranking::tcount(o.push(e)) == crate::termination::helpers_ranking::tcount(o) + (if is_html(
            e,
            Tag::Template,
        ) {
            1nat
        } else {
            0nat
        }),
{
    let b = o.push(e);
    crate::termination::helpers_ranking::lemma_templates_in_same(o, b, o.len() as int);
    assert(b[o.len() as int] == e);
}

/// [`pop`].
pub fn pop_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop(old(p)@),
        parser_inv(final(p)@),
{
    proof {
        lemma_pop_inv(old(p)@);
    }
    if !p.open.is_empty() {
        let ghost v = p.open@;
        let _ = p.open.pop();
        proof {
            lemma_pop_view(v);
        }
    }
}

/// [`push`]: the record must be an [`elem_ok`] one unless parsing has
/// stopped (the records [`super::insert`] makes are).
pub fn push_exec(p: &mut ParserBuf, e: ExecElem)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped ==> elem_ok(old(p)@.doc, e@),
        !old(p)@.stopped && is_html(e@, Tag::Template) ==> crate::termination::template_count(old(p)@)
            < old(p)@.template_modes.len(),
    ensures
        final(p)@ == push(old(p)@, e@),
        parser_inv(final(p)@),
{
    if !p.stopped {
        let ghost v = p.open@;
        let ghost x = e@;
        p.open.push(e);
        proof {
            assert(elems_view(p.open@) =~= elems_view(v).push(x));
            lemma_inv_iff(old(p)@);
            lemma_inv_iff(p@);
            lemma_open_push(p@.doc, elems_view(v), x);
            lemma_tcount_push(elems_view(v), x);
        }
    }
}

/// Pop until a record satisfying `f` has been popped (all of them if none
/// does): the form of [`pop_until_popped`], [`pop_until_heading_popped`]
/// and [`pop_until_node_popped`].
pub open spec fn pop_until_where(p: Parser, f: spec_fn(Elem) -> bool) -> Parser
    decreases p.open.len(),
{
    if p.open.len() == 0 {
        p
    } else if f(current_node(p)) {
        pop(p)
    } else {
        pop_until_where(pop(p), f)
    }
}

/// [`pop_until_popped`] is [`pop_until_where`].
pub proof fn lemma_pop_until_popped(p: Parser, tag: Tag)
    ensures
        pop_until_popped(p, tag) == pop_until_where(p, |e: Elem| is_html(e, tag)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_html(current_node(p), tag) {
        lemma_pop_until_popped(pop(p), tag);
    }
}

/// [`pop_until_heading_popped`] is [`pop_until_where`].
pub proof fn lemma_pop_until_heading_popped(p: Parser)
    ensures
        pop_until_heading_popped(p) == pop_until_where(p, |e: Elem| is_heading(e)),
    decreases p.open.len(),
{
    if p.open.len() > 0 && !is_heading(current_node(p)) {
        lemma_pop_until_heading_popped(pop(p));
    }
}

/// [`pop_until_node_popped`] is [`pop_until_where`].
pub proof fn lemma_pop_until_node_popped(p: Parser, id: NodeId)
    ensures
        pop_until_node_popped(p, id) == pop_until_where(p, |e: Elem| e.id == id),
    decreases p.open.len(),
{
    if p.open.len() > 0 && current_node(p).id != id {
        lemma_pop_until_node_popped(pop(p), id);
    }
}

/// [`pop_until_where`].
pub fn pop_until_where_exec(p: &mut ParserBuf, pr: &ElemPred, Ghost(f): Ghost<spec_fn(Elem) -> bool>)
    requires
        parser_inv(old(p)@),
        pred_is(pr, f),
    ensures
        final(p)@ == pop_until_where(old(p)@, f),
        parser_inv(final(p)@),
{
    loop
        invariant
            parser_inv(p@),
            pred_is(pr, f),
            pop_until_where(p@, f) == pop_until_where(old(p)@, f),
        decreases p@.open.len(),
    {
        if p.open.is_empty() {
            return;
        }
        let hit = pred_exec(pr, current_node_exec(p));
        pop_exec(p);
        if hit {
            return;
        }
    }
}

/// [`pop_until_popped`].
pub fn pop_until_popped_exec(p: &mut ParserBuf, tag: Tag)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop_until_popped(old(p)@, tag),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem| is_html(e, tag);
    proof {
        lemma_pop_until_popped(old(p)@, tag);
    }
    pop_until_where_exec(p, &ElemPred::HtmlTag(tag), Ghost(f));
}

/// [`pop_until_heading_popped`].
pub fn pop_until_heading_popped_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop_until_heading_popped(old(p)@),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem| is_heading(e);
    proof {
        lemma_pop_until_heading_popped(old(p)@);
    }
    pop_until_where_exec(p, &ElemPred::Heading, Ghost(f));
}

/// [`pop_until_node_popped`].
pub fn pop_until_node_popped_exec(p: &mut ParserBuf, id: usize)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == pop_until_node_popped(old(p)@, id),
        parser_inv(final(p)@),
{
    let ghost f = |e: Elem| e.id == id;
    proof {
        lemma_pop_until_node_popped(old(p)@, id);
    }
    pop_until_where_exec(p, &ElemPred::Id(id), Ghost(f));
}

/// [`pop_while`].
pub fn pop_while_exec(p: &mut ParserBuf, pr: &ElemPred, Ghost(f): Ghost<spec_fn(Elem) -> bool>)
    requires
        parser_inv(old(p)@),
        pred_is(pr, f),
    ensures
        final(p)@ == pop_while(old(p)@, f),
        parser_inv(final(p)@),
{
    loop
        invariant
            parser_inv(p@),
            pred_is(pr, f),
            pop_while(p@, f) == pop_while(old(p)@, f),
        decreases p@.open.len(),
    {
        if p.open.is_empty() {
            return;
        }
        if !pred_exec(pr, current_node_exec(p)) {
            return;
        }
        pop_exec(p);
    }
}

/// [`remove_open_at`].
pub fn remove_open_at_exec(p: &mut ParserBuf, i: usize)
    requires
        parser_inv(old(p)@),
        i < old(p)@.open.len(),
    ensures
        final(p)@ == remove_open_at(old(p)@, i as int),
        parser_inv(final(p)@),
{
    let ghost v = p.open@;
    let _ = p.open.remove(i);
    proof {
        assert(elems_view(p.open@) =~= elems_view(v).remove(i as int));
        lemma_inv_iff(old(p)@);
        lemma_inv_iff(p@);
        lemma_open_remove(p@.doc, elems_view(v), i as int);
        lemma_tcount_remove(elems_view(v), i as int);
    }
}

// ---------------------------------------------------------------------
// §13.2.4.1 reset the insertion mode appropriately

/// [`reset_insertion_mode`]. (Step 10 reads the current template
/// insertion mode, which exists by `modes_ok`'s count of templates.)
pub fn reset_insertion_mode_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == reset_insertion_mode(old(p)@),
        parser_inv(final(p)@),
{
    let m = reset_mode(p);
    p.mode = m;
}

/// The mode [`reset_from`] gives from the last entry.
fn reset_mode(p: &ParserBuf) -> (r: Mode)
    requires
        parser_inv(p@),
    ensures
        r == reset_from(p@, p@.open.len() - 1),
        r != Mode::Text && r != Mode::InTableText,
        r == Mode::InTemplate ==> p@.template_modes.len() > 0,
{
    proof {
        lemma_inv_iff(p@);
    }
    let n = p.open.len();
    if n == 0 {
        return Mode::InBody;
    }
    let mut i: usize = n.saturating_sub(1);
    loop
        invariant
            n == p@.open.len(),
            i < n,
            parser_inv(p@),
            modes_core(p@),
            reset_from(p@, n - 1) == reset_from(p@, i as int),
        decreases i,
    {
        let last = i == 0;
        let node: &ExecElem = if last && p.context.is_some() {
            match &p.context {
                Some(c) => c,
                None => vstd::pervasive::unreached(),
            }
        } else {
            match p.open.get(i) {
                Some(e) => e,
                None => vstd::pervasive::unreached(),
            }
        };
        let html = is_html_ns(node);
        if html && matches!(node.tag, Tag::Td | Tag::Th) && !last {
            // 4.
            return Mode::InCell;
        } else if html && matches!(node.tag, Tag::Tr) {
            // 5.
            return Mode::InRow;
        } else if html && matches!(node.tag, Tag::Tbody | Tag::Thead | Tag::Tfoot) {
            // 6.
            return Mode::InTableBody;
        } else if html && matches!(node.tag, Tag::Caption) {
            // 7.
            return Mode::InCaption;
        } else if html && matches!(node.tag, Tag::Colgroup) {
            // 8.
            return Mode::InColumnGroup;
        } else if html && matches!(node.tag, Tag::Table) {
            // 9.
            return Mode::InTable;
        } else if html && matches!(node.tag, Tag::Template) {
            // 10.
            proof {
                if !(last && p@.context is Some) {
                    crate::termination::helpers_ranking::lemma_templates_in_pos(p@.open, n as int, i as int);
                }
                let k = p@.template_modes.len() - 1;
                assert(crate::termination::template_mode_ok(p@.template_modes[k]));
            }
            let k = p.template_modes.len();
            return match p.template_modes.get(k.saturating_sub(1)) {
                Some(m) => copy_mode(m),
                None => vstd::pervasive::unreached(),
            };
        } else if html && matches!(node.tag, Tag::Head) && !last {
            // 11.
            return Mode::InHead;
        } else if html && matches!(node.tag, Tag::Body) {
            // 12.
            return Mode::InBody;
        } else if html && matches!(node.tag, Tag::Frameset) {
            // 13.
            return Mode::InFrameset;
        } else if html && matches!(node.tag, Tag::Html) {
            // 14.1, 14.2
            return if p.head.is_none() {
                Mode::BeforeHead
            } else {
                Mode::AfterHead
            };
        } else if last {
            // 15.
            return Mode::InBody;
        }
        // 16., 17.
        i = i.saturating_sub(1);
    }
}

} // verus!
