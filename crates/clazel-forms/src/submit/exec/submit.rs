//! The form submission algorithm, executably: the attributes of a form and
//! its submitter, the target, and the navigation request. Each function is
//! proven equal to the spec function it names (see
//! [`crate::submit::contract`]).

use super::encode::*;
use super::strings::*;
#[cfg(verus_only)]
use crate::contract::*;
use crate::exec::entry::{ExecControl, ExecEntry, ascii_vec, copy_all};
#[cfg(verus_only)]
use crate::exec::entry::{entries_view, state_view};
use crate::exec::fields::construct_entry_list_exec;
use crate::exec::read::*;
use crate::exec::strings::{ci_eq_exec, eq_ascii};
use crate::exec::tree::tree_order_exec;
use crate::exec::walk::root_exec;
#[cfg(verus_only)]
use crate::lemmas::{lemma_in_order, lemma_root_facts};
use crate::spec::InputType;
#[cfg(verus_only)]
use crate::spec::*;
#[cfg(verus_only)]
use crate::submit::contract::*;
#[cfg(verus_only)]
use crate::submit::lemmas::*;
#[cfg(verus_only)]
use crate::submit::spec::*;
use crate::submit::spec::{
    Body, EnctypeState, MethodState, NavMethod, Navigation, Outcome, Refusal, Target,
};
use clazel_dom::exec::{Arena, ExecKind};
#[cfg(verus_only)]
use clazel_dom::lemmas::lemma_wf_witness;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
use clazel_encoding::labels::spec::Encoding;
use clazel_url::url::record::ParsedUrl;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Attribute states

/// [`method_of_value`].
pub fn method_of_value_exec(v: &[u32]) -> (r: MethodState)
    ensures
        method_of_value_ensures(v@, r),
{
    if ci_eq_exec(v, b"get") {
        MethodState::Get
    } else if ci_eq_exec(v, b"post") {
        MethodState::Post
    } else if ci_eq_exec(v, b"dialog") {
        MethodState::Dialog
    } else {
        MethodState::Get
    }
}

/// [`enctype_of_value`].
pub fn enctype_of_value_exec(v: &[u32]) -> (r: EnctypeState)
    ensures
        enctype_of_value_ensures(v@, r),
{
    if ci_eq_exec(v, b"application/x-www-form-urlencoded") {
        EnctypeState::UrlEncoded
    } else if ci_eq_exec(v, b"multipart/form-data") {
        EnctypeState::FormData
    } else if ci_eq_exec(v, b"text/plain") {
        EnctypeState::Text
    } else {
        EnctypeState::UrlEncoded
    }
}

/// [`is_submit_button`].
pub fn is_submit_button_exec(arena: &Arena, n: usize) -> (r: bool)
    requires
        dom::valid(arena@, n),
    ensures
        is_submit_button_ensures(arena@, n, r),
{
    if is_html_exec(arena, n, b"button") {
        proof {
            assert(is_element(arena@, n));
        }
        match attr_exec(arena, n, b"type") {
            None => true,
            Some(v) => !(ci_eq_exec(v.as_slice(), b"reset") || ci_eq_exec(v.as_slice(), b"button")),
        }
    } else if is_html_exec(arena, n, b"input") {
        proof {
            assert(is_element(arena@, n));
        }
        matches!(input_type_exec(arena, n), InputType::Submit | InputType::Image)
    } else {
        false
    }
}

/// [`submitter_action`].
pub fn submitter_action_exec(arena: &Arena, form: usize, submitter: usize) -> (r: Vec<u32>)
    requires
        attrs_requires(arena@, form, submitter),
    ensures
        submitter_action_ensures(arena@, form, submitter, r@),
{
    proof {
        assert(dom::valid(arena@, submitter));
    }
    let own = if is_submit_button_exec(arena, submitter) {
        attr_exec(arena, submitter, b"formaction")
    } else {
        None
    };
    if let Some(v) = own {
        return copy_all(v.as_slice());
    }
    match attr_exec(arena, form, b"action") {
        Some(v) => copy_all(v.as_slice()),
        None => Vec::new(),
    }
}

/// [`submitter_method`].
pub fn submitter_method_exec(arena: &Arena, form: usize, submitter: usize) -> (r: MethodState)
    requires
        attrs_requires(arena@, form, submitter),
    ensures
        submitter_method_ensures(arena@, form, submitter, r),
{
    proof {
        assert(dom::valid(arena@, submitter));
    }
    let own = if is_submit_button_exec(arena, submitter) {
        attr_exec(arena, submitter, b"formmethod")
    } else {
        None
    };
    if let Some(v) = own {
        return method_of_value_exec(v.as_slice());
    }
    match attr_exec(arena, form, b"method") {
        Some(v) => method_of_value_exec(v.as_slice()),
        None => MethodState::Get,
    }
}

/// [`submitter_enctype`].
pub fn submitter_enctype_exec(arena: &Arena, form: usize, submitter: usize) -> (r: EnctypeState)
    requires
        attrs_requires(arena@, form, submitter),
    ensures
        submitter_enctype_ensures(arena@, form, submitter, r),
{
    proof {
        assert(dom::valid(arena@, submitter));
    }
    let own = if is_submit_button_exec(arena, submitter) {
        attr_exec(arena, submitter, b"formenctype")
    } else {
        None
    };
    if let Some(v) = own {
        return enctype_of_value_exec(v.as_slice());
    }
    match attr_exec(arena, form, b"enctype") {
        Some(v) => enctype_of_value_exec(v.as_slice()),
        None => EnctypeState::UrlEncoded,
    }
}

// ---------------------------------------------------------------------
// Encoding selection

/// [`pick_encoding`]: HTML "picking an encoding for the form".
pub fn pick_encoding_exec(document_encoding: Encoding, accept_charset: Option<&Vec<u32>>) -> (r: Encoding)
    ensures
        pick_encoding_ensures(document_encoding, ref_view(accept_charset), r),
{
    match accept_charset {
        None => output_encoding_exec(document_encoding),
        Some(input) => {
            let labels = split_ws_exec(input.as_slice());
            let ghost iv = input@;
            proof {
                assert(tokens_view(labels@) == split_ws(iv));
            }
            let ghost lv = tokens_view(labels@);
            let mut i: usize = 0;
            proof {
                assert(lv.skip(0) =~= lv);
            }
            while i < labels.len()
                invariant
                    i <= labels.len(),
                    lv == tokens_view(labels@),
                    lv == split_ws(iv),
                    iv == input@,
                    accept_charset == Some(input),
                    candidate_encodings(lv) == candidate_encodings(lv.skip(i as int)),
                decreases labels.len() - i,
            {
                if let Some(l) = labels.get(i) {
                    proof {
                        assert(lv.skip(i as int).drop_first() =~= lv.skip(i as int + 1));
                        assert(lv.skip(i as int)[0] == lv[i as int]);
                        assert(lv[i as int] == labels@[i as int]@);
                    }
                    if let Some(e) = clazel_encoding::labels::exec::get_an_encoding(l.as_slice()) {
                        // The first candidate: 2.6 "Return the first
                        // encoding in candidate encodings."
                        proof {
                            lemma_candidates_first(lv.skip(i as int), e);
                            assert(lv == split_ws(iv));
                            assert(candidate_encodings(lv).len() > 0);
                            assert(candidate_encodings(lv)[0] == e);
                            assert(accept_charset == Some(input));
                            assert(ref_view(Some(input)) == Some(iv));
                            assert(pick_encoding(document_encoding, Some(iv)) == output_encoding(e));
                        }
                        return output_encoding_exec(e);
                    }
                }
                // Never saturates: i < labels.len().
                i = i.saturating_add(1);
            }
            proof {
                assert(lv.skip(labels.len() as int) =~= Seq::<Seq<u32>>::empty());
            }
            // 2.5 "If candidate encodings is empty, return UTF-8."
            Encoding::Utf8
        },
    }
}

// ---------------------------------------------------------------------
// Targets

/// The view of an optional string.
pub open spec fn opt_vec_view(o: Option<Vec<u32>>) -> Option<Seq<u32>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

/// [`first_base_target`].
pub fn first_base_target_exec(arena: &Arena, order: &[usize]) -> (r: Option<Vec<u32>>)
    requires
        first_base_target_requires(arena@, order@),
    ensures
        first_base_target_ensures(arena@, order@, opt_vec_view(r)),
{
    let ghost ord = order@;
    let mut i: usize = 0;
    proof {
        assert(ord.skip(0) =~= ord);
    }
    while i < order.len()
        invariant
            i <= order.len(),
            ord == order@,
            first_base_target_requires(arena@, ord),
            first_base_target(arena@, ord) == first_base_target(arena@, ord.skip(i as int)),
        decreases order.len() - i,
    {
        if let Some(n) = order.get(i) {
            let n = *n;
            proof {
                assert(ord.skip(i as int).drop_first() =~= ord.skip(i as int + 1));
                assert(ord.skip(i as int)[0] == ord[i as int]);
                assert(dom::valid(arena@, n));
            }
            if is_html_exec(arena, n, b"base") {
                proof {
                    assert(is_element(arena@, n));
                }
                if let Some(v) = attr_exec(arena, n, b"target") {
                    return Some(copy_all(v.as_slice()));
                }
            }
        }
        // Never saturates: i < order.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(ord.skip(order.len() as int) =~= Seq::<NodeId>::empty());
    }
    None
}

/// [`has_tab_newline`].
pub fn has_tab_newline_exec(s: &[u32]) -> (r: bool)
    ensures
        r == has_tab_newline(s@),
{
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            has_tab_newline(s@) == has_tab_newline(s@.skip(i as int)),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            proof {
                assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                assert(s@.skip(i as int)[0] == s@[i as int]);
            }
            if *c == 0x09 || *c == 0x0A || *c == 0x0D {
                return true;
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    false
}

/// [`has_lt`].
pub fn has_lt_exec(s: &[u32]) -> (r: bool)
    ensures
        r == has_lt(s@),
{
    let mut i: usize = 0;
    proof {
        assert(s@.skip(0) =~= s@);
    }
    while i < s.len()
        invariant
            i <= s.len(),
            has_lt(s@) == has_lt(s@.skip(i as int)),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            proof {
                assert(s@.skip(i as int).drop_first() =~= s@.skip(i as int + 1));
                assert(s@.skip(i as int)[0] == s@[i as int]);
            }
            if *c == 0x3C {
                return true;
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(s@.skip(s.len() as int) =~= Seq::<u32>::empty());
    }
    false
}

/// [`get_an_elements_target`]: HTML "get an element's target".
pub fn get_an_elements_target_exec(
    arena: &Arena,
    form: usize,
    target: Option<Vec<u32>>,
    base_target: Option<Vec<u32>>,
) -> (r: Option<Vec<u32>>)
    requires
        dom::wf(arena@),
        is_element(arena@, form),
    ensures
        get_an_elements_target_ensures(arena@, form, opt_vec_view(target), opt_vec_view(base_target), opt_vec_view(r)),
{
    // 1. "If target is null:"
    let target = match target {
        None => match attr_exec(arena, form, b"target") {
            // 1.1
            Some(v) => Some(copy_all(v.as_slice())),
            // 1.2
            None => base_target,
        },
        Some(t) => Some(t),
    };
    // 2., 3.
    match target {
        Some(t) => {
            if has_tab_newline_exec(t.as_slice()) && has_lt_exec(t.as_slice()) {
                Some(ascii_vec(b"_blank"))
            } else {
                Some(t)
            }
        },
        None => None,
    }
}

/// [`choose_navigable`].
pub fn choose_navigable_exec(target: &Option<Vec<u32>>) -> (r: Target)
    ensures
        choose_navigable_ensures(opt_vec_view(*target), r),
{
    match target {
        None => Target::ThisTab,
        Some(t) => {
            if t.is_empty() || ci_eq_exec(t.as_slice(), b"_self") || ci_eq_exec(t.as_slice(), b"_parent")
                || ci_eq_exec(t.as_slice(), b"_top") {
                Target::ThisTab
            } else {
                Target::NewTab
            }
        },
    }
}

// ---------------------------------------------------------------------
// The navigation request

/// A request body and its content type ([`Body`]).
pub struct ExecBody {
    /// The request body, bytes.
    pub bytes: Vec<u8>,
    /// The request content type.
    pub content_type: Vec<u8>,
}

impl View for ExecBody {
    type V = Body;

    open spec fn view(&self) -> Body {
        Body { bytes: self.bytes@, content_type: self.content_type@ }
    }
}

/// The view of an optional body.
pub open spec fn opt_body_view(b: Option<ExecBody>) -> Option<Body> {
    match b {
        Some(b) => Some(b@),
        None => None,
    }
}

/// A navigation request ([`Navigation`]): what the kernel sends.
pub struct ExecNavigation {
    /// The URL to navigate to.
    pub url: ParsedUrl,
    /// GET, or POST with a body.
    pub method: NavMethod,
    /// The POST resource.
    pub body: Option<ExecBody>,
    /// This tab or a new one.
    pub target: Target,
    /// The referrer policy is `no-referrer`.
    pub no_referrer: bool,
}

impl View for ExecNavigation {
    type V = Navigation;

    open spec fn view(&self) -> Navigation {
        Navigation {
            url: self.url@,
            method: self.method,
            body: opt_body_view(self.body),
            target: self.target,
            no_referrer: self.no_referrer,
        }
    }
}

/// The result of the form submission algorithm ([`Outcome`]).
pub enum ExecOutcome {
    /// The standard returns: nothing happens.
    Ignored,
    /// Not supported here.
    Refused(Refusal),
    /// Navigate.
    Navigate(Box<ExecNavigation>),
}

impl View for ExecOutcome {
    type V = Outcome;

    open spec fn view(&self) -> Outcome {
        match self {
            ExecOutcome::Ignored => Outcome::Ignored,
            ExecOutcome::Refused(r) => Outcome::Refused(*r),
            ExecOutcome::Navigate(n) => Outcome::Navigate((**n)@),
        }
    }
}

/// A navigation with no body.
fn nav_get(url: ParsedUrl, target: Target, no_referrer: bool) -> (r: ExecOutcome)
    ensures
        r@ == Outcome::Navigate(Navigation { url: url@, method: NavMethod::Get, body: None, target, no_referrer }),
{
    ExecOutcome::Navigate(Box::new(ExecNavigation { url, method: NavMethod::Get, body: None, target, no_referrer }))
}

/// [`mutate_action_url`]: "Mutate action URL", as a navigation.
fn mutate_exec(
    parsed: ParsedUrl,
    entry_list: &[ExecEntry],
    encoding: Encoding,
    target: Target,
    no_referrer: bool,
) -> (r: ExecOutcome)
    requires
        encodable(encoding),
        entries_scalar(entries_view(entry_list@)),
    ensures
        r@ == Outcome::Navigate(
            Navigation {
                url: mutate_action_url(parsed@, convert_to_pairs(entries_view(entry_list@)), encoding),
                method: NavMethod::Get,
                body: None,
                target,
                no_referrer,
            },
        ),
{
    let pairs = convert_to_pairs_exec(entry_list);
    proof {
        lemma_convert_scalar(entries_view(entry_list@));
        assert(output_encoding(encoding) == encoding);
    }
    let query = urlencoded_serialize_exec(pairs.as_slice(), encoding);
    let mut parsed = parsed;
    parsed.query = Some(query);
    nav_get(parsed, target, no_referrer)
}

/// [`entity_body`]: "Submit as entity body".
fn entity_body_exec(enctype: &EnctypeState, entry_list: &[ExecEntry], encoding: Encoding, boundary: &[u8]) -> (r: ExecBody)
    requires
        encodable(encoding),
        entries_scalar(entries_view(entry_list@)),
    ensures
        r@ == entity_body(*enctype, entries_view(entry_list@), encoding, boundary@),
{
    match enctype {
        EnctypeState::UrlEncoded => {
            let pairs = convert_to_pairs_exec(entry_list);
            proof {
                lemma_convert_scalar(entries_view(entry_list@));
                assert(output_encoding(encoding) == encoding);
            }
            let text = urlencoded_serialize_exec(pairs.as_slice(), encoding);
            proof {
                lemma_urlencoded_serialize_ascii(entries_view(pairs@), encoding);
            }
            let bytes = clazel_encoding::utf8::encode::encode(text.as_slice());
            let mut content_type: Vec<u8> = Vec::new();
            append8(&mut content_type, b"application/x-www-form-urlencoded");
            ExecBody { bytes, content_type }
        },
        EnctypeState::FormData => {
            let bytes = multipart_encode_exec(entry_list, encoding, boundary);
            let mut content_type: Vec<u8> = Vec::new();
            append8(&mut content_type, b"multipart/form-data; boundary=");
            append8(&mut content_type, boundary);
            ExecBody { bytes, content_type }
        },
        EnctypeState::Text => {
            let pairs = convert_to_pairs_exec(entry_list);
            proof {
                lemma_convert_scalar(entries_view(entry_list@));
            }
            let text = text_plain_encode_exec(pairs.as_slice());
            proof {
                lemma_text_plain_scalar(entries_view(pairs@));
            }
            let bytes = encode_with_exec(encoding, text.as_slice());
            let mut content_type: Vec<u8> = Vec::new();
            append8(&mut content_type, b"text/plain");
            ExecBody { bytes, content_type }
        },
    }
}

/// Steps 21 and 22: the submitter's `formtarget`, if it is a submit button
/// with one.
fn form_target_exec(arena: &Arena, submitter: usize, sb: bool) -> (r: Option<Vec<u32>>)
    requires
        is_element(arena@, submitter),
    ensures
        opt_vec_view(r) == (if sb {
            attr(arena@, submitter, b"formtarget"@)
        } else {
            None
        }),
{
    if !sb {
        return None;
    }
    let v = attr_exec(arena, submitter, b"formtarget")?;
    Some(copy_all(v.as_slice()))
}

/// Steps 13 on of the form submission algorithm ([`submit_from_method`]).
pub fn submit_from_method_exec(
    arena: &Arena,
    elements: (usize, usize),
    encoding: Encoding,
    entry_list: &[ExecEntry],
    document_url: &[u32],
    base_url: &ParsedUrl,
    boundary: &[u8],
) -> (r: ExecOutcome)
    requires
        attrs_requires(arena@, elements.0, elements.1),
        entries_scalar(entries_view(entry_list@)),
    ensures
        r@ == submit_from_method(
            arena@,
            elements.0,
            elements.1,
            encoding,
            entries_view(entry_list@),
            document_url@,
            base_url@,
            boundary@,
        ),
{
    let (form, submitter) = elements;
    proof {
        assert(dom::valid(arena@, form));
        assert(dom::valid(arena@, submitter));
    }
    // 13. "Let method be the submitter element's method."
    let method = submitter_method_exec(arena, form, submitter);
    // 14. "If method is dialog": refused.
    if let MethodState::Dialog = method {
        return ExecOutcome::Refused(Refusal::Dialog);
    }
    // 15., 16.
    let action0 = submitter_action_exec(arena, form, submitter);
    let action: Vec<u32> = if action0.is_empty() {
        copy_all(document_url)
    } else {
        action0
    };
    // 17. "encoding-parsing a URL given action"
    let input = to_scalar_exec(action.as_slice());
    proof {
        lemma_to_scalar_scalar(action@);
    }
    let parsed = match clazel_url::url::parse::basic_url_parser(input.as_slice(), Some(base_url)) {
        // 18. "If parsed action is failure, then return."
        None => {
            return ExecOutcome::Ignored;
        },
        Some(p) => p,
    };
    // 19., 20.
    let enctype = submitter_enctype_exec(arena, form, submitter);
    // 21. to 23.
    let sb = is_submit_button_exec(arena, submitter);
    let form_target: Option<Vec<u32>> = form_target_exec(arena, submitter, sb);
    let r0 = root_exec(arena, form);
    proof {
        let paths = lemma_wf_witness(arena@);
        lemma_root_facts(arena@, paths, form);
    }
    let order = tree_order_exec(arena, r0);
    proof {
        assert forall|k: int| 0 <= k < order@.len() implies dom::valid(arena@, #[trigger] order@[k]) by {
            lemma_in_order(arena@, form, order@[k]);
        }
    }
    let base_target = first_base_target_exec(arena, order.as_slice());
    let target = get_an_elements_target_exec(arena, form, form_target, base_target);
    let chosen = choose_navigable_exec(&target);
    let no_referrer = match attr_exec(arena, form, b"rel") {
        Some(rel) => {
            let toks = split_ws_exec(rel.as_slice());
            any_ci_exec(toks.as_slice(), b"noreferrer")
        },
        None => false,
    };
    // 29. the table.
    let is_get = matches!(method, MethodState::Get);
    let http = eq_ascii(parsed.scheme.as_slice(), b"http") || eq_ascii(parsed.scheme.as_slice(), b"https");
    let encodable_enc = is_encodable_exec(encoding);
    if http {
        if !encodable_enc {
            ExecOutcome::Refused(Refusal::UnsupportedEncoding)
        } else if is_get {
            mutate_exec(parsed, entry_list, encoding, chosen, no_referrer)
        } else if matches!(enctype, EnctypeState::FormData) && !wf_boundary_exec(boundary) {
            ExecOutcome::Refused(Refusal::BadBoundary)
        } else {
            let body = entity_body_exec(&enctype, entry_list, encoding, boundary);
            ExecOutcome::Navigate(Box::new(ExecNavigation { url: parsed, method: NavMethod::Post, body: Some(body), target: chosen, no_referrer }))
        }
    } else if eq_ascii(parsed.scheme.as_slice(), b"data") && is_get {
        if !encodable_enc {
            ExecOutcome::Refused(Refusal::UnsupportedEncoding)
        } else {
            mutate_exec(parsed, entry_list, encoding, chosen, no_referrer)
        }
    } else if eq_ascii(parsed.scheme.as_slice(), b"data") || eq_ascii(parsed.scheme.as_slice(), b"ftp") {
        nav_get(parsed, chosen, no_referrer)
    } else if eq_ascii(parsed.scheme.as_slice(), b"javascript") {
        ExecOutcome::Refused(Refusal::JavascriptScheme)
    } else if eq_ascii(parsed.scheme.as_slice(), b"mailto") {
        ExecOutcome::Refused(Refusal::MailtoScheme)
    } else {
        ExecOutcome::Refused(Refusal::UnlistedScheme)
    }
}

/// [`encodable`].
pub fn is_encodable_exec(e: Encoding) -> (r: bool)
    ensures
        r == encodable(e),
{
    match e {
        Encoding::Utf8 => true,
        _ => is_single_byte_exec(e),
    }
}

/// [`is_single_byte`] for an encoding, by its number in the table of §4.2.
pub fn is_single_byte_exec(e: Encoding) -> (r: bool)
    ensures
        r == clazel_encoding::single_byte::spec::is_single_byte(e),
{
    let n = clazel_encoding::labels::exec::number(e);
    (1..=28).contains(&n)
}

/// The form is connected: its root is a `Document`.
pub fn is_connected_exec(arena: &Arena, form: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, form),
    ensures
        r == (root(arena@, form) < arena@.nodes.len() && arena@.nodes[root(arena@, form) as int].kind is Document),
{
    let r0 = root_exec(arena, form);
    proof {
        let paths = lemma_wf_witness(arena@);
        lemma_root_facts(arena@, paths, form);
    }
    matches!(arena.kind(r0), ExecKind::Document { .. })
}

/// [`encoding_name`].
pub fn encoding_name_exec(e: Encoding) -> (r: Vec<u32>)
    ensures
        r@ == encoding_name(e),
{
    let name_bytes = clazel_encoding::labels::exec::name(e);
    let name = ascii_vec(name_bytes.as_slice());
    proof {
        assert(name@ == encoding_name(e));
    }
    name
}

/// [`submit`]: HTML "submit" a form from a submitter, from the standard's
/// step 9 on.
pub fn submit_exec(
    arena: &Arena,
    rows: &[ExecControl],
    elements: (usize, usize),
    document_encoding: Encoding,
    document_url: &[u32],
    base_url: &ParsedUrl,
    boundary: &[u8],
) -> (r: ExecOutcome)
    requires
        submit_requires(arena@, elements.0, elements.1),
    ensures
        submit_ensures(
            arena@,
            state_view(rows@),
            elements.0,
            elements.1,
            document_encoding,
            document_url@,
            base_url@,
            boundary@,
            r@,
        ),
{
    let (form, submitter) = elements;
    proof {
        assert(dom::valid(arena@, form));
        assert(dom::valid(arena@, submitter));
    }
    // 1. "If form cannot navigate, then return."
    if !is_connected_exec(arena, form) {
        return ExecOutcome::Ignored;
    }
    // 9. "Let encoding be the result of picking an encoding for the form."
    let encoding = pick_encoding_exec(document_encoding, attr_exec(arena, form, b"accept-charset"));
    // 10. "Let entry list be the result of constructing the entry list ..."
    let name = encoding_name_exec(encoding);
    match construct_entry_list_exec(arena, rows, form, Some(submitter), name.as_slice(), false) {
        None => ExecOutcome::Ignored,
        Some(list) => {
            let scalar = scalar_entries_exec(list.as_slice());
            proof {
                lemma_scalar_entries_scalar(entries_view(list@));
            }
            submit_from_method_exec(
                arena,
                (form, submitter),
                encoding,
                scalar.as_slice(),
                document_url,
                base_url,
                boundary,
            )
        },
    }
}

} // verus!
