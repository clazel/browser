//! What has activation behavior (DOM §2.9†), and what is focusable (HTML
//! §6.6.3†), over a `clazel-dom` arena.
//!
//! <https://html.spec.whatwg.org/multipage/dom.html#interactive-content>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit; steps are quoted by their words).
//!
//! Tier 0, not proven. The HTML reads of a form control (its `type`, whether
//! it is disabled, its form owner) are `clazel-forms`' proven functions.
//!
//! Modelling choices:
//! - **Which elements have activation behavior**: `a` with an `href` (HTML
//!   §4.6.1†, "follow the hyperlink"); `button` (§4.10.6†); `input` of the
//!   types submit, image, reset, checkbox and radio (§4.10.5.1†); `label`
//!   (§4.10.4†). `area`, `summary`, `details`, `select` and `option` do not
//!   have it here, and `input type=file`, `color` and the date types do
//!   nothing when clicked (they would open a picker).
//! - **A `button` of type `button`** has the behavior and does nothing; it
//!   counts, because a nearer activation target stops the search for an
//!   ancestor's.
//! - **Focusable** is decided from the markup alone: there is no rendering
//!   state here, so an element that is `display: none` or `visibility:
//!   hidden` is still focusable (HTML says it is not "being rendered").

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_forms::exec::entry::is_disabled_exec;
use clazel_forms::exec::read::{
    attr_exec, has_attr_exec, input_type_exec, is_element_exec, is_html_exec, is_submittable_exec,
};
use clazel_forms::spec::InputType;

use crate::scripting::dom;

/// What an element's activation behavior does.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// An `a` with an `href`: "follow the hyperlink".
    Hyperlink,
    /// A submit button: "submit the form owner from the element".
    Submit,
    /// A reset button: "reset the form owner".
    Reset,
    /// A checkbox: toggles, and fires `input` and `change`.
    Checkbox,
    /// A radio button: checks itself, and fires `input` and `change`.
    Radio,
    /// A `label`: clicks its labeled control.
    Label,
    /// A button that does nothing (`type=button`).
    Inert,
}

fn is_element(arena: &Arena, n: usize) -> bool {
    n < arena.len() && is_element_exec(arena, n)
}

/// An ASCII case-insensitive comparison with a lowercase keyword.
fn ci_is(v: &[u32], keyword: &str) -> bool {
    dom::eq_ignore_ascii_case(v, keyword)
}

/// The activation behavior `n` has, if any.
#[must_use]
pub fn kind_of(arena: &Arena, n: usize) -> Option<Kind> {
    if !is_element(arena, n) {
        return None;
    }
    if is_html_exec(arena, n, b"a") {
        return has_attr_exec(arena, n, b"href").then_some(Kind::Hyperlink);
    }
    if is_html_exec(arena, n, b"button") {
        return Some(match attr_exec(arena, n, b"type") {
            None => Kind::Submit,
            Some(v) if ci_is(v, "reset") => Kind::Reset,
            Some(v) if ci_is(v, "button") => Kind::Inert,
            Some(_) => Kind::Submit,
        });
    }
    if is_html_exec(arena, n, b"input") {
        return match input_type_exec(arena, n) {
            InputType::Submit | InputType::Image => Some(Kind::Submit),
            InputType::Reset => Some(Kind::Reset),
            InputType::Checkbox => Some(Kind::Checkbox),
            InputType::Radio => Some(Kind::Radio),
            _ => None,
        };
    }
    if is_html_exec(arena, n, b"label") {
        return Some(Kind::Label);
    }
    None
}

/// HTML §4.10.18.5†: "a form control that is disabled": a submittable
/// element with the `disabled` attribute, or under a disabled `fieldset`.
/// "A form control that is disabled must prevent any click events that are
/// targeted at it from being dispatched".
#[must_use]
pub fn is_disabled_control(arena: &Arena, n: usize) -> bool {
    is_element(arena, n) && is_submittable_exec(arena, n) && is_disabled_exec(arena, n)
}

/// The value of `n`'s attribute `name` as code points.
#[must_use]
pub fn attribute(arena: &Arena, n: usize, name: &str) -> Option<Vec<u32>> {
    match arena.kind(n) {
        ExecKind::Element { attributes, .. } if n < arena.len() => {
            dom::attribute(attributes, name).map(<[u32]>::to_vec)
        }
        _ => None,
    }
}

/// The attributes of an element.
fn attributes(arena: &Arena, n: usize) -> Option<&[ExecAttr]> {
    if n >= arena.len() {
        return None;
    }
    match arena.kind(n) {
        ExecKind::Element { attributes, .. } => Some(attributes),
        _ => None,
    }
}

/// HTML §2.4.4† "rules for parsing integers", for `tabindex`: optional ASCII
/// whitespace, an optional sign, digits; `None` if there are none.
fn parse_integer(v: &[u32]) -> Option<i64> {
    let v = dom::strip(v);
    let (neg, digits) = match v.first() {
        Some(0x2D) => (true, v.get(1..).unwrap_or(&[])),
        Some(0x2B) => (false, v.get(1..).unwrap_or(&[])),
        _ => (false, v),
    };
    let mut n: i64 = 0;
    let mut any = false;
    for &c in digits {
        if !(0x30..=0x39).contains(&c) {
            break;
        }
        any = true;
        n = n
            .saturating_mul(10)
            .saturating_add(i64::from(c.saturating_sub(0x30)));
    }
    any.then_some(if neg { n.saturating_neg() } else { n })
}

/// The element's `tabindex` content attribute, parsed (HTML §6.6.3†
/// "tabindex value"), if it has a valid one.
#[must_use]
pub fn tabindex(arena: &Arena, n: usize) -> Option<i64> {
    let a = attributes(arena, n)?;
    parse_integer(dom::attribute(a, "tabindex")?)
}

/// HTML §6.6.3† "focusable area", from the markup: "elements that have an
/// tabindex attribute" with a valid value; `a` with an `href`; `button`,
/// `input` (not `type=hidden`), `select` and `textarea` that are not
/// disabled. Only HTML elements; the body of a document is not focusable by
/// itself.
#[must_use]
pub fn is_focusable(arena: &Arena, n: usize) -> bool {
    if !is_element(arena, n) {
        return false;
    }
    if !matches!(
        arena.kind(n),
        ExecKind::Element {
            namespace: Some(Namespace::Html),
            ..
        }
    ) {
        return false;
    }
    if tabindex(arena, n).is_some() {
        return true;
    }
    if is_html_exec(arena, n, b"a") {
        return has_attr_exec(arena, n, b"href");
    }
    if is_html_exec(arena, n, b"input") {
        return !matches!(input_type_exec(arena, n), InputType::Hidden)
            && !is_disabled_control(arena, n);
    }
    if is_html_exec(arena, n, b"button")
        || is_html_exec(arena, n, b"select")
        || is_html_exec(arena, n, b"textarea")
    {
        return !is_disabled_control(arena, n);
    }
    false
}

/// Whether the focusable area is in "sequential focus navigation order": a
/// `tabindex` below zero takes it out (it can be focused by script and
/// click, not by Tab).
#[must_use]
pub fn in_tab_order(arena: &Arena, n: usize) -> bool {
    is_focusable(arena, n) && tabindex(arena, n).is_none_or(|t| t >= 0)
}

/// Whether `n` is an `input` or `textarea` that takes typed text (the text
/// controls: input types text, search, tel, url, email, password and the
/// ones read as text, and `textarea`), and is not disabled.
#[must_use]
pub fn is_text_control(arena: &Arena, n: usize) -> bool {
    if !is_element(arena, n) || is_disabled_control(arena, n) {
        return false;
    }
    if is_html_exec(arena, n, b"textarea") {
        return true;
    }
    is_html_exec(arena, n, b"input")
        && matches!(
            input_type_exec(arena, n),
            InputType::Text
                | InputType::Search
                | InputType::Tel
                | InputType::Url
                | InputType::Email
                | InputType::Password
                | InputType::Other
        )
}

/// The nodes of the document in tree order (an iterative walk bounded by the
/// arena's size).
#[must_use]
pub fn tree_order(arena: &Arena) -> Vec<usize> {
    let mut out = Vec::new();
    let mut stack: Vec<usize> = vec![0];
    let mut budget = arena.len().saturating_mul(2).saturating_add(1);
    while let Some(id) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget = budget.saturating_sub(1);
        if id >= arena.len() {
            continue;
        }
        out.push(id);
        stack.extend(arena.children(id).iter().rev());
    }
    out
}
