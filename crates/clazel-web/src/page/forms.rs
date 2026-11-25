//! Activation behaviors and default actions of the elements (item 7.14):
//! following a link (HTML §7.4.2.?†, "follow the hyperlink"), submitting and
//! resetting a form (§4.10.21.3†, §4.10.21.4†), toggling a checkbox or radio
//! button (§4.10.5.1.15†, §4.10.5.1.16†), clicking a label's control
//! (§4.10.4†), and the typing that changes a text control's value.
//!
//! <https://html.spec.whatwg.org/multipage/form-control-infrastructure.html#form-submission-algorithm>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit; steps are quoted by their words).
//!
//! Tier 0, not proven. The form submission algorithm from its step 9, the
//! entry list and the encodings are `clazel-forms`' proven functions
//! (`submit_exec`); what is here is the algorithm's start (events, the
//! "cannot navigate" rule) and its end (handing the navigation to the
//! hooks).
//!
//! Modelling choices (each also in the README):
//! - **Constraint validation is not run** ("If the submitter element's no
//!   validate state is false, then interactively validate the constraints"):
//!   there is no validation UI, and `checkValidity` is not exposed; a form
//!   always submits.
//! - **`submit` is a plain `Event`**, bubbling and cancelable. The standard's
//!   `SubmitEvent` (with `submitter`) is not exposed.
//! - **The navigation** is `Navigate` for a `GET` (the kernel's message has a
//!   URL only) and `Submit` for a `POST`; a form whose `target` names another
//!   browsing context navigates this tab (there is no `OpenTab` before item
//!   7.16). `javascript:`, `mailto:` and `dialog` actions are refused by
//!   `submit_exec` and do nothing.
//! - **A `label`'s click** goes to its labeled control as a synthetic
//!   (untrusted) `click`, as HTML §4.10.4† says.

use clazel_dom::exec::Arena;
use clazel_encoding::labels::spec::Encoding;
use clazel_forms::exec::controls::controls_exec;
use clazel_forms::exec::entry::{
    ExecControl, checkedness_exec, input_value_exec, textarea_raw_exec,
};
use clazel_forms::exec::read::{attr_exec, input_type_exec, is_html_exec};
use clazel_forms::exec::walk::nearest_form_exec;
use clazel_forms::spec::InputType;
use clazel_forms::submit::exec::submit::{ExecOutcome, is_connected_exec, submit_exec};
use clazel_forms::submit::spec::NavMethod;
use clazel_js::{Result, Scope};

use super::event::fire_with;
use super::{HookCall, Page, page};
use crate::activation::{self, Kind};
use crate::events::{EventInit, TargetId};
use crate::scripting::dom;
use crate::ui::PreActivation;

fn clean_row() -> ExecControl {
    ExecControl {
        value: Vec::new(),
        dirty_value: false,
        checked: false,
        dirty_checked: false,
        selected: false,
        x: 0,
        y: 0,
    }
}

/// Grows the control state table to one row per node of the arena.
pub(crate) fn ensure_rows(p: &mut Page) {
    while p.ui.controls.len() < p.arena.len() {
        p.ui.controls.push(clean_row());
    }
}

/// HTML "checkedness" of the `input` `n`.
pub(crate) fn is_checked(p: &mut Page, n: usize) -> bool {
    ensure_rows(p);
    checkedness_exec(&p.arena, &p.ui.controls, n)
}

/// The current "value" of the text control `n`: a `textarea`'s raw value or
/// an `input`'s sanitized value, as code points.
pub(crate) fn control_value(p: &mut Page, n: usize) -> Vec<u32> {
    ensure_rows(p);
    if is_html_exec(&p.arena, n, b"textarea") {
        textarea_raw_exec(&p.arena, &p.ui.controls, n)
    } else {
        input_value_exec(&p.arena, &p.ui.controls, n)
    }
}

/// Sets the value of the text control `n`: "set the value ... and set the
/// dirty value flag".
pub(crate) fn set_control_value(p: &mut Page, n: usize, value: Vec<u32>) {
    ensure_rows(p);
    if let Some(row) = p.ui.controls.get_mut(n) {
        row.value = value;
        row.dirty_value = true;
    }
}

/// The radio buttons of `n`'s "radio button group" other than `n`: the
/// `input` radios with the same non-empty `name`, in the same form (or both
/// outside every form and in the same tree).
fn radio_group(arena: &Arena, n: usize) -> Vec<usize> {
    let Some(name) = attr_exec(arena, n, b"name").cloned() else {
        return Vec::new();
    };
    if name.is_empty() {
        return Vec::new();
    }
    let owner = nearest_form_exec(arena, n);
    let mut root = n;
    while let Some(p) = arena.parent(root) {
        root = p;
    }
    let mut out = Vec::new();
    for m in activation::tree_order(arena) {
        if m == n || !is_html_exec(arena, m, b"input") {
            continue;
        }
        if !matches!(input_type_exec(arena, m), InputType::Radio) {
            continue;
        }
        if attr_exec(arena, m, b"name") != Some(&name) {
            continue;
        }
        if nearest_form_exec(arena, m) != owner {
            continue;
        }
        let mut r = m;
        while let Some(p) = arena.parent(r) {
            r = p;
        }
        if r == root {
            out.push(m);
        }
    }
    out
}

/// HTML "legacy-pre-activation behavior" of a checkbox ("set its checkedness
/// to its opposite value ... and set the element's indeterminate IDL
/// attribute to false") or a radio button ("set the element's checkedness to
/// true", and uncheck the group), saving what is needed to restore.
pub(crate) fn legacy_pre_activation(p: &mut Page, n: usize) {
    ensure_rows(p);
    let kind = activation::kind_of(&p.arena, n);
    let checked = is_checked(p, n);
    let dirty_checked = p.ui.controls.get(n).is_some_and(|r| r.dirty_checked);
    let mut previous = None;
    match kind {
        Some(Kind::Checkbox) => {
            if let Some(r) = p.ui.controls.get_mut(n) {
                r.checked = !checked;
                r.dirty_checked = true;
            }
        }
        Some(Kind::Radio) => {
            for m in radio_group(&p.arena, n) {
                if is_checked(p, m) {
                    let d = p.ui.controls.get(m).is_some_and(|r| r.dirty_checked);
                    previous = Some((m, d));
                    if let Some(r) = p.ui.controls.get_mut(m) {
                        r.checked = false;
                        r.dirty_checked = true;
                    }
                }
            }
            if let Some(r) = p.ui.controls.get_mut(n) {
                r.checked = true;
                r.dirty_checked = true;
            }
        }
        _ => return,
    }
    p.ui.pre_activation = Some(PreActivation {
        element: n,
        checked,
        dirty_checked,
        previous,
    });
}

/// HTML "legacy-canceled-activation behavior": "set the element's checkedness
/// ... back to the values they had before the legacy-pre-activation behavior
/// was run" (and, for a radio, re-check the one that was).
pub(crate) fn legacy_canceled_activation(p: &mut Page, n: usize) {
    let Some(saved) = p.ui.pre_activation.take() else {
        return;
    };
    if saved.element != n {
        return;
    }
    ensure_rows(p);
    if let Some(r) = p.ui.controls.get_mut(n) {
        r.checked = saved.checked;
        r.dirty_checked = saved.dirty_checked;
    }
    if let Some((m, _)) = saved.previous
        && let Some(r) = p.ui.controls.get_mut(m)
    {
        r.checked = true;
    }
}

/// The element `label` is for: HTML §4.10.4† "labeled control": the element
/// whose `id` is the `for` attribute, if it is labelable; else the first
/// labelable descendant.
pub(crate) fn labeled_control(arena: &Arena, label: usize) -> Option<usize> {
    let labelable = |m: usize| {
        is_html_exec(arena, m, b"input") && !matches!(input_type_exec(arena, m), InputType::Hidden)
            || is_html_exec(arena, m, b"button")
            || is_html_exec(arena, m, b"select")
            || is_html_exec(arena, m, b"textarea")
    };
    if let Some(id) = attr_exec(arena, label, b"for").cloned() {
        return activation::tree_order(arena).into_iter().find(|&m| {
            labelable(m)
                && attr_exec(arena, m, b"id") == Some(&id)
                && dom::is_connected(arena, label) == dom::is_connected(arena, m)
        });
    }
    let mut stack: Vec<usize> = arena.children(label).iter().rev().copied().collect();
    let mut budget = arena.len();
    while let Some(m) = stack.pop() {
        if budget == 0 {
            break;
        }
        budget = budget.saturating_sub(1);
        if m >= arena.len() {
            continue;
        }
        if labelable(m) {
            return Some(m);
        }
        stack.extend(arena.children(m).iter().rev());
    }
    None
}

/// Runs the activation behavior of `n` for the click `event_target` (DOM
/// §2.9† "run activationTarget's activation behavior with event").
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn activation_behavior(
    scope: &mut Scope<'_>,
    n: usize,
    event_target: Option<usize>,
) -> Result<()> {
    let kind = activation::kind_of(&page(scope)?.arena, n);
    match kind {
        Some(Kind::Hyperlink) => follow_hyperlink(scope, n),
        Some(Kind::Submit) => {
            let p = page(scope)?;
            if activation::is_disabled_control(&p.arena, n) {
                return Ok(());
            }
            // "If element's form owner is null, return." (The form owner is
            // the nearest form ancestor here; the `form` attribute is the
            // control's own business in `clazel-forms`' entry list.)
            let owner = form_owner(&p.arena, n);
            match owner {
                Some(form) => submit_form(scope, form, n, true),
                None => Ok(()),
            }
        }
        Some(Kind::Reset) => {
            let p = page(scope)?;
            if activation::is_disabled_control(&p.arena, n) {
                return Ok(());
            }
            match form_owner(&p.arena, n) {
                Some(form) => reset_form(scope, form),
                None => Ok(()),
            }
        }
        Some(Kind::Checkbox | Kind::Radio) => {
            // "If the element is not connected, then return. Fire an event
            // named input at the element with the bubbles and composed
            // attributes initialized to true. Fire an event named change at
            // the element with the bubbles attribute initialized to true."
            let p = page(scope)?;
            if !dom::is_connected(&p.arena, n) {
                return Ok(());
            }
            fire_with(
                scope,
                TargetId::Node(n),
                "input",
                EventInit {
                    bubbles: true,
                    cancelable: false,
                    composed: true,
                },
            )?;
            fire_with(
                scope,
                TargetId::Node(n),
                "change",
                EventInit {
                    bubbles: true,
                    cancelable: false,
                    composed: false,
                },
            )?;
            Ok(())
        }
        Some(Kind::Label) => {
            let p = page(scope)?;
            let Some(control) = labeled_control(&p.arena, n) else {
                return Ok(());
            };
            // "If the event's target is the labeled control or inside it,
            // do nothing" (the click reached the control already).
            if let Some(t) = event_target {
                let mut cur = Some(t);
                for _ in 0..=p.arena.len() {
                    match cur {
                        Some(c) if c == control => return Ok(()),
                        Some(c) => cur = p.arena.parent(c),
                        None => break,
                    }
                }
            }
            super::input::synthetic_click(scope, control)
        }
        Some(Kind::Inert) | None => Ok(()),
    }
}

/// The form owner of a button or control: its nearest `form` ancestor.
pub(crate) fn form_owner(arena: &Arena, n: usize) -> Option<usize> {
    nearest_form_exec(arena, n)
}

/// HTML §7.4.2.?† "follow the hyperlink" for the `a` element `n`: parse its
/// `href` against the document base URL and navigate (this tab; see the
/// module's modelling choices). A `javascript:` URL goes to the hooks like
/// any other: the renderer runs it in the page (HTML "navigate").
fn follow_hyperlink(scope: &mut Scope<'_>, n: usize) -> Result<()> {
    let p = page(scope)?;
    let Some(href) = attr_exec(&p.arena, n, b"href").cloned() else {
        return Ok(());
    };
    // "Let url be the result of parsing href relative to the element's node
    // document" (HTML §2.5.? "parse a URL"); "If url is failure, return."
    let base = dom::document_base_url(&p.arena);
    let Some(url) = dom::parse_url(&href, base.as_ref()) else {
        return Ok(());
    };
    let url = dom::serialize(&url);
    p.record(HookCall::Navigate {
        url,
        replace: false,
    });
    Ok(())
}

/// HTML §4.10.21.4† "reset": "fire an event named reset at form, with the
/// bubbles and cancelable attributes initialized to true. If the event is
/// not canceled, then reset each resettable element": the dynamic state of
/// every control owned by the form is dropped, so each is at its default.
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn reset_form(scope: &mut Scope<'_>, form: usize) -> Result<()> {
    let ok = fire_with(
        scope,
        TargetId::Node(form),
        "reset",
        EventInit {
            bubbles: true,
            cancelable: true,
            composed: false,
        },
    )?;
    if !ok {
        return Ok(());
    }
    let p = page(scope)?;
    ensure_rows(p);
    if form >= p.arena.len() {
        return Ok(());
    }
    for c in controls_exec(&p.arena, form) {
        if let Some(r) = p.ui.controls.get_mut(c) {
            *r = clean_row();
        }
    }
    Ok(())
}

/// HTML §4.10.21.3† "submit": "If form cannot navigate, then return. If
/// form's firing submission events is true, then return. Set form's firing
/// submission events to true. ... If submitted from submit() method is not
/// set, then fire an event named submit at form with bubbles and cancelable
/// true ...; if the event was canceled, return", then, from step 9, the
/// algorithm of `clazel-forms`. `fire_event` false is `form.submit()`.
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn submit_form(
    scope: &mut Scope<'_>,
    form: usize,
    submitter: usize,
    fire_event: bool,
) -> Result<()> {
    {
        let p = page(scope)?;
        // "If form cannot navigate": "form is not connected".
        if form >= p.arena.len() || !is_connected_exec(&p.arena, form) {
            return Ok(());
        }
    }
    if fire_event {
        let ok = fire_with(
            scope,
            TargetId::Node(form),
            "submit",
            EventInit {
                bubbles: true,
                cancelable: true,
                composed: false,
            },
        )?;
        if !ok {
            return Ok(());
        }
    }
    let encoding = crate::scripting::state::state(scope)
        .map(|s| s.encoding)
        .unwrap_or(Encoding::Utf8);
    let p = page(scope)?;
    if form >= p.arena.len() || submitter >= p.arena.len() {
        return Ok(());
    }
    ensure_rows(p);
    let Some(base) = dom::document_base_url(&p.arena) else {
        return Ok(());
    };
    let document_url = dom::document_url(&p.arena);
    // A boundary of `bchar`s the page cannot predict: the page's own
    // xorshift state, 16 hex digits.
    p.random ^= p.random.wrapping_shl(13);
    p.random ^= p.random.wrapping_shr(7);
    p.random ^= p.random.wrapping_shl(17);
    let boundary = format!("----ClazelFormBoundary{:016x}", p.random);
    let outcome = submit_exec(
        &p.arena,
        &p.ui.controls,
        (form, submitter),
        encoding,
        &document_url,
        &base,
        boundary.as_bytes(),
    );
    let ExecOutcome::Navigate(nav) = outcome else {
        return Ok(());
    };
    let url = dom::serialize(&nav.url);
    match (nav.method, nav.body) {
        (NavMethod::Post, Some(body)) => p.record(HookCall::Submit {
            url,
            method: "POST".to_owned(),
            content_type: String::from_utf8_lossy(&body.content_type).into_owned(),
            body: body.bytes,
        }),
        _ => p.record(HookCall::Navigate {
            url,
            replace: false,
        }),
    }
    Ok(())
}
