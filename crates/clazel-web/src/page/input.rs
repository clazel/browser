//! The user's input as events (phase-7.md item 7.14): a click, a key, a
//! wheel turn and a scroll become UI events at the element they hit or the
//! element that has focus, with the default actions they have when no
//! listener cancels them.
//!
//! <https://w3c.github.io/uievents/#events-mouse-types> and
//! <https://html.spec.whatwg.org/multipage/interaction.html#focus>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit; steps are quoted by their words).
//!
//! Tier 0, not proven. The embedder decides what an input hits (hit testing
//! is layout's, and `clazel-web` has no layout): it passes the node id.
//!
//! Event order and default actions, as the standards and browsers have them:
//! - **A click** is `mousemove`, `mousedown`, `mouseup`, `click`, all at the
//!   hit element, all trusted. `mousedown` is an "activation triggering
//!   input event": the page's user activation is notified before it is
//!   dispatched (so its listeners, and the click's, see it, as browsers
//!   do). Unless `mousedown` is canceled, its default action moves focus to
//!   the nearest focusable ancestor-or-self, or removes it. `click`'s
//!   default actions are the target's (or an ancestor's) activation
//!   behavior ([`crate::activation`]). A control that is disabled gets no
//!   mouse events at all.
//! - **A key** is `keydown`, then (if not canceled, for a character) `keypress`
//!   and the text input (`beforeinput`, the change, `input`), then `keyup`.
//!   `keydown`'s default actions: Tab and Shift-Tab move focus in sequential
//!   focus navigation order; Enter on a link, a button or a checkbox
//!   clicks it, in a text input implicitly submits its form (HTML
//!   §4.10.21.2†) and in a `textarea` inserts a line break; Backspace deletes
//!   the last character of a text control. Space on a button or a
//!   checkbox clicks it at `keyup`.
//! - **Text editing is the end of the value only**: there is no caret or
//!   selection, so typing appends and Backspace removes the last code point.
//!   Listed in the README.
//! - **A wheel turn** is a cancelable `wheel` event; what its default action
//!   does (scroll) is the renderer's, which asks whether it was canceled.
//!
//! The `focus` and `blur` events do not bubble, `focusin` and `focusout` do;
//! the order for moving focus is `blur`, `focusout` (at the old element),
//! `focus`, `focusin` (at the new one), as HTML's "focus update steps" and
//! the browsers have it.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_forms::exec::read::{input_type_exec, is_html_exec};
use clazel_forms::spec::InputType;
use clazel_js::{Result, Scope};
use clazel_webidl::generated::bindings::*;
use clazel_webidl::platform::ObjectKey;

use super::event::{dispatch, fire_with};
use super::ui_events::{clock_ms, create};
use super::{Page, page, points_to_units};
use crate::activation::{self, Kind};
use crate::events::{EventInit, TargetId};
use crate::ui::{Modifiers, UiData};

/// A mouse input: where it is and what it hit.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct MouseInput {
    /// The element the pointer is over (hit testing is the embedder's).
    pub target: usize,
    /// The position in the viewport, in CSS pixels.
    pub client_x: i32,
    /// See `client_x`.
    pub client_y: i32,
    /// The position on the screen (the page does not know it: the viewport's
    /// origin is taken for the screen's).
    pub screen_x: i32,
    /// See `screen_x`.
    pub screen_y: i32,
    /// `button`: 0 the main button.
    pub button: i16,
    /// The modifier keys held.
    pub mods: Modifiers,
}

/// A key input.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct KeyInput {
    /// `KeyboardEvent.key`: the character typed, or a key name ("Enter",
    /// "Backspace", "Tab", "Escape", "ArrowUp", ...).
    pub key: String,
    /// `KeyboardEvent.code`: the physical key, "" if the host does not know.
    pub code: String,
    /// The modifier keys held.
    pub mods: Modifiers,
    /// `repeat`: an auto-repeat of a key held down.
    pub repeat: bool,
}

/// A wheel input.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct WheelInput {
    /// The element under the pointer.
    pub target: usize,
    /// The position in the viewport, in CSS pixels.
    pub client_x: i32,
    /// See `client_x`.
    pub client_y: i32,
    /// `deltaX`
    pub delta_x: f64,
    /// `deltaY`
    pub delta_y: f64,
    /// `deltaMode` (0 pixels, 1 lines, 2 pages).
    pub delta_mode: u32,
    /// The modifier keys held.
    pub mods: Modifiers,
}

/// The element of the node `n` an input hits: `n` if it is an element, else
/// its parent (a text node is hit as its element is).
fn element_of(arena: &Arena, n: usize) -> Option<usize> {
    let mut cur = n;
    for _ in 0..=arena.len() {
        if cur >= arena.len() {
            return None;
        }
        if matches!(arena.kind(cur), ExecKind::Element { .. }) {
            return Some(cur);
        }
        cur = arena.parent(cur)?;
    }
    None
}

/// "The body element, or the document element if there is none" (the
/// default target of a key event: HTML §6.6.4† "the document's focused area
/// ... or the body").
fn body_or_root(arena: &Arena) -> Option<usize> {
    let root = arena
        .children(0)
        .iter()
        .copied()
        .find(|&c| c < arena.len() && matches!(arena.kind(c), ExecKind::Element { .. }))?;
    arena
        .children(root)
        .iter()
        .copied()
        .find(|&c| is_html_exec(arena, c, b"body") || is_html_exec(arena, c, b"frameset"))
        .or(Some(root))
}

/// Dispatches a trusted `interface` event named `type_` at `target`, and
/// forgets the event object if script did not take hold of it. Returns false
/// if it was canceled.
fn fire_ui(
    scope: &mut Scope<'_>,
    target: TargetId,
    interface: InterfaceId,
    type_: &str,
    init: EventInit,
    data: UiData,
) -> Result<bool> {
    let key = create(scope, interface, type_, init, data, true)?;
    let result = dispatch(scope, target, key);
    discard(scope, key);
    result
}

/// Drops an event object nothing refers to any more: one script never got a
/// wrapper of (a wrapper keeps the object alive for as long as the realm).
fn discard(scope: &mut Scope<'_>, key: ObjectKey) {
    if let Ok(p) = page(scope)
        && !p.other_wrappers.contains_key(&key)
        && let Some(id) = Page::object_id(key)
    {
        p.objects.remove(&id);
        p.ui.events.remove(&id);
    }
}

const BUBBLING: EventInit = EventInit {
    bubbles: true,
    cancelable: true,
    composed: true,
};

fn mouse_data(m: &MouseInput, buttons: u16, detail: i32) -> UiData {
    UiData {
        view: true,
        detail,
        which: u32::try_from(m.button.saturating_add(1)).unwrap_or(0),
        mods: m.mods,
        screen_x: m.screen_x,
        screen_y: m.screen_y,
        client_x: m.client_x,
        client_y: m.client_y,
        button: m.button,
        buttons,
        ..UiData::default()
    }
}

/// UI Events §5.2† a trusted mouse event named `type_` at `target`.
fn fire_mouse(
    scope: &mut Scope<'_>,
    target: usize,
    type_: &str,
    m: &MouseInput,
    buttons: u16,
    detail: i32,
) -> Result<bool> {
    fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::MouseEvent,
        type_,
        BUBBLING,
        mouse_data(m, buttons, detail),
    )
}

/// Notifies the window's user activation (HTML §6.4.2† "activation
/// notification") now.
fn notify_activation(scope: &mut Scope<'_>) -> Result<()> {
    let now = clock_ms(scope)?;
    page(scope)?.ui.activation.notify(now);
    Ok(())
}

/// A click of the user on `input.target`: see the module's order.
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn click(scope: &mut Scope<'_>, input: &MouseInput) -> Result<()> {
    let Some(target) = element_of(&page(scope)?.arena, input.target) else {
        return Ok(());
    };
    // "A form control that is disabled must prevent any click events that
    // are targeted at it from being dispatched": as browsers do, no mouse
    // event reaches it.
    if activation::is_disabled_control(&page(scope)?.arena, target) {
        return Ok(());
    }
    fire_mouse(scope, target, "mousemove", input, 0, 0)?;
    // "mousedown" is an activation triggering input event.
    notify_activation(scope)?;
    let down = fire_mouse(scope, target, "mousedown", input, 1, 1)?;
    page(scope)?.ui.pressed = Some(target);
    // The default action of mousedown: "focus the nearest focusable
    // ancestor, or the viewport".
    if down {
        let focusable = {
            let arena = &page(scope)?.arena;
            let mut cur = Some(target);
            let mut found = None;
            for _ in 0..=arena.len() {
                match cur {
                    Some(c) if activation::is_focusable(arena, c) => {
                        found = Some(c);
                        break;
                    }
                    Some(c) => cur = arena.parent(c),
                    None => break,
                }
            }
            found
        };
        set_focus(scope, focusable)?;
    }
    fire_mouse(scope, target, "mouseup", input, 0, 1)?;
    // "click": mousedown and mouseup were at the same element.
    if page(scope)?.ui.pressed.take() == Some(target) {
        fire_mouse(scope, target, "click", input, 0, 1)?;
    }
    Ok(())
}

/// A trusted `click` at `element` with no pointer (a key made it, or
/// another element's activation forwarded it): `detail` 0.
fn key_click(scope: &mut Scope<'_>, element: usize) -> Result<()> {
    let m = MouseInput {
        target: element,
        ..MouseInput::default()
    };
    fire_mouse(scope, element, "click", &m, 0, 0)?;
    Ok(())
}

/// HTML §3.2.6.? `click()`: "If this element is a form control that is
/// disabled, then return. If this element's click in progress flag is set,
/// then return. Set this element's click in progress flag. Fire a synthetic
/// pointer event named click at this element, with the not trusted flag
/// set. Unset this element's click in progress flag."
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn synthetic_click(scope: &mut Scope<'_>, element: usize) -> Result<()> {
    {
        let p = page(scope)?;
        if element >= p.arena.len()
            || activation::is_disabled_control(&p.arena, element)
            || p.ui.click_in_progress.contains(&element)
        {
            return Ok(());
        }
        p.ui.click_in_progress.push(element);
    }
    let key = create(
        scope,
        InterfaceId::MouseEvent,
        "click",
        BUBBLING,
        UiData {
            view: true,
            ..UiData::default()
        },
        false,
    )?;
    let r = dispatch(scope, TargetId::Node(element), key);
    discard(scope, key);
    page(scope)?.ui.click_in_progress.retain(|&e| e != element);
    r.map(|_| ())
}

// ---- Focus ----------------------------------------------------------------

/// The focused element, if there is one.
pub(crate) fn focused(scope: &mut Scope<'_>) -> Result<Option<usize>> {
    Ok(page(scope)?.ui.focused)
}

/// HTML §6.6.4† "focus update steps", for one document: moves the focus to
/// `new` (`None`: nothing). The `change` event of a text control whose value
/// changed since it was focused is fired first ("when the element loses
/// focus"); then `blur` and `focusout` at the old, `focus` and `focusin` at
/// the new. Does nothing if `new` is not focusable or already focused.
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn set_focus(scope: &mut Scope<'_>, new: Option<usize>) -> Result<()> {
    let old = {
        let p = page(scope)?;
        if let Some(n) = new
            && !activation::is_focusable(&p.arena, n)
        {
            return Ok(());
        }
        if p.ui.focused == new {
            return Ok(());
        }
        p.ui.focused
    };
    if let Some(o) = old {
        let changed = {
            let p = page(scope)?;
            let before = p.ui.value_at_focus.take();
            before.is_some_and(|b| {
                activation::is_text_control(&p.arena, o) && super::forms::control_value(p, o) != b
            })
        };
        if changed {
            fire_with(
                scope,
                TargetId::Node(o),
                "change",
                EventInit {
                    bubbles: true,
                    cancelable: false,
                    composed: false,
                },
            )?;
        }
        page(scope)?.ui.focused = None;
        focus_event(scope, o, "blur", false, new)?;
        focus_event(scope, o, "focusout", true, new)?;
    }
    if let Some(n) = new {
        let p = page(scope)?;
        p.ui.focused = Some(n);
        p.ui.value_at_focus =
            activation::is_text_control(&p.arena, n).then(|| super::forms::control_value(p, n));
        focus_event(scope, n, "focus", false, old)?;
        focus_event(scope, n, "focusin", true, old)?;
    }
    Ok(())
}

fn focus_event(
    scope: &mut Scope<'_>,
    target: usize,
    type_: &str,
    bubbles: bool,
    related: Option<usize>,
) -> Result<()> {
    fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::FocusEvent,
        type_,
        EventInit {
            bubbles,
            cancelable: false,
            composed: true,
        },
        UiData {
            view: true,
            related_target: related.map(TargetId::Node),
            ..UiData::default()
        },
    )?;
    Ok(())
}

/// HTML §6.6.5† sequential focus navigation: the element after (or before,
/// with `backwards`) the focused one, wrapping: those with a positive
/// `tabindex` in increasing order, then the others in tree order.
fn next_in_tab_order(arena: &Arena, from: Option<usize>, backwards: bool) -> Option<usize> {
    let all: Vec<usize> = activation::tree_order(arena)
        .into_iter()
        .filter(|&n| activation::in_tab_order(arena, n))
        .collect();
    let mut ordered: Vec<usize> = all
        .iter()
        .copied()
        .filter(|&n| activation::tabindex(arena, n).is_some_and(|t| t > 0))
        .collect();
    ordered.sort_by_key(|&n| activation::tabindex(arena, n).unwrap_or(0));
    ordered.extend(
        all.iter()
            .copied()
            .filter(|&n| activation::tabindex(arena, n).is_none_or(|t| t == 0)),
    );
    if ordered.is_empty() {
        return None;
    }
    let pos = from.and_then(|f| ordered.iter().position(|&n| n == f));
    let len = ordered.len();
    let next = match (pos, backwards) {
        (Some(i), false) => i.saturating_add(1).checked_rem(len).unwrap_or(0),
        (Some(i), true) => i.checked_sub(1).unwrap_or(len.saturating_sub(1)),
        (None, false) => 0,
        (None, true) => len.saturating_sub(1),
    };
    ordered.get(next).copied()
}

// ---- Keys -----------------------------------------------------------------

/// The legacy `keyCode` of a key (the values browsers give for the keys the
/// renderer can send).
fn key_code_of(key: &str) -> u32 {
    match key {
        "Backspace" => 8,
        "Tab" => 9,
        "Enter" => 13,
        "Shift" => 16,
        "Control" => 17,
        "Alt" => 18,
        "Escape" => 27,
        " " => 32,
        "PageUp" => 33,
        "PageDown" => 34,
        "End" => 35,
        "Home" => 36,
        "ArrowLeft" => 37,
        "ArrowUp" => 38,
        "ArrowRight" => 39,
        "ArrowDown" => 40,
        "Delete" => 46,
        k => {
            let mut cs = k.chars();
            match (cs.next(), cs.next()) {
                (Some(c), None) if c.is_ascii_alphabetic() => u32::from(c.to_ascii_uppercase()),
                (Some(c), None) if c.is_ascii_digit() => u32::from(c),
                _ => 0,
            }
        }
    }
}

fn key_data(k: &KeyInput) -> UiData {
    let key_code = key_code_of(&k.key);
    UiData {
        view: true,
        which: key_code,
        mods: k.mods,
        key: points_to_units(&super::str_points(&k.key)),
        code: points_to_units(&super::str_points(&k.code)),
        repeat: k.repeat,
        key_code,
        ..UiData::default()
    }
}

/// A key pressed and released.
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn key(scope: &mut Scope<'_>, k: &KeyInput) -> Result<()> {
    let target = {
        let p = page(scope)?;
        match p.ui.focused.filter(|&f| f < p.arena.len()) {
            Some(f) => f,
            None => match body_or_root(&p.arena) {
                Some(b) => b,
                None => return Ok(()),
            },
        }
    };
    // "keydown, provided the key is neither the Esc key nor a shortcut key
    // reserved by the user agent" is an activation triggering input event.
    if crate::user_activation::is_activation_triggering("keydown", Some(&k.key)) {
        notify_activation(scope)?;
    }
    let down = fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::KeyboardEvent,
        "keydown",
        BUBBLING,
        key_data(k),
    )?;
    if down {
        keydown_default(scope, target, k)?;
    }
    // "keyup" at the element that has focus now? It goes to the element the
    // keydown went to, as browsers have it (the focus may have moved).
    let up_target = {
        let p = page(scope)?;
        if target < p.arena.len() {
            target
        } else {
            return Ok(());
        }
    };
    let up = fire_ui(
        scope,
        TargetId::Node(up_target),
        InterfaceId::KeyboardEvent,
        "keyup",
        BUBBLING,
        key_data(k),
    )?;
    if up && k.key == " " {
        let p = page(scope)?;
        let kind = activation::kind_of(&p.arena, up_target);
        if matches!(
            kind,
            Some(Kind::Submit | Kind::Reset | Kind::Checkbox | Kind::Radio | Kind::Inert)
        ) && !matches!(
            k.mods,
            Modifiers { ctrl: true, .. } | Modifiers { meta: true, .. }
        ) {
            key_click(scope, up_target)?;
        }
    }
    Ok(())
}

/// What a `keydown` that nobody canceled does.
fn keydown_default(scope: &mut Scope<'_>, target: usize, k: &KeyInput) -> Result<()> {
    match k.key.as_str() {
        "Tab" if !k.mods.ctrl && !k.mods.alt && !k.mods.meta => {
            let next = {
                let p = page(scope)?;
                next_in_tab_order(&p.arena, p.ui.focused, k.mods.shift)
            };
            set_focus(scope, next)?;
        }
        "Enter" => enter(scope, target, k)?,
        "Backspace" => {
            let p = page(scope)?;
            if activation::is_text_control(&p.arena, target) {
                edit(scope, target, Edit::DeleteBackward)?;
            }
        }
        key if key.chars().count() == 1 && !k.mods.ctrl && !k.mods.meta => {
            let ch = key.chars().next().unwrap_or(' ');
            // The legacy `keypress`, for a key that produces a character.
            let mut data = key_data(k);
            data.char_code = u32::from(ch);
            data.which = u32::from(ch);
            data.key_code = u32::from(ch);
            let pressed = fire_ui(
                scope,
                TargetId::Node(target),
                InterfaceId::KeyboardEvent,
                "keypress",
                BUBBLING,
                data,
            )?;
            let p = page(scope)?;
            if pressed && activation::is_text_control(&p.arena, target) {
                edit(scope, target, Edit::Insert(key.to_owned()))?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Enter: clicks a link, a button or a checkbox; implicit submission from a
/// text input; a line break in a `textarea`.
fn enter(scope: &mut Scope<'_>, target: usize, k: &KeyInput) -> Result<()> {
    let (kind, textarea, text_input, form) = {
        let p = page(scope)?;
        (
            activation::kind_of(&p.arena, target),
            is_html_exec(&p.arena, target, b"textarea")
                && activation::is_text_control(&p.arena, target),
            is_html_exec(&p.arena, target, b"input")
                && activation::is_text_control(&p.arena, target),
            super::forms::form_owner(&p.arena, target),
        )
    };
    // The `keypress` of Enter, which a listener can cancel.
    let mut data = key_data(k);
    data.char_code = 13;
    let pressed = fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::KeyboardEvent,
        "keypress",
        BUBBLING,
        data,
    )?;
    if !pressed {
        return Ok(());
    }
    match kind {
        Some(Kind::Hyperlink | Kind::Submit | Kind::Reset | Kind::Checkbox | Kind::Inert) => {
            key_click(scope, target)
        }
        _ if textarea => edit(scope, target, Edit::Insert("\n".to_owned())),
        _ if text_input => match form {
            Some(f) => implicit_submission(scope, f),
            None => Ok(()),
        },
        _ => Ok(()),
    }
}

/// HTML §4.10.21.2† "implicit submission": "If the form has a default button
/// ... fire a click event at it. If the form has no submit button, then the
/// implicit submission mechanism must perform the following steps: if the
/// form has more than one field that blocks implicit submission, then
/// return. Otherwise submit the form element from the form element itself."
fn implicit_submission(scope: &mut Scope<'_>, form: usize) -> Result<()> {
    let (default_button, blockers) = {
        let p = page(scope)?;
        let controls = clazel_forms::exec::controls::controls_exec(&p.arena, form);
        let button = controls
            .iter()
            .copied()
            .find(|&c| clazel_forms::submit::exec::submit::is_submit_button_exec(&p.arena, c));
        let blockers = controls
            .iter()
            .filter(|&&c| {
                is_html_exec(&p.arena, c, b"input")
                    && matches!(
                        input_type_exec(&p.arena, c),
                        InputType::Text
                            | InputType::Search
                            | InputType::Tel
                            | InputType::Url
                            | InputType::Email
                            | InputType::Password
                            | InputType::Other
                    )
            })
            .count();
        (button, blockers)
    };
    match default_button {
        Some(b) => {
            // "If the default button is not disabled, fire a click event at it".
            if activation::is_disabled_control(&page(scope)?.arena, b) {
                return Ok(());
            }
            key_click(scope, b)
        }
        None if blockers <= 1 => super::forms::submit_form(scope, form, form, true),
        None => Ok(()),
    }
}

/// A change to a text control's value.
enum Edit {
    Insert(String),
    DeleteBackward,
}

/// UI Events `beforeinput` and `input` around a change of the value of the
/// text control `target`: "beforeinput" is cancelable; `input` follows the
/// change.
fn edit(scope: &mut Scope<'_>, target: usize, change: Edit) -> Result<()> {
    let (input_type, data) = match &change {
        Edit::Insert(s) if s == "\n" => ("insertLineBreak", None),
        Edit::Insert(s) => ("insertText", Some(s.clone())),
        Edit::DeleteBackward => ("deleteContentBackward", None),
    };
    let unit_data = data
        .as_deref()
        .map(|s| points_to_units(&super::str_points(s)));
    let ui = UiData {
        view: true,
        data: unit_data,
        input_type: points_to_units(&super::str_points(input_type)),
        ..UiData::default()
    };
    let ok = fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::InputEvent,
        "beforeinput",
        BUBBLING,
        ui.clone(),
    )?;
    if !ok {
        return Ok(());
    }
    {
        let p = page(scope)?;
        let mut v = super::forms::control_value(p, target);
        match change {
            Edit::Insert(s) => v.extend(s.chars().map(u32::from)),
            Edit::DeleteBackward => {
                v.pop();
            }
        }
        super::forms::set_control_value(p, target, v);
    }
    fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::InputEvent,
        "input",
        EventInit {
            bubbles: true,
            cancelable: false,
            composed: true,
        },
        ui,
    )?;
    Ok(())
}

// ---- Wheel and scroll -------------------------------------------------------

/// A wheel turn: the `wheel` event at the element under the pointer. Returns
/// false if a listener canceled it ("the default action ... is to scroll").
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn wheel(scope: &mut Scope<'_>, w: &WheelInput) -> Result<bool> {
    let Some(target) = element_of(&page(scope)?.arena, w.target) else {
        return Ok(true);
    };
    fire_ui(
        scope,
        TargetId::Node(target),
        InterfaceId::WheelEvent,
        "wheel",
        BUBBLING,
        UiData {
            view: true,
            mods: w.mods,
            client_x: w.client_x,
            client_y: w.client_y,
            screen_x: w.client_x,
            screen_y: w.client_y,
            delta_x: w.delta_x,
            delta_y: w.delta_y,
            delta_mode: w.delta_mode,
            ..UiData::default()
        },
    )
}

/// CSSOM View §? "run the scroll steps": "fire an event named scroll that
/// bubbles at target" for a viewport scroll, the document.
///
/// # Errors
/// What the engine throws that is not an exception.
pub(crate) fn scroll(scope: &mut Scope<'_>) -> Result<()> {
    fire_with(
        scope,
        TargetId::Node(0),
        "scroll",
        EventInit {
            bubbles: true,
            cancelable: false,
            composed: false,
        },
    )?;
    Ok(())
}

// ---- HTMLElement: click, focus, blur, tabIndex ---------------------------------

fn element(scope: &mut Scope<'_>, this: ObjectKey) -> Result<usize> {
    super::node::element_of(scope, this)
}

impl HTMLElementImpl for Page {
    /// HTML §3.2.6.? `click()`.
    fn click<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        let e = element(scope, this)?;
        synthetic_click(scope, e)
    }

    /// HTML §6.6.? `focus()`: "run the focusing steps" for the element (it
    /// does nothing if the element is not focusable).
    fn focus<'s>(scope: &mut Scope<'s>, this: ObjectKey, _options: FocusOptions) -> Result<()> {
        let e = element(scope, this)?;
        set_focus(scope, Some(e))
    }

    /// `blur()`: "if this is the focused area, run the unfocusing steps".
    fn blur<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<()> {
        let e = element(scope, this)?;
        if page(scope)?.ui.focused == Some(e) {
            set_focus(scope, None)?;
        }
        Ok(())
    }

    /// HTML §6.6.3† `tabIndex`: "the tabindex content attribute's value if
    /// it parses, else 0 for the elements that are focusable by default and
    /// -1 for the others".
    fn tab_index<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        let e = element(scope, this)?;
        let arena = &page(scope)?.arena;
        Ok(match activation::tabindex(arena, e) {
            Some(t) => i32::try_from(t).unwrap_or(0),
            None if activation::is_focusable(arena, e) => 0,
            None => -1,
        })
    }

    /// `tabIndex`'s setter: "set the content attribute to the value".
    fn set_tab_index<'s>(scope: &mut Scope<'s>, this: ObjectKey, value: i32) -> Result<()> {
        let e = element(scope, this)?;
        let p = page(scope)?;
        super::node::set_attribute_value(
            &mut p.arena,
            e,
            &super::str_points("tabindex"),
            super::str_points(&value.to_string()),
        );
        Ok(())
    }
}
