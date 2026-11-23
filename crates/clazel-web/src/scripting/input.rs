//! The embedder's way in for the user's input (phase-7.md item 7.14): a
//! click, a key, a wheel turn and a scroll of the page as UI events, with
//! their default actions, through the page's bindings and listeners
//! ([`crate::page::input`]).
//!
//! The renderer hit-tests (layout is its, and the page has none): it passes
//! the node id of the element under the pointer. The default actions of a
//! click that script did not cancel happen inside the call, through the
//! page's hooks: following a link is [`crate::page::PageHooks::navigate`]
//! (the renderer runs a `javascript:` URL itself), submitting a form is
//! `navigate` for a `GET` and [`crate::page::PageHooks::submit`] for a
//! `POST`.
//!
//! Each call is a task of the event loop in the sense that the microtask
//! checkpoint ("clean up after running script") follows it and the events
//! the page fired meanwhile ([`super::state::FiredEvent`]) are dispatched.

use clazel_js::{Result, Scope};

use super::state::state;
use super::{Page, element};
use crate::page::input::{self, KeyInput, MouseInput, WheelInput};

/// Runs `f` as a script-running task: the page counts it as running a
/// script (so `document.currentScript` is null and the checkpoint waits for
/// the outermost one), and the microtask checkpoint and the page's own fired
/// events follow.
fn task<R>(scope: &mut Scope<'_>, f: impl FnOnce(&mut Scope<'_>) -> Result<R>) -> Result<R> {
    {
        let st = state(scope)?;
        st.running = st.running.saturating_add(1);
    }
    let r = f(scope);
    {
        let st = state(scope)?;
        st.running = st.running.saturating_sub(1);
    }
    element::clean_up_after_running_script(scope)?;
    r
}

impl Page {
    /// How many listeners and event handlers dispatch has called, ever. An
    /// embedder compares it before and after an input to learn whether the
    /// page's script ran (and the page may have changed).
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn listener_calls(&mut self) -> Result<u64> {
        self.rt
            .scope(|scope| Ok(crate::page::page(scope)?.ui.listener_calls))
    }

    /// A click of the user on the element `input.target`: `mousemove`,
    /// `mousedown` (which notifies the page's user activation and moves
    /// focus), `mouseup` and `click`, with the default actions.
    ///
    /// # Errors
    /// An error that stops the page (termination, out of memory).
    pub fn click(&mut self, input: MouseInput) -> Result<()> {
        self.rt.scope(|scope| task(scope, |s| input::click(s, &input)))
    }

    /// A key pressed and released with focus where it is: `keydown`,
    /// `keypress` and the text input, `keyup`, with the default actions
    /// (Tab, Enter, Backspace and text).
    ///
    /// # Errors
    /// An error that stops the page.
    pub fn key(&mut self, input: KeyInput) -> Result<()> {
        self.rt.scope(|scope| task(scope, |s| input::key(s, &input)))
    }

    /// A wheel turn over `input.target`: the `wheel` event. Returns `true`
    /// if the default action (scrolling) is to happen, `false` if a listener
    /// canceled the event.
    ///
    /// # Errors
    /// An error that stops the page.
    pub fn wheel(&mut self, input: WheelInput) -> Result<bool> {
        self.rt.scope(|scope| task(scope, |s| input::wheel(s, &input)))
    }

    /// The viewport scrolled: the `scroll` event at the document, which
    /// bubbles (CSSOM View's "run the scroll steps").
    ///
    /// # Errors
    /// An error that stops the page.
    pub fn scrolled(&mut self) -> Result<()> {
        self.rt.scope(|scope| task(scope, input::scroll))
    }

    /// Moves focus to `node` (`None`: away from every element), as the
    /// user does by clicking: the `blur`, `focusout`, `focus` and `focusin`
    /// events. Does nothing if `node` is not focusable.
    ///
    /// # Errors
    /// An error that stops the page.
    pub fn set_focus(&mut self, node: Option<usize>) -> Result<()> {
        self.rt.scope(|scope| task(scope, |s| input::set_focus(s, node)))
    }

    /// The focused element, if any.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn focused(&mut self) -> Result<Option<usize>> {
        self.rt.scope(input::focused)
    }

    /// HTML §6.4.2† "has transient activation" for the page's window now.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn has_transient_activation(&mut self) -> Result<bool> {
        self.rt.scope(|scope| {
            let now = crate::page::ui_events::clock_ms(scope)?;
            Ok(crate::page::page(scope)?.ui.activation.has_transient(now))
        })
    }

    /// HTML §6.4.2† "consume user activation": the check the page's own
    /// `window.open` and `target=_blank` make before asking the kernel to
    /// open a tab (item 7.16's `OpenTab`), where the kernel's own record of
    /// the user's input is the guarantee. Returns whether there was a
    /// transient activation to consume.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn consume_user_activation(&mut self) -> Result<bool> {
        self.rt.scope(|scope| {
            let now = crate::page::ui_events::clock_ms(scope)?;
            Ok(crate::page::page(scope)?.ui.activation.consume(now))
        })
    }

    /// HTML §6.4.2† "has sticky activation".
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn has_sticky_activation(&mut self) -> Result<bool> {
        self.rt
            .scope(|scope| Ok(crate::page::page(scope)?.ui.activation.has_sticky()))
    }

    /// The current value of the text control `node` (`input` or `textarea`),
    /// as the form's entry list would take it.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn control_value(&mut self, node: usize) -> Result<String> {
        self.rt.scope(|scope| {
            let p = crate::page::page(scope)?;
            Ok(crate::page::points_to_string(
                &crate::page::forms::control_value(p, node),
            ))
        })
    }

    /// Whether the checkbox or radio button `node` is checked.
    ///
    /// # Errors
    /// What `clazel-js` returns.
    pub fn control_checked(&mut self, node: usize) -> Result<bool> {
        self.rt
            .scope(|scope| Ok(crate::page::forms::is_checked(crate::page::page(scope)?, node)))
    }
}
