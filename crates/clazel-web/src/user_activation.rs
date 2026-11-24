//! HTML §6.4† user activation: the state a `Window` keeps of the user's
//! interaction with its page, and what reads it (`navigator.userActivation`,
//! and, from item 7.16, the page's `window.open` and `target=_blank`).
//!
//! <https://html.spec.whatwg.org/multipage/interaction.html#tracking-user-activation>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit; steps are quoted by their words).
//!
//! Tier 0, not proven.
//!
//! Modelling choices:
//! - **One window.** There are no frames in this browser's pages, so "the
//!   top-level traversable's active window and every descendant" is the one
//!   `Window`.
//! - **Times** are the page clock's milliseconds as `f64`: "last activation
//!   timestamp" is `+∞` for "never" (the standard's initial value) and `−∞`
//!   after "consume user activation", which keeps "sticky activation" true
//!   (it is "last activation timestamp is not +∞") and "transient
//!   activation" false (the current time is not less than `−∞` plus the
//!   duration).
//! - **The transient activation duration** is 5 seconds, the "implementation-
//!   defined" value the standard suggests and browsers use.
//! - **History-action activation** is tracked as the standard has it, with
//!   its own "last history-action activation timestamp"; this browser's
//!   history actions (`pushState`, `history.back()` and the rest) do not read
//!   it yet.
//! - **Where the kernel's record hooks in.** The renderer's state here is
//!   what page-visible APIs read. Item 7.16's popup rule is about the
//!   kernel's own record: the kernel sees every `Input` it forwards (and so
//!   knows how many of its steps ago the last one was), and an `OpenTab` from
//!   the renderer is allowed only within the window of kernel steps after
//!   one (`theorem_popup_needs_input`). The renderer-side call that sends
//!   `OpenTab` is the place that asks [`UserActivation::consume`] first, as
//!   `window.open` does ("If the relevant global object of this does not have
//!   transient activation, then return null"): that check is the page's own
//!   courtesy, the kernel's is the guarantee.

/// "transient activation duration", in milliseconds.
pub const TRANSIENT_ACTIVATION_DURATION_MS: f64 = 5000.0;

/// The user activation state of a `Window`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct UserActivation {
    /// "last activation timestamp": `+∞` initially.
    last_activation: f64,
    /// "last history-action activation timestamp": `−∞` initially.
    last_history_action: f64,
}

impl Default for UserActivation {
    fn default() -> UserActivation {
        UserActivation::new()
    }
}

impl UserActivation {
    /// A window nobody has interacted with.
    #[must_use]
    pub fn new() -> UserActivation {
        UserActivation {
            last_activation: f64::INFINITY,
            last_history_action: f64::NEG_INFINITY,
        }
    }

    /// HTML §6.4.2† "activation notification": "Set window's last activation
    /// timestamp to the current high resolution time" (the standard sets it
    /// for the window and the ones in its tree; there is one), and the same
    /// for the last history-action activation timestamp.
    pub fn notify(&mut self, now: f64) {
        self.last_activation = now;
        self.last_history_action = now;
    }

    /// "has transient activation": "the current high resolution time is
    /// greater than or equal to last activation timestamp, and less than last
    /// activation timestamp plus the transient activation duration".
    #[must_use]
    pub fn has_transient(&self, now: f64) -> bool {
        now >= self.last_activation && now < self.last_activation + TRANSIENT_ACTIVATION_DURATION_MS
    }

    /// "has sticky activation": "last activation timestamp is not
    /// positive infinity".
    #[must_use]
    pub fn has_sticky(&self) -> bool {
        self.last_activation != f64::INFINITY
    }

    /// "has history-action activation": the last history-action activation
    /// timestamp is not negative infinity (a consumed one is, and so is one
    /// never set); the standard puts no time limit on it.
    #[must_use]
    pub fn has_history_action(&self, now: f64) -> bool {
        let _ = now;
        self.last_history_action != f64::NEG_INFINITY
    }

    /// "consume user activation": "If W does not have transient activation,
    /// return false. Otherwise set W's last activation timestamp to negative
    /// infinity (and, for history-action, its timestamp to negative infinity
    /// too); return true."
    pub fn consume(&mut self, now: f64) -> bool {
        if !self.has_transient(now) {
            return false;
        }
        self.last_activation = f64::NEG_INFINITY;
        true
    }

    /// "consume history-action user activation": the same for the
    /// history-action timestamp.
    pub fn consume_history_action(&mut self, now: f64) -> bool {
        if !self.has_history_action(now) {
            return false;
        }
        self.last_history_action = f64::NEG_INFINITY;
        true
    }

    /// `navigator.userActivation.isActive`: "has transient activation".
    #[must_use]
    pub fn is_active(&self, now: f64) -> bool {
        self.has_transient(now)
    }

    /// `navigator.userActivation.hasBeenActive`: "has sticky activation".
    #[must_use]
    pub fn has_been_active(&self) -> bool {
        self.has_sticky()
    }
}

/// HTML §6.4.2† "activation triggering input event": "keydown, provided the
/// key is neither the Esc key nor a shortcut key reserved by the user
/// agent; mousedown; pointerdown, provided the event's pointerType is
/// "mouse"; pointerup, provided the event's pointerType is not "mouse";
/// touchend". The renderer's input has no pointer or touch events, so the
/// types are `keydown` and `mousedown`; `key` is the key's `key` value.
#[must_use]
pub fn is_activation_triggering(type_: &str, key: Option<&str>) -> bool {
    match type_ {
        "mousedown" => true,
        "keydown" => key != Some("Escape"),
        _ => false,
    }
}
