//! The state of the page's user interface that script and the embedder share
//! (phase-7.md item 7.14): the form controls' dynamic state, focus, user
//! activation, the data of UI events, and the event handlers (HTML §8.1.8†).
//!
//! Tier 0, not proven.

use std::collections::HashMap;

use clazel_forms::exec::entry::ExecControl;

use crate::events::TargetId;
use crate::user_activation::UserActivation;

/// The modifier keys held (UI Events §3.8† `EventModifierInit`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Modifiers {
    /// `ctrlKey`
    pub ctrl: bool,
    /// `shiftKey`
    pub shift: bool,
    /// `altKey`
    pub alt: bool,
    /// `metaKey`
    pub meta: bool,
}

/// The members `UIEvent` and its subclasses add to `Event`, for one event
/// object (UI Events §3†, §4†, §5†, §6†). One flat record for all of them: the
/// event's interface decides which a script can read.
#[derive(Debug, Clone, Default)]
pub struct UiData {
    /// `view` is the window (`UIEvent`).
    pub view: bool,
    /// `detail`
    pub detail: i32,
    /// `which` (legacy)
    pub which: u32,
    /// The modifier keys.
    pub mods: Modifiers,
    /// `screenX`
    pub screen_x: i32,
    /// `screenY`
    pub screen_y: i32,
    /// `clientX`
    pub client_x: i32,
    /// `clientY`
    pub client_y: i32,
    /// `button`
    pub button: i16,
    /// `buttons`
    pub buttons: u16,
    /// `relatedTarget`
    pub related_target: Option<TargetId>,
    /// `key` (`KeyboardEvent`), UTF-16
    pub key: Vec<u16>,
    /// `code`, UTF-16
    pub code: Vec<u16>,
    /// `location`
    pub location: u32,
    /// `repeat`
    pub repeat: bool,
    /// `isComposing`
    pub is_composing: bool,
    /// `charCode` (legacy)
    pub char_code: u32,
    /// `keyCode` (legacy)
    pub key_code: u32,
    /// `InputEvent.data`, UTF-16
    pub data: Option<Vec<u16>>,
    /// `inputType`, UTF-16
    pub input_type: Vec<u16>,
    /// `deltaX` (`WheelEvent`)
    pub delta_x: f64,
    /// `deltaY`
    pub delta_y: f64,
    /// `deltaZ`
    pub delta_z: f64,
    /// `deltaMode`
    pub delta_mode: u32,
    /// `momentum`
    pub momentum: bool,
}

/// An event handler's value (HTML §8.1.8.1†: "an event handler ... has a
/// value, which is either null, a callback function, or an internal raw
/// uncompiled handler").
#[derive(Debug, Clone)]
pub(crate) enum HandlerValue {
    /// null
    Null,
    /// A callback the script set (a handle to the object).
    Callback(clazel_js::Handle),
    /// "an internal raw uncompiled handler": the content attribute's text.
    Raw(Vec<u32>),
}

/// One event handler of one target: "event handler map"'s entry.
#[derive(Debug, Clone)]
pub(crate) struct Handler {
    /// The value.
    pub(crate) value: HandlerValue,
    /// The listener it is registered as while active
    /// ([`crate::events::ListenerId`], from the handler id space).
    pub(crate) listener: crate::events::ListenerId,
    /// Whether the listener is in the target's listener list.
    pub(crate) active: bool,
    /// The content attribute's text when the handler last looked (`None`:
    /// absent). A difference is "the attribute changed" (the attribute
    /// change steps of §8.1.8.2†); see `page::handlers`.
    pub(crate) attr_seen: Option<Vec<u32>>,
}

/// The first listener id of the event handlers: below it are the callbacks
/// `addEventListener` was given (`Page::callbacks`).
pub(crate) const HANDLER_ID_BASE: u64 = 1 << 62;

/// The page's UI state.
#[derive(Default)]
pub struct Ui {
    /// The dynamic state of form controls, by node id (HTML "dirty value
    /// flag", "checkedness" and the rest: `clazel-forms`' control state
    /// table). Grown to the arena's size when it is used.
    pub(crate) controls: Vec<ExecControl>,
    /// The focused element ("focused area of the document"), if any.
    pub(crate) focused: Option<usize>,
    /// The value of the focused text control when it got focus, for the
    /// `change` event at blur.
    pub(crate) value_at_focus: Option<Vec<u32>>,
    /// The `Window`'s user activation.
    pub(crate) activation: UserActivation,
    /// The data of UI event objects, by object id.
    pub(crate) events: HashMap<u64, UiData>,
    /// The event handlers, by target and event type.
    pub(crate) handlers: HashMap<(TargetId, String), Handler>,
    /// The next handler id.
    pub(crate) next_handler: u64,
    /// The legacy-pre-activation behavior's saved state: for the checkbox or
    /// radio being activated, what to restore if the event is canceled
    /// (the element, its checkedness, and for a radio the previously checked
    /// one of its group).
    pub(crate) pre_activation: Option<PreActivation>,
    /// The `click()` method's "click in progress flag" holders.
    pub(crate) click_in_progress: Vec<usize>,
    /// The element the mouse button went down on.
    pub(crate) pressed: Option<usize>,
    /// How many listeners (and event handlers) dispatch has called, ever:
    /// the embedder asks whether an input reached any, to know whether the
    /// page may have changed.
    pub(crate) listener_calls: u64,
    /// The `Window`'s "current event" (DOM §2.10† "inner invoke": the legacy
    /// `window.event`): the event whose listener is running.
    pub(crate) current_event: Option<clazel_webidl::platform::ObjectKey>,
}

/// What legacy-pre-activation behavior changed.
#[derive(Debug, Clone)]
pub(crate) struct PreActivation {
    /// The checkbox or radio.
    pub(crate) element: usize,
    /// Its checkedness before.
    pub(crate) checked: bool,
    /// Its "dirty checkedness flag" before.
    pub(crate) dirty_checked: bool,
    /// For a radio, the element of its group that was checked, and its
    /// dirty flag.
    pub(crate) previous: Option<(usize, bool)>,
}
