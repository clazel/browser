//! `UIEvent`, `MouseEvent`, `WheelEvent`, `KeyboardEvent`, `FocusEvent`,
//! `InputEvent` and `UserActivation` (UI Events §3† to §5†, §6†, Pointer
//! Events' `MouseEvent` and `WheelEvent`, HTML §6.4†), over
//! [`crate::events`]'s `Event`.
//!
//! <https://w3c.github.io/uievents/>
//! (section numbers carry the mark † of phase-7.md: from memory, not read at
//! a pinned commit).
//!
//! Tier 0, not proven. An event of these interfaces is an `Event` object
//! ([`super::Object::Event`]) with its interface and, in the page's side
//! table ([`crate::ui::Ui::events`]), the members the interface adds
//! ([`crate::ui::UiData`]). The platform makes them with [`create`]; script
//! makes them with the constructors here.
//!
//! Not implemented: the `Pointer*` events (the renderer sends no pointer
//! type), `CompositionEvent` and `TextEvent` (no input method), and the
//! `layerX` and `layerY` of `MouseEvent` (always the client position: the
//! page has no positioned ancestors to measure from, and they are legacy).

use clazel_js::{Result, Scope};
use clazel_webidl::convert::DomString;
use clazel_webidl::generated::bindings::*;
use clazel_webidl::platform::ObjectKey;

use super::event::{key_of_target, target_of};
use super::{EventData, Object, Page, WINDOW, page, type_error};
use crate::events::{Event, EventInit as Init, TargetId};
use crate::ui::{Modifiers, UiData};

/// The page's clock, in milliseconds: the page's own clock when HTML's script
/// processing runs the page, else the hooks' ([`super::PageHooks::now_ms`]).
pub(crate) fn clock_ms(scope: &mut Scope<'_>) -> Result<f64> {
    if let Ok(st) = crate::scripting::state::state(scope) {
        // Milliseconds since the page's time origin, as `performance.now()`
        // counts them (and so `Event.timeStamp`: HTML's "current high
        // resolution time"), without its 100 µs coarsening.
        let since = st.clock.now_us().saturating_sub(st.time_origin_us);
        return Ok(since as f64 / 1000.0);
    }
    Ok(page(scope)?.hooks.now_ms())
}

/// Makes an event object of `interface` with the members `data`, of type
/// `type_`, trusted if the platform made it. The object is "initialized".
pub(crate) fn create(
    scope: &mut Scope<'_>,
    interface: InterfaceId,
    type_: &str,
    init: Init,
    data: UiData,
    trusted: bool,
) -> Result<ObjectKey> {
    let t = clock_ms(scope)?;
    let points = super::str_points(type_);
    let mut event = if trusted {
        Event::new_trusted(&points, init, t)
    } else {
        Event::new(&points, init, t)
    };
    event.set_mouse_event(interface.inherits(InterfaceId::MouseEvent));
    let p = page(scope)?;
    let key = p.add_object(Object::Event(Box::new(EventData {
        event,
        interface,
        detail: None,
    })));
    if let Some(id) = Page::object_id(key) {
        p.ui.events.insert(id, data);
    }
    Ok(key)
}

/// The members of event object `this`, which must be one (an event the
/// platform or `createEvent` made without them has the empty record).
fn data<'a>(scope: &'a mut Scope<'_>, this: ObjectKey) -> Result<&'a mut UiData> {
    let Some(id) = Page::object_id(this) else {
        return Err(type_error(scope, "not an Event"));
    };
    if !matches!(page(scope)?.object(this), Some(Object::Event(_))) {
        return Err(type_error(scope, "not an Event"));
    }
    Ok(page(scope)?.ui.events.entry(id).or_default())
}

fn event_of<'a>(scope: &'a mut Scope<'_>, this: ObjectKey) -> Result<&'a mut Event> {
    if !matches!(page(scope)?.object(this), Some(Object::Event(_))) {
        return Err(type_error(scope, "not an Event"));
    }
    match page(scope)?.object_mut(this) {
        Some(Object::Event(e)) => Ok(&mut e.event),
        _ => Err(clazel_js::Error::WrongType("an Event")),
    }
}

/// The target a `relatedTarget` or `view` key names.
fn related(scope: &mut Scope<'_>, key: Option<ObjectKey>) -> Result<Option<TargetId>> {
    let Some(k) = key else { return Ok(None) };
    Ok(target_of(page(scope)?, k))
}

fn new_event(
    scope: &mut Scope<'_>,
    interface: InterfaceId,
    type_: &[u16],
    init: Init,
    d: UiData,
) -> Result<ObjectKey> {
    let t = String::from_utf16_lossy(type_);
    create(scope, interface, &t, init, d, false)
}

fn init_of(bubbles: bool, cancelable: bool, composed: bool) -> Init {
    Init {
        bubbles,
        cancelable,
        composed,
    }
}

/// `initUIEvent`'s steps (UI Events §3.1.2†): "If the dispatch flag is set,
/// return. Initialize the event with type, bubbles, cancelable; set view
/// and detail."
fn init_ui(
    scope: &mut Scope<'_>,
    this: ObjectKey,
    type_: &[u16],
    bubbles: bool,
    cancelable: bool,
    view: Option<ObjectKey>,
    detail: i32,
) -> Result<bool> {
    if event_of(scope, this)?.is_dispatching() {
        return Ok(false);
    }
    event_of(scope, this)?.init_event(&super::units_to_points(type_), bubbles, cancelable);
    let d = data(scope, this)?;
    d.view = view == Some(WINDOW);
    d.detail = detail;
    Ok(true)
}

impl UIEventImpl for Page {
    fn view<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(data(scope, this)?.view.then_some(WINDOW))
    }

    fn detail<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.detail)
    }

    fn which<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(data(scope, this)?.which)
    }

    fn init_ui_event<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        type_arg: DomString,
        bubbles_arg: bool,
        cancelable_arg: bool,
        view_arg: Option<ObjectKey>,
        detail_arg: i32,
    ) -> Result<()> {
        init_ui(
            scope,
            this,
            &type_arg,
            bubbles_arg,
            cancelable_arg,
            view_arg,
            detail_arg,
        )?;
        Ok(())
    }

    /// UI Events §3.1† `new UIEvent(type, eventInitDict)`.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: UIEventInit,
    ) -> Result<ObjectKey> {
        let d = UiData {
            view: init.view == Some(WINDOW),
            detail: init.detail,
            which: init.which,
            ..UiData::default()
        };
        new_event(
            scope,
            InterfaceId::UIEvent,
            &type_,
            init_of(init.bubbles, init.cancelable, init.composed),
            d,
        )
    }
}

impl MouseEventImpl for Page {
    fn screen_x<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.screen_x)
    }

    fn screen_y<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.screen_y)
    }

    fn client_x<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.client_x)
    }

    fn client_y<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.client_y)
    }

    fn layer_x<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.client_x)
    }

    fn layer_y<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i32> {
        Ok(data(scope, this)?.client_y)
    }

    fn ctrl_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.ctrl)
    }

    fn shift_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.shift)
    }

    fn alt_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.alt)
    }

    fn meta_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.meta)
    }

    fn button<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<i16> {
        Ok(data(scope, this)?.button)
    }

    fn buttons<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u16> {
        Ok(data(scope, this)?.buttons)
    }

    fn related_target<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(data(scope, this)?.related_target.map(key_of_target))
    }

    /// UI Events §5.2.2† `getModifierState(keyArg)`: for the keys the page
    /// tracks (Control, Shift, Alt, Meta).
    fn get_modifier_state<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        key_arg: DomString,
    ) -> Result<bool> {
        let m = data(scope, this)?.mods;
        Ok(modifier_state(m, &String::from_utf16_lossy(&key_arg)))
    }

    /// UI Events §5.2.3† `initMouseEvent` (the arguments are in a struct: the
    /// operation has 15, more than a method may have).
    fn init_mouse_event<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        a: MouseEventInitMouseEventArgs,
    ) -> Result<()> {
        if !init_ui(
            scope,
            this,
            &a.type_arg,
            a.bubbles_arg,
            a.cancelable_arg,
            a.view_arg,
            a.detail_arg,
        )? {
            return Ok(());
        }
        let related = related(scope, a.related_target_arg)?;
        let d = data(scope, this)?;
        d.screen_x = a.screen_x_arg;
        d.screen_y = a.screen_y_arg;
        d.client_x = a.client_x_arg;
        d.client_y = a.client_y_arg;
        d.mods = Modifiers {
            ctrl: a.ctrl_key_arg,
            alt: a.alt_key_arg,
            shift: a.shift_key_arg,
            meta: a.meta_key_arg,
        };
        d.button = a.button_arg;
        d.related_target = related;
        Ok(())
    }

    /// UI Events §5.2† `new MouseEvent(type, eventInitDict)`.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: MouseEventInit,
    ) -> Result<ObjectKey> {
        let related = related(scope, init.related_target)?;
        let d = UiData {
            view: init.view == Some(WINDOW),
            detail: init.detail,
            which: init.which,
            mods: Modifiers {
                ctrl: init.ctrl_key,
                shift: init.shift_key,
                alt: init.alt_key,
                meta: init.meta_key,
            },
            screen_x: init.screen_x,
            screen_y: init.screen_y,
            client_x: init.client_x,
            client_y: init.client_y,
            button: init.button,
            buttons: init.buttons,
            related_target: related,
            ..UiData::default()
        };
        new_event(
            scope,
            InterfaceId::MouseEvent,
            &type_,
            init_of(init.bubbles, init.cancelable, init.composed),
            d,
        )
    }
}

/// `getModifierState` for the modifiers tracked.
fn modifier_state(m: Modifiers, key: &str) -> bool {
    match key {
        "Control" => m.ctrl,
        "Shift" => m.shift,
        "Alt" => m.alt,
        "Meta" => m.meta,
        _ => false,
    }
}

impl WheelEventImpl for Page {
    fn delta_x<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<f64> {
        Ok(data(scope, this)?.delta_x)
    }

    fn delta_y<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<f64> {
        Ok(data(scope, this)?.delta_y)
    }

    fn delta_z<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<f64> {
        Ok(data(scope, this)?.delta_z)
    }

    fn delta_mode<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(data(scope, this)?.delta_mode)
    }

    fn momentum<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.momentum)
    }

    /// `new WheelEvent(type, eventInitDict)`.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: WheelEventInit,
    ) -> Result<ObjectKey> {
        let related = related(scope, init.related_target)?;
        let d = UiData {
            view: init.view == Some(WINDOW),
            detail: init.detail,
            which: init.which,
            mods: Modifiers {
                ctrl: init.ctrl_key,
                shift: init.shift_key,
                alt: init.alt_key,
                meta: init.meta_key,
            },
            screen_x: init.screen_x,
            screen_y: init.screen_y,
            client_x: init.client_x,
            client_y: init.client_y,
            button: init.button,
            buttons: init.buttons,
            related_target: related,
            delta_x: init.delta_x,
            delta_y: init.delta_y,
            delta_z: init.delta_z,
            delta_mode: init.delta_mode,
            momentum: init.momentum,
            ..UiData::default()
        };
        new_event(
            scope,
            InterfaceId::WheelEvent,
            &type_,
            init_of(init.bubbles, init.cancelable, init.composed),
            d,
        )
    }
}

impl KeyboardEventImpl for Page {
    fn key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        Ok(data(scope, this)?.key.clone())
    }

    fn code<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        Ok(data(scope, this)?.code.clone())
    }

    fn location<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(data(scope, this)?.location)
    }

    fn ctrl_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.ctrl)
    }

    fn shift_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.shift)
    }

    fn alt_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.alt)
    }

    fn meta_key<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.mods.meta)
    }

    fn repeat<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.repeat)
    }

    fn is_composing<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.is_composing)
    }

    fn char_code<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(data(scope, this)?.char_code)
    }

    fn key_code<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<u32> {
        Ok(data(scope, this)?.key_code)
    }

    fn get_modifier_state<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        key_arg: DomString,
    ) -> Result<bool> {
        let m = data(scope, this)?.mods;
        Ok(modifier_state(m, &String::from_utf16_lossy(&key_arg)))
    }

    /// UI Events §6.? `initKeyboardEvent` (the arguments are in a struct).
    fn init_keyboard_event<'s>(
        scope: &mut Scope<'s>,
        this: ObjectKey,
        a: KeyboardEventInitKeyboardEventArgs,
    ) -> Result<()> {
        if !init_ui(
            scope,
            this,
            &a.type_arg,
            a.bubbles_arg,
            a.cancelable_arg,
            a.view_arg,
            0,
        )? {
            return Ok(());
        }
        let d = data(scope, this)?;
        d.key = a.key_arg;
        d.location = a.location_arg;
        d.mods = Modifiers {
            ctrl: a.ctrl_key,
            alt: a.alt_key,
            shift: a.shift_key,
            meta: a.meta_key,
        };
        Ok(())
    }

    /// UI Events §6.? `new KeyboardEvent(type, eventInitDict)`.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: KeyboardEventInit,
    ) -> Result<ObjectKey> {
        let d = UiData {
            view: init.view == Some(WINDOW),
            detail: init.detail,
            which: init.which,
            mods: Modifiers {
                ctrl: init.ctrl_key,
                shift: init.shift_key,
                alt: init.alt_key,
                meta: init.meta_key,
            },
            key: init.key,
            code: init.code,
            location: init.location,
            repeat: init.repeat,
            is_composing: init.is_composing,
            char_code: init.char_code,
            key_code: init.key_code,
            ..UiData::default()
        };
        new_event(
            scope,
            InterfaceId::KeyboardEvent,
            &type_,
            init_of(init.bubbles, init.cancelable, init.composed),
            d,
        )
    }
}

impl FocusEventImpl for Page {
    fn related_target<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(data(scope, this)?.related_target.map(key_of_target))
    }

    /// UI Events §4.? `new FocusEvent(type, eventInitDict)`.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: FocusEventInit,
    ) -> Result<ObjectKey> {
        let related = related(scope, init.related_target)?;
        let d = UiData {
            view: init.view == Some(WINDOW),
            detail: init.detail,
            which: init.which,
            related_target: related,
            ..UiData::default()
        };
        new_event(
            scope,
            InterfaceId::FocusEvent,
            &type_,
            init_of(init.bubbles, init.cancelable, init.composed),
            d,
        )
    }
}

impl InputEventImpl for Page {
    fn data<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<Option<String>> {
        Ok(data(scope, this)?
            .data
            .as_ref()
            .map(|d| String::from_utf16_lossy(d)))
    }

    fn is_composing<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<bool> {
        Ok(data(scope, this)?.is_composing)
    }

    fn input_type<'s>(scope: &mut Scope<'s>, this: ObjectKey) -> Result<DomString> {
        Ok(data(scope, this)?.input_type.clone())
    }

    /// UI Events §5.? `new InputEvent(type, eventInitDict)`.
    fn constructor<'s>(
        scope: &mut Scope<'s>,
        type_: DomString,
        init: InputEventInit,
    ) -> Result<ObjectKey> {
        let d = UiData {
            view: init.view == Some(WINDOW),
            detail: init.detail,
            which: init.which,
            data: init.data,
            input_type: init.input_type,
            is_composing: init.is_composing,
            ..UiData::default()
        };
        new_event(
            scope,
            InterfaceId::InputEvent,
            &type_,
            init_of(init.bubbles, init.cancelable, init.composed),
            d,
        )
    }
}

impl UserActivationImpl for Page {
    /// HTML §6.4.? `hasBeenActive`: "has sticky activation".
    fn has_been_active<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(page(scope)?.ui.activation.has_been_active())
    }

    /// `isActive`: "has transient activation".
    fn is_active<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        let now = clock_ms(scope)?;
        Ok(page(scope)?.ui.activation.is_active(now))
    }
}
