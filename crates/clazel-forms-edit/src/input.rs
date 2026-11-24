//! `Input` messages to editor events (phase-6.md item 6.15, with 5.18's
//! `Input` and 6.0(f)'s `TextInput`).
//!
//! `clazel-ipc`'s `Input` is `(kind, x, y, negative, delta, key)` with kind 0
//! a click, 1 a scroll and 2 a key. This module reads the fields as plain
//! integers (no dependency on `clazel-ipc`: the renderer, which has both,
//! calls it).
//!
//! Modelling choices (listed):
//! - **Key codes** are the DOM's legacy `keyCode` numbers for the editing
//!   keys ([`code`]); Shift is bit 16 of the key field ([`SHIFT`]), because
//!   `Input` has no modifier field. This is a proposal for the host shells
//!   (6.0(f) fixes the message, not the numbers); `Input`'s schema is not
//!   changed.
//! - **A click** (kind 0) is a press followed by a release: it focuses,
//!   places the caret, toggles and activates, but cannot select by dragging.
//!   Dragging needs a press, a move and a release, which `Input` has no kinds
//!   for: [`PRESS`], [`DRAG`] and [`RELEASE`] (3, 4 and 5) are the kinds this
//!   module reads for them, **proposed and not in `clazel-ipc`'s schema**
//!   (which makes the receiver refuse an unknown kind), so a kernel that
//!   routes them needs a schema change first. The tests use them.
//! - **Positions** are device pixels in the viewport; the caller gives the
//!   scale and the vertical scroll, and the events are in CSS pixels of the
//!   document.
//! - Typed text is not an `Input`: it is 6.0(f)'s `TextInput { text }`, which
//!   the caller turns into [`Event::Text`] itself.

use crate::editor::{Event, Key};

/// `Input`'s kind for a click.
pub const CLICK: u64 = 0;
/// `Input`'s kind for a key.
pub const KEY: u64 = 2;
/// Proposed kind: the button went down.
pub const PRESS: u64 = 3;
/// Proposed kind: the pointer moved with the button down.
pub const DRAG: u64 = 4;
/// Proposed kind: the button went up.
pub const RELEASE: u64 = 5;
/// Bit 16 of a key field: Shift.
pub const SHIFT: u64 = 1 << 16;

/// The key codes of the editing keys.
pub mod code {
    /// Backspace.
    pub const BACKSPACE: u64 = 8;
    /// Tab.
    pub const TAB: u64 = 9;
    /// Enter.
    pub const ENTER: u64 = 13;
    /// End.
    pub const END: u64 = 35;
    /// Home.
    pub const HOME: u64 = 36;
    /// Left arrow.
    pub const LEFT: u64 = 37;
    /// Up arrow.
    pub const UP: u64 = 38;
    /// Right arrow.
    pub const RIGHT: u64 = 39;
    /// Down arrow.
    pub const DOWN: u64 = 40;
    /// Delete.
    pub const DELETE: u64 = 46;
}

/// Where an `Input` lands: the device pixel ratio and the scroll.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Surface {
    /// Device pixels per CSS pixel (at least 1).
    pub scale: u32,
    /// The viewport's top in CSS pixels of the document.
    pub scroll_y: i32,
}

fn css(v: u64, scale: u32) -> i32 {
    i32::try_from(v.checked_div(u64::from(scale.max(1))).unwrap_or(0)).unwrap_or(i32::MAX)
}

/// The events an `Input` with these fields stands for (none for a scroll,
/// which is the page's, and for a key or kind the editor does not know).
pub fn from_input(kind: u64, x: u64, y: u64, key: u64, on: Surface) -> Vec<Event> {
    let (px, py) = (
        css(x, on.scale),
        css(y, on.scale).saturating_add(on.scroll_y),
    );
    match kind {
        CLICK => vec![
            Event::Press {
                x: px,
                y: py,
                shift: false,
            },
            Event::Release,
        ],
        PRESS => vec![Event::Press {
            x: px,
            y: py,
            shift: key & SHIFT != 0,
        }],
        DRAG => vec![Event::Drag { x: px, y: py }],
        RELEASE => vec![Event::Release],
        KEY => {
            let shift = key & SHIFT != 0;
            let k = match key & 0xFFFF {
                code::BACKSPACE => Key::Backspace,
                code::TAB => Key::Tab,
                code::ENTER => Key::Enter,
                code::END => Key::End,
                code::HOME => Key::Home,
                code::LEFT => Key::Left,
                code::UP => Key::Up,
                code::RIGHT => Key::Right,
                code::DOWN => Key::Down,
                code::DELETE => Key::Delete,
                _ => return Vec::new(),
            };
            vec![Event::Key { key: k, shift }]
        }
        _ => Vec::new(),
    }
}
