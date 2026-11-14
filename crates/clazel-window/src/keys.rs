//! The keys `clazel browse` acts on (phase-5.md item 5.23), named from each
//! platform's key codes, so the browser's loop is the same everywhere.
//!
//! - macOS: the virtual key codes of `<HIToolbox/Events.h>` (`kVK_Return` 0x24,
//!   `kVK_ANSI_L` 0x25, and so on), which are positions on an ANSI keyboard, so
//!   Command-L is the key where L is on a US layout.
//! - Windows: the virtual-key codes of `<WinUser.h>` (`VK_RETURN` 0x0D, `'L'`
//!   0x4C, `VK_OEM_4` 0xDB for `[`), which follow the layout.
//! - Linux (X11): the keysym in the first column of the key's keycode
//!   (`<X11/keysymdef.h>`: `XK_Return` 0xFF0D, `XK_l` 0x6C, `XK_bracketleft`
//!   0x5B), which follows the layout and ignores Shift.
//!
//! A code outside the table names nothing; its typed characters still arrive as
//! [`crate::Event::Char`].

/// A key the browser acts on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Named {
    /// Return (Enter).
    Return,
    /// Escape.
    Escape,
    /// Backspace (Delete on a Mac keyboard).
    Backspace,
    /// The space bar.
    Space,
    /// Page Up.
    PageUp,
    /// Page Down.
    PageDown,
    /// The left arrow.
    Left,
    /// The right arrow.
    Right,
    /// The up arrow.
    Up,
    /// The down arrow.
    Down,
    /// L (Command-L focuses the address bar).
    L,
    /// R (Command-R reloads).
    R,
    /// `[` (Command-`[` goes back).
    LeftBracket,
}

/// macOS's virtual key codes for [`Named`], from `<HIToolbox/Events.h>`.
pub const MACOS: [(u32, Named); 13] = [
    (0x24, Named::Return),
    (0x35, Named::Escape),
    (0x33, Named::Backspace),
    (0x31, Named::Space),
    (0x74, Named::PageUp),
    (0x79, Named::PageDown),
    (0x7B, Named::Left),
    (0x7C, Named::Right),
    (0x7E, Named::Up),
    (0x7D, Named::Down),
    (0x25, Named::L),
    (0x0F, Named::R),
    (0x21, Named::LeftBracket),
];

/// Windows' virtual-key codes for [`Named`], from `<WinUser.h>`.
pub const WINDOWS: [(u32, Named); 13] = [
    (0x0D, Named::Return),
    (0x1B, Named::Escape),
    (0x08, Named::Backspace),
    (0x20, Named::Space),
    (0x21, Named::PageUp),
    (0x22, Named::PageDown),
    (0x25, Named::Left),
    (0x27, Named::Right),
    (0x26, Named::Up),
    (0x28, Named::Down),
    (0x4C, Named::L),
    (0x52, Named::R),
    (0xDB, Named::LeftBracket),
];

/// X11's keysyms for [`Named`], from `<X11/keysymdef.h>`: the unshifted keysym
/// of the key.
pub const X11: [(u32, Named); 13] = [
    (0xFF0D, Named::Return),
    (0xFF1B, Named::Escape),
    (0xFF08, Named::Backspace),
    (0x0020, Named::Space),
    (0xFF55, Named::PageUp),
    (0xFF56, Named::PageDown),
    (0xFF51, Named::Left),
    (0xFF53, Named::Right),
    (0xFF52, Named::Up),
    (0xFF54, Named::Down),
    (0x006C, Named::L),
    (0x0072, Named::R),
    (0x005B, Named::LeftBracket),
];

/// The key `code` names in `table`.
pub fn named_in(table: &[(u32, Named)], code: u32) -> Option<Named> {
    table.iter().find(|(c, _)| *c == code).map(|(_, n)| *n)
}

/// The key `code` names on this platform (none on a platform with no window).
pub fn named(code: u32) -> Option<Named> {
    if cfg!(target_os = "macos") {
        named_in(&MACOS, code)
    } else if cfg!(windows) {
        named_in(&WINDOWS, code)
    } else if cfg!(target_os = "linux") {
        named_in(&X11, code)
    } else {
        None
    }
}

impl Named {
    /// The DOM `keyCode` of the key (UI Events KeyboardEvent code values, legacy
    /// `keyCode` table), which `browse` sends to the renderer in an `Input` of kind
    /// key for the keys that scroll.
    pub fn dom_key_code(self) -> u32 {
        match self {
            Named::Backspace => 8,
            Named::Return => 13,
            Named::Escape => 27,
            Named::Space => 32,
            Named::PageUp => 33,
            Named::PageDown => 34,
            Named::Left => 37,
            Named::Up => 38,
            Named::Right => 39,
            Named::Down => 40,
            Named::L => 76,
            Named::R => 82,
            Named::LeftBracket => 219,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{MACOS, Named, WINDOWS, X11, named_in};

    #[test]
    fn each_table_names_every_key_once() {
        for table in [MACOS, WINDOWS, X11] {
            for (i, (code, name)) in table.iter().enumerate() {
                assert_eq!(named_in(&table, *code), Some(*name));
                let same_name = table.iter().filter(|(_, n)| n == name).count();
                assert_eq!(same_name, 1, "{name:?} at {i}");
            }
        }
    }

    #[test]
    fn the_shortcut_keys_are_where_the_headers_put_them() {
        assert_eq!(named_in(&MACOS, 0x25), Some(Named::L));
        assert_eq!(named_in(&MACOS, 0x0F), Some(Named::R));
        assert_eq!(named_in(&MACOS, 0x21), Some(Named::LeftBracket));
        assert_eq!(named_in(&MACOS, 0x00), None);
        assert_eq!(named_in(&WINDOWS, 0xDB), Some(Named::LeftBracket));
        assert_eq!(named_in(&X11, 0x6C), Some(Named::L));
        assert_eq!(named_in(&X11, 0xFF56), Some(Named::PageDown));
        assert_eq!(named_in(&X11, 0x4C), None);
        assert_eq!(Named::Down.dom_key_code(), 40);
    }
}
