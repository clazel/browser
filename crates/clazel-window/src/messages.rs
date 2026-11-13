//! What a Win32 message means, as a pure function of its three numbers. The values
//! are from winuser.h; the field layouts from Microsoft Learn's page for each
//! message (`WM_LBUTTONDOWN`, `WM_MOUSEWHEEL`, `WM_KEYDOWN`, `WM_CHAR`, `WM_PAINT`).

use crate::Event;

const WM_PAINT: u32 = 0x000F;
const WM_KEYDOWN: u32 = 0x0100;
const WM_CHAR: u32 = 0x0102;
const WM_LBUTTONDOWN: u32 = 0x0201;
const WM_MOUSEWHEEL: u32 = 0x020A;

/// A message's meaning. A wheel's point is on the screen, not in the client area,
/// so it comes back as [`Translated::WheelOnScreen`] for the caller to convert.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Translated {
    /// Ready to report.
    Event(Event),
    /// A wheel turn with the pointer at this point of the screen.
    WheelOnScreen {
        /// As [`Event::Wheel`].
        delta: i16,
        /// From the screen's left edge.
        x: i32,
        /// From the screen's top edge.
        y: i32,
    },
}

/// The low 16 bits as a signed number: GET_X_LPARAM.
fn low_i16(v: isize) -> i16 {
    v as u16 as i16
}

/// Bits 16 to 31 as a signed number: GET_Y_LPARAM and GET_WHEEL_DELTA_WPARAM.
fn high_i16(v: isize) -> i16 {
    (v >> 16) as u16 as i16
}

/// The message's meaning, or `None` for one a window does not report.
pub fn translate(message: u32, w_param: usize, l_param: isize) -> Option<Translated> {
    let x = i32::from(low_i16(l_param));
    let y = i32::from(high_i16(l_param));
    match message {
        WM_PAINT => Some(Translated::Event(Event::Expose)),
        WM_LBUTTONDOWN => Some(Translated::Event(Event::Click { x, y })),
        WM_MOUSEWHEEL => Some(Translated::WheelOnScreen {
            delta: high_i16(w_param as isize),
            x,
            y,
        }),
        WM_KEYDOWN => Some(Translated::Event(Event::Key {
            code: w_param as u32,
            command: false,
        })),
        WM_CHAR => Some(Translated::Event(Event::Char {
            unit: w_param as u16,
        })),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn event(e: Event) -> Option<Translated> {
        Some(Translated::Event(e))
    }

    #[test]
    fn paint() {
        assert_eq!(translate(WM_PAINT, 0, 0), event(Event::Expose));
    }

    #[test]
    fn a_click_unpacks_x_low_and_y_high() {
        assert_eq!(
            translate(WM_LBUTTONDOWN, 0x0001, 0x0064_0032),
            event(Event::Click { x: 50, y: 100 })
        );
    }

    #[test]
    fn coordinates_are_signed() {
        // A window on a monitor to the left has negative screen coordinates, so
        // LOWORD and HIWORD alone would be wrong (Microsoft Learn, WM_LBUTTONDOWN).
        assert_eq!(
            translate(WM_LBUTTONDOWN, 0, 0xFFFE_FFFF_u32 as isize),
            event(Event::Click { x: -1, y: -2 })
        );
    }

    #[test]
    fn a_wheel_notch_each_way() {
        assert_eq!(
            translate(WM_MOUSEWHEEL, 0x0078_0000, 0x0064_0032),
            Some(Translated::WheelOnScreen {
                delta: 120,
                x: 50,
                y: 100
            })
        );
        assert_eq!(
            translate(WM_MOUSEWHEEL, 0xFF88_0000, 0),
            Some(Translated::WheelOnScreen {
                delta: -120,
                x: 0,
                y: 0
            })
        );
    }

    #[test]
    fn wheel_key_state_in_the_low_word_is_ignored() {
        // MK_CONTROL in the low word changes nothing.
        assert_eq!(
            translate(WM_MOUSEWHEEL, 0x0078_0008, 0),
            Some(Translated::WheelOnScreen {
                delta: 120,
                x: 0,
                y: 0
            })
        );
    }

    #[test]
    fn keys_and_characters() {
        assert_eq!(
            translate(WM_KEYDOWN, 0x41, 0),
            event(Event::Key {
                code: 0x41,
                command: false
            })
        );
        assert_eq!(
            translate(WM_CHAR, 0xD83D, 0),
            event(Event::Char { unit: 0xD83D })
        );
    }

    #[test]
    fn other_messages_mean_nothing() {
        assert_eq!(translate(0x0200, 0, 0), None); // WM_MOUSEMOVE
        assert_eq!(translate(0, usize::MAX, isize::MIN), None);
    }

    #[test]
    fn extreme_values_do_not_panic() {
        for message in [WM_LBUTTONDOWN, WM_MOUSEWHEEL, WM_KEYDOWN, WM_CHAR] {
            for w_param in [0, usize::MAX] {
                for l_param in [0, -1, isize::MIN, isize::MAX] {
                    assert!(translate(message, w_param, l_param).is_some());
                }
            }
        }
    }
}
