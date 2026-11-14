//! What an AppKit event means, and where things go in a window's content area, as
//! pure functions that every target can test (phase-5.md item 5.21). The event
//! type values are from <AppKit/NSEvent.h>; AppKit's coordinates are points from
//! the bottom left, and [`Event`]'s are pixels from the top left.
//!
//! # Modelling choices (ours, each listed)
//!
//! - **Clicks and wheel turns count only inside the content area** and only for
//!   this window. A click on the title bar moves the window and is not reported.
//! - **Points to pixels**: a position is multiplied by the backing scale and
//!   rounded down, so pixel `x` covers `[x, x + 1)`; a size is rounded to the
//!   nearest pixel.
//! - **The wheel** is reported in [`Event::Wheel`]'s unit, 120 a notch. A mouse
//!   wheel's delta is in lines, one line taken as a notch, as Windows' notch is
//!   one step of the wheel. A trackpad's delta is in points (precise), 40 points
//!   taken as a notch, so 3 units a point (Windows' default notch scrolls three
//!   lines, and a line of text is about 13 points). The sign is AppKit's, which
//!   already follows the user's scrolling direction setting, so positive scrolls
//!   toward the top as [`Event::Wheel`] says. Horizontal scrolling is not
//!   reported, as on Windows.
//! - **Keys**: a key down is [`Event::Key`] with AppKit's virtual key code, then
//!   one [`Event::Char`] for each UTF-16 code unit it typed, as Windows sends
//!   `WM_KEYDOWN` then `WM_CHAR`. Not typed: the code units AppKit gives the
//!   function keys (U+F700 to U+F8FF, `NSUpArrowFunctionKey` and its neighbours,
//!   which `WM_CHAR` has no equivalent of), and anything typed with Command held,
//!   which is a shortcut, not text.
//! - **Which events go back to AppKit** ([`forward`]): all but key events. AppKit
//!   needs mouse events to move, resize and close the window; a key event it is
//!   given finds no view that wants it and beeps.
//! - **Closing** is seen as the window no longer being visible while neither
//!   minimised nor hidden with its application ([`is_closed`]); no delegate tells
//!   us.

use crate::Event;

/// `NSEventTypeLeftMouseDown`.
pub const LEFT_MOUSE_DOWN: usize = 1;
/// `NSEventTypeKeyDown`.
pub const KEY_DOWN: usize = 10;
/// `NSEventTypeKeyUp`.
pub const KEY_UP: usize = 11;
/// `NSEventTypeFlagsChanged`.
pub const FLAGS_CHANGED: usize = 12;
/// `NSEventTypeScrollWheel`.
pub const SCROLL_WHEEL: usize = 22;
/// `NSEventModifierFlagCommand`, `1 << 20`.
pub const COMMAND: usize = 0x0010_0000;

/// An event's fields, as `clazel_sys::macos::window::RawEvent` reads them, in
/// terms any target can build: what the recorded events of the tests are.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Recorded {
    /// `NSEventType`.
    pub kind: usize,
    /// `modifierFlags`.
    pub modifiers: usize,
    /// Whether the event's `window` is this window.
    pub this_window: bool,
    /// `locationInWindow`, points from the bottom left.
    pub location: Option<(f64, f64)>,
    /// `keyCode`.
    pub key_code: Option<u16>,
    /// `characters`, as UTF-16 code units.
    pub characters: Vec<u16>,
    /// `scrollingDeltaY` and `hasPreciseScrollingDeltas`.
    pub scroll_y: Option<(f64, bool)>,
}

/// The content area's size in points and the backing scale (pixels a point).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Geometry {
    /// Width in points.
    pub width: f64,
    /// Height in points.
    pub height: f64,
    /// `backingScaleFactor`.
    pub scale: f64,
}

impl Geometry {
    /// The content area's size in pixels.
    pub fn pixels(&self) -> (u32, u32) {
        (
            size_in_pixels(self.width, self.scale),
            size_in_pixels(self.height, self.scale),
        )
    }
}

/// A length of `points` at `scale`, in whole pixels: rounded, 0 for anything not
/// finite or not positive, and at most `u32::MAX`.
pub fn size_in_pixels(points: f64, scale: f64) -> u32 {
    let px = (points * scale).round();
    if px.is_finite() && px > 0.0 {
        // `as` saturates at u32::MAX.
        px as u32
    } else {
        0
    }
}

/// The dots per inch [`crate::Window::dpi`] reports, 96 being unscaled, as on
/// Windows: 192 for a scale of 2. `None` for a scale that is not finite and
/// positive.
pub fn dpi(scale: f64) -> Option<u32> {
    let d = (scale * 96.0).round();
    (d.is_finite() && d > 0.0).then_some(d as u32)
}

/// Whether AppKit should be given the event (see the module's modelling choices).
pub fn forward(kind: usize) -> bool {
    !matches!(kind, KEY_DOWN | KEY_UP | FLAGS_CHANGED)
}

/// Whether a window is closed, from what can be read of it.
pub fn is_closed(visible: bool, miniaturized: bool, app_hidden: bool) -> bool {
    !visible && !miniaturized && !app_hidden
}

/// A point in the window (points from the bottom left) as a pixel of the content
/// area (from the top left), if it is inside it.
pub fn content_pixel(at: (f64, f64), geometry: &Geometry) -> Option<(i32, i32)> {
    let (width, height) = geometry.pixels();
    let x = (at.0 * geometry.scale).floor();
    let y = ((geometry.height - at.1) * geometry.scale).floor();
    let inside = |v: f64, max: u32| v.is_finite() && v >= 0.0 && v < f64::from(max);
    if !inside(x, width) || !inside(y, height) {
        return None;
    }
    // Both are in [0, u32::MAX); `as` saturates at i32::MAX beyond that.
    Some((x as i32, y as i32))
}

/// A vertical scroll as [`Event::Wheel`]'s delta, 120 a notch, rounded and
/// clamped to `i16`; `None` if it rounds to nothing.
pub fn wheel_delta(dy: f64, precise: bool) -> Option<i16> {
    let per_unit = if precise { 3.0 } else { 120.0 };
    let d = (dy * per_unit).round();
    if !d.is_finite() || d == 0.0 {
        return None;
    }
    // `as` saturates at the ends of i16.
    Some(d as i16)
}

/// Whether a code unit is typed text: not one of AppKit's function-key units.
fn typed(unit: u16) -> bool {
    !(0xF700..=0xF8FF).contains(&unit)
}

/// What the event means for this window, in order; most events mean nothing.
pub fn translate(event: &Recorded, geometry: &Geometry) -> Vec<Event> {
    match event.kind {
        LEFT_MOUSE_DOWN if event.this_window => event
            .location
            .and_then(|at| content_pixel(at, geometry))
            .map(|(x, y)| Event::Click { x, y })
            .into_iter()
            .collect(),
        SCROLL_WHEEL if event.this_window => {
            let at = event.location.and_then(|at| content_pixel(at, geometry));
            let delta = event
                .scroll_y
                .and_then(|(dy, precise)| wheel_delta(dy, precise));
            match (at, delta) {
                (Some((x, y)), Some(delta)) => vec![Event::Wheel { delta, x, y }],
                _ => Vec::new(),
            }
        }
        KEY_DOWN => {
            let mut out = Vec::new();
            if let Some(code) = event.key_code {
                out.push(Event::Key {
                    code: u32::from(code),
                });
            }
            if event.modifiers & COMMAND == 0 {
                out.extend(
                    event
                        .characters
                        .iter()
                        .copied()
                        .filter(|&u| typed(u))
                        .map(|unit| Event::Char { unit }),
                );
            }
            out
        }
        _ => Vec::new(),
    }
}

/// A rectangle in points from the bottom left, as Core Animation places layers.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PointRect {
    /// From the left.
    pub x: f64,
    /// From the bottom.
    pub y: f64,
    /// Width.
    pub width: f64,
    /// Height.
    pub height: f64,
}

/// Where a layer goes to cover the pixels `x`, `y` (from the content area's top
/// left), `width` by `height`: the same rectangle in points from the bottom left.
pub fn layer_frame(x: u32, y: u32, width: u32, height: u32, geometry: &Geometry) -> PointRect {
    let scale = geometry.scale;
    let w = f64::from(width) / scale;
    let h = f64::from(height) / scale;
    PointRect {
        x: f64::from(x) / scale,
        y: geometry.height - f64::from(y) / scale - h,
        width: w,
        height: h,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Recorded events: the field values AppKit gives each kind of event, written
    // from <AppKit/NSEvent.h> and the virtual key codes of <HIToolbox/Events.h>
    // (kVK_ANSI_A 0x00, kVK_Return 0x24, kVK_UpArrow 0x7E), for a 400 by 300 point
    // content area at scale 2.
    const GEOMETRY: Geometry = Geometry {
        width: 400.0,
        height: 300.0,
        scale: 2.0,
    };

    fn click(x: f64, y: f64) -> Recorded {
        Recorded {
            kind: LEFT_MOUSE_DOWN,
            this_window: true,
            location: Some((x, y)),
            ..Recorded::default()
        }
    }

    fn key(code: u16, characters: &[u16], modifiers: usize) -> Recorded {
        Recorded {
            kind: KEY_DOWN,
            modifiers,
            key_code: Some(code),
            characters: characters.to_vec(),
            ..Recorded::default()
        }
    }

    fn wheel(dy: f64, precise: bool) -> Recorded {
        Recorded {
            kind: SCROLL_WHEEL,
            this_window: true,
            location: Some((10.0, 290.0)),
            scroll_y: Some((dy, precise)),
            ..Recorded::default()
        }
    }

    #[test]
    fn the_content_area_in_pixels() {
        assert_eq!(GEOMETRY.pixels(), (800, 600));
        assert_eq!(size_in_pixels(100.25, 2.0), 201);
        assert_eq!(size_in_pixels(f64::NAN, 2.0), 0);
        assert_eq!(size_in_pixels(-3.0, 1.0), 0);
        assert_eq!(size_in_pixels(1e12, 2.0), u32::MAX);
        assert_eq!(size_in_pixels(f64::MAX, 2.0), 0);
    }

    #[test]
    fn a_click_is_flipped_to_the_top_left_and_scaled() {
        assert_eq!(
            translate(&click(10.0, 290.0), &GEOMETRY),
            vec![Event::Click { x: 20, y: 20 }]
        );
        assert_eq!(
            translate(&click(0.0, 300.0), &GEOMETRY),
            vec![Event::Click { x: 0, y: 0 }]
        );
        // The last pixel of the bottom right corner.
        assert_eq!(
            translate(&click(399.9, 0.1), &GEOMETRY),
            vec![Event::Click { x: 799, y: 599 }]
        );
    }

    #[test]
    fn clicks_outside_the_content_area_or_window_mean_nothing() {
        // On the title bar, above the content view.
        assert!(translate(&click(10.0, 310.0), &GEOMETRY).is_empty());
        assert!(translate(&click(400.0, 10.0), &GEOMETRY).is_empty());
        assert!(translate(&click(-0.5, 10.0), &GEOMETRY).is_empty());
        assert!(translate(&click(10.0, 0.0), &GEOMETRY).is_empty());
        assert!(translate(&click(f64::NAN, 10.0), &GEOMETRY).is_empty());
        let other = Recorded {
            this_window: false,
            ..click(10.0, 10.0)
        };
        assert!(translate(&other, &GEOMETRY).is_empty());
        let nowhere = Recorded {
            location: None,
            ..click(10.0, 10.0)
        };
        assert!(translate(&nowhere, &GEOMETRY).is_empty());
    }

    #[test]
    fn a_wheel_notch_and_a_trackpad_swipe() {
        assert_eq!(
            translate(&wheel(1.0, false), &GEOMETRY),
            vec![Event::Wheel {
                delta: 120,
                x: 20,
                y: 20
            }]
        );
        assert_eq!(
            translate(&wheel(-2.5, false), &GEOMETRY),
            vec![Event::Wheel {
                delta: -300,
                x: 20,
                y: 20
            }]
        );
        assert_eq!(
            translate(&wheel(40.0, true), &GEOMETRY),
            vec![Event::Wheel {
                delta: 120,
                x: 20,
                y: 20
            }]
        );
        // Too small to round to a unit, or horizontal only.
        assert!(translate(&wheel(0.1, true), &GEOMETRY).is_empty());
        assert!(translate(&wheel(0.0, false), &GEOMETRY).is_empty());
    }

    #[test]
    fn wheel_deltas_saturate() {
        assert_eq!(wheel_delta(1e9, false), Some(i16::MAX));
        assert_eq!(wheel_delta(-1e9, true), Some(i16::MIN));
        assert_eq!(wheel_delta(f64::NAN, false), None);
        assert_eq!(wheel_delta(f64::INFINITY, false), None);
    }

    #[test]
    fn a_key_is_its_code_then_what_it_typed() {
        assert_eq!(
            translate(&key(0x00, &[0x61], 0), &GEOMETRY),
            vec![Event::Key { code: 0 }, Event::Char { unit: 0x61 }]
        );
        assert_eq!(
            translate(&key(0x24, &[0x0D], 0), &GEOMETRY),
            vec![Event::Key { code: 0x24 }, Event::Char { unit: 0x0D }]
        );
        // A character outside the BMP is two code units, as on Windows.
        assert_eq!(
            translate(&key(0x00, &[0xD83D, 0xDE00], 0), &GEOMETRY),
            vec![
                Event::Key { code: 0 },
                Event::Char { unit: 0xD83D },
                Event::Char { unit: 0xDE00 }
            ]
        );
    }

    #[test]
    fn function_keys_and_shortcuts_type_nothing() {
        // The up arrow's characters are NSUpArrowFunctionKey, U+F700.
        assert_eq!(
            translate(&key(0x7E, &[0xF700], 0x00A0_0000), &GEOMETRY),
            vec![Event::Key { code: 0x7E }]
        );
        // Command-L.
        assert_eq!(
            translate(&key(0x25, &[0x6C], COMMAND), &GEOMETRY),
            vec![Event::Key { code: 0x25 }]
        );
    }

    #[test]
    fn key_ups_and_other_events_mean_nothing() {
        let up = Recorded {
            kind: KEY_UP,
            ..key(0x00, &[0x61], 0)
        };
        assert!(translate(&up, &GEOMETRY).is_empty());
        for kind in [0, 2, 3, 5, 6, 9, 12, 13, 15, 25, usize::MAX] {
            let e = Recorded {
                kind,
                this_window: true,
                location: Some((1.0, 1.0)),
                ..Recorded::default()
            };
            assert!(translate(&e, &GEOMETRY).is_empty(), "{kind}");
        }
    }

    #[test]
    fn key_events_stay_with_us_and_the_rest_go_to_appkit() {
        assert!(!forward(KEY_DOWN) && !forward(KEY_UP) && !forward(FLAGS_CHANGED));
        for kind in [LEFT_MOUSE_DOWN, 2, 6, SCROLL_WHEEL, 13, 15, 0] {
            assert!(forward(kind), "{kind}");
        }
    }

    #[test]
    fn closed_means_gone_rather_than_minimised_or_hidden() {
        assert!(is_closed(false, false, false));
        assert!(!is_closed(true, false, false));
        assert!(!is_closed(false, true, false));
        assert!(!is_closed(false, false, true));
    }

    #[test]
    fn dpi_follows_the_scale() {
        assert_eq!(dpi(1.0), Some(96));
        assert_eq!(dpi(2.0), Some(192));
        assert_eq!(dpi(0.0), None);
        assert_eq!(dpi(f64::NAN), None);
    }

    #[test]
    fn layers_are_placed_from_the_top_left() {
        // The full content area.
        assert_eq!(
            layer_frame(0, 0, 800, 600, &GEOMETRY),
            PointRect {
                x: 0.0,
                y: 0.0,
                width: 400.0,
                height: 300.0
            }
        );
        // A 40 pixel strip at the top.
        assert_eq!(
            layer_frame(0, 0, 800, 40, &GEOMETRY),
            PointRect {
                x: 0.0,
                y: 280.0,
                width: 400.0,
                height: 20.0
            }
        );
        // The page below it.
        assert_eq!(
            layer_frame(0, 40, 800, 560, &GEOMETRY),
            PointRect {
                x: 0.0,
                y: 0.0,
                width: 400.0,
                height: 280.0
            }
        );
    }
}
