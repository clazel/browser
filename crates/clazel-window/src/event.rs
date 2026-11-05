//! What a window reports, in terms of no particular platform.

/// One thing that happened to a window.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// Part of the window needs drawing again.
    Expose,
    /// The client area is now this many pixels.
    Resized {
        /// Its width.
        width: u32,
        /// Its height.
        height: u32,
    },
    /// The left button went down at this point of the client area.
    Click {
        /// From the left edge.
        x: i32,
        /// From the top edge.
        y: i32,
    },
    /// The wheel turned with the pointer at this point of the client area.
    Wheel {
        /// Positive is away from the user; one notch is 120.
        delta: i16,
        /// From the left edge.
        x: i32,
        /// From the top edge.
        y: i32,
    },
    /// A key went down.
    Key {
        /// The platform's key code.
        code: u32,
    },
    /// A UTF-16 code unit was typed. A character outside the BMP arrives as two.
    Char {
        /// The code unit.
        unit: u16,
    },
    /// The window is gone. Nothing follows this.
    Closed,
}
