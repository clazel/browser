//! Text field editing: the pure state of one text control's value, its
//! caret and its selection (phase-6.md item 6.15; item 6.0(f)'s text
//! input).
//!
//! Sources: HTML §4.10.5.1.2 to §4.10.5.1.7 and §4.10.11 for what the value
//! of a text control is (newlines are stripped from a one-line field's
//! value by its value sanitization algorithm; a `textarea`'s API value has
//! LF newlines, "normalize newlines"), and the `maxlength` attribute
//! (§4.10.18.7 "Limiting user input length": "the maximum allowed value
//! length" counts the value's length in UTF-16 code units and constrains
//! what the user may enter). HTML does not specify how a caret and a
//! selection move; this module is the user agent's own, by the usual
//! conventions.
//!
//! Modelling choices (listed):
//! - The value is a vector of `char` (Unicode scalar values) and the caret
//!   and selection are indices between them, so Backspace removes one scalar
//!   value, not one grapheme cluster (no combining sequence or emoji
//!   sequence logic until Phase 8's text work).
//! - **`maxlength`** counts UTF-16 code units as HTML says; text that does
//!   not fit is cut after the last whole scalar value that does.
//! - **Selection** is the range between `anchor` and `caret`; Shift extends
//!   it, a movement without Shift collapses it (Left to its start, Right to
//!   its end). Words, double and triple clicks, "select all" and the clipboard
//!   are not there: no clipboard until the host offers one.
//! - **Home and End** go to the start and end of the line (the logical line:
//!   between newlines, not between wrapped rows); **Up and Down** in a
//!   `textarea` move between logical lines keeping the column (Up on the
//!   first line goes to the start, Down on the last to the end); in a
//!   one-line field they go to the start and the end.

/// One text control's editing state.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Field {
    /// The value.
    pub chars: Vec<char>,
    /// The caret: an index in `0..=chars.len()`.
    pub caret: usize,
    /// The other end of the selection: equal to `caret` when none.
    pub anchor: usize,
}

/// `text` as the control keeps it: a one-line field's value has no newline
/// (HTML's value sanitization algorithm "strip newlines"); a `textarea`'s
/// has LF ("normalize newlines": CRLF and CR become LF).
pub fn normalize(text: &str, multiline: bool) -> Vec<char> {
    let mut out = Vec::new();
    let mut it = text.chars().peekable();
    while let Some(c) = it.next() {
        if c == '\r' {
            if it.peek() == Some(&'\n') {
                it.next();
            }
            if multiline {
                out.push('\n');
            }
        } else if c == '\n' {
            if multiline {
                out.push('\n');
            }
        } else {
            out.push(c);
        }
    }
    out
}

impl Field {
    /// A field holding `text` with the caret at its end.
    pub fn new(chars: Vec<char>) -> Field {
        let n = chars.len();
        Field {
            chars,
            caret: n,
            anchor: n,
        }
    }

    /// The value as a string.
    pub fn text(&self) -> String {
        self.chars.iter().collect()
    }

    /// The selected range, `start < end`, if any.
    pub fn selection(&self) -> Option<(usize, usize)> {
        let (a, b) = (self.anchor.min(self.caret), self.anchor.max(self.caret));
        (a < b).then_some((a, b))
    }

    fn clamp(&mut self) {
        let n = self.chars.len();
        self.caret = self.caret.min(n);
        self.anchor = self.anchor.min(n);
    }

    fn collapse(&mut self, at: usize) {
        self.caret = at;
        self.anchor = at;
    }

    /// Moves the caret to `at`, keeping the anchor when `extend`.
    pub fn set_caret(&mut self, at: usize, extend: bool) {
        self.clamp();
        self.caret = at.min(self.chars.len());
        if !extend {
            self.anchor = self.caret;
        }
    }

    /// Removes the selection, leaving the caret where it was.
    fn remove_selection(&mut self) -> bool {
        self.clamp();
        let Some((a, b)) = self.selection() else {
            return false;
        };
        self.chars.drain(a..b);
        self.collapse(a);
        true
    }

    /// Types `text` (the user's input) over the selection, subject to the
    /// newline rule and to `max` (`maxlength`, in UTF-16 code units).
    /// Returns whether the value changed.
    pub fn insert(&mut self, text: &str, multiline: bool, max: Option<usize>) -> bool {
        self.clamp();
        let mut add = normalize(text, multiline);
        let removed = self.selection().map_or(0, |(a, b)| {
            self.chars
                .get(a..b)
                .map_or(0, |s| s.iter().map(|c| c.len_utf16()).sum::<usize>())
        });
        if let Some(m) = max {
            let have: usize = self.chars.iter().map(|c| c.len_utf16()).sum();
            let mut room = m.saturating_sub(have.saturating_sub(removed));
            let mut keep = 0usize;
            for c in &add {
                let w = c.len_utf16();
                if w > room {
                    break;
                }
                room = room.saturating_sub(w);
                keep = keep.saturating_add(1);
            }
            add.truncate(keep);
        }
        if add.is_empty() {
            return false;
        }
        self.remove_selection();
        let at = self.caret;
        let n = add.len();
        self.chars.splice(at..at, add);
        self.collapse(at.saturating_add(n));
        true
    }

    /// Backspace: the selection, else the character before the caret.
    pub fn backspace(&mut self) -> bool {
        if self.remove_selection() {
            return true;
        }
        if self.caret == 0 {
            return false;
        }
        let at = self.caret.saturating_sub(1);
        self.chars.remove(at);
        self.collapse(at);
        true
    }

    /// Delete: the selection, else the character after the caret.
    pub fn delete(&mut self) -> bool {
        if self.remove_selection() {
            return true;
        }
        if self.caret >= self.chars.len() {
            return false;
        }
        self.chars.remove(self.caret);
        self.collapse(self.caret);
        true
    }

    /// Left: one character back; with a selection and no Shift, to its
    /// start.
    pub fn left(&mut self, extend: bool) {
        self.clamp();
        if !extend && let Some((a, _)) = self.selection() {
            self.collapse(a);
            return;
        }
        self.set_caret(self.caret.saturating_sub(1), extend);
    }

    /// Right: one character on; with a selection and no Shift, to its end.
    pub fn right(&mut self, extend: bool) {
        self.clamp();
        if !extend && let Some((_, b)) = self.selection() {
            self.collapse(b);
            return;
        }
        self.set_caret(self.caret.saturating_add(1), extend);
    }

    /// The start of the logical line holding index `at`.
    fn line_start(&self, at: usize) -> usize {
        self.chars
            .get(..at.min(self.chars.len()))
            .and_then(|s| s.iter().rposition(|&c| c == '\n'))
            .map_or(0, |p| p.saturating_add(1))
    }

    /// The end of the logical line holding index `at` (before its newline).
    fn line_end(&self, at: usize) -> usize {
        let at = at.min(self.chars.len());
        self.chars
            .get(at..)
            .and_then(|s| s.iter().position(|&c| c == '\n'))
            .map_or(self.chars.len(), |p| at.saturating_add(p))
    }

    /// Home.
    pub fn home(&mut self, extend: bool) {
        self.clamp();
        self.set_caret(self.line_start(self.caret), extend);
    }

    /// End.
    pub fn end(&mut self, extend: bool) {
        self.clamp();
        self.set_caret(self.line_end(self.caret), extend);
    }

    /// Up (see the module's choice for `multiline == false`).
    pub fn up(&mut self, extend: bool, multiline: bool) {
        if !multiline {
            return self.home(extend);
        }
        self.clamp();
        let start = self.line_start(self.caret);
        if start == 0 {
            return self.set_caret(0, extend);
        }
        let col = self.caret.saturating_sub(start);
        let prev_end = start.saturating_sub(1);
        let prev_start = self.line_start(prev_end);
        let len = prev_end.saturating_sub(prev_start);
        self.set_caret(prev_start.saturating_add(col.min(len)), extend);
    }

    /// Down.
    pub fn down(&mut self, extend: bool, multiline: bool) {
        if !multiline {
            return self.end(extend);
        }
        self.clamp();
        let start = self.line_start(self.caret);
        let end = self.line_end(self.caret);
        if end >= self.chars.len() {
            return self.set_caret(self.chars.len(), extend);
        }
        let col = self.caret.saturating_sub(start);
        let next_start = end.saturating_add(1);
        let next_end = self.line_end(next_start);
        let len = next_end.saturating_sub(next_start);
        self.set_caret(next_start.saturating_add(col.min(len)), extend);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(s: &str) -> Field {
        Field::new(s.chars().collect())
    }

    #[test]
    fn insert_at_the_caret_and_over_a_selection() {
        let mut x = f("abcd");
        x.set_caret(2, false);
        assert!(x.insert("XY", false, None));
        assert_eq!((x.text().as_str(), x.caret), ("abXYcd", 4));
        x.set_caret(1, false);
        x.set_caret(5, true);
        assert_eq!(x.selection(), Some((1, 5)));
        assert!(x.insert("-", false, None));
        assert_eq!(
            (x.text().as_str(), x.caret, x.selection()),
            ("a-d", 2, None)
        );
    }

    #[test]
    fn newlines_follow_the_control_kind() {
        let mut one = f("");
        one.insert("a\r\nb\nc\rd", false, None);
        assert_eq!(one.text(), "abcd");
        let mut many = f("");
        many.insert("a\r\nb\nc\rd", true, None);
        assert_eq!(many.text(), "a\nb\nc\nd");
    }

    #[test]
    fn maxlength_counts_utf16_units_and_cuts_whole_scalars() {
        let mut x = f("ab");
        assert!(x.insert("cdef", false, Some(4)));
        assert_eq!(x.text(), "abcd");
        assert!(!x.insert("z", false, Some(4)));
        let mut y = f("a");
        // U+1F600 is two UTF-16 code units: it does not fit in the 2 left.
        assert!(y.insert("\u{1F600}\u{1F600}", false, Some(3)));
        assert_eq!(y.text(), "a\u{1F600}");
        // Replacing a selection frees its length.
        let mut z = f("abcd");
        z.set_caret(0, false);
        z.set_caret(4, true);
        assert!(z.insert("wxyz!", false, Some(4)));
        assert_eq!(z.text(), "wxyz");
    }

    #[test]
    fn backspace_and_delete() {
        let mut x = f("abc");
        assert!(x.backspace());
        assert_eq!(x.text(), "ab");
        x.set_caret(0, false);
        assert!(!x.backspace());
        assert!(x.delete());
        assert_eq!(x.text(), "b");
        x.set_caret(1, false);
        assert!(!x.delete());
        let mut y = f("abcd");
        y.set_caret(1, false);
        y.set_caret(3, true);
        assert!(y.delete());
        assert_eq!((y.text().as_str(), y.caret), ("ad", 1));
    }

    #[test]
    fn arrows_extend_and_collapse() {
        let mut x = f("abcd");
        x.set_caret(2, false);
        x.left(true);
        x.left(true);
        assert_eq!(x.selection(), Some((0, 2)));
        x.right(false);
        assert_eq!((x.caret, x.selection()), (2, None));
        x.left(true);
        x.left(false);
        assert_eq!((x.caret, x.selection()), (1, None));
        x.right(true);
        x.right(true);
        x.left(false);
        assert_eq!(x.caret, 1);
        x.home(true);
        assert_eq!(x.selection(), Some((0, 1)));
        x.end(false);
        assert_eq!(x.caret, 4);
    }

    #[test]
    fn lines_in_a_textarea() {
        let mut x = f("one\ntwo three\nx");
        x.set_caret(6, false);
        x.home(false);
        assert_eq!(x.caret, 4);
        x.end(false);
        assert_eq!(x.caret, 13);
        x.up(false, true);
        assert_eq!(x.caret, 3);
        x.up(false, true);
        assert_eq!(x.caret, 0);
        x.set_caret(5, false);
        x.down(false, true);
        assert_eq!(x.caret, 15);
        x.down(false, true);
        assert_eq!(x.caret, 15);
        x.set_caret(5, false);
        x.up(false, true);
        assert_eq!(x.caret, 1);
        let mut one = f("abc");
        one.set_caret(1, false);
        one.down(false, false);
        assert_eq!(one.caret, 3);
        one.up(false, false);
        assert_eq!(one.caret, 0);
    }
}
