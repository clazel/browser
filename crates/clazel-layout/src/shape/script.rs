//! The two character properties the shaper reads: a run's script, which
//! picks the `GPOS` script table, and whether a character is a combining
//! mark, which gets a zero advance and is skipped by pair kerning.
//!
//! Both are hand-written block tables for the three scripts of decision
//! 5.0(c), H1 (Latin, Greek, Cyrillic), listed in [`super`]'s modelling
//! choices: they approximate Unicode's `Scripts.txt` (UAX #24) and
//! `General_Category` (`Mn`, `Me`) for those scripts only.

use clazel_font::Tag;

/// The script of a run, as far as shaping needs it: which `GPOS`
/// ScriptRecord to use (OpenType 1.9, chapter2, "Script List Table and
/// Script Record"; the tags are from the "Script Tags" registry,
/// <https://learn.microsoft.com/en-us/typography/opentype/otspec190/scripttags>).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Script {
    /// `latn`.
    Latin,
    /// `grek`.
    Greek,
    /// `cyrl`.
    Cyrillic,
    /// No script of H1 was found: the `DFLT` script table is used.
    Other,
}

impl Script {
    /// The script tag. [`Script::Other`] is `DFLT`, which chapter2 says
    /// "an application should use … if there is not a script table
    /// associated with the specific script of the text being formatted".
    pub fn tag(self) -> Tag {
        match self {
            Self::Latin => Tag(*b"latn"),
            Self::Greek => Tag(*b"grek"),
            Self::Cyrillic => Tag(*b"cyrl"),
            Self::Other => clazel_font::layout::DFLT,
        }
    }

    /// The script of `c`, or `None` if it is in none of the blocks below
    /// (punctuation, digits, spaces and combining marks, which Unicode
    /// gives the `Common` or `Inherited` script, among everything else).
    pub fn of_char(c: char) -> Option<Self> {
        match u32::from(c) {
            0x41..=0x5A
            | 0x61..=0x7A
            | 0xAA
            | 0xBA
            | 0xC0..=0xD6
            | 0xD8..=0xF6
            | 0xF8..=0x2AF
            | 0x1D00..=0x1D25
            | 0x1E00..=0x1EFF
            | 0x2C60..=0x2C7F
            | 0xA722..=0xA787
            | 0xA78B..=0xA7FF
            | 0xAB30..=0xAB5A
            | 0xFB00..=0xFB06
            | 0xFF21..=0xFF3A
            | 0xFF41..=0xFF5A => Some(Self::Latin),
            0x370..=0x373
            | 0x375..=0x377
            | 0x37A..=0x37D
            | 0x37F
            | 0x384
            | 0x386
            | 0x388..=0x3E1
            | 0x3F0..=0x3FF
            | 0x1F00..=0x1FFF => Some(Self::Greek),
            0x400..=0x482
            | 0x48A..=0x52F
            | 0x1C80..=0x1C8F
            | 0xA640..=0xA66E
            | 0xA673
            | 0xA67E..=0xA69D => Some(Self::Cyrillic),
            _ => None,
        }
    }

    /// The script of a run: that of its first character with one, as
    /// HarfBuzz's `guess_segment_properties` takes the first character
    /// whose script is neither `Common` nor `Inherited`; [`Script::Other`]
    /// if none has one.
    pub fn of_text(text: &str) -> Self {
        text.chars().find_map(Self::of_char).unwrap_or(Self::Other)
    }
}

/// Whether `c` is a combining mark: in one of the blocks of combining
/// marks that H1's scripts use, whose assigned characters are all
/// `General_Category` `Mn` (nonspacing) or `Me` (enclosing).
pub fn is_combining_mark(c: char) -> bool {
    matches!(
        u32::from(c),
        // Combining Diacritical Marks.
        0x300..=0x36F
            // Cyrillic combining marks (titlo, palatalization, …).
            | 0x483..=0x489
            // Combining Diacritical Marks Extended.
            | 0x1AB0..=0x1AFF
            // Combining Diacritical Marks Supplement.
            | 0x1DC0..=0x1DFF
            // Combining Diacritical Marks for Symbols.
            | 0x20D0..=0x20FF
            // Cyrillic Extended-A (combining letters) and Cyrillic
            // Extended-B's combining marks.
            | 0x2DE0..=0x2DFF
            | 0xA66F..=0xA672
            | 0xA674..=0xA67D
            | 0xA69E..=0xA69F
            // Combining Half Marks.
            | 0xFE20..=0xFE2F
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scripts() {
        assert_eq!(Script::of_text("Hello"), Script::Latin);
        assert_eq!(Script::of_text("12, Ωμέγα"), Script::Greek);
        assert_eq!(Script::of_text(" — Привет"), Script::Cyrillic);
        assert_eq!(Script::of_text("1234 !?"), Script::Other);
        assert_eq!(Script::of_text(""), Script::Other);
        // A combining mark has no script of its own.
        assert_eq!(Script::of_text("\u{301}Ж"), Script::Cyrillic);
        assert_eq!(Script::of_char('×'), None);
        assert_eq!(Script::of_char('ÿ'), Some(Script::Latin));
        assert_eq!(Script::Other.tag(), Tag(*b"DFLT"));
    }

    #[test]
    fn marks() {
        assert!(is_combining_mark('\u{301}'));
        assert!(is_combining_mark('\u{483}'));
        assert!(!is_combining_mark('a'));
        assert!(!is_combining_mark('\u{2DF}'));
        assert!(!is_combining_mark('\u{370}'));
    }
}
