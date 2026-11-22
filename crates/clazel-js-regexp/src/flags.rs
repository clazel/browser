//! The flags of a regular expression (§22.2.3.4† RegExpInitialize, §13.2.7.1†).

use crate::error::FlagsError;

/// The eight flags. The parser reads only [`Flags::unicode`] and
/// [`Flags::unicode_sets`]; the others are the matcher's.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Flags {
    /// `d`: match indices.
    pub has_indices: bool,
    /// `g`: global.
    pub global: bool,
    /// `i`: ignore case.
    pub ignore_case: bool,
    /// `m`: multiline.
    pub multiline: bool,
    /// `s`: dot matches line terminators.
    pub dot_all: bool,
    /// `u`: Unicode mode.
    pub unicode: bool,
    /// `v`: Unicode sets mode.
    pub unicode_sets: bool,
    /// `y`: sticky.
    pub sticky: bool,
}

impl Flags {
    /// Reads a flag string (UTF-16 code units).
    ///
    /// ECMA-262 §13.2.7.1† Static Semantics: Early Errors: the text may hold
    /// only `d g i m s u v y`, each at most once; RegExpInitialize §22.2.3.4†
    /// adds: not both `u` and `v`.
    ///
    /// # Errors
    ///
    /// [`FlagsError`], as above.
    pub fn parse(text: &[u16]) -> Result<Flags, FlagsError> {
        let mut f = Flags::default();
        for &unit in text {
            let slot = match unit {
                0x64 => &mut f.has_indices,
                0x67 => &mut f.global,
                0x69 => &mut f.ignore_case,
                0x6D => &mut f.multiline,
                0x73 => &mut f.dot_all,
                0x75 => &mut f.unicode,
                0x76 => &mut f.unicode_sets,
                0x79 => &mut f.sticky,
                _ => return Err(FlagsError::Invalid),
            };
            if *slot {
                return Err(FlagsError::Duplicate);
            }
            *slot = true;
        }
        if f.unicode && f.unicode_sets {
            return Err(FlagsError::UnicodeAndUnicodeSets);
        }
        Ok(f)
    }

    /// Whether the pattern is parsed as code points with the `[+UnicodeMode]`
    /// grammar: `u` or `v` is set.
    #[must_use]
    pub fn unicode_mode(&self) -> bool {
        self.unicode || self.unicode_sets
    }
}
