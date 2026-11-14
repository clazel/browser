//! Generic families and the fallback list, per OS (decision 5.0(c), S3;
//! CSS Fonts 3 §5.2 steps 2 and 7).
//!
//! Each list is tried in order and the first family present in the font
//! table is used, so a list may name families an installation lacks. The
//! families are those decision 5.0(c) found at the known paths (S1): on
//! macOS `/System/Library/Fonts/` and `Supplemental/`, on Linux
//! `/usr/share/fonts/` with DejaVu or Liberation, and the standard Windows
//! families in `C:\Windows\Fonts`. CFF-only families (decision 5.0(c), C1)
//! are not listed: a face of theirs is never in the table.
//!
//! The bundled family that S3 adds as the last resort of every list is not
//! chosen yet (item 5.1 proposes one; committing a font file is the
//! maintainer's call), so it is a parameter: [`Generics::with_bundled`].

use super::table::FontTable;

/// A generic family keyword of `font-family` (CSS Fonts 3 §3.1.1) that this
/// phase maps; decision 5.0(c) maps these three.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Generic {
    /// `serif`.
    Serif,
    /// `sans-serif`.
    SansSerif,
    /// `monospace`.
    Monospace,
}

/// An operating system with a family table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Os {
    /// macOS.
    MacOs,
    /// Linux and other Unix systems with `/usr/share/fonts`.
    Linux,
    /// Windows.
    Windows,
}

impl Os {
    /// The OS this was compiled for (Linux for every Unix but macOS).
    pub const fn current() -> Self {
        if cfg!(target_os = "macos") {
            Self::MacOs
        } else if cfg!(target_os = "windows") {
            Self::Windows
        } else {
            Self::Linux
        }
    }
}

/// The families each generic keyword names, and the fallback list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generics {
    /// `serif`, in order of preference.
    pub serif: Vec<String>,
    /// `sans-serif`.
    pub sans_serif: Vec<String>,
    /// `monospace`.
    pub monospace: Vec<String>,
    /// Step 7's system font fallback, before the rest of the table.
    pub fallback: Vec<String>,
}

fn owned(names: &[&str]) -> Vec<String> {
    names.iter().map(|s| (*s).to_owned()).collect()
}

impl Generics {
    /// The fixed table for `os`.
    pub fn for_os(os: Os) -> Self {
        let (serif, sans, mono, fallback): (&[&str], &[&str], &[&str], &[&str]) = match os {
            // /System/Library/Fonts: Times.ttc, Helvetica.ttc, Menlo.ttc,
            // Courier.ttc, LucidaGrande.ttc, Apple Symbols.ttf, Geneva.ttf;
            // Supplemental/: Times New Roman, Arial, Verdana, Courier New,
            // Arial Unicode.
            Os::MacOs => (
                &["Times", "Times New Roman"],
                &["Helvetica", "Arial", "Verdana"],
                &["Menlo", "Courier", "Courier New"],
                &[
                    "Helvetica",
                    "Lucida Grande",
                    "Geneva",
                    "Arial Unicode MS",
                    "Apple Symbols",
                ],
            ),
            Os::Linux => (
                &["DejaVu Serif", "Liberation Serif"],
                &["DejaVu Sans", "Liberation Sans"],
                &["DejaVu Sans Mono", "Liberation Mono"],
                &["DejaVu Sans", "Liberation Sans", "FreeSans"],
            ),
            Os::Windows => (
                &["Times New Roman"],
                &["Arial"],
                &["Consolas", "Courier New"],
                &["Arial", "Segoe UI", "Segoe UI Symbol", "Arial Unicode MS"],
            ),
        };
        Self {
            serif: owned(serif),
            sans_serif: owned(sans),
            monospace: owned(mono),
            fallback: owned(fallback),
        }
    }

    /// The table for the OS this was compiled for.
    pub fn current() -> Self {
        Self::for_os(Os::current())
    }

    /// Append the bundled family (S3's fallback) to every list: `serif`,
    /// `sans` and `mono` are its three families, and all three join the
    /// fallback list, sans first.
    pub fn with_bundled(mut self, serif: &str, sans: &str, mono: &str) -> Self {
        self.serif.push(serif.to_owned());
        self.sans_serif.push(sans.to_owned());
        self.monospace.push(mono.to_owned());
        self.fallback
            .extend([sans, serif, mono].iter().map(|s| (*s).to_owned()));
        self
    }

    /// The families `generic` names.
    pub fn names(&self, generic: Generic) -> &[String] {
        match generic {
            Generic::Serif => &self.serif,
            Generic::SansSerif => &self.sans_serif,
            Generic::Monospace => &self.monospace,
        }
    }

    /// CSS Fonts 3 §5.2 step 2: "the user agent looks up the appropriate
    /// font family name to be used" for a generic family: here the first
    /// family of its list that `table` has.
    pub fn resolve<'a>(&'a self, generic: Generic, table: &FontTable) -> Option<&'a str> {
        self.names(generic)
            .iter()
            .find(|f| table.has_family(f))
            .map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fonts::table::{FaceInfo, FontStyle, STRETCH_NORMAL};

    fn face(family: &str) -> FaceInfo {
        FaceInfo {
            family: family.to_owned(),
            weight: 400,
            stretch: STRETCH_NORMAL,
            style: FontStyle::Normal,
        }
    }

    #[test]
    fn step_2_takes_the_first_family_present() {
        let g = Generics::for_os(Os::Linux);
        let mut t = FontTable::new();
        t.push(face("Liberation Serif"));
        assert_eq!(g.resolve(Generic::Serif, &t), Some("Liberation Serif"));
        t.push(face("dejavu serif"));
        assert_eq!(g.resolve(Generic::Serif, &t), Some("DejaVu Serif"));
        assert_eq!(g.resolve(Generic::Monospace, &t), None);
    }

    #[test]
    fn every_os_maps_the_three_generics() {
        for os in [Os::MacOs, Os::Linux, Os::Windows] {
            let g = Generics::for_os(os);
            for generic in [Generic::Serif, Generic::SansSerif, Generic::Monospace] {
                assert!(!g.names(generic).is_empty(), "{os:?} {generic:?}");
            }
            assert!(!g.fallback.is_empty());
        }
        assert_eq!(
            Generics::for_os(Os::MacOs).resolve(Generic::SansSerif, &FontTable::new()),
            None
        );
    }

    #[test]
    fn bundled_family_is_the_last_resort() {
        let g = Generics::for_os(Os::Windows).with_bundled("B Serif", "B Sans", "B Mono");
        assert_eq!(g.serif.last().map(String::as_str), Some("B Serif"));
        assert_eq!(g.sans_serif.last().map(String::as_str), Some("B Sans"));
        assert_eq!(g.monospace.last().map(String::as_str), Some("B Mono"));
        let n = g.fallback.len();
        assert_eq!(
            g.fallback.get(n.saturating_sub(3)..),
            Some(&owned(&["B Sans", "B Serif", "B Mono"])[..])
        );
        let mut t = FontTable::new();
        t.push(face("B Sans"));
        assert_eq!(g.resolve(Generic::SansSerif, &t), Some("B Sans"));
    }
}
