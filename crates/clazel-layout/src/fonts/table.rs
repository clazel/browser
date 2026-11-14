//! The font table of decision 5.0(c): faces, each with a family name,
//! weight, width and style.

use clazel_font::Face;

/// `name` ID 1, font family name.
const NAME_FAMILY: u16 = 1;
/// `name` ID 16, typographic family name.
const NAME_TYPOGRAPHIC_FAMILY: u16 = 16;
/// `OS/2.fsSelection` bit 0, `ITALIC`.
const FS_ITALIC: u16 = 1 << 0;
/// `OS/2.fsSelection` bit 9, `OBLIQUE`.
const FS_OBLIQUE: u16 = 1 << 9;
/// `head.macStyle` bit 0, bold.
const MAC_BOLD: u16 = 1 << 0;
/// `head.macStyle` bit 1, italic.
const MAC_ITALIC: u16 = 1 << 1;

/// `font-stretch: normal` on the 1 to 9 scale of `OS/2.usWidthClass`.
pub const STRETCH_NORMAL: u8 = 5;

/// A face's style: the values of `font-style` (CSS Fonts 3 §3.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FontStyle {
    /// `normal`.
    Normal,
    /// `italic`.
    Italic,
    /// `oblique`.
    Oblique,
}

/// A face's index in its [`FontTable`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FaceId(pub usize);

/// What matching knows about a face.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FaceInfo {
    /// Family name.
    pub family: String,
    /// Weight, 1 to 1000 (`font-weight`'s numbers; `OS/2.usWeightClass`).
    pub weight: u16,
    /// Width, 1 (`ultra-condensed`) to 9 (`ultra-expanded`), 5 being
    /// `normal` (`font-stretch`'s keywords in order; `OS/2.usWidthClass`).
    pub stretch: u8,
    /// Style.
    pub style: FontStyle,
}

impl FaceInfo {
    /// A face's description from its `name`, `OS/2` and `head` tables (see
    /// the modelling choices in [`super`]). `None` if it has no family name
    /// we can read, or a table it has cannot be read.
    pub fn from_face(face: &Face<'_>) -> Option<Self> {
        let name = face.name().ok()??;
        let family = match name.get(NAME_TYPOGRAPHIC_FAMILY).ok()? {
            Some(f) if !f.is_empty() => f,
            _ => name.get(NAME_FAMILY).ok()??,
        };
        if family.is_empty() {
            return None;
        }
        let (weight, stretch, style) = match face.os2().ok()? {
            Some(os2) => {
                let stretch = u8::try_from(os2.width_class)
                    .ok()
                    .filter(|w| (1..=9).contains(w))
                    .unwrap_or(STRETCH_NORMAL);
                let style = if os2.fs_selection & FS_OBLIQUE != 0 {
                    FontStyle::Oblique
                } else if os2.fs_selection & FS_ITALIC != 0 {
                    FontStyle::Italic
                } else {
                    FontStyle::Normal
                };
                (os2.weight_class, stretch, style)
            }
            None => {
                let mac = face.head.mac_style;
                let weight = if mac & MAC_BOLD != 0 { 700 } else { 400 };
                let style = if mac & MAC_ITALIC != 0 {
                    FontStyle::Italic
                } else {
                    FontStyle::Normal
                };
                (weight, STRETCH_NORMAL, style)
            }
        };
        Some(Self {
            family,
            weight,
            stretch,
            style,
        })
    }
}

/// Family names compared as §5.1 asks, approximated by lowercasing (a
/// modelling choice in [`super`]).
pub fn same_family(a: &str, b: &str) -> bool {
    a == b || a.to_lowercase() == b.to_lowercase()
}

/// Every face the renderer may draw with, in the order they were added.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FontTable {
    faces: Vec<FaceInfo>,
}

impl FontTable {
    /// An empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a face; its id is its position.
    pub fn push(&mut self, face: FaceInfo) -> FaceId {
        let id = FaceId(self.faces.len());
        self.faces.push(face);
        id
    }

    /// Face `id`.
    pub fn get(&self, id: FaceId) -> Option<&FaceInfo> {
        self.faces.get(id.0)
    }

    /// Every face with its id.
    pub fn iter(&self) -> impl Iterator<Item = (FaceId, &FaceInfo)> {
        self.faces.iter().enumerate().map(|(i, f)| (FaceId(i), f))
    }

    /// The faces of family `family` (§5.1 caseless), in table order.
    pub fn family(&self, family: &str) -> Vec<(FaceId, &FaceInfo)> {
        self.iter()
            .filter(|(_, f)| same_family(&f.family, family))
            .collect()
    }

    /// Whether any face has family `family`.
    pub fn has_family(&self, family: &str) -> bool {
        self.faces.iter().any(|f| same_family(&f.family, family))
    }

    /// Each family once, in the order its first face was added.
    pub fn families(&self) -> Vec<&str> {
        let mut out: Vec<&str> = Vec::new();
        for f in &self.faces {
            if !out.iter().any(|g| same_family(g, &f.family)) {
                out.push(&f.family);
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn family_names_are_caseless() {
        assert!(same_family("DejaVu Serif", "dejavu serif"));
        assert!(same_family("ÉCOLE", "école"));
        assert!(!same_family("Arial", "Arial Black"));
        let mut t = FontTable::new();
        let face = |family: &str| FaceInfo {
            family: family.to_owned(),
            weight: 400,
            stretch: STRETCH_NORMAL,
            style: FontStyle::Normal,
        };
        t.push(face("Times"));
        t.push(face("Helvetica"));
        t.push(face("times"));
        assert_eq!(t.families(), ["Times", "Helvetica"]);
        assert_eq!(t.family("TIMES").len(), 2);
        assert!(t.has_family("helvetica"));
        assert!(!t.has_family("Menlo"));
    }
}
