//! The renderer's fonts (phase-5.md item 5.20, decision 5.0(c)): font files
//! read before the sandbox is entered, as faces for layout (item 5.10's
//! table and matching, 5.11's shaping) and outlines for glyph masks (5.17).
//!
//! Modelling choices: `mod.rs`'s "Fonts". A file's bytes are leaked once,
//! so its faces borrow them for the life of the process (the renderer never
//! loads a font again: it cannot open a file once sandboxed).

use std::path::Path;

use clazel_font::Face;
use clazel_layout::flow::{BoxFont, FaceFonts, FontMetrics, ShapedGlyph, TextFns};
use clazel_layout::fonts::{FaceInfo, FontTable, Generics};
use clazel_style::cascade::computed::{ComputedStyle, Family};

/// The faces the renderer has.
pub struct Fonts {
    /// The faces, indexed like the table.
    pub faces: Vec<Face<'static>>,
    /// Item 5.10's table of them.
    pub table: FontTable,
    /// The generic families for this OS.
    pub generics: Generics,
}

/// The most bytes of one font file read (a large CJK face is about 30 MiB).
pub const MAX_FONT_FILE: u64 = 64 * 1024 * 1024;

impl Fonts {
    /// No face: layout in em boxes, no text drawn.
    pub fn none() -> Fonts {
        Fonts {
            faces: Vec::new(),
            table: FontTable::new(),
            generics: Generics::current(),
        }
    }

    /// The first face of each file of `files` (bytes), skipping any that is
    /// not a face item 5.9 reads.
    pub fn from_bytes(files: Vec<Vec<u8>>) -> Fonts {
        Fonts::from_static(
            files
                .into_iter()
                .map(|bytes| -> &'static [u8] { Box::leak(bytes.into_boxed_slice()) })
                .collect(),
        )
    }

    /// As [`Fonts::from_bytes`], over bytes that already live for the whole
    /// process (`include_bytes!`, or a file leaked once), so nothing is
    /// copied or leaked here.
    pub fn from_static(files: Vec<&'static [u8]>) -> Fonts {
        let mut f = Fonts::none();
        for data in files {
            let Ok(face) = Face::parse(data, 0) else {
                continue;
            };
            let Some(info) = FaceInfo::from_face(&face) else {
                continue;
            };
            f.table.push(info);
            f.faces.push(face);
        }
        f
    }

    /// The files at `paths`, read now (before the sandbox); a file that
    /// cannot be read, or is larger than [`MAX_FONT_FILE`], is skipped.
    pub fn read(paths: &[&Path]) -> Fonts {
        let files = paths
            .iter()
            .filter(|p| std::fs::metadata(p).is_ok_and(|m| m.len() <= MAX_FONT_FILE))
            .filter_map(|p| std::fs::read(p).ok())
            .collect();
        Fonts::from_bytes(files)
    }
}

/// The text functions layout and paint use: the faces, or em boxes when
/// there is none.
pub enum Text<'a> {
    /// Real faces.
    Faces(FaceFonts<'a>),
    /// No face.
    Boxes,
}

impl<'a> Text<'a> {
    /// The text functions of `fonts` for a document whose computed family
    /// lists are `families`.
    pub fn of(fonts: &'a Fonts, families: &'a [Vec<Family>]) -> Text<'a> {
        if fonts.faces.is_empty() {
            Text::Boxes
        } else {
            Text::Faces(FaceFonts {
                table: &fonts.table,
                generics: &fonts.generics,
                faces: &fonts.faces,
                families,
            })
        }
    }
}

impl TextFns for Text<'_> {
    fn metrics(&self, style: &ComputedStyle) -> FontMetrics {
        match self {
            Text::Faces(f) => f.metrics(style),
            Text::Boxes => BoxFont.metrics(style),
        }
    }

    fn shape(&self, style: &ComputedStyle, text: &str) -> Vec<ShapedGlyph> {
        match self {
            Text::Faces(f) => f.shape(style, text),
            Text::Boxes => BoxFont.shape(style, text),
        }
    }
}
