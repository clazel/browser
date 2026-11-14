//! Font matching over real faces: the TrueType test fonts that item 5.9
//! vendored in `clazel-font` (`crates/clazel-font/tests/data/`, each with
//! its licence and `SOURCE.md`), read with `clazel-font` into a font table.

use clazel_font::Face;
use clazel_layout::fonts::{
    Choice, FaceInfo, Family, FontQuery, FontStyle, FontTable, Generic, Generics, Os,
    face_for_char, first_available_font,
};

const DEJAVU_SERIF: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf");
const SOURCE_SERIF: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-source-serif/SourceSerif4-Regular.ttf");
const SOURCE_CODE_PRO: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-source-code-pro/SourceCodePro-Regular.otf");

#[test]
fn vendored_faces_match_by_family_and_coverage() -> Result<(), clazel_font::Error> {
    // Decision 5.0(c), C1: the CFF face is not readable, so never in the table.
    assert_eq!(
        Face::parse(SOURCE_CODE_PRO, 0).err(),
        Some(clazel_font::Error::CffOutlines)
    );
    let faces = [Face::parse(SOURCE_SERIF, 0)?, Face::parse(DEJAVU_SERIF, 0)?];
    let mut table = FontTable::new();
    for f in &faces {
        let info = FaceInfo::from_face(f).ok_or(clazel_font::Error::Truncated)?;
        table.push(info);
    }
    let names: Vec<&str> = table.families();
    assert_eq!(names, ["Source Serif 4", "DejaVu Serif"]);
    for (_, f) in table.iter() {
        assert_eq!((f.weight, f.stretch, f.style), (400, 5, FontStyle::Normal));
    }

    let generics =
        Generics::for_os(Os::MacOs).with_bundled("DejaVu Serif", "DejaVu Sans", "DejaVu Sans Mono");
    let families = [
        Family::Named("source serif 4".to_owned()),
        Family::Generic(Generic::Serif),
    ];
    let q = FontQuery {
        families: &families,
        weight: 700,
        stretch: 5,
        style: FontStyle::Italic,
    };
    let source = clazel_layout::fonts::FaceId(0);
    let dejavu = clazel_layout::fonts::FaceId(1);
    // Latin from the first family, whatever its weight and style (step 4
    // narrows within the family; it never empties it).
    assert_eq!(
        face_for_char(&table, &generics, &q, 'A', &faces[..]),
        Choice::Face(source)
    );
    // A character Source Serif 4 lacks and DejaVu Serif has (Armenian),
    // through the generic serif, which on macOS falls to the bundled family.
    assert!(faces[0].glyph_index('Ա')?.is_none());
    assert_eq!(
        face_for_char(&table, &generics, &q, 'Ա', &faces[..]),
        Choice::Face(dejavu)
    );
    // Nobody has it: .notdef of the first available font.
    assert_eq!(
        face_for_char(&table, &generics, &q, '\u{10FFFD}', &faces[..]),
        Choice::NotDef(source)
    );
    assert_eq!(
        first_available_font(&table, &generics, &q, &faces[..]),
        Some(source)
    );
    Ok(())
}
