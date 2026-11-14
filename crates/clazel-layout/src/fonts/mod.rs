//! Font matching (phase-5.md item 5.10): which face draws a character.
//!
//! # Sources
//!
//! - **CSS Fonts Module Level 3**, W3C Recommendation, 20 September 2018
//!   (<https://www.w3.org/TR/2018/REC-css-fonts-3-20180920/>), the version
//!   this module is pinned to:
//!   - §5.1 "Case sensitivity of font family names";
//!   - §5.2 "Matching font styles", steps 1 to 8, with step 4's four
//!     numbered sub-steps cited as 4.1 (`font-stretch`), 4.2
//!     (`font-style`), 4.3 (`font-weight`) and 4.4 (`font-size`); and its
//!     definition of the *first available font*;
//!   - §5.3 "Cluster matching", not applied (below);
//!   - §5.4 "Character handling", for private-use code points.
//! - **Decision 5.0(c)** of `docs/phases/phase-5.md` (C1, S3, H1): TrueType
//!   faces only, system fonts first with a bundled family as fallback, and
//!   a fixed family table per OS ([`generic`]).
//!
//! The steps cited are the standard's; each function names those it
//! implements (CLAUDE.md rule 5).
//!
//! # Modelling choices
//!
//! - **The font table is given, not discovered** ([`table::FontTable`]):
//!   family name to faces with weight, width and style, built from the
//!   faces the renderer read before entering its sandbox (item 5.20). There
//!   are no `@font-face` rules (web fonts are Phase 8), so step 3's
//!   `@font-face` lookup and step 5 (downloading, `unicode-range`) never
//!   apply, and every face is a platform face.
//! - **A face's description comes from its tables** ([`table::FaceInfo::from_face`]):
//!   the family is `name` ID 16 (typographic family) if present, else ID 1;
//!   weight is `OS/2.usWeightClass`; width is `OS/2.usWidthClass` (1 to 9,
//!   the nine `font-stretch` keywords in order, `normal` being 5; a value
//!   outside 1 to 9 is read as 5); style is oblique if `fsSelection` bit 9
//!   (`OBLIQUE`) is set, else italic if bit 0 (`ITALIC`) is, else normal.
//!   A face without `OS/2` falls back to `head.macStyle` (bit 0 bold: 700,
//!   else 400; bit 1 italic).
//! - **Caseless matching (§5.1)** is approximated by comparing
//!   `str::to_lowercase` of both names. Unicode's "Default Caseless
//!   Matching" uses full case folding, which differs from lowercasing for a
//!   few characters (`ß` folds to `ss`, final sigma); no family name in the
//!   tables of [`generic`] contains one.
//! - **One name per face.** Step 3 asks to match "any" of a family's
//!   localized names; a face is known by one name, the Windows English
//!   (United States) record or else the first UTF-16BE one
//!   (`clazel_font::name::Name::get`).
//! - **Generic families (step 2)**: `serif`, `sans-serif` and `monospace`
//!   each name a list of families per OS ([`generic::Generics`]); the first
//!   of them present in the table is "the appropriate font family name".
//!   The language and the character's Unicode range, which step 2 allows a
//!   user agent to consult, are not. `cursive`, `fantasy` and every other
//!   name are family names, which no face in the tables has.
//! - **Step 4.4 (`font-size`) never narrows**: every face is TrueType, so
//!   scalable to any size.
//! - **Ties after step 4** (two faces of one family with the same width,
//!   style and weight, as a system with two copies of a font has) go to the
//!   face added to the table first.
//! - **Step 6's synthetic oblique** of the family's default face is not
//!   made (no `font-synthesis`), so step 6 always moves to the next family.
//! - **System font fallback (step 7)**, which the standard leaves to the
//!   user agent: the families of the OS's fallback list in order
//!   ([`generic::Generics::fallback`]), then every other family of the table
//!   in the order its first face was added; in each, the face step 4
//!   selects.
//! - **The missing glyph (step 8)** is glyph 0, `.notdef`, of the first
//!   available font, as phase-5.md item 5.10 states. The *first available
//!   font* is the face that a match for U+0020 SPACE selects through steps 1
//!   to 7; if no face maps U+0020, the face step 4 selects in the first
//!   family of the `font-family` list (or, failing that, of the fallback)
//!   present in the table.
//! - **One face per character.** §5.3's cluster matching (a base and its
//!   combining marks from one face) is not applied: shaping (item 5.11) is
//!   one glyph per character, so each character is matched on its own.
//! - **§5.4, private use**: a code point in a Private Use Area (U+E000 to
//!   U+F8FF, planes 15 and 16) is looked for only in the families the
//!   `font-family` list names, never in generic families' or fallback
//!   families; if none maps it, it is the missing glyph. U+FFFD, for which
//!   §5.4 allows skipping the search, is searched like any other character.

pub mod generic;
pub mod matching;
pub mod table;

pub use generic::{Generic, Generics, Os};
pub use matching::{CharMap, Choice, Family, FontQuery, face_for_char, first_available_font};
pub use table::{FaceId, FaceInfo, FontStyle, FontTable};
