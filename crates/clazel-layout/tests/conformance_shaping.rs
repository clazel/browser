//! Differential test of the shaper (`clazel_layout::shape`, phase-5.md item
//! 5.11) against `rustybuzz`, HarfBuzz's shaping algorithm ported to Rust.
//!
//! Two suites, each printing one `clazel-conformance:` line
//! (`xtask/src/conformance.rs`):
//!
//! - **vendored fonts**: every face of every TrueType font `clazel-font`
//!   vendored under `crates/clazel-font/tests/data/` (the CFF font is not
//!   readable, decision 5.0(c) C1, and is skipped). Under Miri a fixed
//!   stride of the cases runs ([`MIRI_STRIDE`]), because Miri runs this
//!   code thousands of times slower and CI fails a test that takes 300 s.
//! - **system fonts**: the same on every font file under the machine's font
//!   directories, at a stride of [`SYSTEM_STRIDE`] cases per face; ignored
//!   under Miri, which forbids opening files. Its counts depend on the
//!   machine.
//!
//! A unit is one case: one text shaped in one face. Texts are Latin, Greek
//! and Cyrillic: sentences, every ordered pair of characters from an
//! alphabet per script, and every triple from a small set of Latin
//! characters that kern. `rustybuzz` runs with the `kern` feature only:
//! every other feature it would turn on (`liga`, `clig`, `calt`, `ccmp`,
//! `locl`, `mark`, `mkmk`, …) is turned off, at the cluster level
//! `Characters`, left to right, with the script our shaper chose. Compared,
//! in font units: the glyph count, then per glyph its id, cluster and
//! advance, and its horizontal and vertical offset unless it is a combining
//! mark (we place marks at the pen with no offset; HarfBuzz's fallback mark
//! positioning moves them).
//!
//! Set `SHAPE_DEBUG` to print every expected difference with its glyphs.
//!
//! Expected differences. A case that differs is counted under the first
//! of these that applies, in this order: first what the case itself shows,
//! then what the face has (so a face-wide name counts only cases nothing
//! more specific explains):
//!
//! - `canonical composition`: the case has a combining mark and HarfBuzz
//!   drew fewer glyphs: its normalization composed a base and mark into
//!   the precomposed character the face maps (`y` with U+0308 to `ÿ`), where
//!   we map each character as it is (listed in `shape`'s modelling choices).
//! - `unmapped character`: the face does not map a character of the case,
//!   and HarfBuzz's normalization (composing or decomposing to what the
//!   face maps) and space fallback change the glyphs.
//! - `kern table split`: the face is kerned from its `kern` table, and
//!   HarfBuzz splits each pair's value between the two glyphs (half to the
//!   first glyph's advance, the rest to the second's advance and offset)
//!   where we give it to the first glyph's advance. The case counts only
//!   if every glyph's position (pen plus offset) and the run's width agree.
//! - `GDEF mark classes`: HarfBuzz reads `GDEF` glyph classes to decide
//!   what a mark is, and gives a mark a zero advance; we use the
//!   character's block. Counted when every glyph whose advance differs is
//!   a `GDEF` mark (class 3) to which HarfBuzz gave zero advance (Times New
//!   Roman Bold Italic classes `"` as a mark), or the case has a
//!   combining mark whose advance differs and the face has `GDEF` classes.
//! - `marks in kern pairs`: the case has a combining mark and the face is
//!   kerned. We skip marks when forming pairs; HarfBuzz skips them only
//!   for a lookup whose `lookupFlag` says so, and only glyphs `GDEF` (or
//!   the character's category) calls marks.
//! - `AAT tables`: the face has `morx`, `mort` or `kerx`, Apple's layout
//!   tables, which `rustybuzz` applies (substitutions included, which no
//!   feature setting turns off) and we do not read.
//! - `Apple kern table`: the face's `kern` table is Apple's version 1,
//!   which `clazel-font` does not read (5.9) and `rustybuzz` does.
//! - `kern subtable formats`: the face's `kern` table has subtables we do
//!   not use (format 2, cross-stream or minimum values; 5.9).
//! - `non-pair lookups under kern`: the face's `kern` feature has lookups
//!   that are not pair adjustment (Euphemia UCAS has a single adjustment
//!   that narrows the space), which HarfBuzz applies and H1 does not.
//! - `unordered GPOS`: a `kern` lookup's Coverage, ClassDef or PairSet is
//!   not in the order the chapters require, so each engine's bisection may
//!   find a different element.
//! - `GPOS without kern for the script`: the face has `GPOS`, but no
//!   `kern` lookup under the run's script, `DFLT`, `dflt` or `latn`, so we
//!   kern it from its `kern` table or not at all, where HarfBuzz may have
//!   chosen a script table differently (`shape`'s modelling choices,
//!   "Script") or applied the other `GPOS` features it always applies.

use clazel_font::file::FontFile;
use clazel_font::kern::coverage;
use clazel_font::layout::ClassDef;
use clazel_font::{Face, Tag};
use clazel_layout::shape::{KerningTable, Script, Shaper, UnitGlyph, is_combining_mark};
use std::collections::BTreeMap;

const DEJAVU_SERIF: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf");
const SOURCE_SERIF: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-source-serif/SourceSerif4-Regular.ttf");
const SOURCE_CODE_PRO: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-source-code-pro/SourceCodePro-Regular.otf");
const TTC: &[u8] = include_bytes!("../../clazel-font/tests/data/fonts-fontations/TTC.ttc");
const GLYF_COMPONENTS: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-fontations/glyf_components.ttf");
const CMAP12: &[u8] =
    include_bytes!("../../clazel-font/tests/data/fonts-fontations/cmap12_font1.ttf");
const CMAP6: &[u8] = include_bytes!("../../clazel-font/tests/data/fonts-fontations/cmap6.ttf");

/// Every vendored font file.
const VENDORED: &[(&str, &[u8])] = &[
    ("fonts-dejavu/DejaVuSerif.ttf", DEJAVU_SERIF),
    ("fonts-source-serif/SourceSerif4-Regular.ttf", SOURCE_SERIF),
    (
        "fonts-source-code-pro/SourceCodePro-Regular.otf",
        SOURCE_CODE_PRO,
    ),
    ("fonts-fontations/TTC.ttc", TTC),
    ("fonts-fontations/glyf_components.ttf", GLYF_COMPONENTS),
    ("fonts-fontations/cmap12_font1.ttf", CMAP12),
    ("fonts-fontations/cmap6.ttf", CMAP6),
];

/// Under Miri, every `MIRI_STRIDE`-th case of the vendored suite runs:
/// about 75 cases, sized to finish in about a minute on this machine.
const MIRI_STRIDE: usize = 1_000;

/// In the system suite, every `SYSTEM_STRIDE`-th case of each face runs, so
/// a machine with hundreds of faces finishes in a few minutes.
const SYSTEM_STRIDE: usize = 11;

const LATIN_SENTENCES: &[&str] = &[
    "The quick brown fox jumps over the lazy dog.",
    "AVATAR WAVY Typography: To Tell, Yes. P.F. L'Avenir, \"Quoted\" (paren) 1/2 -- 1,234.56",
    "Voix ambiguë d'un cœur qui, au zéphyr, préfère les jattes de kiwis.",
    "Falsches Üben von Xylophonmusik quält jeden größeren Zwerg.",
    "Zwölf Boxkämpfer jagen Viktor quer über den großen Sylter Deich.",
    "Pchnąć w tę łódź jeża lub ośm skrzyń fig. Příliš žluťoučký kůň úpěl ďábelské ódy.",
    "Kerning: AV AW AY Av Aw Ay FA LT LV LW LY PA TA Ta Te To Tr Tu Tw Ty VA Va Ve Vo WA Wa We Wo YA Ya Ye Yo",
    "Combining marks: q\u{303} x\u{301}y\u{308} a\u{30A}\u{301}b n\u{331}",
    "r. r, y. y, f' ff fi fl ffi ffl",
];

const GREEK_SENTENCES: &[&str] = &[
    "Ξεσκεπάζω την ψυχοφθόρα βδελυγμία.",
    "Τάχιστη αλώπηξ βαφής ψημένη γη, δρασκελίζει υπέρ νωθρού κυνός.",
    "ΑΥΤΟΚΙΝΗΤΟ ΤΑΥΤΟΤΗΤΑ Λόγος, Ύμνος, Ώρα. Αυτό Τόπος Υγεία",
    "Πολυτονικό: ἀρχὴ ἡμέρας, Ἀθῆναι, ᾠδή",
];

const CYRILLIC_SENTENCES: &[&str] = &[
    "Съешь же ещё этих мягких французских булок да выпей чаю.",
    "Широкая электрификация южных губерний даст мощный толчок подъёму сельского хозяйства.",
    "ГОЛОВА ТАТЬЯНА УГОЛ ГЪ ТЬ Гу Ту Тя Гл Ул Ул. Р. Г. Ф. Т.",
    "Чуєш їх, доцю, га? Кумедна ж ти, прощайся без ґольфів!",
    "Ѓ Ќ Љ Њ Ћ Џ ђ љ њ ћ џ — ѐ ѝ",
    "Ударе\u{301}ние: мо\u{301}локо, за\u{301}мок",
];

const LATIN_ALPHABET: &str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 .,:;'\"-()?!ÀÅÇÉÑÖØÜßàåçéñöøüŁłŒœ";
const GREEK_ALPHABET: &str = "ΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩαβγδεζηθικλμνξοπρστυφχψωςάέήίόύώΆΈΉΊΌΎΏ .,;";
const CYRILLIC_ALPHABET: &str =
    "АБВГДЕЁЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЫЬЭЮЯабвгдеёжзийклмнопрстуфхцчшщъыьэюяЄІЇЎЂЉЊЋЏєіїўђљњћџ .,";
const LATIN_TRIPLES: &str = "AVTYPLWo.,'y";

/// Every case: sentences, pairs per script, Latin triples.
fn cases() -> Vec<String> {
    let mut out: Vec<String> = LATIN_SENTENCES
        .iter()
        .chain(GREEK_SENTENCES)
        .chain(CYRILLIC_SENTENCES)
        .map(|s| (*s).to_owned())
        .collect();
    for alphabet in [LATIN_ALPHABET, GREEK_ALPHABET, CYRILLIC_ALPHABET] {
        for a in alphabet.chars() {
            for b in alphabet.chars() {
                out.push([a, b].iter().collect());
            }
        }
    }
    for a in LATIN_TRIPLES.chars() {
        for b in LATIN_TRIPLES.chars() {
            for c in LATIN_TRIPLES.chars() {
                out.push([a, b, c].iter().collect());
            }
        }
    }
    out
}

/// Results of a suite.
#[derive(Default)]
struct Tally {
    pass: u64,
    xfail: BTreeMap<&'static str, u64>,
    fail: u64,
    messages: Vec<String>,
    /// Faces by kerning table.
    kerning: BTreeMap<&'static str, u64>,
}

impl Tally {
    fn xfail_total(&self) -> u64 {
        self.xfail.values().copied().sum()
    }

    fn report(&self, suite: &str) {
        let total = self
            .pass
            .saturating_add(self.xfail_total())
            .saturating_add(self.fail);
        println!(
            "clazel-conformance: suite=\"{suite}\" pass={} xfail={} fail={} total={total}",
            self.pass,
            self.xfail_total(),
            self.fail
        );
        for (k, n) in &self.kerning {
            println!("  faces kerned from {k}: {n}");
        }
        for (k, n) in &self.xfail {
            println!("  expected difference {k}: {n}");
        }
        for m in self.messages.iter().take(40) {
            println!("  FAIL {m}");
        }
    }
}

/// What about a face can explain a difference.
struct FaceTraits {
    aat: bool,
    non_pair_kern: bool,
    apple_kern: bool,
    kern_formats: bool,
    unordered_gpos: bool,
    gdef_classes: bool,
    gpos_without_kern: bool,
}

fn has(face: &Face<'_>, tag: &[u8; 4]) -> bool {
    matches!(face.directory().find(Tag(*tag)), Ok(Some(_)))
}

/// Whether a lookup under some script's `kern` feature has a subtable that
/// is not pair adjustment, as `ttf-parser` (which `rustybuzz` uses) reads it.
fn non_pair_kern(data: &[u8], index: u32) -> bool {
    use rustybuzz::ttf_parser::gpos::PositioningSubtable;
    let Ok(f) = rustybuzz::ttf_parser::Face::parse(data, index) else {
        return false;
    };
    let Some(gpos) = f.tables().gpos else {
        return false;
    };
    let kern = rustybuzz::ttf_parser::Tag::from_bytes(b"kern");
    gpos.features
        .into_iter()
        .filter(|feature| feature.tag == kern)
        .flat_map(|feature| feature.lookup_indices)
        .filter_map(|l| gpos.lookups.get(l))
        .any(|lookup| {
            (0..lookup.subtables.len()).any(|k| {
                !matches!(
                    lookup.subtables.get::<PositioningSubtable>(k),
                    Some(PositioningSubtable::Pair(_)) | None
                )
            })
        })
}

/// The `GDEF` glyph class of `glyph` (3 is "Mark glyph"), 0 if none.
fn gdef_class(face: &Face<'_>, glyph: u16) -> u16 {
    let Some(gdef) = face.directory().table(Tag(*b"GDEF")).ok().flatten() else {
        return 0;
    };
    let Some(&[a, b]) = gdef.get(4..6) else {
        return 0;
    };
    match usize::from(u16::from_be_bytes([a, b])) {
        0 => 0,
        o => gdef
            .get(o..)
            .map(|d| ClassDef::new(d).class(glyph).unwrap_or(0))
            .unwrap_or(0),
    }
}

fn traits(data: &[u8], index: u32, face: &Face<'_>, shaper: &Shaper<'_>) -> FaceTraits {
    let table = shaper.kerning_table();
    let kern_formats = match face.kern() {
        Ok(Some(k)) => {
            let mut other = false;
            let read = k.subtables(|s| {
                let usable = s.format() == 0
                    && s.coverage & coverage::HORIZONTAL != 0
                    && s.coverage & (coverage::MINIMUM | coverage::CROSS_STREAM) == 0;
                other |= !usable;
                Ok(())
            });
            other || read.is_err()
        }
        _ => false,
    };
    let unordered_gpos = match face.gpos() {
        Ok(Some(g)) => [
            Script::Latin,
            Script::Greek,
            Script::Cyrillic,
            Script::Other,
        ]
        .iter()
        .flat_map(|s| g.kern_lookups(s.tag()).unwrap_or_default())
        .any(|l| !g.lookup_is_ordered(l).unwrap_or(false)),
        _ => false,
    };
    FaceTraits {
        aat: has(face, b"morx") || has(face, b"mort") || has(face, b"kerx"),
        non_pair_kern: non_pair_kern(data, index),
        apple_kern: has(face, b"kern") && face.kern().is_err() && table != KerningTable::Gpos,
        kern_formats: kern_formats && table == KerningTable::Kern,
        unordered_gpos,
        // GDEF's glyphClassDefOffset (at 4) is non-zero.
        gdef_classes: face
            .directory()
            .table(Tag(*b"GDEF"))
            .ok()
            .flatten()
            .and_then(|d| d.get(4..6))
            .is_some_and(|o| o != [0, 0]),
        gpos_without_kern: has(face, b"GPOS") && table != KerningTable::Gpos,
    }
}

/// The rustybuzz features: `kern` on, everything else it would apply off.
fn features() -> Vec<rustybuzz::Feature> {
    let mut f = vec![rustybuzz::Feature::new(
        rustybuzz::ttf_parser::Tag::from_bytes(b"kern"),
        1,
        ..,
    )];
    for tag in [
        b"liga", b"clig", b"calt", b"ccmp", b"locl", b"mark", b"mkmk", b"rlig", b"rclt", b"curs",
        b"dist", b"abvm", b"blwm", b"ltra", b"ltrm", b"rvrn", b"frac", b"numr", b"dnom", b"rand",
        b"trak",
    ] {
        f.push(rustybuzz::Feature::new(
            rustybuzz::ttf_parser::Tag::from_bytes(tag),
            0,
            ..,
        ));
    }
    f
}

fn rb_script(s: Script) -> rustybuzz::Script {
    match s {
        Script::Latin => rustybuzz::script::LATIN,
        Script::Greek => rustybuzz::script::GREEK,
        Script::Cyrillic => rustybuzz::script::CYRILLIC,
        Script::Other => rustybuzz::script::COMMON,
    }
}

/// One glyph as rustybuzz gives it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Theirs {
    glyph: u32,
    cluster: u32,
    x_advance: i32,
    x_offset: i32,
    y_offset: i32,
}

/// Each glyph's position (pen plus x offset), and the run's width.
fn positions(advances_offsets: impl Iterator<Item = (i32, i32)>) -> (Vec<i64>, i64) {
    let mut pen = 0i64;
    let mut out = Vec::new();
    for (adv, off) in advances_offsets {
        out.push(pen.saturating_add(i64::from(off)));
        pen = pen.saturating_add(i64::from(adv));
    }
    (out, pen)
}

/// Compare one case; `None` if it agrees, else the kinds of difference
/// that may explain it and a message.
fn compare(ours: &[UnitGlyph], theirs: &[Theirs]) -> Option<(Vec<&'static str>, String)> {
    let same_ids = ours.len() == theirs.len()
        && ours.iter().zip(theirs).all(|(o, t)| {
            u32::from(o.glyph) == t.glyph && u32::try_from(o.cluster).ok() == Some(t.cluster)
        });
    if !same_ids {
        let o: Vec<u16> = ours.iter().map(|g| g.glyph).collect();
        let t: Vec<u32> = theirs.iter().map(|g| g.glyph).collect();
        return Some((vec!["glyphs"], format!("glyphs {o:?}, rustybuzz {t:?}")));
    }
    let mut kinds = Vec::new();
    let advances_differ = ours
        .iter()
        .zip(theirs)
        .any(|(o, t)| o.x_advance != t.x_advance);
    let offsets_differ = ours
        .iter()
        .zip(theirs)
        .any(|(o, t)| !o.mark && (o.x_offset != t.x_offset || o.y_offset != t.y_offset));
    let mark_advances_differ = ours
        .iter()
        .zip(theirs)
        .any(|(o, t)| o.mark && o.x_advance != t.x_advance);
    if !advances_differ && !offsets_differ {
        return None;
    }
    if mark_advances_differ {
        kinds.push("marks");
    }
    let mine = positions(ours.iter().map(|g| (g.x_advance, g.x_offset)));
    let rb = positions(theirs.iter().map(|g| (g.x_advance, g.x_offset)));
    let y_agree = ours
        .iter()
        .zip(theirs)
        .all(|(o, t)| o.mark || o.y_offset == t.y_offset);
    if mine == rb && y_agree {
        kinds.push("split");
    }
    let o: Vec<(i32, i32, i32)> = ours
        .iter()
        .map(|g| (g.x_advance, g.x_offset, g.y_offset))
        .collect();
    let t: Vec<(i32, i32, i32)> = theirs
        .iter()
        .map(|g| (g.x_advance, g.x_offset, g.y_offset))
        .collect();
    Some((kinds, format!("(advance, x, y) {o:?}, rustybuzz {t:?}")))
}

/// Shape every `stride`-th case (from `offset`) in every face of `data`.
fn compare_file(data: &[u8], name: &str, stride: usize, offset: &mut usize, t: &mut Tally) {
    let Ok(file) = FontFile::parse(data) else {
        return;
    };
    let features = features();
    let all = cases();
    for index in 0..file.num_faces().min(32) {
        let Ok(face) = Face::parse(data, index) else {
            // CFF and unreadable faces are not shaped (5.0(c), C1; 5.9).
            continue;
        };
        let Some(rb) = rustybuzz::Face::from_slice(data, index) else {
            continue;
        };
        let mut shapers: BTreeMap<&'static str, (Shaper<'_>, rustybuzz::ShapePlan)> =
            BTreeMap::new();
        for script in [
            Script::Latin,
            Script::Greek,
            Script::Cyrillic,
            Script::Other,
        ] {
            let plan = rustybuzz::ShapePlan::new(
                &rb,
                rustybuzz::Direction::LeftToRight,
                Some(rb_script(script)),
                None,
                &features,
            );
            shapers.insert(script_name(script), (Shaper::new(face, script), plan));
        }
        let latin = shapers.get("latn").map(|(s, _)| s.kerning_table());
        let key = match latin {
            Some(KerningTable::Gpos) => "GPOS",
            Some(KerningTable::Kern) => "kern",
            _ => "nothing",
        };
        let n = t.kerning.entry(key).or_default();
        *n = n.saturating_add(1);
        let Some((latin_shaper, _)) = shapers.get("latn") else {
            continue;
        };
        let face_traits = traits(data, index, &face, latin_shaper);
        for text in &all {
            let run = *offset;
            *offset = offset.wrapping_add(1);
            if run.checked_rem(stride) != Some(0) {
                continue;
            }
            let script = Script::of_text(text);
            let Some((shaper, plan)) = shapers.get(script_name(script)) else {
                continue;
            };
            let ours = shaper.shape(text);
            let mut buffer = rustybuzz::UnicodeBuffer::new();
            buffer.push_str(text);
            buffer.set_direction(rustybuzz::Direction::LeftToRight);
            buffer.set_script(rb_script(script));
            buffer.set_cluster_level(rustybuzz::BufferClusterLevel::Characters);
            let out = rustybuzz::shape_with_plan(&rb, plan, buffer);
            let theirs: Vec<Theirs> = out
                .glyph_infos()
                .iter()
                .zip(out.glyph_positions())
                .map(|(i, p)| Theirs {
                    glyph: i.glyph_id,
                    cluster: i.cluster,
                    x_advance: p.x_advance,
                    x_offset: p.x_offset,
                    y_offset: p.y_offset,
                })
                .collect();
            let Some((kinds, message)) = compare(&ours, &theirs) else {
                t.pass = t.pass.saturating_add(1);
                continue;
            };
            let unmapped = text
                .chars()
                .any(|c| !matches!(face.glyph_index(c), Ok(Some(_))));
            let has_mark = text.chars().any(is_combining_mark);
            // Every glyph whose advance differs is a GDEF mark that
            // HarfBuzz gave a zero advance.
            let gdef_zeroed = ours.len() == theirs.len()
                && ours.iter().zip(&theirs).all(|(o, t)| {
                    o.x_advance == t.x_advance
                        || (t.x_advance == 0 && gdef_class(&face, o.glyph) == 3)
                });
            // Per-case causes first, then what the face has.
            let explained: Option<&'static str> = if has_mark && theirs.len() < ours.len() {
                Some("canonical composition")
            } else if unmapped {
                Some("unmapped character")
            } else if kinds.contains(&"split") && shaper.kerning_table() == KerningTable::Kern {
                Some("kern table split")
            } else if gdef_zeroed
                || (has_mark && face_traits.gdef_classes && kinds.contains(&"marks"))
            {
                Some("GDEF mark classes")
            } else if has_mark && shaper.kerning_table() != KerningTable::None {
                Some("marks in kern pairs")
            } else if face_traits.aat {
                Some("AAT tables")
            } else if face_traits.apple_kern {
                Some("Apple kern table")
            } else if face_traits.kern_formats {
                Some("kern subtable formats")
            } else if face_traits.non_pair_kern {
                Some("non-pair lookups under kern")
            } else if face_traits.unordered_gpos {
                Some("unordered GPOS")
            } else if face_traits.gpos_without_kern {
                Some("GPOS without kern for the script")
            } else {
                None
            };
            match explained {
                Some(k) => {
                    if std::env::var_os("SHAPE_DEBUG").is_some() {
                        println!("XFAIL {k} {name}#{index} {text:?}: {message}");
                    }
                    let n = t.xfail.entry(k).or_default();
                    *n = n.saturating_add(1);
                }
                None => {
                    t.fail = t.fail.saturating_add(1);
                    t.messages
                        .push(format!("{name}#{index} {text:?}: {message}"));
                }
            }
        }
    }
}

fn script_name(s: Script) -> &'static str {
    match s {
        Script::Latin => "latn",
        Script::Greek => "grek",
        Script::Cyrillic => "cyrl",
        Script::Other => "DFLT",
    }
}

#[test]
fn vendored_fonts() {
    let stride = if cfg!(miri) { MIRI_STRIDE } else { 1 };
    let mut t = Tally::default();
    let mut offset = 0usize;
    for (name, data) in VENDORED {
        compare_file(data, name, stride, &mut offset, &mut t);
    }
    println!("cases per face: {}", cases().len());
    t.report("vendored fonts vs rustybuzz");
    assert!(t.fail == 0, "{} unexpected differences", t.fail);
}

/// Font directories by OS, read without enumeration services (5.0(c), S1).
const SYSTEM_DIRS: &[&str] = &[
    "/System/Library/Fonts",
    "/Library/Fonts",
    "/usr/share/fonts",
    "/usr/local/share/fonts",
    "C:\\Windows\\Fonts",
];

fn font_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>, depth: u8) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() && depth < 6 {
            font_files(&p, out, depth.saturating_add(1));
        } else if p.extension().and_then(|e| e.to_str()).is_some_and(|e| {
            ["ttf", "otf", "ttc", "otc"].contains(&e.to_ascii_lowercase().as_str())
        }) {
            out.push(p);
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "opens files, which Miri's isolation forbids")]
fn system_fonts() {
    let mut files = Vec::new();
    for d in SYSTEM_DIRS {
        font_files(std::path::Path::new(d), &mut files, 0);
    }
    let mut t = Tally::default();
    let mut offset = 0usize;
    let mut read = 0usize;
    for f in &files {
        let Ok(data) = std::fs::read(f) else { continue };
        if data.len() > 64 << 20 {
            continue;
        }
        read = read.saturating_add(1);
        compare_file(
            &data,
            &f.display().to_string(),
            SYSTEM_STRIDE,
            &mut offset,
            &mut t,
        );
    }
    println!("system font files read: {read}");
    t.report("system fonts vs rustybuzz");
    assert!(t.fail == 0, "{} unexpected differences", t.fail);
}
