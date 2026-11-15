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
//! Both suites gate (the system suite's result is machine-dependent
//! evidence, the vendored suite's is exact: see `VENDORED_EXPECTED`), as `clazel-font`'s system font suite does: the vendored
//! suite's input is fixed, and the system suite runs on whatever fonts each
//! CI runner has. A difference on a system font is never ignored: it is a
//! shaper bug to fix, or a new kind below with its reason. On failure the
//! output names it: up to 40 `FAIL <file>#<face> <text>: <what differed>`
//! lines (glyph ids, or (advance, x offset, y offset) per glyph, ours then
//! rustybuzz's), then one `FAILING FACE <file>#<face>: <n>` line per face
//! with any; a panic in either shaper is a `FAIL` line naming the shaper.
//! The system suite also prints how many font files each directory gave.
//!
//! Set `SHAPE_DEBUG` to print every expected difference with its glyphs.
//!
//! Expected differences. A case that differs is counted under the first
//! of these that applies, in this order: first what the case itself shows,
//! then what the face has (so a face-wide name counts only cases nothing
//! more specific explains). Each reason excuses only the kind of difference
//! it explains. Differences are compared cluster by cluster. Reasons that
//! change glyphs (composition, unmapped characters, AAT substitutions) may
//! change glyph ids, but composition and unmapped characters only in the
//! window of the characters they concern; any differing cluster outside the
//! window (the residue) must have identical glyph ids and be explained by a
//! positioning reason (the kern table split run by run, or a face-wide
//! positioning trait). Every other reason is positioning only: the glyph
//! ids and clusters must be identical.
//!
//! - `canonical composition`: the case has a combining mark and HarfBuzz
//!   drew fewer glyphs: its normalization composed a base and mark into
//!   the precomposed character the face maps (`y` with U+0308 to `ÿ`), where
//!   we map each character as it is (listed in `shape`'s modelling choices).
//!   Window: two characters before to one after each combining mark.
//! - `unmapped character`: the face does not map a character of the case,
//!   and HarfBuzz's normalization (composing or decomposing to what the
//!   face maps) and space fallback change the glyphs. Window: the
//!   character's base and combining marks, and one character either side.
//! - `kern table split`: the face is kerned from its `kern` table, and
//!   HarfBuzz splits each pair's value between the two glyphs (half to the
//!   first glyph's advance, the rest to the second's advance and offset)
//!   where we give it to the first glyph's advance. The case counts only
//!   if every glyph's position (pen plus offset) and the run's width agree.
//! - `GDEF mark classes`: HarfBuzz reads `GDEF` glyph classes to decide
//!   what a mark is, and gives a mark a zero advance; we use the
//!   character's block. Counted when the glyph ids, clusters and the offsets
//!   of non-marks agree, at least one advance differs, and every glyph whose
//!   advance differs is a `GDEF` mark (class 3) to which HarfBuzz gave zero
//!   advance (Times New Roman Bold Italic classes `"` as a mark).
//! - `marks in kern pairs`: positioning only; the case has a combining mark
//!   and the face is kerned, and every differing cluster is the mark or
//!   next to one. We skip marks when forming pairs; HarfBuzz skips them only
//!   for a lookup whose `lookupFlag` says so, and only glyphs `GDEF` (or
//!   the character's category) calls marks.
//! - `AAT tables`: the face has `morx`, `mort` or `kerx`, Apple's layout
//!   tables, which `rustybuzz` applies (substitutions included, which no
//!   feature setting turns off, so any difference, glyph ids too) and we do
//!   not read.
//! - `Apple kern table`: positioning only; the face's `kern` table is
//!   Apple's version 1, which `clazel-font` does not read (5.9) and
//!   `rustybuzz` does.
//! - `kern subtable formats`: positioning only; the face's `kern` table has
//!   subtables we do not use (format 2, cross-stream or minimum values; 5.9).
//! - `non-pair lookups under kern`: positioning only; the face's `kern`
//!   feature has lookups that are not pair adjustment (Euphemia UCAS has a
//!   single adjustment that narrows the space), which HarfBuzz applies and
//!   H1 does not.
//! - `unordered GPOS`: positioning only; a `kern` lookup's Coverage,
//!   ClassDef or PairSet is not in the order the chapters require, so each
//!   engine's bisection may find a different element.
//! - `GPOS without kern for the script`: positioning only; the face has
//!   `GPOS`, but the script table chosen for Latin (the first listed of
//!   `latn`, `DFLT`, `dflt`) has no `kern` lookup, so we kern it from its
//!   `kern` table or not at all, where HarfBuzz may also apply the `GPOS`
//!   features it always applies (a LangSys's required feature).
//!
//! The vendored suite pins its expected differences per case
//! (`VENDORED_EXPECTED`); the system suite cannot.

use clazel_font::file::FontFile;
use clazel_font::kern::coverage;
use clazel_font::layout::ClassDef;
use clazel_font::{Face, Tag};
use clazel_layout::shape::{KerningTable, Script, Shaper, UnitGlyph, is_combining_mark};
use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

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

/// Under Miri, every `MIRI_STRIDE`-th case of the vendored suite runs: 115
/// cases, 46 s on Miri's clock (`--report-time`, measured 2026-11-11),
/// within the minute the plan sizes Miri runs to; CI fails a test at 300 s.
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

/// Every case: sentences, pairs per script, Latin triples. A case is made
/// from its index when it is taken, so a strided run (under Miri) never
/// builds the other texts.
struct Cases {
    sentences: Vec<&'static str>,
    alphabets: Vec<Vec<char>>,
    triples: Vec<char>,
}

impl Cases {
    fn new() -> Self {
        Self {
            sentences: LATIN_SENTENCES
                .iter()
                .chain(GREEK_SENTENCES)
                .chain(CYRILLIC_SENTENCES)
                .copied()
                .collect(),
            alphabets: [LATIN_ALPHABET, GREEK_ALPHABET, CYRILLIC_ALPHABET]
                .iter()
                .map(|a| a.chars().collect())
                .collect(),
            triples: LATIN_TRIPLES.chars().collect(),
        }
    }

    fn len(&self) -> usize {
        let pairs: usize = self
            .alphabets
            .iter()
            .map(|a| a.len().saturating_mul(a.len()))
            .sum();
        let t = self.triples.len();
        self.sentences
            .len()
            .saturating_add(pairs)
            .saturating_add(t.saturating_mul(t).saturating_mul(t))
    }

    /// Case `i`: sentences in order, then each alphabet's pairs `ab` in
    /// order of `a` then `b`, then the triples likewise.
    fn get(&self, i: usize) -> Option<String> {
        if let Some(s) = self.sentences.get(i) {
            return Some((*s).to_owned());
        }
        let mut i = i.checked_sub(self.sentences.len())?;
        for a in &self.alphabets {
            let n = a.len();
            let square = n.saturating_mul(n);
            if i < square {
                let (x, y) = (i.checked_div(n)?, i.checked_rem(n)?);
                return Some([*a.get(x)?, *a.get(y)?].iter().collect());
            }
            i = i.checked_sub(square)?;
        }
        let t = &self.triples;
        let n = t.len();
        let (x, rest) = (
            i.checked_div(n.saturating_mul(n))?,
            i.checked_rem(n.saturating_mul(n))?,
        );
        let (y, z) = (rest.checked_div(n)?, rest.checked_rem(n)?);
        Some([*t.get(x)?, *t.get(y)?, *t.get(z)?].iter().collect())
    }
}

/// Results of a suite.
#[derive(Default)]
struct Tally {
    pass: u64,
    xfail: BTreeMap<&'static str, u64>,
    fail: u64,
    messages: Vec<String>,
    /// Unexpected differences per face (`file#index`), all of them.
    failing_faces: BTreeMap<String, u64>,
    /// Faces by kerning table.
    kerning: BTreeMap<&'static str, u64>,
    /// Faces whose cases were taken (readable and parsed by both engines).
    faces: u64,
    /// Every expected difference: `(file#face, text, reason)`.
    xfail_cases: Vec<(String, String, &'static str)>,
}

impl Tally {
    fn failure(&mut self, face: String, message: String) {
        self.fail = self.fail.saturating_add(1);
        self.messages.push(message);
        let n = self.failing_faces.entry(face).or_default();
        *n = n.saturating_add(1);
    }

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
        println!("  faces shaped: {}", self.faces);
        for (k, n) in &self.kerning {
            println!("  faces kerned from {k}: {n}");
        }
        for (k, n) in &self.xfail {
            println!("  expected difference {k}: {n}");
        }
        // On failure CI's log shows this output: the first 40 unexpected
        // differences in full, then every face that had any, with counts.
        for m in self.messages.iter().take(40) {
            println!("  FAIL {m}");
        }
        for (face, n) in &self.failing_faces {
            println!("  FAILING FACE {face}: {n} unexpected differences");
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

/// How one case differs from rustybuzz.
struct Diff {
    /// Kinds of difference that may explain it (`glyphs`, `marks`, `split`).
    kinds: Vec<&'static str>,
    message: String,
    /// Same glyph count, and per glyph the same id and cluster.
    ids_same: bool,
    /// Some glyph that is not a combining mark has another x or y offset.
    offsets_differ: bool,
    /// Indices of the glyphs whose advance differs (only if `ids_same`).
    advance_diffs: Vec<usize>,
    /// Byte offsets of the clusters whose glyphs (ids, advances, and the
    /// offsets of non-marks) differ between the two engines, compared
    /// cluster by cluster, so that it works when the glyph counts differ.
    clusters: Vec<usize>,
}

/// One glyph of a cluster, as compared: id, advance, offsets (zero for a
/// combining mark, whose offset is not compared).
type Cell = (u32, i32, i32, i32);

/// The byte offsets of `text`'s clusters that differ (see [`Diff`]).
fn differing_clusters(text: &str, ours: &[UnitGlyph], theirs: &[Theirs]) -> Vec<usize> {
    let mark_at = |cluster: usize| {
        text.get(cluster..)
            .and_then(|r| r.chars().next())
            .is_some_and(is_combining_mark)
    };
    let mut a: BTreeMap<usize, Vec<Cell>> = BTreeMap::new();
    let mut b: BTreeMap<usize, Vec<Cell>> = BTreeMap::new();
    for g in ours {
        let (x, y) = if g.mark {
            (0, 0)
        } else {
            (g.x_offset, g.y_offset)
        };
        a.entry(g.cluster)
            .or_default()
            .push((u32::from(g.glyph), g.x_advance, x, y));
    }
    for g in theirs {
        let c = usize::try_from(g.cluster).unwrap_or(usize::MAX);
        let (x, y) = if mark_at(c) {
            (0, 0)
        } else {
            (g.x_offset, g.y_offset)
        };
        b.entry(c).or_default().push((g.glyph, g.x_advance, x, y));
    }
    let keys: std::collections::BTreeSet<usize> = a.keys().chain(b.keys()).copied().collect();
    keys.into_iter().filter(|k| a.get(k) != b.get(k)).collect()
}

/// Compare one case; `None` if it agrees.
fn compare(text: &str, ours: &[UnitGlyph], theirs: &[Theirs]) -> Option<Diff> {
    let clusters = differing_clusters(text, ours, theirs);
    let same_ids = ours.len() == theirs.len()
        && ours.iter().zip(theirs).all(|(o, t)| {
            u32::from(o.glyph) == t.glyph && u32::try_from(o.cluster).ok() == Some(t.cluster)
        });
    if !same_ids {
        let o: Vec<u16> = ours.iter().map(|g| g.glyph).collect();
        let t: Vec<u32> = theirs.iter().map(|g| g.glyph).collect();
        return Some(Diff {
            kinds: vec!["glyphs"],
            message: format!("glyphs {o:?}, rustybuzz {t:?}"),
            ids_same: false,
            offsets_differ: false,
            advance_diffs: Vec::new(),
            clusters,
        });
    }
    let mut kinds = Vec::new();
    let advance_diffs: Vec<usize> = ours
        .iter()
        .zip(theirs)
        .enumerate()
        .filter(|(_, (o, t))| o.x_advance != t.x_advance)
        .map(|(i, _)| i)
        .collect();
    let offsets_differ = ours
        .iter()
        .zip(theirs)
        .any(|(o, t)| !o.mark && (o.x_offset != t.x_offset || o.y_offset != t.y_offset));
    let mark_advances_differ = ours
        .iter()
        .zip(theirs)
        .any(|(o, t)| o.mark && o.x_advance != t.x_advance);
    if advance_diffs.is_empty() && !offsets_differ {
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
    Some(Diff {
        kinds,
        message: format!("(advance, x, y) {o:?}, rustybuzz {t:?}"),
        ids_same: true,
        offsets_differ,
        advance_diffs,
        clusters,
    })
}

/// The char index of the character at byte offset `byte` of `text`.
fn char_index(text: &str, byte: usize) -> Option<usize> {
    text.char_indices().position(|(b, _)| b == byte)
}

/// The windows (inclusive char index ranges) around each combining mark
/// `m`: `[m - before, m + after]`.
fn mark_windows(text: &str, before: usize, after: usize) -> Vec<(usize, usize)> {
    text.chars()
        .enumerate()
        .filter(|(_, c)| is_combining_mark(*c))
        .map(|(m, _)| (m.saturating_sub(before), m.saturating_add(after)))
        .collect()
}

/// The windows around each character the face does not map: its base and
/// combining marks (HarfBuzz normalizes the whole sequence), and one
/// character either side (a kern pair with a glyph that changed).
fn unmapped_windows(text: &str, face: &Face<'_>) -> Vec<(usize, usize)> {
    let chars: Vec<char> = text.chars().collect();
    let mut windows = Vec::new();
    for (i, c) in chars.iter().enumerate() {
        if matches!(face.glyph_index(*c), Ok(Some(_))) {
            continue;
        }
        let mut lo = i;
        while lo > 0 && chars.get(lo).copied().is_some_and(is_combining_mark) {
            lo = lo.saturating_sub(1);
        }
        let mut hi = i;
        while chars
            .get(hi.saturating_add(1))
            .copied()
            .is_some_and(is_combining_mark)
        {
            hi = hi.saturating_add(1);
        }
        windows.push((lo.saturating_sub(1), hi.saturating_add(1)));
    }
    windows
}

/// The differing clusters (byte offsets) outside every window.
fn outside(text: &str, clusters: &[usize], windows: &[(usize, usize)]) -> Vec<usize> {
    clusters
        .iter()
        .copied()
        .filter(|&c| {
            !char_index(text, c)
                .is_some_and(|ci| windows.iter().any(|&(lo, hi)| ci >= lo && ci <= hi))
        })
        .collect()
}

/// Whether the glyphs of the clusters `residual` (differing, outside the
/// windows of a glyph-changing reason) are explained by a positioning
/// reason: the glyph ids agree cluster by cluster, and either the face is
/// kerned from its `kern` table and each run of consecutive such clusters
/// splits a pair's values (every glyph's position relative to the run's
/// start, and the run's width, agree), or the face has a face-wide
/// positioning trait.
fn residual_is_positioning(
    text: &str,
    ours: &[UnitGlyph],
    theirs: &[Theirs],
    residual: &[usize],
    kern_table: bool,
    traits: &FaceTraits,
) -> bool {
    let of = |c: usize| -> Vec<&UnitGlyph> { ours.iter().filter(|g| g.cluster == c).collect() };
    let tf = |c: usize| -> Vec<&Theirs> {
        theirs
            .iter()
            .filter(|g| usize::try_from(g.cluster).ok() == Some(c))
            .collect()
    };
    let ids_agree = residual.iter().all(|&c| {
        let (a, b) = (of(c), tf(c));
        !a.is_empty()
            && a.len() == b.len()
            && a.iter().zip(&b).all(|(x, y)| u32::from(x.glyph) == y.glyph)
    });
    if !ids_agree {
        return false;
    }
    if traits.apple_kern
        || traits.kern_formats
        || traits.non_pair_kern
        || traits.unordered_gpos
        || traits.gpos_without_kern
    {
        return true;
    }
    if !kern_table {
        return false;
    }
    // Runs of residual clusters at consecutive char indices.
    let idx: Vec<(usize, usize)> = residual
        .iter()
        .filter_map(|&c| char_index(text, c).map(|i| (i, c)))
        .collect();
    let mut runs: Vec<Vec<usize>> = Vec::new();
    let mut last: Option<usize> = None;
    for &(i, c) in &idx {
        if last.is_some_and(|l| l.saturating_add(1) == i) {
            if let Some(r) = runs.last_mut() {
                r.push(c);
            }
        } else {
            runs.push(vec![c]);
        }
        last = Some(i);
    }
    runs.iter().all(|run| {
        let a: Vec<&UnitGlyph> = run.iter().flat_map(|&c| of(c)).collect();
        let b: Vec<&Theirs> = run.iter().flat_map(|&c| tf(c)).collect();
        let pa = positions(a.iter().map(|g| (g.x_advance, g.x_offset)));
        let pb = positions(b.iter().map(|g| (g.x_advance, g.x_offset)));
        pa == pb
            && a.iter()
                .zip(&b)
                .all(|(x, y)| x.mark || x.y_offset == y.y_offset)
    })
}

/// Shape every `stride`-th case (from `offset`) in every face of `data`.
fn compare_file(
    data: &[u8],
    name: &str,
    all: &Cases,
    stride: usize,
    offset: &mut usize,
    t: &mut Tally,
) {
    let Ok(file) = FontFile::parse(data) else {
        return;
    };
    let features = features();
    for index in 0..file.num_faces().min(32) {
        let Ok(face) = Face::parse(data, index) else {
            // CFF and unreadable faces are not shaped (5.0(c), C1; 5.9).
            continue;
        };
        // The cases of this face are numbered `first..first + all.len()`.
        let first = *offset;
        *offset = offset.wrapping_add(all.len());
        let latin_shaper = Shaper::new(face, Script::Latin);
        let key = match latin_shaper.kerning_table() {
            KerningTable::Gpos => "GPOS",
            KerningTable::Kern => "kern",
            KerningTable::None => "nothing",
        };
        let n = t.kerning.entry(key).or_default();
        *n = n.saturating_add(1);
        t.faces = t.faces.saturating_add(1);
        // Skip parsing for rustybuzz a face none of whose cases is taken
        // (under Miri, where the stride exceeds a face's cases).
        let skip = first
            .checked_rem(stride)
            .and_then(|r| stride.saturating_sub(r).checked_rem(stride))
            .unwrap_or(0);
        if skip >= all.len() {
            continue;
        }
        let Some(rb) = rustybuzz::Face::from_slice(data, index) else {
            continue;
        };
        // Shapers and plans per script, made when a case first needs one.
        let mut shapers: BTreeMap<&'static str, (Shaper<'_>, rustybuzz::ShapePlan)> =
            BTreeMap::new();
        let mut face_traits: Option<FaceTraits> = None;
        for i in (skip..all.len()).step_by(stride.max(1)) {
            let Some(text) = all.get(i) else { continue };
            let text = text.as_str();
            let script = Script::of_text(text);
            if !shapers.contains_key(script_name(script)) {
                let made = catch_unwind(AssertUnwindSafe(|| {
                    let plan = rustybuzz::ShapePlan::new(
                        &rb,
                        rustybuzz::Direction::LeftToRight,
                        Some(rb_script(script)),
                        None,
                        &features,
                    );
                    (Shaper::new(face, script), plan)
                }));
                match made {
                    Ok(pair) => {
                        shapers.insert(script_name(script), pair);
                    }
                    Err(_) => {
                        t.failure(
                            format!("{name}#{index}"),
                            format!("{name}#{index}: making the shapers for {script:?} panicked"),
                        );
                        continue;
                    }
                }
            }
            let Some((shaper, plan)) = shapers.get(script_name(script)) else {
                continue;
            };
            // A panic in either shaper is reported with the font, face and
            // text, not only as a panic message without them.
            let Ok(ours) = catch_unwind(AssertUnwindSafe(|| shaper.shape(text))) else {
                t.failure(
                    format!("{name}#{index}"),
                    format!("{name}#{index} {text:?}: our shaper panicked"),
                );
                continue;
            };
            let mut buffer = rustybuzz::UnicodeBuffer::new();
            buffer.push_str(text);
            buffer.set_direction(rustybuzz::Direction::LeftToRight);
            buffer.set_script(rb_script(script));
            buffer.set_cluster_level(rustybuzz::BufferClusterLevel::Characters);
            let Ok(out) = catch_unwind(AssertUnwindSafe(|| {
                rustybuzz::shape_with_plan(&rb, plan, buffer)
            })) else {
                t.failure(
                    format!("{name}#{index}"),
                    format!("{name}#{index} {text:?}: rustybuzz panicked"),
                );
                continue;
            };
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
            let Some(diff) = compare(text, &ours, &theirs) else {
                t.pass = t.pass.saturating_add(1);
                continue;
            };
            let message = format!(
                "{} [differing char indices {:?}]",
                diff.message,
                diff.clusters
                    .iter()
                    .map(|&c| char_index(text, c))
                    .collect::<Vec<_>>()
            );
            let message = message.as_str();
            let kinds = &diff.kinds;
            let has_mark = text.chars().any(is_combining_mark);
            let kerned = shaper.kerning_table() != KerningTable::None;
            // GDEF mark classes: glyph ids, clusters and the offsets of
            // non-marks agree; at least one advance differs; and every
            // glyph whose advance differs is a GDEF mark (class 3) that
            // HarfBuzz gave a zero advance.
            let gdef_zeroed = diff.ids_same
                && !diff.offsets_differ
                && !diff.advance_diffs.is_empty()
                && diff.advance_diffs.iter().all(|&i| {
                    matches!((ours.get(i), theirs.get(i)),
                        (Some(o), Some(t)) if t.x_advance == 0 && gdef_class(&face, o.glyph) == 3)
                });
            let face_traits =
                face_traits.get_or_insert_with(|| traits(data, index, &face, &latin_shaper));
            // Each reason excuses only the kind of difference it explains.
            // Reasons that change glyphs (composition, unmapped characters,
            // AAT substitutions) may differ in ids, but only at the clusters
            // they affect; every other reason is about positioning, so the
            // glyph ids and clusters must be identical.
            let positioning_only = diff.ids_same;
            let kern_table = shaper.kerning_table() == KerningTable::Kern;
            // Glyph-changing reasons: the differing clusters inside their
            // windows are excused; the rest (the residue) must be
            // positioning explained by another reason.
            let composed = has_mark && theirs.len() < ours.len();
            let comp_w = if composed {
                mark_windows(text, 2, 1)
            } else {
                Vec::new()
            };
            let unm_w = unmapped_windows(text, &face);
            let both_w: Vec<(usize, usize)> = comp_w.iter().chain(&unm_w).copied().collect();
            let residue_ok = |w: &[(usize, usize)]| {
                let r = outside(text, &diff.clusters, w);
                r.is_empty()
                    || residual_is_positioning(text, &ours, &theirs, &r, kern_table, face_traits)
            };
            let glyph_reason: Option<&'static str> = if positioning_only {
                None
            } else if !comp_w.is_empty() && residue_ok(&comp_w) {
                Some("canonical composition")
            } else if !unm_w.is_empty() && residue_ok(&unm_w) {
                Some("unmapped character")
            } else if !both_w.is_empty() && residue_ok(&both_w) {
                // Both in one text: counted under the second.
                Some("unmapped character")
            } else {
                None
            };
            let explained: Option<&'static str> = if glyph_reason.is_some() {
                glyph_reason
            } else if kinds.contains(&"split") && shaper.kerning_table() == KerningTable::Kern {
                Some("kern table split")
            } else if gdef_zeroed {
                Some("GDEF mark classes")
            } else if positioning_only
                && has_mark
                && kerned
                && !diff.clusters.is_empty()
                && outside(text, &diff.clusters, &mark_windows(text, 1, 1)).is_empty()
            {
                Some("marks in kern pairs")
            } else if face_traits.aat {
                // morx/mort substitutions change glyphs anywhere.
                Some("AAT tables")
            } else if positioning_only && face_traits.apple_kern {
                Some("Apple kern table")
            } else if positioning_only && face_traits.kern_formats {
                Some("kern subtable formats")
            } else if positioning_only && face_traits.non_pair_kern {
                Some("non-pair lookups under kern")
            } else if positioning_only && face_traits.unordered_gpos {
                Some("unordered GPOS")
            } else if positioning_only && face_traits.gpos_without_kern {
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
                    t.xfail_cases
                        .push((format!("{name}#{index}"), text.to_owned(), k));
                }
                None => t.failure(
                    format!("{name}#{index}"),
                    format!("{name}#{index} {text:?}: {message}"),
                ),
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

/// The vendored suite's expected differences, per case: `(file#face, text,
/// reason)`. Its input is fixed (the vendored fonts, the cases above), so
/// the list is exact: a case that differs and is not here fails, and so
/// does a case here that now agrees (an unexpected pass: the shaper
/// improved, or the test went blind). Measured with `SHAPE_DEBUG`.
const VENDORED_EXPECTED: &[(&str, &str, &str)] = &[
    (
        "fonts-dejavu/DejaVuSerif.ttf#0",
        COMBINING,
        "canonical composition",
    ),
    (
        "fonts-source-serif/SourceSerif4-Regular.ttf#0",
        COMBINING,
        "canonical composition",
    ),
    // Source Serif 4 lacks the precomposed polytonic Greek characters.
    (
        "fonts-source-serif/SourceSerif4-Regular.ttf#0",
        "Πολυτονικό: ἀρχὴ ἡμέρας, Ἀθῆναι, ᾠδή",
        "unmapped character",
    ),
];

const COMBINING: &str = "Combining marks: q\u{303} x\u{301}y\u{308} a\u{30A}\u{301}b n\u{331}";

/// Faces of the vendored fonts that both engines read and that we shape
/// (measured; Source Code Pro is CFF, which `clazel-font` does not read).
const VENDORED_FACES: u64 = 5;

#[test]
fn vendored_fonts() {
    let stride = if cfg!(miri) { MIRI_STRIDE } else { 1 };
    let mut t = Tally::default();
    let mut offset = 0usize;
    let all = Cases::new();
    for (name, data) in VENDORED {
        compare_file(data, name, &all, stride, &mut offset, &mut t);
    }
    println!("cases per face: {}", all.len());
    t.report("vendored fonts vs rustybuzz");
    assert!(t.fail == 0, "{} unexpected differences", t.fail);
    // Never a silent success: zero faces or zero cases would pass the
    // check above with nothing compared.
    let total = t
        .pass
        .saturating_add(t.xfail_total())
        .saturating_add(t.fail);
    assert!(total > 0, "the vendored suite compared no cases");
    assert!(t.pass > 0, "the vendored suite had no agreeing case");
    assert_eq!(
        t.faces, VENDORED_FACES,
        "faces shaped in the vendored suite"
    );
    if cfg!(miri) {
        // Only a stride of the cases ran: the per-case list is checked in
        // normal runs.
        return;
    }
    assert_eq!(
        total,
        VENDORED_FACES.saturating_mul(all.len() as u64),
        "every case of every face is taken"
    );
    let mut got: Vec<(&str, &str, &str)> = t
        .xfail_cases
        .iter()
        .map(|(f, x, r)| (f.as_str(), x.as_str(), *r))
        .collect();
    got.sort_unstable();
    let mut want: Vec<(&str, &str, &str)> = VENDORED_EXPECTED.to_vec();
    want.sort_unstable();
    assert!(
        !got.is_empty(),
        "expected differences were pinned, none seen"
    );
    assert_eq!(
        got, want,
        "the vendored suite's expected differences changed (new difference \
         with a reason, or an unexpected pass)"
    );
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
        let before = files.len();
        font_files(std::path::Path::new(d), &mut files, 0);
        println!(
            "font files under {d}: {}",
            files.len().saturating_sub(before)
        );
    }
    let mut t = Tally::default();
    let mut offset = 0usize;
    let all = Cases::new();
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
            &all,
            SYSTEM_STRIDE,
            &mut offset,
            &mut t,
        );
    }
    println!("system font files read: {read}");
    // This suite depends on the machine: its counts and expected
    // differences cannot be pinned, and a machine without fonts compares
    // nothing. Say so loudly; CLAZEL_REQUIRE_SYSTEM_FONTS=1 makes it fail.
    println!(
        "NOTE: the system-fonts suite is MACHINE-DEPENDENT evidence (fonts \
         found: {read}, faces shaped: {}). Only the vendored suite's \
         result is reproducible.",
        t.faces
    );
    if t.faces == 0 {
        println!(
            "WARNING: ZERO system font faces were compared on this machine; \
             this test proved nothing here."
        );
        assert!(
            std::env::var_os("CLAZEL_REQUIRE_SYSTEM_FONTS").is_none(),
            "CLAZEL_REQUIRE_SYSTEM_FONTS is set but no system font face was compared"
        );
    }
    t.report("system fonts vs rustybuzz");
    assert!(t.fail == 0, "{} unexpected differences", t.fail);
}
