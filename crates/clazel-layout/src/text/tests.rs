//! Unit tests of white space processing and line breaking, per rule, and
//! the examples CSS Text 3 §4.1.2 gives for `pre-wrap`.

use super::collapse::{Item, Kind, collapse};
use super::lines::{break_lines, initial_tab_size, max_content, min_content, tab_advance, trim};
use super::wrap::{Wrap, opportunities};
use super::{Lb, Props, TextStyle, breaks};
use clazel_style::cascade::computed::{OverflowWrap, WhiteSpace, WordBreak};

/// One `ch` in 26.6 for these tests' monospace font.
const CH: i32 = 64;

fn ws(w: WhiteSpace) -> TextStyle {
    TextStyle::with_white_space(w)
}

/// The text after Phase I of one item.
fn collapsed(text: &str, style: TextStyle) -> String {
    collapse(&[Item::Text { text, style }])
        .iter()
        .map(|u| u.ch)
        .collect()
}

/// The text with `|` at each soft wrap opportunity, `!` at each forced
/// break other than the last, and `~` at each emergency one.
fn marked(items: &[Item<'_>]) -> String {
    let units = collapse(items);
    let wraps = opportunities(&units);
    let mut out = String::new();
    let last = units.len().saturating_sub(1);
    for (i, (u, w)) in units.iter().zip(&wraps).enumerate() {
        out.push(if u.kind == Kind::Atomic { '#' } else { u.ch });
        match w {
            Wrap::Soft => out.push('|'),
            Wrap::Forced if i != last => out.push('!'),
            Wrap::Emergency { .. } => out.push('~'),
            _ => {}
        }
    }
    out
}

fn text(t: &str, style: TextStyle) -> Item<'_> {
    Item::Text { text: t, style }
}

/// Lines of `t` (one style) at `available` ch, each unit one ch wide, as
/// the text of each line from its first to its last unit.
fn lines_of(t: &str, style: TextStyle, available: i32) -> Vec<String> {
    let units = collapse(&[text(t, style)]);
    let wraps = opportunities(&units);
    break_lines(&units, &wraps, available.saturating_mul(CH), |_, _| CH)
        .iter()
        .map(|l| {
            units
                .get(l.start..l.end)
                .unwrap_or_default()
                .iter()
                .map(|u| u.ch)
                .collect()
        })
        .collect()
}

// §4.1.1 Phase I.

#[test]
fn normal_collapses_spaces_and_tabs() {
    let n = ws(WhiteSpace::Normal);
    assert_eq!(collapsed("a  b\t\tc", n), "a b c");
    // Step 1 removes spaces around a segment break; step 2 makes it a space.
    assert_eq!(collapsed("a  \n  b", n), "a b");
    // §4.1.3: a segment break after another is removed.
    assert_eq!(collapsed("a\n\nb", n), "a b");
    assert_eq!(collapsed("a \n \n b", n), "a b");
    // §4: a carriage return is a space.
    assert_eq!(collapsed("a\r\rb", n), "a b");
    // Leading and trailing spaces stay for Phase II.
    assert_eq!(collapsed("  a  ", n), " a ");
    // No-break spaces and other space separators are not white space.
    assert_eq!(collapsed("a\u{A0} \u{2003} b", n), "a\u{A0} \u{2003} b");
}

#[test]
fn nowrap_collapses_like_normal() {
    assert_eq!(collapsed("a \t\n b", ws(WhiteSpace::Nowrap)), "a b");
}

#[test]
fn pre_line_keeps_segment_breaks() {
    let units = collapse(&[text("a  \n  b\n\nc", ws(WhiteSpace::PreLine))]);
    let s: String = units.iter().map(|u| u.ch).collect();
    assert_eq!(s, "a\nb\n\nc");
    assert_eq!(
        units.get(1).map(|u| u.kind),
        Some(Kind::ForcedBreak),
        "a preserved segment break is a forced break"
    );
}

#[test]
fn pre_and_pre_wrap_preserve_everything() {
    for w in [
        WhiteSpace::Pre,
        WhiteSpace::PreWrap,
        WhiteSpace::BreakSpaces,
    ] {
        let units = collapse(&[text(" a \t\n b", ws(w))]);
        let kinds: Vec<Kind> = units.iter().map(|u| u.kind).collect();
        assert_eq!(
            kinds,
            [
                Kind::PreservedSpace,
                Kind::Char,
                Kind::PreservedSpace,
                Kind::PreservedTab,
                Kind::ForcedBreak,
                Kind::PreservedSpace,
                Kind::Char
            ],
            "{w:?}"
        );
    }
}

#[test]
fn collapsing_crosses_inline_boundaries() {
    let n = ws(WhiteSpace::Normal);
    let units = collapse(&[text("a ", n), text(" b", n)]);
    let s: String = units.iter().map(|u| u.ch).collect();
    assert_eq!(s, "a b");
    // The space kept is the first one's.
    assert_eq!(units.get(1).map(|u| (u.item, u.offset)), Some((0, 1)));
    // A preserved space is not "another collapsible space".
    let units = collapse(&[text("a ", ws(WhiteSpace::Pre)), text(" b", n)]);
    assert_eq!(units.len(), 4);
}

#[test]
fn bidi_controls_are_skipped_as_neighbours() {
    // U+200E between two spaces does not stop the second collapsing.
    assert_eq!(
        collapsed("a \u{200E} b", ws(WhiteSpace::Normal)),
        "a \u{200E}b"
    );
}

// §5 soft wrap opportunities.

#[test]
fn normal_wraps_after_spaces() {
    let n = ws(WhiteSpace::Normal);
    assert_eq!(marked(&[text("the cat", n)]), "the |cat");
    // UAX #14 LB13: no break before ")" even after a space.
    assert_eq!(marked(&[text("a )", n)]), "a )");
    // LB21: a break after a hyphen.
    assert_eq!(marked(&[text("well-known", n)]), "well-|known");
}

#[test]
fn pre_and_nowrap_never_wrap() {
    for w in [WhiteSpace::Pre, WhiteSpace::Nowrap] {
        assert_eq!(marked(&[text("a b-c", ws(w))]), "a b-c", "{w:?}");
    }
}

#[test]
fn forced_breaks() {
    assert_eq!(marked(&[text("a\nb", ws(WhiteSpace::Pre))]), "a\n!b");
    // §5.5: BK and NL "regardless of the white-space value".
    assert_eq!(
        marked(&[text("a\u{2028}b", ws(WhiteSpace::Nowrap))]),
        "a\u{2028}!b"
    );
    assert_eq!(
        marked(&[text("a\u{85}b", ws(WhiteSpace::Normal))]),
        "a\u{85}!b"
    );
}

#[test]
fn pre_wrap_wraps_at_the_end_of_a_space_sequence() {
    // Not between the space and the tab (UAX #14 alone would: LB18).
    assert_eq!(
        marked(&[text("a \t b", ws(WhiteSpace::PreWrap))]),
        "a \t |b"
    );
}

#[test]
fn break_spaces_wraps_after_every_space() {
    assert_eq!(
        marked(&[text("a  b", ws(WhiteSpace::BreakSpaces))]),
        "a | |b"
    );
}

#[test]
fn word_break() {
    let style = |wb| TextStyle {
        word_break: wb,
        ..TextStyle::INITIAL
    };
    // Ideographs break between each other unless keep-all.
    assert_eq!(
        marked(&[text("漢字漢", style(WordBreak::Normal))]),
        "漢|字|漢"
    );
    assert_eq!(
        marked(&[text("漢字 漢", style(WordBreak::KeepAll))]),
        "漢字 |漢"
    );
    // Hangul: keep-all keeps words together.
    assert_eq!(
        marked(&[text("한국어", style(WordBreak::Normal))]),
        "한|국|어"
    );
    assert_eq!(
        marked(&[text("한국어", style(WordBreak::KeepAll))]),
        "한국어"
    );
    // break-all: letters and digits as ID.
    assert_eq!(marked(&[text("ab1", style(WordBreak::BreakAll))]), "a|b|1");
    // break-all leaves punctuation alone (LB13).
    assert_eq!(marked(&[text("a)", style(WordBreak::BreakAll))]), "a)");
}

#[test]
fn thai_breaks_between_letters() {
    // §5.5 without a dictionary: SA letters as ID. U+0E01 U+0E32 U+0E23.
    assert_eq!(
        marked(&[text("\u{E01}\u{E32}\u{E23}", TextStyle::INITIAL)]),
        "\u{E01}|\u{E32}|\u{E23}"
    );
    // The default rules keep them together (SA as AL).
    let p: Vec<Props> = "\u{E01}\u{E32}".chars().map(Props::of).collect();
    assert_eq!(p.first().map(|p| p.class), Some(Lb::AL));
    assert_eq!(breaks(&p).first(), Some(&super::Break::Prohibited));
}

#[test]
fn overflow_wrap() {
    let style = |wb, ow| TextStyle {
        word_break: wb,
        overflow_wrap: ow,
        ..TextStyle::INITIAL
    };
    let units = collapse(&[text(
        "ab c\u{301}d",
        style(WordBreak::Normal, OverflowWrap::Anywhere),
    )]);
    let wraps = opportunities(&units);
    assert_eq!(
        wraps,
        [
            Wrap::Emergency { min_content: true },
            // Not before the space (LB7); a soft one after it.
            Wrap::None,
            Wrap::Soft,
            // Not between c and its combining accent (LB9).
            Wrap::None,
            Wrap::Emergency { min_content: true },
            Wrap::Forced,
        ]
    );
    let units = collapse(&[text(
        "ab",
        style(WordBreak::Normal, OverflowWrap::BreakWord),
    )]);
    assert_eq!(
        opportunities(&units).first(),
        Some(&Wrap::Emergency { min_content: false })
    );
    // word-break: break-word is overflow-wrap: anywhere.
    let units = collapse(&[text(
        "ab",
        style(WordBreak::BreakWord, OverflowWrap::Normal),
    )]);
    assert_eq!(
        opportunities(&units).first(),
        Some(&Wrap::Emergency { min_content: true })
    );
    // Not where wrapping is off.
    let units = collapse(&[text(
        "ab",
        TextStyle {
            white_space: WhiteSpace::Nowrap,
            ..style(WordBreak::BreakWord, OverflowWrap::Normal)
        },
    )]);
    assert_eq!(opportunities(&units).first(), Some(&Wrap::None));
}

#[test]
fn atomic_inlines() {
    let n = TextStyle::INITIAL;
    let atomic = Item::Atomic { style: n };
    // Before and after, even after an opening parenthesis (LB14).
    assert_eq!(marked(&[text("a", n), atomic, text("b", n)]), "a|#|b");
    assert_eq!(marked(&[text("(", n), atomic]), "(|#");
    // U+00A0 does not prevent it; other GL and WJ do.
    assert_eq!(marked(&[text("\u{A0}", n), atomic]), "\u{A0}|#");
    assert_eq!(marked(&[text("\u{2060}", n), atomic]), "\u{2060}#");
    assert_eq!(marked(&[atomic, text("\u{202F}", n)]), "#\u{202F}");
    // Not before a space; after it.
    assert_eq!(marked(&[atomic, text(" b", n)]), "# |b");
}

// §4.1.2 Phase II and choosing lines.

#[test]
fn pre_wrap_example_centered() {
    // §4.1.2's first example: `<p> 0 </p>`, pre-wrap, 5ch: the final space
    // is before a forced break (the end of the block), so it hangs only
    // conditionally.
    let units = collapse(&[text(" 0 ", ws(WhiteSpace::PreWrap))]);
    let t = trim(&units, 0, 3, true);
    assert_eq!((t.start, t.hang, t.end, t.conditional), (0, 2, 3, true));
}

#[test]
fn pre_wrap_example_three_ch() {
    // §4.1.2's second example: `<p> 0 0 0 0 </p>`, pre-wrap, 3ch, renders
    // " 0 ", "0 0 ", "0 ".
    let p = ws(WhiteSpace::PreWrap);
    assert_eq!(lines_of(" 0 0 0 0 ", p, 3), [" 0 ", "0 0 ", "0 "]);
    // The third: `<p>0 0 0 0 </p>` renders "0 0 ", "0 0 ": "The last line
    // is not wrapped before the last 0 because characters that
    // conditionally hang are not considered when measuring the line's
    // contents for fit."
    assert_eq!(lines_of("0 0 0 0 ", p, 3), ["0 0 ", "0 0 "]);
    let units = collapse(&[text("0 0 0 0 ", p)]);
    let wraps = opportunities(&units);
    let lines = break_lines(&units, &wraps, 3 * CH, |_, _| CH);
    let widths: Vec<i32> = lines.iter().map(|l| l.width).collect();
    assert_eq!(widths, [3 * CH, 3 * CH]);
    let last = lines.last().copied();
    let t = last.map(|l| trim(&units, l.start, l.end, l.forced));
    assert_eq!(
        t.map(|t| (t.hang, t.end, t.conditional)),
        Some((7, 8, true))
    );
}

#[test]
fn normal_trims_spaces_at_line_ends() {
    let n = ws(WhiteSpace::Normal);
    assert_eq!(lines_of(" aa bb cc ", n, 5), [" aa bb ", "cc "]);
    let units = collapse(&[text(" aa bb cc ", n)]);
    // The first line: the leading space removed, the trailing one too.
    let t = trim(&units, 0, 7, false);
    assert_eq!((t.start, t.hang, t.end), (1, 6, 6));
    // A trailing U+1680 is removed under normal; an em space hangs.
    let units = collapse(&[text("a\u{1680}", n)]);
    let t = trim(&units, 0, 2, true);
    assert_eq!((t.hang, t.end), (1, 1));
    let units = collapse(&[text("a\u{2003}", n)]);
    let t = trim(&units, 0, 2, true);
    assert_eq!((t.hang, t.end, t.conditional), (1, 2, false));
}

#[test]
fn forced_break_ends_a_line_and_is_not_content() {
    let p = ws(WhiteSpace::Pre);
    assert_eq!(lines_of("ab\ncd", p, 1), ["ab\n", "cd"]);
    let units = collapse(&[text("ab \ncd", ws(WhiteSpace::PreWrap))]);
    let t = trim(&units, 0, 4, true);
    assert_eq!((t.start, t.hang, t.end, t.conditional), (0, 2, 3, true));
}

#[test]
fn overflow_wrap_is_used_only_without_soft_opportunities() {
    let any = TextStyle {
        overflow_wrap: OverflowWrap::Anywhere,
        ..TextStyle::INITIAL
    };
    assert_eq!(lines_of("abcdef", any, 4), ["abcd", "ef"]);
    assert_eq!(lines_of("ab cdef", any, 4), ["ab ", "cdef"]);
    // Without overflow-wrap, a long word overflows to the next opportunity.
    assert_eq!(
        lines_of("abcdef gh", TextStyle::INITIAL, 4),
        ["abcdef ", "gh"]
    );
}

#[test]
fn intrinsic_sizes() {
    let width = |_: usize, _: i32| CH;
    let n = TextStyle::INITIAL;
    let units = collapse(&[text("aa bbbb c", n)]);
    let wraps = opportunities(&units);
    assert_eq!(min_content(&units, &wraps, width), 4 * CH);
    assert_eq!(max_content(&units, &wraps, width), 9 * CH);
    // anywhere counts for min-content; break-word does not.
    for (ow, min) in [
        (OverflowWrap::Anywhere, CH),
        (OverflowWrap::BreakWord, 4 * CH),
    ] {
        let style = TextStyle {
            overflow_wrap: ow,
            ..n
        };
        let units = collapse(&[text("aa bbbb", style)]);
        let wraps = opportunities(&units);
        assert_eq!(min_content(&units, &wraps, width), min, "{ow:?}");
    }
}

#[test]
fn tab_stops() {
    let tab = initial_tab_size(CH);
    assert_eq!(tab, 8 * CH);
    let half = CH / 2;
    assert_eq!(tab_advance(0, tab, half), 8 * CH);
    assert_eq!(tab_advance(3 * CH, tab, half), 5 * CH);
    // Less than 0.5ch to the next stop: the one after.
    assert_eq!(tab_advance(8 * CH - 10, tab, half), 8 * CH + 10);
    assert_eq!(tab_advance(5 * CH, 0, half), 0);
    // Saturates instead of overflowing.
    assert!(tab_advance(i32::MAX, i32::MAX, i32::MAX) >= 0);
}

// The step formulations against the first readings (`reference.rs`).

/// Under Miri, check one case in this many (Miri runs this code thousands
/// of times slower; the cases are generated, so a stride keeps their
/// spread).
const MIRI_STRIDE: usize = if cfg!(miri) { 997 } else { 1 };

/// Every line breaking class, each as properties with no flags, then the
/// flag combinations the rules read: Pi and Pf quotation marks, East Asian
/// OP, CP and QU, U+25CC, an unassigned pictographic, East Asian ID.
fn alphabet() -> Vec<Props> {
    let mut classes: Vec<Lb> = Vec::new();
    for &(_, _, c) in super::data::LINE_BREAK.iter() {
        if !classes.contains(&c) {
            classes.push(c);
        }
    }
    let plain = |class| Props {
        class,
        ..Props::LETTER_A
    };
    let mut out: Vec<Props> = classes.into_iter().map(plain).collect();
    out.extend([
        Props {
            pi: true,
            ..plain(Lb::QU)
        },
        Props {
            pf: true,
            ..plain(Lb::QU)
        },
        Props {
            east_asian: true,
            ..plain(Lb::QU)
        },
        Props {
            east_asian: true,
            ..plain(Lb::OP)
        },
        Props {
            east_asian: true,
            ..plain(Lb::CP)
        },
        Props {
            east_asian: true,
            ..plain(Lb::ID)
        },
        Props {
            dotted_circle: true,
            ..plain(Lb::AL)
        },
        Props {
            pictographic_unassigned: true,
            ..plain(Lb::ID)
        },
    ]);
    out
}

/// A small deterministic generator (a 64-bit linear congruential one).
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let n = u64::try_from(n).unwrap_or(1).max(1);
        usize::try_from((self.0 >> 33).checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
}

#[test]
fn uax14_step_matches_reference() {
    let alphabet = alphabet();
    let k = alphabet.len();
    let mut checked: usize = 0;
    // Every string of length 1 to 3 over the alphabet.
    let total3 = k.saturating_mul(k).saturating_mul(k);
    for n in (0..total3).step_by(MIRI_STRIDE) {
        for len in 1..=3usize {
            let text: Vec<Props> = (0..len)
                .filter_map(|d| {
                    alphabet
                        .get(n / k.pow(u32::try_from(d).unwrap_or(0)) % k)
                        .copied()
                })
                .collect();
            assert_eq!(
                super::breaks_with_rules(&text),
                super::reference::breaks_with_rules(&text),
                "{text:?}"
            );
            checked = checked.saturating_add(1);
        }
    }
    // Random strings of length 4 to 16, with long runs of spaces, marks,
    // RIs and number punctuation more likely than the alphabet makes them.
    let runs: Vec<Props> = [
        Lb::SP,
        Lb::CM,
        Lb::ZWJ,
        Lb::RI,
        Lb::IS,
        Lb::SY,
        Lb::NU,
        Lb::QU,
    ]
    .iter()
    .map(|&class| Props {
        class,
        ..Props::LETTER_A
    })
    .collect();
    let mut rng = Lcg(5_812);
    let cases: usize = if cfg!(miri) { 60 } else { 200_000 };
    for _ in 0..cases {
        let len = 4usize.saturating_add(rng.below(13));
        let text: Vec<Props> = (0..len)
            .filter_map(|_| {
                if rng.below(2) == 0 {
                    runs.get(rng.below(runs.len())).copied()
                } else {
                    alphabet.get(rng.below(k)).copied()
                }
            })
            .collect();
        assert_eq!(
            super::breaks_with_rules(&text),
            super::reference::breaks_with_rules(&text),
            "{text:?}"
        );
        checked = checked.saturating_add(1);
    }
    assert!(checked > 0);
}

#[test]
fn collapse_step_matches_reference() {
    use super::collapse::{Raw, Unit, collapse_raw};
    let raws = [
        Raw::Space,
        Raw::Tab,
        Raw::SegmentBreak,
        Raw::Bidi,
        Raw::Other(Kind::Char),
    ];
    let styles = [
        WhiteSpace::Normal,
        WhiteSpace::Nowrap,
        WhiteSpace::Pre,
        WhiteSpace::PreWrap,
        WhiteSpace::BreakSpaces,
        WhiteSpace::PreLine,
    ];
    let symbols: Vec<(Raw, WhiteSpace)> = raws
        .iter()
        .flat_map(|&r| styles.iter().map(move |&w| (r, w)))
        .collect();
    let k = symbols.len();
    let make = |seq: &[(Raw, WhiteSpace)]| -> Vec<(Raw, Unit)> {
        seq.iter()
            .enumerate()
            .map(|(i, &(r, w))| {
                let ch = match r {
                    Raw::Space => ' ',
                    Raw::Tab => '\t',
                    Raw::SegmentBreak => '\n',
                    Raw::Bidi => '\u{200E}',
                    Raw::Other(_) => 'a',
                };
                (
                    r,
                    Unit {
                        ch,
                        kind: Kind::Char,
                        item: i,
                        offset: 0,
                        style: ws(w),
                    },
                )
            })
            .collect()
    };
    // Every sequence of length 1 to 4 over 30 symbols.
    let total4 = k.pow(4);
    for n in (0..total4).step_by(MIRI_STRIDE) {
        for len in 1..=4usize {
            let seq: Vec<(Raw, WhiteSpace)> = (0..len)
                .filter_map(|d| {
                    symbols
                        .get(n / k.pow(u32::try_from(d).unwrap_or(0)) % k)
                        .copied()
                })
                .collect();
            let raw = make(&seq);
            assert_eq!(
                collapse_raw(&raw),
                super::reference::collapse_raw(&raw),
                "{seq:?}"
            );
        }
    }
    // Random sequences of length 5 to 24.
    let mut rng = Lcg(77);
    let cases: usize = if cfg!(miri) { 60 } else { 100_000 };
    for _ in 0..cases {
        let len = 5usize.saturating_add(rng.below(20));
        let seq: Vec<(Raw, WhiteSpace)> = (0..len)
            .filter_map(|_| symbols.get(rng.below(k)).copied())
            .collect();
        let raw = make(&seq);
        assert_eq!(
            collapse_raw(&raw),
            super::reference::collapse_raw(&raw),
            "{seq:?}"
        );
    }
}
