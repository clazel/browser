//! The compiled decoder and validator, against hand-built cases and against a second
//! decoder and validator written here from the format's table in `src/spec.rs`, not
//! from the code. This format is ours, so no outside suite or engine exists; the
//! differential is what stands in for one, and the suite names say so.

use clazel_displaylist::exec::{ExecItem, Validator, decode, encode_list};

/// A small generator, so a failure repeats.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64.
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }

    fn byte(&mut self) -> u8 {
        self.next().to_le_bytes().first().copied().unwrap_or(0)
    }
}

/// An item as the second decoder sees it.
#[derive(Debug, PartialEq, Eq, Clone)]
enum Second {
    Fill(i32, i32, u32, u32, u32),
    Push(i32, i32, u32, u32),
    Pop,
    Upload(u32, u16, u16, Vec<u8>),
    Draw(u32, i32, i32, u32),
    Free(u32),
}

fn second_u32(s: &[u8], at: usize) -> Option<u32> {
    let piece: [u8; 4] = s.get(at..at.checked_add(4)?)?.try_into().ok()?;
    Some(u32::from_le_bytes(piece))
}

fn second_i32(s: &[u8], at: usize) -> Option<i32> {
    let piece: [u8; 4] = s.get(at..at.checked_add(4)?)?.try_into().ok()?;
    Some(i32::from_le_bytes(piece))
}

fn second_u16(s: &[u8], at: usize) -> Option<u16> {
    let piece: [u8; 2] = s.get(at..at.checked_add(2)?)?.try_into().ok()?;
    Some(u16::from_le_bytes(piece))
}

/// The second decoder: `from_le_bytes` over the table, nothing shared with the crate.
fn second_decode(mut s: &[u8]) -> Option<Vec<Second>> {
    let mut out = Vec::new();
    while let Some(tag) = s.first() {
        let (item, taken) = match tag {
            1 => (
                Second::Fill(
                    second_i32(s, 1)?,
                    second_i32(s, 5)?,
                    second_u32(s, 9)?,
                    second_u32(s, 13)?,
                    second_u32(s, 17)?,
                ),
                21,
            ),
            2 => (
                Second::Push(
                    second_i32(s, 1)?,
                    second_i32(s, 5)?,
                    second_u32(s, 9)?,
                    second_u32(s, 13)?,
                ),
                17,
            ),
            3 => (Second::Pop, 1),
            4 => {
                let columns = second_u16(s, 5)?;
                let rows = second_u16(s, 7)?;
                let size = usize::from(columns).checked_mul(usize::from(rows))?;
                let end = size.checked_add(9)?;
                (
                    Second::Upload(second_u32(s, 1)?, columns, rows, s.get(9..end)?.to_vec()),
                    end,
                )
            }
            5 => (
                Second::Draw(
                    second_u32(s, 1)?,
                    second_i32(s, 5)?,
                    second_i32(s, 9)?,
                    second_u32(s, 13)?,
                ),
                17,
            ),
            6 => (Second::Free(second_u32(s, 1)?), 5),
            _ => return None,
        };
        out.push(item);
        s = s.get(taken..)?;
    }
    Some(out)
}

fn to_second(item: &ExecItem) -> Second {
    match item {
        ExecItem::FillRect {
            x,
            y,
            width,
            height,
            colour,
        } => Second::Fill(*x, *y, *width, *height, *colour),
        ExecItem::PushClip {
            x,
            y,
            width,
            height,
        } => Second::Push(*x, *y, *width, *height),
        ExecItem::PopClip => Second::Pop,
        ExecItem::UploadMask {
            id,
            columns,
            rows,
            coverage,
        } => Second::Upload(*id, *columns, *rows, coverage.clone()),
        ExecItem::DrawMask { id, x, y, colour } => Second::Draw(*id, *x, *y, *colour),
        ExecItem::FreeMask { id } => Second::Free(*id),
    }
}

/// The second validator, a table and counters written from the rules' prose.
fn second_valid(masks: &mut std::collections::HashMap<u32, u64>, items: &[Second]) -> bool {
    const COORD: i64 = 1 << 23;
    let position = |v: i32| i64::from(v).abs() <= COORD;
    let size = |v: u32| i64::from(v) <= COORD;
    if items.len() > 1 << 20 {
        return false;
    }
    let mut depth = 0u32;
    for item in items {
        match item {
            Second::Fill(x, y, w, h, _) => {
                if !(position(*x) && position(*y) && size(*w) && size(*h)) {
                    return false;
                }
            }
            Second::Push(x, y, w, h) => {
                if !(position(*x) && position(*y) && size(*w) && size(*h)) || depth == 256 {
                    return false;
                }
                depth = depth.saturating_add(1);
            }
            Second::Pop => {
                let Some(d) = depth.checked_sub(1) else {
                    return false;
                };
                depth = d;
            }
            Second::Upload(id, columns, rows, _) => {
                let (c, r) = (u64::from(*columns), u64::from(*rows));
                let total: u64 = masks
                    .values()
                    .sum::<u64>()
                    .saturating_add(c.saturating_mul(r));
                if *id >= 1 << 16
                    || masks.contains_key(id)
                    || c == 0
                    || r == 0
                    || c > 2048
                    || r > 2048
                    || total > 1 << 26
                {
                    return false;
                }
                masks.insert(*id, c.saturating_mul(r));
            }
            Second::Draw(id, x, y, _) => {
                if !(position(*x) && position(*y) && masks.contains_key(id)) {
                    return false;
                }
            }
            Second::Free(id) => {
                if masks.remove(id).is_none() {
                    return false;
                }
            }
        }
    }
    depth == 0
}

fn random_item(rng: &mut Rng) -> ExecItem {
    // Mostly in range, sometimes at or past an edge, so the rules are exercised.
    let coordinate = |rng: &mut Rng| -> i32 {
        match rng.below(8) {
            0 => 8_388_608,
            1 => -8_388_608,
            2 => 8_388_609,
            _ => i32::try_from(rng.below(2000))
                .unwrap_or(0)
                .saturating_sub(1000),
        }
    };
    let side = |rng: &mut Rng| -> u32 {
        match rng.below(12) {
            0 => 8_388_609,
            _ => u32::try_from(rng.below(4000)).unwrap_or(0),
        }
    };
    let id = |rng: &mut Rng| -> u32 { u32::try_from(rng.below(20)).unwrap_or(0) };
    match rng.below(6) {
        0 => ExecItem::FillRect {
            x: coordinate(rng),
            y: coordinate(rng),
            width: side(rng),
            height: side(rng),
            colour: u32::try_from(rng.below(1 << 32)).unwrap_or(0),
        },
        1 => ExecItem::PushClip {
            x: coordinate(rng),
            y: coordinate(rng),
            width: side(rng),
            height: side(rng),
        },
        2 => ExecItem::PopClip,
        3 => {
            let columns = u16::try_from(rng.below(5)).unwrap_or(0);
            let rows = u16::try_from(rng.below(5)).unwrap_or(0);
            let size = usize::from(columns).saturating_mul(usize::from(rows));
            let coverage = (0..size).map(|_| rng.byte()).collect();
            ExecItem::UploadMask {
                id: id(rng),
                columns,
                rows,
                coverage,
            }
        }
        4 => ExecItem::DrawMask {
            id: id(rng),
            x: coordinate(rng),
            y: coordinate(rng),
            colour: 0xFF00_FF00,
        },
        _ => ExecItem::FreeMask { id: id(rng) },
    }
}

fn report(suite: &str, pass: usize, fail: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={pass} xfail=0 fail={fail} total={}",
        pass.saturating_add(fail)
    );
}

/// Hand-built cases, each pinning one line of the format's table or one rule.
#[test]
fn hand_built_cases() {
    let fill = [
        1u8, 0xFF, 0xFF, 0xFF, 0xFF, 2, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0x78, 0x56, 0x34, 0x12,
    ];
    let decoded: &[(&[u8], Option<Vec<ExecItem>>)] = &[
        (&[], Some(vec![])),
        (&[3], Some(vec![ExecItem::PopClip])),
        (&[3, 3], Some(vec![ExecItem::PopClip, ExecItem::PopClip])),
        (
            &fill,
            Some(vec![ExecItem::FillRect {
                x: -1,
                y: 2,
                width: 3,
                height: 4,
                colour: 0x1234_5678,
            }]),
        ),
        (&[6, 1, 0, 0, 0], Some(vec![ExecItem::FreeMask { id: 1 }])),
        (
            &[4, 7, 0, 0, 0, 2, 0, 1, 0, 9, 8],
            Some(vec![ExecItem::UploadMask {
                id: 7,
                columns: 2,
                rows: 1,
                coverage: vec![9, 8],
            }]),
        ),
        // A mask with no pixels decodes; the validator refuses it.
        (
            &[4, 0, 0, 0, 0, 0, 0, 5, 0],
            Some(vec![ExecItem::UploadMask {
                id: 0,
                columns: 0,
                rows: 5,
                coverage: vec![],
            }]),
        ),
        // Unknown tags, including the one kept for Phase 6.
        (&[0], None),
        (&[7], None),
        (&[255], None),
        // Items cut short, and coverage cut short.
        (&[1, 0, 0], None),
        (&[6, 1, 0, 0], None),
        (&[4, 7, 0, 0, 0, 2, 0, 1, 0, 9], None),
        // Sides whose product is large, with no bytes behind them.
        (&[4, 7, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF], None),
        // A good item, then a bad one, is no list.
        (&[3, 9], None),
    ];
    let mut pass = 0usize;
    let mut fail = 0usize;
    for (bytes, want) in decoded {
        if decode(bytes) == *want {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            println!("decode({bytes:?}) gave {:?}", decode(bytes));
        }
    }

    if cfg!(miri) {
        // Every rule below builds a validator, a table of 65,536 entries, and one list
        // has a million items. Under Miri that passes its 300 s guard; the decoding above
        // is what Miri adds here, since the code is safe Rust and the rules are proven.
        report("hand-built cases, decoding only (Miri)", pass, fail);
        assert_eq!(fail, 0);
        return;
    }

    let upload = |id, columns: u16, rows: u16| ExecItem::UploadMask {
        id,
        columns,
        rows,
        coverage: vec![0; usize::from(columns).saturating_mul(usize::from(rows))],
    };
    let draw = |id| ExecItem::DrawMask {
        id,
        x: 0,
        y: 0,
        colour: 0,
    };
    let rect = |x, width| ExecItem::FillRect {
        x,
        y: 0,
        width,
        height: 1,
        colour: 0,
    };
    let clip = ExecItem::PushClip {
        x: 0,
        y: 0,
        width: 1,
        height: 1,
    };
    let rules: Vec<(&str, Vec<ExecItem>, bool)> = vec![
        ("an empty list passes", vec![], true),
        (
            "a rectangle at the edge of the range",
            vec![rect(8_388_608, 8_388_608)],
            true,
        ),
        ("a position past the range", vec![rect(8_388_609, 1)], false),
        (
            "a position past the negative range",
            vec![rect(-8_388_609, 1)],
            false,
        ),
        ("the most negative position", vec![rect(i32::MIN, 1)], false),
        ("a size past the range", vec![rect(0, 8_388_609)], false),
        ("a pushed clip must be popped", vec![clip.clone()], false),
        (
            "a balanced clip",
            vec![clip.clone(), ExecItem::PopClip],
            true,
        ),
        ("popping nothing", vec![ExecItem::PopClip], false),
        (
            "clips at the depth limit",
            {
                let mut v = vec![clip.clone(); 256];
                v.extend(vec![ExecItem::PopClip; 256]);
                v
            },
            true,
        ),
        (
            "clips past the depth limit",
            {
                let mut v = vec![clip.clone(); 257];
                v.extend(vec![ExecItem::PopClip; 257]);
                v
            },
            false,
        ),
        ("drawing a mask never uploaded", vec![draw(1)], false),
        ("drawing after upload", vec![upload(1, 2, 2), draw(1)], true),
        (
            "drawing before upload",
            vec![draw(1), upload(1, 2, 2)],
            false,
        ),
        (
            "drawing after free",
            vec![upload(1, 2, 2), ExecItem::FreeMask { id: 1 }, draw(1)],
            false,
        ),
        (
            "uploading a live id",
            vec![upload(1, 2, 2), upload(1, 2, 2)],
            false,
        ),
        (
            "reusing a freed id",
            vec![
                upload(1, 2, 2),
                ExecItem::FreeMask { id: 1 },
                upload(1, 2, 2),
            ],
            true,
        ),
        ("freeing nothing", vec![ExecItem::FreeMask { id: 1 }], false),
        ("the highest id", vec![upload(65_535, 1, 1)], true),
        ("an id past the table", vec![upload(65_536, 1, 1)], false),
        ("drawing an id past the table", vec![draw(65_536)], false),
        (
            "freeing an id past the table",
            vec![ExecItem::FreeMask { id: u32::MAX }],
            false,
        ),
        ("a mask with no columns", vec![upload(1, 0, 1)], false),
        ("a mask with no rows", vec![upload(1, 1, 0)], false),
        ("the largest side", vec![upload(1, 2048, 1)], true),
        ("a side past the limit", vec![upload(1, 2049, 1)], false),
        (
            "too many items",
            vec![ExecItem::FreeMask { id: 0 }; 1_048_577],
            false,
        ),
    ];
    for (name, items, want) in &rules {
        let mut validator = Validator::empty();
        if validator.validate(items) == *want {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            println!("rule failed: {name}");
        }
    }

    // Masks outlive a list, and the coverage budget counts what is live across lists.
    let mut validator = Validator::empty();
    let held = [
        validator.validate(&[upload(1, 1, 1)]),
        validator.validate(&[draw(1)]),
        validator.validate(&[ExecItem::FreeMask { id: 1 }]),
        !validator.validate(&[draw(1)]),
    ];
    let mut budget = Validator::empty();
    let big = |id| upload(id, 2048, 2048);
    let sixteen: Vec<ExecItem> = (0..16).map(big).collect();
    let budget_cases = [
        budget.validate(&sixteen),
        !budget.validate(&[upload(100, 1, 1)]),
    ];
    let mut freed = Validator::empty();
    let freed_cases = [
        freed.validate(&sixteen),
        freed.validate(&[ExecItem::FreeMask { id: 0 }]),
        freed.validate(&[upload(100, 2048, 2048)]),
    ];
    for ok in held.iter().chain(&budget_cases).chain(&freed_cases) {
        if *ok {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
        }
    }
    report(
        "hand-built cases (one or more per line of the format and per rule)",
        pass,
        fail,
    );
    assert_eq!(fail, 0);
}

/// Random lists: every list writes, reads back the same, agrees with the second
/// decoder, and gets the same verdict from both validators.
#[test]
fn differential_random_lists() {
    let cases = if cfg!(miri) { 40 } else { 20_000usize };
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let (mut pass, mut fail) = (0usize, 0usize);
    let (mut accepted, mut refused) = (0usize, 0usize);
    // A few of these allocate a table, so Miri gets one validator per list and a
    // short run.
    for _ in 0..cases {
        let count = rng.below(12);
        let items: Vec<ExecItem> = (0..count).map(|_| random_item(&mut rng)).collect();
        let Some(bytes) = encode_list(&items) else {
            fail = fail.saturating_add(1);
            continue;
        };
        let read = decode(&bytes);
        let second = second_decode(&bytes);
        let seconds: Vec<Second> = items.iter().map(to_second).collect();
        let mut validator = if cfg!(miri) {
            None
        } else {
            Some(Validator::empty())
        };
        let verdict = validator.as_mut().map(|v| v.validate(&items));
        let mut masks = std::collections::HashMap::new();
        let other = second_valid(&mut masks, &seconds);
        match verdict {
            Some(true) => accepted = accepted.saturating_add(1),
            Some(false) => refused = refused.saturating_add(1),
            None => {}
        }
        let agrees = verdict.is_none_or(|v| v == other);
        if read.as_ref() == Some(&items) && second.as_ref() == Some(&seconds) && agrees {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            println!("disagreement on {items:?}");
        }
    }
    report("second decoder and validator: random lists", pass, fail);
    println!("random lists: {accepted} accepted, {refused} refused");
    assert_eq!(fail, 0);
    if !cfg!(miri) {
        // The generator must exercise both answers, or this tests nothing.
        assert!(accepted > 500, "only {accepted} accepted");
        assert!(refused > 500, "only {refused} refused");
    }
}

/// Random and mutated bytes: the decoder never panics, agrees with the second decoder
/// on what is a list and what it holds, and what it reads writes back to the same
/// bytes.
#[test]
fn differential_hostile_bytes() {
    let cases = if cfg!(miri) { 500 } else { 100_000usize };
    let mut rng = Rng(0xD1B5_4A32_D192_ED03);
    let (mut pass, mut fail) = (0usize, 0usize);
    let (mut lists, mut not_lists) = (0usize, 0usize);
    for case in 0..cases {
        let bytes: Vec<u8> = if case.is_multiple_of(2) {
            let count = rng.below(40);
            (0..count)
                .map(|_| {
                    // Mostly tags and small numbers, so lists do sometimes decode.
                    if rng.below(3) == 0 {
                        rng.byte()
                    } else {
                        u8::try_from(rng.below(8)).unwrap_or(0)
                    }
                })
                .collect()
        } else {
            let count = rng.below(6);
            let items: Vec<ExecItem> = (0..count).map(|_| random_item(&mut rng)).collect();
            let mut written = encode_list(&items).unwrap_or_default();
            if let Some(at) =
                usize::try_from(rng.below(u64::try_from(written.len()).unwrap_or(0).max(1))).ok()
                && let Some(byte) = written.get_mut(at)
            {
                *byte ^= rng.byte();
            }
            if rng.below(3) == 0 {
                let keep = usize::try_from(
                    rng.below(u64::try_from(written.len()).unwrap_or(0).saturating_add(1)),
                )
                .unwrap_or(0);
                written.truncate(keep);
            }
            written
        };
        let ours = decode(&bytes);
        let second = second_decode(&bytes);
        let same = match (&ours, &second) {
            (None, None) => {
                not_lists = not_lists.saturating_add(1);
                true
            }
            (Some(items), Some(others)) => {
                lists = lists.saturating_add(1);
                let mine: Vec<Second> = items.iter().map(to_second).collect();
                mine == *others && encode_list(items).as_deref() == Some(bytes.as_slice())
            }
            _ => false,
        };
        if same {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            println!("disagreement on {bytes:?}");
        }
    }
    report("second decoder: random and mutated bytes", pass, fail);
    println!("hostile bytes: {lists} lists, {not_lists} not lists");
    assert_eq!(fail, 0);
    if !cfg!(miri) {
        assert!(lists > 1000, "only {lists} lists");
        assert!(not_lists > 1000, "only {not_lists} not lists");
    }
}

/// An item whose coverage disagrees with its sides cannot be written.
#[test]
fn the_encoder_refuses_a_wrong_coverage() {
    let wrong = ExecItem::UploadMask {
        id: 0,
        columns: 2,
        rows: 2,
        coverage: vec![0; 3],
    };
    assert_eq!(encode_list(std::slice::from_ref(&wrong)), None);
    assert_eq!(encode_list(&[ExecItem::PopClip, wrong]), None);
    assert_eq!(encode_list(&[ExecItem::PopClip]), Some(vec![3]));
}

/// A list past the limit is refused without being read.
#[test]
fn the_decoder_refuses_a_list_past_the_limit() {
    if cfg!(miri) {
        // 128 MiB under Miri is minutes, and the check is one comparison.
        return;
    }
    let long = vec![3u8; 134_217_729];
    assert!(decode(&long).is_none());
}
