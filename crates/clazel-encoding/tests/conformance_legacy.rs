//! Conformance of "get an encoding" and the legacy decoders
//! (docs/phases/phase-4.md items 4.2 and 4.3).
//!
//! The proofs show the executable functions equal `labels/spec.rs`,
//! `single_byte/spec.rs`, `utf16/spec.rs`, `replacement/spec.rs`,
//! `x_user_defined/spec.rs` and `hooks/spec.rs`, over the tables generated
//! from the standard's `encodings.json` and `indexes.json`. This file
//! checks them against the outside world:
//!
//! 1. WPT `encoding/textdecoder-labels.any.js`: every label, as given,
//!    upper-cased, and with each ASCII whitespace character before, after
//!    and around it, names its encoding (`tests/data/wpt-encoding-legacy/`).
//!    One unit per label, holding all 17 of its checks. Replacement's
//!    labels, which the WPT test skips because `TextDecoder` rejects that
//!    encoding, are checked the same way and not counted.
//! 2. A differential test against `encoding_rs`'s `Encoding::for_label`
//!    (Firefox's label resolution, its own table): every label in its
//!    variants, every encoding name, and random strings built from label
//!    fragments, whitespace, ASCII and non-ASCII bytes. A string's bytes are
//!    its code points (isomorphic decode), the form `encoding_rs` reads.
//! 3. WPT `single-byte-decoder.any.js` (its `TextDecoder` variant): every
//!    label of every single-byte encoding decodes bytes 0 to 254 to WPT's
//!    own copy of the index. One unit per label.
//! 4. WPT `textdecoder-fatal-single-byte.any.js`: for every single-byte
//!    encoding and every byte, fatal decoding of that one byte fails
//!    exactly on the bytes WPT lists. One unit per (encoding, byte).
//! 5. WPT `textdecoder-utf16-surrogates.any.js`: each case decodes to the
//!    expected string, and fails in fatal mode. One unit per case.
//! 6. A differential test of "decode" (§6, BOM sniffing included) against
//!    `encoding_rs`'s `Encoding::decode` for every encoding this crate
//!    decodes, of fatal decoding against its
//!    `decode_without_bom_handling_and_without_replacement`, and of the
//!    single-byte encoder against its `encode` (which also writes `&#n;`
//!    for what it cannot encode), on random inputs. `encoding_rs`'s tables
//!    come from the same `indexes.json`, so this checks the algorithms;
//!    `xtask/src/encoding_indexes.rs` checks the tables against the Unicode
//!    Consortium's mapping files.

use clazel_encoding::labels::exec::{get_an_encoding, name};
use clazel_encoding::labels::spec::Encoding;

/// One converted label case.
struct Label {
    line: usize,
    label: &'static str,
    name: &'static str,
    in_wpt: bool,
}

/// WPT's copy of a single-byte index.
struct Index {
    name: &'static str,
    table: &'static [Option<u32>],
}

/// A single-byte decoding case.
struct SingleByte {
    name: &'static str,
    label: &'static str,
    index: &'static str,
}

/// A fatal single-byte case.
struct Fatal {
    line: usize,
    encoding: &'static str,
    bad: &'static [u8],
}

/// A UTF-16 surrogate case.
struct Utf16 {
    line: usize,
    encoding: &'static str,
    name: &'static str,
    input: &'static [u8],
    expected: &'static [u32],
}

include!("generated/wpt_encoding_legacy.rs");

/// The name of the encoding "get an encoding" gives `label`, if any.
fn ours(label: &[u8]) -> Option<String> {
    let cps: Vec<u32> = label.iter().map(|b| u32::from(*b)).collect();
    get_an_encoding(&cps).map(|e| String::from_utf8_lossy(&name(e)).into_owned())
}

/// `encoding_rs`'s answer for `label`.
fn theirs(label: &[u8]) -> Option<String> {
    encoding_rs::Encoding::for_label(label).map(|e| e.name().to_owned())
}

/// The 17 strings the WPT test builds from a label.
fn variants(label: &str) -> Vec<Vec<u8>> {
    let mut out = vec![
        label.as_bytes().to_vec(),
        label.to_ascii_uppercase().into_bytes(),
    ];
    for ws in WHITESPACE {
        let mut before = vec![*ws];
        before.extend_from_slice(label.as_bytes());
        let mut after = label.as_bytes().to_vec();
        after.push(*ws);
        let mut around = before.clone();
        around.push(*ws);
        out.extend([before, after, around]);
    }
    out
}

#[test]
fn wpt_labels() {
    let mut pass = 0usize;
    let mut failures = Vec::new();
    let mut not_counted = 0usize;
    // Miri checks every 5th label (46 of 229; all of them took 258 s
    // there): it looks for undefined behaviour in the paths they exercise,
    // and the normal test job checks every label.
    let stride = if cfg!(miri) { 5 } else { 1 };
    for case in LABELS.iter().step_by(stride) {
        let bad: Vec<String> = variants(case.label)
            .into_iter()
            .filter(|v| ours(v).as_deref() != Some(case.name))
            .map(|v| format!("{:?}", String::from_utf8_lossy(&v)))
            .collect();
        if !case.in_wpt {
            assert!(
                bad.is_empty(),
                "replacement label {:?}: {bad:?}",
                case.label
            );
            not_counted = not_counted.saturating_add(1);
        } else if bad.is_empty() {
            pass = pass.saturating_add(1);
        } else {
            failures.push(format!(
                "textdecoder-labels.any.js (encodings.js:{}) {:?} => {}: {}",
                case.line,
                case.label,
                case.name,
                bad.join(", ")
            ));
        }
    }
    if cfg!(miri) {
        assert!(failures.is_empty(), "{}", failures.join("\n"));
        return;
    }
    let total = LABELS.iter().filter(|c| c.in_wpt).count();
    println!(
        "clazel-conformance: suite=\"WPT encoding/ labels\" pass={pass} xfail=0 fail={} total={total}",
        failures.len()
    );
    assert_eq!(not_counted, 6, "replacement has six labels");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Deterministic SplitMix64, so a failure reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ z.wrapping_shr(30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ z.wrapping_shr(27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ z.wrapping_shr(31)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(u64::MAX);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
}

/// Every encoding, by number.
fn encoding(n: u8) -> Encoding {
    clazel_encoding::labels::exec::from_number(n)
}

#[test]
fn differential_for_label() {
    let mut inputs: Vec<Vec<u8>> = Vec::new();
    for case in LABELS {
        inputs.extend(variants(case.label));
    }
    for n in 0..40u8 {
        inputs.push(name(encoding(n)));
    }
    // Random strings: pieces of labels, whitespace, other ASCII and
    // non-ASCII bytes, so near misses (a prefix, a stray character, a
    // non-ASCII lookalike) are common.
    let pieces: Vec<&[u8]> = LABELS.iter().map(|c| c.label.as_bytes()).collect();
    let mut rng = Rng(0x0004_0002);
    let count = if cfg!(miri) { 200 } else { 50_000 };
    for _ in 0..count {
        let mut s = Vec::new();
        for _ in 0..rng.below(4) {
            match rng.below(6) {
                0 | 1 => {
                    if let Some(p) = pieces.get(rng.below(pieces.len())) {
                        let cut = rng.below(p.len().saturating_add(1));
                        s.extend_from_slice(p.get(..cut).unwrap_or(p));
                    }
                }
                2 => s.push(*WHITESPACE.get(rng.below(WHITESPACE.len())).unwrap_or(&b' ')),
                3 => s.push(u8::try_from(rng.below(0x80)).unwrap_or(0)),
                4 => s.push(u8::try_from(rng.below(0x100)).unwrap_or(0)),
                _ => s.extend_from_slice(b"-8"),
            }
        }
        inputs.push(s);
    }
    let mut pass = 0usize;
    let mut failures = Vec::new();
    // Miri compares every 7th input (591 of 4,133; all of them took 374 s
    // there): it looks for undefined behaviour in the paths they exercise,
    // and the normal test job compares every input.
    let stride = if cfg!(miri) { 7 } else { 1 };
    for input in inputs.iter().step_by(stride) {
        let (a, b) = (ours(input), theirs(input));
        if a == b {
            pass = pass.saturating_add(1);
        } else if failures.len() < 10 {
            failures.push(format!("{input:02X?}: ours {a:?}, encoding_rs {b:?}"));
        }
    }
    if !cfg!(miri) {
        let fail = inputs.len().saturating_sub(pass);
        println!(
            "clazel-conformance: suite=\"encoding_rs for_label differential\" pass={pass} xfail=0 fail={fail} total={}",
            inputs.len()
        );
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Our encoding named `name` (a name the WPT tables give).
fn by_name(name: &str) -> Option<Encoding> {
    let cps: Vec<u32> = name.bytes().map(u32::from).collect();
    get_an_encoding(&cps)
}

/// `encoding_rs`'s encoding for one of ours.
fn rs(e: Encoding) -> Option<&'static encoding_rs::Encoding> {
    encoding_rs::Encoding::for_label(&name(e))
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

#[test]
fn wpt_single_byte() {
    let buffer: Vec<u8> = (0..255u8).collect();
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for case in SINGLE_BYTE {
        let index = SINGLE_BYTE_INDEXES.iter().find(|i| i.name == case.index);
        let result = match (by_name(case.label), index) {
            (Some(e), Some(index)) if name(e) == case.name.as_bytes() => {
                let out = clazel_encoding::single_byte::decode::decode(e, &buffer);
                let expected: Vec<u32> = buffer
                    .iter()
                    .map(|b| match usize::from(*b).checked_sub(0x80) {
                        None => u32::from(*b),
                        Some(p) => index.table.get(p).copied().flatten().unwrap_or(0xFFFD),
                    })
                    .collect();
                if out == expected {
                    Ok(())
                } else {
                    Err(format!("decodes differently: {out:X?}"))
                }
            }
            (got, _) => Err(format!("label gives {got:?}")),
        };
        match result {
            Ok(()) => pass = pass.saturating_add(1),
            Err(e) => failures.push(format!(
                "{}: {} ({}): {e}",
                case.name, case.label, case.index
            )),
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT encoding/ single-byte decoder\" pass={pass} xfail=0 fail={} total={}",
        failures.len(),
        SINGLE_BYTE.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn wpt_fatal_single_byte() {
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for case in FATAL_SINGLE_BYTE {
        let Some(e) = by_name(case.encoding) else {
            failures.push(format!("line {}: no encoding {}", case.line, case.encoding));
            continue;
        };
        for b in 0..=255u8 {
            let fails = clazel_encoding::single_byte::decode::decode_or_fail(e, &[b]).is_none();
            if fails == case.bad.contains(&b) {
                pass = pass.saturating_add(1);
            } else {
                failures.push(format!(
                    "line {}: {} byte {b:#04X}: fails={fails}",
                    case.line, case.encoding
                ));
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT encoding/ fatal single-byte\" pass={pass} xfail=0 fail={} total={}",
        failures.len(),
        FATAL_SINGLE_BYTE.len().saturating_mul(256)
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn wpt_utf16_surrogates() {
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for case in UTF16_SURROGATES {
        let be = case.encoding.eq_ignore_ascii_case("utf-16be");
        let replaced = clazel_encoding::utf16::decode::decode(be, case.input);
        let fatal = clazel_encoding::utf16::decode::decode_or_fail(be, case.input);
        if replaced == case.expected && fatal.is_none() && by_name(case.encoding).is_some() {
            pass = pass.saturating_add(1);
        } else {
            failures.push(format!(
                "line {}: {} {}: {replaced:X?}, fatal {fatal:X?}",
                case.line, case.encoding, case.name
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"WPT encoding/ UTF-16 surrogates\" pass={pass} xfail=0 fail={} total={}",
        failures.len(),
        UTF16_SURROGATES.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Random bytes: often a byte order mark or a surrogate's high byte, often
/// ASCII, otherwise anything.
fn random_bytes(rng: &mut Rng) -> Vec<u8> {
    let mut v = Vec::new();
    match rng.below(8) {
        0 => v.extend_from_slice(&[0xEF, 0xBB, 0xBF]),
        1 => v.extend_from_slice(&[0xFE, 0xFF]),
        2 => v.extend_from_slice(&[0xFF, 0xFE]),
        _ => {}
    }
    for _ in 0..rng.below(24) {
        let b = match rng.below(5) {
            0 => u8::try_from(rng.below(0x80)).unwrap_or(0),
            1 => *[0xD8u8, 0xDB, 0xDC, 0xDF, 0x00]
                .get(rng.below(5))
                .unwrap_or(&0),
            _ => u8::try_from(rng.below(0x100)).unwrap_or(0),
        };
        v.push(b);
    }
    v
}

#[test]
fn differential_decode() {
    let mut rng = Rng(0x0004_0003);
    let per = if cfg!(miri) { 20 } else { 4000 };
    let mut total = 0usize;
    let mut failures = Vec::new();
    for n in 0..40u8 {
        let e = encoding(n);
        let Some(theirs_e) = rs(e) else {
            failures.push(format!("encoding_rs has no {e:?}"));
            continue;
        };
        let single = clazel_encoding::single_byte::decode::is_single_byte_exec(e);
        for _ in 0..per {
            let input = random_bytes(&mut rng);
            let ours = clazel_encoding::hooks::decode::decode(&input, e);
            if !clazel_encoding::hooks::decode::has_decoder_exec(e)
                && clazel_encoding::hooks::decode::bom_sniff(&input).is_none()
            {
                // The multi-byte encodings (item 4.4) have no decoder, and
                // "decode" says so, unless a byte order mark picks UTF-8 or
                // UTF-16 (§6 decode, step 2), which is checked below.
                if ours.is_some() {
                    failures.push(format!("{e:?} decodes without a decoder"));
                }
                continue;
            }
            total = total.saturating_add(1);
            let theirs = scalars(&theirs_e.decode(&input).0);
            if ours.as_ref() != Some(&theirs) {
                failures.push(format!(
                    "decode {e:?} {input:02X?}: ours {ours:X?}, encoding_rs {theirs:X?}"
                ));
            }
            let fatal_theirs = theirs_e
                .decode_without_bom_handling_and_without_replacement(&input)
                .map(|s| scalars(&s));
            let fatal_ours = if single {
                Some(clazel_encoding::single_byte::decode::decode_or_fail(
                    e, &input,
                ))
            } else if e == Encoding::Utf16Be || e == Encoding::Utf16Le {
                Some(clazel_encoding::utf16::decode::decode_or_fail(
                    e == Encoding::Utf16Be,
                    &input,
                ))
            } else {
                None
            };
            if let Some(f) = fatal_ours {
                total = total.saturating_add(1);
                if f != fatal_theirs {
                    failures.push(format!(
                        "fatal {e:?} {input:02X?}: ours {f:X?}, encoding_rs {fatal_theirs:X?}"
                    ));
                }
            }
        }
    }
    let fail = failures.len();
    println!(
        "clazel-conformance: suite=\"encoding_rs decode differential\" pass={} xfail=0 fail={fail} total={total}",
        total.saturating_sub(fail)
    );
    failures.truncate(10);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn differential_single_byte_encode() {
    let mut rng = Rng(0x0004_0004);
    // Miri: 10 strings per encoding (20 took 106 s there).
    let per = if cfg!(miri) { 10 } else { 2000 };
    let mut total = 0usize;
    let mut failures = Vec::new();
    for n in 1..=28u8 {
        let e = encoding(n);
        let Some(theirs_e) = rs(e) else {
            failures.push(format!("encoding_rs has no {e:?}"));
            continue;
        };
        // Code points the index has, so most inputs are encodable.
        let mapped: Vec<u32> = (0..128usize)
            .filter_map(|p| clazel_encoding::single_byte::decode::index_code_point_exec(e, p))
            .collect();
        for _ in 0..per {
            let mut s = String::new();
            for _ in 0..rng.below(16) {
                let c = match rng.below(4) {
                    0 => u32::try_from(rng.below(0x80)).unwrap_or(0),
                    1 | 2 => mapped.get(rng.below(mapped.len())).copied().unwrap_or(0x41),
                    _ => u32::try_from(rng.below(0x11_0000)).unwrap_or(0),
                };
                if let Some(c) = char::from_u32(c) {
                    s.push(c);
                }
            }
            total = total.saturating_add(1);
            let ours = clazel_encoding::single_byte::encode::encode(e, &scalars(&s));
            let (theirs, _, _) = theirs_e.encode(&s);
            if ours != theirs.as_ref() {
                failures.push(format!(
                    "encode {e:?} {s:?}: ours {ours:02X?}, encoding_rs {theirs:02X?}"
                ));
            }
        }
    }
    let fail = failures.len();
    println!(
        "clazel-conformance: suite=\"encoding_rs single-byte encode differential\" pass={} xfail=0 fail={fail} total={total}",
        total.saturating_sub(fail)
    );
    failures.truncate(10);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
