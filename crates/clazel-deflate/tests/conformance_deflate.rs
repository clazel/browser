//! DEFLATE and zlib conformance (phase-6.md item 6.2).
//!
//! `src/` has the decoder; this file checks it against the world:
//!
//! 1. Wuffs' `test/data` streams (`tests/data/wuffs-deflate/`), whose
//!    expected output is the text beside each: every stream, raw and zlib,
//!    must decode to exactly it, using exactly the bytes of the stream, and
//!    `miniz_oxide` must agree.
//! 2. Wuffs' `artificial-deflate` corner cases
//!    (`tests/data/wuffs-deflate-artificial/`): each stream's
//!    `.decompressed` file, with `distance-code-31` (an invalid stream, whose
//!    expected output is empty) required to fail.
//! 3. A differential test against `miniz_oxide` on mutated streams: the
//!    vendored streams, ones made by `miniz_oxide`'s compressor at every
//!    level, and hand-made ones, each with every single-byte change at
//!    chosen offsets, every truncation, and random multi-byte changes. A
//!    stream is "agreed" if both decoders fail, or both succeed with the
//!    same output. Where they differ the difference must be one of the
//!    listed ones (`LISTED`), each with its reason; any other difference
//!    fails the test.
//!
//! The streaming decoder is also checked against a naive transcription of
//! the spec (`tests/model/mod.rs`) in `tests/stream.rs`.

use std::collections::BTreeMap;

use clazel_deflate::oneshot::{inflate, zlib_decompress};
use clazel_deflate::spec::Error;

mod common;

mod model;

use common::{
    BitWriter, Rng, adler32, at, canonical, corpus_raw, corpus_with_data, corpus_zlib, handmade,
    zlib_wrap,
};

include!("generated/wuffs_deflate.rs");

mod artificial {
    include!("generated/wuffs_deflate_artificial.rs");
}

const LIMIT: u64 = 1 << 21;

fn main_file(name: &str) -> &'static [u8] {
    FILES
        .iter()
        .find(|c| c.file == name)
        .map_or(&[], |c| c.bytes)
}

fn artificial_file(name: &str) -> &'static [u8] {
    artificial::FILES
        .iter()
        .find(|c| c.file == name)
        .map_or(&[], |c| c.bytes)
}

fn report(suite: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
}

/// `miniz_oxide`'s answer for a raw stream.
fn theirs_raw(input: &[u8]) -> Result<Vec<u8>, String> {
    miniz_oxide::inflate::decompress_to_vec_with_limit(input, LIMIT as usize)
        .map_err(|e| format!("{:?}", e.status))
}

/// `miniz_oxide`'s answer for a zlib stream.
fn theirs_zlib(input: &[u8]) -> Result<Vec<u8>, String> {
    miniz_oxide::inflate::decompress_to_vec_zlib_with_limit(input, LIMIT as usize)
        .map_err(|e| format!("{:?}", e.status))
}

#[test]
fn wuffs_streams() {
    assert!(FILES.iter().all(|c| c.sha256.len() == 64));
    // (stream, expected output, zlib?)
    let cases: [(&str, &str, bool); 5] = [
        ("romeo.txt.deflate", "romeo.txt", false),
        ("romeo.txt.fixed-huff.deflate", "romeo.txt", false),
        ("romeo.txt.zlib", "romeo.txt", true),
        ("midsummer.txt.zlib", "midsummer.txt", true),
        ("pi.txt.zlib", "pi.txt", true),
    ];
    let mut pass = 0;
    let mut failed = 0;
    for (stream, text, is_zlib) in cases {
        let input = main_file(stream);
        let want = main_file(text);
        let ours = if is_zlib {
            zlib_decompress(input, LIMIT)
        } else {
            inflate(input, LIMIT)
        };
        let theirs = if is_zlib {
            theirs_zlib(input)
        } else {
            theirs_raw(input)
        };
        let ok = !input.is_empty()
            && !want.is_empty()
            && ours == Ok((want.to_vec(), input.len()))
            && theirs.as_deref() == Ok(want);
        if ok {
            pass += 1;
        } else {
            failed += 1;
            println!("FAIL {stream}: ours {:?}", ours.map(|d| d.0.len()));
        }
    }
    report(
        "Wuffs test/data DEFLATE and zlib",
        pass,
        0,
        failed,
        cases.len(),
    );
    assert_eq!(failed, 0);
}

#[test]
fn wuffs_artificial() {
    assert!(artificial::FILES.iter().all(|c| c.sha256.len() == 64));
    let names = [
        "backref-crosses-blocks",
        "degenerate-huffman-0-bit",
        "degenerate-huffman-1-bit",
        "distance-32768",
        "distance-code-31",
        "huffman-primlen-9",
    ];
    let mut pass = 0;
    let mut failed = 0;
    for name in names {
        let input = artificial_file(&format!("{name}.deflate"));
        let want = artificial_file(&format!("{name}.deflate.decompressed"));
        let ours = inflate(input, LIMIT);
        let theirs = theirs_raw(input);
        let ok = if name == "distance-code-31" {
            // The stream names distance code 31, which "will never actually
            // occur" (RFC 1951 §3.2.6): it must fail, and `miniz_oxide` fails too.
            want.is_empty() && ours == Err(Error::InvalidDistanceSymbol) && theirs.is_err()
        } else {
            !input.is_empty()
                && !want.is_empty()
                && ours == Ok((want.to_vec(), input.len()))
                && theirs.as_deref() == Ok(want)
        };
        if ok {
            pass += 1;
        } else {
            failed += 1;
            println!("FAIL {name}: ours {:?}", ours.map(|d| d.0.len()));
        }
    }
    report("Wuffs artificial-deflate", pass, 0, failed, names.len());
    assert_eq!(failed, 0);
}

/// The differences between this decoder and `miniz_oxide` that are expected,
/// each with its reason. A difference is named `theirs-only <our error>`
/// (this decoder refuses a stream `miniz_oxide` accepts), `ours-only (..)` or
/// `both-ok-different-output ..`. **None has been seen** over the streams
/// below (including the hand-made ones that hit each error and the ones
/// with incomplete and over-subscribed codes), so the list is empty and any
/// difference fails the test.
const LISTED: &[(&str, &str)] = &[];

#[derive(Default)]
struct Tally {
    total: usize,
    agree: usize,
    listed: BTreeMap<String, usize>,
    unlisted: BTreeMap<String, (usize, String)>,
}

impl Tally {
    fn compare(&mut self, what: &str, input: &[u8], is_zlib: bool) {
        self.total = self.total.saturating_add(1);
        let ours = if is_zlib {
            zlib_decompress(input, LIMIT)
        } else {
            inflate(input, LIMIT)
        };
        let theirs = if is_zlib {
            theirs_zlib(input)
        } else {
            theirs_raw(input)
        };
        let key = match (&ours, &theirs) {
            (Ok((a, _)), Ok(b)) if a == b => {
                self.agree = self.agree.saturating_add(1);
                return;
            }
            (Err(_), Err(_)) => {
                self.agree = self.agree.saturating_add(1);
                return;
            }
            (Ok((a, _)), Ok(b)) => format!(
                "both-ok-different-output ours {} theirs {}",
                a.len(),
                b.len()
            ),
            (Ok(_), Err(t)) => format!("ours-only (theirs {t})"),
            (Err(e), Ok(_)) => format!("theirs-only {e:?}"),
        };
        let listed = LISTED.iter().any(|(k, _)| *k == key);
        if listed {
            {
                let c = self.listed.entry(key).or_insert(0usize);
                *c = c.saturating_add(1);
            }
        } else {
            let slot = self
                .unlisted
                .entry(key.split(" (").next().unwrap_or("").to_owned())
                .or_insert((0, String::new()));
            slot.0 = slot.0.saturating_add(1);
            if slot.1.is_empty() {
                slot.1 = format!("{what}: {key}");
            }
        }
    }
}

/// The stride of the mutants of a stream of this length: about a hundred
/// prefixes, a few hundred bit flips (a coarser stride under Miri).
fn stride_for(len: usize) -> usize {
    if cfg!(miri) {
        (len / 20).max(7)
    } else {
        (len / 100).max(1)
    }
}

/// Every mutant of `input` that is checked, as `(description, bytes)`.
fn mutants(input: &[u8], seed: u64, stride: usize) -> Vec<(String, Vec<u8>)> {
    let mut out = Vec::new();
    // Every truncation (a prefix of every length).
    for n in (0..input.len()).step_by(stride) {
        out.push((
            format!("prefix {n}"),
            input.get(..n).unwrap_or(&[]).to_vec(),
        ));
    }
    // A single bit flipped, at a stride of bits.
    let mut bit = 0usize;
    while bit < input.len().saturating_mul(8) {
        let mut m = input.to_vec();
        if let Some(b) = m.get_mut(bit / 8) {
            *b ^= 1 << (bit % 8);
        }
        out.push((format!("flip bit {bit}"), m));
        bit = bit.saturating_add(stride.saturating_mul(3).max(1));
    }
    // Random byte changes, one to three of them.
    let mut rng = Rng::new(seed);
    for k in 0..input.len().checked_div(stride).unwrap_or(0).clamp(8, 100) {
        let mut m = input.to_vec();
        let n = 1usize.saturating_add(rng.below(3));
        for _ in 0..n {
            let i = rng.below(m.len());
            if let Some(b) = m.get_mut(i) {
                *b = rng.next() as u8;
            }
        }
        out.push((format!("random {k}"), m));
    }
    out
}

#[test]
fn differential_miniz() {
    let mut raw = vec![
        (
            "romeo.txt.deflate".to_owned(),
            main_file("romeo.txt.deflate").to_vec(),
        ),
        (
            "romeo.txt.fixed-huff.deflate".to_owned(),
            main_file("romeo.txt.fixed-huff.deflate").to_vec(),
        ),
    ];
    for name in [
        "backref-crosses-blocks",
        "degenerate-huffman-0-bit",
        "degenerate-huffman-1-bit",
        "distance-32768",
        "distance-code-31",
        "huffman-primlen-9",
    ] {
        raw.push((
            name.to_owned(),
            artificial_file(&format!("{name}.deflate")).to_vec(),
        ));
    }
    raw.extend(corpus_raw());
    // The hand-made streams that each hit one error (a stream the decoders
    // might treat differently is what this is for).
    for (name, format, stream, _) in error_streams() {
        if format == Format::Raw {
            raw.push((format!("error: {name}"), stream));
        }
    }
    let mut zl = vec![
        (
            "romeo.txt.zlib".to_owned(),
            main_file("romeo.txt.zlib").to_vec(),
        ),
        (
            "midsummer.txt.zlib".to_owned(),
            main_file("midsummer.txt.zlib").to_vec(),
        ),
    ];
    zl.extend(corpus_zlib());

    let mut tally = Tally::default();
    for (i, (name, stream)) in raw.iter().enumerate() {
        // Unmutated: the streams themselves.
        tally.compare(name, stream, false);
        let s = stride_for(stream.len());
        for (what, m) in mutants(stream, 1000 + i as u64, s) {
            tally.compare(&format!("{name} {what}"), &m, false);
        }
    }
    for (i, (name, stream)) in zl.iter().enumerate() {
        tally.compare(name, stream, true);
        let s = stride_for(stream.len());
        for (what, m) in mutants(stream, 5000 + i as u64, s) {
            tally.compare(&format!("{name} {what}"), &m, true);
        }
    }
    println!(
        "differential vs miniz_oxide: {} streams, {} agree, {} listed differences, {} unlisted",
        tally.total,
        tally.agree,
        tally.listed.values().sum::<usize>(),
        tally.unlisted.values().map(|v| v.0).sum::<usize>()
    );
    for (k, n) in &tally.listed {
        println!("  listed: {k}: {n}");
    }
    for (k, (n, example)) in &tally.unlisted {
        println!("  UNLISTED: {k}: {n}, first: {example}");
    }
    let listed: usize = tally.listed.values().sum();
    let unlisted: usize = tally.unlisted.values().map(|v| v.0).sum();
    report(
        "miniz_oxide differential, mutated streams",
        tally.agree,
        listed,
        unlisted,
        tally.total,
    );
    assert_eq!(unlisted, 0);
}

// ---------------------------------------------------------------------------
// The streaming decoder against the whole-input one and the spec's model.
// ---------------------------------------------------------------------------

use clazel_deflate::stream::{Format, Inflater, Status, WINDOW_LEN};

/// What a streamed decode gave: the output, then the bytes of input used or
/// the error.
type Streamed = (Vec<u8>, Result<usize, Error>);

/// Decode `input` giving the decoder `chunk` bytes of input at a time and
/// room for `room` bytes of output at a time.
fn drive(format: Format, input: &[u8], limit: u64, chunk: usize, room: usize) -> Streamed {
    let mut d = Inflater::new(format, limit);
    let mut window = vec![0u8; WINDOW_LEN];
    let mut dst = vec![0u8; room.max(1)];
    let mut out = Vec::new();
    let mut used = 0usize;
    // Bytes of `input` offered but not yet taken are offered again.
    loop {
        let end = used.saturating_add(chunk.max(1)).min(input.len());
        let src = input.get(used..end).unwrap_or(&[]);
        let step = d.step(src, &mut dst, &mut window);
        used = used.saturating_add(step.consumed);
        out.extend_from_slice(dst.get(..step.produced).unwrap_or(&[]));
        match step.status {
            Status::Done => return (out, Ok(used)),
            Status::Failed(e) => return (out, Err(e)),
            Status::NeedOutput => {}
            Status::NeedInput => {
                if used >= input.len() {
                    return match d.end_of_input() {
                        Err(e) => (out, Err(e)),
                        Ok(()) => (out, Ok(used)),
                    };
                }
            }
            Status::BadWindow => return (out, Err(Error::Truncated)),
        }
    }
}

fn whole(format: Format, input: &[u8], limit: u64) -> Result<(Vec<u8>, usize), Error> {
    match format {
        Format::Raw => inflate(input, limit),
        Format::Zlib => zlib_decompress(input, limit),
    }
}

fn model_of(format: Format, input: &[u8], limit: usize) -> model::Out {
    match format {
        Format::Raw => model::inflate(input, limit),
        Format::Zlib => model::zlib(input, limit),
    }
}

/// One stream the streaming tests use: its name, format, bytes and the
/// output it must give.
type Stream = (String, Format, Vec<u8>, Vec<u8>);

/// Every valid stream the streaming tests use.
fn streams() -> Vec<Stream> {
    let mut v: Vec<Stream> = Vec::new();
    for name in ["romeo.txt.deflate", "romeo.txt.fixed-huff.deflate"] {
        v.push((
            name.to_owned(),
            Format::Raw,
            main_file(name).to_vec(),
            main_file("romeo.txt").to_vec(),
        ));
    }
    for (name, text) in [
        ("romeo.txt.zlib", "romeo.txt"),
        ("midsummer.txt.zlib", "midsummer.txt"),
        ("pi.txt.zlib", "pi.txt"),
    ] {
        v.push((
            name.to_owned(),
            Format::Zlib,
            main_file(name).to_vec(),
            main_file(text).to_vec(),
        ));
    }
    for name in [
        "backref-crosses-blocks",
        "degenerate-huffman-0-bit",
        "degenerate-huffman-1-bit",
        "distance-32768",
        "huffman-primlen-9",
    ] {
        v.push((
            name.to_owned(),
            Format::Raw,
            artificial_file(&format!("{name}.deflate")).to_vec(),
            artificial_file(&format!("{name}.deflate.decompressed")).to_vec(),
        ));
    }
    for (name, raw, data) in corpus_with_data() {
        v.push((
            format!("miniz {name}"),
            Format::Raw,
            raw.clone(),
            data.clone(),
        ));
        v.push((
            format!("miniz zlib {name}"),
            Format::Zlib,
            zlib_wrap(&raw, &data),
            data,
        ));
    }
    for (name, raw, data) in handmade() {
        v.push((
            format!("made {name}"),
            Format::Raw,
            raw.clone(),
            data.clone(),
        ));
        v.push((
            format!("made zlib {name}"),
            Format::Zlib,
            zlib_wrap(&raw, &data),
            data,
        ));
    }
    v
}

/// Whole-input decoding gives the output the test data says, and uses every
/// byte of the stream.
#[test]
fn whole_decodes_everything() {
    for (name, format, stream, want) in streams() {
        let got = whole(format, &stream, LIMIT);
        assert_eq!(got, Ok((want, stream.len())), "{name}");
    }
}

/// Cutting the input and the output room anywhere gives the whole-input
/// result (`contract::chunked_ensures`).
#[test]
fn chunking_is_irrelevant() {
    let chunks: &[usize] = if cfg!(miri) {
        &[1, 7, 61, 1 << 20]
    } else {
        &[1, 2, 3, 5, 7, 8, 13, 64, 1000, 1 << 20]
    };
    let rooms: &[usize] = if cfg!(miri) {
        &[1, 100]
    } else {
        &[1, 3, 100, 16384]
    };
    for (name, format, stream, _) in streams() {
        if cfg!(miri) && stream.len() > 3000 {
            continue;
        }
        let want = whole(format, &stream, LIMIT);
        for &chunk in chunks {
            // One-byte chunks of the big streams are slow in a debug build.
            if chunk < 3 && stream.len() > 20000 {
                continue;
            }
            for &room in rooms {
                if room < 3 && stream.len() > 20000 {
                    continue;
                }
                let (out, result) = drive(format, &stream, LIMIT, chunk, room);
                match (&want, &result) {
                    (Ok((w, used)), Ok(u)) => {
                        assert!(w == &out && used == u, "{name} chunk {chunk} room {room}");
                    }
                    (Err(e), Err(f)) => assert_eq!(e, f, "{name} chunk {chunk} room {room}"),
                    _ => unreachable!("{name} chunk {chunk} room {room}: {want:?} vs {result:?}"),
                }
            }
        }
    }
}

/// Mutants of the small streams give the same answer chunked as whole.
#[test]
fn chunking_is_irrelevant_on_mutants() {
    let mut rng = Rng::new(4242);
    for (name, format, stream, _) in streams() {
        if stream.len() > 800 {
            continue;
        }
        let count = if cfg!(miri) { 3 } else { 60 };
        for k in 0..count {
            let mut m = stream.clone();
            for _ in 0..1 + rng.below(3) {
                let i = rng.below(m.len());
                if let Some(b) = m.get_mut(i) {
                    *b = rng.next() as u8;
                }
            }
            let want = whole(format, &m, LIMIT);
            for chunk in [1, 3, 17] {
                let (out, result) = drive(format, &m, LIMIT, chunk, 5);
                match (&want, &result) {
                    (Ok((w, used)), Ok(u)) => {
                        assert!(w == &out && used == u, "{name} mutant {k} chunk {chunk}");
                    }
                    (Err(e), Err(f)) => {
                        assert_eq!(e, f, "{name} mutant {k} chunk {chunk}");
                    }
                    _ => unreachable!("{name} mutant {k} chunk {chunk}: {want:?} vs {result:?}"),
                }
            }
        }
    }
}

/// The decoder equals the model of the spec on the streams, on every prefix
/// of the small ones, and on mutants.
#[test]
fn equals_the_spec_model() {
    let mut checked = 0usize;
    let mut rng = Rng::new(99);
    for (name, format, stream, want) in streams() {
        if stream.len() > 40000 || (cfg!(miri) && stream.len() > 700) {
            continue;
        }
        let got = whole(format, &stream, LIMIT);
        let model = model_of(format, &stream, LIMIT as usize);
        assert_eq!(got, model, "{name}");
        assert_eq!(got.as_ref().ok().map(|d| &d.0), Some(&want), "{name}");
        checked += 1;
        if stream.len() > 800 {
            continue;
        }
        let step = if cfg!(miri) {
            7
        } else {
            (stream.len() / 100).max(1)
        };
        for n in (0..stream.len()).step_by(step) {
            let p = stream.get(..n).unwrap_or(&[]);
            assert_eq!(
                whole(format, p, LIMIT),
                model_of(format, p, LIMIT as usize),
                "{name} prefix {n}"
            );
            checked += 1;
        }
        let count = if cfg!(miri) { 4 } else { 40 };
        for k in 0..count {
            let mut m = stream.clone();
            for _ in 0..1 + rng.below(3) {
                let i = rng.below(m.len());
                if let Some(b) = m.get_mut(i) {
                    *b ^= 1 << rng.below(8);
                }
            }
            assert_eq!(
                whole(format, &m, LIMIT),
                model_of(format, &m, LIMIT as usize),
                "{name} mutant {k}"
            );
            checked += 1;
        }
    }
    println!("model: {checked} streams agree");
}

/// With the limit at the output's length it decodes; below it it stops with
/// `OutputLimit`, having produced no more than the limit.
#[test]
fn output_limit_is_exact() {
    for (name, format, stream, want) in streams() {
        if stream.len() > 20000 {
            continue;
        }
        let n = want.len() as u64;
        assert!(whole(format, &stream, n).is_ok(), "{name}");
        if n > 0 {
            for limit in [n - 1, n / 2, 0] {
                assert_eq!(
                    whole(format, &stream, limit).err(),
                    Some(Error::OutputLimit),
                    "{name} limit {limit}"
                );
                let (out, result) = drive(format, &stream, limit, 100, 7);
                assert!(
                    out.len() as u64 <= limit,
                    "{name} limit {limit}: {} bytes",
                    out.len()
                );
                assert_eq!(
                    result.err(),
                    Some(Error::OutputLimit),
                    "{name} limit {limit}"
                );
            }
        }
    }
}

/// A stream that expands without end of any useful size stops at the limit:
/// 64 MiB of zeros compresses to about 64 KiB, and a limit of 1 MiB stops it.
#[test]
fn bomb_stops_at_the_limit() {
    let size: usize = if cfg!(miri) { 1 << 16 } else { 1 << 26 };
    let data = vec![0u8; size];
    let raw = miniz_oxide::deflate::compress_to_vec(&data, 6);
    assert!(raw.len().saturating_mul(100) < size, "{} bytes", raw.len());
    let limit: u64 = if cfg!(miri) { 1 << 12 } else { 1 << 20 };
    assert_eq!(inflate(&raw, limit).err(), Some(Error::OutputLimit));
    let (out, result) = drive(Format::Raw, &raw, limit, 4096, 4096);
    assert_eq!(result.err(), Some(Error::OutputLimit));
    assert!(out.len() as u64 <= limit);
    // With room for all of it, the whole bomb decodes.
    let ok = inflate(&raw, size as u64).map(|d| d.0.len());
    assert_eq!(ok, Ok(size));
}

/// A stream made for one error: its name, format, bytes, and the error.
type ErrorCase = (&'static str, Format, Vec<u8>, Error);

/// Streams for each error, built by hand.
fn error_streams() -> Vec<ErrorCase> {
    let mut v: Vec<ErrorCase> = Vec::new();
    let raw = Format::Raw;
    // §3.2.3: BTYPE 11.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(3, 2);
    v.push((
        "reserved block type",
        raw,
        w.bytes,
        Error::ReservedBlockType,
    ));
    // §3.2.4: NLEN not the complement of LEN.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(0, 2);
    w.raw(&[5, 0, 0, 0]);
    v.push((
        "LEN and NLEN",
        raw,
        w.bytes,
        Error::LengthComplementMismatch,
    ));
    // §3.2.7: HLIT 31 is 288 codes.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(2, 2);
    w.bits(31, 5);
    w.bits(0, 5);
    w.bits(0, 4);
    v.push(("HLIT 288", raw, w.bytes, Error::TooManyLengthCodes));
    // The code length code over-subscribed: four codes of length 1.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(2, 2);
    w.bits(0, 5);
    w.bits(0, 5);
    w.bits(0, 4);
    for _ in 0..4 {
        w.bits(1, 3);
    }
    v.push((
        "code length code over-subscribed",
        raw,
        w.bytes,
        Error::BadCodeLengths,
    ));
    // The code length code incomplete: one code of length 1.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(2, 2);
    w.bits(0, 5);
    w.bits(0, 5);
    w.bits(0, 4);
    for l in [0, 0, 0, 1] {
        w.bits(l, 3);
    }
    v.push((
        "code length code incomplete",
        raw,
        w.bytes,
        Error::BadCodeLengths,
    ));
    // A literal/length code that never mentions symbol 256.
    let mut lit = vec![0u32; 257];
    for s in [97, 98] {
        if let Some(x) = lit.get_mut(s) {
            *x = 1;
        }
    }
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[1, 1]);
    v.push(("no end of block", raw, w.bytes, Error::NoEndOfBlock));
    // A literal/length code that is incomplete: only 256, with length 2.
    let mut lit = vec![0u32; 257];
    if let Some(x) = lit.get_mut(256) {
        *x = 2;
    }
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[1, 1]);
    v.push((
        "literal code incomplete",
        raw,
        w.bytes,
        Error::BadCodeLengths,
    ));
    // A literal/length code over-subscribed: three codes of length 1.
    let mut lit = vec![0u32; 257];
    for s in [97, 98, 256] {
        if let Some(x) = lit.get_mut(s) {
            *x = 1;
        }
    }
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[1, 1]);
    v.push((
        "literal code over-subscribed",
        raw,
        w.bytes,
        Error::BadCodeLengths,
    ));
    // A distance code incomplete in the way §3.2.7 does not allow: one code
    // of length 2.
    let mut lit = vec![0u32; 257];
    for s in [97, 256] {
        if let Some(x) = lit.get_mut(s) {
            *x = 1;
        }
    }
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[2]);
    v.push((
        "distance code incomplete",
        raw,
        w.bytes,
        Error::BadCodeLengths,
    ));
    // 15 bits matching no code: symbol 256 alone with length 1.
    let mut lit = vec![0u32; 257];
    if let Some(x) = lit.get_mut(256) {
        *x = 1;
    }
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[0, 1]);
    for _ in 0..15 {
        w.bits(1, 1);
    }
    v.push(("invalid code", raw, w.bytes, Error::InvalidCode));
    // The same, with 11 bits where the header ends on a byte boundary: Truncated, not InvalidCode.
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[0, 1]);
    for _ in 0..11 {
        w.bits(1, 1);
    }
    v.push(("invalid code cut short", raw, w.bytes, Error::Truncated));
    // §3.2.6: literal/length symbol 286.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(1, 2);
    w.fixed_lit(286);
    v.push(("symbol 286", raw, w.bytes, Error::InvalidSymbol));
    // §3.2.6: distance symbol 30.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(1, 2);
    w.fixed_lit(u32::from(b'a'));
    w.fixed_lit(257);
    w.code(30, 5);
    v.push((
        "distance symbol 30",
        raw,
        w.bytes,
        Error::InvalidDistanceSymbol,
    ));
    // §3.2.3: a distance past the start of the output.
    let mut w = BitWriter::new();
    w.bits(1, 1);
    w.bits(1, 2);
    w.fixed_lit(u32::from(b'a'));
    w.fixed_match(3, 2);
    w.fixed_lit(256);
    v.push(("distance too far", raw, w.bytes, Error::DistanceTooFar));
    // RFC 1950 §2.2 and §2.3.
    v.push((
        "zlib header cut",
        Format::Zlib,
        vec![0x78],
        Error::Truncated,
    ));
    v.push((
        "zlib FCHECK",
        Format::Zlib,
        vec![0x78, 0x9D, 3, 0],
        Error::BadZlibCheck,
    ));
    v.push((
        "zlib CM",
        Format::Zlib,
        vec![0x79, 0x18, 3, 0],
        Error::BadZlibMethod,
    ));
    v.push((
        "zlib CINFO",
        Format::Zlib,
        vec![0x88, 0x1C, 3, 0],
        Error::BadZlibWindow,
    ));
    v.push((
        "zlib FDICT",
        Format::Zlib,
        vec![0x78, 0x20, 3, 0],
        Error::PresetDictionary,
    ));
    // An empty fixed block with the wrong checksum, and a cut one.
    v.push((
        "zlib Adler-32",
        Format::Zlib,
        vec![0x78, 0x9C, 3, 0, 0, 0, 0, 2],
        Error::AdlerMismatch,
    ));
    v.push((
        "zlib trailer cut",
        Format::Zlib,
        vec![0x78, 0x9C, 3, 0, 0, 0, 0],
        Error::Truncated,
    ));
    v.push(("empty input", raw, Vec::new(), Error::Truncated));
    v
}

#[test]
fn every_error() {
    for (name, format, stream, want) in error_streams() {
        assert_eq!(whole(format, &stream, LIMIT).err(), Some(want), "{name}");
        assert_eq!(
            model_of(format, &stream, LIMIT as usize).err(),
            Some(want),
            "{name} (model)"
        );
        for chunk in [1, 2, 1000] {
            let (_, result) = drive(format, &stream, LIMIT, chunk, 16);
            assert_eq!(result.err(), Some(want), "{name} chunk {chunk}");
        }
    }
}

/// A dynamic block with no distance code at all ("the data is all
/// literals", §3.2.7), and bytes after the stream, which are not part of it.
#[test]
fn degenerate_codes_and_trailing_data() {
    let mut lit = vec![0u32; 258];
    for (s, l) in [(97, 1), (98, 2), (256, 2)] {
        if let Some(x) = lit.get_mut(s) {
            *x = l;
        }
    }
    let mut w = BitWriter::new();
    w.dynamic_header(true, &lit, &[0]);
    let codes = canonical(&lit);
    let mut out = Vec::new();
    for s in [97usize, 98, 98, 97] {
        let (c, n) = at(&codes, s, (0, 0));
        w.code(c, n);
        out.push(s as u8);
    }
    let (c, n) = at(&codes, 256, (0, 0));
    w.code(c, n);
    let used = w.bytes.len();
    let mut stream = w.bytes.clone();
    stream.extend_from_slice(&[9, 9, 9]);
    assert_eq!(inflate(&stream, LIMIT), Ok((out.clone(), used)));
    assert_eq!(
        model::inflate(&stream, LIMIT as usize),
        Ok((out.clone(), used))
    );
    // In a zlib stream the trailer follows the block.
    let z = zlib_wrap(&w.bytes, &out);
    assert_eq!(zlib_decompress(&z, LIMIT), Ok((out, z.len())));
    // Adler-32's own example: "Wikipedia" is 0x11E60398.
    assert_eq!(adler32(b"Wikipedia"), 0x11E6_0398);
}

/// A window of the wrong size is refused and nothing happens.
#[test]
fn bad_window() {
    let mut d = Inflater::new(Format::Raw, 10);
    let mut dst = [0u8; 4];
    let mut small = vec![0u8; 100];
    let s = d.step(&[1, 2, 3], &mut dst, &mut small);
    assert_eq!(
        (s.consumed, s.produced, s.status),
        (0, 0, Status::BadWindow)
    );
}

/// The fixed codes of RFC 1951 §3.2.6 are complete, so `Inflater` may ignore
/// the result of building them: Kraft's sum is exactly 1 for both.
#[test]
fn fixed_codes_are_complete() {
    use clazel_deflate::huffman::Table;
    let lens: Vec<u8> = (0..288usize)
        .map(|s| match s {
            0..=143 => 8,
            144..=255 => 9,
            256..=279 => 7,
            _ => 8,
        })
        .collect();
    let mut t = Table::new();
    assert!(t.build(&lens, false));
    assert!(t.build(&[5u8; 32], false));
    // And one fewer symbol is no longer complete.
    assert!(!t.build(&[5u8; 31], false));
}
