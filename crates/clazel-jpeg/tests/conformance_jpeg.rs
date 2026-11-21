//! Conformance of `clazel-jpeg` (phase-6.md item 6.5) against libjpeg-turbo's
//! decoder output.
//!
//! The reference is libjpeg-turbo, driven by `scripts/jpeg-reference.py`
//! (its header says how, and which version: the installed 2.1.5, not the
//! pinned 3.2.1 the plan wanted, see the crate's README) over two kinds of
//! file, both vendored with their reference output and read here through
//! the tables `cargo xtask testdata` generates:
//!
//! - `libjpeg-turbo-testimages`: `testorig.jpg` and `testimgint.jpg` of
//!   libjpeg-turbo's own `testimages/` (decoded by libjpeg-turbo to
//!   `*.ref`), and `testimgari.jpg` (arithmetic coding) and `monkey12.jpg`
//!   (12-bit), which must be refused;
//! - `jpeg-corpus`: 132 files the script encodes (every sampling ratio,
//!   restart intervals, non-interleaved scans, gray, YCbCr, RGB, CMYK and
//!   YCCK, SOF1, 16-bit tables, sizes from 1 by 1 up, EXIF orientations),
//!   each with libjpeg-turbo's output.
//!
//! Suites, each printing a `clazel-conformance:` line
//! (`xtask/src/conformance.rs`); a unit is one file:
//!
//! - **differential**: the file through the `Decoder` interface; a file
//!   passes when **every sample of the RGBA is within [`TOLERANCE`] of the
//!   reference's** (zero: the IDCT and the upsampling are libjpeg-turbo's
//!   integer ones), and the alpha is 255. The reference gives gray, RGB or
//!   CMYK as libjpeg returns them; this test makes RGBA of them (gray to
//!   three channels, Adobe-inverted CMYK as `C * K / 255`) and applies the
//!   EXIF orientation (which libjpeg does not), written separately from the
//!   decoder's code. The difference histogram of every file with a nonzero
//!   difference, and of all files together, is printed.
//! - **refusals**: arithmetic, 12-bit, progressive and the other files the
//!   decoder does not read are refused with `Error::Unsupported`.
//! - **chunking**: each file at chunk sizes 1 to 4096 gives exactly what one
//!   chunk of the whole file gives, the invariant checked on every step and
//!   the bytes past the buffers untouched.
//! - **mutations**: deterministic byte mutations of every file never panic,
//!   the invariant holds after every step, `consumed` obeys the contract
//!   and an error leaves the decoder spent.
//! - **JPEGs by hand**: small streams for DC prediction, restart intervals,
//!   the marker rules and the errors, in this file and in the sources.
//!
//! Under Miri the suites are cut to strides, stated at each (`miri_*`
//! constants). They were first sized assuming Miri runs about 1,600 times
//! slower than a debug build; CI measured about 13,000 times on this crate
//! (the chunking test took 397 s), and the chunking stride was cut to fit.

use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status,
};
use clazel_jpeg::Jpeg;

mod testimages {
    include!("generated/libjpeg_turbo_testimages.rs");
}
mod progressive_table {
    include!("generated/jpeg_progressive.rs");
}
mod corpus_table {
    include!("generated/jpeg_corpus.rs");
}

/// The tolerance, in levels, of every sample against libjpeg-turbo's. The
/// IDCT (`jpeg_idct_islow`), the fancy upsampling and the YCbCr conversion
/// are the same integer arithmetic, so the expected difference is zero.
const TOLERANCE: u8 = 0;

const CANARY: u8 = 0xEE;

// ---------------------------------------------------------------- strides

/// Miri runs only the files whose JPEG is at most this many bytes (93 of the
/// 134: the small sizes of the corpus; the full-size images take minutes).
const MIRI_MAX_FILE: usize = 800;
/// Of those, the differential test takes every 2nd and the chunking test every
/// 8th, the chunking test at chunk size 1 only (natively 1 to 4096). CI took
/// 397 s under Miri for every 4th at sizes 1 and 64; this is about a quarter
/// of that.
const MIRI_DIFF_EVERY: usize = 2;
const MIRI_CHUNK_EVERY: usize = 8;
const MIRI_CHUNKS: &[usize] = &[1];
/// Mutants per file (natively 10, under Miri 6) and files (natively all, under
/// Miri 5 spread over the list).
const MIRI_MUTANTS: usize = 6;
const MIRI_MUTATION_FILES: usize = 5;

fn miri() -> bool {
    cfg!(miri)
}

// ----------------------------------------------------------------- decode

/// What the decoder gave for a file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Decoded {
    width: u32,
    height: u32,
    pixels: Vec<u8>,
    /// Bytes of the file the frame used.
    used: usize,
}

/// Decodes `bytes` through the shared interface, in chunks of `chunk`
/// bytes, checking the invariant and the contract on every step.
fn decode(bytes: &[u8], chunk: usize) -> Result<Decoded, Error> {
    let config = match Jpeg::decode_config(bytes)? {
        ConfigStatus::Ready(c) => c,
        ConfigStatus::NeedMore => return Err(Error::Truncated),
    };
    let plen = config.rgba_len()?;
    let wlen = Jpeg::work_len(&config)?;
    let mut pixels = vec![CANARY; plen.saturating_add(3)];
    let mut work = vec![CANARY; wlen.saturating_add(3)];
    let mut state = Jpeg::start(&config)?;
    let mut result = Err(Error::Truncated);
    {
        let mut buffers = Buffers::new(&config, wlen, &mut pixels, &mut work)?;
        assert!(state.inv(&buffers));
        let mut pos = 0usize;
        while pos < bytes.len() {
            let take = chunk.min(bytes.len().saturating_sub(pos));
            let part = bytes
                .get(pos..pos.saturating_add(take))
                .ok_or(Error::Truncated)?;
            let step = state.step(part, &mut buffers);
            assert!(state.inv(&buffers), "invariant lost at byte {pos}");
            match step {
                Ok(step) => {
                    assert!(step.consumed <= part.len());
                    match step.status {
                        Status::NeedMore => {
                            assert_eq!(step.consumed, part.len());
                            pos = pos.saturating_add(take);
                        }
                        Status::FrameDone => {
                            result = Ok(pos.saturating_add(step.consumed));
                            break;
                        }
                    }
                }
                Err(e) => {
                    // An errored decoder is spent, and says so.
                    assert_eq!(state.step(&[0], &mut buffers), Err(Error::Spent));
                    assert!(state.inv(&buffers));
                    result = Err(e);
                    break;
                }
            }
        }
        if let Ok(used) = result {
            // After the frame: nothing more.
            assert_eq!(state.step(&[0], &mut buffers), Err(Error::NoMoreFrames));
            assert!(state.inv(&buffers));
            let _ = used;
        }
    }
    assert!(
        pixels
            .get(plen..)
            .is_some_and(|t| t.iter().all(|&b| b == CANARY))
    );
    assert!(
        work.get(wlen..)
            .is_some_and(|t| t.iter().all(|&b| b == CANARY))
    );
    pixels.truncate(plen);
    Ok(Decoded {
        width: config.width(),
        height: config.height(),
        pixels,
        used: result?,
    })
}

// -------------------------------------------------------------- reference

/// A libjpeg-turbo output (`scripts/jpeg-reference.py`'s `.ref` format).
struct Refd {
    width: usize,
    height: usize,
    channels: usize,
    samples: Vec<u8>,
}

fn le32(b: &[u8], at: usize) -> Option<usize> {
    let a: [u8; 4] = b.get(at..at.checked_add(4)?)?.try_into().ok()?;
    usize::try_from(u32::from_le_bytes(a)).ok()
}

fn parse_ref(b: &[u8]) -> Option<Refd> {
    let (width, height) = (le32(b, 0)?, le32(b, 4)?);
    let channels = usize::from(*b.get(8)?);
    let samples = b.get(9..)?.to_vec();
    (samples.len() == width.checked_mul(height)?.checked_mul(channels)?
        && matches!(channels, 1 | 3 | 4))
    .then_some(Refd {
        width,
        height,
        channels,
        samples,
    })
}

/// `R = C * K / 255`, rounded (the decoder's listed choice, written here
/// again).
fn cmyk_rgb(c: u8, m: u8, y: u8, k: u8) -> [u8; 3] {
    let f = |a: u8| {
        let p = u32::from(a).saturating_mul(u32::from(k));
        u8::try_from(p.saturating_add(127).checked_div(255).unwrap_or(0)).unwrap_or(255)
    };
    [f(c), f(m), f(y)]
}

/// The reference as RGBA, with EXIF orientation `o` applied by the
/// destination-to-source formulas (the decoder maps source to destination).
fn expected_rgba(r: &Refd, o: u8) -> (usize, usize, Vec<u8>) {
    let (w, h) = (r.width, r.height);
    let src = |x: usize, y: usize| -> [u8; 4] {
        let at = y
            .saturating_mul(w)
            .saturating_add(x)
            .saturating_mul(r.channels);
        let s = |i: usize| r.samples.get(at.saturating_add(i)).copied().unwrap_or(0);
        match r.channels {
            1 => [s(0), s(0), s(0), 255],
            3 => [s(0), s(1), s(2), 255],
            _ => {
                let [a, b, c] = cmyk_rgb(s(0), s(1), s(2), s(3));
                [a, b, c, 255]
            }
        }
    };
    let (dw, dh) = if (5..=8).contains(&o) { (h, w) } else { (w, h) };
    let mut out = Vec::with_capacity(dw.saturating_mul(dh).saturating_mul(4));
    for dy in 0..dh {
        for dx in 0..dw {
            let (rx, ry) = (
                w.saturating_sub(1).saturating_sub(dx),
                h.saturating_sub(1).saturating_sub(dy),
            );
            let (sx, sy) = match o {
                2 => (rx, dy),
                3 => (rx, ry),
                4 => (dx, ry),
                5 => (dy, dx),
                // Rotated 90 degrees clockwise: destination (dx, dy) came
                // from source column dy, row h - 1 - dx.
                6 => (dy, h.saturating_sub(1).saturating_sub(dx)),
                7 => (
                    w.saturating_sub(1).saturating_sub(dy),
                    h.saturating_sub(1).saturating_sub(dx),
                ),
                8 => (w.saturating_sub(1).saturating_sub(dy), dx),
                _ => (dx, dy),
            };
            out.extend(src(sx, sy));
        }
    }
    (dw, dh, out)
}

/// Bucket of a difference: 0, 1, 2, 3 to 4, 5 to 8, 9 or more.
fn bucket(d: u8) -> usize {
    match d {
        0 => 0,
        1 => 1,
        2 => 2,
        3..=4 => 3,
        5..=8 => 4,
        _ => 5,
    }
}

const BUCKETS: [&str; 6] = ["0", "1", "2", "3-4", "5-8", "9+"];

/// The histogram of `|got - want|` over every sample, and the largest.
fn histogram(got: &[u8], want: &[u8]) -> ([u64; 6], u8) {
    let mut h = [0u64; 6];
    let mut max = 0u8;
    for (a, b) in got.iter().zip(want) {
        let d = a.abs_diff(*b);
        max = max.max(d);
        if let Some(slot) = h.get_mut(bucket(d)) {
            *slot = slot.saturating_add(1);
        }
    }
    (h, max)
}

fn show(h: &[u64; 6]) -> String {
    BUCKETS
        .iter()
        .zip(h)
        .map(|(b, n)| format!("{b}: {n}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The orientation a corpus file's name asks for (`...-orient-N`).
fn orientation_of(name: &str) -> u8 {
    name.rsplit_once("-orient-")
        .and_then(|(_, n)| n.parse().ok())
        .unwrap_or(1)
}

// ----------------------------------------------------------------- corpus

/// One record of `corpus.pack`: name, JPEG, reference (empty: none).
struct Entry<'a> {
    name: &'a str,
    jpeg: &'a [u8],
    reference: &'a [u8],
}

fn corpus() -> Vec<Entry<'static>> {
    entries_of(corpus_table::FILES.first().map_or(&[][..], |c| c.bytes))
}

/// The records of a pack (`corpus.pack` or `progressive.pack`).
fn entries_of(pack: &'static [u8]) -> Vec<Entry<'static>> {
    let mut out = Vec::new();
    let mut at = 0usize;
    while at < pack.len() {
        let name_len = usize::from(pack.get(at).copied().unwrap_or(0));
        let name_at = at.saturating_add(1);
        let name = pack
            .get(name_at..name_at.saturating_add(name_len))
            .and_then(|n| std::str::from_utf8(n).ok())
            .unwrap_or("?");
        let jl_at = name_at.saturating_add(name_len);
        let jl = le32(pack, jl_at).unwrap_or(0);
        let j_at = jl_at.saturating_add(4);
        let jpeg = pack.get(j_at..j_at.saturating_add(jl)).unwrap_or(&[]);
        let rl_at = j_at.saturating_add(jl);
        let rl = le32(pack, rl_at).unwrap_or(0);
        let r_at = rl_at.saturating_add(4);
        let reference = pack.get(r_at..r_at.saturating_add(rl)).unwrap_or(&[]);
        out.push(Entry {
            name,
            jpeg,
            reference,
        });
        at = r_at.saturating_add(rl);
    }
    out
}

fn testimage(name: &str) -> &'static [u8] {
    testimages::FILES
        .iter()
        .find(|c| c.file == name)
        .map_or(&[][..], |c| c.bytes)
}

/// Every file with its reference: the two testimages and the corpus.
fn all_decodable() -> Vec<(String, &'static [u8], Vec<u8>)> {
    let mut v = vec![
        (
            "testorig.jpg".to_owned(),
            testimage("testorig.jpg"),
            testimage("testorig.ref").to_vec(),
        ),
        (
            "testimgint.jpg".to_owned(),
            testimage("testimgint.jpg"),
            testimage("testimgint.ref").to_vec(),
        ),
    ];
    for e in corpus() {
        v.push((e.name.to_owned(), e.jpeg, e.reference.to_vec()));
    }
    v
}

/// Compares the decoder's output for `jpeg` with `reference`: `Ok` with the
/// histogram, or a description of the failure.
fn compare(name: &str, jpeg: &[u8], reference: &[u8]) -> Result<[u64; 6], String> {
    let got = decode(jpeg, jpeg.len().max(1)).map_err(|e| format!("{name}: {e:?}"))?;
    let r = parse_ref(reference).ok_or_else(|| format!("{name}: bad reference"))?;
    let (w, h, want) = expected_rgba(&r, orientation_of(name));
    if (usize::try_from(got.width), usize::try_from(got.height)) != (Ok(w), Ok(h)) {
        return Err(format!(
            "{name}: size {}x{}, reference {w}x{h}",
            got.width, got.height
        ));
    }
    let (hist, max) = histogram(&got.pixels, &want);
    if max > TOLERANCE {
        return Err(format!(
            "{name}: largest difference {max} over {TOLERANCE}: {}",
            show(&hist)
        ));
    }
    Ok(hist)
}

fn print_suite(name: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{name}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
}

/// The decodable files against libjpeg-turbo. Under Miri: the files of at
/// most [`MIRI_MAX_FILE`] bytes (the small sizes of the corpus).
#[test]
fn differential_vs_libjpeg_turbo() {
    let files = all_decodable();
    let mut total_hist = [0u64; 6];
    let (mut pass, mut fail, mut run) = (0usize, 0usize, 0usize);
    let mut notes = Vec::new();
    let mut seen = 0usize;
    for (name, jpeg, reference) in &files {
        if miri() {
            if jpeg.len() > MIRI_MAX_FILE {
                continue;
            }
            seen = seen.saturating_add(1);
            if !seen.is_multiple_of(MIRI_DIFF_EVERY) {
                continue;
            }
        }
        run = run.saturating_add(1);
        match compare(name, jpeg, reference) {
            Ok(hist) => {
                for (t, n) in total_hist.iter_mut().zip(hist) {
                    *t = t.saturating_add(n);
                }
                if hist.iter().skip(1).any(|&n| n > 0) {
                    println!("  {name}: within tolerance, histogram {}", show(&hist));
                }
                pass = pass.saturating_add(1);
            }
            Err(e) => {
                fail = fail.saturating_add(1);
                notes.push(e);
            }
        }
    }
    println!(
        "  difference histogram of every sample compared: {}",
        show(&total_hist)
    );
    print_suite(
        "JPEG vs libjpeg-turbo: testimages and corpus, within tolerance",
        pass,
        0,
        fail,
        run,
    );
    assert!(notes.is_empty(), "{}", notes.join("\n"));
    assert!(miri() || run == files.len());
}

/// The files the decoder must refuse, and why.
#[test]
fn refusals() {
    let ari = decode(testimage("testimgari.jpg"), 4096);
    assert!(
        matches!(ari, Err(Error::Unsupported(m)) if m.contains("arithmetic")),
        "{ari:?}"
    );
    let twelve = decode(testimage("monkey12.jpg"), 4096);
    assert!(
        matches!(twelve, Err(Error::Unsupported(m)) if m.contains("precision")),
        "{twelve:?}"
    );
    print_suite("JPEG refusals: arithmetic and 12-bit", 2, 0, 0, 2);
}

/// Each file at several chunk sizes equals the whole-file decode.
#[test]
fn chunking() {
    let files = all_decodable();
    let chunks: &[usize] = if miri() {
        MIRI_CHUNKS
    } else {
        &[1, 2, 3, 7, 64, 4096]
    };
    let (mut pass, mut fail, mut run) = (0usize, 0usize, 0usize);
    let mut seen = 0usize;
    for (name, jpeg, _) in &files {
        if miri() {
            if jpeg.len() > MIRI_MAX_FILE {
                continue;
            }
            seen = seen.saturating_add(1);
            if !seen.is_multiple_of(MIRI_CHUNK_EVERY) {
                continue;
            }
        }
        run = run.saturating_add(1);
        let whole = decode(jpeg, jpeg.len().max(1));
        let same = chunks.iter().all(|&c| {
            let got = decode(jpeg, c);
            let ok = got == whole;
            if !ok {
                println!("  {name}: chunk size {c} differs");
            }
            ok
        });
        if same && whole.is_ok() {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
        }
    }
    print_suite(
        "JPEG chunking: every file at chunk sizes 1 to 4096",
        pass,
        0,
        fail,
        run,
    );
    assert_eq!(fail, 0);
}

// -------------------------------------------------------------- mutations

/// A deterministic generator (xorshift64*).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n.max(1)).unwrap_or(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
}

/// A mutant of `bytes`: bytes changed, a truncation, a run deleted, a run
/// repeated, or a run overwritten.
fn mutate(bytes: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = bytes.to_vec();
    match rng.below(6) {
        0 | 1 => {
            for _ in 0..=rng.below(3) {
                let at = rng.below(v.len());
                if let Some(b) = v.get_mut(at) {
                    *b = u8::try_from(rng.below(256)).unwrap_or(0);
                }
            }
        }
        2 => v.truncate(rng.below(v.len())),
        3 => {
            let at = rng.below(v.len());
            let n = rng.below(16);
            v.drain(at..at.saturating_add(n).min(v.len()));
        }
        4 => {
            let at = rng.below(v.len());
            let n = rng.below(16).min(v.len().saturating_sub(at));
            let run: Vec<u8> = v.get(at..at.saturating_add(n)).unwrap_or(&[]).to_vec();
            for (i, b) in run.into_iter().enumerate() {
                v.insert(at.saturating_add(i), b);
            }
        }
        _ => {
            let at = rng.below(v.len());
            for i in 0..rng.below(16) {
                if let Some(b) = v.get_mut(at.saturating_add(i)) {
                    *b = 0xFF;
                }
            }
        }
    }
    v
}

/// Decodes a mutant: whatever the bytes, no panic, the invariant kept and
/// the contract obeyed (`decode` asserts them).
fn survive(bytes: &[u8], chunk: usize) -> Result<usize, Error> {
    // `decode` runs `decode_config` first, which may refuse: also fine.
    decode(bytes, chunk).map(|d| d.used)
}

#[test]
fn mutations_never_panic() {
    let files = all_decodable();
    let per_file = if miri() { MIRI_MUTANTS } else { 10 };
    let stride = if miri() {
        files.len().div_ceil(MIRI_MUTATION_FILES).max(1)
    } else {
        1
    };
    let (mut mutants, mut errors, mut frames, mut units) = (0usize, 0usize, 0usize, 0usize);
    for (n, (name, jpeg, _)) in files.iter().enumerate() {
        if n % stride != 0 || (miri() && jpeg.len() > 4096) {
            continue;
        }
        units = units.saturating_add(1);
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ (u64::try_from(n).unwrap_or(0) << 32) ^ 1);
        for _ in 0..per_file {
            let m = mutate(jpeg, &mut rng);
            for chunk in [m.len().max(1), 5] {
                mutants = mutants.saturating_add(1);
                match survive(&m, chunk) {
                    Ok(_) => frames = frames.saturating_add(1),
                    Err(_) => errors = errors.saturating_add(1),
                }
            }
        }
        let _ = name;
    }
    println!("  {mutants} mutants, {errors} ended in an error, {frames} frames completed");
    print_suite(
        "JPEG mutations: no panic, the invariant kept",
        units,
        0,
        0,
        units,
    );
}

// --------------------------------------------------------------- by hand

/// Bits to bytes, padded with ones, with `0xFF` stuffed (T.81 B.1.1.5).
fn pack(bits: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    for chunk in bits.chunks(8) {
        let mut v = 0u32;
        for i in 0..8 {
            v = v
                .saturating_mul(2)
                .saturating_add(u32::from(chunk.get(i).copied().unwrap_or(1)));
        }
        let b = u8::try_from(v).unwrap_or(0);
        out.push(b);
        if b == 0xFF {
            out.push(0);
        }
    }
    out
}

fn seg(marker: u8, body: &[u8]) -> Vec<u8> {
    let len = u16::try_from(body.len().saturating_add(2)).unwrap_or(0);
    let mut v = vec![0xFF, marker];
    v.extend(len.to_be_bytes());
    v.extend(body);
    v
}

/// DQT of table 0 with `q` for every coefficient.
fn dqt(q: u8) -> Vec<u8> {
    let mut b = vec![0u8];
    b.extend([q; 64]);
    seg(0xDB, &b)
}

fn dht(class_id: u8, counts: &[(usize, u8)], symbols: &[u8]) -> Vec<u8> {
    let mut c = [0u8; 16];
    for &(len, n) in counts {
        if let Some(s) = c.get_mut(len.saturating_sub(1)) {
            *s = n;
        }
    }
    let mut b = vec![class_id];
    b.extend(c);
    b.extend(symbols);
    seg(0xC4, &b)
}

/// The DC table of these tests: `0` is category 0 (no bits), `1` is
/// category 4 (4 bits, EXTEND'ed: 0 to 7 are -15 to -8, 8 to 15 are 8 to 15).
fn dc_table() -> Vec<u8> {
    dht(0x00, &[(1, 2)], &[0, 4])
}

/// The AC table: `0` is EOB.
fn ac_table() -> Vec<u8> {
    dht(0x10, &[(1, 1)], &[0x00])
}

fn sof0(w: u16, h: u16, comps: &[(u8, u8, u8)]) -> Vec<u8> {
    let mut b = vec![8];
    b.extend(h.to_be_bytes());
    b.extend(w.to_be_bytes());
    b.push(u8::try_from(comps.len()).unwrap_or(0));
    for &(id, hv, tq) in comps {
        b.extend([id, hv, tq]);
    }
    seg(0xC0, &b)
}

fn sos(comps: &[(u8, u8)]) -> Vec<u8> {
    let mut b = vec![u8::try_from(comps.len()).unwrap_or(0)];
    for &(id, tdta) in comps {
        b.extend([id, tdta]);
    }
    b.extend([0, 63, 0]);
    seg(0xDA, &b)
}

/// The bits of a DC difference `d` (-15 to 15, not 0 to 7 as category 4
/// would give: |d| 8 to 15 only) or 0, then an EOB.
fn block_bits(d: i32) -> Vec<u8> {
    let mut bits = Vec::new();
    if d == 0 {
        bits.push(0);
    } else {
        bits.push(1);
        let v = if d > 0 { d } else { d.saturating_add(15) };
        for i in (0..4).rev() {
            bits.push(u8::from((v >> i) & 1 == 1));
        }
    }
    // The AC code for EOB.
    bits.push(0);
    bits
}

/// A gray image of `blocks` 8 by 8 blocks in a row, one scan, DC
/// differences `diffs`, quantizer 8 (a DC step of 1 is 1 level), with a
/// restart interval and the markers in between if `restart` is nonzero.
fn gray_row(blocks: u16, diffs: &[i32], restart: u16) -> Vec<u8> {
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof0(blocks.saturating_mul(8), 8, &[(1, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(ac_table());
    if restart != 0 {
        v.extend(seg(0xDD, &restart.to_be_bytes()));
    }
    v.extend(sos(&[(1, 0x00)]));
    let mut rst = 0u8;
    let mut bits = Vec::new();
    for (i, &d) in diffs.iter().enumerate() {
        if restart != 0 && i > 0 && i.is_multiple_of(usize::from(restart)) {
            v.extend(pack(&bits));
            bits.clear();
            v.extend([0xFF, 0xD0u8.saturating_add(rst)]);
            rst = rst.saturating_add(1) & 7;
        }
        bits.extend(block_bits(d));
    }
    v.extend(pack(&bits));
    v.extend([0xFF, 0xD9]);
    v
}

/// The gray level of column `x` of the first row of a decoded image.
fn level(d: &Decoded, x: usize) -> Option<u8> {
    d.pixels.get(x.checked_mul(4)?).copied()
}

/// The config of `bytes`, [`Error::Truncated`] if more is needed.
fn ready(bytes: &[u8]) -> Result<Config, Error> {
    match Jpeg::decode_config(bytes)? {
        ConfigStatus::Ready(c) => Ok(c),
        ConfigStatus::NeedMore => Err(Error::Truncated),
    }
}

fn expect_err(bytes: &[u8]) -> Error {
    decode(bytes, bytes.len().max(1))
        .err()
        .unwrap_or(Error::Truncated)
}

#[test]
fn dc_prediction_and_levels() -> Result<(), Error> {
    // Blocks of a DC step of 8 per unit: level = 128 + dc, so differences
    // +10, -3 (as -3 + 15 = 12 in 4 bits: use +12, -10 here instead; the
    // table only codes |d| 8 to 15).
    let img = gray_row(3, &[12, -10, 15], 0);
    let d = decode(&img, img.len())?;
    assert_eq!((d.width, d.height), (24, 8));
    // DC = 12, 2, 17; each dequantized by 8 and divided by 8 by the IDCT.
    assert_eq!(level(&d, 0), Some(140));
    assert_eq!(level(&d, 7), Some(140));
    assert_eq!(level(&d, 8), Some(130));
    assert_eq!(level(&d, 16), Some(145));
    // Every pixel is opaque gray.
    assert!(
        d.pixels
            .as_chunks::<4>()
            .0
            .iter()
            .all(|p| p.first() == p.get(1) && p.get(1) == p.get(2) && p.get(3) == Some(&255))
    );
    Ok(())
}

#[test]
fn restart_markers_reset_the_predictor() -> Result<(), Error> {
    let with = gray_row(3, &[12, 12, 12], 1);
    let d = decode(&with, with.len())?;
    assert_eq!(
        [level(&d, 0), level(&d, 8), level(&d, 16)],
        [Some(140), Some(140), Some(140)]
    );
    // Interval 2: the third block restarts.
    let two = gray_row(3, &[12, 12, 12], 2);
    let d = decode(&two, two.len())?;
    assert_eq!(
        [level(&d, 0), level(&d, 8), level(&d, 16)],
        [Some(140), Some(152), Some(140)]
    );
    // No restart interval: the predictor accumulates.
    let none = gray_row(3, &[12, 12, 12], 0);
    let d = decode(&none, none.len())?;
    assert_eq!(
        [level(&d, 0), level(&d, 8), level(&d, 16)],
        [Some(140), Some(152), Some(164)]
    );
    Ok(())
}

#[test]
fn restart_markers_must_come_in_order() {
    let mut img = gray_row(3, &[12, 12, 12], 1);
    // Make the first RST0 an RST1.
    let at = img.windows(2).position(|w| w == [0xFF, 0xD0]);
    if let Some(i) = at
        && let Some(b) = img.get_mut(i.saturating_add(1))
    {
        *b = 0xD1;
    }
    assert!(matches!(expect_err(&img), Error::Malformed(m) if m.contains("order")));
    // A restart marker where the interval is not over.
    let mut img = gray_row(3, &[12, 12, 12], 2);
    let at = img.windows(2).position(|w| w == [0xFF, 0xD0]);
    assert!(at.is_some());
    // Cut the first interval short: a marker inside the data.
    let img2 = gray_row(3, &[12, 12, 12], 1);
    let mut cut = img2.clone();
    let pos = cut.windows(2).position(|w| w == [0xFF, 0xD0]).unwrap_or(0);
    cut.splice(pos..pos, [0xFF, 0xD9]);
    assert!(
        matches!(expect_err(&cut), Error::Malformed(_)),
        "{:?}",
        expect_err(&cut)
    );
    img.truncate(img.len().saturating_sub(2));
    assert_eq!(decode(&img, img.len()).err(), Some(Error::Truncated));
}

#[test]
fn trailing_bytes_are_not_consumed() -> Result<(), Error> {
    let mut img = gray_row(1, &[12], 0);
    let n = img.len();
    img.extend([1, 2, 3]);
    let d = decode(&img, img.len())?;
    assert_eq!(d.used, n);
    Ok(())
}

#[test]
fn refusals_by_marker() {
    let base = |marker: u8| {
        let mut v = vec![0xFF, 0xD8];
        v.extend(seg(marker, &[8, 0, 8, 0, 8, 1, 1, 0x11, 0]));
        v
    };
    for (m, word) in [
        (0xC3, "lossless"),
        (0xC5, "hierarchical"),
        (0xC9, "arithmetic"),
        (0xCA, "arithmetic"),
    ] {
        let e = expect_err(&base(m));
        assert!(
            matches!(e, Error::Unsupported(w) if w.contains(word)),
            "marker {m:#x}: {e:?}"
        );
    }
    // Precision 12, and 2 components: unsupported, not malformed.
    let mut v = vec![0xFF, 0xD8];
    v.extend(seg(0xC1, &[12, 0, 8, 0, 8, 1, 1, 0x11, 0]));
    assert!(matches!(expect_err(&v), Error::Unsupported(_)));
    let mut v = vec![0xFF, 0xD8];
    v.extend(seg(0xC0, &[8, 0, 8, 0, 8, 2, 1, 0x11, 0, 2, 0x11, 0]));
    assert!(matches!(expect_err(&v), Error::Unsupported(_)));
}

#[test]
fn malformed_streams() {
    // Not a JPEG.
    assert!(matches!(expect_err(b"GIF89a"), Error::Malformed(_)));
    assert!(matches!(expect_err(&[0xFF]), Error::Truncated));
    // EOI, SOS and a second SOI before a frame.
    assert!(matches!(
        expect_err(&[0xFF, 0xD8, 0xFF, 0xD9]),
        Error::Malformed(_)
    ));
    assert!(matches!(
        expect_err(&[0xFF, 0xD8, 0xFF, 0xDA, 0, 3, 0]),
        Error::Malformed(_)
    ));
    assert!(matches!(
        expect_err(&[0xFF, 0xD8, 0xFF, 0xD8]),
        Error::Malformed(_)
    ));
    // Garbage between segments, a segment length under 2.
    assert!(matches!(
        expect_err(&[0xFF, 0xD8, 0x00, 0xFF]),
        Error::Malformed(_)
    ));
    assert!(matches!(
        expect_err(&[0xFF, 0xD8, 0xFF, 0xFE, 0, 1]),
        Error::Malformed(_)
    ));
    // Zero size.
    let mut v = vec![0xFF, 0xD8];
    v.extend(seg(0xC0, &[8, 0, 0, 0, 8, 1, 1, 0x11, 0]));
    assert!(matches!(expect_err(&v), Error::Malformed(_)));
    // A scan without its tables, and with a quantization table undefined.
    let base = |dq: bool, dc: bool, ac: bool| {
        let mut v = vec![0xFF, 0xD8];
        if dq {
            v.extend(dqt(1));
        }
        v.extend(sof0(8, 8, &[(1, 0x11, 0)]));
        if dc {
            v.extend(dc_table());
        }
        if ac {
            v.extend(ac_table());
        }
        v.extend(sos(&[(1, 0)]));
        v.extend(pack(&[0, 0]));
        v.extend([0xFF, 0xD9]);
        v
    };
    assert!(decode(&base(true, true, true), 4096).is_ok());
    for (dq, dc, ac) in [
        (false, true, true),
        (true, false, true),
        (true, true, false),
    ] {
        assert!(
            matches!(expect_err(&base(dq, dc, ac)), Error::Malformed(m) if m.contains("not defined")),
            "{dq} {dc} {ac}"
        );
    }
    // A scan naming a component the frame lacks; two frames; fractional
    // sampling (3 does not divide 4).
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(1));
    v.extend(sof0(8, 8, &[(1, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(ac_table());
    v.extend(sos(&[(9, 0)]));
    assert!(matches!(expect_err(&v), Error::Malformed(_)));
    let mut v = vec![0xFF, 0xD8];
    v.extend(sof0(8, 8, &[(1, 0x11, 0)]));
    v.extend(sof0(8, 8, &[(1, 0x11, 0)]));
    assert!(matches!(expect_err(&v), Error::Malformed(_)));
    let mut v = vec![0xFF, 0xD8];
    v.extend(sof0(16, 16, &[(1, 0x41, 0), (2, 0x31, 0), (3, 0x11, 0)]));
    assert!(matches!(expect_err(&v), Error::Unsupported(_)));
    // The same component id twice.
    let mut v = vec![0xFF, 0xD8];
    v.extend(sof0(8, 8, &[(1, 0x11, 0), (1, 0x11, 0), (3, 0x11, 0)]));
    assert!(matches!(expect_err(&v), Error::Malformed(_)));
    // More than 10 blocks in an MCU.
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(1));
    v.extend(sof0(32, 32, &[(1, 0x44, 0), (2, 0x11, 0), (3, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(ac_table());
    v.extend(sos(&[(1, 0), (2, 0), (3, 0)]));
    assert!(matches!(expect_err(&v), Error::Malformed(m) if m.contains("10 blocks")));
}

/// A marker (not the expected restart) before the last MCU is an error.
#[test]
fn a_marker_inside_the_data_is_an_error() {
    let mut img = gray_row(2, &[12, 12], 0);
    // Insert EOI after the first byte of data.
    let sos_end = img
        .windows(2)
        .position(|w| w == [0xFF, 0xDA])
        .map_or(0, |p| p.saturating_add(2));
    let len = img
        .get(sos_end..sos_end.saturating_add(2))
        .and_then(|b| Some(usize::from(u16::from_be_bytes([*b.first()?, *b.get(1)?]))))
        .unwrap_or(0);
    let data = sos_end.saturating_add(len);
    img.splice(data..data, [0xFF, 0xD9]);
    assert!(matches!(expect_err(&img), Error::Malformed(m) if m.contains("inside")));
}

#[test]
fn config_of_every_prefix() -> Result<(), Error> {
    let img = testimage("testorig.jpg");
    let want = ready(img)?;
    assert_eq!(
        (want.format(), want.width(), want.height(), want.frames()),
        (Format::Jpeg, 227, 149, FrameCount::Known(1))
    );
    let mut ready_at = None;
    for n in 0..img.len().min(700) {
        let p = img.get(..n).unwrap_or(&[]);
        match Jpeg::decode_config(p) {
            Ok(ConfigStatus::NeedMore) => assert!(ready_at.is_none(), "{n}"),
            Ok(ConfigStatus::Ready(c)) => {
                assert_eq!(c, want);
                ready_at.get_or_insert(n);
            }
            Err(e) => return Err(e),
        }
    }
    assert!(ready_at.is_some());
    // Over a limit: the size of the frame header is the config's.
    let mut v = vec![0xFF, 0xD8];
    v.extend(seg(0xC0, &[8, 0xFF, 0xFF, 0xFF, 0xFF, 1, 1, 0x11, 0]));
    assert!(matches!(Jpeg::decode_config(&v), Err(Error::Size(_))));
    Ok(())
}

/// With an EXIF orientation of 5 to 8 the config is the turned size, and
/// the config and the step function agree on which APP1 counts.
#[test]
fn orientation_in_the_config() -> Result<(), Error> {
    let mut base = vec![0xFF, 0xD8];
    base.extend(dqt(8));
    let frame = sof0(16, 8, &[(1, 0x11, 0)]);
    let exif = |o: u16| -> Vec<u8> {
        let mut b = b"Exif\0\0II".to_vec();
        b.extend([42, 0, 8, 0, 0, 0, 1, 0]);
        b.extend([0x12, 0x01, 3, 0, 1, 0, 0, 0]);
        b.extend(o.to_le_bytes());
        b.extend([0, 0, 0, 0, 0, 0]);
        seg(0xE1, &b)
    };
    for (o, dims) in [
        (1u16, (16, 8)),
        (3, (16, 8)),
        (5, (8, 16)),
        (6, (8, 16)),
        (8, (8, 16)),
        (9, (16, 8)),
    ] {
        let mut v = base.clone();
        v.extend(exif(o));
        v.extend(&frame);
        let c = ready(&v)?;
        assert_eq!((c.width(), c.height()), dims, "o = {o}");
    }
    // After the frame header it is ignored.
    let mut v = base.clone();
    v.extend(&frame);
    v.extend(exif(6));
    assert!(matches!(
        Jpeg::decode_config(&v),
        Ok(ConfigStatus::Ready(c)) if (c.width(), c.height()) == (16, 8)
    ));
    // Only the first valid one counts.
    let mut v = base;
    v.extend(exif(6));
    v.extend(exif(1));
    v.extend(&frame);
    assert!(matches!(
        Jpeg::decode_config(&v),
        Ok(ConfigStatus::Ready(c)) if (c.width(), c.height()) == (8, 16)
    ));
    Ok(())
}

/// The decoder refuses a config of another format, and steps with the wrong
/// buffers poison it.
#[test]
fn interface_edges() -> Result<(), Error> {
    let config = Config::new(Format::Png, 8, 8, FrameCount::Known(1))?;
    assert!(matches!(Jpeg::start(&config), Err(Error::Unsupported(_))));
    let config = Config::new(Format::Jpeg, 8, 8, FrameCount::Known(1))?;
    let wlen = Jpeg::work_len(&config)?;
    assert_eq!(wlen, 6 * 39 * 43);
    let mut s = Jpeg::start(&config)?;
    let (mut p, mut w) = (vec![0u8; 256], vec![0u8; 10]);
    let mut b = Buffers {
        pixels: &mut p,
        work: &mut w,
    };
    assert!(!s.inv(&b));
    assert_eq!(s.step(&[0xFF], &mut b), Err(Error::Buffers));
    assert_eq!(s.step(&[0xFF], &mut b), Err(Error::Spent));
    Ok(())
}

/// The tables are what `SOURCE.md` lists (the generator checked the hashes),
/// and the pack holds the 132 files the script says it made.
#[test]
fn vendored_tables() {
    let named = testimages::FILES
        .iter()
        .map(|c| (c.file, c.sha256))
        .chain(corpus_table::FILES.iter().map(|c| (c.file, c.sha256)))
        .chain(progressive_table::FILES.iter().map(|c| (c.file, c.sha256)));
    let mut n = 0usize;
    for (file, sha) in named {
        assert!(!file.is_empty());
        assert!(sha.len() == 64 && sha.bytes().all(|b| b.is_ascii_hexdigit()));
        n = n.saturating_add(1);
    }
    assert_eq!(n, 9);
    assert_eq!(progressive_files().len(), 654);
    let entries = corpus();
    assert_eq!(entries.len(), 132);
    // Every file with a reference is one libjpeg-turbo decoded.
    assert!(
        entries
            .iter()
            .all(|e| e.reference.is_empty() || parse_ref(e.reference).is_some())
    );
}

// ------------------------------------------------------------ progressive

/// Miri runs the progressive files of at most this many bytes, every 20th
/// (the differential test) and every 60th at chunk size 1 (chunking).
const MIRI_PROG_MAX_FILE: usize = 800;
const MIRI_PROG_DIFF_EVERY: usize = 20;
const MIRI_PROG_CHUNK_EVERY: usize = 60;

/// `progressive.pack`: `VARIANT/ORIGINAL` names, the progressive JPEG, no
/// reference of its own.
fn progressive_files() -> Vec<Entry<'static>> {
    entries_of(
        progressive_table::FILES
            .iter()
            .find(|c| c.file == "progressive.pack")
            .map_or(&[][..], |c| c.bytes),
    )
}

/// The name of the baseline original of a `VARIANT/ORIGINAL` name.
fn original_of(name: &str) -> &str {
    name.split_once('/').map_or(name, |(_, o)| o)
}

/// The reference of a progressive file: that of its baseline original (the
/// file `jpegtran` transcoded; the script asserted libjpeg-turbo decodes
/// both alike).
fn original_reference(name: &str) -> Option<Vec<u8>> {
    let original = original_of(name);
    all_decodable()
        .into_iter()
        .find(|(n, _, _)| n == original)
        .map(|(_, _, r)| r)
}

/// Every progressive file against libjpeg-turbo's output for its baseline
/// original: every sample exact.
#[test]
fn progressive_differential_vs_libjpeg_turbo() {
    let files = progressive_files();
    let mut total_hist = [0u64; 6];
    let (mut pass, mut run, mut xfail) = (0usize, 0usize, 0usize);
    let mut notes = Vec::new();
    let mut seen = 0usize;
    let mut variants: Vec<(String, usize)> = Vec::new();
    for e in &files {
        if miri() {
            if e.jpeg.len() > MIRI_PROG_MAX_FILE {
                continue;
            }
            seen = seen.saturating_add(1);
            if !seen.is_multiple_of(MIRI_PROG_DIFF_EVERY) {
                continue;
            }
        }
        run = run.saturating_add(1);
        let Some(reference) = original_reference(e.name) else {
            notes.push(format!("{}: no baseline original", e.name));
            continue;
        };
        // The orientation is in the original's name.
        match compare(original_of(e.name), e.jpeg, &reference) {
            Ok(hist) => {
                for (t, n) in total_hist.iter_mut().zip(hist) {
                    *t = t.saturating_add(n);
                }
                pass = pass.saturating_add(1);
                let v = e.name.split_once('/').map_or("?", |(v, _)| v);
                match variants.iter_mut().find(|(n, _)| n == v) {
                    Some((_, n)) => *n = n.saturating_add(1),
                    None => variants.push((v.to_owned(), 1)),
                }
            }
            Err(msg) if msg.contains("do not fit the work buffer") && is_four_component(e.name) => {
                xfail = xfail.saturating_add(1);
            }
            Err(msg) => notes.push(format!("{}: {msg}", e.name)),
        }
    }
    println!(
        "  difference histogram of every sample compared: {}",
        show(&total_hist)
    );
    println!("  files by variant: {variants:?}");
    print_suite(
        "JPEG progressive vs libjpeg-turbo: jpegtran copies of every baseline file (xfail: 4-component, full-resolution, refused by the work buffer)",
        pass,
        xfail,
        notes.len(),
        run,
    );
    assert!(notes.is_empty(), "{}", notes.join("\n"));
    assert!(miri() || run == files.len());
}

/// Progressive files at several chunk sizes equal the whole-file decode.
#[test]
fn progressive_chunking() {
    let files = progressive_files();
    let chunks: &[usize] = if miri() { &[1] } else { &[1, 5, 4096] };
    let every = if miri() { MIRI_PROG_CHUNK_EVERY } else { 3 };
    let (mut pass, mut run, mut xfail) = (0usize, 0usize, 0usize);
    for (i, e) in files.iter().enumerate() {
        if i % every != 0 || (miri() && e.jpeg.len() > MIRI_PROG_MAX_FILE) {
            continue;
        }
        run = run.saturating_add(1);
        let whole = decode(e.jpeg, e.jpeg.len().max(1));
        let same = chunks.iter().all(|&c| decode(e.jpeg, c) == whole);
        let refused = matches!(&whole, Err(Error::Unsupported(m)) if m.contains("work buffer"))
            && is_four_component(e.name);
        if same && whole.is_ok() {
            pass = pass.saturating_add(1);
        } else if same && refused {
            xfail = xfail.saturating_add(1);
        } else {
            println!("  {}: chunking differs or fails", e.name);
        }
    }
    print_suite(
        "JPEG progressive chunking: files at chunk sizes 1, 5 and 4096",
        pass,
        xfail,
        run.saturating_sub(pass).saturating_sub(xfail),
        run,
    );
    assert_eq!(pass.saturating_add(xfail), run);
}

/// Whether a file's name says it has four components (CMYK or YCCK): the
/// ones whose full-resolution coefficients may not fit the work buffer.
fn is_four_component(name: &str) -> bool {
    name.contains("cmyk") || name.contains("ycck")
}

/// Mutants of progressive files never panic and keep the invariant.
#[test]
fn progressive_mutations_never_panic() {
    let files = progressive_files();
    let every = if miri() { 100 } else { 4 };
    let per_file = if miri() { 2 } else { 6 };
    let (mut mutants, mut errors, mut frames, mut units) = (0usize, 0usize, 0usize, 0usize);
    for (n, e) in files.iter().enumerate() {
        if n % every != 0 || (miri() && e.jpeg.len() > 4096) {
            continue;
        }
        units = units.saturating_add(1);
        let mut rng = Rng(0x2545_F491_4F6C_DD1D ^ (u64::try_from(n).unwrap_or(0) << 20) ^ 7);
        for _ in 0..per_file {
            let m = mutate(e.jpeg, &mut rng);
            for chunk in [m.len().max(1), 5] {
                mutants = mutants.saturating_add(1);
                match survive(&m, chunk) {
                    Ok(_) => frames = frames.saturating_add(1),
                    Err(_) => errors = errors.saturating_add(1),
                }
            }
        }
    }
    println!("  {mutants} mutants, {errors} ended in an error, {frames} frames completed");
    print_suite(
        "JPEG progressive mutations: no panic, the invariant kept",
        units,
        0,
        0,
        units,
    );
}

/// SOF2 with these components and size.
fn sof2(w: u16, h: u16, comps: &[(u8, u8, u8)]) -> Vec<u8> {
    let mut b = vec![8];
    b.extend(h.to_be_bytes());
    b.extend(w.to_be_bytes());
    b.push(u8::try_from(comps.len()).unwrap_or(0));
    for &(id, hv, tq) in comps {
        b.extend([id, hv, tq]);
    }
    seg(0xC2, &b)
}

/// SOS of a progressive scan: `(component, DC and AC table selectors)`, then
/// `Ss`, `Se`, `Ah` and `Al`.
fn sos_p(comps: &[(u8, u8)], ss: u8, se: u8, ah: u8, al: u8) -> Vec<u8> {
    let mut b = vec![u8::try_from(comps.len()).unwrap_or(0)];
    for &(id, tdta) in comps {
        b.extend([id, tdta]);
    }
    b.extend([ss, se, (ah << 4) | al]);
    seg(0xDA, &b)
}

/// The AC table of the progressive tests: `0` is symbol `0x01` (run 0, size
/// 1), `10` is `0x02` (run 0, size 2), `110` is `0x00` (`EOB0`), `1110` is
/// `0x10` (`EOB1`: a run of 2 and one more bit), `1111` is `0x11`.
fn ac_table_p() -> Vec<u8> {
    dht(
        0x10,
        &[(1, 1), (2, 1), (3, 1), (4, 2)],
        &[0x01, 0x02, 0x00, 0x10, 0x11],
    )
}

/// A scan: its header and its already packed data.
type ScanBytes = (Vec<u8>, Vec<u8>);

/// A gray image of `blocks` blocks in a row, quantizer 8, with these scans.
fn prog_gray(blocks: u16, scans: &[ScanBytes]) -> Vec<u8> {
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof2(blocks.saturating_mul(8), 8, &[(1, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(ac_table_p());
    for (head, data) in scans {
        v.extend(head);
        v.extend(data);
    }
    v.extend([0xFF, 0xD9]);
    v
}

/// The R channel of every pixel of a decoded image.
fn reds(d: &Decoded) -> Vec<u8> {
    d.pixels
        .chunks(4)
        .filter_map(|p| p.first().copied())
        .collect()
}

#[test]
fn progressive_dc_first_and_refinement() -> Result<(), Error> {
    // DC code `1` then 4 bits: 1100 is a difference of 12; shifted left by
    // Al = 1 it is 24: a level of 128 + 24 * 8 / 8.
    let first = (sos_p(&[(1, 0x00)], 0, 0, 0, 1), pack(&[1, 1, 1, 0, 0]));
    // The refinement bit 1 of Ah = 1, Al = 0 makes it 25.
    let refine = (sos_p(&[(1, 0x00)], 0, 0, 1, 0), pack(&[1]));
    let one = prog_gray(1, std::slice::from_ref(&first));
    let d = decode(&one, one.len())?;
    assert_eq!(reds(&d), vec![152; 64]);
    let two = prog_gray(1, &[first.clone(), refine]);
    let d = decode(&two, two.len())?;
    assert_eq!(reds(&d), vec![153; 64]);
    // A refinement bit 0 changes nothing.
    let zero = prog_gray(1, &[first, (sos_p(&[(1, 0x00)], 0, 0, 1, 0), pack(&[0]))]);
    let d = decode(&zero, zero.len())?;
    assert_eq!(reds(&d), vec![152; 64]);
    Ok(())
}

#[test]
fn progressive_eob_run_covers_following_blocks() -> Result<(), Error> {
    // Three blocks, DC 0 in each (DC code `0`: category 0).
    let dc = (sos_p(&[(1, 0x00)], 0, 0, 0, 0), pack(&[0, 0, 0]));
    // Block 1: `0` and bit 1 (+1 at k = 1), then `1110` (EOB1) and the extra
    // bit 0: a run of 2, this block and the next, which takes no bits.
    // Block 3: `0` and bit 1, then `110` (EOB0).
    let ac = (
        sos_p(&[(1, 0x00)], 1, 63, 0, 0),
        pack(&[0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 0]),
    );
    let img = prog_gray(3, &[dc, ac]);
    let d = decode(&img, img.len())?;
    let r = reds(&d);
    let block = |b: usize| {
        let at = b.saturating_mul(8);
        r.get(at..at.saturating_add(8)).map(<[u8]>::to_vec)
    };
    // The first row of each block: blocks 1 and 3 equal and not flat, block
    // 2 flat.
    assert_eq!(block(0), block(2));
    assert_ne!(block(0), Some(vec![128; 8]));
    assert_eq!(block(1), Some(vec![128; 8]));
    Ok(())
}

#[test]
fn progressive_successive_approximation_equals_direct() -> Result<(), Error> {
    let dc = (sos_p(&[(1, 0x00)], 0, 0, 0, 0), pack(&[0]));
    // A: one AC-first scan, Al = 0: `10` (size 2), `11` (value 3), then
    // `110` (EOB0).
    let a = prog_gray(
        1,
        &[
            dc.clone(),
            (
                sos_p(&[(1, 0x00)], 1, 63, 0, 0),
                pack(&[1, 0, 1, 1, 1, 1, 0]),
            ),
        ],
    );
    // B: Al = 1: `0` (size 1), bit 1 (+1, shifted to 2), `110` EOB0; then the
    // refinement Ah = 1, Al = 0: `110` is an EOB0, whose run corrects the
    // nonzero coefficient with the next bit 1: 2 becomes 3.
    let b = prog_gray(
        1,
        &[
            dc,
            (sos_p(&[(1, 0x00)], 1, 63, 0, 1), pack(&[0, 1, 1, 1, 0])),
            (sos_p(&[(1, 0x00)], 1, 63, 1, 0), pack(&[1, 1, 0, 1])),
        ],
    );
    let (da, db) = (decode(&a, a.len())?, decode(&b, b.len())?);
    assert_eq!(da.pixels, db.pixels);
    // The coefficient is not flat.
    assert!(reds(&da).windows(2).any(|w| w.first() != w.get(1)));
    Ok(())
}

#[test]
fn progressive_scan_header_errors() {
    let dc = (sos_p(&[(1, 0x00)], 0, 0, 0, 0), pack(&[0]));
    let with = |head: Vec<u8>| prog_gray(1, &[dc.clone(), (head, pack(&[0]))]);
    // Al over 13, Al not Ah - 1, a DC scan with Se, a band backwards, Se
    // over 63.
    for (ss, se, ah, al) in [
        (0, 0, 0, 14),
        (1, 5, 2, 0),
        (0, 1, 0, 0),
        (5, 2, 0, 0),
        (1, 64, 0, 0),
    ] {
        let img = with(sos_p(&[(1, 0x00)], ss, se, ah, al));
        assert!(
            matches!(expect_err(&img), Error::Malformed(m) if m.contains("progressive scan")),
            "{ss} {se} {ah} {al}"
        );
    }
    // An AC scan of several components.
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof2(8, 8, &[(1, 0x11, 0), (2, 0x11, 0), (3, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(ac_table_p());
    v.extend(sos_p(&[(1, 0), (2, 0)], 1, 5, 0, 0));
    assert!(matches!(expect_err(&v), Error::Malformed(m) if m.contains("several components")));
    // A component never scanned.
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof2(8, 8, &[(1, 0x11, 0), (2, 0x11, 0), (3, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(ac_table_p());
    v.extend(sos_p(&[(1, 0)], 0, 0, 0, 0));
    v.extend(pack(&[0]));
    v.extend([0xFF, 0xD9]);
    assert!(matches!(expect_err(&v), Error::Malformed(m) if m.contains("no scan data")));
    // An AC scan with no AC table.
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof2(8, 8, &[(1, 0x11, 0)]));
    v.extend(dc_table());
    v.extend(sos_p(&[(1, 0)], 1, 5, 0, 0));
    assert!(matches!(expect_err(&v), Error::Malformed(m) if m.contains("not defined")));
    // A stream with no EOI after complete scans is truncated.
    let mut cut = prog_gray(1, &[dc]);
    cut.truncate(cut.len().saturating_sub(2));
    assert_eq!(decode(&cut, cut.len()).err(), Some(Error::Truncated));
}

/// A never-ending sequence of scans is refused at the 101st, and costs no
/// more than its bytes.
#[test]
fn progressive_scan_count_is_bounded() {
    let scan = (sos_p(&[(1, 0x00)], 0, 0, 0, 0), pack(&[0]));
    let ok = prog_gray(1, &vec![scan.clone(); 100]);
    assert!(decode(&ok, ok.len()).is_ok());
    let many = prog_gray(1, &vec![scan; 5000]);
    let e = expect_err(&many);
    assert!(
        matches!(e, Error::Unsupported(m) if m.contains("100 scans")),
        "{e:?}"
    );
}

/// Hostile sizes: a frame over the pixel limit is refused by the config; a
/// 4-component frame whose coefficients do not fit the work buffer by the
/// frame header; neither needs a big work buffer to say so.
#[test]
fn progressive_sizes_are_bounded() {
    for side in [65535u16, 16384] {
        let mut v = vec![0xFF, 0xD8];
        v.extend(sof2(side, side, &[(1, 0x11, 0)]));
        assert!(matches!(Jpeg::decode_config(&v), Err(Error::Size(_))));
    }
    // 1024 by 1024 with four full components needs 4 * (2 * 2^20 + ...) over
    // the 6 * 1055 * 1059 the config allows.
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof2(
        1024,
        1024,
        &[(1, 0x11, 0), (2, 0x11, 0), (3, 0x11, 0), (4, 0x11, 0)],
    ));
    v.extend(dc_table());
    v.extend(sos_p(&[(1, 0)], 0, 0, 0, 0));
    assert!(matches!(expect_err(&v), Error::Unsupported(m) if m.contains("work buffer")));
    // Subsampled, the four components fit: the decode goes on to the data.
    let mut v = vec![0xFF, 0xD8];
    v.extend(dqt(8));
    v.extend(sof2(
        1024,
        1024,
        &[(1, 0x22, 0), (2, 0x11, 0), (3, 0x11, 0), (4, 0x22, 0)],
    ));
    v.extend(dc_table());
    v.extend(sos_p(&[(1, 0)], 0, 0, 0, 0));
    assert_eq!(expect_err(&v), Error::Truncated);
}
