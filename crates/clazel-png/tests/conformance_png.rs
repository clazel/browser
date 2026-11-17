//! Conformance of `clazel-png` (phase-6.md item 6.4) on PngSuite
//! (`tests/data/pngsuite/`, the 2017-07-19 archive, embedded through
//! `tests/generated/pngsuite.rs`) and on streams made here, against the `png`
//! crate 0.18.1 as the reference engine. Each suite prints a
//! `clazel-conformance:` line (`xtask/src/conformance.rs`); a unit is one
//! file or stream.
//!
//! - **PngSuite differential**: every file. The `x*` files (14 corrupt ones)
//!   must be refused by both decoders; every other file must be accepted by
//!   both, with the same size and, **exactly**, the same RGBA8 for every
//!   frame. The reference is `png` with `EXPAND | STRIP_16`; the choices that
//!   make that exact (16 bits truncated to the high byte, 1, 2 and 4-bit
//!   samples scaled by 255 / (2^depth - 1), a palette index past the entries
//!   black) are listed in `src/pixel.rs`.
//! - **chunking**: each file through the `Decoder` interface in chunks of 1,
//!   2, 3, 7, 64 and 4096 bytes, with and without empty chunks between,
//!   gives exactly what one chunk of the whole file gives, with the
//!   invariant checked after every step and the canary bytes past the
//!   buffers untouched.
//! - **mutations**: deterministic mutants of each file (a byte or bit
//!   changed, a truncation, a run deleted, repeated or overwritten; half of
//!   them with every chunk's CRC rewritten so the mutation reaches the
//!   chunk's meaning) are decoded in two chunkings: none panics, the
//!   invariant holds after every step, the two chunkings agree, an error
//!   leaves the decoder spent, and where both decoders accept a mutant they
//!   agree on its pixels.
//! - **generated images**: every colour type and bit depth of Table 11.1,
//!   interlaced and not, odd sizes, every filter type, `tRNS`, palettes of
//!   every size, IDAT cut into pieces and ancillary chunks (`gAMA`, `cHRM`,
//!   `sRGB`, `iCCP`, `cICP`) among them, written by `tests/common` (stored
//!   zlib blocks, its own filters and Adam7 order) and by the `png`
//!   encoder (compressed), against the reference, exactly.
//! - **animations**: APNG streams with random frames (offsets, sizes, every
//!   `dispose_op` and `blend_op`, the default image in the animation or
//!   not, interlaced, every colour type), the frames' facts and the
//!   composited canvas after each frame against the reference's frames
//!   composited by the test's own code.
//! - **by hand**: streams for each rule of the chunk grammar, each
//!   refusal and each listed choice, with the outcome stated.
//!
//! Under Miri (about 1,600 times slower than a native debug run, with a
//! 300 s limit per test) every suite runs a stride, stated where it is used
//! (`MIRI`); the strides were sized by running each suite natively with the
//! Miri branch forced on and timing it: see the README.

mod common;

mod suite {
    include!("generated/pngsuite.rs");
}

use common::{
    Decoded, End, FrameSpec, Img, KINDS, Rng, apng_bytes, at, chunk, compare, crc32, decode, fctl,
    ihdr, png_bytes, random_img, reference, us, zlib_stored,
};

/// Whether the tests are running under Miri.
const MIRI: bool = cfg!(miri);

/// Ours and the reference's verdict on a stream.
fn run(bytes: &[u8]) -> Option<(Decoded, Result<common::Reference, String>)> {
    let ours = decode(bytes, 4096, false).ok()?;
    Some((ours, reference(bytes)))
}

/// Whether the reference read the whole stream.
fn ref_ok(r: &Result<common::Reference, String>) -> bool {
    r.as_ref().is_ok_and(|r| r.complete)
}

fn report(name: &str, pass: usize, xfail: usize, fail: usize, total: usize) {
    println!(
        "clazel-conformance: suite=\"{name}\" pass={pass} xfail={xfail} fail={fail} total={total}"
    );
}

/// The archive's 176 files, 14 of them the corrupt `x*` ones.
#[test]
fn pngsuite_inventory() {
    assert_eq!(suite::FILES.len(), 176);
    assert_eq!(
        suite::FILES
            .iter()
            .filter(|c| c.file.starts_with('x'))
            .count(),
        14
    );
    assert!(suite::FILES.iter().all(|c| c.sha256.len() == 64));
}

#[test]
fn pngsuite_differential() {
    let (mut pass, mut fail) = (0usize, 0usize);
    let mut notes = Vec::new();
    let mut refused = 0usize;
    // Under Miri: the files of at most 1 KiB, whichever of the 176 they are.
    let files: Vec<(&str, &[u8])> = suite::FILES
        .iter()
        .map(|c| (c.file, c.bytes))
        .filter(|(_, b)| !MIRI || b.len() <= MIRI_FILE_BYTES)
        .collect();
    for (name, bytes) in &files {
        let corrupt = name.starts_with('x');
        let ours = decode(bytes, 4096, false);
        let reference = reference(bytes);
        let verdict: Result<(), String> = if corrupt {
            // A config error (bad signature, IHDR) is a refusal too.
            let ours_refuses = match &ours {
                Ok(o) => matches!(o.end, End::Error(_)),
                Err(_) => true,
            };
            if ours_refuses && !ref_ok(&reference) {
                refused += 1;
                Ok(())
            } else {
                Err(format!(
                    "a corrupt file: ours refuses {ours_refuses}, the reference reads it {}",
                    ref_ok(&reference)
                ))
            }
        } else {
            match (&ours, &reference) {
                (Ok(o), Ok(r)) => {
                    if o.end != End::Iend {
                        Err(format!("ours ends {:?}", o.end))
                    } else if !r.complete {
                        Err("the reference fails".into())
                    } else {
                        compare(o, r)
                    }
                }
                (Err(e), _) => Err(format!("ours fails: {e}")),
                (_, Err(e)) => Err(format!("the reference fails: {e}")),
            }
        };
        match verdict {
            Ok(()) => pass += 1,
            Err(why) => {
                fail += 1;
                notes.push(format!("{name}: {why}"));
            }
        }
    }
    println!("  {} corrupt files refused by both", refused);
    report(
        "PngSuite differential: exact RGBA8 against png 0.18.1",
        pass,
        0,
        fail,
        files.len(),
    );
    assert!(notes.is_empty(), "{}", notes.join("\n"));
}

/// Under Miri, the PngSuite files of at most this many bytes.
const MIRI_FILE_BYTES: usize = 300;

#[test]
fn pngsuite_chunking() {
    let sizes: &[usize] = if MIRI {
        &[1, 64]
    } else {
        &[1, 2, 3, 7, 64, 4096]
    };
    let (mut pass, mut fail) = (0usize, 0usize);
    let files: Vec<(&str, &[u8])> = suite::FILES
        .iter()
        .map(|c| (c.file, c.bytes))
        .filter(|(_, b)| !MIRI || b.len() <= MIRI_FILE_BYTES)
        .collect();
    for (name, bytes) in &files {
        let whole = decode(bytes, bytes.len().max(1), false);
        let mut ok = true;
        for &size in sizes {
            for empties in [false, true] {
                if decode(bytes, size, empties) != whole {
                    println!("  {name}: chunk {size}, empties {empties}: differs from one chunk");
                    ok = false;
                }
            }
        }
        if ok {
            pass += 1;
        } else {
            fail += 1;
        }
    }
    report(
        "PNG chunking: every file at chunk sizes 1 to 4096",
        pass,
        0,
        fail,
        files.len(),
    );
    assert_eq!(fail, 0);
}

/// Rewrites every chunk's CRC of `bytes` so a mutation inside a chunk is
/// not stopped by the CRC check.
fn fix_crcs(bytes: &mut [u8]) {
    let mut pos = 8usize;
    while let Some(head) = bytes.get(pos..pos.saturating_add(8)) {
        let len = us(u32::from_be_bytes([
            at(head, 0),
            at(head, 1),
            at(head, 2),
            at(head, 3),
        ]));
        let end = pos.saturating_add(8).saturating_add(len);
        let Some(body) = bytes.get(pos.saturating_add(4)..end) else {
            return;
        };
        let crc = crc32(body).to_be_bytes();
        let Some(slot) = bytes.get_mut(end..end.saturating_add(4)) else {
            return;
        };
        slot.copy_from_slice(&crc);
        pos = end.saturating_add(4);
    }
}

/// The `i`-th mutant of `bytes` (deterministic in `seed`).
fn mutant(bytes: &[u8], seed: u64, i: usize) -> Vec<u8> {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    for _ in 0..=i {
        rng.next();
    }
    let mut v = bytes.to_vec();
    let n = v.len().max(1);
    let pos = |rng: &mut Rng| rng.below(n);
    match i % 7 {
        0 => {
            let p = pos(&mut rng);
            if let Some(b) = v.get_mut(p) {
                *b = rng.byte();
            }
        }
        1 => {
            let p = pos(&mut rng);
            v.truncate(p);
        }
        2 => {
            let p = pos(&mut rng);
            let l = rng.below(40).saturating_add(1);
            v.drain(p.min(v.len())..p.saturating_add(l).min(v.len()));
        }
        3 => {
            let p = pos(&mut rng);
            let l = rng.below(40).saturating_add(1);
            let end = p.saturating_add(l).min(v.len());
            let run: Vec<u8> = v.get(p.min(end)..end).unwrap_or(&[]).to_vec();
            let at_ = p.min(v.len());
            v.splice(at_..at_, run);
        }
        4 => {
            let p = pos(&mut rng);
            let l = rng.below(16).saturating_add(1);
            for k in 0..l {
                if let Some(b) = v.get_mut(p.saturating_add(k)) {
                    *b = rng.byte();
                }
            }
        }
        5 => {
            // A bit of the first 70 bytes: the signature, IHDR and what follows.
            let p = rng.below(v.len().clamp(1, 70));
            let bit = rng.below(8);
            if let Some(b) = v.get_mut(p) {
                *b ^= 1u8.wrapping_shl(u32::try_from(bit).unwrap_or(0));
            }
        }
        _ => {
            // Several bytes at once.
            for _ in 0..rng.below(4).saturating_add(2) {
                let p = pos(&mut rng);
                if let Some(b) = v.get_mut(p) {
                    *b = rng.byte();
                }
            }
        }
    }
    if rng.below(2) == 0 {
        fix_crcs(&mut v);
    }
    v
}

/// Mutants per file, and under Miri.
const MUTANTS: usize = 60;
const MIRI_MUTANTS: usize = 2;

#[test]
fn pngsuite_mutations() {
    let per_file = if MIRI { MIRI_MUTANTS } else { MUTANTS };
    let (mut mutants, mut errors, mut frames, mut both_ok, mut one_ok, mut skipped) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
    let mut notes = Vec::new();
    let files: Vec<(&str, &[u8])> = suite::FILES
        .iter()
        .map(|c| (c.file, c.bytes))
        .filter(|(n, b)| !n.starts_with('x') && (!MIRI || b.len() <= MIRI_FILE_BYTES))
        .collect();
    for (name, bytes) in &files {
        let seed = u64::from(crc32(name.as_bytes()));
        for i in 0..per_file {
            let m = mutant(bytes, seed, i);
            let whole = decode(&m, m.len().max(1), false);
            let small = decode(&m, 7, false);
            mutants += 1;
            if whole != small {
                notes.push(format!("{name} mutant {i}: chunkings differ"));
                continue;
            }
            let Ok(o) = whole else {
                skipped += 1;
                continue;
            };
            frames += o.frames.len();
            if matches!(o.end, End::Error(_)) {
                errors += 1;
            }
            if !MIRI {
                match (o.end == End::Iend, reference(&m)) {
                    (true, Ok(r)) if r.complete => {
                        both_ok += 1;
                        if let Err(why) = compare(&o, &r) {
                            notes.push(format!("{name} mutant {i}: accepted by both, {why}"));
                        }
                    }
                    (true, _) | (false, Ok(_)) => one_ok += 1,
                    (false, Err(_)) => {}
                }
            }
        }
    }
    println!(
        "  {mutants} mutants, {errors} ended in an error, {skipped} refused at the header, {frames} frames completed, {both_ok} accepted by both (and equal), {one_ok} accepted by one only"
    );
    report(
        "PNG mutations: no panic, the invariant kept, both chunkings agree",
        files.len().saturating_sub(notes.len()),
        0,
        notes.len(),
        files.len(),
    );
    assert!(notes.is_empty(), "{}", notes.join("\n"));
}

// ------------------------------------------------------- generated images

/// Ancillary chunks a decoder reads and ignores (11.3.2): `gAMA`, `cHRM`,
/// `sRGB`, `iCCP`, `cICP`, and a few text and metadata chunks.
fn ancillary() -> Vec<Vec<u8>> {
    let mut icc = b"profile\0\0".to_vec();
    icc.extend(zlib_stored(b"not really a profile"));
    vec![
        chunk(b"gAMA", &45455u32.to_be_bytes()),
        chunk(
            b"cHRM",
            &[
                0x00, 0x00, 0x7A, 0x26, 0x00, 0x00, 0x80, 0x84, 0x00, 0x00, 0xFA, 0x00, 0x00, 0x00,
                0x80, 0xE8, 0x00, 0x00, 0x75, 0x30, 0x00, 0x00, 0xEA, 0x60, 0x00, 0x00, 0x3A, 0x98,
                0x00, 0x00, 0x17, 0x70,
            ],
        ),
        chunk(b"sRGB", &[0]),
        chunk(b"iCCP", &icc),
        chunk(b"cICP", &[1, 13, 0, 1]),
        chunk(b"tEXt", b"Title\0a title"),
        chunk(b"pHYs", &[0, 0, 0x0B, 0x13, 0, 0, 0x0B, 0x13, 1]),
        chunk(b"tIME", &[0x07, 0xE9, 11, 17, 12, 0, 0]),
    ]
}

/// A deterministic mix of images: every colour type and depth, interlaced
/// and not, sizes that exercise every Adam7 pass boundary, filters, `tRNS`,
/// palettes of every size, IDAT cut into pieces, ancillary chunks.
fn generated(stride: usize) -> Vec<(String, Vec<u8>)> {
    let mut rng = Rng(0x5EED_0001);
    let sizes = [1u32, 2, 3, 5, 8, 9];
    let mut out = Vec::new();
    let mut n = 0usize;
    for &(ct, depth) in KINDS {
        for interlaced in [false, true] {
            for &w in &sizes {
                for &h in &sizes {
                    n = n.saturating_add(1);
                    let mut img =
                        random_img(&mut rng, w, h, ct, depth, interlaced, n.is_multiple_of(2));
                    if !n.is_multiple_of(stride) {
                        continue;
                    }
                    img.filters = (0..5u8)
                        .map(|k| k.wrapping_add(u8::try_from(n % 5).unwrap_or(0)) % 5)
                        .collect();
                    img.idat_size = at(&[0usize, 1, 3, 7, 64], n % 5);
                    if n.is_multiple_of(4) {
                        img.extras = ancillary();
                    }
                    if (ct == 2 || ct == 6) && n.is_multiple_of(7) {
                        // A suggested palette (11.2.2) of a truecolour image.
                        img.palette = (0..9).map(|_| rng.byte()).collect();
                    }
                    out.push((
                        format!("{ct}/{depth} {w}x{h} interlaced={interlaced} #{n}"),
                        png_bytes(&img),
                    ));
                }
            }
        }
    }
    out
}

/// The same kinds written by the `png` encoder (compressed, its own
/// filters), not interlaced (the encoder cannot write Adam7).
fn encoded(stride: usize) -> Vec<(String, Vec<u8>)> {
    let mut rng = Rng(0x5EED_0002);
    let filters = [
        png::Filter::NoFilter,
        png::Filter::Sub,
        png::Filter::Up,
        png::Filter::Avg,
        png::Filter::Paeth,
        png::Filter::Adaptive,
        png::Filter::MinEntropy,
    ];
    let levels = [
        png::Compression::NoCompression,
        png::Compression::Fastest,
        png::Compression::Fast,
        png::Compression::Balanced,
        png::Compression::High,
    ];
    let mut out = Vec::new();
    let mut n = 0usize;
    for &(ct, depth) in KINDS {
        for &(w, h) in &[(1u32, 1u32), (7, 5), (33, 17), (64, 40)] {
            n = n.saturating_add(1);
            if !n.is_multiple_of(stride) {
                continue;
            }
            let img = random_img(&mut rng, w, h, ct, depth, false, !n.is_multiple_of(2));
            let ch = common::channels(ct);
            let mut data = Vec::new();
            for row in img.samples.chunks(us(w).saturating_mul(ch).max(1)) {
                data.extend(common::pack(row, depth));
            }
            let mut bytes = Vec::new();
            let mut enc = png::Encoder::new(&mut bytes, w, h);
            enc.set_color(match ct {
                0 => png::ColorType::Grayscale,
                2 => png::ColorType::Rgb,
                3 => png::ColorType::Indexed,
                4 => png::ColorType::GrayscaleAlpha,
                _ => png::ColorType::Rgba,
            });
            enc.set_depth(match depth {
                1 => png::BitDepth::One,
                2 => png::BitDepth::Two,
                4 => png::BitDepth::Four,
                8 => png::BitDepth::Eight,
                _ => png::BitDepth::Sixteen,
            });
            if ct == 3 {
                enc.set_palette(img.palette.clone());
            }
            if let Some(t) = &img.trns {
                enc.set_trns(t.clone());
            }
            enc.set_filter(at_f(&filters, n));
            enc.set_compression(at_c(&levels, n));
            let wrote = enc
                .write_header()
                .and_then(|mut wr| wr.write_image_data(&data).and_then(|()| wr.finish()));
            if wrote.is_ok() {
                out.push((format!("encoder {ct}/{depth} {w}x{h} #{n}"), bytes));
            }
        }
    }
    out
}

fn at_f(v: &[png::Filter], i: usize) -> png::Filter {
    v.get(i.checked_rem(v.len()).unwrap_or(0))
        .copied()
        .unwrap_or_default()
}

fn at_c(v: &[png::Compression], i: usize) -> png::Compression {
    v.get(i.checked_rem(v.len()).unwrap_or(0))
        .copied()
        .unwrap_or_default()
}

/// Runs each stream through both decoders; a stream passes when both accept
/// it and agree exactly.
fn differential(name: &str, cases: &[(String, Vec<u8>)]) {
    let (mut pass, mut fail) = (0usize, 0usize);
    for (what, bytes) in cases {
        let verdict = match run(bytes) {
            None => Err("ours refuses the header".to_string()),
            Some((o, Ok(r))) => {
                if o.end != End::Iend {
                    Err(format!("ours ends {:?}", o.end))
                } else if !r.complete {
                    Err("the reference fails".into())
                } else {
                    compare(&o, &r)
                }
            }
            Some((_, Err(e))) => Err(format!("the reference fails: {e}")),
        };
        match verdict {
            Ok(()) => pass = pass.saturating_add(1),
            Err(why) => {
                fail = fail.saturating_add(1);
                println!("  {what}: {why}");
            }
        }
    }
    report(name, pass, 0, fail, cases.len());
    assert_eq!(fail, 0);
}

/// Under Miri every `MIRI_STRIDE`-th generated image.
const MIRI_STRIDE: usize = 40;

#[test]
fn generated_images() {
    differential(
        "PNG generated: every colour type and depth, Adam7, filters, tRNS, palettes",
        &generated(if MIRI { MIRI_STRIDE } else { 1 }),
    );
}

#[test]
fn encoder_images() {
    differential(
        "PNG from the png encoder: compressed, every filter, against png",
        &encoded(if MIRI { 4 } else { 1 }),
    );
}

// -------------------------------------------------------------- animations

/// Random APNG streams: a canvas, a default image, 1 to 4 frames with random
/// rectangles and every dispose and blend operation.
fn animations(count: usize) -> Vec<(String, Vec<u8>)> {
    let mut rng = Rng(0x5EED_0003);
    let mut out = Vec::new();
    for case in 0..count {
        let (ct, depth) = at(
            &KINDS.iter().map(|&k| Some(k)).collect::<Vec<_>>(),
            case.checked_rem(KINDS.len()).unwrap_or(0),
        )
        .unwrap_or((6, 8));
        let w = u32::try_from(rng.below(11).saturating_add(1)).unwrap_or(1);
        let h = u32::try_from(rng.below(11).saturating_add(1)).unwrap_or(1);
        let interlaced = rng.below(2) == 0;
        let with_trns = rng.below(2) == 0;
        let base = random_img(&mut rng, w, h, ct, depth, interlaced, with_trns);
        let entries = base.palette.len() / 3;
        let frame = |rng: &mut Rng, fw: u32, fh: u32, x: u32, y: u32| {
            let mut img = random_img(rng, fw, fh, ct, depth, interlaced, false);
            img.palette = base.palette.clone();
            img.trns = base.trns.clone();
            if ct == 3 {
                for s in &mut img.samples {
                    *s = s
                        .checked_rem(u16::try_from(entries).unwrap_or(1))
                        .unwrap_or(0);
                }
            }
            img.idat_size = at(&[0usize, 1, 5, 64], rng.below(4));
            FrameSpec {
                x,
                y,
                img,
                delay: (u16::try_from(rng.below(50)).unwrap_or(0), 100),
                dispose: u8::try_from(rng.below(3)).unwrap_or(0),
                blend: u8::try_from(rng.below(2)).unwrap_or(0),
            }
        };
        let default_frame = if rng.below(2) == 0 {
            Some(frame(&mut rng, w, h, 0, 0))
        } else {
            None
        };
        let mut frames = Vec::new();
        for _ in 0..rng.below(4).saturating_add(1) {
            let fw = u32::try_from(rng.below(us(w)).saturating_add(1)).unwrap_or(1);
            let fh = u32::try_from(rng.below(us(h)).saturating_add(1)).unwrap_or(1);
            let x =
                u32::try_from(rng.below(us(w.saturating_sub(fw)).saturating_add(1))).unwrap_or(0);
            let y =
                u32::try_from(rng.below(us(h.saturating_sub(fh)).saturating_add(1))).unwrap_or(0);
            frames.push(frame(&mut rng, fw, fh, x, y));
        }
        out.push((
            format!(
                "apng #{case} {ct}/{depth} {w}x{h} interlaced={interlaced} default_in_animation={} frames={}",
                default_frame.is_some(),
                frames.len()
            ),
            apng_bytes(&base, default_frame.as_ref(), &frames),
        ));
    }
    out
}

#[test]
fn animation_images() {
    differential(
        "APNG: frames, dispose and blend, composited, against png",
        &animations(if MIRI { 8 } else { 600 }),
    );
}

// ----------------------------------------------------------------- by hand

fn tiny() -> Img {
    Img {
        w: 2,
        h: 2,
        ct: 0,
        depth: 8,
        interlaced: false,
        samples: vec![10, 20, 30, 40],
        palette: Vec::new(),
        trns: None,
        filters: vec![0],
        idat_size: 0,
        extras: Vec::new(),
    }
}

fn join(chunks: &[Vec<u8>]) -> Vec<u8> {
    let mut v = common::SIG.to_vec();
    for c in chunks {
        v.extend_from_slice(c);
    }
    v
}

fn iend() -> Vec<u8> {
    chunk(b"IEND", &[])
}

fn idat_of(img: &Img) -> Vec<u8> {
    chunk(b"IDAT", &zlib_stored(&common::scanlines(img)))
}

/// What a hand-made stream must do.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Want {
    /// IEND after this many frames.
    Frames(usize),
    /// This many frames and then the input ends (no IEND).
    FramesThenEnd(usize),
    /// An error (or the header refused), after any number of frames.
    Refused,
}

fn outcome(bytes: &[u8]) -> Want {
    match decode(bytes, 5, false) {
        Err(_) => Want::Refused,
        Ok(d) => match d.end {
            End::Iend => Want::Frames(d.frames.len()),
            End::Truncated => Want::FramesThenEnd(d.frames.len()),
            End::Error(_) => Want::Refused,
        },
    }
}

fn flip_last_byte_of(chunk_bytes: &[u8]) -> Vec<u8> {
    let mut c = chunk_bytes.to_vec();
    if let Some(b) = c.last_mut() {
        *b ^= 0xFF;
    }
    c
}

fn img_with(f: impl FnOnce(&mut Img)) -> Img {
    let mut i = tiny();
    f(&mut i);
    i
}

/// The 2 by 2 image's chunks, to take apart.
fn parts() -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let img = tiny();
    (ihdr(&img), idat_of(&img), iend())
}

fn hand_cases() -> Vec<(String, Vec<u8>, Want)> {
    let (h, d, e) = parts();
    let mut v: Vec<(String, Vec<u8>, Want)> = Vec::new();
    let mut add = |name: &str, bytes: Vec<u8>, want: Want| v.push((name.to_string(), bytes, want));
    add(
        "minimal",
        join(&[h.clone(), d.clone(), e.clone()]),
        Want::Frames(1),
    );
    // 5.6, 5.4: unknown ancillary chunks are ignored, unknown critical ones refused.
    add(
        "unknown ancillary",
        join(&[h.clone(), chunk(b"abcd", b"xyz"), d.clone(), e.clone()]),
        Want::Frames(1),
    );
    add(
        "unknown critical",
        join(&[h.clone(), chunk(b"ABCD", b"xyz"), d.clone(), e.clone()]),
        Want::Refused,
    );
    add(
        "chunk type not letters",
        join(&[h.clone(), chunk(b"ab1d", b""), d.clone(), e.clone()]),
        Want::Refused,
    );
    // 5.5: every CRC is checked, ancillary ones too (stricter than png's default).
    add(
        "bad IDAT CRC",
        join(&[h.clone(), flip_last_byte_of(&d), e.clone()]),
        Want::Refused,
    );
    add(
        "bad IHDR CRC",
        join(&[flip_last_byte_of(&h), d.clone(), e.clone()]),
        Want::Refused,
    );
    add(
        "bad ancillary CRC",
        join(&[
            h.clone(),
            flip_last_byte_of(&chunk(b"tEXt", b"a\0b")),
            d.clone(),
            e.clone(),
        ]),
        Want::Refused,
    );
    add(
        "bad IEND CRC (the frame was delivered before it)",
        join(&[h.clone(), d.clone(), flip_last_byte_of(&e)]),
        Want::Refused,
    );
    // 5.6, 11.2.3: IDAT chunks are consecutive; empty ones are allowed.
    let z = zlib_stored(&common::scanlines(&tiny()));
    let pieces: Vec<Vec<u8>> = z.chunks(1).map(|p| chunk(b"IDAT", p)).collect();
    let mut one_byte = vec![h.clone()];
    one_byte.extend(pieces.clone());
    one_byte.push(e.clone());
    add(
        "IDAT in pieces of one byte",
        join(&one_byte),
        Want::Frames(1),
    );
    let mut with_empty = vec![h.clone(), chunk(b"IDAT", b"")];
    with_empty.extend(pieces.iter().flat_map(|p| [p.clone(), chunk(b"IDAT", b"")]));
    with_empty.push(e.clone());
    add(
        "empty IDAT chunks between",
        join(&with_empty),
        Want::Frames(1),
    );
    let (first, second) = z.split_at(z.len() / 2);
    add(
        "IDAT split by another chunk",
        join(&[
            h.clone(),
            chunk(b"IDAT", first),
            chunk(b"tEXt", b"a\0b"),
            chunk(b"IDAT", second),
            e.clone(),
        ]),
        Want::Refused,
    );
    // The frame is done when its IDAT's CRC is read; IEND is not needed for it.
    add(
        "no IEND",
        join(&[h.clone(), d.clone()]),
        Want::FramesThenEnd(1),
    );
    add(
        "bytes after IEND",
        {
            let mut b = join(&[h.clone(), d.clone(), e.clone()]);
            b.extend_from_slice(b"trailing");
            b
        },
        Want::Frames(1),
    );
    // Extra bytes after the zlib stream, in its IDAT or in a later one.
    let mut padded = z.clone();
    padded.extend_from_slice(&[1, 2, 3]);
    add(
        "bytes after the zlib stream",
        join(&[h.clone(), chunk(b"IDAT", &padded), e.clone()]),
        Want::Frames(1),
    );
    add(
        "a second IDAT after the stream",
        join(&[h.clone(), d.clone(), chunk(b"IDAT", b"junk"), e.clone()]),
        Want::Frames(1),
    );
    // 5.6, 11.2.1: IHDR first, once, 13 bytes.
    add("no IDAT", join(&[h.clone(), e.clone()]), Want::Refused);
    add(
        "IDAT before IHDR",
        join(&[d.clone(), h.clone(), e.clone()]),
        Want::Refused,
    );
    add(
        "IHDR twice",
        join(&[h.clone(), h.clone(), d.clone(), e.clone()]),
        Want::Refused,
    );
    add(
        "IHDR of 12 bytes",
        join(&[
            chunk(b"IHDR", &[0, 0, 0, 2, 0, 0, 0, 2, 8, 0, 0, 0]),
            d.clone(),
            e.clone(),
        ]),
        Want::Refused,
    );
    add(
        "signature wrong",
        {
            let mut b = join(&[h.clone(), d.clone(), e.clone()]);
            if let Some(x) = b.get_mut(3) {
                *x = 0x48;
            }
            b
        },
        Want::Refused,
    );
    // 11.2.1: IHDR's fields. Table 11.1 is every (colour type, depth) allowed.
    for ct in 0..=7u8 {
        for depth in 0..=17u8 {
            let allowed = KINDS.contains(&(ct, depth));
            let mut img = tiny();
            img.ct = ct;
            img.depth = depth;
            let mut data = Vec::new();
            data.extend_from_slice(&2u32.to_be_bytes());
            data.extend_from_slice(&2u32.to_be_bytes());
            data.extend_from_slice(&[depth, ct, 0, 0, 0]);
            // Enough zeros for any layout of 2 by 2 (rows of at most 16 bytes).
            let idat = chunk(b"IDAT", &zlib_stored(&[0u8; 34]));
            let mut parts = vec![chunk(b"IHDR", &data)];
            if ct == 3 && allowed {
                parts.push(chunk(b"PLTE", &[0, 0, 0]));
            }
            parts.push(idat);
            parts.push(e.clone());
            let _ = img;
            // Allowed kinds with 34 zero bytes: too much data for the small
            // ones (11.2.3 and 10.2: the stream is exactly the scanlines), so
            // only the refusal of the unallowed ones is stated here.
            if !allowed {
                add(
                    &format!("IHDR colour type {ct} depth {depth}"),
                    join(&parts),
                    Want::Refused,
                );
            }
        }
    }
    for (what, bad) in [
        ("compression method 1", [8u8, 0, 1, 0, 0]),
        ("filter method 1", [8, 0, 0, 1, 0]),
        ("interlace method 2", [8, 0, 0, 0, 2]),
    ] {
        let mut data = Vec::new();
        data.extend_from_slice(&2u32.to_be_bytes());
        data.extend_from_slice(&2u32.to_be_bytes());
        data.extend_from_slice(&bad);
        add(
            &format!("IHDR {what}"),
            join(&[chunk(b"IHDR", &data), d.clone(), e.clone()]),
            Want::Refused,
        );
    }
    let zero_width = [0u8, 0, 0, 0, 0, 0, 0, 2, 8, 0, 0, 0, 0];
    add(
        "IHDR width 0",
        join(&[chunk(b"IHDR", &zero_width), d.clone(), e.clone()]),
        Want::Refused,
    );
    // 11.2.2 PLTE and 11.3.1 tRNS.
    let pal = |n: usize| chunk(b"PLTE", &vec![9u8; n]);
    let indexed = |f: &dyn Fn(&mut Img)| {
        img_with(|i| {
            i.ct = 3;
            i.depth = 8;
            i.samples = vec![0, 1, 1, 0];
            f(i);
        })
    };
    let ix = indexed(&|_| {});
    add(
        "indexed with PLTE",
        join(&[ihdr(&ix), pal(6), idat_of(&ix), e.clone()]),
        Want::Frames(1),
    );
    add(
        "indexed without PLTE",
        join(&[ihdr(&ix), idat_of(&ix), e.clone()]),
        Want::Refused,
    );
    add(
        "PLTE twice",
        join(&[ihdr(&ix), pal(6), pal(6), idat_of(&ix), e.clone()]),
        Want::Refused,
    );
    add(
        "PLTE after IDAT",
        join(&[ihdr(&ix), pal(6), idat_of(&ix), pal(6), e.clone()]),
        Want::Refused,
    );
    add(
        "PLTE of 4 bytes",
        join(&[ihdr(&ix), pal(4), idat_of(&ix), e.clone()]),
        Want::Refused,
    );
    add(
        "PLTE of 0 bytes",
        join(&[ihdr(&ix), pal(0), idat_of(&ix), e.clone()]),
        Want::Refused,
    );
    add(
        "PLTE of 771 bytes",
        join(&[ihdr(&ix), pal(771), idat_of(&ix), e.clone()]),
        Want::Refused,
    );
    add(
        "PLTE of 256 entries",
        join(&[ihdr(&ix), pal(768), idat_of(&ix), e.clone()]),
        Want::Frames(1),
    );
    add(
        "PLTE in a greyscale image",
        join(&[h.clone(), pal(3), d.clone(), e.clone()]),
        Want::Refused,
    );
    let rgb = img_with(|i| {
        i.ct = 2;
        i.samples = vec![1; 12];
    });
    add(
        "PLTE (suggested) in a truecolour image",
        join(&[ihdr(&rgb), pal(6), idat_of(&rgb), e.clone()]),
        Want::Frames(1),
    );
    add(
        "tRNS before PLTE",
        join(&[
            ihdr(&ix),
            chunk(b"tRNS", &[1]),
            pal(6),
            idat_of(&ix),
            e.clone(),
        ]),
        Want::Refused,
    );
    add(
        "tRNS for indexed",
        join(&[
            ihdr(&ix),
            pal(6),
            chunk(b"tRNS", &[1, 2]),
            idat_of(&ix),
            e.clone(),
        ]),
        Want::Frames(1),
    );
    add(
        "tRNS of 0 entries",
        join(&[
            ihdr(&ix),
            pal(6),
            chunk(b"tRNS", &[]),
            idat_of(&ix),
            e.clone(),
        ]),
        Want::Frames(1),
    );
    add(
        "tRNS longer than the palette",
        join(&[
            ihdr(&ix),
            pal(6),
            chunk(b"tRNS", &[1, 2, 3]),
            idat_of(&ix),
            e.clone(),
        ]),
        Want::Refused,
    );
    add(
        "tRNS twice",
        join(&[
            ihdr(&ix),
            pal(6),
            chunk(b"tRNS", &[1]),
            chunk(b"tRNS", &[1]),
            idat_of(&ix),
            e.clone(),
        ]),
        Want::Refused,
    );
    add(
        "tRNS after IDAT",
        join(&[
            ihdr(&ix),
            pal(6),
            idat_of(&ix),
            chunk(b"tRNS", &[1]),
            e.clone(),
        ]),
        Want::Refused,
    );
    add(
        "tRNS for greyscale",
        join(&[h.clone(), chunk(b"tRNS", &[0, 10]), d.clone(), e.clone()]),
        Want::Frames(1),
    );
    add(
        "tRNS for greyscale of 1 byte",
        join(&[h.clone(), chunk(b"tRNS", &[10]), d.clone(), e.clone()]),
        Want::Refused,
    );
    add(
        "tRNS for truecolour",
        join(&[
            ihdr(&rgb),
            chunk(b"tRNS", &[0, 1, 0, 1, 0, 1]),
            idat_of(&rgb),
            e.clone(),
        ]),
        Want::Frames(1),
    );
    add(
        "tRNS for truecolour of 2 bytes",
        join(&[
            ihdr(&rgb),
            chunk(b"tRNS", &[0, 1]),
            idat_of(&rgb),
            e.clone(),
        ]),
        Want::Refused,
    );
    let rgba = img_with(|i| {
        i.ct = 6;
        i.samples = vec![1; 16];
    });
    add(
        "tRNS with an alpha channel",
        join(&[
            ihdr(&rgba),
            chunk(b"tRNS", &[0, 1, 0, 1, 0, 1]),
            idat_of(&rgba),
            e.clone(),
        ]),
        Want::Refused,
    );
    // 10.2, 9.1: the stream holds exactly the scanlines; filter types are 0 to 4.
    let raw = common::scanlines(&tiny());
    let short = zlib_stored(raw.get(..raw.len().saturating_sub(1)).unwrap_or(&[]));
    add(
        "data one byte short",
        join(&[h.clone(), chunk(b"IDAT", &short), e.clone()]),
        Want::Refused,
    );
    let mut long_raw = raw.clone();
    long_raw.push(0);
    add(
        "data one byte long",
        join(&[
            h.clone(),
            chunk(b"IDAT", &zlib_stored(&long_raw)),
            e.clone(),
        ]),
        Want::Refused,
    );
    let mut bad_adler = z.clone();
    if let Some(b) = bad_adler.last_mut() {
        *b ^= 1;
    }
    add(
        "bad Adler-32",
        join(&[h.clone(), chunk(b"IDAT", &bad_adler), e.clone()]),
        Want::Refused,
    );
    let mut f5 = raw.clone();
    if let Some(b) = f5.first_mut() {
        *b = 5;
    }
    add(
        "filter type 5",
        join(&[h.clone(), chunk(b"IDAT", &zlib_stored(&f5)), e.clone()]),
        Want::Refused,
    );
    add(
        "IEND with data",
        join(&[h.clone(), d.clone(), chunk(b"IEND", b"x")]),
        Want::Refused,
    );
    add(
        "zlib header wrong",
        join(&[h.clone(), chunk(b"IDAT", &[0x78, 0x00, 1, 2, 3]), e.clone()]),
        Want::Refused,
    );
    v
}

#[test]
fn hand_made_streams() {
    let cases = hand_cases();
    let (mut pass, mut fail) = (0usize, 0usize);
    for (name, bytes, want) in &cases {
        let got = outcome(bytes);
        if got == *want {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            println!("  {name}: wanted {want:?}, got {got:?}");
        }
    }
    report(
        "PNG by hand: chunk grammar, refusals, listed choices",
        pass,
        0,
        fail,
        cases.len(),
    );
    assert_eq!(fail, 0);
}

// ------------------------------------------------------------ APNG by hand

fn actl(frames: u32) -> Vec<u8> {
    let mut d = frames.to_be_bytes().to_vec();
    d.extend_from_slice(&0u32.to_be_bytes());
    chunk(b"acTL", &d)
}

fn spec(x: u32, y: u32, w: u32, h: u32, dispose: u8, blend: u8) -> FrameSpec {
    let mut img = tiny();
    img.w = w;
    img.h = h;
    img.samples = vec![200; us(w).saturating_mul(us(h))];
    FrameSpec {
        x,
        y,
        img,
        delay: (1, 10),
        dispose,
        blend,
    }
}

fn fdat_of(seq: u32, f: &FrameSpec) -> Vec<u8> {
    let mut d = seq.to_be_bytes().to_vec();
    d.extend(zlib_stored(&common::scanlines(&f.img)));
    chunk(b"fdAT", &d)
}

fn apng_cases() -> Vec<(String, Vec<u8>, Want)> {
    let (h, d, e) = parts();
    let full = spec(0, 0, 2, 2, 0, 0);
    let small = spec(1, 1, 1, 1, 0, 0);
    let mut v: Vec<(String, Vec<u8>, Want)> = Vec::new();
    let mut add = |name: &str, chunks: &[Vec<u8>], want: Want| {
        v.push((format!("APNG {name}"), join(chunks), want));
    };
    // 4.9.1: the default image is the first frame if an fcTL comes before IDAT.
    add(
        "default image hidden",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &small),
            fdat_of(1, &small),
            e.clone(),
        ],
        Want::Frames(2),
    );
    add(
        "default image animated",
        &[
            h.clone(),
            actl(2),
            fctl(0, &full),
            d.clone(),
            fctl(1, &small),
            fdat_of(2, &small),
            e.clone(),
        ],
        Want::Frames(2),
    );
    add(
        "fewer frames than acTL says",
        &[
            h.clone(),
            actl(3),
            fctl(0, &full),
            d.clone(),
            fctl(1, &small),
            fdat_of(2, &small),
            e.clone(),
        ],
        Want::Frames(2),
    );
    add(
        "more fcTL than acTL says",
        &[
            h.clone(),
            actl(1),
            fctl(0, &full),
            d.clone(),
            fctl(1, &small),
            fdat_of(2, &small),
            e.clone(),
        ],
        Want::Refused,
    );
    // 4.9.2, 11.3.6.2, 11.3.6.3: sequence numbers.
    add(
        "fcTL sequence starts at 1",
        &[h.clone(), actl(2), fctl(1, &full), d.clone(), e.clone()],
        Want::Refused,
    );
    add(
        "fdAT sequence out of order",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &small),
            fdat_of(2, &small),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "fcTL sequence repeated",
        &[
            h.clone(),
            actl(2),
            fctl(0, &full),
            d.clone(),
            fctl(0, &small),
            fdat_of(1, &small),
            e.clone(),
        ],
        Want::Refused,
    );
    // 11.3.6.1: acTL before IDAT, once, at least one frame, 8 bytes.
    add(
        "acTL after IDAT",
        &[h.clone(), d.clone(), actl(1), e.clone()],
        Want::Refused,
    );
    add(
        "acTL twice",
        &[h.clone(), actl(1), actl(1), d.clone(), e.clone()],
        Want::Refused,
    );
    add(
        "acTL of 0 frames",
        &[h.clone(), actl(0), d.clone(), e.clone()],
        Want::Refused,
    );
    add(
        "acTL of 7 bytes",
        &[
            h.clone(),
            chunk(b"acTL", &[0, 0, 0, 1, 0, 0, 0]),
            d.clone(),
            e.clone(),
        ],
        Want::Refused,
    );
    // 11.3.6.2: the frame is inside the canvas and not empty; the default
    // image's covers the canvas; dispose_op is 0 to 2 and blend_op 0 or 1.
    add(
        "frame outside the canvas",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &spec(1, 1, 2, 1, 0, 0)),
            fdat_of(1, &spec(1, 1, 2, 1, 0, 0)),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "frame of width 0",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &spec(0, 0, 0, 1, 0, 0)),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "default fcTL not the canvas",
        &[h.clone(), actl(2), fctl(0, &small), d.clone(), e.clone()],
        Want::Refused,
    );
    add(
        "dispose_op 3",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &spec(0, 0, 1, 1, 3, 0)),
            fdat_of(1, &small),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "blend_op 2",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &spec(0, 0, 1, 1, 0, 2)),
            fdat_of(1, &small),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "fcTL of 25 bytes",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            chunk(b"fcTL", &[0; 25]),
            e.clone(),
        ],
        Want::Refused,
    );
    // A frame needs its data.
    add(
        "fcTL without fdAT",
        &[h.clone(), actl(1), d.clone(), fctl(0, &small), e.clone()],
        Want::Refused,
    );
    add(
        "two fcTL in a row",
        &[
            h.clone(),
            actl(2),
            d.clone(),
            fctl(0, &small),
            fctl(1, &small),
            fdat_of(2, &small),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "fdAT of 4 bytes",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &small),
            chunk(b"fdAT", &1u32.to_be_bytes()),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "fdAT of 3 bytes",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &small),
            chunk(b"fdAT", &[0, 0, 0]),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "fdAT before IDAT",
        &[
            h.clone(),
            actl(1),
            chunk(b"fdAT", &[0, 0, 0, 0, 1]),
            d.clone(),
            e.clone(),
        ],
        Want::Refused,
    );
    add(
        "fdAT with no fcTL",
        &[h.clone(), actl(1), d.clone(), fdat_of(0, &small), e.clone()],
        Want::Refused,
    );
    // Without an acTL the animation chunks are not meaningful and are skipped.
    add(
        "fcTL and fdAT without acTL",
        &[
            h.clone(),
            fctl(0, &full),
            d.clone(),
            fctl(1, &small),
            fdat_of(2, &small),
            e.clone(),
        ],
        Want::Frames(1),
    );
    // A frame's data cut off by the next chunk.
    let half = zlib_stored(&common::scanlines(&small.img));
    let mut cut = 0u32.to_be_bytes().to_vec();
    cut.extend_from_slice(half.get(..3).unwrap_or(&[]));
    add(
        "frame data cut by IEND",
        &[
            h.clone(),
            actl(1),
            d.clone(),
            fctl(0, &small),
            chunk(b"fdAT", &{
                let mut c = 1u32.to_be_bytes().to_vec();
                c.extend_from_slice(half.get(..3).unwrap_or(&[]));
                c
            }),
            e.clone(),
        ],
        Want::Refused,
    );
    let _ = cut;
    v
}

#[test]
fn apng_by_hand() {
    let cases = apng_cases();
    let (mut pass, mut fail) = (0usize, 0usize);
    for (name, bytes, want) in &cases {
        let got = outcome(bytes);
        if got == *want {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            println!("  {name}: wanted {want:?}, got {got:?}");
        }
    }
    report(
        "APNG by hand: acTL, fcTL, fdAT rules and refusals",
        pass,
        0,
        fail,
        cases.len(),
    );
    assert_eq!(fail, 0);
}

// ---------------------------------------------------------- listed choices

/// The RGBA8 of every pixel of a stream's first frame.
fn pixels_of(bytes: &[u8]) -> Vec<[u8; 4]> {
    let d = decode(bytes, 3, false).unwrap_or_else(|e| Decoded {
        width: 0,
        height: 0,
        frames: Vec::new(),
        end: End::Error(e),
    });
    d.frames
        .first()
        .map(|(_, p)| {
            p.chunks(4)
                .map(|c| [at(c, 0), at(c, 1), at(c, 2), at(c, 3)])
                .collect()
        })
        .unwrap_or_default()
}

fn pic(ct: u8, depth: u8, samples: &[u16], palette: &[u8], trns: Option<Vec<u8>>) -> Vec<u8> {
    let mut img = tiny();
    img.ct = ct;
    img.depth = depth;
    img.w =
        u32::try_from(samples.len().checked_div(common::channels(ct)).unwrap_or(1)).unwrap_or(1);
    img.h = 1;
    img.samples = samples.to_vec();
    img.palette = palette.to_vec();
    img.trns = trns;
    png_bytes(&img)
}

#[test]
fn listed_choices() {
    let mut fail = 0usize;
    let mut total = 0usize;
    let mut check = |name: &str, got: Vec<[u8; 4]>, want: &[[u8; 4]]| {
        total = total.saturating_add(1);
        if got != want {
            fail = fail.saturating_add(1);
            println!("  {name}: wanted {want:?}, got {got:?}");
        }
    };
    // 13.12 (listed): 1, 2 and 4-bit samples scale by 255 / (2^depth - 1).
    check(
        "gray 1",
        pixels_of(&pic(0, 1, &[0, 1], &[], None)),
        &[[0, 0, 0, 255], [255, 255, 255, 255]],
    );
    check(
        "gray 2",
        pixels_of(&pic(0, 2, &[0, 1, 2, 3], &[], None)),
        &[
            [0, 0, 0, 255],
            [85, 85, 85, 255],
            [170, 170, 170, 255],
            [255, 255, 255, 255],
        ],
    );
    check(
        "gray 4",
        pixels_of(&pic(0, 4, &[0, 5, 15], &[], None)),
        &[[0, 0, 0, 255], [85, 85, 85, 255], [255, 255, 255, 255]],
    );
    // 13.12 (listed): 16 bits are reduced to the high byte.
    check(
        "gray 16",
        pixels_of(&pic(0, 16, &[0x1234, 0xFFFF, 0x00FF], &[], None)),
        &[
            [0x12, 0x12, 0x12, 255],
            [255, 255, 255, 255],
            [0, 0, 0, 255],
        ],
    );
    check(
        "rgb 16",
        pixels_of(&pic(2, 16, &[0x1234, 0x5678, 0x9ABC], &[], None)),
        &[[0x12, 0x56, 0x9A, 255]],
    );
    check(
        "rgba 16",
        pixels_of(&pic(6, 16, &[0x1234, 0x5678, 0x9ABC, 0xDEF0], &[], None)),
        &[[0x12, 0x56, 0x9A, 0xDE]],
    );
    check(
        "gray alpha 8",
        pixels_of(&pic(4, 8, &[7, 9, 8, 255], &[], None)),
        &[[7, 7, 7, 9], [8, 8, 8, 255]],
    );
    // 11.3.1 (listed): the transparent colour is compared with the full
    // 16-bit samples; below 16 bits it is the low byte of the chunk.
    check(
        "tRNS gray 16 full compare",
        pixels_of(&pic(0, 16, &[0x1234, 0x1235], &[], Some(vec![0x12, 0x34]))),
        &[[0x12, 0x12, 0x12, 0], [0x12, 0x12, 0x12, 255]],
    );
    check(
        "tRNS rgb 16",
        pixels_of(&pic(
            2,
            16,
            &[1, 2, 3, 1, 2, 4],
            &[],
            Some(vec![0, 1, 0, 2, 0, 3]),
        )),
        &[[0, 0, 0, 0], [0, 0, 0, 255]],
    );
    check(
        "tRNS gray 8 low byte",
        pixels_of(&pic(0, 8, &[10, 11], &[], Some(vec![0x01, 10]))),
        &[[10, 10, 10, 0], [11, 11, 11, 255]],
    );
    check(
        "tRNS gray 2",
        pixels_of(&pic(0, 2, &[1, 2], &[], Some(vec![0, 2]))),
        &[[85, 85, 85, 255], [170, 170, 170, 0]],
    );
    // 11.2.2 (listed): an index past the palette is opaque black; tRNS covers the first entries.
    check(
        "palette and tRNS",
        pixels_of(&pic(
            3,
            8,
            &[0, 1, 2, 9],
            &[1, 2, 3, 4, 5, 6],
            Some(vec![7]),
        )),
        &[[1, 2, 3, 7], [4, 5, 6, 255], [0, 0, 0, 255], [0, 0, 0, 255]],
    );
    check(
        "palette of 1 bit",
        pixels_of(&pic(3, 1, &[1, 0], &[10, 20, 30, 40, 50, 60], None)),
        &[[40, 50, 60, 255], [10, 20, 30, 255]],
    );
    // 4.9 (listed rounding): OVER.
    use clazel_png::pixel::over;
    total = total.saturating_add(4);
    for (src, dst, want) in [
        ([255, 0, 0, 128], [0, 0, 255, 255], [128, 0, 127, 255]),
        ([255, 0, 0, 128], [0, 0, 0, 0], [255, 0, 0, 128]),
        ([10, 20, 30, 0], [1, 2, 3, 4], [1, 2, 3, 4]),
        ([10, 20, 30, 255], [1, 2, 3, 4], [10, 20, 30, 255]),
    ] {
        if over(src, dst) != want {
            fail = fail.saturating_add(1);
            println!(
                "  over {src:?} {dst:?}: wanted {want:?}, got {:?}",
                over(src, dst)
            );
        }
    }
    report(
        "PNG listed choices: scaling, reduction, tRNS, palette, OVER",
        total.saturating_sub(fail),
        0,
        fail,
        total,
    );
    assert_eq!(fail, 0);
}

// ----------------------------------------------------------------- limits

#[test]
fn size_limits() {
    use clazel_image_shape::{ConfigStatus, Decoder};
    let head = |w: u32, h: u32| {
        let mut v = common::SIG.to_vec();
        v.extend(chunk(b"IHDR", &{
            let mut d = w.to_be_bytes().to_vec();
            d.extend_from_slice(&h.to_be_bytes());
            d.extend_from_slice(&[8, 0, 0, 0, 0]);
            d
        }));
        v
    };
    let config = |w: u32, h: u32| common::Dec::decode_config(&head(w, h));
    // 6.0(j): at most 2^14 on a side and 2^26 pixels.
    assert!(matches!(config(16384, 1), Ok(ConfigStatus::Ready(_))));
    assert!(matches!(config(1, 16384), Ok(ConfigStatus::Ready(_))));
    assert!(config(16385, 1).is_err());
    assert!(config(1, 16385).is_err());
    assert!(config(16384, 4097).is_err());
    assert!(matches!(config(16384, 4096), Ok(ConfigStatus::Ready(_))));
    assert!(config(0, 1).is_err());
    assert!(config(1, 0).is_err());
    assert!(config(0x8000_0000, 1).is_err());
    // A prefix that is a valid start is `NeedMore`, a wrong one an error.
    let full = head(5, 5);
    for n in 0..full.len() {
        let r = common::Dec::decode_config(full.get(..n).unwrap_or(&[]));
        assert!(
            matches!(r, Ok(ConfigStatus::NeedMore)) || n >= 24,
            "prefix of {n}"
        );
    }
    assert!(common::Dec::decode_config(b"GIF89a").is_err());
    assert!(
        common::Dec::decode_config(&[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0, 0, 0, 12])
            .is_err()
    );
    // The widest and tallest images decode, exactly as the reference does.
    for (w, h) in [(16384u32, 1u32), (1, 16384), (300, 200)] {
        let mut rng = Rng(7);
        let mut img = random_img(&mut rng, w, h, 2, 16, w == 300, false);
        img.filters = vec![1, 2, 3, 4, 0];
        let bytes = png_bytes(&img);
        let ours = decode(&bytes, 4096, false);
        let r = reference(&bytes);
        assert!(
            ours.is_ok() && r.is_ok(),
            "{w}x{h}: {:?} {:?}",
            ours.as_ref().err(),
            r.as_ref().err()
        );
        if let (Ok(o), Ok(r)) = (ours, r) {
            assert_eq!(o.end, End::Iend);
            assert_eq!(compare(&o, &r), Ok(()));
        }
    }
}

/// Every prefix of a stream is a valid start of it: never an `Iend` (until
/// the whole stream), never a panic, the frames only from complete data.
#[test]
fn every_prefix() {
    let mut rng = Rng(11);
    let img = random_img(&mut rng, 5, 4, 6, 8, true, false);
    let base = random_img(&mut rng, 4, 4, 6, 8, false, false);
    let rgba_frame = |rng: &mut Rng, x: u32, y: u32, w: u32, dispose: u8| FrameSpec {
        x,
        y,
        img: random_img(rng, w, w, 6, 8, false, false),
        delay: (1, 10),
        dispose,
        blend: 1,
    };
    let first = rgba_frame(&mut rng, 0, 0, 4, 1);
    let second = rgba_frame(&mut rng, 1, 1, 2, 2);
    let streams = [png_bytes(&img), apng_bytes(&base, Some(&first), &[second])];
    let mut cuts = 0usize;
    for bytes in &streams {
        let step = if MIRI { 9 } else { 1 };
        for n in (0..bytes.len()).step_by(step) {
            let part = bytes.get(..n).unwrap_or(&[]);
            if let Ok(d) = decode(part, 1_000_000, false) {
                assert_ne!(d.end, End::Iend, "a prefix of {n} bytes reached IEND");
                cuts = cuts.saturating_add(1);
            }
        }
        assert_eq!(
            decode(bytes, 1_000_000, false).map(|d| d.end),
            Ok(End::Iend)
        );
    }
    assert!(cuts > 0);
}
