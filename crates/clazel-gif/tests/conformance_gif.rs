//! Conformance of `clazel-gif` (phase-6.md item 6.7) on Wuffs' GIF test
//! data, `tests/data/wuffs-gif/` and `tests/data/wuffs-gif-artificial/`
//! (Wuffs commit `b36a81d`, through the tables `cargo xtask testdata`
//! generates), against the `gif` crate 0.14.2 as the reference engine.
//!
//! Four suites, each printing a `clazel-conformance:` line
//! (`xtask/src/conformance.rs`); a unit is one file:
//!
//! - **differential**: both decoders read the file; a file passes when the
//!   two agree on the screen's size, on how many frames they complete, on
//!   every frame's facts (rectangle, interlacing, delay, disposal,
//!   transparent index) and on **every frame's composited RGBA, exactly**,
//!   and on how the stream ends (trailer or error). The `gif` crate gives
//!   each frame's own pixels in RGBA; this test composites them onto a
//!   canvas itself (`reference_canvases`) with the listed choices of
//!   `clazel-gif`'s `lib.rs` (transparent black start, disposal 2 to
//!   transparent, disposal 3 from the saved canvas, clipping, a transparent
//!   pixel keeps the canvas), written separately from the decoder's code.
//!   The expected differences are listed with their reasons (`XFAIL`).
//! - **chunking**: each file through the `Decoder` interface in chunks of 1,
//!   2, 3, 7, 64, 4096 bytes, with and without empty chunks between, gives
//!   exactly what one chunk of the whole file gives (the same frames, the
//!   same canvases, the same end), with the invariant checked after every
//!   step and the canary bytes past the buffers untouched.
//! - **mutations**: many deterministic byte mutations of each file (bytes
//!   changed, truncations, deleted and repeated runs, runs overwritten) are
//!   decoded in two chunkings; none panics, the invariant holds after every
//!   step, `consumed` obeys the contract, and an error leaves the decoder
//!   spent.
//! - **GIFs by hand**: `s.gif`, the 1 by 1 transparent GIF of Hacker News's
//!   pages, and small streams for each block, disposal and interlace rule,
//!   in `src` tests and here.
//!
//! Under Miri (about 100 times slower, and unable to open files, though
//! these are embedded): the differential and chunking suites run on files
//! of at most 16 KiB with chunk sizes 1 and 4096, and the mutation suite on
//! those files with 4 mutations each (a stride of every 3rd file of the
//! rest of the list); the whole takes about a minute.

mod main_files {
    include!("generated/wuffs_gif.rs");
}
mod artificial_files {
    include!("generated/wuffs_gif_artificial.rs");
}

use clazel_gif::{Disposal, FrameInfo, Gif};
use clazel_image_shape::{Buffers, ConfigStatus, Decoder, Error, Status};

/// How a decode ended.
#[derive(Debug, Clone, PartialEq, Eq)]
enum End {
    /// The trailer.
    Trailer,
    /// An error (the frames before it were completed).
    Error(String),
    /// The input ran out.
    Truncated,
}

/// What the decoder gave for a file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Decoded {
    width: u32,
    height: u32,
    /// Each completed frame: its facts and the canvas after it.
    frames: Vec<(FrameInfo, Vec<u8>)>,
    end: End,
}

const CANARY: u8 = 0xEE;

/// Decodes `bytes` through the shared interface, in chunks of `chunk` bytes
/// (with an empty chunk between each pair if `empties`), checking the
/// invariant and the contract on every step.
fn decode(bytes: &[u8], chunk: usize, empties: bool) -> Result<Decoded, String> {
    let head = bytes.get(..bytes.len().min(10)).unwrap_or(bytes);
    let config = match Gif::decode_config(head) {
        Ok(ConfigStatus::Ready(c)) => c,
        Ok(ConfigStatus::NeedMore) => return Err("the input ends inside the header".into()),
        Err(e) => return Err(format!("{e:?}")),
    };
    // A longer prefix gives the same config.
    if let Ok(ConfigStatus::Ready(c2)) = Gif::decode_config(bytes) {
        assert_eq!(c2, config);
    }
    let plen = config.rgba_len().map_err(|e| format!("{e:?}"))?;
    let wlen = Gif::work_len(&config).map_err(|e| format!("{e:?}"))?;
    let mut pixels = vec![CANARY; plen.saturating_add(3)];
    let mut work = vec![CANARY; wlen.saturating_add(3)];
    let mut state = Gif::start(&config).map_err(|e| format!("{e:?}"))?;
    let mut frames = Vec::new();
    let mut end = End::Truncated;
    {
        let mut buffers =
            Buffers::new(&config, wlen, &mut pixels, &mut work).map_err(|e| format!("{e:?}"))?;
        assert!(state.inv(&buffers));
        let mut pos = 0usize;
        let mut spent = false;
        let mut empty_turn = false;
        'feed: while pos < bytes.len() {
            let take = if empties && empty_turn {
                0
            } else {
                chunk.min(bytes.len().saturating_sub(pos))
            };
            empty_turn = !empty_turn;
            let part = bytes
                .get(pos..pos.saturating_add(take))
                .ok_or("chunk out of range")?;
            let result = state.step(part, &mut buffers);
            assert!(state.inv(&buffers), "invariant lost at byte {pos}");
            match result {
                Ok(step) => {
                    assert!(step.consumed <= part.len());
                    match step.status {
                        Status::NeedMore => {
                            assert_eq!(step.consumed, part.len());
                            pos = pos.saturating_add(take);
                        }
                        Status::FrameDone => {
                            let info = *state.frame().ok_or("FrameDone without a frame")?;
                            frames.push((info, buffers.pixels.to_vec()));
                            pos = pos.saturating_add(step.consumed);
                        }
                    }
                }
                Err(Error::NoMoreFrames) => {
                    end = End::Trailer;
                    break 'feed;
                }
                Err(e) => {
                    end = End::Error(format!("{e:?}"));
                    spent = true;
                    break 'feed;
                }
            }
        }
        if spent {
            // An errored decoder is spent, and says so.
            assert_eq!(state.step(&[0], &mut buffers), Err(Error::Spent));
            assert!(state.inv(&buffers));
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
    Ok(Decoded {
        width: config.width(),
        height: config.height(),
        frames,
        end,
    })
}

/// What the reference decoder gave.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Reference {
    width: u32,
    height: u32,
    frames: Vec<(FrameInfo, Vec<u8>)>,
    end: End,
}

fn disposal_of(d: gif::DisposalMethod) -> Disposal {
    match d {
        gif::DisposalMethod::Any => Disposal::None,
        gif::DisposalMethod::Keep => Disposal::Keep,
        gif::DisposalMethod::Background => Disposal::Background,
        gif::DisposalMethod::Previous => Disposal::Previous,
    }
}

/// Reads `bytes` with the `gif` crate, compositing each frame's RGBA onto a
/// canvas: the listed choices of `clazel-gif`, written here again.
fn reference(bytes: &[u8]) -> Result<Reference, String> {
    let mut options = gif::DecodeOptions::new();
    options.set_color_output(gif::ColorOutput::RGBA);
    let mut decoder = options.read_info(bytes).map_err(|e| format!("{e}"))?;
    let (w, h) = (usize::from(decoder.width()), usize::from(decoder.height()));
    let mut canvas = vec![0u8; w.saturating_mul(h).saturating_mul(4)];
    let mut saved: Option<Vec<u8>> = None;
    let mut previous: Option<FrameInfo> = None;
    let mut frames = Vec::new();
    let end = loop {
        match decoder.read_next_frame() {
            Ok(Some(frame)) => {
                let info = FrameInfo {
                    left: frame.left,
                    top: frame.top,
                    width: frame.width,
                    height: frame.height,
                    interlaced: frame.interlaced,
                    delay_cs: frame.delay,
                    disposal: disposal_of(frame.dispose),
                    transparent: frame.transparent,
                };
                // The previous frame's disposal first.
                if let Some(p) = previous {
                    match p.disposal {
                        Disposal::Background => {
                            for y in usize::from(p.top)
                                ..usize::from(p.top).saturating_add(usize::from(p.height))
                            {
                                for x in usize::from(p.left)
                                    ..usize::from(p.left).saturating_add(usize::from(p.width))
                                {
                                    if x < w && y < h {
                                        let at =
                                            y.saturating_mul(w).saturating_add(x).saturating_mul(4);
                                        if let Some(px) = canvas.get_mut(at..at.saturating_add(4)) {
                                            px.fill(0);
                                        }
                                    }
                                }
                            }
                        }
                        Disposal::Previous => {
                            if let Some(s) = saved.take() {
                                canvas = s;
                            }
                        }
                        Disposal::None | Disposal::Keep => {}
                    }
                }
                saved = (info.disposal == Disposal::Previous).then(|| canvas.clone());
                // This frame's pixels, clipped, a transparent one skipped.
                let (fw, fh) = (usize::from(frame.width), usize::from(frame.height));
                for fy in 0..fh {
                    for fx in 0..fw {
                        let x = usize::from(frame.left).saturating_add(fx);
                        let y = usize::from(frame.top).saturating_add(fy);
                        if x >= w || y >= h {
                            continue;
                        }
                        let from = fy.saturating_mul(fw).saturating_add(fx).saturating_mul(4);
                        let src = frame
                            .buffer
                            .get(from..from.saturating_add(4))
                            .ok_or("short frame")?;
                        if src.get(3) == Some(&0) {
                            continue;
                        }
                        let at = y.saturating_mul(w).saturating_add(x).saturating_mul(4);
                        canvas
                            .get_mut(at..at.saturating_add(4))
                            .ok_or("outside canvas")?
                            .copy_from_slice(src);
                    }
                }
                previous = Some(info);
                frames.push((info, canvas.clone()));
            }
            Ok(None) => break End::Trailer,
            Err(e) => break End::Error(format!("{e}")),
        }
    };
    Ok(Reference {
        width: u32::from(decoder.width()),
        height: u32::from(decoder.height()),
        frames,
        end,
    })
}

/// Files whose outcome legitimately differs from the `gif` crate's, with
/// the reason. Each is checked to differ in the way described (a file
/// listed here that starts to agree fails the suite, so the list stays
/// true).
const XFAIL: &[(&str, &str)] = &[
    (
        "empty-palette.gif",
        "its second frame has no colour table at all: the gif crate errors, we draw nothing for it (listed choice 4)",
    ),
    (
        "no-frames.gif",
        "the trailer comes before any frame: the gif crate refuses the file at once, we start and report no frame (the same broken image to clazel-image)",
    ),
    (
        "pixel-data-none.gif",
        "a frame with no image data: the gif crate errors (image truncated), we keep the frame as the canvas had it (listed choice 6)",
    ),
    (
        "pixel-data-not-enough.gif",
        "a frame with too little image data: the gif crate errors, we keep the pixels decoded (listed choice 6)",
    ),
    (
        "pixel-data-too-much-bad-lzw.gif",
        "invalid LZW after the last pixel: the gif crate delivers the frame and then errors, we stop reading codes once the frame is full and skip the rest of the data (listed choice 6)",
    ),
    (
        "zero-width-frame.gif",
        "a frame of width 0: the gif crate errors (odd-sized buffer), we draw nothing for it (listed choice 3)",
    ),
];

fn xfail_reason(file: &str) -> Option<&'static str> {
    XFAIL.iter().find(|(f, _)| *f == file).map(|(_, r)| *r)
}

/// The small files, for Miri.
const MIRI_MAX_BYTES: usize = 16 * 1024;

fn all_files() -> Vec<(&'static str, &'static [u8])> {
    let mut v: Vec<(&str, &[u8])> = Vec::new();
    for c in main_files::FILES {
        assert_eq!(c.sha256.len(), 64);
        v.push((c.file, c.bytes));
    }
    for c in artificial_files::FILES {
        assert_eq!(c.sha256.len(), 64);
        v.push((c.file, c.bytes));
    }
    if cfg!(miri) {
        v.retain(|(_, b)| b.len() <= MIRI_MAX_BYTES);
    }
    v
}

fn describe(d: &Decoded) -> String {
    format!(
        "{}x{}, {} frames, {:?}",
        d.width,
        d.height,
        d.frames.len(),
        d.end
    )
}

/// A frame's facts as the two decoders can be compared: the `gif` crate
/// de-interlaces for us and then reports the frame as not interlaced, so
/// the flag is not compared (a test below checks ours on both kinds of
/// file), and its default disposal for a frame with no control extension,
/// `Keep`, means what our `None` does (both leave the frame in place).
fn comparable(mut info: FrameInfo) -> FrameInfo {
    info.interlaced = false;
    if info.disposal == Disposal::Keep {
        info.disposal = Disposal::None;
    }
    info
}

/// Whether two ends are the same: a stream that ends inside a frame is
/// our `Truncated` (the caller says it, the decoder only runs out of
/// bytes) and the `gif` crate's unexpected-end error.
fn same_end(ours: &End, theirs: &End) -> bool {
    match (ours, theirs) {
        (End::Truncated, End::Error(why)) => {
            why.contains("End of File") || why.contains("truncated")
        }
        _ => ours == theirs,
    }
}

/// What differs between the two decoders on a file, if anything.
fn differences(file: &str, bytes: &[u8]) -> Option<String> {
    let ours = match decode(bytes, usize::MAX, false) {
        Ok(d) => d,
        Err(e) => return Some(format!("{file}: ours failed to start: {e}")),
    };
    let theirs = match reference(bytes) {
        Ok(r) => r,
        Err(e) => return Some(format!("{file}: reference failed to start: {e}")),
    };
    if (ours.width, ours.height) != (theirs.width, theirs.height) {
        return Some(format!(
            "{file}: screen {}x{} vs {}x{}",
            ours.width, ours.height, theirs.width, theirs.height
        ));
    }
    if ours.frames.len() != theirs.frames.len() {
        return Some(format!(
            "{file}: {} frames vs the reference's {} (ours: {:?}; theirs: {:?})",
            ours.frames.len(),
            theirs.frames.len(),
            ours.end,
            theirs.end
        ));
    }
    for (i, (a, b)) in ours.frames.iter().zip(&theirs.frames).enumerate() {
        if comparable(a.0) != comparable(b.0) {
            return Some(format!("{file}: frame {i} facts {:?} vs {:?}", a.0, b.0));
        }
        if a.1 != b.1 {
            let at = a.1.iter().zip(&b.1).position(|(x, y)| x != y);
            return Some(format!(
                "{file}: frame {i} canvas differs, first at byte {at:?}"
            ));
        }
    }
    if !same_end(&ours.end, &theirs.end) {
        return Some(format!(
            "{file}: ends {:?} vs the reference's {:?}",
            ours.end, theirs.end
        ));
    }
    None
}

fn suite(name: &str, files: &[(&'static str, &'static [u8])]) {
    let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
    let mut notes = Vec::new();
    for (file, bytes) in files {
        let diff = differences(file, bytes);
        match (diff, xfail_reason(file)) {
            (None, None) => {
                pass = pass.saturating_add(1);
                if let Ok(d) = decode(bytes, usize::MAX, false) {
                    println!("  {file}: agrees ({})", describe(&d));
                }
            }
            (Some(d), Some(why)) => {
                xfail = xfail.saturating_add(1);
                println!("  {file}: expected difference ({why}): {d}");
            }
            (Some(d), None) => {
                fail = fail.saturating_add(1);
                notes.push(d);
            }
            (None, Some(why)) => {
                fail = fail.saturating_add(1);
                notes.push(format!("{file}: listed as different ({why}) but agrees"));
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"{name}\" pass={pass} xfail={xfail} fail={fail} total={}",
        files.len()
    );
    assert!(notes.is_empty(), "{}", notes.join("\n"));
}

#[test]
fn differential_wuffs_gif() {
    let files: Vec<_> = all_files()
        .into_iter()
        .filter(|(f, _)| main_files::FILES.iter().any(|c| c.file == *f))
        .collect();
    suite("Wuffs GIF files vs gif 0.14.2", &files);
}

#[test]
fn differential_wuffs_gif_artificial() {
    let files: Vec<_> = all_files()
        .into_iter()
        .filter(|(f, _)| artificial_files::FILES.iter().any(|c| c.file == *f))
        .collect();
    suite("Wuffs artificial GIF files vs gif 0.14.2", &files);
}

#[test]
fn chunking_changes_nothing() {
    let sizes: &[usize] = if cfg!(miri) {
        &[1, 4096]
    } else {
        &[1, 2, 3, 7, 64, 4096]
    };
    let files = all_files();
    let (mut pass, mut fail) = (0usize, 0usize);
    for (file, bytes) in &files {
        let whole = decode(bytes, usize::MAX, false);
        let mut ok = whole.is_ok();
        for &size in sizes {
            for empties in [false, true] {
                if cfg!(miri) && empties {
                    continue;
                }
                let got = decode(bytes, size, empties);
                if got != whole {
                    println!("  {file}: chunk {size} (empties {empties}) differs from the whole");
                    ok = false;
                }
            }
        }
        if ok {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
        }
    }
    println!(
        "clazel-conformance: suite=\"GIF chunking: every file at chunk sizes 1 to 4096\" pass={pass} xfail=0 fail={fail} total={}",
        files.len()
    );
    assert_eq!(fail, 0);
}

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

/// One mutation of `bytes`, chosen by `rng`.
fn mutate(bytes: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = bytes.to_vec();
    for _ in 0..=rng.below(3) {
        let len = v.len().max(1);
        let at = rng.below(len);
        match rng.below(7) {
            0 => {
                if let Some(b) = v.get_mut(at) {
                    *b = u8::try_from(rng.below(256)).unwrap_or(0);
                }
            }
            1 => {
                if let Some(b) = v.get_mut(at) {
                    *b = if rng.below(2) == 0 { 0 } else { 255 };
                }
            }
            2 => v.truncate(at),
            3 => {
                let n = 1usize.saturating_add(rng.below(16));
                let end = at.saturating_add(n).min(v.len());
                if at < end {
                    v.drain(at..end);
                }
            }
            4 => {
                let n = 1usize.saturating_add(rng.below(16));
                let end = at.saturating_add(n).min(v.len());
                if let Some(run) = v.get(at..end).map(<[u8]>::to_vec) {
                    for (i, b) in run.iter().enumerate() {
                        v.insert(at.saturating_add(i), *b);
                    }
                }
            }
            5 => {
                for i in 0..4 {
                    if let Some(b) = v.get_mut(at.saturating_add(i)) {
                        *b = u8::try_from(rng.below(256)).unwrap_or(0);
                    }
                }
            }
            _ => {
                // A bit flip, the commonest corruption.
                if let Some(b) = v.get_mut(at) {
                    *b ^= 1 << rng.below(8);
                }
            }
        }
    }
    v
}

#[test]
fn mutated_files_never_panic() {
    let files = all_files();
    let mut pass = 0usize;
    let mut mutants = 0usize;
    let mut errors = 0usize;
    let mut frames = 0usize;
    for (n, (file, bytes)) in files.iter().enumerate() {
        // About two million bytes of mutants per file, at least 8 of them.
        let count = if cfg!(miri) {
            4
        } else {
            (2_000_000usize / bytes.len().max(1)).clamp(8, 400)
        };
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ (u64::try_from(n).unwrap_or(0) << 32) ^ 1);
        for i in 0..count {
            let mutant = mutate(bytes, &mut rng);
            // Two chunkings: one chunk, and 7 bytes (or 4096 on big ones).
            let small = if mutant.len() > 100_000 { 4096 } else { 7 };
            let a = decode(&mutant, usize::MAX, false);
            let b = decode(&mutant, small, i % 2 == 0);
            assert_eq!(a, b, "{file} mutant {i}: chunking changed the result");
            mutants = mutants.saturating_add(1);
            if let Ok(d) = a {
                frames = frames.saturating_add(d.frames.len());
                if matches!(d.end, End::Error(_)) {
                    errors = errors.saturating_add(1);
                }
            }
        }
        pass = pass.saturating_add(1);
    }
    println!("  {mutants} mutants, {errors} ended in an error, {frames} frames completed");
    println!(
        "clazel-conformance: suite=\"GIF mutations: no panic, the invariant kept\" pass={pass} xfail=0 fail=0 total={}",
        files.len()
    );
}

/// `s.gif`, the 1 by 1 GIF Hacker News uses for spacing: 43 bytes, global
/// colour table of 2 entries, a Graphic Control Extension with transparency
/// index 0, one 1 by 1 frame.
const S_GIF: &[u8] = &[
    0x47, 0x49, 0x46, 0x38, 0x39, 0x61, 0x01, 0x00, 0x01, 0x00, 0x80, 0x00, 0x00, 0xff, 0xff, 0xff,
    0x00, 0x00, 0x00, 0x21, 0xf9, 0x04, 0x01, 0x00, 0x00, 0x00, 0x00, 0x2c, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x01, 0x00, 0x00, 0x02, 0x02, 0x44, 0x01, 0x00, 0x3b,
];

#[test]
fn s_gif_is_one_transparent_pixel() -> Result<(), String> {
    let d = decode(S_GIF, usize::MAX, false)?;
    assert_eq!((d.width, d.height), (1, 1));
    assert_eq!(d.end, End::Trailer);
    assert_eq!(d.frames.len(), 1);
    let (info, canvas) = d.frames.first().ok_or("no frame")?;
    assert_eq!(info.transparent, Some(0));
    assert_eq!(canvas, &[0, 0, 0, 0]);
    // The same file at every chunk size.
    for size in 1..=S_GIF.len() {
        assert_eq!(decode(S_GIF, size, true)?, d);
    }
    // Without the transparency flag, index 0 is the first colour of the
    // table, opaque white.
    let mut opaque = S_GIF.to_vec();
    if let Some(flags) = opaque.get_mut(19 + 3) {
        *flags = 0;
    }
    let d = decode(&opaque, usize::MAX, false)?;
    assert_eq!(
        d.frames.first().map(|f| f.1.clone()),
        Some(vec![255, 255, 255, 255])
    );
    // The reference agrees on both.
    assert_eq!(differences("s.gif", S_GIF), None);
    assert_eq!(differences("s-opaque.gif", &opaque), None);
    Ok(())
}

/// Our decoder reports a frame's interlacing as the descriptor says.
#[test]
fn interlacing_is_reported() -> Result<(), String> {
    let pick = |name: &str| {
        main_files::FILES
            .iter()
            .find(|c| c.file == name)
            .map(|c| c.bytes)
            .ok_or(format!("{name} is not vendored"))
    };
    for (name, interlaced) in [
        ("hippopotamus.interlaced.gif", true),
        ("hippopotamus.regular.gif", false),
    ] {
        let d = decode(pick(name)?, usize::MAX, false)?;
        assert_eq!(d.frames.first().map(|f| f.0.interlaced), Some(interlaced));
    }
    // The same picture, interlaced or not (the vendored files differ only
    // in the order of rows).
    let a = decode(pick("hippopotamus.interlaced.gif")?, usize::MAX, false)?;
    let b = decode(pick("hippopotamus.regular.gif")?, usize::MAX, false)?;
    assert_eq!(
        a.frames.first().map(|f| &f.1),
        b.frames.first().map(|f| &f.1)
    );
    Ok(())
}

// ---------------------------------------------------------------------
// GIFs made by hand: a small writer (with a real LZW encoder) and cases
// for each rule of the decoder, with the canvas after every frame written
// out by hand.
// ---------------------------------------------------------------------

use std::collections::HashMap;

/// How the encoder treats a full table.
#[derive(Clone, Copy)]
enum Full {
    /// Emit a clear code and start over (what encoders do).
    Clear,
    /// Keep going with the table as it is until the end (what a decoder
    /// must accept: the deferred clear of `lzw.rs`).
    Deferred,
}

/// GIF's LZW, greedy, from first principles (GIF89a Appendix F).
fn lzw_encode(indices: &[u8], min: u8, full: Full) -> Vec<u8> {
    struct Bits {
        out: Vec<u8>,
        acc: u32,
        n: u32,
    }
    impl Bits {
        fn put(&mut self, code: u16, size: u32) {
            self.acc |= u32::from(code) << self.n;
            self.n = self.n.saturating_add(size);
            while self.n >= 8 {
                self.out.push((self.acc & 0xFF) as u8);
                self.acc >>= 8;
                self.n = self.n.saturating_sub(8);
            }
        }
    }
    let clear = 1u16 << min;
    let end = clear.saturating_add(1);
    let mut bits = Bits {
        out: Vec::new(),
        acc: 0,
        n: 0,
    };
    let mut dict: HashMap<(u16, u8), u16> = HashMap::new();
    let mut next = end.saturating_add(1);
    let mut size = u32::from(min) + 1;
    bits.put(clear, size);
    let mut cur: Option<u16> = None;
    for &k in indices {
        let Some(c) = cur else {
            cur = Some(u16::from(k));
            continue;
        };
        if let Some(&d) = dict.get(&(c, k)) {
            cur = Some(d);
            continue;
        }
        bits.put(c, size);
        if next < 4096 {
            dict.insert((c, k), next);
            next = next.saturating_add(1);
            if u32::from(next) > (1 << size) && size < 12 {
                size = size.saturating_add(1);
            }
        } else if matches!(full, Full::Clear) {
            bits.put(clear, size);
            dict.clear();
            next = end.saturating_add(1);
            size = u32::from(min) + 1;
        }
        cur = Some(u16::from(k));
    }
    if let Some(c) = cur {
        bits.put(c, size);
        // The decoder adds an entry on receiving this code, and may grow its
        // code size for the end code; the encoder does the same, as encoders
        // do (giflib bumps its running code after the last one).
        if next < 4096 {
            next = next.saturating_add(1);
            if u32::from(next) > (1 << size) && size < 12 {
                size = size.saturating_add(1);
            }
        }
    }
    bits.put(end, size);
    if bits.n > 0 {
        bits.out.push((bits.acc & 0xFF) as u8);
    }
    bits.out
}

type Rgb = [u8; 3];

/// A frame to write.
#[derive(Clone)]
struct F {
    left: u16,
    top: u16,
    w: u16,
    h: u16,
    /// Row-major, picture order.
    indices: Vec<u8>,
    interlaced: bool,
    local: Option<Vec<Rgb>>,
    /// Disposal, delay, transparent index.
    gce: Option<(u8, u16, Option<u8>)>,
    full: Full,
}

impl F {
    fn solid(left: u16, top: u16, w: u16, h: u16, index: u8) -> F {
        F {
            left,
            top,
            w,
            h,
            indices: vec![index; usize::from(w).saturating_mul(usize::from(h))],
            interlaced: false,
            local: None,
            gce: None,
            full: Full::Clear,
        }
    }
    fn gce(mut self, disposal: u8, delay: u16, transparent: Option<u8>) -> F {
        self.gce = Some((disposal, delay, transparent));
        self
    }
}

enum Item {
    Frame(F),
    Raw(Vec<u8>),
}

fn table(colours: &[Rgb]) -> (u8, Vec<u8>) {
    // The packed size field N such that 2^(N+1) >= len, and the bytes.
    let mut n = 0u8;
    while (2usize << n) < colours.len() {
        n = n.saturating_add(1);
    }
    let mut bytes: Vec<u8> = colours.iter().flatten().copied().collect();
    bytes.resize((2usize << n).saturating_mul(3), 0);
    (n, bytes)
}

fn sub_blocks(data: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    for chunk in data.chunks(255) {
        out.push(chunk.len() as u8);
        out.extend_from_slice(chunk);
    }
    out.push(0);
    out
}

fn build(w: u16, h: u16, global: Option<&[Rgb]>, items: &[Item]) -> Vec<u8> {
    let mut v = b"GIF89a".to_vec();
    v.extend(w.to_le_bytes());
    v.extend(h.to_le_bytes());
    let gt = global.map(table);
    v.push(gt.as_ref().map_or(0, |(n, _)| 0x80 | n));
    v.extend([0, 0]);
    if let Some((_, bytes)) = &gt {
        v.extend(bytes);
    }
    for item in items {
        match item {
            Item::Raw(bytes) => v.extend(bytes),
            Item::Frame(f) => {
                if let Some((disposal, delay, transparent)) = f.gce {
                    v.extend([
                        0x21,
                        0xF9,
                        4,
                        (disposal << 2) | u8::from(transparent.is_some()),
                    ]);
                    v.extend(delay.to_le_bytes());
                    v.extend([transparent.unwrap_or(0), 0]);
                }
                v.push(0x2C);
                for x in [f.left, f.top, f.w, f.h] {
                    v.extend(x.to_le_bytes());
                }
                let lt = f.local.as_deref().map(table);
                v.push(
                    lt.as_ref().map_or(0, |(n, _)| 0x80 | n) | if f.interlaced { 0x40 } else { 0 },
                );
                if let Some((_, bytes)) = &lt {
                    v.extend(bytes);
                }
                // The colour count the indexes may use sets the minimum
                // code size (at least 2).
                let colours = f
                    .local
                    .as_ref()
                    .map(Vec::len)
                    .or(global.map(<[Rgb]>::len))
                    .unwrap_or(2);
                let top_index = f.indices.iter().copied().max().map_or(0, usize::from);
                let mut min = 2u8;
                while (1usize << min) < colours.max(top_index.saturating_add(1)) {
                    min = min.saturating_add(1);
                }
                // Storage order of rows.
                let h = usize::from(f.h);
                let rows: Vec<usize> = if f.interlaced {
                    [(0, 8), (4, 8), (2, 4), (1, 2)]
                        .iter()
                        .flat_map(|&(s, st)| (s..h).step_by(st))
                        .collect()
                } else {
                    (0..h).collect()
                };
                let w = usize::from(f.w);
                let mut stored = Vec::new();
                for r in rows {
                    stored.extend_from_slice(
                        f.indices
                            .get(r.saturating_mul(w)..r.saturating_add(1).saturating_mul(w))
                            .unwrap_or(&[]),
                    );
                }
                v.push(min);
                v.extend(sub_blocks(&lzw_encode(&stored, min, f.full)));
            }
        }
    }
    v.push(0x3B);
    v
}

const RED: Rgb = [255, 0, 0];
const GREEN: Rgb = [0, 255, 0];
const BLUE: Rgb = [0, 0, 255];
const BLACK: Rgb = [0, 0, 0];

fn px(c: Rgb) -> [u8; 4] {
    [c[0], c[1], c[2], 255]
}
const T: [u8; 4] = [0, 0, 0, 0];

fn canvas(pixels: &[[u8; 4]]) -> Vec<u8> {
    pixels.iter().flatten().copied().collect()
}

/// A hand-made case: the stream and the canvas after each frame.
struct Hand {
    name: String,
    bytes: Vec<u8>,
    canvases: Vec<Vec<u8>>,
}

fn hand_cases() -> Vec<Hand> {
    let pal = [RED, GREEN, BLUE, BLACK];
    let mut cases = Vec::new();
    let mut add = |name: &str, bytes: Vec<u8>, canvases: Vec<Vec<u8>>| {
        cases.push(Hand {
            name: name.to_owned(),
            bytes,
            canvases,
        });
    };
    // Disposal 2 and 3 across four frames (computed by hand in the
    // comment: R red, G green, B blue, T transparent).
    //   A (keep)             R R R R
    //   B (green 1..3, 2)    R G G R
    //   C (dispose B: clear) R T T R, blue at 0, disposal 3: B T T R
    //   D (dispose C: back)  R T T R, green at 3:              R T T G
    add(
        "disposal methods 1, 2 and 3",
        build(
            4,
            1,
            Some(&pal),
            &[
                Item::Frame(F::solid(0, 0, 4, 1, 0).gce(1, 5, None)),
                Item::Frame(F::solid(1, 0, 2, 1, 1).gce(2, 5, None)),
                Item::Frame(F::solid(0, 0, 1, 1, 2).gce(3, 5, None)),
                Item::Frame(F::solid(3, 0, 1, 1, 1)),
            ],
        ),
        vec![
            canvas(&[px(RED); 4]),
            canvas(&[px(RED), px(GREEN), px(GREEN), px(RED)]),
            canvas(&[px(BLUE), T, T, px(RED)]),
            canvas(&[px(RED), T, T, px(GREEN)]),
        ],
    );
    // A transparent index leaves the canvas as it is; index 3 is the
    // transparent colour here.
    add(
        "a transparent index keeps the canvas",
        build(
            2,
            1,
            Some(&pal),
            &[
                Item::Frame(F::solid(0, 0, 2, 1, 0)),
                Item::Frame(F {
                    indices: vec![3, 1],
                    ..F::solid(0, 0, 2, 1, 0).gce(0, 0, Some(3))
                }),
            ],
        ),
        vec![canvas(&[px(RED), px(RED)]), canvas(&[px(RED), px(GREEN)])],
    );
    // Without the flag, the same index 3 is black.
    add(
        "an index is opaque without the transparency flag",
        build(
            2,
            1,
            Some(&pal),
            &[
                Item::Frame(F::solid(0, 0, 2, 1, 0)),
                Item::Frame(F {
                    indices: vec![3, 1],
                    ..F::solid(0, 0, 2, 1, 0).gce(0, 0, None)
                }),
            ],
        ),
        vec![canvas(&[px(RED), px(RED)]), canvas(&[px(BLACK), px(GREEN)])],
    );
    // A local table replaces the global one, and there may be no global.
    add(
        "local colour tables",
        build(
            2,
            1,
            None,
            &[Item::Frame(F {
                local: Some(vec![BLUE, GREEN]),
                indices: vec![0, 1],
                ..F::solid(0, 0, 2, 1, 0)
            })],
        ),
        vec![canvas(&[px(BLUE), px(GREEN)])],
    );
    // Clipping: a frame partly or wholly outside the canvas.
    add(
        "frames outside the canvas are clipped",
        build(
            2,
            2,
            Some(&pal),
            &[
                Item::Frame(F::solid(1, 1, 3, 3, 1)),
                Item::Frame(F::solid(5, 5, 2, 2, 2)),
            ],
        ),
        vec![canvas(&[T, T, T, px(GREEN)]), canvas(&[T, T, T, px(GREEN)])],
    );
    // An index past the palette draws nothing.
    add(
        "an index past the colour table draws nothing",
        build(
            2,
            1,
            Some(&[RED, GREEN]),
            &[Item::Frame(F {
                indices: vec![1, 3],
                ..F::solid(0, 0, 2, 1, 0)
            })],
        ),
        vec![canvas(&[px(GREEN), T])],
    );
    // Extensions of every kind before and between frames are skipped.
    let mut ext = vec![0x21, 0xFE];
    ext.extend(sub_blocks(b"a comment, with two sub-blocks"));
    ext.extend([0x21, 0xFF, 11]);
    ext.extend(b"NETSCAPE2.0");
    ext.extend(sub_blocks(&[1, 0, 0]));
    ext.extend([0x21, 0x01, 12, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0]);
    ext.extend(sub_blocks(b"T"));
    add(
        "comment, application, plain text and unknown extensions",
        build(
            1,
            1,
            Some(&pal),
            &[
                Item::Raw(ext.clone()),
                Item::Frame(F::solid(0, 0, 1, 1, 2)),
                Item::Raw(ext),
            ],
        ),
        vec![canvas(&[px(BLUE)])],
    );
    // An extension with a label nobody defined, 300 bytes in two sub-blocks.
    let mut unknown = vec![0x21, 0x99];
    unknown.extend(sub_blocks(&[7; 300]));
    add(
        "an unknown extension is skipped",
        build(
            1,
            1,
            Some(&pal),
            &[Item::Raw(unknown), Item::Frame(F::solid(0, 0, 1, 1, 2))],
        ),
        vec![canvas(&[px(BLUE)])],
    );
    // Interlacing for every height from 1 to 40: row r is colour r % 4. The
    // frames are 8 wide: the gif crate 0.14.2 reports "image truncated" for
    // some interlaced frames only 3 wide (30 of the 40 heights, though the
    // same stream decodes to the expected rows here, and a twin stored in
    // order decodes there); wider ones it reads.
    for h in 1..=40u16 {
        let indices: Vec<u8> = (0..h).flat_map(|r| [(r % 4) as u8; 8]).collect();
        let expected: Vec<[u8; 4]> = (0..h)
            .flat_map(|r| [px(pal.get(usize::from(r % 4)).copied().unwrap_or(BLACK)); 8])
            .collect();
        add(
            &format!("interlaced, height {h}"),
            build(
                8,
                h,
                Some(&pal),
                &[Item::Frame(F {
                    interlaced: true,
                    indices,
                    ..F::solid(0, 0, 8, h, 0)
                })],
            ),
            vec![canvas(&expected)],
        );
    }
    // LZW: random data through every minimum code size, with a clear when
    // the table is full and with the deferred clear.
    for min in 2..=8u8 {
        for (label, full) in [("clear", Full::Clear), ("deferred", Full::Deferred)] {
            let colours: Vec<Rgb> = (0..(1usize << min))
                .map(|i| {
                    [
                        i as u8,
                        i.wrapping_mul(7) as u8,
                        255u8.wrapping_sub(i as u8),
                    ]
                })
                .collect();
            let mut rng = Rng(0xC0FF_EE00 + u64::from(min));
            let (w, h) = (150u16, 120u16);
            let indices: Vec<u8> = (0..usize::from(w).saturating_mul(usize::from(h)))
                .map(|i| {
                    // Runs and noise, so that "K w K" codes occur.
                    if (i / 37) % 3 == 0 {
                        (i / 37).checked_rem(1usize << min).unwrap_or(0) as u8
                    } else {
                        (rng.below(1 << min)) as u8
                    }
                })
                .collect();
            let expected: Vec<[u8; 4]> = indices
                .iter()
                .map(|&i| px(colours.get(usize::from(i)).copied().unwrap_or(BLACK)))
                .collect();
            add(
                &format!("LZW, minimum code size {min}, full table: {label}"),
                build(
                    w,
                    h,
                    Some(&colours),
                    &[Item::Frame(F {
                        indices,
                        full,
                        ..F::solid(0, 0, w, h, 0)
                    })],
                ),
                vec![canvas(&expected)],
            );
        }
    }
    cases
}

#[test]
fn gifs_by_hand() {
    // Under Miri only the first cases (the LZW ones of 18,000 pixels are
    // too slow there).
    let all = hand_cases();
    let cases: Vec<&Hand> = if cfg!(miri) {
        all.iter().filter(|c| !c.name.starts_with("LZW")).collect()
    } else {
        all.iter().collect()
    };
    let (mut pass, mut fail) = (0usize, 0usize);
    for case in &cases {
        let outcome = (|| -> Result<(), String> {
            for (size, empties) in [(usize::MAX, false), (1, false), (5, true)] {
                let d = decode(&case.bytes, size, empties)?;
                if d.end != End::Trailer {
                    return Err(format!("ended {:?}", d.end));
                }
                let got: Vec<&Vec<u8>> = d.frames.iter().map(|f| &f.1).collect();
                let want: Vec<&Vec<u8>> = case.canvases.iter().collect();
                if got != want {
                    return Err(format!("canvases differ at chunk {size}"));
                }
            }
            // The `gif` crate agrees on the canvases (its frames composited
            // by this test), except where a rule is ours (listed).
            if let Some(why) = differences(&case.name, &case.bytes)
                && !case.name.contains("past the colour table")
                && !case.name.contains("unknown extension")
            {
                return Err(format!("the gif crate disagrees: {why}"));
            }
            Ok(())
        })();
        match outcome {
            Ok(()) => pass = pass.saturating_add(1),
            Err(why) => {
                fail = fail.saturating_add(1);
                println!("  {}: {why}", case.name);
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"GIFs by hand: disposal, transparency, interlacing, LZW\" pass={pass} xfail=0 fail={fail} total={}",
        cases.len()
    );
    assert_eq!(fail, 0);
}

/// The fields a frame reports, and the errors of malformed streams.
#[test]
fn frame_facts_and_errors() -> Result<(), String> {
    let pal = [RED, GREEN];
    let f = F::solid(2, 1, 1, 1, 1).gce(2, 0x1234, Some(0));
    let bytes = build(4, 4, Some(&pal), &[Item::Frame(f)]);
    let d = decode(&bytes, usize::MAX, false)?;
    let info = d.frames.first().ok_or("no frame")?.0;
    assert_eq!(
        info,
        FrameInfo {
            left: 2,
            top: 1,
            width: 1,
            height: 1,
            interlaced: false,
            delay_cs: 0x1234,
            disposal: Disposal::Background,
            transparent: Some(0),
        }
    );
    // Disposal values 4 to 7 are read as none.
    for bits in 4..8u8 {
        let f = F::solid(0, 0, 1, 1, 0).gce(bits, 0, None);
        let d = decode(
            &build(1, 1, Some(&pal), &[Item::Frame(f)]),
            usize::MAX,
            false,
        )?;
        assert_eq!(d.frames.first().map(|f| f.0.disposal), Some(Disposal::None));
    }
    // A bare trailer: no frame.
    let d = decode(&build(1, 1, Some(&pal), &[]), usize::MAX, false)?;
    assert_eq!((d.frames.len(), d.end.clone()), (0, End::Trailer));
    // Not a GIF, and a screen of 0 by 0.
    assert!(matches!(
        Gif::decode_config(b"GIF90a\x01\x00\x01\x00"),
        Err(Error::Malformed(_))
    ));
    assert!(matches!(
        Gif::decode_config(b"PNG"),
        Err(Error::Malformed(_))
    ));
    assert_eq!(Gif::decode_config(b"GIF8"), Ok(ConfigStatus::NeedMore));
    assert_eq!(Gif::decode_config(b""), Ok(ConfigStatus::NeedMore));
    assert!(matches!(
        Gif::decode_config(b"GIF89a\x00\x00\x01\x00"),
        Err(Error::Size(_))
    ));
    // Minimum code sizes outside 2 to 8, an unknown block: each ends in an
    // error with no frame.
    let good = build(1, 1, Some(&pal), &[Item::Frame(F::solid(0, 0, 1, 1, 1))]);
    let image_at = good
        .iter()
        .position(|&b| b == 0x2C)
        .ok_or("no image block")?;
    for min in [1u8, 9, 0, 255] {
        let mut bad = good.clone();
        if let Some(b) = bad.get_mut(image_at + 10) {
            *b = min;
        }
        let d = decode(&bad, usize::MAX, false)?;
        assert!(
            matches!(d.end, End::Error(_)),
            "minimum code size {min}: {:?}",
            d.end
        );
        assert!(d.frames.is_empty());
    }
    let mut bad = good.clone();
    if let Some(b) = bad.get_mut(image_at) {
        *b = 0x42;
    }
    assert!(matches!(
        decode(&bad, usize::MAX, false)?.end,
        End::Error(_)
    ));
    // Two frames, the third block broken: the two are delivered.
    let mut two = good.clone();
    two.pop();
    let tail = good.get(image_at..).ok_or("short")?.to_vec();
    two.extend_from_slice(&tail);
    let d = decode(&two, usize::MAX, false)?;
    assert_eq!((d.frames.len(), &d.end), (2, &End::Trailer));
    two.pop();
    two.push(0x42);
    let d = decode(&two, usize::MAX, false)?;
    assert_eq!(d.frames.len(), 2);
    assert!(matches!(d.end, End::Error(_)));
    // The screen in the stream must be the config's.
    let config = match Gif::decode_config(&good) {
        Ok(ConfigStatus::Ready(c)) => c,
        other => return Err(format!("{other:?}")),
    };
    let mut other_size = good.clone();
    if let Some(b) = other_size.get_mut(6) {
        *b = 2;
    }
    let mut pixels = vec![0u8; 4];
    let mut work = vec![0u8; Gif::work_len(&config).map_err(|e| format!("{e:?}"))?];
    let wlen = work.len();
    let mut buffers =
        Buffers::new(&config, wlen, &mut pixels, &mut work).map_err(|e| format!("{e:?}"))?;
    let mut state = Gif::start(&config).map_err(|e| format!("{e:?}"))?;
    assert!(matches!(
        state.step(&other_size, &mut buffers),
        Err(Error::Malformed(_))
    ));
    assert_eq!(state.step(&good, &mut buffers), Err(Error::Spent));
    Ok(())
}
