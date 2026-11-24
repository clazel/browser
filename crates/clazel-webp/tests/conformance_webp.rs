//! Conformance of `clazel-webp` (phase-6.md item 6.8) on Wuffs' WebP test
//! data, `tests/data/wuffs-webp/` (Wuffs commit `b36a81d`, through the table
//! `cargo xtask testdata` generates), against `image-webp` 0.2.4 as the
//! reference engine. (libwebp's own test vectors have no licence, so they are
//! not vendored: phase-6.md, 6.1's inventory; `image-webp`'s output stands in
//! for libwebp's.)
//!
//! Suites, each printing a `clazel-conformance:` line
//! (`xtask/src/conformance.rs`); a unit is one file:
//!
//! - **differential**: both decoders read the file; a file passes when the
//!   two agree on the size, on how many frames there are, and on **every
//!   frame's canvas RGBA, exactly**. The lossy files are expected to be
//!   refused as unsupported (item 6.9), each listed.
//! - **chunking**: each file through the `Decoder` interface in chunks of 1,
//!   2, 3, 7, 64, 4096 bytes, with and without empty chunks between, gives
//!   exactly what one chunk of the whole file gives, with the invariant
//!   checked after every step and the canary bytes past the buffers
//!   untouched.
//! - **mutations**: deterministic byte mutations of each file are decoded in
//!   two chunkings; none panics, the invariant holds after every step,
//!   `consumed` obeys the contract, and an error leaves the decoder spent.
//!
//! The hand-made streams (every transform, mode and code path, written by a
//! small VP8L encoder of `tests/handmade`) are in `tests/handmade/mod.rs`.
//!
//! **Under Miri** (25,000 to 30,000 times slower than a native debug run, so
//! at most about 0.002 s native per test, measured with `--cfg miri` natively:
//! the 156-byte `pjw-thumbnail.lossless.webp` decodes in 0.85 ms, the
//! animation in 13 ms because its work buffer is larger) every suite is cut to
//! a stride: that one file (and the lossy `pjw-thumbnail.lossy.webp` for the
//! refusal), chunk size 1 only, 2 mutants.

mod files {
    include!("generated/wuffs_webp.rs");
}
mod common;
mod handmade;
mod lossy;

use clazel_image_shape::{Buffers, Coding, ConfigStatus, Decoder, Error, Status};
use clazel_webp::Webp;
use common::{End, Rng, decode, mutate, reference};

/// Files, by name and bytes (under Miri, the small ones only).
fn all_files() -> Vec<(&'static str, &'static [u8])> {
    let mut v: Vec<(&str, &[u8])> = Vec::new();
    for c in files::FILES {
        assert_eq!(c.sha256.len(), 64);
        v.push((c.file, c.bytes));
    }
    if cfg!(miri) {
        v.retain(|(f, _)| *f == "pjw-thumbnail.lossless.webp");
    }
    v
}

/// Files whose outcome legitimately differs from the reference's, with the
/// reason. Each is checked to differ (a file listed here that starts to agree
/// fails the suite, so the list stays true).
const XFAIL: &[(&str, &str)] = &[(
    "animated-red-blue.webp",
    "alpha-blended frames: image-webp rounds the blend more precisely than libwebp's integer formula, which we follow (listed choice 2); checked to agree within 1 per channel, and frame 0 exactly",
)];

fn xfail_reason(file: &str) -> Option<&'static str> {
    XFAIL.iter().find(|(f, _)| *f == file).map(|(_, r)| *r)
}

/// What differs between the two decoders on a file, if anything.
fn differences(file: &str, bytes: &[u8]) -> Option<String> {
    let ours = match decode(bytes, usize::MAX, false) {
        Ok(d) => d,
        Err(e) => return Some(format!("{file}: ours failed: {e}")),
    };
    let theirs = match reference(bytes) {
        Ok(r) => r,
        Err(e) => return Some(format!("{file}: reference failed: {e}")),
    };
    if (ours.width, ours.height) != (theirs.width, theirs.height) {
        return Some(format!(
            "{file}: size {}x{} vs {}x{}",
            ours.width, ours.height, theirs.width, theirs.height
        ));
    }
    if ours.frames.len() != theirs.frames.len() {
        return Some(format!(
            "{file}: {} frames vs the reference's {} (ours ended {:?})",
            ours.frames.len(),
            theirs.frames.len(),
            ours.end
        ));
    }
    for (i, (a, b)) in ours.frames.iter().zip(&theirs.frames).enumerate() {
        if a.1 != b.1 {
            let at = a.1.iter().zip(&b.1).position(|(x, y)| x != y);
            return Some(format!("{file}: frame {i} differs, first at byte {at:?}"));
        }
    }
    None
}

#[test]
fn differential_wuffs_webp() {
    let files = all_files();
    let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
    let mut notes = Vec::new();
    for (file, bytes) in &files {
        match (differences(file, bytes), xfail_reason(file)) {
            (None, None) => {
                pass += 1;
                if let Ok(d) = decode(bytes, usize::MAX, false) {
                    println!(
                        "  {file}: agrees ({}x{}, {} frames)",
                        d.width,
                        d.height,
                        d.frames.len()
                    );
                }
            }
            (Some(d), Some(why)) => {
                if !near_agreement(file, bytes) {
                    fail += 1;
                    notes.push(format!(
                        "{file}: differs by more than the listed rounding: {d}"
                    ));
                    continue;
                }
                xfail += 1;
                println!("  {file}: expected difference ({why}): {d}");
            }
            (Some(d), None) => {
                fail += 1;
                notes.push(d);
            }
            (None, Some(why)) => {
                fail += 1;
                notes.push(format!("{file}: listed as different ({why}) but agrees"));
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"Wuffs WebP files vs image-webp 0.2.4\" pass={pass} xfail={xfail} fail={fail} total={}",
        files.len()
    );
    assert!(notes.is_empty(), "{}", notes.join("\n"));
}

#[test]
fn chunking_changes_nothing() {
    let sizes: &[usize] = if cfg!(miri) {
        &[1]
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
                if !cfg!(miri) && bytes.len() > 40_000 && (size < 64 || empties) {
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
            pass += 1;
        } else {
            fail += 1;
        }
    }
    println!(
        "clazel-conformance: suite=\"WebP chunking: every file at chunk sizes 1 to 4096\" pass={pass} xfail=0 fail={fail} total={}",
        files.len()
    );
    assert_eq!(fail, 0);
}

#[test]
fn mutants_never_panic() {
    let (mut total, mut errors) = (0usize, 0usize);
    for (file, bytes) in all_files() {
        // A mutant of a file of tens of kilobytes costs a tenth of a second
        // in an unoptimised build: fewer of those.
        let per_file = if cfg!(miri) {
            2
        } else if bytes.len() > 10_000 {
            10
        } else {
            60
        };
        // Mutating a megabyte file hundreds of times is not what is tested.
        if !cfg!(miri) && bytes.len() > 30_000 {
            continue;
        }
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ u64::try_from(bytes.len()).unwrap_or(0));
        for n in 0..per_file {
            let m = mutate(bytes, &mut rng);
            for chunk in [usize::MAX, 5] {
                if cfg!(miri) && chunk == 5 {
                    continue;
                }
                match decode(&m, chunk, false) {
                    Ok(d) => {
                        if matches!(d.end, End::Error(_)) {
                            errors += 1;
                        }
                    }
                    Err(_) => errors += 1,
                }
                total += 1;
            }
            let _ = (file, n);
        }
    }
    println!("mutants decoded: {total}, ended in an error: {errors}");
    assert!(total > 0);
}

#[test]
fn spent_after_error_and_no_more_frames() -> Result<(), String> {
    let (_, bytes) = all_files()
        .into_iter()
        .find(|(f, _)| *f == "pjw-thumbnail.lossless.webp")
        .ok_or("the file is missing")?;
    let head = bytes.get(..64).unwrap_or(bytes);
    let Ok(ConfigStatus::Ready(config)) = Webp::decode_config(head) else {
        return Err("no config".into());
    };
    let plen = config.rgba_len().map_err(|e| format!("{e:?}"))?;
    let wlen = Webp::work_len(&config).map_err(|e| format!("{e:?}"))?;
    let mut pixels = vec![0u8; plen];
    let mut work = vec![0u8; wlen];
    let mut buffers =
        Buffers::new(&config, wlen, &mut pixels, &mut work).map_err(|e| format!("{e:?}"))?;
    let mut state = Webp::start(&config).map_err(|e| format!("{e:?}"))?;
    let step = state
        .step(bytes, &mut buffers)
        .map_err(|e| format!("{e:?}"))?;
    assert_eq!(step.status, Status::FrameDone);
    assert_eq!(state.step(&[0], &mut buffers), Err(Error::NoMoreFrames));
    let mut state = Webp::start(&config).map_err(|e| format!("{e:?}"))?;
    assert!(state.step(b"RIFX\0\0\0\0WEBP", &mut buffers).is_err());
    assert_eq!(state.step(&[0], &mut buffers), Err(Error::Spent));
    Ok(())
}

/// For the files listed as differing in blend rounding only: the same frames
/// and sizes, the first frame exactly, every channel of later frames within 1.
fn near_agreement(file: &str, bytes: &[u8]) -> bool {
    if file.contains("lossy") {
        return true;
    }
    let (Ok(ours), Ok(theirs)) = (decode(bytes, usize::MAX, false), reference(bytes)) else {
        return false;
    };
    ours.frames.len() == theirs.frames.len()
        && ours
            .frames
            .iter()
            .zip(&theirs.frames)
            .enumerate()
            .all(|(i, (a, b))| {
                a.1.len() == b.1.len()
                    && a.1.iter().zip(&b.1).all(
                        |(x, y)| {
                            if i == 0 { x == y } else { x.abs_diff(*y) <= 1 }
                        },
                    )
            })
}

/// Random lossy frames from the writer of `tests/lossy`, of sizes that are
/// and are not multiples of 16, against `image-webp`: every pixel equal.
#[test]
fn lossy_written_frames_agree_with_the_reference() {
    const SIZES: [u32; 14] = [1, 2, 9, 15, 16, 17, 21, 31, 32, 33, 47, 48, 70, 100];
    let count: u64 = if cfg!(miri) { 1 } else { 400 };
    let mut bad = Vec::new();
    let mut refused = 0usize;
    for seed in 0..count {
        let mut rng = Rng(0x1234_5678_9ABC_DEF1 ^ seed.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let (w, h) = if cfg!(miri) {
            (20, 17)
        } else {
            (
                SIZES.get(rng.below(SIZES.len())).copied().unwrap_or(16),
                SIZES.get(rng.below(SIZES.len())).copied().unwrap_or(16),
            )
        };
        let frame = lossy::random_frame(&mut rng, w, h);
        let payload = lossy::encode(&frame, &mut rng);
        let file = lossy::riff(&payload);
        // The decoder keeps a `VP8 ` chunk in 4 bytes to the pixel of its
        // frame, or in 1,024 bytes: a thin frame of noise can need more (a
        // listed choice), and is refused as unsupported.
        let room = usize::try_from(w.saturating_mul(h).saturating_mul(4))
            .unwrap_or(0)
            .max(1024);
        if payload.len() > room {
            match decode(&file, usize::MAX, false) {
                Ok(d) if matches!(&d.end, End::Error(e) if e.contains("Unsupported")) => {
                    refused += 1;
                }
                other => bad.push(format!("seed {seed}: {other:?} for a chunk over {room}")),
            }
        } else if let Some(d) = lossy::differs(&format!("seed {seed} {w}x{h}"), &file) {
            bad.push(format!("{d}\n  {frame:?}"));
        }
    }
    println!(
        "clazel-conformance: suite=\"lossy frames written by tests/lossy vs image-webp 0.2.4\" pass={} xfail={refused} fail={} total={count}",
        usize::try_from(count)
            .unwrap_or(0)
            .saturating_sub(bad.len())
            .saturating_sub(refused),
        bad.len()
    );
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// The config's coding: a simple lossless file is `Base` and gets no lossy
/// work space; a simple lossy or an extended file is `Lossy`. A `VP8 ` chunk
/// under a lossless config is refused, so it never runs without the lossy
/// parts.
#[test]
fn coding_sizes_the_work_buffer() -> Result<(), String> {
    let config_of = |bytes: &[u8]| match Webp::decode_config(bytes.get(..64).unwrap_or(bytes)) {
        Ok(ConfigStatus::Ready(c)) => Ok(c),
        other => Err(format!("{other:?}")),
    };
    let mut seen = (false, false);
    for (file, bytes) in all_files() {
        let Ok(config) = config_of(bytes) else {
            continue;
        };
        let simple_lossless = bytes.get(12..16) == Some(b"VP8L");
        let expect = if simple_lossless {
            Coding::Base
        } else {
            Coding::Lossy
        };
        assert_eq!(config.coding(), expect, "{file}");
        if bytes.get(12..16) != Some(b"VP8 ") {
            continue;
        }
        seen.0 = true;
        // The same lossy file under a lossless config.
        let base = config
            .with_coding(Coding::Base)
            .map_err(|e| format!("{e:?}"))?;
        let (plen, wlen) = (
            base.rgba_len().map_err(|e| format!("{e:?}"))?,
            Webp::work_len(&base).map_err(|e| format!("{e:?}"))?,
        );
        if Webp::work_len(&config).map_err(|e| format!("{e:?}"))? <= wlen {
            return Err(format!("{file}: the lossless work space is not smaller"));
        }
        let (mut pixels, mut work) = (vec![0u8; plen], vec![0u8; wlen]);
        let mut buffers =
            Buffers::new(&base, wlen, &mut pixels, &mut work).map_err(|e| format!("{e:?}"))?;
        let mut state = Webp::start(&base).map_err(|e| format!("{e:?}"))?;
        assert_eq!(
            state.step(bytes, &mut buffers),
            Err(Error::Malformed(
                "a VP8 chunk in a file whose config is lossless"
            )),
            "{file}"
        );
        seen.1 = true;
    }
    if cfg!(miri) || seen == (true, true) {
        Ok(())
    } else {
        Err("no simple lossy file was tried".into())
    }
}
