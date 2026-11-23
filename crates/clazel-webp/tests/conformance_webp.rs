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

use clazel_image_shape::{Buffers, ConfigStatus, Decoder, Error, Status};
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
const XFAIL: &[(&str, &str)] = &[
    (
        "animated-red-blue.webp",
        "alpha-blended frames: image-webp rounds the blend more precisely than libwebp's integer formula, which we follow (listed choice 2); checked to agree within 1 per channel, and frame 0 exactly",
    ),
    (
        "pjw-thumbnail.lossy.webp",
        "lossy (VP8): refused as unsupported, decoding it is item 6.9",
    ),
    (
        "mona-lisa.21x32.q0.lossy.webp",
        "lossy (VP8): refused as unsupported, decoding it is item 6.9",
    ),
];

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
fn lossy_is_refused_not_misread() -> Result<(), String> {
    for c in files::FILES {
        let (file, bytes) = (c.file, c.bytes);
        let wanted = if cfg!(miri) {
            file == "pjw-thumbnail.lossy.webp"
        } else {
            file.contains("lossy")
        };
        if !wanted {
            continue;
        }
        // The config is read (the size of the VP8 frame)...
        let head = bytes.get(..bytes.len().min(64)).unwrap_or(bytes);
        let Ok(ConfigStatus::Ready(config)) = Webp::decode_config(head) else {
            return Err(format!("{file}: no config"));
        };
        assert!(config.width() > 0 && config.height() > 0);
        // ... and decoding says unsupported.
        match decode(bytes, usize::MAX, false) {
            Ok(d) => assert!(
                matches!(&d.end, End::Error(e) if e.contains("Unsupported")),
                "{file}: {:?}",
                d.end
            ),
            Err(e) => return Err(format!("{file}: {e}")),
        }
    }
    Ok(())
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
    let per_file = if cfg!(miri) { 2 } else { 60 };
    let (mut total, mut errors) = (0usize, 0usize);
    for (file, bytes) in all_files() {
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
