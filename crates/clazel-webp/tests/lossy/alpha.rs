//! `ALPH` chunks (RFC 9649 section 2.7.1.2) on lossy frames: an alpha plane
//! of every filtering method, raw and compressed with the lossless format
//! (made by the VP8L encoder of `tests/handmade`), at sizes that are and are
//! not multiples of 16; each file is decoded by `clazel-webp` and by
//! `image-webp` and the two must agree on every pixel. Then the cases the
//! RFC leaves to the decoder (a bad chunk that nothing uses, a plane that is
//! too short, trailing bytes, the reserved and preprocessing bits).
//!
//! Under Miri each test makes one file of at most 20 by 20 pixels.

use super::{Frame, chunked, differs, encode, random_frame};
use crate::common::{End, Rng, decode};
use crate::handmade::{self, Opts, T};

fn at(v: &[u8], i: usize) -> u8 {
    v.get(i).copied().unwrap_or(0)
}

/// The filtering of section 2.7.1.2, forwards (the encoder's side): the
/// values to store so that adding the predictor gives back `plane`.
fn filter(plane: &[u8], width: usize, method: u8) -> Vec<u8> {
    (0..plane.len())
        .map(|i| {
            let (x, y) = (
                i.checked_rem(width).unwrap_or(0),
                i.checked_div(width).unwrap_or(0),
            );
            let a = i32::from(at(plane, i.wrapping_sub(1)));
            let b = i32::from(at(plane, i.wrapping_sub(width)));
            let c = i32::from(at(plane, i.wrapping_sub(width).wrapping_sub(1)));
            let pred = match (method, x > 0, y > 0) {
                (0, _, _) | (_, false, false) => 0,
                (1, true, _) | (2, true, false) | (3, true, false) => a,
                (1, false, true) | (2, _, true) | (3, false, true) => b,
                _ => a.wrapping_add(b).wrapping_sub(c).clamp(0, 255),
            };
            at(plane, i).wrapping_sub(pred as u8)
        })
        .collect()
}

/// An alpha plane with smooth parts and noise.
fn plane(rng: &mut Rng, w: usize, h: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(w.wrapping_mul(h));
    for i in 0..w.wrapping_mul(h) {
        let (x, y) = (i.checked_rem(w).unwrap_or(0), i.checked_div(w).unwrap_or(0));
        let smooth = (x.wrapping_mul(7).wrapping_add(y.wrapping_mul(3))) % 256;
        let value = if rng.below(5) == 0 {
            rng.below(256)
        } else {
            smooth
        };
        v.push(u8::try_from(value).unwrap_or(0));
    }
    v
}

/// The `ALPH` payload for `plane`: the header byte (`rsv`, `pre` and the
/// method and compression), then the bytes, raw or as a headerless lossless
/// stream of an image whose green channel is the alpha (the others random).
fn alph(
    rng: &mut Rng,
    plane: &[u8],
    w: usize,
    h: usize,
    method: u8,
    compression: u8,
    junk: u8,
) -> Result<Vec<u8>, String> {
    let stored = filter(plane, w, method);
    let mut out = vec![(junk << 4) | (method << 2) | compression];
    if compression == 0 {
        out.extend_from_slice(&stored);
    } else {
        let argb: Vec<u32> = stored
            .iter()
            .map(|&g| {
                let other = u32::try_from(rng.below(0x1_0000)).unwrap_or(0);
                0xFF00_0000 | (other & 0xFF) << 16 | u32::from(g) << 8 | (other >> 8)
            })
            .collect();
        let ts: Vec<T> = match rng.below(3) {
            0 => vec![],
            1 => vec![T::Green],
            _ => vec![T::Pred(2, vec![])],
        };
        let payload = handmade::vp8l_payload(rng, &argb, w, h, &ts, &Opts::default())?;
        // "does NOT contain any headers describing the image dimensions": the
        // 5 bytes of section 3.4 (signature, sizes, alpha hint, version) are
        // not there.
        out.extend_from_slice(payload.get(5..).unwrap_or(&[]));
    }
    Ok(out)
}

/// A lossy frame of `w` by `h` and the file with `chunks` before it.
fn file_with(rng: &mut Rng, w: u32, h: u32, before: Vec<([u8; 4], Vec<u8>)>) -> (Frame, Vec<u8>) {
    let frame = random_frame(rng, w, h);
    let vp8 = encode(&frame, rng);
    let mut chunks = before;
    chunks.push((*b"VP8 ", vp8));
    (frame, chunked(&chunks, Some((w, h))))
}

#[test]
fn alpha_of_every_filter_and_compression_agrees() -> Result<(), String> {
    let sizes: &[(usize, usize)] = if cfg!(miri) {
        &[(7, 5)]
    } else {
        &[(1, 1), (3, 2), (16, 16), (17, 9), (31, 33), (40, 7)]
    };
    let mut bad = Vec::new();
    let mut n = 0u32;
    for (si, &(w, h)) in sizes.iter().enumerate() {
        for method in 0..4u8 {
            for compression in 0..2u8 {
                if cfg!(miri) && (method != 3 || compression != 1) {
                    continue;
                }
                let mut rng = Rng(0xA1FA_0000
                    ^ u64::try_from(si * 64 + usize::from(method) * 4 + usize::from(compression))
                        .unwrap_or(0));
                let p = plane(&mut rng, w, h);
                // Rsv (any) and P (0 or 1: image-webp refuses 2 and 3)
                let junk = u8::try_from((rng.below(4) << 2) | rng.below(2)).unwrap_or(0);
                let a = alph(&mut rng, &p, w, h, method, compression, junk)?;
                let (_, file) = file_with(
                    &mut rng,
                    u32::try_from(w).unwrap_or(1),
                    u32::try_from(h).unwrap_or(1),
                    vec![(*b"ALPH", a)],
                );
                n += 1;
                if let Some(d) = differs(&format!("alpha {w}x{h} F{method} C{compression}"), &file)
                {
                    bad.push(d);
                }
                // And the alpha really is the plane.
                if let Ok(d) = decode(&file, usize::MAX, false) {
                    let got: Vec<u8> = d
                        .frames
                        .first()
                        .map(|f| {
                            f.1.chunks(4)
                                .map(|px| px.get(3).copied().unwrap_or(0))
                                .collect()
                        })
                        .unwrap_or_default();
                    if got != p {
                        bad.push(format!(
                            "alpha {w}x{h} F{method} C{compression}: wrong plane"
                        ));
                    }
                }
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"lossy with ALPH vs image-webp 0.2.4\" pass={} fail={} total={n}",
        usize::try_from(n).unwrap_or(0).saturating_sub(bad.len()),
        bad.len()
    );
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    Ok(())
}

/// What `decode` ended with, as text.
fn end_of(file: &[u8]) -> Result<String, String> {
    match decode(file, usize::MAX, false) {
        Ok(d) => match d.end {
            End::Error(e) => Ok(e),
            other => Ok(format!("{other:?}")),
        },
        Err(e) => Ok(e),
    }
}

#[test]
fn alpha_edge_cases() -> Result<(), String> {
    let (w, h) = (9usize, 5usize);
    let mut rng = Rng(77);
    let p = plane(&mut rng, w, h);
    let (wu, hu) = (u32::try_from(w).unwrap_or(1), u32::try_from(h).unwrap_or(1));

    // Bytes after the plane are not looked at.
    let mut raw = alph(&mut rng, &p, w, h, 0, 0, 0)?;
    raw.extend_from_slice(&[1, 2, 3]);
    let (_, file) = file_with(&mut rng, wu, hu, vec![(*b"ALPH", raw)]);
    if let Some(d) = differs("trailing bytes", &file) {
        return Err(d);
    }

    // A plane too short, a header only, an empty chunk, a compression method
    // over 1: errors (the image uses the plane).
    let short: Vec<u8> = alph(&mut rng, &p, w, h, 0, 0, 0)?
        .into_iter()
        .take(w * h)
        .collect();
    for (name, a) in [
        ("short plane", short),
        ("header only", vec![0]),
        ("empty chunk", vec![]),
        ("compression 2", vec![2, 0, 0, 0]),
        ("compression 3", vec![3, 0, 0, 0]),
        ("bad lossless stream", vec![1, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
    ] {
        let (_, file) = file_with(&mut rng, wu, hu, vec![(*b"ALPH", a)]);
        let e = end_of(&file)?;
        if !e.contains("Malformed") {
            return Err(format!("{name}: {e}"));
        }
    }

    // A second `ALPH` chunk is not looked at; one after the image neither.
    let good = alph(&mut rng, &p, w, h, 1, 0, 0)?;
    let second = plane(&mut rng, w, h);
    let other = alph(&mut rng, &second, w, h, 2, 0, 0)?;
    let (_, file) = file_with(
        &mut rng,
        wu,
        hu,
        vec![(*b"ALPH", good.clone()), (*b"ALPH", other)],
    );
    let d = decode(&file, usize::MAX, false)?;
    let got: Vec<u8> = d
        .frames
        .first()
        .map(|f| {
            f.1.chunks(4)
                .map(|px| px.get(3).copied().unwrap_or(0))
                .collect()
        })
        .unwrap_or_default();
    if got != p {
        return Err("a second ALPH chunk was used".into());
    }

    // A bad `ALPH` chunk before a lossless image is not an error: the image
    // has its own alpha.
    let argb = handmade::image(&mut rng, w, h, 5, true);
    let vp8l = handmade::vp8l_payload(&mut rng, &argb, w, h, &[], &Opts::default())?;
    let file = chunked(
        &[(*b"ALPH", vec![3, 1, 2]), (*b"VP8L", vp8l)],
        Some((wu, hu)),
    );
    let d = decode(&file, usize::MAX, false)?;
    if d.frames.first().map(|f| f.1.clone()) != Some(handmade::rgba(&argb)) {
        return Err(format!("a lossless image after a bad ALPH: {:?}", d.end));
    }

    // Without an `ALPH` chunk every pixel is opaque.
    let (_, file) = file_with(&mut rng, wu, hu, vec![]);
    let d = decode(&file, usize::MAX, false)?;
    let opaque = d
        .frames
        .first()
        .is_some_and(|f| f.1.chunks(4).all(|px| px.get(3) == Some(&255)));
    if !opaque {
        return Err("a lossy image without ALPH is not opaque".into());
    }
    Ok(())
}
