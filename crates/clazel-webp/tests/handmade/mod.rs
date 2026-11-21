//! WebP streams made by hand: a small VP8L **encoder** (written here, from
//! RFC 9649, sharing no code with the decoder) makes images that use every
//! transform, predictor mode, colour cache size, meta prefix codes, simple and
//! normal code length codes and backward references; each is decoded and must
//! equal the image it was made from, exactly, and `image-webp` must agree.
//! Container cases (still `VP8X`, chunks to skip, animations with blending and
//! disposal, and malformed files) are built the same way.
//!
//! The workspace lints apply to tests (no indexing, no unchecked arithmetic),
//! so the encoder is written with the small helpers below.
//!
//! Under Miri (25,000 to 30,000 times slower than a native debug run: about
//! 0.002 s native per test) each test runs one or two images of at most 6 by 6
//! pixels, and the loops over seeds, sizes and cache bits run once.

use crate::common::{End, Rng, decode, reference};

const CL_ORDER: [usize; 19] = [
    17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
];

/// Figure 20 of RFC 9649, again, as `(xi, yi)`.
const MAP: [(i32, i32); 120] = [
    (0, 1),
    (1, 0),
    (1, 1),
    (-1, 1),
    (0, 2),
    (2, 0),
    (1, 2),
    (-1, 2),
    (2, 1),
    (-2, 1),
    (2, 2),
    (-2, 2),
    (0, 3),
    (3, 0),
    (1, 3),
    (-1, 3),
    (3, 1),
    (-3, 1),
    (2, 3),
    (-2, 3),
    (3, 2),
    (-3, 2),
    (0, 4),
    (4, 0),
    (1, 4),
    (-1, 4),
    (4, 1),
    (-4, 1),
    (3, 3),
    (-3, 3),
    (2, 4),
    (-2, 4),
    (4, 2),
    (-4, 2),
    (0, 5),
    (3, 4),
    (-3, 4),
    (4, 3),
    (-4, 3),
    (5, 0),
    (1, 5),
    (-1, 5),
    (5, 1),
    (-5, 1),
    (2, 5),
    (-2, 5),
    (5, 2),
    (-5, 2),
    (4, 4),
    (-4, 4),
    (3, 5),
    (-3, 5),
    (5, 3),
    (-5, 3),
    (0, 6),
    (6, 0),
    (1, 6),
    (-1, 6),
    (6, 1),
    (-6, 1),
    (2, 6),
    (-2, 6),
    (6, 2),
    (-6, 2),
    (4, 5),
    (-4, 5),
    (5, 4),
    (-5, 4),
    (3, 6),
    (-3, 6),
    (6, 3),
    (-6, 3),
    (0, 7),
    (7, 0),
    (1, 7),
    (-1, 7),
    (5, 5),
    (-5, 5),
    (7, 1),
    (-7, 1),
    (4, 6),
    (-4, 6),
    (6, 4),
    (-6, 4),
    (2, 7),
    (-2, 7),
    (7, 2),
    (-7, 2),
    (3, 7),
    (-3, 7),
    (7, 3),
    (-7, 3),
    (5, 6),
    (-5, 6),
    (6, 5),
    (-6, 5),
    (8, 0),
    (4, 7),
    (-4, 7),
    (7, 4),
    (-7, 4),
    (8, 1),
    (8, 2),
    (6, 6),
    (-6, 6),
    (8, 3),
    (5, 7),
    (-5, 7),
    (7, 5),
    (-7, 5),
    (8, 4),
    (6, 7),
    (-6, 7),
    (7, 6),
    (-7, 6),
    (8, 5),
    (7, 7),
    (-7, 7),
    (8, 6),
    (8, 7),
];

// -------------------------------------------------------------- helpers

fn add(a: usize, b: usize) -> usize {
    a.wrapping_add(b)
}
fn sub(a: usize, b: usize) -> usize {
    a.wrapping_sub(b)
}
fn mul(a: usize, b: usize) -> usize {
    a.wrapping_mul(b)
}
/// `v[i]`, or the default.
fn at<T: Copy + Default>(v: &[T], i: usize) -> T {
    v.get(i).copied().unwrap_or_default()
}
fn set<T>(v: &mut [T], i: usize, x: T) {
    if let Some(s) = v.get_mut(i) {
        *s = x;
    }
}
/// `ceil(a / 2^bits)`.
fn ceil_shr(a: usize, bits: u32) -> usize {
    add(a, sub(1usize.wrapping_shl(bits), 1)).wrapping_shr(bits)
}
fn ch(p: u32, shift: u32) -> u8 {
    p.wrapping_shr(shift) as u8
}
fn px(a: u8, r: u8, g: u8, b: u8) -> u32 {
    (u32::from(a) << 24) | (u32::from(r) << 16) | (u32::from(g) << 8) | u32::from(b)
}
const SHIFTS: [u32; 4] = [0, 8, 16, 24];

// ---------------------------------------------------------------- bits

#[derive(Default)]
pub struct Writer {
    bytes: Vec<u8>,
    acc: u64,
    n: u32,
}

impl Writer {
    pub fn put(&mut self, v: u32, k: u32) {
        for i in 0..k {
            let bit = u64::from(v.wrapping_shr(i) & 1);
            self.acc |= bit.wrapping_shl(self.n);
            self.n = self.n.wrapping_add(1);
            if self.n == 8 {
                self.bytes.push(self.acc as u8);
                self.acc = 0;
                self.n = 0;
            }
        }
    }

    /// A code, first bit most significant.
    fn put_code(&mut self, code: u32, len: u32) {
        for i in (0..len).rev() {
            self.put(code.wrapping_shr(i) & 1, 1);
        }
    }

    pub fn finish(mut self) -> Vec<u8> {
        if self.n > 0 {
            self.bytes.push(self.acc as u8);
        }
        self.bytes
    }
}

// ---------------------------------------------------------------- codes

/// Lengths of a complete code over `n >= 2` symbols.
fn complete_lengths(n: usize) -> Vec<u8> {
    let mut k = 1u32;
    while 1usize.wrapping_shl(k) < n {
        k = k.wrapping_add(1);
    }
    let short = sub(1usize.wrapping_shl(k), n);
    (0..n)
        .map(|i| {
            if i < short {
                k.wrapping_sub(1) as u8
            } else {
                k as u8
            }
        })
        .collect()
}

/// Canonical codes for lengths (0 for unused).
fn canonical(lens: &[u8]) -> Vec<u32> {
    let mut codes = vec![0u32; lens.len()];
    let mut code = 0u32;
    for len in 1..=15u8 {
        for (i, &l) in lens.iter().enumerate() {
            if l == len {
                set(&mut codes, i, code);
                code = code.wrapping_add(1);
            }
        }
        code = code.wrapping_shl(1);
    }
    codes
}

/// How a code is written and used.
enum Code {
    /// One symbol, zero bits.
    One(u32),
    /// Two symbols (low, high), one bit.
    Two(u32, u32),
    /// A full normal code.
    Full(Vec<u8>, Vec<u32>),
}

impl Code {
    fn emit(&self, w: &mut Writer, sym: u32) {
        match self {
            Code::One(s) => assert_eq!(*s, sym),
            Code::Two(a, b) => {
                assert!(sym == *a || sym == *b);
                w.put(u32::from(sym == *b && a != b), 1);
            }
            Code::Full(lens, codes) => {
                let i = sym as usize;
                w.put_code(at(codes, i), u32::from(at(lens, i)));
            }
        }
    }
}

/// Writes the code lengths of a normal code (section 3.7.2.1.2).
fn write_normal(w: &mut Writer, lens: &[u8]) {
    let n_eff = lens.iter().rposition(|&l| l != 0).map_or(1, |p| add(p, 1));
    let trimmed = n_eff < lens.len();
    let body: &[u8] = lens
        .get(..if trimmed { n_eff } else { lens.len() })
        .unwrap_or(lens);
    // Tokens: (symbol, extra bits, extra value).
    let mut toks: Vec<(usize, u32, u32)> = Vec::new();
    let mut prev = 8u8;
    let mut i = 0;
    while i < body.len() {
        let v = at(body, i);
        let run = body
            .get(i..)
            .unwrap_or(&[])
            .iter()
            .take_while(|&&x| x == v)
            .count();
        if v == 0 && run >= 11 {
            let r = run.min(138);
            toks.push((18, 7, sub(r, 11) as u32));
            i = add(i, r);
        } else if v == 0 && run >= 3 {
            let r = run.min(10);
            toks.push((17, 3, sub(r, 3) as u32));
            i = add(i, r);
        } else if v != 0 && v == prev && run >= 3 {
            let r = run.min(6);
            toks.push((16, 2, sub(r, 3) as u32));
            i = add(i, r);
        } else {
            toks.push((usize::from(v), 0, 0));
            if v != 0 {
                prev = v;
            }
            i = add(i, 1);
        }
    }
    let use_max = trimmed && toks.len() >= 2;
    let cl_lens = complete_lengths(19);
    let cl_codes = canonical(&cl_lens);
    w.put(0, 1); // normal
    w.put(15, 4); // num_code_lengths = 19
    for &o in &CL_ORDER {
        w.put(u32::from(at(&cl_lens, o)), 3);
    }
    if use_max {
        w.put(1, 1);
        let rest = sub(toks.len(), 2);
        let mut k = 0u32;
        while rest >= 1usize.wrapping_shl(add(2, mul(2, k as usize)) as u32) {
            k = k.wrapping_add(1);
        }
        w.put(k, 3);
        w.put(rest as u32, add(2, mul(2, k as usize)) as u32);
    } else {
        w.put(0, 1);
        // Without max_symbol every symbol of the alphabet must be covered.
        assert_eq!(body.len(), lens.len());
    }
    for (sym, extra, val) in toks {
        w.put_code(at(&cl_codes, sym), u32::from(at(&cl_lens, sym)));
        w.put(val, extra);
    }
}

/// Picks and writes the code for the symbols used in `hist`, over an
/// alphabet of `n` symbols.
fn make_code(w: &mut Writer, hist: &[u32], n: usize, force_full: bool) -> Code {
    let used: Vec<usize> = (0..n).filter(|&s| at(hist, s) > 0).collect();
    if !force_full && used.len() <= 2 && used.iter().all(|&s| s < 256) {
        w.put(1, 1); // simple
        match used.as_slice() {
            [] => {
                w.put(0, 1); // one symbol
                w.put(0, 1); // first is 1 bit
                w.put(0, 1); // symbol 0
                Code::One(0)
            }
            [a] => {
                w.put(0, 1);
                if *a < 2 {
                    w.put(0, 1);
                    w.put(*a as u32, 1);
                } else {
                    w.put(1, 1);
                    w.put(*a as u32, 8);
                }
                Code::One(*a as u32)
            }
            [a, b] => {
                w.put(1, 1); // two symbols
                w.put(1, 1); // first is 8 bits
                w.put(*a as u32, 8);
                w.put(*b as u32, 8);
                Code::Two(*a as u32, *b as u32)
            }
            _ => Code::One(0),
        }
    } else {
        let lens = complete_lengths(n);
        let codes = canonical(&lens);
        write_normal(w, &lens);
        Code::Full(lens, codes)
    }
}

// ---------------------------------------------------------------- images

/// A token of the entropy-coded image.
#[derive(Clone, Copy, Debug)]
enum Tok {
    Lit(u32),
    Cache(u32),
    Copy { len: u32, code: u32 },
}

/// The LZ77 prefix coding of a value (libwebp's `VP8LPrefixEncode`).
fn prefix_encode(v: u32) -> (u32, u32, u32) {
    if v <= 4 {
        return (v.wrapping_sub(1), 0, 0);
    }
    let v1 = v.wrapping_sub(1);
    let hb = 31u32.wrapping_sub(v1.leading_zeros());
    let second = v1.wrapping_shr(hb.wrapping_sub(1)) & 1;
    let extra = hb.wrapping_sub(1);
    let mask = 1u32.wrapping_shl(extra).wrapping_sub(1);
    (hb.wrapping_mul(2).wrapping_add(second), extra, v1 & mask)
}

fn cache_key(argb: u32, bits: u8) -> usize {
    (0x1e35_a7bd_u32
        .wrapping_mul(argb)
        .wrapping_shr(32u32.wrapping_sub(u32::from(bits)))) as usize
}

/// The distance of code `code` in an image `w` wide.
fn dist_of(code: u32, w: usize) -> usize {
    if code > 120 {
        return code.wrapping_sub(120) as usize;
    }
    let (xi, yi) = MAP
        .get(code.wrapping_sub(1) as usize)
        .copied()
        .unwrap_or((0, 1));
    let d = xi.wrapping_add(yi.wrapping_mul(w as i32));
    d.max(1) as usize
}

/// How to code one image.
#[derive(Clone, Debug, Default)]
pub struct Opts {
    pub cache_bits: u8,
    /// Meta prefix codes: (prefix bits, groups).
    pub meta: Option<(u8, u32)>,
    /// Random backward references.
    pub lz: bool,
    /// Never use the simple code length code.
    pub full_codes: bool,
    /// Tries at a backward reference at each position.
    pub copy_tries: u32,
}

/// Counts one use of symbol `s` of code `c` of group `g`.
fn bump(hist: &mut [Vec<Vec<u32>>], g: usize, c: usize, s: usize) {
    if let Some(slot) = hist
        .get_mut(g)
        .and_then(|h| h.get_mut(c))
        .and_then(|h| h.get_mut(s))
    {
        *slot = slot.wrapping_add(1);
    }
}

/// Writes an entropy-coded image of `img` (`width` wide). `main` adds the
/// meta prefix part.
fn write_image(w: &mut Writer, rng: &mut Rng, img: &[u32], width: usize, o: &Opts, main: bool) {
    let height = img.len().checked_div(width).unwrap_or(0);
    if o.cache_bits > 0 {
        w.put(1, 1);
        w.put(u32::from(o.cache_bits), 4);
    } else {
        w.put(0, 1);
    }
    // Groups of the blocks.
    let (mbits, ngroups, group_of): (u32, usize, Vec<u32>) = match (main, o.meta) {
        (true, Some((bits, groups))) => {
            let bits = u32::from(bits);
            let bw = ceil_shr(width, bits);
            let bh = ceil_shr(height, bits);
            let mut gs: Vec<u32> = (0..mul(bw, bh))
                .map(|_| rng.below(groups as usize) as u32)
                .collect();
            if let Some(last) = gs.last_mut() {
                *last = groups.wrapping_sub(1);
            }
            w.put(1, 1);
            w.put(bits.wrapping_sub(2), 3);
            let entropy: Vec<u32> = gs
                .iter()
                .map(|&g| 0xFF00_0000 | ((g >> 8) << 16) | ((g & 0xFF) << 8))
                .collect();
            let sub = Opts {
                full_codes: o.full_codes,
                ..Opts::default()
            };
            write_image(w, rng, &entropy, bw, &sub, false);
            (bits, groups as usize, gs)
        }
        (true, None) => {
            w.put(0, 1);
            (0, 1, Vec::new())
        }
        _ => (0, 1, Vec::new()),
    };
    let group_at = |pos: usize| -> usize {
        if ngroups == 1 {
            return 0;
        }
        let x = pos.checked_rem(width).unwrap_or(0);
        let y = pos.checked_div(width).unwrap_or(0);
        let bw = ceil_shr(width, mbits);
        let i = add(mul(y.wrapping_shr(mbits), bw), x.wrapping_shr(mbits));
        at(&group_of, i) as usize
    };
    // Tokens.
    let mut toks: Vec<(usize, Tok)> = Vec::new();
    let cache_len = if o.cache_bits > 0 {
        1usize.wrapping_shl(u32::from(o.cache_bits))
    } else {
        0
    };
    let mut cache = vec![0u32; cache_len];
    let mut pos = 0usize;
    while pos < img.len() {
        let g = group_at(pos);
        let mut done = false;
        if o.lz && pos > 0 && rng.below(3) == 0 {
            for _ in 0..o.copy_tries.max(4) {
                let code = if rng.below(2) == 0 {
                    add(1, rng.below(120)) as u32
                } else {
                    add(121, rng.below(pos)) as u32
                };
                let d = dist_of(code, width);
                if d > pos {
                    continue;
                }
                let mut l = 0usize;
                while add(pos, l) < img.len()
                    && l < 4096
                    && at(img, add(pos, l)) == at(img, sub(add(pos, l), d))
                {
                    l = add(l, 1);
                }
                if l == 0 {
                    continue;
                }
                let l = add(1, rng.below(l));
                toks.push((
                    g,
                    Tok::Copy {
                        len: l as u32,
                        code,
                    },
                ));
                for k in 0..l {
                    let p = at(img, add(pos, k));
                    if !cache.is_empty() {
                        set(&mut cache, cache_key(p, o.cache_bits), p);
                    }
                }
                pos = add(pos, l);
                done = true;
                break;
            }
        }
        if done {
            continue;
        }
        let p = at(img, pos);
        if !cache.is_empty() {
            let k = cache_key(p, o.cache_bits);
            let hit = at(&cache, k) == p;
            set(&mut cache, k, p);
            if hit && rng.below(4) != 0 {
                toks.push((g, Tok::Cache(k as u32)));
                pos = add(pos, 1);
                continue;
            }
        }
        toks.push((g, Tok::Lit(p)));
        pos = add(pos, 1);
    }
    // Histograms per group and code.
    let green_n = add(280, cache_len);
    let sizes = [green_n, 256, 256, 256, 40];
    let mut hist: Vec<Vec<Vec<u32>>> = (0..ngroups)
        .map(|_| sizes.iter().map(|&n| vec![0u32; n]).collect())
        .collect();
    for &(g, t) in &toks {
        match t {
            Tok::Lit(p) => {
                bump(&mut hist, g, 0, usize::from(ch(p, 8)));
                bump(&mut hist, g, 1, usize::from(ch(p, 16)));
                bump(&mut hist, g, 2, usize::from(ch(p, 0)));
                bump(&mut hist, g, 3, usize::from(ch(p, 24)));
            }
            Tok::Cache(k) => bump(&mut hist, g, 0, add(280, k as usize)),
            Tok::Copy { len, code } => {
                bump(&mut hist, g, 0, add(256, prefix_encode(len).0 as usize));
                bump(&mut hist, g, 4, prefix_encode(code).0 as usize);
            }
        }
    }
    let none: Vec<u32> = Vec::new();
    let codes: Vec<Vec<Code>> = hist
        .iter()
        .map(|h| {
            (0..5)
                .map(|c| make_code(w, h.get(c).unwrap_or(&none), at(&sizes, c), o.full_codes))
                .collect()
        })
        .collect();
    for (g, t) in toks {
        let Some(c) = codes.get(g) else { continue };
        let emit = |w: &mut Writer, i: usize, s: u32| {
            if let Some(code) = c.get(i) {
                code.emit(w, s);
            }
        };
        match t {
            Tok::Lit(p) => {
                emit(w, 0, u32::from(ch(p, 8)));
                emit(w, 1, u32::from(ch(p, 16)));
                emit(w, 2, u32::from(ch(p, 0)));
                emit(w, 3, u32::from(ch(p, 24)));
            }
            Tok::Cache(k) => emit(w, 0, k.wrapping_add(280)),
            Tok::Copy { len, code } => {
                let (lp, le, lv) = prefix_encode(len);
                emit(w, 0, lp.wrapping_add(256));
                w.put(lv, le);
                let (dp, de, dv) = prefix_encode(code);
                emit(w, 4, dp);
                w.put(dv, de);
            }
        }
    }
}

// ---------------------------------------------------------- transforms

#[derive(Clone, Debug)]
pub enum T {
    /// Size bits, and the modes (cycled over the blocks; empty is random).
    Pred(u8, Vec<u8>),
    /// Size bits.
    Colour(u8),
    Green,
    /// The palette is taken from the image.
    Index,
}

fn avg2(a: u32, b: u32) -> u32 {
    let mut out = 0u32;
    for s in SHIFTS {
        let v = (u32::from(ch(a, s)).wrapping_add(u32::from(ch(b, s)))) / 2;
        out |= v.wrapping_shl(s);
    }
    out
}

fn clamp(v: i32) -> u32 {
    v.clamp(0, 255) as u32
}

fn per_channel(f: &dyn Fn(i32, i32, i32) -> i32, l: u32, t: u32, tl: u32) -> u32 {
    let mut out = 0u32;
    for s in SHIFTS {
        let v = f(
            i32::from(ch(l, s)),
            i32::from(ch(t, s)),
            i32::from(ch(tl, s)),
        );
        out |= clamp(v).wrapping_shl(s);
    }
    out
}

fn predict(mode: u8, l: u32, t: u32, tr: u32, tl: u32) -> u32 {
    match mode {
        1 => l,
        2 => t,
        3 => tr,
        4 => tl,
        5 => avg2(avg2(l, tr), t),
        6 => avg2(l, tl),
        7 => avg2(l, t),
        8 => avg2(tl, t),
        9 => avg2(t, tr),
        10 => avg2(avg2(l, tl), avg2(t, tr)),
        11 => {
            let (mut pl, mut pt) = (0i32, 0i32);
            for s in SHIFTS {
                let (a, b, c) = (
                    i32::from(ch(l, s)),
                    i32::from(ch(t, s)),
                    i32::from(ch(tl, s)),
                );
                let p = a.wrapping_add(b).wrapping_sub(c);
                pl = pl.wrapping_add(p.wrapping_sub(a).abs());
                pt = pt.wrapping_add(p.wrapping_sub(b).abs());
            }
            if pl < pt { l } else { t }
        }
        12 => per_channel(&|a, b, c| a.wrapping_add(b).wrapping_sub(c), l, t, tl),
        13 => {
            let a = avg2(l, t);
            per_channel(&|x, _, y| x.wrapping_add(x.wrapping_sub(y) / 2), a, a, tl)
        }
        // 0, and 14 and 15 (listed choice 8).
        _ => 0xFF00_0000,
    }
}

fn sub_px(a: u32, b: u32) -> u32 {
    let mut out = 0u32;
    for s in SHIFTS {
        out |= u32::from(ch(a, s).wrapping_sub(ch(b, s))).wrapping_shl(s);
    }
    out
}

fn delta(t: u8, c: u8) -> u8 {
    (i32::from(t as i8).wrapping_mul(i32::from(c as i8)) >> 5) as u8
}

/// Applies the forward transforms in order and writes them; returns the
/// image the entropy coder gets and its width.
fn write_transforms(
    w: &mut Writer,
    rng: &mut Rng,
    mut img: Vec<u32>,
    mut width: usize,
    ts: &[T],
    sub_opts: &Opts,
) -> Result<(Vec<u32>, usize), String> {
    let height = img.len().checked_div(width).unwrap_or(0);
    for t in ts {
        w.put(1, 1);
        match t {
            T::Pred(bits, modes) => {
                let bits = u32::from(*bits);
                w.put(0, 2);
                w.put(bits.wrapping_sub(2), 3);
                let bw = ceil_shr(width, bits);
                let bh = ceil_shr(height, bits);
                let ms: Vec<u8> = (0..mul(bw, bh))
                    .map(|i| {
                        if modes.is_empty() {
                            rng.below(14) as u8
                        } else {
                            at(modes, i.checked_rem(modes.len()).unwrap_or(0))
                        }
                    })
                    .collect();
                let mut out = img.clone();
                for y in 0..height {
                    for x in 0..width {
                        let i = add(mul(y, width), x);
                        let pred = if y == 0 && x == 0 {
                            0xFF00_0000
                        } else if y == 0 {
                            at(&img, sub(i, 1))
                        } else if x == 0 {
                            at(&img, sub(i, width))
                        } else {
                            let b = add(mul(y.wrapping_shr(bits), bw), x.wrapping_shr(bits));
                            let up = sub(i, width);
                            predict(
                                at(&ms, b),
                                at(&img, sub(i, 1)),
                                at(&img, up),
                                at(&img, add(up, 1)),
                                at(&img, sub(up, 1)),
                            )
                        };
                        set(&mut out, i, sub_px(at(&img, i), pred));
                    }
                }
                let modes_img: Vec<u32> = ms
                    .iter()
                    .map(|&m| 0xFF00_0000 | (u32::from(m) << 8))
                    .collect();
                write_image(w, rng, &modes_img, bw, sub_opts, false);
                img = out;
            }
            T::Colour(bits) => {
                let bits = u32::from(*bits);
                w.put(1, 2);
                w.put(bits.wrapping_sub(2), 3);
                let bw = ceil_shr(width, bits);
                let bh = ceil_shr(height, bits);
                // green_to_red, green_to_blue, red_to_blue
                let elems: Vec<(u8, u8, u8)> = (0..mul(bw, bh))
                    .map(|_| {
                        (
                            rng.below(256) as u8,
                            rng.below(256) as u8,
                            rng.below(256) as u8,
                        )
                    })
                    .collect();
                let mut out = img.clone();
                for y in 0..height {
                    for x in 0..width {
                        let i = add(mul(y, width), x);
                        let (g2r, g2b, r2b) = elems
                            .get(add(mul(y.wrapping_shr(bits), bw), x.wrapping_shr(bits)))
                            .copied()
                            .unwrap_or_default();
                        let p = at(&img, i);
                        let (r, g, b) = (ch(p, 16), ch(p, 8), ch(p, 0));
                        let nr = r.wrapping_sub(delta(g2r, g));
                        let nb = b.wrapping_sub(delta(g2b, g)).wrapping_sub(delta(r2b, r));
                        set(&mut out, i, px(ch(p, 24), nr, g, nb));
                    }
                }
                // Alpha 255, red red_to_blue, green green_to_blue, blue green_to_red.
                let e: Vec<u32> = elems
                    .iter()
                    .map(|&(g2r, g2b, r2b)| px(255, r2b, g2b, g2r))
                    .collect();
                write_image(w, rng, &e, bw, sub_opts, false);
                img = out;
            }
            T::Green => {
                w.put(2, 2);
                for p in &mut img {
                    let g = ch(*p, 8);
                    *p = px(
                        ch(*p, 24),
                        ch(*p, 16).wrapping_sub(g),
                        g,
                        ch(*p, 0).wrapping_sub(g),
                    );
                }
            }
            T::Index => {
                let mut pal: Vec<u32> = Vec::new();
                for &p in &img {
                    if !pal.contains(&p) {
                        pal.push(p);
                    }
                }
                if pal.len() > 256 {
                    return Err("more than 256 colours".into());
                }
                w.put(3, 2);
                w.put(sub(pal.len(), 1) as u32, 8);
                let deltas: Vec<u32> = pal
                    .iter()
                    .enumerate()
                    .map(|(i, &p)| {
                        if i == 0 {
                            p
                        } else {
                            sub_px(p, at(&pal, sub(i, 1)))
                        }
                    })
                    .collect();
                write_image(w, rng, &deltas, pal.len(), sub_opts, false);
                let bits: u32 = match pal.len() {
                    0..=2 => 3,
                    3..=4 => 2,
                    5..=16 => 1,
                    _ => 0,
                };
                let pw = ceil_shr(width, bits);
                let per = 1usize.wrapping_shl(bits);
                let bpp = 8usize.wrapping_shr(bits);
                let mut out = vec![0xFF00_0000u32; mul(pw, height)];
                for y in 0..height {
                    for x in 0..width {
                        let want = at(&img, add(mul(y, width), x));
                        let idx = pal.iter().position(|&c| c == want).unwrap_or(0) as u32;
                        let slot = x.checked_rem(per).unwrap_or(0);
                        let o = add(mul(y, pw), x.wrapping_shr(bits));
                        let shift = add(8, mul(bpp, slot)) as u32;
                        let cur = at(&out, o);
                        set(&mut out, o, cur | idx.wrapping_shl(shift));
                    }
                }
                img = out;
                width = pw;
            }
        }
    }
    w.put(0, 1);
    Ok((img, width))
}

/// A complete VP8L chunk payload for `argb` (`w` by `h`).
pub fn vp8l_payload(
    rng: &mut Rng,
    argb: &[u32],
    w: usize,
    h: usize,
    ts: &[T],
    o: &Opts,
) -> Result<Vec<u8>, String> {
    assert_eq!(argb.len(), mul(w, h));
    let mut wr = Writer::default();
    wr.put(0x2F, 8);
    wr.put(sub(w, 1) as u32, 14);
    wr.put(sub(h, 1) as u32, 14);
    wr.put(1, 1);
    wr.put(0, 3);
    let subopts = Opts {
        cache_bits: o.cache_bits.min(2),
        lz: false,
        full_codes: o.full_codes,
        ..Opts::default()
    };
    let (img, width) = write_transforms(&mut wr, rng, argb.to_vec(), w, ts, &subopts)?;
    write_image(&mut wr, rng, &img, width, o, true);
    Ok(wr.finish())
}

// ----------------------------------------------------------- containers

pub fn chunk(fourcc: &[u8; 4], payload: &[u8]) -> Vec<u8> {
    let mut v = fourcc.to_vec();
    v.extend((payload.len() as u32).to_le_bytes());
    v.extend(payload);
    if payload.len() % 2 == 1 {
        v.push(0);
    }
    v
}

pub fn riff(chunks: &[Vec<u8>]) -> Vec<u8> {
    let body: Vec<u8> = chunks.concat();
    let mut v = b"RIFF".to_vec();
    v.extend((body.len() as u32).wrapping_add(4).to_le_bytes());
    v.extend(b"WEBP");
    v.extend(body);
    v
}

fn u24(v: u32) -> [u8; 3] {
    let [a, b, c, _] = v.to_le_bytes();
    [a, b, c]
}

pub fn vp8x(flags: u8, w: u32, h: u32) -> Vec<u8> {
    let mut p = vec![flags, 0, 0, 0];
    p.extend(u24(w.wrapping_sub(1)));
    p.extend(u24(h.wrapping_sub(1)));
    chunk(b"VP8X", &p)
}

pub struct Frame {
    pub x: u32,
    pub y: u32,
    pub w: u32,
    pub h: u32,
    pub ms: u32,
    pub no_blend: bool,
    pub dispose_bg: bool,
    pub argb: Vec<u32>,
}

pub fn anmf(f: &Frame, rng: &mut Rng) -> Result<Vec<u8>, String> {
    let mut p = Vec::new();
    p.extend(u24(f.x / 2));
    p.extend(u24(f.y / 2));
    p.extend(u24(f.w.wrapping_sub(1)));
    p.extend(u24(f.h.wrapping_sub(1)));
    p.extend(u24(f.ms));
    p.push((u8::from(f.no_blend) << 1) | u8::from(f.dispose_bg));
    let payload = vp8l_payload(
        rng,
        &f.argb,
        f.w as usize,
        f.h as usize,
        &[],
        &Opts::default(),
    )?;
    p.extend(chunk(b"VP8L", &payload));
    Ok(chunk(b"ANMF", &p))
}

pub fn rgba(argb: &[u32]) -> Vec<u8> {
    argb.iter()
        .flat_map(|&p| [ch(p, 16), ch(p, 8), ch(p, 0), ch(p, 24)])
        .collect()
}

/// Random image with a few "regions" so that references and caches occur.
pub fn image(rng: &mut Rng, w: usize, h: usize, colours: usize, alpha: bool) -> Vec<u32> {
    let pal: Vec<u32> = (0..colours.max(1))
        .map(|_| {
            let a = if alpha { rng.below(256) as u32 } else { 255 };
            (a << 24) | (rng.next() as u32 & 0x00FF_FFFF)
        })
        .collect();
    let mut img: Vec<u32> = Vec::with_capacity(mul(w, h));
    for i in 0..mul(w, h) {
        let p = if i > w && rng.below(3) == 0 {
            at(&img, sub(i, w))
        } else if i > 0 && rng.below(3) == 0 {
            at(&img, sub(i, 1))
        } else {
            at(&pal, rng.below(pal.len()))
        };
        img.push(p);
    }
    img
}

// ---------------------------------------------------------------- checks

/// Decodes `file` whole and in chunks of 1, and compares with `want` and
/// with `image-webp`.
fn check(name: &str, file: &[u8], want: &[u8]) -> Result<(), String> {
    let whole = decode(file, usize::MAX, false).map_err(|e| format!("{name}: {e}"))?;
    let frame = whole
        .frames
        .first()
        .ok_or_else(|| format!("{name}: no frame, ended {:?}", whole.end))?;
    if frame.1 != want {
        let first = frame.1.iter().zip(want).position(|(a, b)| a != b);
        return Err(format!("{name}: pixels differ, first at byte {first:?}"));
    }
    let bytewise = decode(file, 1, false).map_err(|e| format!("{name}: {e}"))?;
    if bytewise != whole {
        return Err(format!("{name}: byte-at-a-time differs from whole"));
    }
    if !cfg!(miri) {
        let theirs = reference(file).map_err(|e| format!("{name}: reference: {e}"))?;
        let their_frame = theirs.frames.first().ok_or("reference has no frame")?;
        if their_frame.1 != want {
            return Err(format!(
                "{name}: image-webp disagrees with the source image"
            ));
        }
    }
    Ok(())
}

fn still(
    rng: &mut Rng,
    argb: &[u32],
    w: usize,
    h: usize,
    ts: &[T],
    o: &Opts,
) -> Result<Vec<u8>, String> {
    let payload = vp8l_payload(rng, argb, w, h, ts, o)?;
    Ok(riff(&[chunk(b"VP8L", &payload)]))
}

/// A case: its name, the file made (or why it could not be), the pixels wanted.
type Case = (String, Result<Vec<u8>, String>, Vec<u8>);

fn run(cases: Vec<Case>, suite: &str) {
    let (mut pass, mut fail) = (0usize, 0usize);
    let total = cases.len();
    let mut notes = Vec::new();
    for (name, file, want) in cases {
        match file.and_then(|f| check(&name, &f, &want)) {
            Ok(()) => pass = add(pass, 1),
            Err(e) => {
                fail = add(fail, 1);
                notes.push(e);
            }
        }
    }
    println!("clazel-conformance: suite=\"{suite}\" pass={pass} xfail=0 fail={fail} total={total}");
    assert!(notes.is_empty(), "{}", notes.join("\n"));
}

fn seeds() -> u64 {
    if cfg!(miri) { 1 } else { 6 }
}

#[test]
fn transforms_in_every_combination() {
    let orders: Vec<Vec<T>> = vec![
        vec![],
        vec![T::Green],
        vec![T::Pred(2, vec![]), T::Green],
        vec![T::Colour(3)],
        vec![T::Green, T::Colour(2), T::Pred(3, vec![])],
        vec![T::Pred(2, vec![]), T::Colour(2), T::Green],
        vec![T::Index],
        vec![T::Index, T::Pred(2, vec![])],
        vec![T::Index, T::Colour(2), T::Green],
        vec![T::Green, T::Index],
    ];
    let sizes: &[(usize, usize)] = if cfg!(miri) {
        &[(3, 2)]
    } else {
        &[(1, 1), (2, 3), (5, 4), (9, 7), (17, 9), (33, 5)]
    };
    let mut cases: Vec<Case> = Vec::new();
    for seed in 0..seeds() {
        for (oi, ts) in orders.iter().enumerate() {
            if cfg!(miri) && oi != 4 {
                continue;
            }
            for &(w, h) in sizes {
                let salt = seed
                    .wrapping_mul(7919)
                    .wrapping_add((oi as u64).wrapping_mul(31));
                let mut rng = Rng(0x1234_5678u64
                    .wrapping_add(salt)
                    .wrapping_add(mul(w, h) as u64));
                // Few colours so that indexing is possible at any position.
                let img = image(&mut rng, w, h, 6, seed % 2 == 0);
                let name = format!("order {oi} {w}x{h} seed {seed}");
                let file = still(
                    &mut rng,
                    &img,
                    w,
                    h,
                    ts,
                    &Opts {
                        cache_bits: (seed % 3) as u8 * 2,
                        lz: seed % 2 == 1,
                        ..Opts::default()
                    },
                );
                cases.push((name, file, rgba(&img)));
            }
        }
    }
    // A combination the image does not allow (an indexing after a transform
    // that makes more than 256 colours) is not a case: it is dropped.
    cases.retain(|(_, f, _)| f.is_ok());
    assert!(!cases.is_empty());
    run(cases, "WebP hand-made: transforms in combination");
}

#[test]
fn every_predictor_mode() {
    // 16 blocks of 4 by 4: the modes 0 to 13 in order, then 0 and 1 again.
    let modes: Vec<u8> = (0..14).collect();
    let (w, h) = if cfg!(miri) { (8, 4) } else { (16, 16) };
    let mut cases: Vec<Case> = Vec::new();
    for seed in 0..seeds() {
        let mut rng = Rng(77u64.wrapping_add(seed));
        let img = image(&mut rng, w, h, if seed % 2 == 0 { 200 } else { 5 }, true);
        let name = format!("modes 0..13 seed {seed}");
        let file = still(
            &mut rng,
            &img,
            w,
            h,
            &[T::Pred(2, modes.clone())],
            &Opts::default(),
        );
        cases.push((name, file, rgba(&img)));
    }
    run(cases, "WebP hand-made: every predictor mode");
}

#[test]
fn pixel_bundling_at_every_palette_size() {
    let widths: &[usize] = if cfg!(miri) {
        &[3]
    } else {
        &[1, 2, 3, 7, 8, 9, 15, 16, 17]
    };
    let sizes: &[usize] = if cfg!(miri) {
        &[3]
    } else {
        &[1, 2, 3, 4, 5, 16, 17, 100, 256]
    };
    let mut cases: Vec<Case> = Vec::new();
    for &n in sizes {
        for &w in widths {
            let mut rng = Rng(5u64.wrapping_add(add(mul(n, 100), w) as u64));
            let h = 3;
            // The palette is exactly n colours, and each appears.
            let pal: Vec<u32> = (0..n)
                .map(|i| 0xFF00_0000 | (i as u32).wrapping_mul(0x0001_0203))
                .collect();
            let mut img: Vec<u32> = (0..mul(w, h))
                .map(|i| at(&pal, add(mul(i, 7), i / 3).checked_rem(n).unwrap_or(0)))
                .collect();
            for (i, &c) in pal.iter().enumerate().take(mul(w, h)) {
                set(&mut img, i, c);
            }
            let name = format!("palette {n} width {w}");
            let file = still(&mut rng, &img, w, h, &[T::Index], &Opts::default());
            cases.push((name, file, rgba(&img)));
        }
    }
    cases.retain(|(_, f, _)| f.is_ok());
    run(cases, "WebP hand-made: colour indexing and pixel bundling");
}

#[test]
fn colour_caches_and_meta_codes() {
    let mut cases: Vec<Case> = Vec::new();
    let bits_list: Vec<u8> = if cfg!(miri) {
        vec![2]
    } else {
        (0..=11).collect()
    };
    for seed in 0..seeds() {
        for &bits in &bits_list {
            let mut rng = Rng(900u64
                .wrapping_add(seed.wrapping_mul(13))
                .wrapping_add(u64::from(bits)));
            let (w, h) = if cfg!(miri) { (5, 4) } else { (23, 19) };
            let img = image(&mut rng, w, h, 40, true);
            let meta = if seed % 2 == 0 {
                None
            } else {
                Some((2 + (seed % 3) as u8, 2 + (seed % 5) as u32))
            };
            let name = format!("cache {bits} meta {meta:?} seed {seed}");
            let file = still(
                &mut rng,
                &img,
                w,
                h,
                &[],
                &Opts {
                    cache_bits: bits,
                    meta,
                    lz: true,
                    copy_tries: 8,
                    ..Opts::default()
                },
            );
            cases.push((name, file, rgba(&img)));
        }
    }
    run(
        cases,
        "WebP hand-made: colour cache sizes and meta prefix codes",
    );
}

#[test]
fn backward_references_and_simple_codes() {
    let mut cases: Vec<Case> = Vec::new();
    for seed in 0..seeds().wrapping_mul(2) {
        let mut rng = Rng(4242u64.wrapping_add(seed));
        let (w, h) = if cfg!(miri) {
            (6, 5)
        } else {
            (add(21, (seed % 4) as usize), 17)
        };
        // Two colours and long runs: references of every kind, and simple codes.
        let img = image(&mut rng, w, h, if seed % 3 == 0 { 1 } else { 2 }, false);
        let name = format!("lz {w}x{h} seed {seed}");
        let file = still(
            &mut rng,
            &img,
            w,
            h,
            &[],
            &Opts {
                lz: true,
                copy_tries: 20,
                full_codes: seed % 4 == 3,
                ..Opts::default()
            },
        );
        cases.push((name, file, rgba(&img)));
    }
    run(
        cases,
        "WebP hand-made: backward references, simple and normal codes",
    );
}

// ------------------------------------------------------- the container

#[test]
fn still_extended_with_chunks_to_skip() -> Result<(), String> {
    let mut rng = Rng(31);
    let (w, h) = (5usize, 4usize);
    let img = image(&mut rng, w, h, 4, true);
    let payload = vp8l_payload(&mut rng, &img, w, h, &[], &Opts::default())?;
    let file = riff(&[
        vp8x(0x10 | 0x20 | 0x08, w as u32, h as u32),
        chunk(b"ICCP", &[1, 2, 3]),
        chunk(b"ALPH", &[0, 0]),
        chunk(b"VP8L", &payload),
        chunk(b"EXIF", &[9; 5]),
        chunk(b"XMP ", &[]),
        chunk(b"junk", &[7; 4]),
    ]);
    check("still VP8X", &file, &rgba(&img))?;
    // The same with data after the RIFF size: ignored.
    let mut tail = file.clone();
    tail.extend([1, 2, 3, 4, 5]);
    check("RIFF with trailing data", &tail, &rgba(&img))
}

/// The compositing rule of `lib.rs`'s listed choice 2, written again.
fn blend(src: [u8; 4], dst: [u8; 4]) -> [u8; 4] {
    let [sr, sg, sb, sa8] = src;
    let [dr, dg, db, da8] = dst;
    let (sa, da) = (u32::from(sa8), u32::from(da8));
    if sa == 0 {
        return dst;
    }
    if sa == 255 || da == 0 {
        return src;
    }
    let factor = da.wrapping_mul(256u32.wrapping_sub(sa)) >> 8;
    let ba = sa.wrapping_add(factor);
    let scale = (1u32 << 24).checked_div(ba).unwrap_or(0);
    let c = |s: u8, d: u8| {
        let sum = u32::from(s)
            .wrapping_mul(sa)
            .wrapping_add(u32::from(d).wrapping_mul(factor));
        (sum.wrapping_mul(scale) >> 24) as u8
    };
    [c(sr, dr), c(sg, dg), c(sb, db), ba as u8]
}

#[test]
fn animation_composites_frames() -> Result<(), String> {
    let (cw, chh) = (8u32, 6u32);
    let mut rng = Rng(555);
    let mk =
        |rng: &mut Rng, w: u32, h: u32, alpha: bool| image(rng, w as usize, h as usize, 3, alpha);
    let f = |x, y, w, h, ms, no_blend, dispose_bg, argb| Frame {
        x,
        y,
        w,
        h,
        ms,
        no_blend,
        dispose_bg,
        argb,
    };
    let mut frames = vec![
        f(0, 0, cw, chh, 10, true, false, mk(&mut rng, cw, chh, false)),
        f(2, 2, 4, 3, 20, false, true, mk(&mut rng, 4, 3, true)),
        f(4, 0, 3, 6, 30, false, false, mk(&mut rng, 3, 6, true)),
        f(0, 4, 6, 2, 40, true, true, mk(&mut rng, 6, 2, true)),
        f(2, 2, 2, 2, 50, false, false, mk(&mut rng, 2, 2, true)),
    ];
    if cfg!(miri) {
        frames.truncate(2);
    }
    let mut chunks = vec![vp8x(0x02 | 0x10, cw, chh)];
    let mut anim = vec![1, 2, 3, 4];
    anim.extend(7u16.to_le_bytes());
    chunks.push(chunk(b"ANIM", &anim));
    for fr in &frames {
        chunks.push(anmf(fr, &mut rng)?);
    }
    chunks.push(chunk(b"EXIF", &[1, 2, 3]));
    let file = riff(&chunks);
    let got = decode(&file, usize::MAX, false)?;
    if got.end != End::Trailer || got.frames.len() != frames.len() {
        return Err(format!("{} frames, ended {:?}", got.frames.len(), got.end));
    }
    // Expected canvases, composited here.
    let mut canvas = vec![[0u8; 4]; mul(cw as usize, chh as usize)];
    let mut prev: Option<&Frame> = None;
    for (i, fr) in frames.iter().enumerate() {
        if let Some(p) = prev
            && p.dispose_bg
        {
            for y in p.y..p.y.wrapping_add(p.h) {
                for x in p.x..p.x.wrapping_add(p.w) {
                    set(
                        &mut canvas,
                        add(mul(y as usize, cw as usize), x as usize),
                        [0; 4],
                    );
                }
            }
        }
        for y in 0..fr.h {
            for x in 0..fr.w {
                let s = at(&fr.argb, add(mul(y as usize, fr.w as usize), x as usize));
                let src = [ch(s, 16), ch(s, 8), ch(s, 0), ch(s, 24)];
                let cx = fr.x.wrapping_add(x) as usize;
                let cy = fr.y.wrapping_add(y) as usize;
                let to = add(mul(cy, cw as usize), cx);
                let old = at(&canvas, to);
                set(
                    &mut canvas,
                    to,
                    if fr.no_blend { src } else { blend(src, old) },
                );
            }
        }
        let want: Vec<u8> = canvas.iter().flatten().copied().collect();
        let (info, pixels) = got.frames.get(i).ok_or("a frame is missing")?;
        if *pixels != want {
            return Err(format!("frame {i}: canvas differs"));
        }
        let info = info.ok_or("no frame facts")?;
        if (
            info.left,
            info.top,
            info.width,
            info.height,
            info.duration_ms,
        ) != (fr.x, fr.y, fr.w, fr.h, fr.ms)
        {
            return Err(format!("frame {i}: facts {info:?}"));
        }
        prev = Some(fr);
    }
    // In chunks of 1 with empty chunks between, the same.
    if decode(&file, 1, true)? != got {
        return Err("chunked animation differs".into());
    }
    Ok(())
}

fn error_of(file: &[u8]) -> Result<String, String> {
    match decode(file, usize::MAX, false) {
        Ok(d) => match d.end {
            End::Error(e) => Ok(e),
            other => Err(format!("no error: {other:?}, {} frames", d.frames.len())),
        },
        Err(e) => Ok(e),
    }
}

/// `(name, file, text the error must mention)`.
type Bad = (&'static str, Vec<u8>, &'static str);

#[test]
fn malformed_files_are_errors() -> Result<(), String> {
    let mut rng = Rng(9);
    let (w, h) = (4usize, 3usize);
    let img = image(&mut rng, w, h, 3, false);
    let payload = vp8l_payload(&mut rng, &img, w, h, &[], &Opts::default())?;
    let good = riff(&[chunk(b"VP8L", &payload)]);
    check("the good file", &good, &rgba(&img))?;
    let with = |f: &dyn Fn(&mut Vec<u8>)| {
        let mut p = payload.clone();
        f(&mut p);
        riff(&[chunk(b"VP8L", &p)])
    };
    let short = payload
        .get(..payload.len().saturating_sub(3))
        .unwrap_or(&[]);
    // The RIFF size claims less than the chunk holds.
    let mut cut = good.clone();
    for (i, b) in 20u32.to_le_bytes().iter().enumerate() {
        set(&mut cut, add(4, i), *b);
    }
    let cases: Vec<Bad> = vec![
        (
            "bad signature byte",
            with(&|p| set(p, 0, 0x2E)),
            "signature",
        ),
        (
            "version 1",
            with(&|p| {
                let v = at(p, 4) | 0x20;
                set(p, 4, v);
            }),
            "version",
        ),
        ("truncated data", riff(&[chunk(b"VP8L", short)]), "ends"),
        ("a chunk past the RIFF end", cut, "past"),
        (
            "lossy",
            riff(&[chunk(
                b"VP8 ",
                &[0x10, 0, 0, 0x9D, 0x01, 0x2A, 4, 0, 3, 0, 0, 0],
            )]),
            "Unsupported",
        ),
        (
            "VP8X canvas disagrees",
            riff(&[vp8x(0, 5, 3), chunk(b"VP8L", &payload)]),
            "size its container says",
        ),
        (
            "no image",
            riff(&[vp8x(0, 4, 3), chunk(b"EXIF", &[1, 2])]),
            "no image",
        ),
        (
            "animation flag without ANIM",
            riff(&[vp8x(2, 4, 3), chunk(b"VP8L", &payload)]),
            "outside a frame",
        ),
    ];
    for (name, file, needle) in cases {
        let e = error_of(&file)?;
        if !e.contains(needle) {
            return Err(format!("{name}: error {e:?} does not mention {needle:?}"));
        }
    }
    Ok(())
}

#[test]
fn malformed_streams_are_errors() -> Result<(), String> {
    // Streams a decoder must refuse, written bit by bit.
    let hdr = |w: &mut Writer| {
        w.put(0x2F, 8);
        w.put(1, 14);
        w.put(1, 14);
        w.put(0, 4);
    };
    let wrap = |w: Writer| riff(&[chunk(b"VP8L", &w.finish())]);
    let mut cases: Vec<Bad> = Vec::new();
    // The same transform twice.
    let mut w = Writer::default();
    hdr(&mut w);
    w.put(1, 1);
    w.put(2, 2);
    w.put(1, 1);
    w.put(2, 2);
    cases.push(("transform twice", wrap(w), "twice"));
    // Colour cache of 12 bits (and of 0 bits).
    for (bits, name) in [(12u32, "cache 12"), (0, "cache 0")] {
        let mut w = Writer::default();
        hdr(&mut w);
        w.put(0, 1);
        w.put(1, 1);
        w.put(bits, 4);
        cases.push((name, wrap(w), "colour cache"));
    }
    // A normal code with 4 code length codes all of length 0.
    let mut w = Writer::default();
    hdr(&mut w);
    w.put(0, 1); // no transform
    w.put(0, 1); // no cache
    w.put(0, 1); // no meta
    w.put(0, 1); // normal code
    w.put(0, 4); // 4 code lengths
    w.put(0, 12);
    cases.push(("empty code length code", wrap(w), "code length code"));
    for (name, file, needle) in cases {
        let e = error_of(&file)?;
        if !e.contains(needle) {
            return Err(format!("{name}: error {e:?} does not mention {needle:?}"));
        }
    }
    Ok(())
}

/// Modes 14 and 15, which RFC 9649 does not define, predict like mode 0
/// (listed choice 8, libwebp's); `image-webp` does not, so only ours is asked.
#[test]
fn undefined_predictor_modes_are_black() -> Result<(), String> {
    let (w, h) = (8usize, 4usize);
    let mut rng = Rng(14);
    let img = image(&mut rng, w, h, 5, true);
    let a = still(
        &mut rng,
        &img,
        w,
        h,
        &[T::Pred(2, vec![14, 15])],
        &Opts::default(),
    )?;
    let got = decode(&a, usize::MAX, false)?;
    let frame = got.frames.first().ok_or("no frame")?;
    if frame.1 != rgba(&img) {
        return Err("modes 14 and 15 do not predict like mode 0".into());
    }
    Ok(())
}
