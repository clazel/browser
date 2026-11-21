//! Shared by the tests: a random generator, streams made by `miniz_oxide`'s
//! compressor and by hand (a bit writer and the fixed codes of RFC 1951
//! §3.2.6, so every length code, every distance code and stored blocks are
//! covered), and the zlib wrapper. Written to the workspace's lints (no
//! indexing, no unchecked arithmetic) like everything else.

/// The element of `s` at `i`, or `default`.
pub fn at<T: Copy>(s: &[T], i: usize, default: T) -> T {
    s.get(i).copied().unwrap_or(default)
}

/// xorshift64*: deterministic pseudo-random numbers.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 11
    }

    /// A number below `n` (which must not be 0).
    pub fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next())
            .unwrap_or(0)
            .checked_rem(n)
            .unwrap_or(0)
    }
}

/// Adler-32 (RFC 1950 §8.2), written again here.
pub fn adler32(data: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    for &x in data {
        a = a.wrapping_add(u32::from(x)) % 65521;
        b = b.wrapping_add(a) % 65521;
    }
    (b << 16) | a
}

/// A raw DEFLATE stream as a zlib stream (CMF 0x78, FLG 0x9C) for `out`.
pub fn zlib_wrap(raw: &[u8], out: &[u8]) -> Vec<u8> {
    let mut v = vec![0x78, 0x9C];
    v.extend_from_slice(raw);
    v.extend_from_slice(&adler32(out).to_be_bytes());
    v
}

/// The canonical code of RFC 1951 §3.2.2 for `lens`, as `(code, length)` per
/// symbol, written from the RFC's pseudo-code (a different shape from
/// `src/huffman.rs`: arrays indexed by length, as the RFC has them).
pub fn canonical(lens: &[u32]) -> Vec<(u32, u32)> {
    let mut bl_count = vec![0u32; 16];
    for &l in lens {
        if let Some(c) = bl_count.get_mut(l as usize).filter(|_| l > 0) {
            *c = c.wrapping_add(1);
        }
    }
    let mut next_code = vec![0u32; 17];
    let mut code = 0u32;
    for bits in 1..=15usize {
        code = code.wrapping_add(at(&bl_count, bits.wrapping_sub(1), 0)) << 1;
        if let Some(n) = next_code.get_mut(bits) {
            *n = code;
        }
    }
    lens.iter()
        .map(|&l| {
            if l == 0 {
                (0, 0)
            } else {
                let c = at(&next_code, l as usize, 0);
                if let Some(n) = next_code.get_mut(l as usize) {
                    *n = n.wrapping_add(1);
                }
                (c, l)
            }
        })
        .collect()
}

/// Writes bits least significant first (RFC 1951 §3.1.1).
#[derive(Default)]
pub struct BitWriter {
    pub bytes: Vec<u8>,
    used: u32,
}

impl BitWriter {
    pub fn new() -> BitWriter {
        BitWriter::default()
    }

    /// A data element: `n` bits of `v`, least significant first.
    pub fn bits(&mut self, v: u32, n: u32) {
        for i in 0..n {
            if self.used == 0 {
                self.bytes.push(0);
            }
            let set = (v >> i) & 1 == 1;
            if let Some(b) = self.bytes.last_mut().filter(|_| set) {
                *b |= 1 << self.used;
            }
            self.used = self.used.wrapping_add(1) % 8;
        }
    }

    /// A Huffman code: `n` bits of `code`, most significant first.
    pub fn code(&mut self, code: u32, n: u32) {
        for i in (0..n).rev() {
            self.bits((code >> i) & 1, 1);
        }
    }

    /// Skip to the next byte boundary.
    pub fn align(&mut self) {
        self.used = 0;
    }

    /// Whole bytes, at the next byte boundary.
    pub fn raw(&mut self, data: &[u8]) {
        self.align();
        self.bytes.extend_from_slice(data);
    }

    /// RFC 1951 §3.2.6's literal/length code for symbol `s`.
    pub fn fixed_lit(&mut self, s: u32) {
        match s {
            0..=143 => self.code(0x30u32.wrapping_add(s), 8),
            144..=255 => self.code(0x190u32.wrapping_add(s.wrapping_sub(144)), 9),
            256..=279 => self.code(s.wrapping_sub(256), 7),
            _ => self.code(0xC0u32.wrapping_add(s.wrapping_sub(280)), 8),
        }
    }

    /// A match in a fixed block: `length` 3 to 258, `distance` 1 to 32768.
    pub fn fixed_match(&mut self, length: u32, distance: u32) {
        let (sym, extra_bits, extra) = length_code(length);
        self.fixed_lit(sym);
        self.bits(extra, extra_bits);
        let (d, d_bits, d_extra) = distance_code(distance);
        self.code(d, 5);
        self.bits(d_extra, d_bits);
    }

    /// The header of a dynamic block (RFC 1951 §3.2.7) for these code
    /// lengths, with the code length alphabet using no repeat codes: the
    /// distinct lengths get a complete code (at most 4 of them).
    pub fn dynamic_header(&mut self, last: bool, lit: &[u32], dist: &[u32]) {
        self.bits(u32::from(last), 1);
        self.bits(2, 2);
        self.bits(lit.len().saturating_sub(257) as u32, 5);
        self.bits(dist.len().saturating_sub(1) as u32, 5);
        self.bits(15, 4);
        let mut used: Vec<u32> = lit.iter().chain(dist).copied().collect();
        used.sort_unstable();
        used.dedup();
        let shape: &[u32] = match used.len() {
            2 => &[1, 1],
            3 => &[1, 2, 2],
            _ => &[2, 2, 2, 2],
        };
        let mut cl = vec![0u32; 19];
        for (v, l) in used.iter().zip(shape) {
            if let Some(slot) = cl.get_mut(*v as usize) {
                *slot = *l;
            }
        }
        for sym in [
            16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
        ] {
            self.bits(at(&cl, sym, 0), 3);
        }
        let codes = canonical(&cl);
        for &l in lit.iter().chain(dist) {
            let (c, n) = at(&codes, l as usize, (0, 0));
            self.code(c, n);
        }
    }
}

/// The length code for `length` (RFC 1951 §3.2.5): symbol, extra bits, value.
pub fn length_code(length: u32) -> (u32, u32, u32) {
    let base: [u32; 29] = [
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
        131, 163, 195, 227, 258,
    ];
    let extra: [u32; 29] = [
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
    ];
    let i = (0..29)
        .rev()
        .find(|&i| at(&base, i, u32::MAX) <= length)
        .unwrap_or(0);
    (
        257u32.wrapping_add(i as u32),
        at(&extra, i, 0),
        length.wrapping_sub(at(&base, i, 0)),
    )
}

/// The distance code for `distance`: code, extra bits, value.
pub fn distance_code(distance: u32) -> (u32, u32, u32) {
    let base: [u32; 30] = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
        2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
    ];
    let extra: [u32; 30] = [
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
        13, 13,
    ];
    let i = (0..30)
        .rev()
        .find(|&i| at(&base, i, u32::MAX) <= distance)
        .unwrap_or(0);
    (
        i as u32,
        at(&extra, i, 0),
        distance.wrapping_sub(at(&base, i, 0)),
    )
}

/// Append a match to `out` as RFC 1951 §3.2.3 says (overlap allowed).
pub fn lz(out: &mut Vec<u8>, length: usize, distance: usize) {
    for _ in 0..length {
        let b = at(out, out.len().saturating_sub(distance), 0);
        out.push(b);
    }
}

/// One hand-made stream: its name, the stream and what it decodes to.
pub type Made = (String, Vec<u8>, Vec<u8>);

/// Hand-made raw streams and what they decode to.
pub fn handmade() -> Vec<Made> {
    let mut all = Vec::new();

    // Every length 3 to 258 against every distance code's smallest and
    // largest distance, in one fixed block after 32,768 literals. Not under
    // Miri (an interpreter): 130 KiB of output is far too slow there, and
    // the normal test job runs it (docs/VERIFICATION.md, Miri).
    if !cfg!(miri) {
        let mut w = BitWriter::new();
        w.bits(1, 1);
        w.bits(1, 2);
        let mut out = Vec::new();
        let mut rng = Rng::new(7);
        for _ in 0..32768 {
            let b = rng.below(256) as u8;
            w.fixed_lit(u32::from(b));
            out.push(b);
        }
        let dists: Vec<u32> = vec![
            1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 17, 24, 25, 32, 33, 48, 49, 64, 65, 96, 97, 128,
            129, 192, 193, 256, 257, 384, 385, 512, 513, 768, 769, 1024, 1025, 1536, 1537, 2048,
            2049, 3072, 3073, 4096, 4097, 6144, 6145, 8192, 8193, 12288, 12289, 16384, 16385,
            24576, 24577, 32768,
        ];
        for length in 3u32..=258 {
            for k in 0..3usize {
                let d = at(
                    &dists,
                    (length as usize)
                        .wrapping_mul(3)
                        .wrapping_add(k.wrapping_mul(17))
                        .checked_rem(dists.len())
                        .unwrap_or(0),
                    1,
                );
                w.fixed_match(length, d);
                lz(&mut out, length as usize, d as usize);
            }
        }
        w.fixed_lit(256);
        all.push((
            "fixed: every length and distance code".to_owned(),
            w.bytes,
            out,
        ));
    }

    // Stored blocks: empty, 1 byte after a fixed block (so the header is not
    // byte aligned), 65,535 bytes (300 under Miri, for speed), and the last
    // one empty.
    {
        let mut w = BitWriter::new();
        let mut out = Vec::new();
        w.bits(0, 1);
        w.bits(0, 2);
        w.raw(&[0, 0, 0xFF, 0xFF]);
        w.bits(0, 1);
        w.bits(1, 2);
        for c in b"abc" {
            w.fixed_lit(u32::from(*c));
            out.push(*c);
        }
        w.fixed_lit(256);
        w.bits(0, 1);
        w.bits(0, 2);
        w.raw(&[1, 0, 0xFE, 0xFF, b'z']);
        out.push(b'z');
        let mut rng = Rng::new(11);
        let len: u16 = if cfg!(miri) { 300 } else { 65535 };
        let big: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
        let [lo, hi] = len.to_le_bytes();
        w.align();
        w.bits(0, 1);
        w.bits(0, 2);
        w.raw(&[lo, hi, !lo, !hi]);
        w.raw(&big);
        out.extend_from_slice(&big);
        w.align();
        w.bits(1, 1);
        w.bits(0, 2);
        w.raw(&[0, 0, 0xFF, 0xFF]);
        all.push(("stored blocks".to_owned(), w.bytes, out));
    }

    // The empty final fixed block.
    {
        let mut w = BitWriter::new();
        w.bits(1, 1);
        w.bits(1, 2);
        w.fixed_lit(256);
        all.push(("empty fixed block".to_owned(), w.bytes, Vec::new()));
    }

    // Overlapping matches: distance 1 and 2, length 258, from a short start.
    {
        let mut w = BitWriter::new();
        w.bits(1, 1);
        w.bits(1, 2);
        let mut out = Vec::new();
        for c in b"ab" {
            w.fixed_lit(u32::from(*c));
            out.push(*c);
        }
        for (l, d) in [(258u32, 2u32), (258, 1), (3, 1), (100, 2)] {
            w.fixed_match(l, d);
            lz(&mut out, l as usize, d as usize);
        }
        w.fixed_lit(256);
        all.push(("fixed: overlapping matches".to_owned(), w.bytes, out));
    }

    // A dynamic block with a hand-made code: 'a' 1 bit, 'b' and the end of
    // block 2 bits, one length symbol (257) of 3 bits would make it
    // incomplete, so the code is a (1,2,3,3): 'a', 'b', 256, 257.
    {
        let mut lit = vec![0u32; 258];
        if let Some(x) = lit.get_mut(97) {
            *x = 1;
        }
        if let Some(x) = lit.get_mut(98) {
            *x = 2;
        }
        if let Some(x) = lit.get_mut(256) {
            *x = 3;
        }
        if let Some(x) = lit.get_mut(257) {
            *x = 3;
        }
        let dist = vec![1u32, 1];
        let mut w = BitWriter::new();
        w.dynamic_header(true, &lit, &dist);
        let lc = canonical(&lit);
        let dc = canonical(&dist);
        let mut out = Vec::new();
        for s in [97usize, 98, 97, 97] {
            let (c, n) = at(&lc, s, (0, 0));
            w.code(c, n);
            out.push(s as u8);
        }
        // A match of length 3 at distance 2 (distance code 1).
        let (c, n) = at(&lc, 257, (0, 0));
        w.code(c, n);
        let (c, n) = at(&dc, 1, (0, 0));
        w.code(c, n);
        lz(&mut out, 3, 2);
        let (c, n) = at(&lc, 256, (0, 0));
        w.code(c, n);
        all.push(("dynamic: hand-made code".to_owned(), w.bytes, out));
    }
    all
}

/// Some data, deterministic: `kind` picks the shape.
pub fn sample(kind: usize, n: usize) -> Vec<u8> {
    let words = [
        "the ", "quick ", "brown ", "fox ", "jumps ", "over ", "a ", "lazy ", "dog\n", "and ",
        "then ", "some ", "more ", "words ", "to ", "make ", "text ",
    ];
    let mut rng = Rng::new((kind as u64).wrapping_add(100));
    let mut v = Vec::new();
    match kind {
        0 => {
            while v.len() < n {
                v.extend_from_slice(at(&words, rng.below(words.len()), "").as_bytes());
            }
        }
        1 => v = vec![0; n],
        2 => v = (0..n).map(|_| rng.next() as u8).collect(),
        3 => {
            while v.len() < n {
                v.extend_from_slice(b"abcabcabd");
            }
        }
        _ => {
            while v.len() < n {
                let b = (rng.below(4) as u8).wrapping_add(b'a');
                let run = 1usize.wrapping_add(rng.below(40));
                v.extend(std::iter::repeat_n(b, run));
            }
        }
    }
    v.truncate(n);
    v
}

/// What the corpus holds: `(name, data, level)`. Under Miri (an
/// interpreter) only the 100-byte inputs at level 6, for speed; the
/// normal test job compresses all of them (docs/VERIFICATION.md, Miri).
fn corpus_inputs() -> Vec<(String, Vec<u8>, u8)> {
    let sizes: &[usize] = if cfg!(miri) {
        &[100]
    } else {
        &[0, 1, 100, 3000]
    };
    let levels: &[u8] = if cfg!(miri) { &[6] } else { &[0, 1, 6, 9] };
    let mut v = Vec::new();
    for kind in 0..5usize {
        for &n in sizes {
            for &level in levels {
                v.push((
                    format!("kind {kind} n {n} level {level}"),
                    sample(kind, n),
                    level,
                ));
            }
        }
    }
    v
}

/// Raw streams from `miniz_oxide`'s compressor, under 5,000 bytes.
pub fn corpus_raw() -> Vec<(String, Vec<u8>)> {
    corpus_inputs()
        .into_iter()
        .map(|(name, data, level)| (name, miniz_oxide::deflate::compress_to_vec(&data, level)))
        .filter(|(_, s)| s.len() < 5000)
        .collect()
}

/// Zlib streams from `miniz_oxide`'s compressor, under 5,000 bytes.
pub fn corpus_zlib() -> Vec<(String, Vec<u8>)> {
    corpus_inputs()
        .into_iter()
        .filter(|(_, data, _)| data.len() == 100 || data.len() == 3000)
        .map(|(name, data, level)| {
            (
                format!("zlib {name}"),
                miniz_oxide::deflate::compress_to_vec_zlib(&data, level),
            )
        })
        .filter(|(_, s)| s.len() < 5000)
        .collect()
}

/// The corpus with its data: `(name, raw stream, data)`.
pub fn corpus_with_data() -> Vec<Made> {
    corpus_inputs()
        .into_iter()
        .map(|(name, data, level)| {
            let raw = miniz_oxide::deflate::compress_to_vec(&data, level);
            (name, raw, data)
        })
        .collect()
}
