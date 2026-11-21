//! A naive transcription of `src/spec.rs` in plain Rust: one function per
//! spec function, in the spec's order, written without looking at
//! `src/stream.rs` or `src/huffman.rs`. The only departure from the spec's
//! form is that the canonical code of each symbol is computed once per code
//! (`Code::new`) instead of by recounting the symbols before it at every
//! lookup: `code_of(n)` is `next_code[len]` plus the number of symbols before
//! `n` of the same length, which is the same number. Loops stand in for the
//! spec's fuel. It is slow, so the tests run it on small inputs.

use clazel_deflate::spec::Error;

/// The output and the number of bytes the stream occupies.
pub type Out = Result<(Vec<u8>, usize), Error>;

fn add(a: usize, b: usize) -> usize {
    a.saturating_add(b)
}

fn mul(a: usize, b: usize) -> usize {
    a.saturating_mul(b)
}

fn pow2(n: usize) -> usize {
    1usize.checked_shl(n as u32).unwrap_or(usize::MAX)
}

fn at<T: Copy>(s: &[T], i: usize, default: T) -> T {
    s.get(i).copied().unwrap_or(default)
}

/// `bit_at`: bit `pos` of the stream, first bit of each byte least significant.
fn bit_at(input: &[u8], pos: usize) -> usize {
    usize::from(at(input, pos / 8, 0))
        .checked_div(pow2(pos % 8))
        .unwrap_or(0)
        % 2
}

/// `bits_value`: the first bit read is the least significant.
fn bits_value(input: &[u8], pos: usize, n: usize) -> usize {
    let mut v = 0;
    let mut i = 0;
    while i < n {
        v = add(v, mul(bit_at(input, add(pos, i)), pow2(i)));
        i = add(i, 1);
    }
    v
}

/// `read_bits`: `None` if the input ends first.
fn read_bits(input: &[u8], pos: usize, n: usize) -> Option<(usize, usize)> {
    if add(pos, n) > mul(input.len(), 8) {
        None
    } else {
        Some((bits_value(input, pos, n), add(pos, n)))
    }
}

/// `Sym`.
pub enum Sym {
    Found(usize, usize),
    Truncated,
    Invalid,
}

/// The canonical code of §3.2.2 for a list of lengths.
pub struct Code {
    lens: Vec<usize>,
    /// `code_of(lens, n)` for every `n` (meaningful where it has a length).
    codes: Vec<usize>,
}

fn count_eq(lens: &[usize], v: usize, n: usize) -> usize {
    lens.iter().take(n).filter(|&&l| l == v).count()
}

fn bl_count(lens: &[usize], bits: usize) -> usize {
    if bits == 0 {
        0
    } else {
        count_eq(lens, bits, lens.len())
    }
}

fn next_code(lens: &[usize], bits: usize) -> usize {
    let mut code = 0;
    let mut b = 1;
    while b <= bits {
        code = mul(add(code, bl_count(lens, b.saturating_sub(1))), 2);
        b = add(b, 1);
    }
    code
}

impl Code {
    pub fn new(lens: &[usize]) -> Code {
        let codes = (0..lens.len())
            .map(|n| {
                let l = at(lens, n, 0);
                add(next_code(lens, l), count_eq(lens, l, n))
            })
            .collect();
        Code {
            lens: lens.to_vec(),
            codes,
        }
    }

    fn find_code(&self, len: usize, code: usize) -> Option<usize> {
        (0..self.lens.len()).find(|&i| at(&self.lens, i, 0) == len && at(&self.codes, i, 0) == code)
    }

    /// `decode_symbol`.
    pub fn decode(&self, input: &[u8], pos: usize) -> Sym {
        let mut p = pos;
        let mut len = 0;
        let mut code = 0;
        loop {
            if len >= 15 {
                return Sym::Invalid;
            }
            if p >= mul(input.len(), 8) {
                return Sym::Truncated;
            }
            code = add(mul(code, 2), bit_at(input, p));
            if let Some(s) = self.find_code(add(len, 1), code) {
                return Sym::Found(s, add(p, 1));
            }
            p = add(p, 1);
            len = add(len, 1);
        }
    }
}

fn kraft(lens: &[usize]) -> usize {
    (1..=15usize).fold(0, |s, k| {
        add(s, mul(bl_count(lens, k), pow2(15usize.saturating_sub(k))))
    })
}

fn used(lens: &[usize]) -> usize {
    lens.len().saturating_sub(count_eq(lens, 0, lens.len()))
}

/// `code_usable`.
pub fn code_usable(lens: &[usize], allow_incomplete: bool) -> bool {
    lens.iter().all(|&l| l <= 15)
        && (kraft(lens) == pow2(15)
            || (allow_incomplete
                && (used(lens) == 0 || (used(lens) == 1 && bl_count(lens, 1) == 1))))
}

fn len_extra(code: usize) -> usize {
    match code {
        257..=264 => 0,
        265..=268 => 1,
        269..=272 => 2,
        273..=276 => 3,
        277..=280 => 4,
        281..=284 => 5,
        _ => 0,
    }
}

fn len_base(code: usize) -> usize {
    let t = [
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
        131, 163, 195, 227, 258,
    ];
    code.checked_sub(257).map_or(0, |i| at(&t, i, 0))
}

fn dist_extra(code: usize) -> usize {
    match code {
        0..=3 => 0,
        4 | 5 => 1,
        6 | 7 => 2,
        8 | 9 => 3,
        10 | 11 => 4,
        12 | 13 => 5,
        14 | 15 => 6,
        16 | 17 => 7,
        18 | 19 => 8,
        20 | 21 => 9,
        22 | 23 => 10,
        24 | 25 => 11,
        26 | 27 => 12,
        28 | 29 => 13,
        _ => 0,
    }
}

fn dist_base(code: usize) -> usize {
    let t = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
        2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
    ];
    at(&t, code, 0)
}

/// `fixed_lit_lengths`.
pub fn fixed_lit_lengths() -> Vec<usize> {
    (0..288)
        .map(|s| match s {
            0..=143 => 8,
            144..=255 => 9,
            256..=279 => 7,
            _ => 8,
        })
        .collect()
}

/// `lz_copy`, with `distance` in `1..=out.len()`.
fn lz_copy(out: &mut Vec<u8>, distance: usize, length: usize) {
    for _ in 0..length {
        let b = at(out, out.len().saturating_sub(distance), 0);
        out.push(b);
    }
}

type Block = Result<(usize, Vec<u8>), Error>;

/// `data_loop`.
fn data_loop(
    input: &[u8],
    pos: usize,
    out: Vec<u8>,
    limit: usize,
    lit: &Code,
    dist: &Code,
) -> Block {
    let mut out = out;
    let mut pos = pos;
    loop {
        let (sym, p1) = match lit.decode(input, pos) {
            Sym::Truncated => return Err(Error::Truncated),
            Sym::Invalid => return Err(Error::InvalidCode),
            Sym::Found(s, p) => (s, p),
        };
        if sym < 256 {
            if add(out.len(), 1) > limit {
                return Err(Error::OutputLimit);
            }
            out.push(sym as u8);
            pos = p1;
        } else if sym == 256 {
            return Ok((p1, out));
        } else if sym > 285 {
            return Err(Error::InvalidSymbol);
        } else {
            let (e, p2) = read_bits(input, p1, len_extra(sym)).ok_or(Error::Truncated)?;
            let length = add(len_base(sym), e);
            let (d, p3) = match dist.decode(input, p2) {
                Sym::Truncated => return Err(Error::Truncated),
                Sym::Invalid => return Err(Error::InvalidCode),
                Sym::Found(d, p) => (d, p),
            };
            if d > 29 {
                return Err(Error::InvalidDistanceSymbol);
            }
            let (e2, p4) = read_bits(input, p3, dist_extra(d)).ok_or(Error::Truncated)?;
            let distance = add(dist_base(d), e2);
            if distance > out.len() {
                return Err(Error::DistanceTooFar);
            }
            if add(out.len(), length) > limit {
                return Err(Error::OutputLimit);
            }
            lz_copy(&mut out, distance, length);
            pos = p4;
        }
    }
}

/// `stored_block`.
fn stored_block(input: &[u8], pos: usize, out: Vec<u8>, limit: usize) -> Block {
    let start = add(pos, 7) / 8;
    if add(start, 4) > input.len() {
        return Err(Error::Truncated);
    }
    let byte = |k: usize| usize::from(at(input, add(start, k), 0));
    let len = add(byte(0), mul(256, byte(1)));
    let nlen = add(byte(2), mul(256, byte(3)));
    if add(len, nlen) != 65535 {
        Err(Error::LengthComplementMismatch)
    } else if add(out.len(), len) > limit {
        Err(Error::OutputLimit)
    } else if add(add(start, 4), len) > input.len() {
        Err(Error::Truncated)
    } else {
        let mut out = out;
        let from = add(start, 4);
        out.extend_from_slice(input.get(from..add(from, len)).unwrap_or(&[]));
        Ok((mul(add(from, len), 8), out))
    }
}

const CL_ORDER: [usize; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

type Tables = (Vec<usize>, Vec<usize>, usize);

/// `read_dynamic_tables`: the two lists of lengths and the position after them.
fn read_dynamic_tables(input: &[u8], pos: usize) -> Result<Tables, Error> {
    let (hlit_field, p1) = read_bits(input, pos, 5).ok_or(Error::Truncated)?;
    let (hdist_field, p2) = read_bits(input, p1, 5).ok_or(Error::Truncated)?;
    let (hclen_field, p3) = read_bits(input, p2, 4).ok_or(Error::Truncated)?;
    let hlit = add(hlit_field, 257);
    let hdist = add(hdist_field, 1);
    let hclen = add(hclen_field, 4);
    if hlit > 286 {
        return Err(Error::TooManyLengthCodes);
    }
    let mut cl = vec![0usize; 19];
    let mut p = p3;
    for i in 0..hclen {
        let (v, np) = read_bits(input, p, 3).ok_or(Error::Truncated)?;
        if let Some(slot) = cl.get_mut(at(&CL_ORDER, i, 0)) {
            *slot = v;
        }
        p = np;
    }
    if !code_usable(&cl, false) {
        return Err(Error::BadCodeLengths);
    }
    let cl_code = Code::new(&cl);
    let total = add(hlit, hdist);
    let mut acc: Vec<usize> = Vec::new();
    while acc.len() < total {
        let (sym, p1) = match cl_code.decode(input, p) {
            Sym::Truncated => return Err(Error::Truncated),
            Sym::Invalid => return Err(Error::InvalidCode),
            Sym::Found(s, q) => (s, q),
        };
        if sym < 16 {
            acc.push(sym);
            p = p1;
        } else if sym == 16 {
            let Some(&prev) = acc.last() else {
                return Err(Error::RepeatWithoutPrevious);
            };
            let (e, p2) = read_bits(input, p1, 2).ok_or(Error::Truncated)?;
            if add(acc.len(), add(3, e)) > total {
                return Err(Error::RepeatTooLong);
            }
            acc.extend(std::iter::repeat_n(prev, add(3, e)));
            p = p2;
        } else {
            let (bits, base) = if sym == 17 { (3, 3) } else { (7, 11) };
            let (e, p2) = read_bits(input, p1, bits).ok_or(Error::Truncated)?;
            if add(acc.len(), add(base, e)) > total {
                return Err(Error::RepeatTooLong);
            }
            acc.extend(std::iter::repeat_n(0, add(base, e)));
            p = p2;
        }
    }
    let lit: Vec<usize> = acc.iter().take(hlit).copied().collect();
    let dist: Vec<usize> = acc.iter().skip(hlit).take(hdist).copied().collect();
    if at(&lit, 256, 0) == 0 {
        Err(Error::NoEndOfBlock)
    } else if !code_usable(&lit, true) || !code_usable(&dist, true) {
        Err(Error::BadCodeLengths)
    } else {
        Ok((lit, dist, p))
    }
}

/// `inflate`.
pub fn inflate(input: &[u8], limit: usize) -> Out {
    let mut pos = 0;
    let mut out: Vec<u8> = Vec::new();
    loop {
        let (header, p) = read_bits(input, pos, 3).ok_or(Error::Truncated)?;
        let block = match header / 2 {
            0 => stored_block(input, p, out, limit),
            1 => data_loop(
                input,
                p,
                out,
                limit,
                &Code::new(&fixed_lit_lengths()),
                &Code::new(&[5; 32]),
            ),
            2 => {
                let (lit, dist, p2) = read_dynamic_tables(input, p)?;
                data_loop(input, p2, out, limit, &Code::new(&lit), &Code::new(&dist))
            }
            _ => Err(Error::ReservedBlockType),
        };
        let (p2, out2) = block?;
        out = out2;
        pos = p2;
        if header % 2 == 1 {
            return Ok((out, add(pos, 7) / 8));
        }
    }
}

/// `adler32`.
pub fn adler32(data: &[u8]) -> usize {
    let (mut s1, mut s2) = (1usize, 0usize);
    for &b in data {
        s1 = add(s1, usize::from(b)) % 65521;
        s2 = add(s2, s1) % 65521;
    }
    add(mul(s2, 65536), s1)
}

/// `zlib_decompress`.
pub fn zlib(input: &[u8], limit: usize) -> Out {
    if input.len() < 2 {
        return Err(Error::Truncated);
    }
    let cmf = usize::from(at(input, 0, 0));
    let flg = usize::from(at(input, 1, 0));
    if !add(mul(cmf, 256), flg).is_multiple_of(31) {
        return Err(Error::BadZlibCheck);
    } else if cmf % 16 != 8 {
        return Err(Error::BadZlibMethod);
    } else if cmf / 16 > 7 {
        return Err(Error::BadZlibWindow);
    } else if (flg / 32) % 2 == 1 {
        return Err(Error::PresetDictionary);
    }
    let (out, used_bytes) = inflate(input.get(2..).unwrap_or(&[]), limit)?;
    let end = add(2, used_bytes);
    if add(end, 4) > input.len() {
        return Err(Error::Truncated);
    }
    let b = |k: usize| usize::from(at(input, add(end, k), 0));
    let stored = add(
        add(mul(b(0), 16777216), mul(b(1), 65536)),
        add(mul(b(2), 256), b(3)),
    );
    if stored != adler32(&out) {
        Err(Error::AdlerMismatch)
    } else {
        Ok((out, add(end, 4)))
    }
}
