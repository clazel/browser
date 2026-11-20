//! The VP8L bitstream (RFC 9649 section 3), as a state machine fed one byte
//! at a time.
//!
//! Citations are to RFC 9649 by section; the listed choices are in `lib.rs`.
//!
//! # How it runs
//!
//! [`Vp8l::push`] appends a byte to the bit reader and [`Vp8l::advance`]
//! then runs **atomic actions** until one needs bits that have not come: an
//! action is one fixed-width read (at most 18 bits), or one prefix-coded
//! symbol (at most 15 bits), plus what follows from it. Each action is a
//! phase of the machine; what an action holds between bytes is in the
//! fields of [`Vp8l`], so the state is a fixed-size value. When the last
//! byte of the chunk has been pushed (`Bits::end`) an action that wants bits
//! that are not there is an error.
//!
//! # What it decodes into
//!
//! The image is decoded into `target` as RGBA bytes. The transforms'
//! images, the entropy image, the colour table, the colour cache and the
//! prefix codes live in the regions of [`Scratch`]. When the last pixel has
//! come, the inverse transforms run over `target` in place, last transform
//! first (section 3.5: "The inverse transforms are applied in the reverse
//! order that they are read from the bitstream").

use clazel_image_shape::Error;

use crate::bits::Bits;
use crate::distance;
use crate::huffman::{self, Decoded};
use crate::transform::{self, Px, put, px};
use crate::work::{
    CL_ALPHABET, COUNTS_BYTES, DIST_ALPHABET, GREEN_BASE, GROUP_BYTES, MAX_CACHE_BITS, SYMBOL_BASE,
    Scratch,
};

/// The message for a chunk that ends inside the image.
const EOS: &str = "the VP8L data ends before the image is complete";

fn bad(why: &'static str) -> Error {
    Error::Malformed(why)
}

/// `kCodeLengthCodeOrder` of section 3.7.2.1.2.
const CL_ORDER: [usize; CL_ALPHABET] = [
    17, 18, 0, 1, 2, 3, 4, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
];

/// What an image is for (section 3.6.1, "Roles of Image Data").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Role {
    /// The ARGB image.
    Main,
    /// The entropy image.
    Meta,
    /// The predictor image.
    Predictor,
    /// The colour transform image.
    Colour,
    /// The colour table.
    Palette,
}

/// The four transforms (section 3.5, Table 1, in that order).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Predictor,
    Colour,
    Green,
    Index,
}

/// A transform read from the stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Tf {
    kind: Kind,
    /// Block size bits (predictor, colour), or pixel bundling bits (index).
    bits: u8,
    /// The width of the image the transform applies to when it is inverted
    /// (for the index transform, the width **after** expanding).
    xsize: u32,
}

/// The phases of the machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum P {
    /// Section 3.4: the signature byte 0x2f.
    Signature,
    /// 14 bits: width minus one.
    Width,
    /// 14 bits: height minus one.
    Height,
    /// 1 bit alpha_is_used, 3 bits version.
    Version,
    /// Section 3.5: 1 bit, another transform?
    TransformFlag,
    /// 2 bits: the type.
    TransformType,
    /// 3 bits: size bits of the predictor or colour transform.
    TransformBits,
    /// 8 bits: colour table size minus one.
    PaletteSize,
    /// Section 3.6.2.3: 1 bit, a colour cache?
    CacheFlag,
    /// 4 bits: the cache size bits.
    CacheBits,
    /// Section 3.7.2.2: 1 bit, meta prefix codes?
    MetaFlag,
    /// 3 bits: prefix bits.
    MetaBits,
    /// Section 3.7.2.1: 1 bit, simple code length code?
    CodeKind,
    /// 1 bit: number of symbols minus one.
    SimpleCount,
    /// 1 bit: is_first_8bits.
    SimpleFirst,
    /// 1 or 8 bits: the first symbol.
    SimpleSym0,
    /// 8 bits: the second symbol.
    SimpleSym1,
    /// 4 bits: num_code_lengths minus 4.
    NormalCount,
    /// 3 bits each: the code length code's lengths.
    NormalCl,
    /// 1 bit: a max_symbol follows?
    NormalFlag,
    /// 3 bits: length_nbits.
    NormalNbits,
    /// length_nbits bits: max_symbol minus 2.
    NormalMax,
    /// A symbol of the code length code.
    Lengths,
    /// The extra bits of a repeat code.
    LengthRep,
    /// The code is complete: build it.
    BuildCode,
    /// Section 3.7.2.3: a symbol of the green code.
    Green,
    /// A red symbol.
    Red,
    /// A blue symbol.
    Blue,
    /// An alpha symbol.
    Alpha,
    /// The extra bits of a length.
    LenExtra,
    /// A distance prefix symbol.
    DistSym,
    /// The extra bits of a distance.
    DistExtra,
    /// The image is decoded and its transforms inverted.
    Done,
}

/// What one action did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Act {
    /// Run the next action.
    Again,
    /// More bits are needed.
    Wait,
    /// An image (of whatever role) has all its pixels.
    ImageDone,
    /// The main image is complete.
    Finished,
}

/// The lossless decoder's state.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Vp8l {
    phase: P,
    bits: Bits,
    /// The size the container says the image has.
    want_w: u32,
    want_h: u32,
    /// The size in the header, and the width after colour indexing.
    width: u32,
    height: u32,
    xsize: u32,
    /// The transforms read so far, and which kinds (bit per kind).
    tf: [Tf; 4],
    ntf: u8,
    used: u8,
    /// The image being decoded: its role, width, pixel count, position.
    role: Role,
    ixs: u32,
    total: u32,
    pos: u32,
    /// The colour cache's size bits (0: none) and the main image's, saved
    /// while its entropy image is read.
    cache_bits: u8,
    main_cache_bits: u8,
    /// The main image has meta prefix codes: bits, width of the entropy
    /// image, and the number of groups.
    use_meta: bool,
    meta_bits: u8,
    meta_w: u32,
    ngroups: u32,
    /// What the transform being read is, and its size bits or colour count.
    pending: Kind,
    tbits: u8,
    ncolors: u16,
    /// The prefix code being read: group, code (0 to 4), alphabet size.
    g: u32,
    c: u8,
    alphabet: u16,
    simple_n: u8,
    first8: bool,
    cl_n: u8,
    cl_i: u8,
    nbits: u8,
    max_left: u32,
    sym: u32,
    prev: u8,
    rep: u8,
    /// A pixel being read: green, red, blue; a length; the prefix code and
    /// extra bit count of a length or distance.
    lit_g: u8,
    lit_r: u8,
    lit_b: u8,
    length: u32,
    dprefix: u32,
    extra_n: u8,
}

/// `ceil(v / 2^bits)` (section 3.5.1's `DIV_ROUND_UP`).
fn ceil_shr(v: u32, bits: u8) -> Option<u32> {
    let add = 1u32.checked_shl(u32::from(bits))?.checked_sub(1)?;
    v.checked_add(add)?.checked_shr(u32::from(bits))
}

/// The cache slot of a pixel: `(0x1e35a7bd * color) >> (32 - bits)`
/// (section 3.6.2.3), where `color` is the ARGB value.
fn cache_key(p: Px, bits: u8) -> usize {
    let [r, g, b, a] = p;
    let argb = u32::from(a).wrapping_shl(24)
        | u32::from(r).wrapping_shl(16)
        | u32::from(g).wrapping_shl(8)
        | u32::from(b);
    let h = 0x1e35_a7bd_u32.wrapping_mul(argb);
    let shift = 32u32.saturating_sub(u32::from(bits));
    usize::try_from(h.checked_shr(shift).unwrap_or(0)).unwrap_or(0)
}

/// The counts and symbols slices of code `c` of group `g`.
fn group_ref(groups: &[u8], g: u32, c: u8) -> Option<(&[u8], &[u8])> {
    let start = usize::try_from(g).ok()?.checked_mul(GROUP_BYTES)?;
    let grp = groups.get(start..start.checked_add(GROUP_BYTES)?)?;
    let (counts, syms) = grp.split_at_checked(5 * COUNTS_BYTES)?;
    let c = usize::from(c);
    let at = c.checked_mul(COUNTS_BYTES)?;
    let counts = counts.get(at..at.checked_add(COUNTS_BYTES)?)?;
    let base = SYMBOL_BASE.get(c)?.checked_mul(2)?;
    Some((counts, syms.get(base..)?))
}

/// The same, writable.
fn group_mut(groups: &mut [u8], g: u32, c: u8) -> Option<(&mut [u8], &mut [u8])> {
    let start = usize::try_from(g).ok()?.checked_mul(GROUP_BYTES)?;
    let grp = groups.get_mut(start..start.checked_add(GROUP_BYTES)?)?;
    let (counts, syms) = grp.split_at_mut_checked(5 * COUNTS_BYTES)?;
    let c = usize::from(c);
    let at = c.checked_mul(COUNTS_BYTES)?;
    let counts = counts.get_mut(at..at.checked_add(COUNTS_BYTES)?)?;
    let base = SYMBOL_BASE.get(c)?.checked_mul(2)?;
    Some((counts, syms.get_mut(base..)?))
}

impl Vp8l {
    /// A decoder for an image the container says is `want_w` by `want_h`.
    pub(crate) fn new(want_w: u32, want_h: u32) -> Vp8l {
        Vp8l {
            phase: P::Signature,
            bits: Bits::new(),
            want_w,
            want_h,
            width: 0,
            height: 0,
            xsize: 0,
            tf: [Tf {
                kind: Kind::Green,
                bits: 0,
                xsize: 0,
            }; 4],
            ntf: 0,
            used: 0,
            role: Role::Main,
            ixs: 0,
            total: 0,
            pos: 0,
            cache_bits: 0,
            main_cache_bits: 0,
            use_meta: false,
            meta_bits: 0,
            meta_w: 0,
            ngroups: 1,
            pending: Kind::Green,
            tbits: 0,
            ncolors: 0,
            g: 0,
            c: 0,
            alphabet: 0,
            simple_n: 0,
            first8: false,
            cl_n: 0,
            cl_i: 0,
            nbits: 0,
            max_left: 0,
            sym: 0,
            prev: 8,
            rep: 0,
            lit_g: 0,
            lit_r: 0,
            lit_b: 0,
            length: 0,
            dprefix: 0,
            extra_n: 0,
        }
    }

    /// The invariant: every counter is in its range, so that the indexes the
    /// actions compute are in the regions (`groups` is the byte length of the
    /// groups region).
    pub(crate) fn inv(&self, groups: usize) -> bool {
        let cap = groups / GROUP_BYTES;
        self.bits.inv()
            && self.bits.len() <= 40
            && self.ntf <= 4
            && self.used < 16
            && self.pos <= self.total
            && self.ixs <= 16384
            && self.total <= 1 << 26
            && self.width <= 16384
            && self.height <= 16384
            && self.xsize <= 16384
            && self.cache_bits <= MAX_CACHE_BITS
            && self.main_cache_bits <= MAX_CACHE_BITS
            && self.ncolors <= 256
            && self.tbits <= 9
            && self.meta_bits <= 9
            && usize::try_from(self.ngroups).is_ok_and(|n| n >= 1 && n <= cap.max(1))
            && usize::try_from(self.g).is_ok_and(|g| g <= cap)
            && self.c <= 5
            && usize::from(self.alphabet) <= crate::work::MAX_GREEN
            && self.cl_n <= 19
            && self.cl_i <= 19
            && (self.phase != P::NormalCl || self.cl_i < self.cl_n)
            && self.nbits <= 16
            && self.rep <= 2
            && self.extra_n <= 18
            && (self.phase != P::LenExtra
                || (self.dprefix < 24 && self.extra_n == distance::extra_bits(self.dprefix)))
            && (self.phase != P::DistExtra
                || (self.dprefix < 40 && self.extra_n == distance::extra_bits(self.dprefix)))
            && self.sym <= u32::from(self.alphabet)
            && self.length <= 4096
    }

    /// Appends the next byte of the chunk; `last` is true for the chunk's
    /// last byte.
    pub(crate) fn push(&mut self, b: u8, last: bool) {
        self.bits.push(b);
        self.bits.end = last;
    }

    /// Runs actions until bits are needed (`Ok(false)`) or the image is
    /// complete (`Ok(true)`).
    pub(crate) fn advance(
        &mut self,
        s: &mut Scratch<'_>,
        target: &mut [u8],
    ) -> Result<bool, Error> {
        loop {
            if self.phase == P::Done {
                return Ok(true);
            }
            match self.act(s, target)? {
                Act::Again => {}
                Act::Wait => return Ok(false),
                Act::ImageDone => {
                    if self.finish_image(s, target)? == Act::Finished {
                        return Ok(true);
                    }
                }
                Act::Finished => return Ok(true),
            }
        }
    }

    /// Reads `k` bits: `Some` if they are there, `None` to wait, an error if
    /// the chunk has ended.
    fn read(&mut self, k: u8) -> Result<Option<u32>, Error> {
        match self.bits.take(k) {
            Some(v) => Ok(Some(v)),
            None if self.bits.end => Err(bad(EOS)),
            None => Ok(None),
        }
    }

    /// Starts decoding an image of `w` by `h` pixels for `role` into a
    /// region of `region` bytes, at its colour cache information.
    fn begin_image(&mut self, role: Role, w: u32, h: u32, region: usize) -> Result<(), Error> {
        let total = w
            .checked_mul(h)
            .ok_or(bad("an image with too many pixels"))?;
        let bytes = usize::try_from(total).ok().and_then(|t| t.checked_mul(4));
        if w == 0 || h == 0 || bytes.is_none_or(|b| b > region) {
            return Err(bad("an image larger than the space for it"));
        }
        self.role = role;
        self.ixs = w;
        self.total = total;
        self.pos = 0;
        self.cache_bits = 0;
        self.use_meta = false;
        self.ngroups = 1;
        self.phase = P::CacheFlag;
        Ok(())
    }

    /// Adds a transform (each kind at most once: section 3.5, "Each
    /// transform is allowed to be used only once").
    fn push_tf(&mut self, kind: Kind, bits: u8, xsize: u32) -> Result<(), Error> {
        let slot = self.tf.get_mut(usize::from(self.ntf));
        let Some(slot) = slot else {
            return Err(bad("more than four transforms"));
        };
        *slot = Tf { kind, bits, xsize };
        self.ntf = self.ntf.saturating_add(1);
        Ok(())
    }

    /// The alphabet size of code `c` of a group.
    fn alphabet_of(&self, c: u8) -> u16 {
        match c {
            0 => {
                let cache = if self.cache_bits == 0 {
                    0
                } else {
                    1usize.checked_shl(u32::from(self.cache_bits)).unwrap_or(0)
                };
                u16::try_from(GREEN_BASE.saturating_add(cache)).unwrap_or(0)
            }
            1..=3 => 256,
            _ => u16::try_from(DIST_ALPHABET).unwrap_or(0),
        }
    }

    /// The colour cache information is read: the main image goes on to its
    /// meta prefix codes, the others to their prefix codes.
    fn after_cache(&mut self, s: &mut Scratch<'_>) {
        if self.role == Role::Main {
            self.phase = P::MetaFlag;
        } else {
            self.start_codes(s);
        }
    }

    /// Starts reading the prefix codes of every group, and clears the cache.
    fn start_codes(&mut self, s: &mut Scratch<'_>) {
        if self.cache_bits > 0 {
            s.cache.fill(0);
        }
        self.g = 0;
        self.c = 0;
        self.phase = P::CodeKind;
    }

    /// The group that codes the pixel at (`x`, `y`): section 3.7.2.2.2,
    /// `meta_prefix_code = (entropy_image[position] >> 8) & 0xffff`, the red
    /// and green bytes.
    fn group_at(&self, x: u32, y: u32, meta: &[u8]) -> Result<u32, Error> {
        if !self.use_meta {
            return Ok(0);
        }
        let bx = x.checked_shr(u32::from(self.meta_bits)).unwrap_or(0);
        let by = y.checked_shr(u32::from(self.meta_bits)).unwrap_or(0);
        let at = by
            .checked_mul(self.meta_w)
            .and_then(|v| v.checked_add(bx))
            .and_then(|v| usize::try_from(v).ok())
            .ok_or(bad("an entropy image position out of range"))?;
        let [r, g, _, _] = px(meta, at);
        let group = u32::from(r).wrapping_shl(8) | u32::from(g);
        if group >= self.ngroups {
            return Err(bad("a meta prefix code past the last group"));
        }
        Ok(group)
    }

    /// Reads one symbol of code `c` of group `g`.
    fn symbol(&mut self, groups: &[u8], g: u32, c: u8) -> Result<Option<u16>, Error> {
        let (counts, syms) =
            group_ref(groups, g, c).ok_or(bad("a prefix code group out of range"))?;
        match huffman::decode(counts, syms, self.bits.peek32(), self.bits.len()) {
            Decoded::Symbol(sym, len) => {
                self.bits.skip(len);
                Ok(Some(sym))
            }
            Decoded::More if self.bits.end => Err(bad(EOS)),
            Decoded::More => Ok(None),
            Decoded::Invalid => Err(bad("a prefix code that does not decode")),
        }
    }

    /// One atomic action.
    fn act(&mut self, s: &mut Scratch<'_>, target: &mut [u8]) -> Result<Act, Error> {
        macro_rules! take {
            ($k:expr) => {
                match self.read($k)? {
                    Some(v) => v,
                    None => return Ok(Act::Wait),
                }
            };
        }
        match self.phase {
            // Section 3.4, item 6: "1-byte signature 0x2f".
            P::Signature => {
                if take!(8) != 0x2F {
                    return Err(bad("the VP8L signature byte is not 0x2f"));
                }
                self.phase = P::Width;
            }
            // Section 3.4: `ReadBits(14) + 1`, twice.
            P::Width => {
                self.width = take!(14).saturating_add(1);
                self.phase = P::Height;
            }
            P::Height => {
                self.height = take!(14).saturating_add(1);
                self.phase = P::Version;
            }
            // Section 3.4: alpha_is_used (a hint only), then version_number,
            // which "MUST be set to 0".
            P::Version => {
                let v = take!(4);
                if v >> 1 != 0 {
                    return Err(bad("a VP8L version other than 0"));
                }
                if self.width != self.want_w || self.height != self.want_h {
                    return Err(bad("the VP8L image is not the size its container says"));
                }
                self.xsize = self.width;
                self.phase = P::TransformFlag;
            }
            // Section 3.5: `while (ReadBits(1))`.
            P::TransformFlag => {
                if take!(1) == 0 {
                    let region = target.len();
                    self.begin_image(Role::Main, self.xsize, self.height, region)?;
                } else {
                    self.phase = P::TransformType;
                }
            }
            P::TransformType => {
                let kind = match take!(2) {
                    0 => Kind::Predictor,
                    1 => Kind::Colour,
                    2 => Kind::Green,
                    _ => Kind::Index,
                };
                let bit = match kind {
                    Kind::Predictor => 1,
                    Kind::Colour => 2,
                    Kind::Green => 4,
                    Kind::Index => 8,
                };
                if self.used & bit != 0 {
                    return Err(bad("a transform used twice"));
                }
                self.used |= bit;
                self.pending = kind;
                match kind {
                    Kind::Predictor | Kind::Colour => self.phase = P::TransformBits,
                    Kind::Green => {
                        self.push_tf(Kind::Green, 0, self.xsize)?;
                        self.phase = P::TransformFlag;
                    }
                    Kind::Index => self.phase = P::PaletteSize,
                }
            }
            // Sections 3.5.1 and 3.5.2: `size_bits = ReadBits(3) + 2`, then
            // the sub-resolution image of
            // `DIV_ROUND_UP(image_width, 1 << size_bits)` by the same of the
            // height.
            P::TransformBits => {
                let bits = u8::try_from(take!(3).saturating_add(2)).unwrap_or(2);
                self.tbits = bits;
                let w = ceil_shr(self.xsize, bits).ok_or(bad("a block count overflow"))?;
                let h = ceil_shr(self.height, bits).ok_or(bad("a block count overflow"))?;
                let (role, region) = if self.pending == Kind::Predictor {
                    (Role::Predictor, s.pred.len())
                } else {
                    (Role::Colour, s.color.len())
                };
                self.begin_image(role, w, h, region)?;
            }
            // Section 3.5.4: `color_table_size = ReadBits(8) + 1`, read as an
            // image of that width and a height of 1.
            P::PaletteSize => {
                let n = take!(8).saturating_add(1);
                self.ncolors = u16::try_from(n).unwrap_or(256);
                let region = s.palette.len();
                self.begin_image(Role::Palette, n, 1, region)?;
            }
            // Section 3.6.2.3: a 1-bit flag, then `ReadBits(4)`, "[1..11]".
            P::CacheFlag => {
                if take!(1) == 0 {
                    self.cache_bits = 0;
                    self.after_cache(s);
                } else {
                    self.phase = P::CacheBits;
                }
            }
            P::CacheBits => {
                let v = u8::try_from(take!(4)).unwrap_or(0);
                if v == 0 || v > MAX_CACHE_BITS {
                    return Err(bad("a colour cache size outside 1 to 11 bits"));
                }
                self.cache_bits = v;
                self.after_cache(s);
            }
            // Section 3.7.2.2: a 1-bit flag, `prefix_bits = ReadBits(3) + 2`
            // and the entropy image of `DIV_ROUND_UP(width, 1 << prefix_bits)`
            // by the same of the height.
            P::MetaFlag => {
                if take!(1) == 0 {
                    self.use_meta = false;
                    self.ngroups = 1;
                    self.start_codes(s);
                } else {
                    self.phase = P::MetaBits;
                }
            }
            P::MetaBits => {
                let bits = u8::try_from(take!(3).saturating_add(2)).unwrap_or(2);
                let w = ceil_shr(self.xsize, bits).ok_or(bad("a block count overflow"))?;
                let h = ceil_shr(self.height, bits).ok_or(bad("a block count overflow"))?;
                self.main_cache_bits = self.cache_bits;
                self.meta_bits = bits;
                self.meta_w = w;
                let region = s.meta.len();
                self.begin_image(Role::Meta, w, h, region)?;
            }
            // Section 3.7.2.1: 1 means a simple code length code.
            P::CodeKind => {
                self.alphabet = self.alphabet_of(self.c);
                self.sym = 0;
                let a = usize::from(self.alphabet);
                s.lens
                    .get_mut(..a)
                    .ok_or(bad("an alphabet larger than its space"))?
                    .fill(0);
                self.phase = if take!(1) == 1 {
                    P::SimpleCount
                } else {
                    P::NormalCount
                };
            }
            // Section 3.7.2.1.1: `num_symbols = ReadBits(1) + 1`,
            // `is_first_8bits = ReadBits(1)`, `symbol0 = ReadBits(1 + 7 *
            // is_first_8bits)`, and a second 8-bit symbol if there are two.
            P::SimpleCount => {
                self.simple_n = u8::try_from(take!(1).saturating_add(1)).unwrap_or(1);
                self.phase = P::SimpleFirst;
            }
            P::SimpleFirst => {
                self.first8 = take!(1) == 1;
                self.phase = P::SimpleSym0;
            }
            P::SimpleSym0 => {
                let k = if self.first8 { 8 } else { 1 };
                let sym = take!(k);
                self.set_length_one(s, sym);
                self.phase = if self.simple_n == 2 {
                    P::SimpleSym1
                } else {
                    P::BuildCode
                };
            }
            P::SimpleSym1 => {
                let sym = take!(8);
                self.set_length_one(s, sym);
                self.phase = P::BuildCode;
            }
            // Section 3.7.2.1.2: `num_code_lengths = 4 + ReadBits(4)`, then
            // that many 3-bit lengths in `kCodeLengthCodeOrder`.
            P::NormalCount => {
                self.cl_n = u8::try_from(take!(4).saturating_add(4)).unwrap_or(19);
                self.cl_i = 0;
                s.cl_lens.fill(0);
                self.phase = P::NormalCl;
            }
            P::NormalCl => {
                let v = u8::try_from(take!(3)).unwrap_or(0);
                let at = CL_ORDER.get(usize::from(self.cl_i)).copied();
                if let Some(slot) = at.and_then(|a| s.cl_lens.get_mut(a)) {
                    *slot = v;
                }
                self.cl_i = self.cl_i.saturating_add(1);
                if self.cl_i >= self.cl_n {
                    huffman::build(s.cl_lens, s.cl_counts, s.cl_syms)
                        .map_err(|_| bad("an invalid code length code"))?;
                    self.phase = P::NormalFlag;
                }
            }
            // `if (ReadBits(1) == 0) max_symbol = alphabet size; else
            // length_nbits = 2 + 2 * ReadBits(3); max_symbol = 2 +
            // ReadBits(length_nbits)`, an error if over the alphabet.
            P::NormalFlag => {
                self.sym = 0;
                self.prev = 8;
                if take!(1) == 0 {
                    self.max_left = u32::from(self.alphabet);
                    self.phase = P::Lengths;
                } else {
                    self.phase = P::NormalNbits;
                }
            }
            P::NormalNbits => {
                let v = take!(3);
                self.nbits = u8::try_from(v.saturating_mul(2).saturating_add(2)).unwrap_or(2);
                self.phase = P::NormalMax;
            }
            P::NormalMax => {
                let max = take!(self.nbits).saturating_add(2);
                if max > u32::from(self.alphabet) {
                    return Err(bad("a max_symbol over the alphabet"));
                }
                self.max_left = max;
                self.phase = P::Lengths;
            }
            // The code lengths: a symbol of the code length code per step,
            // at most max_symbol of them, 0 to 15 a length, 16 to 18
            // repeats.
            P::Lengths => {
                if self.sym >= u32::from(self.alphabet) || self.max_left == 0 {
                    self.phase = P::BuildCode;
                    return Ok(Act::Again);
                }
                match huffman::decode(s.cl_counts, s.cl_syms, self.bits.peek32(), self.bits.len()) {
                    Decoded::Symbol(sym, len) => {
                        self.bits.skip(len);
                        self.max_left = self.max_left.saturating_sub(1);
                        if sym < 16 {
                            let v = u8::try_from(sym).unwrap_or(0);
                            let at = usize::try_from(self.sym).unwrap_or(usize::MAX);
                            if let Some(slot) = s.lens.get_mut(at) {
                                *slot = v;
                            }
                            self.sym = self.sym.saturating_add(1);
                            if v != 0 {
                                self.prev = v;
                            }
                        } else if sym <= 18 {
                            self.rep = u8::try_from(sym.saturating_sub(16)).unwrap_or(0);
                            self.phase = P::LengthRep;
                        } else {
                            // The code length code has 19 symbols (section
                            // 3.7.2.1.2), so a built code never yields more.
                            return Err(bad("a code length symbol over 18"));
                        }
                    }
                    Decoded::More if self.bits.end => return Err(bad(EOS)),
                    Decoded::More => return Ok(Act::Wait),
                    Decoded::Invalid => return Err(bad("a code length that does not decode")),
                }
            }
            // Code 16 repeats the previous nonzero length 3 + ReadBits(2)
            // times (8 if there is none yet), 17 is 3 + ReadBits(3) zeros,
            // 18 is 11 + ReadBits(7) zeros.
            P::LengthRep => {
                let (extra, offset) = match self.rep {
                    0 => (2, 3),
                    1 => (3, 3),
                    _ => (7, 11),
                };
                let n = take!(extra).saturating_add(offset);
                let end = self.sym.saturating_add(n);
                if end > u32::from(self.alphabet) {
                    return Err(bad("a repeat past the end of the alphabet"));
                }
                let value = if self.rep == 0 { self.prev } else { 0 };
                let from = usize::try_from(self.sym).unwrap_or(usize::MAX);
                let to = usize::try_from(end).unwrap_or(usize::MAX);
                if let Some(run) = s.lens.get_mut(from..to) {
                    run.fill(value);
                }
                self.sym = end;
                self.phase = P::Lengths;
            }
            // Build the code of this group's `c`th slot, then go to the
            // next code, group, or the pixels.
            P::BuildCode => {
                let a = usize::from(self.alphabet);
                let lens = s
                    .lens
                    .get(..a)
                    .ok_or(bad("an alphabet larger than its space"))?;
                let (counts, syms) = group_mut(s.groups, self.g, self.c)
                    .ok_or(bad("a prefix code group out of range"))?;
                huffman::build(lens, counts, syms).map_err(bad)?;
                self.c = self.c.saturating_add(1);
                if self.c >= 5 {
                    self.c = 0;
                    self.g = self.g.saturating_add(1);
                }
                self.phase = if self.g >= self.ngroups {
                    P::Green
                } else {
                    P::CodeKind
                };
            }
            P::Green | P::Red | P::Blue | P::Alpha | P::LenExtra | P::DistSym | P::DistExtra => {
                return self.act_pixel(s, target);
            }
            P::Done => return Ok(Act::Finished),
        }
        Ok(Act::Again)
    }

    /// Sets the length of `sym` to 1 if the alphabet has it (libwebp ignores
    /// a symbol past the alphabet in a simple code: a distance code's
    /// 8-bit symbol, say).
    fn set_length_one(&self, s: &mut Scratch<'_>, sym: u32) {
        if sym < u32::from(self.alphabet)
            && let Some(slot) = usize::try_from(sym).ok().and_then(|at| s.lens.get_mut(at))
        {
            *slot = 1;
        }
    }

    /// One atomic action on the pixels of the image (section 3.7.2.3).
    fn act_pixel(&mut self, s: &mut Scratch<'_>, target: &mut [u8]) -> Result<Act, Error> {
        let (dest, meta): (&mut [u8], &[u8]) = match self.role {
            Role::Main => (target, &*s.meta),
            Role::Meta => (&mut *s.meta, &[]),
            Role::Predictor => (&mut *s.pred, &[]),
            Role::Colour => (&mut *s.color, &[]),
            Role::Palette => (&mut *s.palette, &[]),
        };
        let groups: &[u8] = &*s.groups;
        let cache: &mut [u8] = &mut *s.cache;
        let x = self.pos.checked_rem(self.ixs).unwrap_or(0);
        let y = self.pos.checked_div(self.ixs).unwrap_or(0);
        let group = self.group_at(x, y, meta)?;
        match self.phase {
            P::Green => {
                let Some(sym) = self.symbol(groups, group, 0)? else {
                    return Ok(Act::Wait);
                };
                let sym = usize::from(sym);
                if sym < 256 {
                    self.lit_g = u8::try_from(sym).unwrap_or(0);
                    self.phase = P::Red;
                } else if sym < GREEN_BASE {
                    // A length prefix code (section 3.7.2.3, 2.i).
                    let prefix = u32::try_from(sym.saturating_sub(256)).unwrap_or(0);
                    let extra = distance::extra_bits(prefix);
                    self.dprefix = prefix;
                    if extra == 0 {
                        self.length = distance::value(prefix, 0);
                        self.phase = P::DistSym;
                    } else {
                        self.extra_n = extra;
                        self.phase = P::LenExtra;
                    }
                } else {
                    // A colour cache code (3).
                    let index = sym.saturating_sub(GREEN_BASE);
                    let size = 1usize.checked_shl(u32::from(self.cache_bits)).unwrap_or(0);
                    if self.cache_bits == 0 || index >= size {
                        return Err(bad("a colour cache index past the cache"));
                    }
                    let p = px(cache, index);
                    return self.emit(p, dest, cache);
                }
            }
            P::Red => {
                let Some(sym) = self.symbol(groups, group, 1)? else {
                    return Ok(Act::Wait);
                };
                self.lit_r = u8::try_from(sym).unwrap_or(0);
                self.phase = P::Blue;
            }
            P::Blue => {
                let Some(sym) = self.symbol(groups, group, 2)? else {
                    return Ok(Act::Wait);
                };
                self.lit_b = u8::try_from(sym).unwrap_or(0);
                self.phase = P::Alpha;
            }
            P::Alpha => {
                let Some(sym) = self.symbol(groups, group, 3)? else {
                    return Ok(Act::Wait);
                };
                let a = u8::try_from(sym).unwrap_or(0);
                let p = [self.lit_r, self.lit_g, self.lit_b, a];
                return self.emit(p, dest, cache);
            }
            P::LenExtra => {
                let v = match self.read(self.extra_n)? {
                    Some(v) => v,
                    None => return Ok(Act::Wait),
                };
                self.length = distance::value(self.dprefix, v);
                self.phase = P::DistSym;
            }
            P::DistSym => {
                let Some(sym) = self.symbol(groups, group, 4)? else {
                    return Ok(Act::Wait);
                };
                let prefix = u32::from(sym);
                // The distance code has 40 symbols (section 3.7.2.3), so a built
                // code never yields more.
                if prefix >= 40 {
                    return Err(bad("a distance code over 39"));
                }
                let extra = distance::extra_bits(prefix);
                if extra == 0 {
                    return self.copy(distance::value(prefix, 0), dest, cache);
                }
                self.dprefix = prefix;
                self.extra_n = extra;
                self.phase = P::DistExtra;
            }
            P::DistExtra => {
                let v = match self.read(self.extra_n)? {
                    Some(v) => v,
                    None => return Ok(Act::Wait),
                };
                return self.copy(distance::value(self.dprefix, v), dest, cache);
            }
            _ => return Err(bad("a pixel action outside the pixels")),
        }
        Ok(Act::Again)
    }

    /// Stores a pixel and moves on.
    fn emit(&mut self, p: Px, dest: &mut [u8], cache: &mut [u8]) -> Result<Act, Error> {
        if !put(dest, usize::try_from(self.pos).unwrap_or(usize::MAX), p) {
            return Err(bad("a pixel outside the image"));
        }
        if self.cache_bits > 0 {
            put(cache, cache_key(p, self.cache_bits), p);
        }
        self.pos = self.pos.saturating_add(1);
        Ok(self.after_pixels())
    }

    /// A backward reference of `self.length` pixels at distance code `code`
    /// (section 3.7.2.3, 2.vii: "Copy L pixels (in scan-line order) from the
    /// sequence of pixels starting at the current position minus D pixels").
    /// The copy goes pixel by pixel, so a distance shorter than the length
    /// repeats what was just written. A distance before the start of the
    /// image or a length past its end is an error (as in libwebp).
    fn copy(&mut self, code: u32, dest: &mut [u8], cache: &mut [u8]) -> Result<Act, Error> {
        let dist = distance::distance(code, self.ixs);
        if dist > self.pos {
            return Err(bad("a backward reference before the start of the image"));
        }
        if self.length > self.total.saturating_sub(self.pos) {
            return Err(bad("a backward reference past the end of the image"));
        }
        let pos = usize::try_from(self.pos).unwrap_or(usize::MAX);
        let back = usize::try_from(dist).unwrap_or(usize::MAX);
        for k in 0..usize::try_from(self.length).unwrap_or(0) {
            let to = pos.saturating_add(k);
            let p = px(dest, to.saturating_sub(back));
            if !put(dest, to, p) {
                return Err(bad("a pixel outside the image"));
            }
            if self.cache_bits > 0 {
                put(cache, cache_key(p, self.cache_bits), p);
            }
        }
        self.pos = self.pos.saturating_add(self.length);
        Ok(self.after_pixels())
    }

    /// After a pixel or a copy: the next pixel, or the end of the image.
    fn after_pixels(&mut self) -> Act {
        if self.pos >= self.total {
            Act::ImageDone
        } else {
            self.phase = P::Green;
            Act::Again
        }
    }

    /// An image of any role has all its pixels.
    fn finish_image(&mut self, s: &mut Scratch<'_>, target: &mut [u8]) -> Result<Act, Error> {
        match self.role {
            Role::Predictor => {
                self.push_tf(Kind::Predictor, self.tbits, self.xsize)?;
                self.phase = P::TransformFlag;
            }
            Role::Colour => {
                self.push_tf(Kind::Colour, self.tbits, self.xsize)?;
                self.phase = P::TransformFlag;
            }
            // Section 3.5.4: "The color table is always subtraction-coded":
            // each entry adds the previous one, per channel, modulo 256.
            Role::Palette => {
                let n = usize::from(self.ncolors);
                let mut prev: Px = [0; 4];
                for i in 0..n {
                    let [pr, pg, pb, pa] = prev;
                    let [r, g, b, a] = px(s.palette, i);
                    prev = [
                        r.wrapping_add(pr),
                        g.wrapping_add(pg),
                        b.wrapping_add(pb),
                        a.wrapping_add(pa),
                    ];
                    put(s.palette, i, prev);
                }
                // Pixel bundling (Table 3), and the width it leaves.
                let bits = transform::bundle_bits(n);
                self.push_tf(Kind::Index, bits, self.xsize)?;
                self.xsize = ceil_shr(self.xsize, bits).ok_or(bad("a width overflow"))?;
                self.phase = P::TransformFlag;
            }
            // Section 3.7.2.2.2: `num_prefix_groups = max(entropy image) +
            // 1`, from each pixel's red and green bytes.
            Role::Meta => {
                let mut max = 0u32;
                for i in 0..usize::try_from(self.total).unwrap_or(0) {
                    let [r, g, _, _] = px(s.meta, i);
                    max = max.max(u32::from(r).wrapping_shl(8) | u32::from(g));
                }
                let groups = max.saturating_add(1);
                let cap = s.groups.len().checked_div(GROUP_BYTES).unwrap_or(0);
                if usize::try_from(groups).is_ok_and(|g| g > cap) {
                    return Err(Error::Unsupported(
                        "more prefix code groups than this decoder holds",
                    ));
                }
                self.ngroups = groups;
                // Back to the main image.
                self.role = Role::Main;
                self.cache_bits = self.main_cache_bits;
                self.use_meta = true;
                self.ixs = self.xsize;
                self.total = self.xsize.saturating_mul(self.height);
                self.pos = 0;
                self.start_codes(s);
            }
            Role::Main => {
                self.invert(s, target)?;
                self.phase = P::Done;
                return Ok(Act::Finished);
            }
        }
        Ok(Act::Again)
    }

    /// Inverts the transforms, last first (section 3.5), in place.
    fn invert(&self, s: &mut Scratch<'_>, target: &mut [u8]) -> Result<(), Error> {
        let fail = bad("a transform ran off the buffer");
        let h = usize::try_from(self.height).map_err(|_| fail)?;
        let mut i = self.ntf;
        while i > 0 {
            i = i.saturating_sub(1);
            let Some(t) = self.tf.get(usize::from(i)).copied() else {
                return Err(fail);
            };
            let w = usize::try_from(t.xsize).map_err(|_| fail)?;
            let ok = match t.kind {
                Kind::Predictor => {
                    let bw = ceil_shr(t.xsize, t.bits)
                        .and_then(|v| usize::try_from(v).ok())
                        .ok_or(fail)?;
                    (0..h).all(|y| transform::predictor_row(target, w, y, t.bits, bw, s.pred))
                }
                Kind::Colour => {
                    let bw = ceil_shr(t.xsize, t.bits)
                        .and_then(|v| usize::try_from(v).ok())
                        .ok_or(fail)?;
                    (0..h).all(|y| transform::color_row(target, w, y, t.bits, bw, s.color))
                }
                Kind::Green => (0..h).all(|y| transform::green_row(target, w, y)),
                Kind::Index => {
                    let pw = ceil_shr(t.xsize, t.bits)
                        .and_then(|v| usize::try_from(v).ok())
                        .ok_or(fail)?;
                    let n = usize::from(self.ncolors);
                    (0..h).rev().all(|y| {
                        let src = y.checked_mul(pw);
                        let dst = y.checked_mul(w);
                        match (src, dst) {
                            (Some(src), Some(dst)) => {
                                transform::palette_row(target, src, dst, w, t.bits, s.palette, n)
                            }
                            _ => false,
                        }
                    })
                }
            };
            if !ok {
                return Err(fail);
            }
        }
        Ok(())
    }
}

#[cfg(kani)]
fn any_kind() -> Kind {
    match kani::any::<u8>() & 3 {
        0 => Kind::Predictor,
        1 => Kind::Colour,
        2 => Kind::Green,
        _ => Kind::Index,
    }
}

#[cfg(kani)]
fn any_role() -> Role {
    match kani::any::<u8>() % 5 {
        0 => Role::Main,
        1 => Role::Meta,
        2 => Role::Predictor,
        3 => Role::Colour,
        _ => Role::Palette,
    }
}

/// Any state in `phase`, every field symbolic, with the invariant and with
/// the bounds a harness can unwind: images of at most 4 pixels, 2 rows, 4
/// colours, references of at most 4 pixels, and an alphabet of at most
/// `max_alphabet` symbols. The role is `role`, or any role if `None`.
///
/// One phase per harness: with the phase symbolic too, CBMC ran out of
/// memory (over 4 GB) or time (over 15 minutes) on every class of phases.
#[cfg(kani)]
pub(crate) fn any_vp8l(phase: P, role: Option<Role>, groups: usize, max_alphabet: u16) -> Vp8l {
    let mut v = Vp8l::new(kani::any(), kani::any());
    v.phase = phase;
    v.bits = Bits::any();
    v.width = kani::any();
    v.height = kani::any();
    v.xsize = kani::any();
    for t in &mut v.tf {
        *t = Tf {
            kind: any_kind(),
            bits: kani::any(),
            xsize: kani::any(),
        };
    }
    v.ntf = kani::any();
    v.used = kani::any();
    v.role = role.unwrap_or_else(any_role);
    v.ixs = kani::any();
    v.total = kani::any();
    v.pos = kani::any();
    v.cache_bits = kani::any();
    v.main_cache_bits = kani::any();
    v.use_meta = kani::any();
    v.meta_bits = kani::any();
    v.meta_w = kani::any();
    v.ngroups = kani::any();
    v.pending = any_kind();
    v.tbits = kani::any();
    v.ncolors = kani::any();
    v.g = kani::any();
    v.c = kani::any();
    v.alphabet = kani::any();
    v.simple_n = kani::any();
    v.first8 = kani::any();
    v.cl_n = kani::any();
    v.cl_i = kani::any();
    v.nbits = kani::any();
    v.max_left = kani::any();
    v.sym = kani::any();
    v.prev = kani::any();
    v.rep = kani::any();
    v.lit_g = kani::any();
    v.lit_r = kani::any();
    v.lit_b = kani::any();
    v.length = kani::any();
    v.dprefix = kani::any();
    v.extra_n = kani::any();
    kani::assume(v.inv(groups));
    kani::assume(v.tf.iter().all(|t| t.xsize <= 4 && t.bits <= 9));
    kani::assume(v.ixs <= 4 && v.total <= 4 && v.xsize <= 4 && v.height <= 2);
    kani::assume(v.width <= 4 && v.ncolors <= 4 && v.length <= 4 && v.meta_w <= 4);
    kani::assume(v.alphabet <= max_alphabet);
    v
}

#[cfg(kani)]
impl Vp8l {
    /// One action (for the harnesses).
    pub(crate) fn kani_act(&mut self, s: &mut Scratch<'_>, target: &mut [u8]) -> Result<(), Error> {
        self.act(s, target).map(|_| ())
    }

    /// Finishing an image of any role (for the harnesses).
    pub(crate) fn kani_finish(
        &mut self,
        s: &mut Scratch<'_>,
        target: &mut [u8],
    ) -> Result<(), Error> {
        self.finish_image(s, target).map(|_| ())
    }

    /// The invariant, for the harnesses.
    pub(crate) fn kani_inv(&self, groups: usize) -> bool {
        self.inv(groups)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_state_satisfies_inv() {
        let v = Vp8l::new(0, 0);
        assert!(v.bits.inv());
        assert!(v.inv(GROUP_BYTES));
        assert!(v.inv(GROUP_BYTES * 5));
    }
}
