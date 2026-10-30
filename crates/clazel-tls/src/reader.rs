//! The executable reader of the presentation language (RFC 8446 §3): a
//! cursor over the bytes of a message that have not been consumed. Its
//! view is exactly those bytes, so every method's contract is a function
//! of the view and a message parser built on it reads inside the bytes of
//! its message and nowhere else. A sub-cursor for a vector's contents is
//! how a nested vector is read without reading past its end.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bytes of a message not yet read: `buf[pos..end]`.
pub struct Cur<'a> {
    buf: &'a [u8],
    pos: usize,
    end: usize,
}

impl<'a> View for Cur<'a> {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Seq<u8> {
        self.buf@.subrange(self.pos as int, self.end as int)
    }
}

/// The byte at `i`.
pub fn byte_at(buf: &[u8], i: usize) -> (b: u8)
    requires
        i < buf.len(),
    ensures
        b == buf@[i as int],
{
    match buf.get(i) {
        Some(&b) => b,
        None => 0,
    }
}

impl<'a> Cur<'a> {
    /// The window lies inside the buffer.
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.pos <= self.end && self.end <= self.buf@.len()
    }

    /// A cursor over all of `buf`.
    pub fn new(buf: &'a [u8]) -> (c: Cur<'a>)
        ensures
            c@ == buf@,
    {
        let end = buf.len();
        let c = Cur { buf, pos: 0, end };
        proof {
            assert(c@ =~= buf@);
        }
        c
    }

    /// The number of bytes not yet read.
    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        proof {
            use_type_invariant(self);
        }
        self.end.saturating_sub(self.pos)
    }

    /// §3.3: read a `uint16` ([`read_u16`]).
    pub fn u16(&mut self) -> (r: Option<u16>)
        ensures
            match r {
                Some(v) => read_u16(old(self)@) == Some((v, final(self)@)),
                None => read_u16(old(self)@) is None,
            },
    {
        let ghost before = self@;
        let v = self.uint(2)?;
        proof {
            super::lemmas_pl::lemma_read_uint_canonical(before, 2);
            super::lemmas_pl::lemma_pow256_widths();
        }
        Some(v as u16)
    }

    /// §3.3: read a `uint8` ([`read_uint`] of one byte).
    pub fn u8(&mut self) -> (r: Option<u8>)
        ensures
            match r {
                Some(v) => read_uint(old(self)@, 1) == Some((v as nat, final(self)@)),
                None => read_uint(old(self)@, 1) is None,
            },
    {
        let ghost before = self@;
        let v = self.uint(1)?;
        proof {
            super::lemmas_pl::lemma_read_uint_canonical(before, 1);
            super::lemmas_pl::lemma_pow256_widths();
        }
        Some(v as u8)
    }

    /// §3.3: read a `uint32` ([`read_uint`] of four bytes).
    pub fn u32(&mut self) -> (r: Option<u32>)
        ensures
            match r {
                Some(v) => read_uint(old(self)@, 4) == Some((v as nat, final(self)@)),
                None => read_uint(old(self)@, 4) is None,
            },
    {
        let ghost before = self@;
        let v = self.uint(4)?;
        proof {
            super::lemmas_pl::lemma_read_uint_canonical(before, 4);
            super::lemmas_pl::lemma_pow256_widths();
        }
        Some(v as u32)
    }

    /// The bytes not yet read, as a slice of the buffer.
    pub fn as_slice(&self) -> (s: &'a [u8])
        ensures
            s@ == self@,
    {
        proof {
            use_type_invariant(self);
        }
        vstd::slice::slice_subrange(self.buf, self.pos, self.end)
    }

    /// No bytes are left.
    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self@.len() == 0),
    {
        self.len() == 0
    }

    /// §3.3: read a `w`-byte unsigned integer ([`read_uint`]); at most four
    /// bytes (the widest field of the standard that is read as a number).
    pub fn uint(&mut self, w: usize) -> (r: Option<u64>)
        requires
            w <= 4,
        ensures
            super::contract::uint_ensures(old(self)@, w as nat, r, final(self)@),
    {
        proof {
            use_type_invariant(&*self);
        }
        let avail = self.end.saturating_sub(self.pos);
        if avail < w {
            return None;
        }
        let ghost whole = self@;
        let mut v: u64 = 0;
        let mut i: usize = 0;
        proof {
            assert(whole.take(0) =~= Seq::<u8>::empty());
        }
        while i < w
            invariant
                i <= w,
                w <= 4,
                w <= whole.len(),
                whole == self@,
                self.pos + w <= self.end,
                self.end <= self.buf@.len(),
                v as nat == be_value(whole.take(i as int)),
            decreases w - i,
        {
            // pos + i < end <= buf.len(), so this never saturates.
            let idx = self.pos.saturating_add(i);
            let byte: u8 = match self.buf.get(idx) {
                Some(&b) => b,
                None => 0,
            };
            proof {
                let t = whole.take(i as int);
                assert(whole.take(i as int + 1) =~= t.push(whole[i as int]));
                assert(t.push(whole[i as int]).drop_last() =~= t);
                assert(byte == whole[i as int]);
                super::lemmas_pl::lemma_be_value_bound(t);
                super::lemmas_pl::lemma_pow256_at_most_4(i as nat);
                assert(be_value(whole.take(i as int + 1)) == be_value(t) * 256 + byte as nat);
            }
            // v < 256^i <= 2^24 here (i < 4), so v * 256 + byte < 2^32:
            // this never saturates.
            v = v.saturating_mul(256).saturating_add(byte as u64);
            i = i.saturating_add(1);
        }
        self.pos = self.pos.saturating_add(w);
        proof {
            assert(self@ =~= whole.skip(w as int));
        }
        Some(v)
    }

    /// §3.4: read `n` bytes ([`read_fixed`]), as a slice of the buffer.
    pub fn fixed(&mut self, n: usize) -> (r: Option<&'a [u8]>)
        ensures
            super::contract::fixed_ensures(
                old(self)@,
                n as nat,
                match r {
                    Some(s) => Some(s@),
                    None => None,
                },
                final(self)@,
            ),
    {
        proof {
            use_type_invariant(&*self);
        }
        let avail = self.end.saturating_sub(self.pos);
        if avail < n {
            return None;
        }
        let ghost whole = self@;
        // pos + n <= end, so this never saturates.
        let stop = self.pos.saturating_add(n);
        let s = vstd::slice::slice_subrange(self.buf, self.pos, stop);
        self.pos = stop;
        proof {
            assert(s@ =~= whole.take(n as int));
            assert(self@ =~= whole.skip(n as int));
        }
        Some(s)
    }

    /// §3.4: read a variable-length vector with bounds `floor..ceil`
    /// ([`read_vec`]) and return a cursor over its contents. `ceil` is
    /// below 2^24 (the widest length field is three bytes).
    pub fn vec(&mut self, floor: usize, ceil: usize) -> (r: Option<Cur<'a>>)
        requires
            ceil < 16777216,
        ensures
            super::contract::vec_ensures(
                old(self)@,
                floor as nat,
                ceil as nat,
                match r {
                    Some(c) => Some(c@),
                    None => None,
                },
                final(self)@,
            ),
    {
        proof {
            use_type_invariant(&*self);
        }
        let width: usize = if ceil <= 255 {
            1
        } else if ceil <= 65535 {
            2
        } else {
            3
        };
        let ghost whole = self@;
        let n = self.uint(width)?;
        let ghost after_len = self@;
        proof {
            use_type_invariant(&*self);
            assert(read_uint(whole, width as nat) == Some((n as nat, after_len)));
            assert(len_width(ceil as nat) == width as nat);
        }
        let avail = self.end.saturating_sub(self.pos);
        if n < floor as u64 || n > ceil as u64 || n > avail as u64 {
            proof {
                assert(avail == after_len.len());
                assert(read_vec(whole, floor as nat, ceil as nat) is None);
            }
            return None;
        }
        // n <= avail, so n fits a usize, and pos + n <= end.
        let count = n as usize;
        let stop = self.pos.saturating_add(count);
        let c = Cur { buf: self.buf, pos: self.pos, end: stop };
        self.pos = stop;
        proof {
            assert(c@ =~= after_len.take(n as int));
            assert(self@ =~= after_len.skip(n as int));
        }
        Some(c)
    }
}

} // verus!
