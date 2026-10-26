//! Facts proven about the identifier, length and value framing of the spec
//! ([`super::spec`]): the round trip (`read_*` inverts `encode_*`), DER
//! canonicity (`encode_*` inverts `read_*`, so the encoding of a value is
//! the one the decoder accepted) and the shortest length form. They are
//! evidence that the transcription is right, not part of what the
//! implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Arithmetic on octets.
// ---------------------------------------------------------------------------

/// The first octet of an identifier is its class bits, its form bit and the
/// low five bits: reading them back recovers each.
pub proof fn lemma_first_octet(cb: u8, constructed: bool, low: u8)
    requires
        cb <= 3,
        low <= 31,
    ensures
        ({
            let o = (cb * 64 + (if constructed { 32u8 } else { 0u8 }) + low) as u8;
            &&& o / 64 == cb
            &&& ((o / 32) % 2 == 1) == constructed
            &&& o % 32 == low
        }),
{
    if constructed {
        assert((cb * 64 + 32 + low) / 64 == cb);
        assert(((cb * 64 + 32 + low) / 32) % 2 == 1);
        assert((cb * 64 + 32 + low) % 32 == low);
    } else {
        assert((cb * 64 + low) / 64 == cb);
        assert(((cb * 64 + low) / 32) % 2 == 0);
        assert((cb * 64 + low) % 32 == low);
    }
}

/// An octet is its class bits, form bit and low five bits.
pub proof fn lemma_octet_split(o: u8)
    ensures
        o == (o / 64) * 64 + (if (o / 32) % 2 == 1 { 32u8 } else { 0u8 }) + o % 32,
{
}

/// The class survives a trip through its bits.
pub proof fn lemma_class_bits_roundtrip(class: Class)
    ensures
        class_bits(class) <= 3,
        class_from_bits(class_bits(class)) == class,
{
}

/// The class bits of an octet name its class, which encodes back to them.
pub proof fn lemma_class_from_bits_roundtrip(bits: u8)
    requires
        bits <= 3,
    ensures
        class_bits(class_from_bits(bits)) == bits,
{
}

/// 256^n grows with n.
pub proof fn lemma_pow256_monotone(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow256(a) <= pow256(b),
    decreases b - a,
{
    if a < b {
        lemma_pow256_monotone(a, (b - 1) as nat);
        super::lemmas::lemma_pow256_positive((b - 1) as nat);
    }
}

/// A number below 256^w whose spelling's first octet is zero is below
/// 256^(w-1), and so a spelling with a nonzero first octet is at least
/// 256^(w-1).
pub proof fn lemma_be_value_leading_zero(s: Seq<u8>)
    requires
        s.len() >= 1,
        s[0] == 0,
    ensures
        be_value(s) < pow256((s.len() - 1) as nat),
    decreases s.len(),
{
    let d = s.drop_last();
    if s.len() == 1 {
        assert(d =~= Seq::<u8>::empty());
        assert(be_value(d) == 0);
        assert(s.last() == s[0]);
        assert(be_value(s) == 0);
        assert(pow256(0) == 1);
    } else {
        assert(d[0] == 0);
        lemma_be_value_leading_zero(d);
        assert(pow256((s.len() - 1) as nat) == 256 * pow256((s.len() - 2) as nat));
        assert(be_value(s) == be_value(d) * 256 + s.last() as nat);
    }
}

/// A spelling whose first octet is not zero is at least 256^(w-1).
pub proof fn lemma_be_value_leading_nonzero(s: Seq<u8>)
    requires
        s.len() >= 1,
        s[0] != 0,
    ensures
        be_value(s) >= pow256((s.len() - 1) as nat),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        assert(pow256(0) == 1);
    } else {
        let d = s.drop_last();
        assert(d[0] == s[0]);
        lemma_be_value_leading_nonzero(d);
        assert(pow256((s.len() - 1) as nat) == 256 * pow256((s.len() - 2) as nat));
        assert(be_value(s) == be_value(d) * 256 + s.last() as nat);
    }
}

/// The first octet of `be_bytes(v, w)` is nonzero when `v` is at least
/// 256^(w-1) (and below 256^w).
pub proof fn lemma_be_bytes_first_nonzero(v: nat, w: nat)
    requires
        w >= 1,
        v < pow256(w),
        v >= pow256((w - 1) as nat),
    ensures
        be_bytes(v, w).len() == w,
        be_bytes(v, w)[0] != 0,
{
    super::lemmas::lemma_be_bytes_len(v, w);
    super::lemmas::lemma_be_value_of_be_bytes(v, w);
    let s = be_bytes(v, w);
    if s[0] == 0 {
        lemma_be_value_leading_zero(s);
    }
}

/// A one-octet series spells its low seven bits.
pub proof fn lemma_base128_single(x: u8)
    ensures
        base128(seq![x]) == (x % 128) as nat,
{
    assert(seq![x].drop_last() =~= Seq::<u8>::empty());
    assert(base128(Seq::<u8>::empty()) == 0);
}

/// A two-octet series.
pub proof fn lemma_base128_pair(x: u8, y: u8)
    ensures
        base128(seq![x, y]) == (x % 128) as nat * 128 + (y % 128) as nat,
{
    assert(seq![x, y].drop_last() =~= seq![x]);
    lemma_base128_single(x);
}

// ---------------------------------------------------------------------------
// Identifier octets.
// ---------------------------------------------------------------------------

/// The identifier octets of a tag read back as that tag, wherever they sit
/// in the input and whatever follows.
pub proof fn lemma_read_identifier_encode_identifier(tag: Tag, b: Seq<u8>, pos: nat, end: nat)
    requires
        tag.number <= MAX_TAG_NUMBER,
        pos + encode_identifier(tag).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_identifier(tag).len()) as int) =~= encode_identifier(tag),
    ensures
        read_identifier(b, pos, end) == Some((tag, encode_identifier(tag).len())),
{
    let enc = encode_identifier(tag);
    let cb = class_bits(tag.class);
    lemma_class_bits_roundtrip(tag.class);
    let first = (cb * 64 + (if tag.constructed { 32u8 } else { 0u8 })) as u8;
    assert(b[pos as int] == enc[0]);
    if tag.number < 31 {
        lemma_first_octet(cb, tag.constructed, tag.number as u8);
        assert(enc[0] == (first + tag.number as u8) as u8);
    } else {
        lemma_first_octet(cb, tag.constructed, 31);
        assert(enc[0] == (first + 31) as u8);
        assert(b[pos as int + 1] == enc[1]);
        if tag.number < 128 {
            assert(enc =~= seq![(first + 31) as u8, tag.number as u8]);
            assert(series_end(b, pos + 1, end) == Some((pos + 1) as nat));
            assert(b.subrange(pos as int + 1, pos as int + 2) =~= seq![tag.number as u8]);
            lemma_base128_single(tag.number as u8);
        } else {
            let d1 = (128 + tag.number / 128) as u8;
            let d0 = (tag.number % 128) as u8;
            assert(enc =~= seq![(first + 31) as u8, d1, d0]);
            assert(b[pos as int + 2] == enc[2]);
            assert(d1 >= 128);
            assert(b[pos as int + 1] == d1);
            assert(b[pos as int + 2] == d0);
            assert(d0 < 128);
            assert(pos + 2 < end);
            assert(series_end(b, pos + 2, end) == Some((pos + 2) as nat));
            assert(series_end(b, pos + 1, end) == Some((pos + 2) as nat));
            let s = b.subrange(pos as int + 1, pos as int + 3);
            assert(s =~= seq![d1, d0]);
            lemma_base128_pair(d1, d0);
            assert(base128(s) == tag.number as nat);
        }
    }
}

/// A run of three or more octets, the first with a nonzero low seven bits,
/// spells a number of at least 2^14.
pub proof fn lemma_base128_three_digits(b: Seq<u8>, i: int, j: int)
    requires
        0 <= i,
        i + 3 <= j <= b.len(),
        b[i] % 128 != 0,
    ensures
        base128(b.subrange(i, j)) >= 16384,
{
    super::lemmas::lemma_base128_monotone(b, i, i + 3, j);
    let s = b.subrange(i, i + 3);
    assert(s.drop_last() =~= b.subrange(i, i + 2));
    assert(b.subrange(i, i + 2).drop_last() =~= b.subrange(i, i + 1));
    assert(b.subrange(i, i + 1).drop_last() =~= Seq::<u8>::empty());
    assert(b.subrange(i, i + 1) =~= seq![b[i]]);
    lemma_base128_single(b[i]);
    assert(base128(b.subrange(i, i + 2)) == base128(b.subrange(i, i + 1)) * 128 + (b[i + 1] % 128) as nat);
    assert(base128(s) == base128(b.subrange(i, i + 2)) * 128 + (b[i + 2] % 128) as nat);
}

/// The identifier octets that were read are the encoding of the tag that was
/// read: encoding the tag gives back the bytes (DER canonicity).
pub proof fn lemma_encode_identifier_read_identifier(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_identifier(b, pos, end) {
            Some((tag, n)) => {
                &&& tag.number <= MAX_TAG_NUMBER
                &&& pos + n <= end
                &&& b.subrange(pos as int, (pos + n) as int) =~= encode_identifier(tag)
            },
            None => true,
        },
{
    super::lemmas::lemma_read_identifier_bounds(b, pos, end);
    if let Some((tag, n)) = read_identifier(b, pos, end) {
        let o = b[pos as int];
        lemma_octet_split(o);
        let cb = o / 64;
        lemma_class_from_bits_roundtrip(cb);
        let constructed = (o / 32) % 2 == 1;
        let first = (cb * 64 + (if constructed { 32u8 } else { 0u8 })) as u8;
        assert(tag.constructed == constructed);
        assert(class_bits(tag.class) == cb);
        if o % 32 != 31 {
            assert(n == 1);
            assert(tag.number == (o % 32) as u32);
            assert(encode_identifier(tag) =~= seq![o]);
            assert(b.subrange(pos as int, pos as int + 1) =~= seq![o]);
        } else {
            super::lemmas::lemma_series_end_in_range(b, pos + 1, end);
            let j = series_end(b, pos + 1, end).unwrap();
            let run = b.subrange(pos as int + 1, j as int + 1);
            assert(tag.number as nat == base128(run));
            assert(b[pos as int + 1] % 128 != 0);
            assert(tag.number >= 31);
            if j >= pos + 3 {
                lemma_base128_three_digits(b, pos as int + 1, j as int + 1);
                assert(false);
            }
            if j == pos + 1 {
                // One subsequent octet, below 128.
                assert(b[pos as int + 1] < 128);
                assert(run =~= seq![b[pos as int + 1]]);
                lemma_base128_single(b[pos as int + 1]);
                assert(tag.number as nat == (b[pos as int + 1] % 128) as nat);
                assert(tag.number < 128);
                assert(encode_identifier(tag) =~= seq![o, b[pos as int + 1]]);
                assert(b.subrange(pos as int, pos as int + 2) =~= seq![o, b[pos as int + 1]]);
            } else {
                // Two subsequent octets: the first at least 128.
                assert(j == pos + 2);
                let x = b[pos as int + 1];
                let y = b[pos as int + 2];
                assert(x >= 128) by {
                    if x < 128 {
                        assert(series_end(b, pos + 1, end) == Some((pos + 1) as nat));
                    }
                }
                assert(run =~= seq![x, y]);
                lemma_base128_pair(x, y);
                assert(tag.number as nat == (x % 128) as nat * 128 + (y % 128) as nat);
                assert(tag.number / 128 == (x % 128) as nat);
                assert(tag.number % 128 == y as nat);
                assert(tag.number >= 128);
                assert(encode_identifier(tag) =~= seq![o, x, y]);
                assert(b.subrange(pos as int, pos as int + 3) =~= seq![o, x, y]);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Length octets.
// ---------------------------------------------------------------------------

/// For a length of 128 or more, the number of octets the encoder chooses is
/// the least `w` with `len < 256^w`, and the length is at least
/// 256^(w-1): the first octet of its spelling is nonzero.
pub proof fn lemma_length_octets_bounds(len: nat)
    requires
        128 <= len < pow256(8),
    ensures
        1 <= length_octets(len) <= 8,
        len < pow256(length_octets(len)),
        len >= pow256((length_octets(len) - 1) as nat),
        forall|w: nat| w < length_octets(len) ==> len >= pow256(w),
{
    super::lemmas::lemma_pow256_8();
    assert forall|w: nat| w < length_octets(len) implies len >= pow256(w) by {
        lemma_pow256_monotone(w, (length_octets(len) - 1) as nat);
    }
}

/// `encode_length` is the shortest form (§10.1): one octet below 128, and
/// otherwise the initial octet and the fewest octets that hold the length:
/// no smaller count of octets could.
pub proof fn lemma_encode_length_shortest(len: nat)
    requires
        len < pow256(8),
    ensures
        len < 128 ==> encode_length(len).len() == 1,
        len >= 128 ==> {
            let w = length_octets(len);
            &&& encode_length(len).len() == 1 + w
            &&& len < pow256(w)
            &&& forall|w2: nat| w2 < w ==> len >= pow256(w2)
        },
{
    if len >= 128 {
        lemma_length_octets_bounds(len);
        super::lemmas::lemma_be_bytes_len(len, length_octets(len));
    }
}

/// The length octets of a length below 2^64 read back as that length.
pub proof fn lemma_read_length_encode_length(len: nat, b: Seq<u8>, pos: nat, end: nat)
    requires
        len < pow256(8),
        pos + encode_length(len).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_length(len).len()) as int) =~= encode_length(len),
    ensures
        read_length(b, pos, end) == Some((len, encode_length(len).len())),
{
    let enc = encode_length(len);
    assert(b[pos as int] == enc[0]);
    if len >= 128 {
        let w = length_octets(len);
        lemma_length_octets_bounds(len);
        super::lemmas::lemma_be_bytes_len(len, w);
        assert(enc[0] == (128 + w) as u8);
        assert(pos + 1 + w <= end);
        // The subsequent octets are the spelling of `len`.
        let sub = b.subrange(pos as int + 1, pos as int + 1 + w as int);
        assert(sub =~= be_bytes(len, w)) by {
            assert forall|i: int| 0 <= i < w implies #[trigger] sub[i] == be_bytes(len, w)[i] by {
                assert(b.subrange(pos as int, (pos + enc.len()) as int)[1 + i] == enc[1 + i]);
                assert(enc[1 + i] == be_bytes(len, w)[i]);
            }
        }
        lemma_be_bytes_first_nonzero(len, w);
        super::lemmas::lemma_be_value_of_be_bytes(len, w);
        assert(b[pos as int + 1] == be_bytes(len, w)[0]);
    }
}

/// The length octets that were read are the encoding of the length that was
/// read (DER canonicity: shortest form, no leading zero, no indefinite
/// form), and the length is below 2^64.
pub proof fn lemma_encode_length_read_length(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_length(b, pos, end) {
            Some((v, n)) => {
                &&& v < pow256(8)
                &&& pos + n <= end
                &&& b.subrange(pos as int, (pos + n) as int) =~= encode_length(v)
            },
            None => true,
        },
{
    super::lemmas::lemma_pow256_8();
    if let Some((v, n)) = read_length(b, pos, end) {
        let f = b[pos as int];
        if f < 128 {
            assert(encode_length(v) =~= seq![f]);
            assert(b.subrange(pos as int, pos as int + 1) =~= seq![f]);
        } else {
            let k = (f - 128) as nat;
            let sub = b.subrange(pos as int + 1, pos as int + 1 + k as int);
            super::lemmas::lemma_be_value_bound(sub);
            lemma_pow256_monotone(k, 8);
            assert(sub.len() == k);
            assert(b[pos as int + 1] != 0);
            assert(sub[0] == b[pos as int + 1]);
            lemma_be_value_leading_nonzero(sub);
            super::lemmas::lemma_be_bytes_of_be_value(sub);
            // `v` needs exactly `k` octets: it is below 256^k and at least
            // 256^(k-1).
            assert(length_octets(v) == k) by {
                assert(pow256(1) == 256);
                if k == 1 {
                    assert(v < 256);
                } else {
                    lemma_pow256_monotone(1, (k - 1) as nat);
                    assert(v >= 256);
                }
            }
            assert(encode_length(v) =~= seq![f] + be_bytes(v, k));
            assert(b.subrange(pos as int, (pos + n) as int) =~= seq![f] + sub);
        }
    }
}


// ---------------------------------------------------------------------------
// A whole value.
// ---------------------------------------------------------------------------

/// If `a + c` sits at `pos`, then `a` sits at `pos` and `c` right after it.
pub proof fn lemma_subrange_split(b: Seq<u8>, pos: nat, a: Seq<u8>, c: Seq<u8>)
    requires
        pos + a.len() + c.len() <= b.len(),
        b.subrange(pos as int, (pos + a.len() + c.len()) as int) =~= a + c,
    ensures
        b.subrange(pos as int, (pos + a.len()) as int) =~= a,
        b.subrange((pos + a.len()) as int, (pos + a.len() + c.len()) as int) =~= c,
{
    let whole = b.subrange(pos as int, (pos + a.len() + c.len()) as int);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] b.subrange(pos as int, (pos + a.len()) as int)[i] == a[i] by {
        assert(whole[i] == (a + c)[i]);
    }
    assert forall|i: int| 0 <= i < c.len() implies #[trigger] b.subrange(
        (pos + a.len()) as int,
        (pos + a.len() + c.len()) as int,
    )[i] == c[i] by {
        assert(whole[a.len() + i] == (a + c)[a.len() + i]);
    }
}

/// The encoding of a value, found at `pos` in the input, reads back as that
/// value: the tag, and the contents range, wherever the encoding sits and
/// whatever follows it.
pub proof fn lemma_read_tlv_encode_tlv(tag: Tag, contents: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        tlv_ok(tag, contents),
        pos + encode_tlv(tag, contents).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_tlv(tag, contents).len()) as int) =~= encode_tlv(tag, contents),
    ensures
        ({
            let il = encode_identifier(tag).len();
            let ll = encode_length(contents.len()).len();
            &&& read_tlv(b, pos, end) == Some(
                Tlv { tag, cstart: pos + il + ll, cend: pos + il + ll + contents.len() },
            )
            &&& b.subrange((pos + il + ll) as int, (pos + il + ll + contents.len()) as int) =~= contents
        }),
{
    let id = encode_identifier(tag);
    let ln = encode_length(contents.len());
    let il = id.len();
    let ll = ln.len();
    assert(encode_tlv(tag, contents) == id + ln + contents);
    assert(id + ln + contents =~= id + (ln + contents));
    lemma_subrange_split(b, pos, id, ln + contents);
    assert(pos + il + (ln + contents).len() <= end);
    lemma_subrange_split(b, pos + il, ln, contents);
    lemma_read_identifier_encode_identifier(tag, b, pos, end);
    super::lemmas::lemma_pow256_8();
    lemma_read_length_encode_length(contents.len(), b, pos + il, end);
}

/// The value that was read is the encoding of its tag and contents (DER
/// canonicity: the bytes are the one encoding the standard allows), and
/// its tag and length are ones the encoder accepts.
pub proof fn lemma_encode_tlv_read_tlv(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_tlv(b, pos, end) {
            Some(t) => {
                &&& tlv_ok(t.tag, b.subrange(t.cstart as int, t.cend as int))
                &&& t.cend <= end
                &&& b.subrange(pos as int, t.cend as int) =~= encode_tlv(t.tag, b.subrange(t.cstart as int, t.cend as int))
            },
            None => true,
        },
{
    super::lemmas::lemma_pow256_8();
    super::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some(t) = read_tlv(b, pos, end) {
        let (tag, id_len) = read_identifier(b, pos, end).unwrap();
        lemma_encode_identifier_read_identifier(b, pos, end);
        super::lemmas::lemma_read_identifier_bounds(b, pos, end);
        let (len, len_len) = read_length(b, pos + id_len, end).unwrap();
        lemma_encode_length_read_length(b, pos + id_len, end);
        let c = b.subrange(t.cstart as int, t.cend as int);
        assert(c.len() == len);
        assert(b.subrange(pos as int, t.cend as int) =~= b.subrange(pos as int, (pos + id_len) as int)
            + b.subrange((pos + id_len) as int, (pos + id_len + len_len) as int) + c);
    }
}

} // verus!
