//! Facts about the flag register of `clazel_x64::spec`, for the bounds-check
//! sequence ([`super::spec::check_instr`]): after `add`, `cmp` the carry and
//! zero flags say what the operands were, and `jb`, `ja`, `cmovae` read them.
//!
//! The flags are bits of a `u32` ([`set_bit32`], [`bit`]); the six positions
//! the model writes are `0 2 4 6 7 11`. Everything here is about those. (The
//! integer lemmas `int_*` are generated, one per pair of positions, with
//! literal divisors and the quotient and remainder written out, so that the
//! solver does not have to find them.)

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The positions of the user flags `cf pf af zf sf of`.
pub open spec fn flag_pos(k: nat) -> bool {
    k == 0 || k == 2 || k == 4 || k == 6 || k == 7 || k == 11
}

/// Clearing bit 0 and setting it to `c` does not change bit 2.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_0_2(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 1) % 2) * 1 + c * 1) / 4) % 2 == (x / 4) % 2,
{
    let a = x / 4;
    let z = x % 4;
    let y = z / 1;
    let r = z % 1;
    assert(z == 1 * y + r);
    assert(x == 4 * a + z);
    assert(0 <= y < 4);
    assert(x == 1 * (4 * a + y) + r);
    assert(x / 1 == 4 * a + y);
    let b = (x / 1) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 4);
    assert(x - b * 1 + c * 1 == 4 * a + (1 * y2 + r));
    assert((x - b * 1 + c * 1) / 4 == a);
}

/// Clearing bit 0 and setting it to `c` does not change bit 4.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_0_4(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 1) % 2) * 1 + c * 1) / 16) % 2 == (x / 16) % 2,
{
    let a = x / 16;
    let z = x % 16;
    let y = z / 1;
    let r = z % 1;
    assert(z == 1 * y + r);
    assert(x == 16 * a + z);
    assert(0 <= y < 16);
    assert(x == 1 * (16 * a + y) + r);
    assert(x / 1 == 16 * a + y);
    let b = (x / 1) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 16);
    assert(x - b * 1 + c * 1 == 16 * a + (1 * y2 + r));
    assert((x - b * 1 + c * 1) / 16 == a);
}

/// Clearing bit 0 and setting it to `c` does not change bit 6.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_0_6(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 1) % 2) * 1 + c * 1) / 64) % 2 == (x / 64) % 2,
{
    let a = x / 64;
    let z = x % 64;
    let y = z / 1;
    let r = z % 1;
    assert(z == 1 * y + r);
    assert(x == 64 * a + z);
    assert(0 <= y < 64);
    assert(x == 1 * (64 * a + y) + r);
    assert(x / 1 == 64 * a + y);
    let b = (x / 1) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 64);
    assert(x - b * 1 + c * 1 == 64 * a + (1 * y2 + r));
    assert((x - b * 1 + c * 1) / 64 == a);
}

/// Clearing bit 0 and setting it to `c` does not change bit 7.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_0_7(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 1) % 2) * 1 + c * 1) / 128) % 2 == (x / 128) % 2,
{
    let a = x / 128;
    let z = x % 128;
    let y = z / 1;
    let r = z % 1;
    assert(z == 1 * y + r);
    assert(x == 128 * a + z);
    assert(0 <= y < 128);
    assert(x == 1 * (128 * a + y) + r);
    assert(x / 1 == 128 * a + y);
    let b = (x / 1) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 128);
    assert(x - b * 1 + c * 1 == 128 * a + (1 * y2 + r));
    assert((x - b * 1 + c * 1) / 128 == a);
}

/// Clearing bit 0 and setting it to `c` does not change bit 11.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_0_11(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 1) % 2) * 1 + c * 1) / 2048) % 2 == (x / 2048) % 2,
{
    let a = x / 2048;
    let z = x % 2048;
    let y = z / 1;
    let r = z % 1;
    assert(z == 1 * y + r);
    assert(x == 2048 * a + z);
    assert(0 <= y < 2048);
    assert(x == 1 * (2048 * a + y) + r);
    assert(x / 1 == 2048 * a + y);
    let b = (x / 1) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 2048);
    assert(x - b * 1 + c * 1 == 2048 * a + (1 * y2 + r));
    assert((x - b * 1 + c * 1) / 2048 == a);
}

/// Setting bit 0 of `w` changes that bit to `v % 2` and no other of the six flag bits.
proof fn lemma_set_bit_0(w: u32, v: int)
    ensures
        bit(set_bit32(w, 0, v) as int, 0) == v % 2,
        forall|k2: nat| flag_pos(k2) && k2 != 0 ==> bit(set_bit32(w, 0, v) as int, k2) == bit(w as int, k2),
{
    vstd::arithmetic::power2::lemma2_to64();
    let x = w as int;
    let c = v % 2;
    assert(p2(0) == 1);
    let cleared = x - bit(x, 0) * p2(0);
    let n = cleared + c * p2(0);
    assert(n == x - ((x / 1) % 2) * 1 + c * 1);
    assert(0 <= n < 0x1_0000_0000) by {
        assert(0 <= c < 2);
        assert(x == 1 * (x / 1) + x % 1);
    }
    assert(set_bit32(w, 0, v) as int == n);
    assert(bit(n, 0) == (n / 1) % 2);
    assert forall|k2: nat| flag_pos(k2) && k2 != 0 implies bit(set_bit32(w, 0, v) as int, k2) == bit(w as int, k2) by {
        assert(k2 == 0 || k2 == 2 || k2 == 4 || k2 == 6 || k2 == 7 || k2 == 11);
        if k2 == 2 { int_0_2(x, c); assert(p2(2) == 4); }
        if k2 == 4 { int_0_4(x, c); assert(p2(4) == 16); }
        if k2 == 6 { int_0_6(x, c); assert(p2(6) == 64); }
        if k2 == 7 { int_0_7(x, c); assert(p2(7) == 128); }
        if k2 == 11 { int_0_11(x, c); assert(p2(11) == 2048); }
    }
}

/// Clearing bit 2 and setting it to `c` does not change bit 0.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_2_0(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 4) % 2) * 4 + c * 4) / 1) % 2 == (x / 1) % 2,
{
    let q = x / 4;
    let r = x % 4;
    let b = q % 2;
    assert(x == 4 * q + r);
    let w = q - b + c;
    assert(x - b * 4 + c * 4 == 4 * w + r);
    let rr = r / 1;
    let r2 = r % 1;
    assert(r == 1 * rr + r2);
    assert(x - b * 4 + c * 4 == 1 * (4 * w + rr) + r2);
    assert(x == 1 * (4 * q + rr) + r2);
    assert((x - b * 4 + c * 4) / 1 == 4 * w + rr);
    assert(x / 1 == 4 * q + rr);
    assert((4 * w + rr) % 2 == rr % 2);
    assert((4 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 2 and setting it to `c` does not change bit 4.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_2_4(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 4) % 2) * 4 + c * 4) / 16) % 2 == (x / 16) % 2,
{
    let a = x / 16;
    let z = x % 16;
    let y = z / 4;
    let r = z % 4;
    assert(z == 4 * y + r);
    assert(x == 16 * a + z);
    assert(0 <= y < 4);
    assert(x == 4 * (4 * a + y) + r);
    assert(x / 4 == 4 * a + y);
    let b = (x / 4) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 4);
    assert(x - b * 4 + c * 4 == 16 * a + (4 * y2 + r));
    assert((x - b * 4 + c * 4) / 16 == a);
}

/// Clearing bit 2 and setting it to `c` does not change bit 6.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_2_6(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 4) % 2) * 4 + c * 4) / 64) % 2 == (x / 64) % 2,
{
    let a = x / 64;
    let z = x % 64;
    let y = z / 4;
    let r = z % 4;
    assert(z == 4 * y + r);
    assert(x == 64 * a + z);
    assert(0 <= y < 16);
    assert(x == 4 * (16 * a + y) + r);
    assert(x / 4 == 16 * a + y);
    let b = (x / 4) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 16);
    assert(x - b * 4 + c * 4 == 64 * a + (4 * y2 + r));
    assert((x - b * 4 + c * 4) / 64 == a);
}

/// Clearing bit 2 and setting it to `c` does not change bit 7.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_2_7(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 4) % 2) * 4 + c * 4) / 128) % 2 == (x / 128) % 2,
{
    let a = x / 128;
    let z = x % 128;
    let y = z / 4;
    let r = z % 4;
    assert(z == 4 * y + r);
    assert(x == 128 * a + z);
    assert(0 <= y < 32);
    assert(x == 4 * (32 * a + y) + r);
    assert(x / 4 == 32 * a + y);
    let b = (x / 4) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 32);
    assert(x - b * 4 + c * 4 == 128 * a + (4 * y2 + r));
    assert((x - b * 4 + c * 4) / 128 == a);
}

/// Clearing bit 2 and setting it to `c` does not change bit 11.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_2_11(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 4) % 2) * 4 + c * 4) / 2048) % 2 == (x / 2048) % 2,
{
    let a = x / 2048;
    let z = x % 2048;
    let y = z / 4;
    let r = z % 4;
    assert(z == 4 * y + r);
    assert(x == 2048 * a + z);
    assert(0 <= y < 512);
    assert(x == 4 * (512 * a + y) + r);
    assert(x / 4 == 512 * a + y);
    let b = (x / 4) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 512);
    assert(x - b * 4 + c * 4 == 2048 * a + (4 * y2 + r));
    assert((x - b * 4 + c * 4) / 2048 == a);
}

/// Setting bit 2 of `w` changes that bit to `v % 2` and no other of the six flag bits.
proof fn lemma_set_bit_2(w: u32, v: int)
    ensures
        bit(set_bit32(w, 2, v) as int, 2) == v % 2,
        forall|k2: nat| flag_pos(k2) && k2 != 2 ==> bit(set_bit32(w, 2, v) as int, k2) == bit(w as int, k2),
{
    vstd::arithmetic::power2::lemma2_to64();
    let x = w as int;
    let c = v % 2;
    assert(p2(2) == 4);
    let cleared = x - bit(x, 2) * p2(2);
    let n = cleared + c * p2(2);
    assert(n == x - ((x / 4) % 2) * 4 + c * 4);
    assert(0 <= n < 0x1_0000_0000) by {
        assert(0 <= c < 2);
        assert(x == 4 * (x / 4) + x % 4);
    }
    assert(set_bit32(w, 2, v) as int == n);
    assert(bit(n, 2) == (n / 4) % 2);
    assert forall|k2: nat| flag_pos(k2) && k2 != 2 implies bit(set_bit32(w, 2, v) as int, k2) == bit(w as int, k2) by {
        assert(k2 == 0 || k2 == 2 || k2 == 4 || k2 == 6 || k2 == 7 || k2 == 11);
        if k2 == 0 { int_2_0(x, c); assert(p2(0) == 1); }
        if k2 == 4 { int_2_4(x, c); assert(p2(4) == 16); }
        if k2 == 6 { int_2_6(x, c); assert(p2(6) == 64); }
        if k2 == 7 { int_2_7(x, c); assert(p2(7) == 128); }
        if k2 == 11 { int_2_11(x, c); assert(p2(11) == 2048); }
    }
}

/// Clearing bit 4 and setting it to `c` does not change bit 0.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_4_0(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 16) % 2) * 16 + c * 16) / 1) % 2 == (x / 1) % 2,
{
    let q = x / 16;
    let r = x % 16;
    let b = q % 2;
    assert(x == 16 * q + r);
    let w = q - b + c;
    assert(x - b * 16 + c * 16 == 16 * w + r);
    let rr = r / 1;
    let r2 = r % 1;
    assert(r == 1 * rr + r2);
    assert(x - b * 16 + c * 16 == 1 * (16 * w + rr) + r2);
    assert(x == 1 * (16 * q + rr) + r2);
    assert((x - b * 16 + c * 16) / 1 == 16 * w + rr);
    assert(x / 1 == 16 * q + rr);
    assert((16 * w + rr) % 2 == rr % 2);
    assert((16 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 4 and setting it to `c` does not change bit 2.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_4_2(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 16) % 2) * 16 + c * 16) / 4) % 2 == (x / 4) % 2,
{
    let q = x / 16;
    let r = x % 16;
    let b = q % 2;
    assert(x == 16 * q + r);
    let w = q - b + c;
    assert(x - b * 16 + c * 16 == 16 * w + r);
    let rr = r / 4;
    let r2 = r % 4;
    assert(r == 4 * rr + r2);
    assert(x - b * 16 + c * 16 == 4 * (4 * w + rr) + r2);
    assert(x == 4 * (4 * q + rr) + r2);
    assert((x - b * 16 + c * 16) / 4 == 4 * w + rr);
    assert(x / 4 == 4 * q + rr);
    assert((4 * w + rr) % 2 == rr % 2);
    assert((4 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 4 and setting it to `c` does not change bit 6.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_4_6(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 16) % 2) * 16 + c * 16) / 64) % 2 == (x / 64) % 2,
{
    let a = x / 64;
    let z = x % 64;
    let y = z / 16;
    let r = z % 16;
    assert(z == 16 * y + r);
    assert(x == 64 * a + z);
    assert(0 <= y < 4);
    assert(x == 16 * (4 * a + y) + r);
    assert(x / 16 == 4 * a + y);
    let b = (x / 16) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 4);
    assert(x - b * 16 + c * 16 == 64 * a + (16 * y2 + r));
    assert((x - b * 16 + c * 16) / 64 == a);
}

/// Clearing bit 4 and setting it to `c` does not change bit 7.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_4_7(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 16) % 2) * 16 + c * 16) / 128) % 2 == (x / 128) % 2,
{
    let a = x / 128;
    let z = x % 128;
    let y = z / 16;
    let r = z % 16;
    assert(z == 16 * y + r);
    assert(x == 128 * a + z);
    assert(0 <= y < 8);
    assert(x == 16 * (8 * a + y) + r);
    assert(x / 16 == 8 * a + y);
    let b = (x / 16) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 8);
    assert(x - b * 16 + c * 16 == 128 * a + (16 * y2 + r));
    assert((x - b * 16 + c * 16) / 128 == a);
}

/// Clearing bit 4 and setting it to `c` does not change bit 11.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_4_11(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 16) % 2) * 16 + c * 16) / 2048) % 2 == (x / 2048) % 2,
{
    let a = x / 2048;
    let z = x % 2048;
    let y = z / 16;
    let r = z % 16;
    assert(z == 16 * y + r);
    assert(x == 2048 * a + z);
    assert(0 <= y < 128);
    assert(x == 16 * (128 * a + y) + r);
    assert(x / 16 == 128 * a + y);
    let b = (x / 16) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 128);
    assert(x - b * 16 + c * 16 == 2048 * a + (16 * y2 + r));
    assert((x - b * 16 + c * 16) / 2048 == a);
}

/// Setting bit 4 of `w` changes that bit to `v % 2` and no other of the six flag bits.
proof fn lemma_set_bit_4(w: u32, v: int)
    ensures
        bit(set_bit32(w, 4, v) as int, 4) == v % 2,
        forall|k2: nat| flag_pos(k2) && k2 != 4 ==> bit(set_bit32(w, 4, v) as int, k2) == bit(w as int, k2),
{
    vstd::arithmetic::power2::lemma2_to64();
    let x = w as int;
    let c = v % 2;
    assert(p2(4) == 16);
    let cleared = x - bit(x, 4) * p2(4);
    let n = cleared + c * p2(4);
    assert(n == x - ((x / 16) % 2) * 16 + c * 16);
    assert(0 <= n < 0x1_0000_0000) by {
        assert(0 <= c < 2);
        assert(x == 16 * (x / 16) + x % 16);
    }
    assert(set_bit32(w, 4, v) as int == n);
    assert(bit(n, 4) == (n / 16) % 2);
    assert forall|k2: nat| flag_pos(k2) && k2 != 4 implies bit(set_bit32(w, 4, v) as int, k2) == bit(w as int, k2) by {
        assert(k2 == 0 || k2 == 2 || k2 == 4 || k2 == 6 || k2 == 7 || k2 == 11);
        if k2 == 0 { int_4_0(x, c); assert(p2(0) == 1); }
        if k2 == 2 { int_4_2(x, c); assert(p2(2) == 4); }
        if k2 == 6 { int_4_6(x, c); assert(p2(6) == 64); }
        if k2 == 7 { int_4_7(x, c); assert(p2(7) == 128); }
        if k2 == 11 { int_4_11(x, c); assert(p2(11) == 2048); }
    }
}

/// Clearing bit 6 and setting it to `c` does not change bit 0.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_6_0(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 64) % 2) * 64 + c * 64) / 1) % 2 == (x / 1) % 2,
{
    let q = x / 64;
    let r = x % 64;
    let b = q % 2;
    assert(x == 64 * q + r);
    let w = q - b + c;
    assert(x - b * 64 + c * 64 == 64 * w + r);
    let rr = r / 1;
    let r2 = r % 1;
    assert(r == 1 * rr + r2);
    assert(x - b * 64 + c * 64 == 1 * (64 * w + rr) + r2);
    assert(x == 1 * (64 * q + rr) + r2);
    assert((x - b * 64 + c * 64) / 1 == 64 * w + rr);
    assert(x / 1 == 64 * q + rr);
    assert((64 * w + rr) % 2 == rr % 2);
    assert((64 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 6 and setting it to `c` does not change bit 2.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_6_2(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 64) % 2) * 64 + c * 64) / 4) % 2 == (x / 4) % 2,
{
    let q = x / 64;
    let r = x % 64;
    let b = q % 2;
    assert(x == 64 * q + r);
    let w = q - b + c;
    assert(x - b * 64 + c * 64 == 64 * w + r);
    let rr = r / 4;
    let r2 = r % 4;
    assert(r == 4 * rr + r2);
    assert(x - b * 64 + c * 64 == 4 * (16 * w + rr) + r2);
    assert(x == 4 * (16 * q + rr) + r2);
    assert((x - b * 64 + c * 64) / 4 == 16 * w + rr);
    assert(x / 4 == 16 * q + rr);
    assert((16 * w + rr) % 2 == rr % 2);
    assert((16 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 6 and setting it to `c` does not change bit 4.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_6_4(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 64) % 2) * 64 + c * 64) / 16) % 2 == (x / 16) % 2,
{
    let q = x / 64;
    let r = x % 64;
    let b = q % 2;
    assert(x == 64 * q + r);
    let w = q - b + c;
    assert(x - b * 64 + c * 64 == 64 * w + r);
    let rr = r / 16;
    let r2 = r % 16;
    assert(r == 16 * rr + r2);
    assert(x - b * 64 + c * 64 == 16 * (4 * w + rr) + r2);
    assert(x == 16 * (4 * q + rr) + r2);
    assert((x - b * 64 + c * 64) / 16 == 4 * w + rr);
    assert(x / 16 == 4 * q + rr);
    assert((4 * w + rr) % 2 == rr % 2);
    assert((4 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 6 and setting it to `c` does not change bit 7.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_6_7(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 64) % 2) * 64 + c * 64) / 128) % 2 == (x / 128) % 2,
{
    let a = x / 128;
    let z = x % 128;
    let y = z / 64;
    let r = z % 64;
    assert(z == 64 * y + r);
    assert(x == 128 * a + z);
    assert(0 <= y < 2);
    assert(x == 64 * (2 * a + y) + r);
    assert(x / 64 == 2 * a + y);
    let b = (x / 64) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 2);
    assert(x - b * 64 + c * 64 == 128 * a + (64 * y2 + r));
    assert((x - b * 64 + c * 64) / 128 == a);
}

/// Clearing bit 6 and setting it to `c` does not change bit 11.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_6_11(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 64) % 2) * 64 + c * 64) / 2048) % 2 == (x / 2048) % 2,
{
    let a = x / 2048;
    let z = x % 2048;
    let y = z / 64;
    let r = z % 64;
    assert(z == 64 * y + r);
    assert(x == 2048 * a + z);
    assert(0 <= y < 32);
    assert(x == 64 * (32 * a + y) + r);
    assert(x / 64 == 32 * a + y);
    let b = (x / 64) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 32);
    assert(x - b * 64 + c * 64 == 2048 * a + (64 * y2 + r));
    assert((x - b * 64 + c * 64) / 2048 == a);
}

/// Setting bit 6 of `w` changes that bit to `v % 2` and no other of the six flag bits.
proof fn lemma_set_bit_6(w: u32, v: int)
    ensures
        bit(set_bit32(w, 6, v) as int, 6) == v % 2,
        forall|k2: nat| flag_pos(k2) && k2 != 6 ==> bit(set_bit32(w, 6, v) as int, k2) == bit(w as int, k2),
{
    vstd::arithmetic::power2::lemma2_to64();
    let x = w as int;
    let c = v % 2;
    assert(p2(6) == 64);
    let cleared = x - bit(x, 6) * p2(6);
    let n = cleared + c * p2(6);
    assert(n == x - ((x / 64) % 2) * 64 + c * 64);
    assert(0 <= n < 0x1_0000_0000) by {
        assert(0 <= c < 2);
        assert(x == 64 * (x / 64) + x % 64);
    }
    assert(set_bit32(w, 6, v) as int == n);
    assert(bit(n, 6) == (n / 64) % 2);
    assert forall|k2: nat| flag_pos(k2) && k2 != 6 implies bit(set_bit32(w, 6, v) as int, k2) == bit(w as int, k2) by {
        assert(k2 == 0 || k2 == 2 || k2 == 4 || k2 == 6 || k2 == 7 || k2 == 11);
        if k2 == 0 { int_6_0(x, c); assert(p2(0) == 1); }
        if k2 == 2 { int_6_2(x, c); assert(p2(2) == 4); }
        if k2 == 4 { int_6_4(x, c); assert(p2(4) == 16); }
        if k2 == 7 { int_6_7(x, c); assert(p2(7) == 128); }
        if k2 == 11 { int_6_11(x, c); assert(p2(11) == 2048); }
    }
}

/// Clearing bit 7 and setting it to `c` does not change bit 0.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_7_0(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 128) % 2) * 128 + c * 128) / 1) % 2 == (x / 1) % 2,
{
    let q = x / 128;
    let r = x % 128;
    let b = q % 2;
    assert(x == 128 * q + r);
    let w = q - b + c;
    assert(x - b * 128 + c * 128 == 128 * w + r);
    let rr = r / 1;
    let r2 = r % 1;
    assert(r == 1 * rr + r2);
    assert(x - b * 128 + c * 128 == 1 * (128 * w + rr) + r2);
    assert(x == 1 * (128 * q + rr) + r2);
    assert((x - b * 128 + c * 128) / 1 == 128 * w + rr);
    assert(x / 1 == 128 * q + rr);
    assert((128 * w + rr) % 2 == rr % 2);
    assert((128 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 7 and setting it to `c` does not change bit 2.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_7_2(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 128) % 2) * 128 + c * 128) / 4) % 2 == (x / 4) % 2,
{
    let q = x / 128;
    let r = x % 128;
    let b = q % 2;
    assert(x == 128 * q + r);
    let w = q - b + c;
    assert(x - b * 128 + c * 128 == 128 * w + r);
    let rr = r / 4;
    let r2 = r % 4;
    assert(r == 4 * rr + r2);
    assert(x - b * 128 + c * 128 == 4 * (32 * w + rr) + r2);
    assert(x == 4 * (32 * q + rr) + r2);
    assert((x - b * 128 + c * 128) / 4 == 32 * w + rr);
    assert(x / 4 == 32 * q + rr);
    assert((32 * w + rr) % 2 == rr % 2);
    assert((32 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 7 and setting it to `c` does not change bit 4.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_7_4(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 128) % 2) * 128 + c * 128) / 16) % 2 == (x / 16) % 2,
{
    let q = x / 128;
    let r = x % 128;
    let b = q % 2;
    assert(x == 128 * q + r);
    let w = q - b + c;
    assert(x - b * 128 + c * 128 == 128 * w + r);
    let rr = r / 16;
    let r2 = r % 16;
    assert(r == 16 * rr + r2);
    assert(x - b * 128 + c * 128 == 16 * (8 * w + rr) + r2);
    assert(x == 16 * (8 * q + rr) + r2);
    assert((x - b * 128 + c * 128) / 16 == 8 * w + rr);
    assert(x / 16 == 8 * q + rr);
    assert((8 * w + rr) % 2 == rr % 2);
    assert((8 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 7 and setting it to `c` does not change bit 6.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_7_6(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 128) % 2) * 128 + c * 128) / 64) % 2 == (x / 64) % 2,
{
    let q = x / 128;
    let r = x % 128;
    let b = q % 2;
    assert(x == 128 * q + r);
    let w = q - b + c;
    assert(x - b * 128 + c * 128 == 128 * w + r);
    let rr = r / 64;
    let r2 = r % 64;
    assert(r == 64 * rr + r2);
    assert(x - b * 128 + c * 128 == 64 * (2 * w + rr) + r2);
    assert(x == 64 * (2 * q + rr) + r2);
    assert((x - b * 128 + c * 128) / 64 == 2 * w + rr);
    assert(x / 64 == 2 * q + rr);
    assert((2 * w + rr) % 2 == rr % 2);
    assert((2 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 7 and setting it to `c` does not change bit 11.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_7_11(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 128) % 2) * 128 + c * 128) / 2048) % 2 == (x / 2048) % 2,
{
    let a = x / 2048;
    let z = x % 2048;
    let y = z / 128;
    let r = z % 128;
    assert(z == 128 * y + r);
    assert(x == 2048 * a + z);
    assert(0 <= y < 16);
    assert(x == 128 * (16 * a + y) + r);
    assert(x / 128 == 16 * a + y);
    let b = (x / 128) % 2;
    assert(b == y % 2);
    let y2 = y - b + c;
    assert(0 <= y2 < 16);
    assert(x - b * 128 + c * 128 == 2048 * a + (128 * y2 + r));
    assert((x - b * 128 + c * 128) / 2048 == a);
}

/// Setting bit 7 of `w` changes that bit to `v % 2` and no other of the six flag bits.
proof fn lemma_set_bit_7(w: u32, v: int)
    ensures
        bit(set_bit32(w, 7, v) as int, 7) == v % 2,
        forall|k2: nat| flag_pos(k2) && k2 != 7 ==> bit(set_bit32(w, 7, v) as int, k2) == bit(w as int, k2),
{
    vstd::arithmetic::power2::lemma2_to64();
    let x = w as int;
    let c = v % 2;
    assert(p2(7) == 128);
    let cleared = x - bit(x, 7) * p2(7);
    let n = cleared + c * p2(7);
    assert(n == x - ((x / 128) % 2) * 128 + c * 128);
    assert(0 <= n < 0x1_0000_0000) by {
        assert(0 <= c < 2);
        assert(x == 128 * (x / 128) + x % 128);
    }
    assert(set_bit32(w, 7, v) as int == n);
    assert(bit(n, 7) == (n / 128) % 2);
    assert forall|k2: nat| flag_pos(k2) && k2 != 7 implies bit(set_bit32(w, 7, v) as int, k2) == bit(w as int, k2) by {
        assert(k2 == 0 || k2 == 2 || k2 == 4 || k2 == 6 || k2 == 7 || k2 == 11);
        if k2 == 0 { int_7_0(x, c); assert(p2(0) == 1); }
        if k2 == 2 { int_7_2(x, c); assert(p2(2) == 4); }
        if k2 == 4 { int_7_4(x, c); assert(p2(4) == 16); }
        if k2 == 6 { int_7_6(x, c); assert(p2(6) == 64); }
        if k2 == 11 { int_7_11(x, c); assert(p2(11) == 2048); }
    }
}

/// Clearing bit 11 and setting it to `c` does not change bit 0.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_11_0(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 2048) % 2) * 2048 + c * 2048) / 1) % 2 == (x / 1) % 2,
{
    let q = x / 2048;
    let r = x % 2048;
    let b = q % 2;
    assert(x == 2048 * q + r);
    let w = q - b + c;
    assert(x - b * 2048 + c * 2048 == 2048 * w + r);
    let rr = r / 1;
    let r2 = r % 1;
    assert(r == 1 * rr + r2);
    assert(x - b * 2048 + c * 2048 == 1 * (2048 * w + rr) + r2);
    assert(x == 1 * (2048 * q + rr) + r2);
    assert((x - b * 2048 + c * 2048) / 1 == 2048 * w + rr);
    assert(x / 1 == 2048 * q + rr);
    assert((2048 * w + rr) % 2 == rr % 2);
    assert((2048 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 11 and setting it to `c` does not change bit 2.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_11_2(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 2048) % 2) * 2048 + c * 2048) / 4) % 2 == (x / 4) % 2,
{
    let q = x / 2048;
    let r = x % 2048;
    let b = q % 2;
    assert(x == 2048 * q + r);
    let w = q - b + c;
    assert(x - b * 2048 + c * 2048 == 2048 * w + r);
    let rr = r / 4;
    let r2 = r % 4;
    assert(r == 4 * rr + r2);
    assert(x - b * 2048 + c * 2048 == 4 * (512 * w + rr) + r2);
    assert(x == 4 * (512 * q + rr) + r2);
    assert((x - b * 2048 + c * 2048) / 4 == 512 * w + rr);
    assert(x / 4 == 512 * q + rr);
    assert((512 * w + rr) % 2 == rr % 2);
    assert((512 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 11 and setting it to `c` does not change bit 4.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_11_4(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 2048) % 2) * 2048 + c * 2048) / 16) % 2 == (x / 16) % 2,
{
    let q = x / 2048;
    let r = x % 2048;
    let b = q % 2;
    assert(x == 2048 * q + r);
    let w = q - b + c;
    assert(x - b * 2048 + c * 2048 == 2048 * w + r);
    let rr = r / 16;
    let r2 = r % 16;
    assert(r == 16 * rr + r2);
    assert(x - b * 2048 + c * 2048 == 16 * (128 * w + rr) + r2);
    assert(x == 16 * (128 * q + rr) + r2);
    assert((x - b * 2048 + c * 2048) / 16 == 128 * w + rr);
    assert(x / 16 == 128 * q + rr);
    assert((128 * w + rr) % 2 == rr % 2);
    assert((128 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 11 and setting it to `c` does not change bit 6.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_11_6(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 2048) % 2) * 2048 + c * 2048) / 64) % 2 == (x / 64) % 2,
{
    let q = x / 2048;
    let r = x % 2048;
    let b = q % 2;
    assert(x == 2048 * q + r);
    let w = q - b + c;
    assert(x - b * 2048 + c * 2048 == 2048 * w + r);
    let rr = r / 64;
    let r2 = r % 64;
    assert(r == 64 * rr + r2);
    assert(x - b * 2048 + c * 2048 == 64 * (32 * w + rr) + r2);
    assert(x == 64 * (32 * q + rr) + r2);
    assert((x - b * 2048 + c * 2048) / 64 == 32 * w + rr);
    assert(x / 64 == 32 * q + rr);
    assert((32 * w + rr) % 2 == rr % 2);
    assert((32 * q + rr) % 2 == rr % 2);
}

/// Clearing bit 11 and setting it to `c` does not change bit 7.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
proof fn int_11_7(x: int, c: int)
    requires
        0 <= x < 0x1_0000_0000,
        c == 0 || c == 1,
    ensures
        ((x - ((x / 2048) % 2) * 2048 + c * 2048) / 128) % 2 == (x / 128) % 2,
{
    let q = x / 2048;
    let r = x % 2048;
    let b = q % 2;
    assert(x == 2048 * q + r);
    let w = q - b + c;
    assert(x - b * 2048 + c * 2048 == 2048 * w + r);
    let rr = r / 128;
    let r2 = r % 128;
    assert(r == 128 * rr + r2);
    assert(x - b * 2048 + c * 2048 == 128 * (16 * w + rr) + r2);
    assert(x == 128 * (16 * q + rr) + r2);
    assert((x - b * 2048 + c * 2048) / 128 == 16 * w + rr);
    assert(x / 128 == 16 * q + rr);
    assert((16 * w + rr) % 2 == rr % 2);
    assert((16 * q + rr) % 2 == rr % 2);
}

/// Setting bit 11 of `w` changes that bit to `v % 2` and no other of the six flag bits.
proof fn lemma_set_bit_11(w: u32, v: int)
    ensures
        bit(set_bit32(w, 11, v) as int, 11) == v % 2,
        forall|k2: nat| flag_pos(k2) && k2 != 11 ==> bit(set_bit32(w, 11, v) as int, k2) == bit(w as int, k2),
{
    vstd::arithmetic::power2::lemma2_to64();
    let x = w as int;
    let c = v % 2;
    assert(p2(11) == 2048);
    let cleared = x - bit(x, 11) * p2(11);
    let n = cleared + c * p2(11);
    assert(n == x - ((x / 2048) % 2) * 2048 + c * 2048);
    assert(0 <= n < 0x1_0000_0000) by {
        assert(0 <= c < 2);
        assert(x == 2048 * (x / 2048) + x % 2048);
    }
    assert(set_bit32(w, 11, v) as int == n);
    assert(bit(n, 11) == (n / 2048) % 2);
    assert forall|k2: nat| flag_pos(k2) && k2 != 11 implies bit(set_bit32(w, 11, v) as int, k2) == bit(w as int, k2) by {
        assert(k2 == 0 || k2 == 2 || k2 == 4 || k2 == 6 || k2 == 7 || k2 == 11);
        if k2 == 0 { int_11_0(x, c); assert(p2(0) == 1); }
        if k2 == 2 { int_11_2(x, c); assert(p2(2) == 4); }
        if k2 == 4 { int_11_4(x, c); assert(p2(4) == 16); }
        if k2 == 6 { int_11_6(x, c); assert(p2(6) == 64); }
        if k2 == 7 { int_11_7(x, c); assert(p2(7) == 128); }
    }
}

/// **Setting one flag bit leaves the others alone**, and reads back what was
/// set (mod 2).
pub proof fn lemma_bit_set32(w: u32, k: nat, v: int, k2: nat)
    requires
        flag_pos(k),
        flag_pos(k2),
    ensures
        bit(set_bit32(w, k, v) as int, k2) == if k == k2 {
            v % 2
        } else {
            bit(w as int, k2)
        },
{
    lemma_set_bit_0(w, v);
    lemma_set_bit_2(w, v);
    lemma_set_bit_4(w, v);
    lemma_set_bit_6(w, v);
    lemma_set_bit_7(w, v);
    lemma_set_bit_11(w, v);
}

} // verus!
