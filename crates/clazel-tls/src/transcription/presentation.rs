//! RFC 8446 §3, the presentation language, as far as the messages use it.
//!
//! Modelling choices:
//! - A decoder takes the bytes and returns the value with the bytes after it,
//!   or `None` where the syntax is not met. §3 only describes encodings, so
//!   every decoder here is the inverse its encoder implies, and every `None`
//!   is the "cannot be parsed according to the syntax" of §6.
//! - A vector is decoded to its body bytes ([`read_vector`]), then its body to
//!   elements by the caller. So a body that is not a multiple of the element
//!   size ("a 17-byte vector of uint16 would be illegal", §3.4) fails in
//!   the caller's element decoder.
//! - `select` (§3.8) is a Rust `enum` plus a function of the selector: see
//!   `key_exchange::select_handshake`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §3.3: a number of `width` bytes, big-endian ("network byte order").
pub open spec fn encode_uint(value: nat, width: nat) -> Seq<u8>
    decreases width,
{
    if width == 0 {
        seq![]
    } else {
        encode_uint(value / 256, (width - 1) as nat).push((value % 256) as u8)
    }
}

/// §3.3 uint8.
pub open spec fn uint8(value: nat) -> Seq<u8> {
    encode_uint(value, 1)
}

/// §3.3 uint16.
pub open spec fn uint16(value: nat) -> Seq<u8> {
    encode_uint(value, 2)
}

/// §3.3 uint24.
pub open spec fn uint24(value: nat) -> Seq<u8> {
    encode_uint(value, 3)
}

/// §3.3 uint32.
pub open spec fn uint32(value: nat) -> Seq<u8> {
    encode_uint(value, 4)
}

/// §3.3: the number held in the first `width` bytes of `bytes`.
pub open spec fn read_uint(bytes: Seq<u8>, width: nat) -> nat
    decreases width,
{
    if width == 0 {
        0
    } else {
        read_uint(bytes, (width - 1) as nat) * 256 + (bytes[width - 1] as nat)
    }
}

/// §3.4: the length field of a variable-length vector is "a number consuming
/// as many bytes as required to hold the vector's specified maximum (ceiling)
/// length".
pub open spec fn length_field_width(ceiling: nat) -> nat {
    if ceiling < 0x100 {
        1
    } else if ceiling < 0x1_0000 {
        2
    } else if ceiling < 0x100_0000 {
        3
    } else {
        4
    }
}

/// §3.4: encode `T T'<floor..ceiling>` whose elements are already the encoded
/// bytes `body`.
pub open spec fn write_vector(body: Seq<u8>, ceiling: nat) -> Seq<u8> {
    encode_uint(body.len(), length_field_width(ceiling)) + body
}

/// §3.4: decode `T T'<floor..ceiling>` at the start of `input`, returning its
/// body and the bytes after it. "the actual length precedes the vector's
/// contents" and lies in the "subrange of legal lengths, inclusively".
pub open spec fn read_vector(input: Seq<u8>, floor: nat, ceiling: nat) -> Option<(Seq<u8>, Seq<u8>)> {
    let width = length_field_width(ceiling);
    if input.len() < width {
        None
    } else {
        let actual = read_uint(input, width);
        if actual < floor || actual > ceiling || input.len() < width + actual {
            None
        } else {
            Some((input.subrange(width as int, (width + actual) as int),
                  input.subrange((width + actual) as int, input.len() as int)))
        }
    }
}

/// §3.4: `T T'[n]`, a fixed-length vector of `n` bytes at the start of `input`.
pub open spec fn read_fixed(input: Seq<u8>, n: nat) -> Option<(Seq<u8>, Seq<u8>)> {
    if input.len() < n {
        None
    } else {
        Some((input.subrange(0, n as int), input.subrange(n as int, input.len() as int)))
    }
}

/// §3.4: the body of a vector of uint16 as its elements. An odd number of
/// bytes is "illegal".
pub open spec fn read_uint16_list(body: Seq<u8>) -> Option<Seq<nat>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else if body.len() < 2 {
        None
    } else {
        match read_uint16_list(body.subrange(2, body.len() as int)) {
            None => None,
            Some(tail) => Some(seq![read_uint(body, 2)] + tail),
        }
    }
}

/// §3.4: the encoded bytes of the elements of a vector of uint16.
pub open spec fn write_uint16_list(values: Seq<nat>) -> Seq<u8>
    decreases values.len(),
{
    if values.len() == 0 {
        seq![]
    } else {
        uint16(values[0]) + write_uint16_list(values.subrange(1, values.len() as int))
    }
}

/// Whether `value` is in `values`. A recursive search and not `Seq::contains`,
/// so that it evaluates under `by (compute)`.
pub open spec fn list_has<A>(values: Seq<A>, value: A) -> bool
    decreases values.len(),
{
    if values.len() == 0 {
        false
    } else {
        values[0] == value || list_has(values.subrange(1, values.len() as int), value)
    }
}

/// `M1 || M2 || ... || Mn`, the concatenation written `||` throughout the RFC.
pub open spec fn concatenate(parts: Seq<Seq<u8>>) -> Seq<u8>
    decreases parts.len(),
{
    if parts.len() == 0 {
        seq![]
    } else {
        parts[0] + concatenate(parts.subrange(1, parts.len() as int))
    }
}

/// `count` bytes of value `byte`.
pub open spec fn repeat_byte(byte: u8, count: nat) -> Seq<u8>
    decreases count,
{
    if count == 0 {
        seq![]
    } else {
        repeat_byte(byte, (count - 1) as nat).push(byte)
    }
}

/// Whether every byte is zero.
pub open spec fn all_zero(bytes: Seq<u8>) -> bool
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        true
    } else {
        bytes[0] == 0 && all_zero(bytes.subrange(1, bytes.len() as int))
    }
}

} // verus!
