//! The executable x-user-defined decoder, proven to meet
//! [`super::contract`] (through [`super::independent`]'s equation).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Process a queue" with x-user-defined's decoder over all of `input`.
pub fn decode(input: &[u8]) -> (out: Vec<u32>)
    ensures
        super::contract::decode_ensures(input@, out@),
{
    proof {
        super::independent::lemma_equals_decode(input@);
    }
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            out@ == super::independent::decode_map(input@).subrange(0, i as int),
        decreases input.len() - i,
    {
        // `get` cannot fail: i < input.len().
        let b = match input.get(i) {
            Some(b) => *b,
            None => 0,
        };
        let c = if b < 0x80 {
            b as u32
        } else {
            // 0xF780 + b − 0x80 = 0xF700 + b, and b < 0x100, so the OR adds.
            proof {
                let x = b as u32;
                assert(x < 0x100 ==> 0xF700u32 | x == 0xF700 + x) by (bit_vector);
            }
            0xF700u32 | (b as u32)
        };
        out.push(c);
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
        proof {
            assert(out@ =~= super::independent::decode_map(input@).subrange(0, i as int));
        }
    }
    proof {
        assert(super::independent::decode_map(input@).subrange(0, i as int) =~= super::independent::decode_map(
            input@,
        ));
    }
    out
}

} // verus!
