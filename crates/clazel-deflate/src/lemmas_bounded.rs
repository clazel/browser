//! `theorem_output_bounded`: the output limit holds for every input, proven
//! about [`super::spec`] by induction over the blocks and symbols.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The output limit: `theorem_output_bounded`.
// ---------------------------------------------------------------------------

/// A match adds exactly `length` bytes.
pub proof fn lemma_lz_copy_len(out: Seq<u8>, distance: nat, length: nat)
    ensures
        lz_copy(out, distance, length).len() == out.len() + length,
    decreases length,
{
    if length > 0 {
        lemma_lz_copy_len(out.push(out[out.len() - distance]), distance, (length - 1) as nat);
    }
}

/// The compressed-data loop never returns more output than the limit, given
/// that it started within it.
pub proof fn lemma_data_loop_bounded(
    input: Seq<u8>,
    pos: nat,
    out: Seq<u8>,
    limit: nat,
    lit: Seq<nat>,
    dist: Seq<nat>,
    fuel: nat,
)
    requires
        out.len() <= limit,
    ensures
        match data_loop(input, pos, out, limit, lit, dist, fuel) {
            Ok((p, o)) => o.len() <= limit,
            Err(_) => true,
        },
    decreases fuel,
{
    if fuel > 0 {
        match decode_symbol(lit, input, pos, 0, 0) {
            Sym::Found(sym, p1) => {
                if sym < 256 {
                    if out.len() + 1 <= limit {
                        lemma_data_loop_bounded(
                            input, p1, out.push(sym as u8), limit, lit, dist, (fuel - 1) as nat,
                        );
                    }
                } else if sym > 256 && sym <= 285 {
                    match read_bits(input, p1, len_extra(sym)) {
                        Some((e, p2)) => {
                            let length = len_base(sym) + e;
                            match decode_symbol(dist, input, p2, 0, 0) {
                                Sym::Found(d, p3) => {
                                    if d <= 29 {
                                        match read_bits(input, p3, dist_extra(d)) {
                                            Some((e2, p4)) => {
                                                let distance = dist_base(d) + e2;
                                                if distance <= out.len() && out.len() + length <= limit {
                                                    lemma_lz_copy_len(out, distance, length);
                                                    lemma_data_loop_bounded(
                                                        input, p4, lz_copy(out, distance, length), limit,
                                                        lit, dist, (fuel - 1) as nat,
                                                    );
                                                }
                                            },
                                            None => {},
                                        }
                                    }
                                },
                                _ => {},
                            }
                        },
                        None => {},
                    }
                }
            },
            _ => {},
        }
    }
}

/// The blocks loop never returns more output than the limit, given that it
/// started within it.
pub proof fn lemma_inflate_blocks_bounded(input: Seq<u8>, pos: nat, out: Seq<u8>, limit: nat, fuel: nat)
    requires
        out.len() <= limit,
    ensures
        match inflate_blocks(input, pos, out, limit, fuel) {
            Ok((p, o)) => o.len() <= limit,
            Err(_) => true,
        },
    decreases fuel,
{
    if fuel > 0 {
        match read_bits(input, pos, 3) {
            Some((header, p)) => {
                let btype = header / 2;
                if btype == 0 {
                    match stored_block(input, p, out, limit) {
                        Ok((p2, out2)) => {
                            if header % 2 == 0 {
                                lemma_inflate_blocks_bounded(input, p2, out2, limit, (fuel - 1) as nat);
                            }
                        },
                        Err(_) => {},
                    }
                } else if btype == 1 {
                    lemma_data_loop_bounded(
                        input, p, out, limit, fixed_lit_lengths(), fixed_dist_lengths(), bit_len(input),
                    );
                    match data_loop(input, p, out, limit, fixed_lit_lengths(), fixed_dist_lengths(), bit_len(input)) {
                        Ok((p2, out2)) => {
                            if header % 2 == 0 {
                                lemma_inflate_blocks_bounded(input, p2, out2, limit, (fuel - 1) as nat);
                            }
                        },
                        Err(_) => {},
                    }
                } else if btype == 2 {
                    match read_dynamic_tables(input, p) {
                        Ok((lit, dist, p2)) => {
                            lemma_data_loop_bounded(input, p2, out, limit, lit, dist, bit_len(input));
                            match data_loop(input, p2, out, limit, lit, dist, bit_len(input)) {
                                Ok((p3, out3)) => {
                                    if header % 2 == 0 {
                                        lemma_inflate_blocks_bounded(input, p3, out3, limit, (fuel - 1) as nat);
                                    }
                                },
                                Err(_) => {},
                            }
                        },
                        Err(_) => {},
                    }
                }
            },
            None => {},
        }
    }
}

/// `theorem_output_bounded`: a successful decode, raw or zlib, never
/// produced more than `limit` bytes, so a decompression bomb stops at the
/// limit (the exec decoder is tested against this, see the README).
pub proof fn theorem_output_bounded(input: Seq<u8>, limit: nat)
    ensures
        match inflate(input, limit) {
            Ok((o, _)) => o.len() <= limit,
            Err(_) => true,
        },
        match zlib_decompress(input, limit) {
            Ok((o, _)) => o.len() <= limit,
            Err(_) => true,
        },
{
    lemma_inflate_blocks_bounded(input, 0, Seq::empty(), limit, bit_len(input));
    if input.len() >= 2 {
        let rest = input.subrange(2, input.len() as int);
        lemma_inflate_blocks_bounded(rest, 0, Seq::empty(), limit, bit_len(rest));
    }
}

} // verus!
