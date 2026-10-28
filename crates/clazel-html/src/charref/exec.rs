//! The executable character reference functions, proven to meet
//! [`super::contract`]. The step comments live in [`super::spec`].
//!
//! [`longest_match`] scans the table's rows in order, as
//! [`super::spec::longest_match_upto`] does, comparing each name with the
//! input; a name whose first character differs is rejected after one
//! comparison.

use super::data::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Element `i` of `v`.
pub fn at32(v: &[u32], i: usize) -> (out: u32)
    requires
        i < v.len(),
    ensures
        out == v@[i as int],
{
    match v.get(i) {
        Some(e) => *e,
        // Unreachable: i < v.len().
        None => 0,
    }
}

/// Whether row `i`'s name is what `input` holds from `pos` on.
fn name_matches_at(input: &[u32], pos: usize, i: usize) -> (r: bool)
    requires
        pos <= input.len(),
        i < entity_count(),
    ensures
        r == is_prefix_at(entity_name(i as int), input@, pos as int),
{
    proof {
        super::lemmas::lemma_rows_in_bounds();
    }
    let start = entity_name_start_at_exec(i) as usize;
    let len = entity_name_len_at_exec(i) as usize;
    let ghost name = entity_name(i as int);
    // Never saturates: pos <= input.len().
    if len > input.len().saturating_sub(pos) {
        return false;
    }
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len == name.len(),
            pos + len <= input.len(),
            start + len <= ENTITY_CHARS_LEN,
            name == entity_name(i as int),
            start == entity_name_start_at(i as int),
            forall|j: int| 0 <= j < k ==> input@[pos + j] == #[trigger] name[j],
        decreases len - k,
    {
        // Never saturate: start + len and pos + len are within lengths.
        let c = entity_chars_at_exec(start.saturating_add(k)) as u32;
        if at32(input, pos.saturating_add(k)) != c {
            assert(input@.subrange(pos as int, pos + len)[k as int] != name[k as int]);
            return false;
        }
        // Never saturates: k < len.
        k = k.saturating_add(1);
    }
    assert(input@.subrange(pos as int, pos + len) =~= name);
    true
}

/// HTML §13.2.5.78: the row of the named character references table that
/// the named character reference state consumes from `pos` on, or `None`.
pub fn longest_match_exec(input: &[u32], pos: usize) -> (output: Option<usize>)
    requires
        super::contract::longest_match_requires(input@, pos as int),
    ensures
        super::contract::longest_match_ensures(input@, pos as int, output),
{
    let mut best: Option<usize> = None;
    let mut best_len: usize = 0;
    let mut k: usize = 0;
    while k < ENTITY_NAME_START_LEN
        invariant
            k <= ENTITY_NAME_START_LEN,
            pos <= input.len(),
            match best {
                None => longest_match_upto(input@, pos as int, k as nat) is None,
                Some(b) => longest_match_upto(input@, pos as int, k as nat) == Some(b as nat) && b < k
                    && best_len == entity_name(b as int).len(),
            },
        decreases ENTITY_NAME_START_LEN - k,
    {
        let len = entity_name_len_at_exec(k) as usize;
        let longer = match best {
            None => true,
            Some(_) => best_len < len,
        };
        if longer && name_matches_at(input, pos, k) {
            best = Some(k);
            best_len = len;
        }
        // Never saturates: k < ENTITY_NAME_START_LEN.
        k = k.saturating_add(1);
    }
    best
}

/// The length of row `i`'s name.
pub fn entity_name_len_exec(i: usize) -> (n: usize)
    ensures
        n == entity_name(i as int).len(),
{
    entity_name_len_at_exec(i) as usize
}

/// The last character of row `i`'s name.
pub fn entity_name_last_exec(i: usize) -> (c: u32)
    requires
        i < entity_count(),
    ensures
        entity_name(i as int).len() > 0,
        c == entity_name(i as int).last(),
{
    proof {
        super::lemmas::lemma_rows_in_bounds();
    }
    let start = entity_name_start_at_exec(i) as usize;
    let len = entity_name_len_at_exec(i) as usize;
    // Never saturate: 1 <= len and start + len is in the table.
    entity_chars_at_exec(start.saturating_add(len).saturating_sub(1)) as u32
}

/// Row `i`'s code points.
pub fn entity_code_points_exec(i: usize) -> (out: Vec<u32>)
    ensures
        super::contract::entity_code_points_ensures(i as int, out@),
{
    let cp1 = entity_cp1_at_exec(i);
    let cp2 = entity_cp2_at_exec(i);
    let mut out = Vec::new();
    out.push(cp1);
    if cp2 != 0 {
        out.push(cp2);
    }
    assert(out@ =~= entity_code_points(i as int));
    out
}

/// §13.2.5.84's table, for an exec number.
fn c1_replacement_exec(n: u32) -> (r: Option<u32>)
    ensures
        r == c1_replacement(n as nat),
{
    match n {
        0x80 => Some(0x20AC),
        0x82 => Some(0x201A),
        0x83 => Some(0x0192),
        0x84 => Some(0x201E),
        0x85 => Some(0x2026),
        0x86 => Some(0x2020),
        0x87 => Some(0x2021),
        0x88 => Some(0x02C6),
        0x89 => Some(0x2030),
        0x8A => Some(0x0160),
        0x8B => Some(0x2039),
        0x8C => Some(0x0152),
        0x8E => Some(0x017D),
        0x91 => Some(0x2018),
        0x92 => Some(0x2019),
        0x93 => Some(0x201C),
        0x94 => Some(0x201D),
        0x95 => Some(0x2022),
        0x96 => Some(0x2013),
        0x97 => Some(0x2014),
        0x98 => Some(0x02DC),
        0x99 => Some(0x2122),
        0x9A => Some(0x0161),
        0x9B => Some(0x203A),
        0x9C => Some(0x0153),
        0x9E => Some(0x017E),
        0x9F => Some(0x0178),
        _ => None,
    }
}

/// HTML §13.2.5.84: the code point the numeric character reference end
/// state appends, from the capped character reference code.
pub fn numeric_reference_end_code_exec(capped: u32) -> (r: u32)
    requires
        capped <= 0x110000,
    ensures
        super::contract::numeric_reference_end_code_ensures(capped as nat, r),
{
    let code = if capped == 0 { 0xFFFDu32 } else { capped };
    let code = if code > 0x10FFFF { 0xFFFDu32 } else { code };
    let code = match code {
        0xD800..=0xDFFF => 0xFFFDu32,
        _ => code,
    };
    let is_control = matches!(code, 0..=0x1F | 0x7F..=0x9F);
    let is_ws = code == 0x09 || code == 0x0A || code == 0x0C || code == 0x0D || code == 0x20;
    if code == 0x0D || (is_control && !is_ws) {
        match c1_replacement_exec(code) {
            Some(r) => r,
            None => code,
        }
    } else {
        code
    }
}

/// "Multiply the character reference code by `base`. Add" `digit`, on
/// the capped code.
pub fn digit_step(capped: u32, base: u32, digit: u32) -> (r: u32)
    requires
        capped <= 0x110000,
        1 <= base <= 16,
        digit < 16,
    ensures
        r <= 0x110000,
        super::contract::digit_step_ensures(capped as nat, base as nat, digit as nat, r as nat),
{
    if capped >= 0x110000 {
        assert forall|code: nat| #[trigger] super::contract::capped_code(code) == capped as nat implies 0x110000 == super::contract::capped_code(
            code * base as nat + digit as nat,
        ) by {
            assert(code >= 0x110000);
            assert(code * base as nat >= code) by (nonlinear_arith)
                requires
                    base >= 1,
            ;
        }
        0x110000
    } else {
        assert(capped as int * base as int <= 0x110000 * 16) by (nonlinear_arith)
            requires
                capped < 0x110000,
                base <= 16,
        ;
        // Never saturates: capped < 0x110000 and base <= 16.
        let v = capped.saturating_mul(base).saturating_add(digit);
        let r = if v > 0x110000 { 0x110000 } else { v };
        assert forall|code: nat| #[trigger] super::contract::capped_code(code) == capped as nat implies r as nat == super::contract::capped_code(
            code * base as nat + digit as nat,
        ) by {
            assert(code == capped as nat);
        }
        r
    }
}

} // verus!
