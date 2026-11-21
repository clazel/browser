//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Each harness runs one step of the parser on **every** input within the
//! bound in its name: a symbolic array of code units, a symbolic length, and
//! a symbolic start position, in the mode in its name. Kani checks that no
//! panic, arithmetic overflow or read outside a slice is reachable, and its
//! unwinding assertions check that every loop and recursion finishes within
//! the stated bound. The bounds are also in the crate's README.
//!
//! The harnesses are cut along the grammar's structure, because the whole parser
//! is beyond CBMC (see "Not done"):
//!
//! - **The cursor** ([`Parser::peek_with`], [`Parser::bump_cp`], [`Parser::adv`],
//!   [`Parser::unit`]): any position of any pattern of up to 4 units, in each mode.
//! - **Numbers** ([`Parser::digits_at`], [`Parser::scan_braces`],
//!   [`Parser::digits_greater`], [`Parser::quantifier`]): up to 6 units.
//! - **Escapes** ([`Parser::character_escape`], [`Parser::unicode_escape_body`],
//!   [`Parser::legacy_octal`], [`Parser::decimal_escape`],
//!   [`Parser::property_escape`]), each in the modes it reads differently, up to
//!   3 to 8 units (in each harness's name).
//! - **Modifiers and group names** ([`Parser::modifiers`], [`Parser::group_name`]).
//! - **Flags** ([`Flags::parse`]): any string of up to 9 units.
//!
//! Each step is checked for what its callers rely on: the position stays inside
//! the pattern, and a step that returns `Ok` consumed something (the loops that
//! call it terminate because of that), and an error's position is inside the
//! pattern.
//!
//! Every tree a harness gets back is passed to `core::mem::forget`: the drop glue
//! of the syntax tree is recursive, and CBMC unrolls it (a harness that dropped
//! an `Atom` ran over six CPU-minutes; with `forget`, six seconds).
//!
//! **Not done** (the README says the same):
//!
//! - **The whole parse ([`super::parse`]) and the steps that build a `Vec` of
//!   tree nodes in a loop** ([`Parser::class_ranges`], [`Parser::class_set_expr`],
//!   [`Parser::alternative`], [`Parser::disjunction`], [`Parser::term`],
//!   [`Parser::group`], [`Parser::class`]). Run on a symbolic pattern of
//!   one to three units, with the `Vec`'s growth and the drop glue of the error
//!   paths in the formula, none finished in 5 to 14 CPU-minutes (`class_ranges`
//!   at one, two and three units; the whole parse at one unit, without `u` and
//!   `v`; at two units, over 8 minutes). The steps they call are the harnesses
//!   above, so what is checked of them is each leaf, not their composition: the
//!   loops' termination (each iteration consumes a code unit, or fails) and the
//!   recursion's (bounded by [`super::MAX_DEPTH`]) are argued in the source's
//!   comments, and tested (`tests/parser.rs`: every pattern of up to three
//!   units over 33 units of the grammar, all three modes; deep and wide
//!   patterns), not proven.
//! - **The `ID_Start` and `ID_Continue` tables**: [`Parser::group_name`] is
//!   checked on code units below U+0080 only (a bisection over the lexer's
//!   table costs CBMC minutes, and `clazel-js-lexer` has Verus prove it
//!   total). With four units no escape reaches U+0080.
//! - **`names_in_disjunction`** (the duplicate-name check) is not run by any
//!   harness: it recurses over a tree of at most [`super::MAX_DEPTH`] levels
//!   and no harness builds a tree.

use super::{Flags, Parser};
use crate::props::SyntaxOnly;

/// A parser at any position of any pattern of at most `N` units, in the mode
/// (0: neither flag, 1: `u`, 2: `v`).
fn with_parser<const N: usize>(mode: u8, named: bool, f: impl FnOnce(Parser<'_>, usize)) {
    let data: [u16; N] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= N);
    let src = data.get(..len).unwrap_or_default();
    let pos: usize = kani::any();
    kani::assume(pos <= len);
    let p = Parser {
        src,
        pos,
        unicode: mode != 0,
        sets: mode == 2,
        named,
        total: if kani::any() { Some(kani::any()) } else { None },
        names: &SyntaxOnly,
        depth: 0,
        groups: 0,
        group_names: Vec::new(),
        backrefs: Vec::new(),
        named_refs: Vec::new(),
    };
    f(p, len);
}

/// [`Parser::peek_with`], [`Parser::bump_cp`], [`Parser::adv`] and
/// [`Parser::unit`] at any position of any pattern of up to 4 units.
#[kani::proof]
#[kani::unwind(6)]
fn cursor_any_4() {
    with_parser::<4>(kani::any::<u8>() % 3, false, |mut p, len| {
        let start = p.pos;
        if let Some((_, w)) = p.peek_with(kani::any()) {
            assert!(w == 1 || w == 2);
            assert!(start.saturating_add(w) <= len);
        } else {
            assert!(start == len);
        }
        let _ = p.unit(kani::any());
        let before = p.pos;
        if p.bump_cp().is_some() {
            assert!(p.pos > before && p.pos <= len);
        }
        p.adv(kani::any());
        assert!(p.pos <= len);
    });
}

/// [`Parser::digits_at`], [`Parser::scan_braces`] and
/// [`Parser::digits_greater`] at any position of any pattern of up to 6 units.
#[kani::proof]
#[kani::unwind(8)]
fn braces_any_6() {
    with_parser::<6>(0, false, |p, len| {
        let d = p.digits_at(p.pos);
        assert!(d.start == p.pos && d.start <= d.end && d.end <= len);
        if let Some((lo, hi)) = p.scan_braces() {
            assert!(lo.start <= lo.end && lo.end <= len);
            if let Some(hi) = hi {
                assert!(hi.start <= hi.end && hi.end <= len);
                let _ = p.digits_greater(&lo, &hi);
                let _ = p.digits_greater(&hi, &lo);
            }
        }
    });
}

/// [`Parser::quantifier`] at any position of any pattern of up to 6 units.
#[kani::proof]
#[kani::unwind(8)]
fn quantifier_any_6() {
    with_parser::<6>(0, false, |mut p, len| {
        let before = p.pos;
        match p.quantifier() {
            Ok(Some(q)) => {
                assert!(p.pos > before && p.pos <= len);
                assert!(q.max.is_none_or(|m| m >= q.min || q.min == u64::MAX));
            }
            Ok(None) => assert!(p.pos == before),
            Err(e) => assert!(e.at <= len),
        }
    });
}

/// [`Parser::character_escape`] (the code after a `\`) at any position of any
/// pattern of up to 4 units, in each mode.
#[kani::proof]
#[kani::unwind(6)]
fn character_escape_any_4() {
    with_parser::<4>(kani::any::<u8>() % 3, kani::any(), |mut p, len| {
        let before = p.pos;
        match p.character_escape() {
            Ok(c) => {
                assert!(p.pos > before && p.pos <= len);
                assert!(c <= 0x10_FFFF);
            }
            Err(e) => assert!(e.at <= len),
        }
    });
}

/// [`Parser::unicode_escape_body`], both forms, at any position of any
/// pattern of up to 8 units.
#[kani::proof]
#[kani::unwind(10)]
fn unicode_escape_any_8() {
    with_parser::<8>(1, false, |mut p, len| {
        match p.unicode_escape_body(kani::any()) {
            Ok(c) => assert!(p.pos <= len && c <= 0x10_FFFF),
            Err(e) => assert!(e.at <= len),
        }
    });
}

/// [`Parser::legacy_octal`] at any octal digit of any pattern of up to 4
/// units.
#[kani::proof]
#[kani::unwind(6)]
fn legacy_octal_any_4() {
    with_parser::<4>(0, false, |mut p, len| {
        kani::assume(p.unit(0).is_some_and(|u| (0x30..=0x37).contains(&u)));
        let before = p.pos;
        let v = p.legacy_octal();
        assert!(p.pos > before && p.pos <= len && v <= 0o377);
    });
}

/// [`Parser::decimal_escape`] at any digit 1 to 9 of any pattern of up to 3
/// units, without `u` or `v` (the mode that reads the group count).
#[kani::proof]
#[kani::unwind(5)]
fn decimal_escape_any_3() {
    with_parser::<3>(0, false, |mut p, len| {
        kani::assume(p.unit(0).is_some_and(|u| (0x31..=0x39).contains(&u)));
        let before = p.pos;
        match p.decimal_escape() {
            Ok(atom) => {
                // The drop glue of a tree is recursive; CBMC need not unroll it.
                core::mem::forget(atom);
                assert!(p.pos > before && p.pos <= len);
            }
            Err(e) => assert!(e.at <= len),
        }
    });
}

/// [`Parser::property_escape`] at any position of any pattern of up to 4
/// units (`p{x}`: a one-character name, the lookups of `props` compared with
/// every name they hold), with `u` or `v`.
#[kani::proof]
#[kani::unwind(6)]
fn property_escape_any_4() {
    with_parser::<4>(1 + kani::any::<u8>() % 2, false, |mut p, len| {
        let before = p.pos;
        match p.property_escape(kani::any()) {
            Ok(_) => assert!(p.pos > before && p.pos <= len),
            Err(e) => assert!(e.at <= len),
        }
    });
}

/// [`Parser::modifiers`] at any position of any pattern of up to 6 units.
#[kani::proof]
#[kani::unwind(8)]
fn modifiers_any_6() {
    with_parser::<6>(0, false, |mut p, len| match p.modifiers() {
        Ok(_) => assert!(p.pos <= len),
        Err(e) => assert!(e.at <= len),
    });
}

/// [`Parser::group_name`] at any position of any pattern of up to 4 units,
/// in each mode, all below U+0080: the tables of `ID_Start` and `ID_Continue`
/// above U+007F are `clazel-js-lexer`'s (Verus proves its lookup total), and a
/// table bisection costs CBMC minutes. With 4 units no escape reaches U+0080
/// either (`\u00e9` is six).
#[kani::proof]
#[kani::unwind(7)]
fn group_name_any_4() {
    with_parser::<4>(kani::any::<u8>() % 3, true, |mut p, len| {
        kani::assume(p.src.iter().all(|&u| u < 0x80));
        let before = p.pos;
        match p.group_name() {
            Ok(n) => assert!(p.pos > before && p.pos <= len && !n.is_empty()),
            Err(e) => assert!(e.at <= len),
        }
    });
}

/// [`Flags::parse`] on any flag string of at most 9 units.
#[kani::proof]
#[kani::unwind(11)]
fn flags_any_9() {
    let data: [u16; 9] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 9);
    let _ = Flags::parse(data.get(..len).unwrap_or_default());
}
