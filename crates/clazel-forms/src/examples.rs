//! Worked examples of the spec's string algorithms, evaluated by Verus.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies, even with
//! `--verify-function`. A mutant that breaks an example would otherwise fail
//! every kill certificate placed next to it, not only the one about the
//! example (see `crates/clazel-percent/src/examples.rs`).

#[cfg(verus_only)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Infra "normalize newlines", "strip newlines" and "strip leading and
/// trailing ASCII whitespace", HTML's "rules for parsing non-negative
/// integers" and `cols`' character width, the textarea wrapping
/// transformation's line breaking, and the decimal serialization of an
/// image button's coordinates, on small inputs worked out by hand from the
/// steps of the algorithms.
pub proof fn lemma_examples()
    ensures
        // ASCII case-insensitive matching lowercases only A to Z.
        ascii_lower(seq![0x5Au32, 0x41, 0x40, 0x5B]) == seq![0x7Au32, 0x61, 0x40, 0x5B],
        ci_eq(seq![0x48u32, 0x41, 0x72, 0x44], seq![0x68u8, 0x61, 0x72, 0x64]),
        // "a CR LF b CR c" normalizes to "a LF b LF c".
        normalize_newlines(seq![0x61u32, 0x0D, 0x0A, 0x62, 0x0D, 0x63]) == seq![0x61u32, 0x0A, 0x62, 0x0A, 0x63],
        // A lone CR at the end is one LF.
        normalize_newlines(seq![0x0Du32]) == seq![0x0Au32],
        // Strip newlines removes both CR and LF.
        strip_newlines(seq![0x61u32, 0x0D, 0x0A, 0x62]) == seq![0x61u32, 0x62],
        // Form feed is ASCII whitespace; so are TAB and SPACE, but not NBSP.
        strip_whitespace(seq![0x0Cu32, 0x61, 0x0C]) == seq![0x61u32],
        strip_whitespace(seq![0x09u32, 0x20, 0x62, 0xA0, 0x20]) == seq![0x62u32, 0xA0],
        // "-0" is zero, "-1" an error, "+7x" is 7, " 20" is 20, "" an error.
        parse_non_negative(seq![0x2Du32, 0x30]) == Some(0nat),
        parse_non_negative(seq![0x2Du32, 0x31]) is None,
        parse_non_negative(seq![0x2Bu32, 0x37, 0x78]) == Some(7nat),
        parse_non_negative(seq![0x20u32, 0x32, 0x30]) == Some(20nat),
        parse_non_negative(Seq::<u32>::empty()) is None,
        // `cols="0"` and an unparsable `cols` give the default width 20; `cols=7` gives 7.
        width_of(Some(seq![0x30u32])) == 20nat,
        width_of(Some(seq![0x78u32])) == 20nat,
        width_of(Some(seq![0x37u32])) == 7nat,
        width_of(None) == 20nat,
        // Hard wrapping at 2 breaks "abcde" into "ab", "cd", "e".
        wrap_from(seq![0x61u32, 0x62, 0x63, 0x64, 0x65], 2, 0) == seq![0x61u32, 0x62, 0x0A, 0x63, 0x64, 0x0A, 0x65],
        // A line that fits is left alone, and an LF starts a new line.
        wrap_from(seq![0x61u32, 0x62, 0x0A, 0x63, 0x64], 2, 0) == seq![0x61u32, 0x62, 0x0A, 0x63, 0x64],
        // Decimal: 0, 9, 10 and 345.
        decimal(0) == seq![0x30u32],
        decimal(9) == seq![0x39u32],
        decimal(10) == seq![0x31u32, 0x30],
        decimal(345) == seq![0x33u32, 0x34, 0x35],
        // The value sanitization algorithms: Text strips newlines; Email also strips whitespace around.
        sanitize(InputType::Text, seq![0x20u32, 0x61, 0x0A, 0x20]) == seq![0x20u32, 0x61, 0x20],
        sanitize(InputType::Email, seq![0x20u32, 0x61, 0x0A, 0x20]) == seq![0x61u32],
        sanitize(InputType::Other, seq![0x20u32, 0x0A]) == seq![0x20u32, 0x0A],
{
    assert(ascii_lower(seq![0x5Au32, 0x41, 0x40, 0x5B]) =~= seq![0x7Au32, 0x61, 0x40, 0x5B]) by (compute_only);
    assert(ci_eq(seq![0x48u32, 0x41, 0x72, 0x44], seq![0x68u8, 0x61, 0x72, 0x64])) by (compute_only);
    assert(normalize_newlines(seq![0x61u32, 0x0D, 0x0A, 0x62, 0x0D, 0x63]) =~= seq![0x61u32, 0x0A, 0x62, 0x0A, 0x63])
        by (compute_only);
    assert(normalize_newlines(seq![0x0Du32]) =~= seq![0x0Au32]) by (compute_only);
    assert(strip_newlines(seq![0x61u32, 0x0D, 0x0A, 0x62]) =~= seq![0x61u32, 0x62]) by (compute_only);
    assert(strip_whitespace(seq![0x0Cu32, 0x61, 0x0C]) =~= seq![0x61u32]) by (compute_only);
    assert(strip_whitespace(seq![0x09u32, 0x20, 0x62, 0xA0, 0x20]) =~= seq![0x62u32, 0xA0]) by (compute_only);
    assert(parse_non_negative(seq![0x2Du32, 0x30]) == Some(0nat)) by (compute_only);
    assert(parse_non_negative(seq![0x2Du32, 0x31]) is None) by (compute_only);
    assert(parse_non_negative(seq![0x2Bu32, 0x37, 0x78]) == Some(7nat)) by (compute_only);
    assert(parse_non_negative(seq![0x20u32, 0x32, 0x30]) == Some(20nat)) by (compute_only);
    assert(parse_non_negative(Seq::<u32>::empty()) is None) by (compute_only);
    assert(width_of(Some(seq![0x30u32])) == 20nat) by (compute_only);
    assert(width_of(Some(seq![0x78u32])) == 20nat) by (compute_only);
    assert(width_of(Some(seq![0x37u32])) == 7nat) by (compute_only);
    assert(width_of(None) == 20nat) by (compute_only);
    assert(wrap_from(seq![0x61u32, 0x62, 0x63, 0x64, 0x65], 2, 0) =~= seq![0x61u32, 0x62, 0x0A, 0x63, 0x64, 0x0A, 0x65])
        by (compute_only);
    assert(wrap_from(seq![0x61u32, 0x62, 0x0A, 0x63, 0x64], 2, 0) =~= seq![0x61u32, 0x62, 0x0A, 0x63, 0x64])
        by (compute_only);
    assert(decimal(0) =~= seq![0x30u32]) by (compute_only);
    assert(decimal(9) =~= seq![0x39u32]) by (compute_only);
    assert(decimal(10) =~= seq![0x31u32, 0x30]) by (compute_only);
    assert(decimal(345) =~= seq![0x33u32, 0x34, 0x35]) by (compute_only);
    assert(sanitize(InputType::Text, seq![0x20u32, 0x61, 0x0A, 0x20]) =~= seq![0x20u32, 0x61, 0x20]) by (compute_only);
    assert(sanitize(InputType::Email, seq![0x20u32, 0x61, 0x0A, 0x20]) =~= seq![0x61u32]) by (compute_only);
    assert(sanitize(InputType::Other, seq![0x20u32, 0x0A]) =~= seq![0x20u32, 0x0A]) by (compute_only);
}

} // verus!
