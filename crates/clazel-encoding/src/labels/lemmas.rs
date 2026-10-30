//! Facts proven about "get an encoding" and the labels table. They are
//! evidence that the transcription is right, not part of what the
//! implementation must meet:
//!
//! - [`lemma_labels_distinct`]: no label is listed twice (case-insensitively),
//!   so "the corresponding encoding" of a label is well defined;
//! - [`lemma_every_label`]: every label maps to exactly one encoding, the
//!   one it is listed under;
//! - [`lemma_name_maps_to_itself`]: "get an encoding" of an encoding's own
//!   name is that encoding (§4.2 notes "ASCII-lowercasing its name yields
//!   one of its labels").
//!
//! The facts about the generated table are proven by evaluating it
//! ([`lemma_table`]), over the tables as sequences, which Verus's
//! evaluator reads quickly; the rest is symbolic.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The number of label rows.
pub open spec fn rows() -> nat {
    228
}

/// A byte a label may have: lowercase ASCII letters, digits, `-_.:`.
pub open spec fn label_byte(b: u8) -> bool {
    (0x61 <= b <= 0x7A) || (0x30 <= b <= 0x39) || b == 0x2D || b == 0x5F || b == 0x2E || b == 0x3A
}

/// A byte a name may have: ASCII letters, digits, `-_`.
pub open spec fn name_byte(b: u8) -> bool {
    (0x41 <= b <= 0x5A) || (0x61 <= b <= 0x7A) || (0x30 <= b <= 0x39) || b == 0x2D || b == 0x5F
}

/// Bytes `cs[start + k]` for `k` from `k` to `len` are label bytes.
pub open spec fn bytes_ok(cs: Seq<u8>, start: int, k: nat, len: nat, name: bool) -> bool
    decreases len - k,
{
    if k >= len {
        true
    } else {
        0 <= start + k < cs.len() && (if name {
            name_byte(cs[start + k])
        } else {
            label_byte(cs[start + k])
        }) && bytes_ok(cs, start, k + 1, len, name)
    }
}

/// Rows `i` to the end are non-empty, in range, and label bytes.
pub open spec fn rows_ok(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, en: Seq<u8>, i: nat) -> bool
    decreases rows() - i,
{
    if i >= rows() {
        true
    } else {
        ln[i as int] > 0 && en[i as int] < 40 && bytes_ok(cs, st[i as int] as int, 0, ln[i as int] as nat, false)
            && rows_ok(cs, st, ln, en, i + 1)
    }
}

/// `cs[a + k ..]` and `cs[b + k ..]` agree for `len - k` bytes.
pub open spec fn same_from(cs: Seq<u8>, a: int, b: int, k: nat, len: nat) -> bool
    decreases len - k,
{
    if k >= len {
        true
    } else {
        cs[a + k] == cs[b + k] && same_from(cs, a, b, k + 1, len)
    }
}

/// Rows `i` and `j` hold the same label.
pub open spec fn same_row(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, i: int, j: int) -> bool {
    ln[i] == ln[j] && same_from(cs, st[i] as int, st[j] as int, 0, ln[i] as nat)
}

/// Row `i`'s label differs from those of rows `j` to the end.
pub open spec fn row_unique(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, i: nat, j: nat) -> bool
    decreases rows() - j,
{
    if j >= rows() {
        true
    } else {
        !same_row(cs, st, ln, i as int, j as int) && row_unique(cs, st, ln, i, j + 1)
    }
}

/// Rows `i` to the end each differ from every later row.
pub open spec fn all_unique(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, i: nat) -> bool
    decreases rows() - i,
{
    if i >= rows() {
        true
    } else {
        row_unique(cs, st, ln, i, i + 1) && all_unique(cs, st, ln, i + 1)
    }
}

/// ASCII lowercase of a byte.
pub open spec fn lower(b: u8) -> u8 {
    if 0x41 <= b <= 0x5A {
        (b + 0x20) as u8
    } else {
        b
    }
}

/// Row `r`'s label is the ASCII lowercase of encoding `n`'s name.
pub open spec fn row_is_name(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, ns: Seq<u32>, nl: Seq<u8>, n: int, r: int) -> bool {
    ln[r] == nl[n] && lower_from(cs, st[r] as int, ns[n] as int, 0, nl[n] as nat)
}

/// `cs[a + k ..]` is the lowercase of `cs[b + k ..]` for `len - k` bytes.
pub open spec fn lower_from(cs: Seq<u8>, a: int, b: int, k: nat, len: nat) -> bool
    decreases len - k,
{
    if k >= len {
        true
    } else {
        cs[a + k] == lower(cs[b + k]) && lower_from(cs, a, b, k + 1, len)
    }
}

/// The first row from `r` that is encoding `n`'s lowercased name and is
/// listed under `n`.
pub open spec fn name_row_from(
    cs: Seq<u8>,
    st: Seq<u32>,
    ln: Seq<u8>,
    en: Seq<u8>,
    ns: Seq<u32>,
    nl: Seq<u8>,
    n: int,
    r: nat,
) -> Option<nat>
    decreases rows() - r,
{
    if r >= rows() {
        None
    } else if en[r as int] == n && row_is_name(cs, st, ln, ns, nl, n, r as int) {
        Some(r)
    } else {
        name_row_from(cs, st, ln, en, ns, nl, n, r + 1)
    }
}

/// Encodings `n` to 39 have well-formed names found among the rows.
pub open spec fn names_ok(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, en: Seq<u8>, ns: Seq<u32>, nl: Seq<u8>, n: nat) -> bool
    decreases 40 - n,
{
    if n >= 40 {
        true
    } else {
        nl[n as int] > 0 && bytes_ok(cs, ns[n as int] as int, 0, nl[n as int] as nat, true)
            && name_row_from(cs, st, ln, en, ns, nl, n as int, 0) is Some && names_ok(cs, st, ln, en, ns, nl, n + 1)
    }
}

/// The generated tables, as sequences.
pub open spec fn cs() -> Seq<u8> {
    super::data::LABEL_CHARS_0@
}

/// See [`cs`].
pub open spec fn st() -> Seq<u32> {
    super::data::LABEL_START_0@
}

/// See [`cs`].
pub open spec fn ln() -> Seq<u8> {
    super::data::LABEL_LEN_0@
}

/// See [`cs`].
pub open spec fn en() -> Seq<u8> {
    super::data::LABEL_ENCODING_0@
}

/// See [`cs`].
pub open spec fn ns() -> Seq<u32> {
    super::data::NAME_START_0@
}

/// See [`cs`].
pub open spec fn nl() -> Seq<u8> {
    super::data::NAME_LEN_0@
}

/// Everything the symbolic proofs need from the table.
pub open spec fn table_ok() -> bool {
    &&& label_count() == rows()
    &&& st().len() == rows() && ln().len() == rows() && en().len() == rows()
    &&& ns().len() == 40 && nl().len() == 40
    &&& rows_ok(cs(), st(), ln(), en(), 0)
    &&& all_unique(cs(), st(), ln(), 0)
    &&& names_ok(cs(), st(), ln(), en(), ns(), nl(), 0)
}

/// The generated table is [`table_ok`], by evaluation.
pub proof fn lemma_table()
    ensures
        table_ok(),
{
    reveal(super::data::LABEL_START_0);
    reveal(super::data::LABEL_LEN_0);
    reveal(super::data::LABEL_ENCODING_0);
    reveal(super::data::NAME_START_0);
    reveal(super::data::NAME_LEN_0);
    reveal(super::data::LABEL_CHARS_0);
    assert(rows_ok(super::data::LABEL_CHARS_0@, super::data::LABEL_START_0@, super::data::LABEL_LEN_0@, super::data::LABEL_ENCODING_0@, 0)) by (compute_only);
    assert(all_unique(super::data::LABEL_CHARS_0@, super::data::LABEL_START_0@, super::data::LABEL_LEN_0@, 0)) by (compute_only);
    assert(names_ok(super::data::LABEL_CHARS_0@, super::data::LABEL_START_0@, super::data::LABEL_LEN_0@, super::data::LABEL_ENCODING_0@, super::data::NAME_START_0@, super::data::NAME_LEN_0@, 0)) by (compute_only);
}

// ---------------------------------------------------------------------
// From the evaluated facts to quantified ones.

proof fn lemma_bytes_ok_at(cs: Seq<u8>, start: int, k: nat, len: nat, name: bool, t: nat)
    requires
        bytes_ok(cs, start, k, len, name),
        k <= t < len,
    ensures
        0 <= start + t < cs.len(),
        if name {
            name_byte(cs[start + t])
        } else {
            label_byte(cs[start + t])
        },
    decreases t - k,
{
    if k < t {
        lemma_bytes_ok_at(cs, start, k + 1, len, name, t);
    }
}

proof fn lemma_rows_ok_at(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, en: Seq<u8>, k: nat, i: nat)
    requires
        rows_ok(cs, st, ln, en, k),
        k <= i < rows(),
    ensures
        ln[i as int] > 0 && en[i as int] < 40 && bytes_ok(cs, st[i as int] as int, 0, ln[i as int] as nat, false),
    decreases i - k,
{
    if k < i {
        lemma_rows_ok_at(cs, st, ln, en, k + 1, i);
    }
}

proof fn lemma_row_unique_at(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, i: nat, k: nat, j: nat)
    requires
        row_unique(cs, st, ln, i, k),
        k <= j < rows(),
    ensures
        !same_row(cs, st, ln, i as int, j as int),
    decreases j - k,
{
    if k < j {
        lemma_row_unique_at(cs, st, ln, i, k + 1, j);
    }
}

proof fn lemma_all_unique_at(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, k: nat, i: nat)
    requires
        all_unique(cs, st, ln, k),
        k <= i < rows(),
    ensures
        row_unique(cs, st, ln, i, i + 1),
    decreases i - k,
{
    if k < i {
        lemma_all_unique_at(cs, st, ln, k + 1, i);
    }
}

proof fn lemma_names_ok_at(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, en: Seq<u8>, ns: Seq<u32>, nl: Seq<u8>, k: nat, n: nat)
    requires
        names_ok(cs, st, ln, en, ns, nl, k),
        k <= n < 40,
    ensures
        nl[n as int] > 0 && bytes_ok(cs, ns[n as int] as int, 0, nl[n as int] as nat, true)
            && name_row_from(cs, st, ln, en, ns, nl, n as int, 0) is Some,
    decreases n - k,
{
    if k < n {
        lemma_names_ok_at(cs, st, ln, en, ns, nl, k + 1, n);
    }
}

proof fn lemma_name_row_from(cs: Seq<u8>, st: Seq<u32>, ln: Seq<u8>, en: Seq<u8>, ns: Seq<u32>, nl: Seq<u8>, n: int, r: nat)
    requires
        name_row_from(cs, st, ln, en, ns, nl, n, r) is Some,
    ensures
        ({
            let x = name_row_from(cs, st, ln, en, ns, nl, n, r)->0;
            x < rows() && en[x as int] == n && row_is_name(cs, st, ln, ns, nl, n, x as int)
        }),
    decreases rows() - r,
{
    if r < rows() && !(en[r as int] == n && row_is_name(cs, st, ln, ns, nl, n, r as int)) {
        lemma_name_row_from(cs, st, ln, en, ns, nl, n, r + 1);
    }
}

proof fn lemma_same_from(cs: Seq<u8>, a: int, b: int, k: nat, len: nat)
    requires
        forall|t: int| k <= t < len ==> #[trigger] cs[a + t] == cs[b + t],
    ensures
        same_from(cs, a, b, k, len),
    decreases len - k,
{
    if k < len {
        lemma_same_from(cs, a, b, k + 1, len);
    }
}

proof fn lemma_lower_from_at(cs: Seq<u8>, a: int, b: int, k: nat, len: nat, t: nat)
    requires
        lower_from(cs, a, b, k, len),
        k <= t < len,
    ensures
        cs[a + t] == lower(cs[b + t]),
    decreases t - k,
{
    if k < t {
        lemma_lower_from_at(cs, a, b, k + 1, len, t);
    }
}

/// Row `i`'s label's length and encoding, read from the sequences.
pub proof fn lemma_row_label(i: int)
    requires
        table_ok(),
        0 <= i < rows(),
    ensures
        row_label(i).len() == ln()[i],
        ln()[i] > 0,
        row_encoding(i) == encoding_from_number(en()[i] as int),
        en()[i] < 40,
{
    lemma_rows_ok_at(cs(), st(), ln(), en(), 0, i as nat);
    assert(super::data::label_start_at(i) == st()[i]);
    assert(super::data::label_len_at(i) == ln()[i]);
    assert(super::data::label_encoding_at(i) == en()[i]);
}

/// Character `k` of row `i`'s label, read from the sequences.
pub proof fn lemma_row_char(i: int, k: int)
    requires
        table_ok(),
        0 <= i < rows(),
        0 <= k < ln()[i],
    ensures
        0 <= st()[i] + k < cs().len(),
        label_byte(cs()[st()[i] + k]),
        row_label(i)[k] == cs()[st()[i] + k] as u32,
{
    lemma_row_label(i);
    lemma_rows_ok_at(cs(), st(), ln(), en(), 0, i as nat);
    lemma_bytes_ok_at(cs(), st()[i] as int, 0, ln()[i] as nat, false, k as nat);
    assert(cs().len() == super::data::LABEL_CHARS_LEN);
    assert(super::data::label_chars_at(st()[i] + k) == cs()[st()[i] + k]);
}

/// A row's label is its own ASCII lowercase.
pub proof fn lemma_row_lowercase(i: int)
    requires
        table_ok(),
        0 <= i < rows(),
    ensures
        ascii_lowercase(row_label(i)) == row_label(i),
{
    lemma_row_label(i);
    assert forall|k: int| 0 <= k < row_label(i).len() implies #[trigger] ascii_lowercase(row_label(i))[k]
        == row_label(i)[k] by {
        lemma_row_char(i, k);
    }
    assert(ascii_lowercase(row_label(i)) =~= row_label(i));
}

/// Two rows with equal labels are the same row.
proof fn lemma_rows_equal(i: int, j: int)
    requires
        table_ok(),
        0 <= i < rows(),
        0 <= j < rows(),
        row_label(i) == row_label(j),
    ensures
        i == j,
{
    lemma_row_label(i);
    lemma_row_label(j);
    if i != j {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        assert forall|t: int| 0 <= t < ln()[a] implies #[trigger] cs()[st()[a] + t] == cs()[st()[b] + t] by {
            lemma_row_char(a, t);
            lemma_row_char(b, t);
            assert(row_label(a)[t] == row_label(b)[t]);
        }
        lemma_same_from(cs(), st()[a] as int, st()[b] as int, 0, ln()[a] as nat);
        lemma_all_unique_at(cs(), st(), ln(), 0, a as nat);
        lemma_row_unique_at(cs(), st(), ln(), a as nat, (a + 1) as nat, b as nat);
    }
}

/// No label is listed twice, even ignoring ASCII case: two rows whose
/// labels are an ASCII case-insensitive match are the same row.
pub proof fn lemma_labels_distinct(i: int, j: int)
    requires
        0 <= i < label_count(),
        0 <= j < label_count(),
        ascii_case_insensitive_match(row_label(i), row_label(j)),
    ensures
        i == j,
{
    lemma_table();
    lemma_row_lowercase(i);
    lemma_row_lowercase(j);
    lemma_rows_equal(i, j);
}

/// The first match is row `i` when row `i` matches and no earlier row does.
proof fn lemma_first_match(label: Seq<u32>, k: nat, i: nat)
    requires
        k <= i < label_count(),
        ascii_case_insensitive_match(label, row_label(i as int)),
        forall|j: int| k <= j < i ==> !ascii_case_insensitive_match(label, #[trigger] row_label(j)),
    ensures
        first_match(label, k) == Some(i),
    decreases i - k,
{
    if k < i {
        lemma_first_match(label, k + 1, i);
    }
}

/// A string whose first and last code points are not ASCII whitespace is
/// unchanged by stripping.
proof fn lemma_strip(s: Seq<u32>)
    requires
        s.len() > 0,
        !is_ascii_whitespace(s[0]),
        !is_ascii_whitespace(s[s.len() - 1]),
    ensures
        strip_leading_and_trailing_ascii_whitespace(s) == s,
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

/// Every label maps to exactly one encoding: "get an encoding" of row `i`'s
/// label is the encoding it is listed under (and no other row matches it,
/// [`lemma_labels_distinct`]).
pub proof fn lemma_every_label(i: int)
    requires
        0 <= i < label_count(),
    ensures
        get_an_encoding(row_label(i)) == Some(row_encoding(i)),
{
    lemma_table();
    lemma_row_label(i);
    let l = row_label(i);
    lemma_row_char(i, 0);
    lemma_row_char(i, l.len() - 1);
    lemma_strip(l);
    assert forall|j: int| 0 <= j < i implies !ascii_case_insensitive_match(l, #[trigger] row_label(j)) by {
        if ascii_case_insensitive_match(l, row_label(j)) {
            lemma_labels_distinct(i, j);
        }
    }
    lemma_first_match(l, 0, i as nat);
}

/// The number of an encoding names it back.
pub proof fn lemma_number(e: Encoding)
    ensures
        encoding_number(e) < 40,
        encoding_from_number(encoding_number(e) as int) == e,
{
}

/// Character `k` of an encoding's name, read from the sequences.
pub proof fn lemma_name_char(e: Encoding, k: int)
    requires
        table_ok(),
        0 <= k < nl()[encoding_number(e) as int],
    ensures
        name(e).len() == nl()[encoding_number(e) as int],
        nl()[encoding_number(e) as int] > 0,
        0 <= ns()[encoding_number(e) as int] + k < cs().len(),
        name_byte(cs()[ns()[encoding_number(e) as int] + k]),
        name(e)[k] == cs()[ns()[encoding_number(e) as int] + k] as u32,
{
    lemma_number(e);
    let n = encoding_number(e);
    lemma_names_ok_at(cs(), st(), ln(), en(), ns(), nl(), 0, n);
    lemma_bytes_ok_at(cs(), ns()[n as int] as int, 0, nl()[n as int] as nat, true, k as nat);
    assert(super::data::name_start_at(n as int) == ns()[n as int]);
    assert(super::data::name_len_at(n as int) == nl()[n as int]);
    assert(cs().len() == super::data::LABEL_CHARS_LEN);
    assert(super::data::label_chars_at(ns()[n as int] + k) == cs()[ns()[n as int] + k]);
}

/// "Get an encoding" of an encoding's own name is that encoding.
pub proof fn lemma_name_maps_to_itself(e: Encoding)
    ensures
        get_an_encoding(name(e)) == Some(e),
{
    lemma_table();
    lemma_number(e);
    let n = encoding_number(e);
    lemma_names_ok_at(cs(), st(), ln(), en(), ns(), nl(), 0, n);
    lemma_name_row_from(cs(), st(), ln(), en(), ns(), nl(), n as int, 0);
    let r = name_row_from(cs(), st(), ln(), en(), ns(), nl(), n as int, 0)->0;
    lemma_row_label(r as int);
    let nm = name(e);
    assert(super::data::name_start_at(n as int) == ns()[n as int]);
    assert(super::data::name_len_at(n as int) == nl()[n as int]);
    lemma_name_char(e, 0);
    lemma_name_char(e, nm.len() - 1);
    lemma_strip(nm);
    // The lowercased name is row r's label.
    assert forall|k: int| 0 <= k < nm.len() implies #[trigger] ascii_lowercase(nm)[k] == row_label(
        r as int,
    )[k] by {
        lemma_name_char(e, k);
        lemma_row_char(r as int, k);
        lemma_lower_from_at(cs(), st()[r as int] as int, ns()[n as int] as int, 0, nl()[n as int] as nat, k as nat);
    }
    assert(ascii_lowercase(nm) =~= row_label(r as int));
    lemma_row_lowercase(r as int);
    assert forall|j: int| 0 <= j < r implies !ascii_case_insensitive_match(nm, #[trigger] row_label(j)) by {
        if ascii_case_insensitive_match(nm, row_label(j)) {
            lemma_row_lowercase(j);
            lemma_rows_equal(j, r as int);
        }
    }
    lemma_first_match(nm, 0, r);
}

} // verus!
