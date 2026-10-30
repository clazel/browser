//! Facts about the generated single-byte indexes ([`super::data`]),
//! proven by evaluating each table: every entry is null or a scalar value
//! of at least U+0080 ([`entry_ok`]), and no code point appears twice in
//! one index. The generator checks the same when it writes the tables
//! (`xtask/src/encoding_indexes.rs`), but nothing relies on that: these
//! lemmas are what the decoder's lemmas use, and a table that breaks them
//! fails here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The generated table that is `e`'s index (empty for an encoding that is
/// not single-byte).
pub open spec fn table(e: crate::labels::spec::Encoding) -> Seq<u32> {
    match e {
        crate::labels::spec::Encoding::Ibm866 => super::data::INDEX_IBM866_0@,
        crate::labels::spec::Encoding::Iso8859_2 => super::data::INDEX_ISO_8859_2_0@,
        crate::labels::spec::Encoding::Iso8859_3 => super::data::INDEX_ISO_8859_3_0@,
        crate::labels::spec::Encoding::Iso8859_4 => super::data::INDEX_ISO_8859_4_0@,
        crate::labels::spec::Encoding::Iso8859_5 => super::data::INDEX_ISO_8859_5_0@,
        crate::labels::spec::Encoding::Iso8859_6 => super::data::INDEX_ISO_8859_6_0@,
        crate::labels::spec::Encoding::Iso8859_7 => super::data::INDEX_ISO_8859_7_0@,
        crate::labels::spec::Encoding::Iso8859_8 => super::data::INDEX_ISO_8859_8_0@,
        crate::labels::spec::Encoding::Iso8859_8I => super::data::INDEX_ISO_8859_8_0@,
        crate::labels::spec::Encoding::Iso8859_10 => super::data::INDEX_ISO_8859_10_0@,
        crate::labels::spec::Encoding::Iso8859_13 => super::data::INDEX_ISO_8859_13_0@,
        crate::labels::spec::Encoding::Iso8859_14 => super::data::INDEX_ISO_8859_14_0@,
        crate::labels::spec::Encoding::Iso8859_15 => super::data::INDEX_ISO_8859_15_0@,
        crate::labels::spec::Encoding::Iso8859_16 => super::data::INDEX_ISO_8859_16_0@,
        crate::labels::spec::Encoding::Koi8R => super::data::INDEX_KOI8_R_0@,
        crate::labels::spec::Encoding::Koi8U => super::data::INDEX_KOI8_U_0@,
        crate::labels::spec::Encoding::Macintosh => super::data::INDEX_MACINTOSH_0@,
        crate::labels::spec::Encoding::Windows874 => super::data::INDEX_WINDOWS_874_0@,
        crate::labels::spec::Encoding::Windows1250 => super::data::INDEX_WINDOWS_1250_0@,
        crate::labels::spec::Encoding::Windows1251 => super::data::INDEX_WINDOWS_1251_0@,
        crate::labels::spec::Encoding::Windows1252 => super::data::INDEX_WINDOWS_1252_0@,
        crate::labels::spec::Encoding::Windows1253 => super::data::INDEX_WINDOWS_1253_0@,
        crate::labels::spec::Encoding::Windows1254 => super::data::INDEX_WINDOWS_1254_0@,
        crate::labels::spec::Encoding::Windows1255 => super::data::INDEX_WINDOWS_1255_0@,
        crate::labels::spec::Encoding::Windows1256 => super::data::INDEX_WINDOWS_1256_0@,
        crate::labels::spec::Encoding::Windows1257 => super::data::INDEX_WINDOWS_1257_0@,
        crate::labels::spec::Encoding::Windows1258 => super::data::INDEX_WINDOWS_1258_0@,
        crate::labels::spec::Encoding::XMacCyrillic => super::data::INDEX_X_MAC_CYRILLIC_0@,
        _ => Seq::empty(),
    }
}

/// An index entry is null or a scalar value from U+0080: never ASCII,
/// never a surrogate, never above U+10FFFF.
pub open spec fn entry_ok(v: u32) -> bool {
    v == null_entry() || (0x80 <= v <= 0x10FFFF && !(0xD800 <= v <= 0xDFFF))
}

/// Entries `p` to 127 of `t` are [`entry_ok`].
pub open spec fn entries_ok_from(t: Seq<u32>, p: nat) -> bool
    decreases 128 - p,
{
    if p >= 128 {
        true
    } else {
        entry_ok(t[p as int]) && entries_ok_from(t, p + 1)
    }
}

/// Entry `p` of `t` is null or differs from entries `q` to 127.
pub open spec fn row_distinct(t: Seq<u32>, p: nat, q: nat) -> bool
    decreases 128 - q,
{
    if q >= 128 {
        true
    } else {
        (t[p as int] == null_entry() || t[p as int] != t[q as int]) && row_distinct(t, p, q + 1)
    }
}

/// Rows `p` to `end - 1` of `t` are each [`row_distinct`] from the rows
/// after them.
pub open spec fn distinct_from(t: Seq<u32>, p: nat, end: nat) -> bool
    decreases end - p,
{
    if p >= end {
        true
    } else {
        row_distinct(t, p, p + 1) && distinct_from(t, p + 1, end)
    }
}

/// The two facts, for all of `e`'s index.
pub open spec fn index_ok(e: crate::labels::spec::Encoding) -> bool {
    table(e).len() == 128 && entries_ok_from(table(e), 0) && distinct_from(table(e), 0, 128)
}

/// index ibm866 is [`index_ok`].
pub proof fn lemma_index_ibm866()
    ensures
        index_ok(crate::labels::spec::Encoding::Ibm866),
{
    reveal(super::data::INDEX_IBM866_0);
    assert(entries_ok_from(super::data::INDEX_IBM866_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_IBM866_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-2 is [`index_ok`].
pub proof fn lemma_index_iso_8859_2()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_2),
{
    reveal(super::data::INDEX_ISO_8859_2_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_2_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_2_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-3 is [`index_ok`].
pub proof fn lemma_index_iso_8859_3()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_3),
{
    reveal(super::data::INDEX_ISO_8859_3_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_3_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_3_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-4 is [`index_ok`].
pub proof fn lemma_index_iso_8859_4()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_4),
{
    reveal(super::data::INDEX_ISO_8859_4_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_4_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_4_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-5 is [`index_ok`].
pub proof fn lemma_index_iso_8859_5()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_5),
{
    reveal(super::data::INDEX_ISO_8859_5_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_5_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_5_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-6 is [`index_ok`].
pub proof fn lemma_index_iso_8859_6()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_6),
{
    reveal(super::data::INDEX_ISO_8859_6_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_6_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_6_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-7 is [`index_ok`].
pub proof fn lemma_index_iso_8859_7()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_7),
{
    reveal(super::data::INDEX_ISO_8859_7_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_7_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_7_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-8 is [`index_ok`].
pub proof fn lemma_index_iso_8859_8()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_8),
{
    reveal(super::data::INDEX_ISO_8859_8_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_8_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_8_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-10 is [`index_ok`].
pub proof fn lemma_index_iso_8859_10()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_10),
{
    reveal(super::data::INDEX_ISO_8859_10_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_10_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_10_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-13 is [`index_ok`].
pub proof fn lemma_index_iso_8859_13()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_13),
{
    reveal(super::data::INDEX_ISO_8859_13_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_13_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_13_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-14 is [`index_ok`].
pub proof fn lemma_index_iso_8859_14()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_14),
{
    reveal(super::data::INDEX_ISO_8859_14_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_14_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_14_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-15 is [`index_ok`].
pub proof fn lemma_index_iso_8859_15()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_15),
{
    reveal(super::data::INDEX_ISO_8859_15_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_15_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_15_0@, 0, 128)) by (compute_only);
}

/// index iso-8859-16 is [`index_ok`].
pub proof fn lemma_index_iso_8859_16()
    ensures
        index_ok(crate::labels::spec::Encoding::Iso8859_16),
{
    reveal(super::data::INDEX_ISO_8859_16_0);
    assert(entries_ok_from(super::data::INDEX_ISO_8859_16_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_ISO_8859_16_0@, 0, 128)) by (compute_only);
}

/// index koi8-r is [`index_ok`].
pub proof fn lemma_index_koi8_r()
    ensures
        index_ok(crate::labels::spec::Encoding::Koi8R),
{
    reveal(super::data::INDEX_KOI8_R_0);
    assert(entries_ok_from(super::data::INDEX_KOI8_R_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_KOI8_R_0@, 0, 128)) by (compute_only);
}

/// index koi8-u is [`index_ok`].
pub proof fn lemma_index_koi8_u()
    ensures
        index_ok(crate::labels::spec::Encoding::Koi8U),
{
    reveal(super::data::INDEX_KOI8_U_0);
    assert(entries_ok_from(super::data::INDEX_KOI8_U_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_KOI8_U_0@, 0, 128)) by (compute_only);
}

/// index macintosh is [`index_ok`].
pub proof fn lemma_index_macintosh()
    ensures
        index_ok(crate::labels::spec::Encoding::Macintosh),
{
    reveal(super::data::INDEX_MACINTOSH_0);
    assert(entries_ok_from(super::data::INDEX_MACINTOSH_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_MACINTOSH_0@, 0, 128)) by (compute_only);
}

/// index windows-874 is [`index_ok`].
pub proof fn lemma_index_windows_874()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows874),
{
    reveal(super::data::INDEX_WINDOWS_874_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_874_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_874_0@, 0, 128)) by (compute_only);
}

/// index windows-1250 is [`index_ok`].
pub proof fn lemma_index_windows_1250()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1250),
{
    reveal(super::data::INDEX_WINDOWS_1250_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1250_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1250_0@, 0, 128)) by (compute_only);
}

/// index windows-1251 is [`index_ok`].
pub proof fn lemma_index_windows_1251()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1251),
{
    reveal(super::data::INDEX_WINDOWS_1251_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1251_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1251_0@, 0, 128)) by (compute_only);
}

/// index windows-1252 is [`index_ok`].
pub proof fn lemma_index_windows_1252()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1252),
{
    reveal(super::data::INDEX_WINDOWS_1252_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1252_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1252_0@, 0, 128)) by (compute_only);
}

/// index windows-1253 is [`index_ok`].
pub proof fn lemma_index_windows_1253()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1253),
{
    reveal(super::data::INDEX_WINDOWS_1253_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1253_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1253_0@, 0, 128)) by (compute_only);
}

/// index windows-1254 is [`index_ok`].
pub proof fn lemma_index_windows_1254()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1254),
{
    reveal(super::data::INDEX_WINDOWS_1254_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1254_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1254_0@, 0, 128)) by (compute_only);
}

/// index windows-1255 is [`index_ok`].
pub proof fn lemma_index_windows_1255()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1255),
{
    reveal(super::data::INDEX_WINDOWS_1255_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1255_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1255_0@, 0, 128)) by (compute_only);
}

/// index windows-1256 is [`index_ok`].
pub proof fn lemma_index_windows_1256()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1256),
{
    reveal(super::data::INDEX_WINDOWS_1256_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1256_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1256_0@, 0, 128)) by (compute_only);
}

/// index windows-1257 is [`index_ok`].
pub proof fn lemma_index_windows_1257()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1257),
{
    reveal(super::data::INDEX_WINDOWS_1257_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1257_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1257_0@, 0, 128)) by (compute_only);
}

/// index windows-1258 is [`index_ok`].
pub proof fn lemma_index_windows_1258()
    ensures
        index_ok(crate::labels::spec::Encoding::Windows1258),
{
    reveal(super::data::INDEX_WINDOWS_1258_0);
    assert(entries_ok_from(super::data::INDEX_WINDOWS_1258_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_WINDOWS_1258_0@, 0, 128)) by (compute_only);
}

/// index x-mac-cyrillic is [`index_ok`].
pub proof fn lemma_index_x_mac_cyrillic()
    ensures
        index_ok(crate::labels::spec::Encoding::XMacCyrillic),
{
    reveal(super::data::INDEX_X_MAC_CYRILLIC_0);
    assert(entries_ok_from(super::data::INDEX_X_MAC_CYRILLIC_0@, 0)) by (compute_only);
    assert(distinct_from(super::data::INDEX_X_MAC_CYRILLIC_0@, 0, 128)) by (compute_only);
}

/// Every single-byte encoding's index is [`index_ok`].
pub proof fn lemma_index_ok(e: crate::labels::spec::Encoding)
    requires
        is_single_byte(e),
    ensures
        index_ok(e),
{
    match e {
        crate::labels::spec::Encoding::Ibm866 => lemma_index_ibm866(),
        crate::labels::spec::Encoding::Iso8859_2 => lemma_index_iso_8859_2(),
        crate::labels::spec::Encoding::Iso8859_3 => lemma_index_iso_8859_3(),
        crate::labels::spec::Encoding::Iso8859_4 => lemma_index_iso_8859_4(),
        crate::labels::spec::Encoding::Iso8859_5 => lemma_index_iso_8859_5(),
        crate::labels::spec::Encoding::Iso8859_6 => lemma_index_iso_8859_6(),
        crate::labels::spec::Encoding::Iso8859_7 => lemma_index_iso_8859_7(),
        crate::labels::spec::Encoding::Iso8859_8 => lemma_index_iso_8859_8(),
        crate::labels::spec::Encoding::Iso8859_8I => lemma_index_iso_8859_8(),
        crate::labels::spec::Encoding::Iso8859_10 => lemma_index_iso_8859_10(),
        crate::labels::spec::Encoding::Iso8859_13 => lemma_index_iso_8859_13(),
        crate::labels::spec::Encoding::Iso8859_14 => lemma_index_iso_8859_14(),
        crate::labels::spec::Encoding::Iso8859_15 => lemma_index_iso_8859_15(),
        crate::labels::spec::Encoding::Iso8859_16 => lemma_index_iso_8859_16(),
        crate::labels::spec::Encoding::Koi8R => lemma_index_koi8_r(),
        crate::labels::spec::Encoding::Koi8U => lemma_index_koi8_u(),
        crate::labels::spec::Encoding::Macintosh => lemma_index_macintosh(),
        crate::labels::spec::Encoding::Windows874 => lemma_index_windows_874(),
        crate::labels::spec::Encoding::Windows1250 => lemma_index_windows_1250(),
        crate::labels::spec::Encoding::Windows1251 => lemma_index_windows_1251(),
        crate::labels::spec::Encoding::Windows1252 => lemma_index_windows_1252(),
        crate::labels::spec::Encoding::Windows1253 => lemma_index_windows_1253(),
        crate::labels::spec::Encoding::Windows1254 => lemma_index_windows_1254(),
        crate::labels::spec::Encoding::Windows1255 => lemma_index_windows_1255(),
        crate::labels::spec::Encoding::Windows1256 => lemma_index_windows_1256(),
        crate::labels::spec::Encoding::Windows1257 => lemma_index_windows_1257(),
        crate::labels::spec::Encoding::Windows1258 => lemma_index_windows_1258(),
        crate::labels::spec::Encoding::XMacCyrillic => lemma_index_x_mac_cyrillic(),
        _ => {},
    }
}

/// Entry `p` of a single-byte encoding's index is entry `p` of its table.
pub proof fn lemma_table_entry(e: crate::labels::spec::Encoding, p: int)
    requires
        is_single_byte(e),
        0 <= p < 128,
    ensures
        index_entry(e, p) == table(e)[p],
{
}

proof fn lemma_entries_ok_at(t: Seq<u32>, k: nat, p: nat)
    requires
        entries_ok_from(t, k),
        k <= p < 128,
    ensures
        entry_ok(t[p as int]),
    decreases p - k,
{
    if k < p {
        lemma_entries_ok_at(t, k + 1, p);
    }
}

proof fn lemma_row_distinct_at(t: Seq<u32>, p: nat, k: nat, q: nat)
    requires
        row_distinct(t, p, k),
        k <= q < 128,
    ensures
        t[p as int] == null_entry() || t[p as int] != t[q as int],
    decreases q - k,
{
    if k < q {
        lemma_row_distinct_at(t, p, k + 1, q);
    }
}

proof fn lemma_distinct_row(t: Seq<u32>, k: nat, end: nat, p: nat)
    requires
        distinct_from(t, k, end),
        k <= p < end,
    ensures
        row_distinct(t, p, p + 1),
    decreases p - k,
{
    if k < p {
        lemma_distinct_row(t, k + 1, end, p);
    }
}

/// Every entry of a single-byte encoding's index is [`entry_ok`].
pub proof fn lemma_entry_ok(e: crate::labels::spec::Encoding, p: int)
    requires
        is_single_byte(e),
        0 <= p < 128,
    ensures
        entry_ok(index_entry(e, p)),
{
    lemma_index_ok(e);
    lemma_table_entry(e, p);
    lemma_entries_ok_at(table(e), 0, p as nat);
}

/// No code point appears twice in a single-byte encoding's index.
pub proof fn lemma_entries_distinct(e: crate::labels::spec::Encoding, p: int, q: int)
    requires
        is_single_byte(e),
        0 <= p < 128,
        0 <= q < 128,
        p != q,
        index_entry(e, p) != null_entry(),
    ensures
        index_entry(e, p) != index_entry(e, q),
{
    lemma_index_ok(e);
    lemma_table_entry(e, p);
    lemma_table_entry(e, q);
    let t = table(e);
    if p < q {
        lemma_distinct_row(t, 0, 128, p as nat);
        lemma_row_distinct_at(t, p as nat, (p + 1) as nat, q as nat);
    } else {
        lemma_distinct_row(t, 0, 128, q as nat);
        lemma_row_distinct_at(t, q as nat, (q + 1) as nat, p as nat);
    }
}

} // verus!
