//! The two transcriptions of HTML §13.2.3.2's prescan agree on every input:
//! [`super::independent_prescan::prescan`] (written from the standard's text
//! without reading `spec.rs`) equals [`super::spec::prescan`] for all bytes,
//! with no exclusions. Both read the same text, so this is a same-text
//! check: it catches a misreading made by one transcriber but not the other.
//!
//! Where the two differ in form, the proof bridges them:
//! - searches started at different bytes (the comment end from `<` + 1 or
//!   from `<!--` + 4, the tag end from `<` or from `<` + 1);
//! - "starts with" as a subrange comparison or as one test per byte;
//! - "already in attribute list" scanned from the front or from the back;
//! - *charset* as an enum or as nested options;
//! - "extracting a character encoding from a meta element", step 6
//!   "Otherwise", when "this character" is 0x3B (;): `spec.rs` takes the
//!   empty substring, the other text takes the 0x3B and what follows up to
//!   the next whitespace or 0x3B. "Get an encoding" fails on both: no label
//!   is empty and none has a 0x3B (proven from the label table).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Correspondences between the two transcriptions' results
// ---------------------------------------------------------------------------

/// The spec's [`super::spec::Attr`] for the other text's get an attribute
/// result.
pub open spec fn attr_of(r: super::independent_prescan::GetAttribute) -> super::spec::Attr {
    match r {
        super::independent_prescan::GetAttribute::OutOfBytes => super::spec::Attr::Abort,
        super::independent_prescan::GetAttribute::NoAttribute { position } => super::spec::Attr::None(position),
        super::independent_prescan::GetAttribute::Attribute { name, value, position } => super::spec::Attr::Some(
            name,
            value,
            position,
        ),
    }
}

/// The spec's *charset* for the other text's nested options.
pub open spec fn charset_of(c: Option<Option<clazel_encoding::labels::spec::Encoding>>) -> super::spec::Charset {
    match c {
        None => super::spec::Charset::Null,
        Some(None) => super::spec::Charset::Failure,
        Some(Some(e)) => super::spec::Charset::Encoding(e),
    }
}

/// The spec's `<meta>` result for the other text's loop step.
pub open spec fn meta_result_of(r: super::independent_prescan::LoopStep) -> super::spec::MetaResult {
    match r {
        super::independent_prescan::LoopStep::OutOfBytes => super::spec::MetaResult::Abort,
        super::independent_prescan::LoopStep::Return(e) => super::spec::MetaResult::Return(e),
        super::independent_prescan::LoopStep::NextByte(p) => super::spec::MetaResult::NextByte(p),
    }
}

/// The spec's "extracting a character encoding from a meta element" from
/// step 2 at `position`, with "get an encoding" applied.
pub open spec fn extract_from(s: Seq<u8>, position: nat) -> Option<clazel_encoding::labels::spec::Encoding> {
    match super::spec::extract_label_from(s, position) {
        Some(label) => clazel_encoding::labels::spec::get_an_encoding(super::spec::as_string(label)),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Small bridges
// ---------------------------------------------------------------------------

/// Both texts turn bytes into code points the same way.
proof fn lemma_code_points(s: Seq<u8>)
    ensures
        super::independent_prescan::as_code_points(s) == super::spec::as_string(s),
{
    assert(super::independent_prescan::as_code_points(s) =~= super::spec::as_string(s));
}

/// "Starts with" two bytes, as a subrange or byte by byte.
proof fn lemma_starts_at_2(b: Seq<u8>, p: nat, x0: u8, x1: u8)
    ensures
        super::spec::starts_at(b, p, seq![x0, x1]) <==> (p + 2 <= b.len() && b[p as int] == x0 && b[(p + 1) as int] == x1),
{
    let pat = seq![x0, x1];
    if p + 2 <= b.len() {
        let sub = b.subrange(p as int, (p + 2) as int);
        if b[p as int] == x0 && b[(p + 1) as int] == x1 {
            assert(sub =~= pat);
        }
        if sub == pat {
            assert(sub[0] == pat[0] && sub[1] == pat[1]);
        }
    }
}

/// "Starts with" four bytes.
proof fn lemma_starts_at_4(b: Seq<u8>, p: nat, x0: u8, x1: u8, x2: u8, x3: u8)
    ensures
        super::spec::starts_at(b, p, seq![x0, x1, x2, x3]) <==> (p + 4 <= b.len() && b[p as int] == x0 && b[(p + 1) as int]
            == x1 && b[(p + 2) as int] == x2 && b[(p + 3) as int] == x3),
{
    let pat = seq![x0, x1, x2, x3];
    if p + 4 <= b.len() {
        let sub = b.subrange(p as int, (p + 4) as int);
        if b[p as int] == x0 && b[(p + 1) as int] == x1 && b[(p + 2) as int] == x2 && b[(p + 3) as int] == x3 {
            assert(sub =~= pat);
        }
        if sub == pat {
            assert(sub[0] == pat[0] && sub[1] == pat[1] && sub[2] == pat[2] && sub[3] == pat[3]);
        }
    }
}

/// "Starts with" six bytes.
proof fn lemma_starts_at_6(b: Seq<u8>, p: nat, x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8)
    ensures
        super::spec::starts_at(b, p, seq![x0, x1, x2, x3, x4, x5])
            <==> super::independent_prescan::starts_with_6(b, p, x0, x1, x2, x3, x4, x5),
{
    let pat = seq![x0, x1, x2, x3, x4, x5];
    if p + 6 <= b.len() {
        let sub = b.subrange(p as int, (p + 6) as int);
        if super::independent_prescan::starts_with_6(b, p, x0, x1, x2, x3, x4, x5) {
            assert(sub =~= pat);
        }
        if sub == pat {
            assert(sub[0] == pat[0] && sub[1] == pat[1] && sub[2] == pat[2] && sub[3] == pat[3] && sub[4] == pat[4]
                && sub[5] == pat[5]);
        }
    }
}

/// The spec's "already in attribute list", from `i`: some item from `i` is
/// `name`.
proof fn lemma_spec_in_list(list: Seq<Seq<u8>>, name: Seq<u8>, i: nat)
    ensures
        super::spec::in_list(list, name, i) <==> exists|k: int| i <= k < list.len() && list[k] == name,
    decreases list.len() - i,
{
    if i < list.len() {
        lemma_spec_in_list(list, name, i + 1);
        if exists|k: int| i <= k < list.len() && list[k] == name {
            let k = choose|k: int| i <= k < list.len() && list[k] == name;
            if k != i {
                assert(i + 1 <= k < list.len() && list[k] == name);
            }
        }
    }
}

/// The other text's "already in attribute list": some item is `name`.
proof fn lemma_independent_in_list(list: Seq<Seq<u8>>, name: Seq<u8>)
    ensures
        super::independent_prescan::in_list(list, name) <==> exists|k: int| 0 <= k < list.len() && list[k] == name,
    decreases list.len(),
{
    if list.len() > 0 {
        let rest = list.drop_last();
        lemma_independent_in_list(rest, name);
        if exists|k: int| 0 <= k < list.len() && list[k] == name {
            let k = choose|k: int| 0 <= k < list.len() && list[k] == name;
            if k != list.len() - 1 {
                assert(rest[k] == list[k]);
            }
        }
        if exists|k: int| 0 <= k < rest.len() && rest[k] == name {
            let k = choose|k: int| 0 <= k < rest.len() && rest[k] == name;
            assert(list[k] == rest[k]);
        }
    }
}

/// The two "already in attribute list" tests agree.
proof fn lemma_in_list(list: Seq<Seq<u8>>, name: Seq<u8>)
    ensures
        super::independent_prescan::in_list(list, name) == super::spec::in_list(list, name, 0),
{
    lemma_spec_in_list(list, name, 0);
    lemma_independent_in_list(list, name);
}

// ---------------------------------------------------------------------------
// Get an attribute
// ---------------------------------------------------------------------------

/// Steps 11 and 12.
proof fn lemma_unquoted(b: Seq<u8>, pos: nat, name: Seq<u8>, value: Seq<u8>)
    ensures
        attr_of(super::independent_prescan::unquoted_value_step(b, pos, name, value)) == super::spec::attr_unquoted(
            b,
            pos,
            name,
            value,
        ),
    decreases b.len() - pos,
{
    if pos < b.len() {
        let c = b[pos as int];
        assert(super::independent_prescan::lowered(c) == super::spec::lower(c));
        lemma_unquoted(b, pos + 1, name, value.push(super::spec::lower(c)));
    }
}

/// Step 10's quoted value: the other text's quote loop at `pos` advances to
/// `pos + 1` first, where the spec's starts.
proof fn lemma_quoted(b: Seq<u8>, quote: u8, pos: nat, name: Seq<u8>, value: Seq<u8>)
    ensures
        attr_of(super::independent_prescan::quote_loop(b, quote, pos, name, value)) == super::spec::attr_quoted(
            b,
            pos + 1,
            name,
            value,
            quote,
        ),
    decreases b.len() - pos,
{
    if pos + 1 < b.len() {
        let c = b[(pos + 1) as int];
        assert(super::independent_prescan::lowered(c) == super::spec::lower(c));
        lemma_quoted(b, quote, pos + 1, name, value.push(super::spec::lower(c)));
    }
}

/// Steps 9 and 10.
proof fn lemma_value(b: Seq<u8>, pos: nat, name: Seq<u8>)
    ensures
        attr_of(super::independent_prescan::value_step(b, pos, name)) == super::spec::attr_value(b, pos, name),
    decreases b.len() - pos,
{
    if pos < b.len() {
        let c = b[pos as int];
        if super::spec::is_space(c) {
            lemma_value(b, pos + 1, name);
        } else if c == 0x22 || c == 0x27 {
            assert(Seq::<u8>::empty() =~= seq![]);
            lemma_quoted(b, c, pos, name, Seq::empty());
        } else if c != 0x3E {
            assert(super::independent_prescan::lowered(c) == super::spec::lower(c));
            lemma_unquoted(b, pos + 1, name, seq![super::spec::lower(c)]);
        }
    }
}

/// Steps 6 to 8.
proof fn lemma_spaces(b: Seq<u8>, pos: nat, name: Seq<u8>)
    ensures
        attr_of(super::independent_prescan::spaces_step(b, pos, name)) == super::spec::attr_spaces(b, pos, name),
    decreases b.len() - pos,
{
    if pos < b.len() {
        if super::spec::is_space(b[pos as int]) {
            lemma_spaces(b, pos + 1, name);
        } else if b[pos as int] == 0x3D {
            lemma_value(b, pos + 1, name);
        }
    }
}

/// Steps 4 and 5.
proof fn lemma_name(b: Seq<u8>, pos: nat, name: Seq<u8>)
    ensures
        attr_of(super::independent_prescan::attribute_name_step(b, pos, name)) == super::spec::attr_name(b, pos, name),
    decreases b.len() - pos,
{
    if pos < b.len() {
        let c = b[pos as int];
        if c == 0x3D && name.len() > 0 {
            lemma_value(b, pos + 1, name);
        } else if super::spec::is_space(c) {
            lemma_spaces(b, pos, name);
        } else if !(c == 0x2F || c == 0x3E) {
            assert(super::independent_prescan::lowered(c) == super::spec::lower(c));
            lemma_name(b, pos + 1, name.push(super::spec::lower(c)));
        }
    }
}

/// "Get an attribute": the two texts agree.
proof fn lemma_get_attribute(b: Seq<u8>, pos: nat)
    ensures
        attr_of(super::independent_prescan::get_an_attribute(b, pos)) == super::spec::get_attribute(b, pos),
    decreases b.len() - pos,
{
    if pos < b.len() {
        if super::spec::is_space(b[pos as int]) || b[pos as int] == 0x2F {
            lemma_get_attribute(b, pos + 1);
        } else if b[pos as int] != 0x3E {
            assert(Seq::<u8>::empty() =~= seq![]);
            lemma_name(b, pos, Seq::empty());
        }
    }
}

// ---------------------------------------------------------------------------
// Extracting a character encoding from a meta element
// ---------------------------------------------------------------------------

/// The searches for "charset" agree, and one that finds it finds it at or
/// after where it started, with all seven characters within `s`.
proof fn lemma_find_charset(s: Seq<u8>, i: nat)
    ensures
        super::independent_prescan::find_charset(s, i) == super::spec::find_charset(s, i),
        match super::spec::find_charset(s, i) {
            Some(k) => i <= k && k + 7 <= s.len(),
            None => true,
        },
    decreases s.len() - i,
{
    if i + 7 <= s.len() {
        reveal_with_fuel(super::spec::charset_from, 8);
        assert(super::spec::charset_word()[0] == 0x63 && super::spec::charset_word()[1] == 0x68
            && super::spec::charset_word()[2] == 0x61 && super::spec::charset_word()[3] == 0x72
            && super::spec::charset_word()[4] == 0x73 && super::spec::charset_word()[5] == 0x65
            && super::spec::charset_word()[6] == 0x74);
        assert(super::independent_prescan::matches_charset_at(s, i) == super::spec::charset_at(s, i));
        lemma_find_charset(s, i + 1);
    }
}

/// The two whitespace skips agree, and stay within `s`.
proof fn lemma_skip_spaces(s: Seq<u8>, k: nat)
    ensures
        super::independent_prescan::skip_whitespace(s, k) == super::spec::skip_spaces(s, k),
        k <= super::spec::skip_spaces(s, k),
        k <= s.len() ==> super::spec::skip_spaces(s, k) <= s.len(),
        super::spec::skip_spaces(s, k) < s.len() ==> !super::spec::is_space(s[super::spec::skip_spaces(s, k) as int]),
    decreases s.len() - k,
{
    if k < s.len() && super::spec::is_space(s[k as int]) {
        lemma_skip_spaces(s, k + 1);
    }
}

/// The two searches for a byte agree.
proof fn lemma_find_byte(s: Seq<u8>, k: nat, c: u8)
    ensures
        super::independent_prescan::find_byte(s, k, c) == super::spec::find_byte(s, k, c),
    decreases s.len() - k,
{
    if k < s.len() && s[k as int] != c {
        lemma_find_byte(s, k + 1, c);
    }
}

/// The two searches for a value's end agree, and stop at or after `k`.
proof fn lemma_find_value_end(s: Seq<u8>, k: nat)
    ensures
        super::independent_prescan::find_value_end(s, k) == super::spec::find_value_end(s, k),
        k <= super::spec::find_value_end(s, k),
        k <= s.len() ==> super::spec::find_value_end(s, k) <= s.len(),
    decreases s.len() - k,
{
    if !(k >= s.len() || super::spec::is_space(s[k as int]) || s[k as int] == 0x3B) {
        lemma_find_value_end(s, k + 1);
    }
}

/// No label of the table is empty or has a 0x3B (;), so "get an encoding"
/// fails on the empty string and on a string that starts with 0x3B.
proof fn lemma_no_label(t: Seq<u32>)
    requires
        t.len() == 0 || t[0] == 0x3B,
    ensures
        clazel_encoding::labels::spec::get_an_encoding(t) is None,
{
    let st = clazel_encoding::labels::spec::strip_leading_and_trailing_ascii_whitespace(t);
    if t.len() > 0 {
        lemma_skip_trailing_keeps_first(t, t.len());
        assert(clazel_encoding::labels::spec::skip_leading(t, 0) == 0);
        assert(st.len() > 0 && st[0] == 0x3B);
    } else {
        assert(st.len() == 0);
    }
    clazel_encoding::labels::lemmas::lemma_table();
    assert forall|i: int| 0 <= i < clazel_encoding::labels::spec::label_count() implies !clazel_encoding::labels::spec::ascii_case_insensitive_match(
        st,
        #[trigger] clazel_encoding::labels::spec::row_label(i),
    ) by {
        clazel_encoding::labels::lemmas::lemma_row_label(i);
        let row = clazel_encoding::labels::spec::row_label(i);
        let lst = clazel_encoding::labels::spec::ascii_lowercase(st);
        let lrow = clazel_encoding::labels::spec::ascii_lowercase(row);
        if st.len() == 0 {
            assert(lst.len() != lrow.len());
        } else {
            clazel_encoding::labels::lemmas::lemma_row_char(i, 0);
            if lst.len() == lrow.len() {
                assert(lst[0] == 0x3B);
                assert(lrow[0] != 0x3B);
            }
        }
    }
    lemma_first_match_none(st, 0);
}

/// "Strip trailing ASCII whitespace" of a string whose first code point is
/// not whitespace keeps that code point.
proof fn lemma_skip_trailing_keeps_first(t: Seq<u32>, j: nat)
    requires
        1 <= j <= t.len(),
        !clazel_encoding::labels::spec::is_ascii_whitespace(t[0]),
    ensures
        1 <= clazel_encoding::labels::spec::skip_trailing(t, j) <= j,
    decreases j,
{
    if clazel_encoding::labels::spec::is_ascii_whitespace(t[j - 1]) {
        lemma_skip_trailing_keeps_first(t, (j - 1) as nat);
    }
}

/// The label search finds no row when no row from `i` matches.
proof fn lemma_first_match_none(label: Seq<u32>, i: nat)
    requires
        forall|r: int|
            0 <= r < clazel_encoding::labels::spec::label_count() ==> !clazel_encoding::labels::spec::ascii_case_insensitive_match(
                label,
                #[trigger] clazel_encoding::labels::spec::row_label(r),
            ),
    ensures
        clazel_encoding::labels::spec::first_match(label, i) is None,
    decreases clazel_encoding::labels::spec::label_count() - i,
{
    if i < clazel_encoding::labels::spec::label_count() {
        lemma_first_match_none(label, i + 1);
    }
}

/// The extraction algorithm from step 2 at `position`: the two texts agree.
proof fn lemma_extract(s: Seq<u8>, position: nat)
    ensures
        super::independent_prescan::extract_loop(s, position) == extract_from(s, position),
    decreases s.len() - position,
{
    lemma_find_charset(s, position);
    match super::spec::find_charset(s, position) {
        None => {},
        Some(k) => {
            lemma_skip_spaces(s, k + 7);
            let j = super::spec::skip_spaces(s, k + 7);
            if j >= s.len() || s[j as int] != 0x3D {
                lemma_extract(s, j);
            } else {
                lemma_skip_spaces(s, j + 1);
                let v = super::spec::skip_spaces(s, j + 1);
                if v < s.len() {
                    let c = s[v as int];
                    if c == 0x22 || c == 0x27 {
                        lemma_find_byte(s, v + 1, c);
                        match super::spec::find_byte(s, v + 1, c) {
                            Some(m) => lemma_code_points(s.subrange((v + 1) as int, m as int)),
                            None => {},
                        }
                    } else {
                        lemma_find_value_end(s, v + 1);
                        let e = super::spec::find_value_end(s, v + 1);
                        lemma_code_points(s.subrange(v as int, e as int));
                        if c == 0x3B {
                            // "This character" is 0x3B: the spec's substring
                            // is empty, the other's starts with 0x3B.
                            assert(super::spec::find_value_end(s, v) == v);
                            lemma_no_label(super::spec::as_string(s.subrange(v as int, v as int)));
                            lemma_no_label(super::spec::as_string(s.subrange(v as int, e as int)));
                        } else {
                            assert(super::spec::find_value_end(s, v) == e);
                        }
                    }
                }
            }
        },
    }
}

/// The extraction algorithm: the two texts agree.
proof fn lemma_extract_agrees(s: Seq<u8>)
    ensures
        super::independent_prescan::extract_character_encoding_from_meta(s) == super::spec::extract(s),
{
    lemma_extract(s, 0);
}

// ---------------------------------------------------------------------------
// The `<meta` branch and other tags
// ---------------------------------------------------------------------------

/// The spec's `<meta>` steps go on to "next byte" only at a byte of `b` at
/// or after where they started.
proof fn lemma_spec_meta_next(b: Seq<u8>, pos: nat, m: super::spec::Meta)
    ensures
        match super::spec::meta_attributes(b, pos, m) {
            super::spec::MetaResult::NextByte(p) => pos <= p < b.len(),
            _ => true,
        },
    decreases b.len() - pos,
{
    super::lemmas::lemma_attribute_advances(b, pos);
    match super::spec::get_attribute(b, pos) {
        super::spec::Attr::Some(name, value, p) => {
            if pos < p <= b.len() {
                if super::spec::in_list(m.attribute_list, name, 0) {
                    lemma_spec_meta_next(b, p, m);
                } else {
                    let m2 = super::spec::Meta { attribute_list: m.attribute_list.push(name), ..m };
                    lemma_spec_meta_next(b, p, super::spec::meta_attribute(m2, name, value));
                }
            }
        },
        _ => {},
    }
}

/// The `<meta` branch from step 6: the two texts agree.
proof fn lemma_meta(
    b: Seq<u8>,
    pos: nat,
    list: Seq<Seq<u8>>,
    got_pragma: bool,
    need_pragma: Option<bool>,
    charset: Option<Option<clazel_encoding::labels::spec::Encoding>>,
)
    ensures
        meta_result_of(super::independent_prescan::meta_attributes(b, pos, list, got_pragma, need_pragma, charset))
            == super::spec::meta_attributes(
            b,
            pos,
            super::spec::Meta { attribute_list: list, got_pragma, need_pragma, charset: charset_of(charset) },
        ),
    decreases b.len() - pos,
{
    lemma_get_attribute(b, pos);
    super::lemmas::lemma_attribute_advances(b, pos);
    match super::independent_prescan::get_an_attribute(b, pos) {
        super::independent_prescan::GetAttribute::Attribute { name, value, position: p } => {
            lemma_in_list(list, name);
            if super::independent_prescan::in_list(list, name) {
                lemma_meta(b, p, list, got_pragma, need_pragma, charset);
            } else {
                let list2 = list.push(name);
                if name == super::independent_prescan::http_equiv() {
                    assert(super::independent_prescan::http_equiv() == super::spec::http_equiv());
                    assert(super::independent_prescan::content_type() == super::spec::content_type());
                    lemma_meta(b, p, list2, true, need_pragma, charset);
                    lemma_meta(b, p, list2, got_pragma, need_pragma, charset);
                } else {
                    assert(super::independent_prescan::http_equiv() == super::spec::http_equiv());
                    assert(super::independent_prescan::content() == super::spec::content());
                    assert(super::independent_prescan::charset_name() == super::spec::charset_name());
                    assert(super::spec::http_equiv() != super::spec::content()) by {
                        assert(super::spec::http_equiv().len() != super::spec::content().len());
                    }
                    assert(super::spec::http_equiv() != super::spec::charset_name()) by {
                        assert(super::spec::http_equiv().len() != super::spec::charset_name().len());
                    }
                    assert(super::spec::content() != super::spec::charset_name()) by {
                        assert(super::spec::content()[1] != super::spec::charset_name()[1]);
                    }
                    if name == super::independent_prescan::content() {
                        lemma_extract_agrees(value);
                        match super::spec::extract(value) {
                            Some(e) => {
                                lemma_meta(b, p, list2, got_pragma, Some(true), Some(Some(e)));
                            },
                            None => {},
                        }
                        lemma_meta(b, p, list2, got_pragma, need_pragma, charset);
                    } else if name == super::independent_prescan::charset_name() {
                        lemma_code_points(value);
                        lemma_meta(
                            b,
                            p,
                            list2,
                            got_pragma,
                            Some(false),
                            Some(clazel_encoding::labels::spec::get_an_encoding(super::spec::as_string(value))),
                        );
                    } else {
                        lemma_meta(b, p, list2, got_pragma, need_pragma, charset);
                    }
                }
            }
        },
        _ => {},
    }
}

/// The spec's "repeatedly get an attribute" stops at a byte of `b` at or
/// after where it started.
proof fn lemma_spec_skip_attributes(b: Seq<u8>, pos: nat)
    ensures
        match super::spec::skip_attributes(b, pos) {
            Some(p) => pos <= p < b.len(),
            None => true,
        },
    decreases b.len() - pos,
{
    super::lemmas::lemma_attribute_advances(b, pos);
    match super::spec::get_attribute(b, pos) {
        super::spec::Attr::Some(_, _, p) => {
            if pos < p <= b.len() {
                lemma_spec_skip_attributes(b, p);
            }
        },
        _ => {},
    }
}

/// The tag branch's step 2: the two texts agree.
proof fn lemma_tag_attributes(b: Seq<u8>, pos: nat)
    ensures
        super::independent_prescan::tag_attributes(b, pos) == match super::spec::skip_attributes(b, pos) {
            Some(p) => super::independent_prescan::LoopStep::NextByte(p),
            None => super::independent_prescan::LoopStep::OutOfBytes,
        },
    decreases b.len() - pos,
{
    lemma_get_attribute(b, pos);
    super::lemmas::lemma_attribute_advances(b, pos);
    match super::independent_prescan::get_an_attribute(b, pos) {
        super::independent_prescan::GetAttribute::Attribute { name: _, value: _, position: p } => {
            lemma_tag_attributes(b, p);
        },
        _ => {},
    }
}

/// The two searches for a tag's end agree, and find a byte at or after
/// where they started.
proof fn lemma_find_tag_end(b: Seq<u8>, q: nat)
    ensures
        super::independent_prescan::find_tag_end(b, q) == super::spec::find_tag_end(b, q),
        match super::spec::find_tag_end(b, q) {
            Some(p) => q <= p < b.len(),
            None => true,
        },
    decreases b.len() - q,
{
    if q < b.len() && !(super::spec::is_space(b[q as int]) || b[q as int] == 0x3E) {
        lemma_find_tag_end(b, q + 1);
    }
}

/// The two searches for a 0x3E agree.
proof fn lemma_find_gt(b: Seq<u8>, q: nat)
    ensures
        super::independent_prescan::find_gt(b, q) == super::spec::find_gt(b, q),
    decreases b.len() - q,
{
    if q < b.len() && b[q as int] != 0x3E {
        lemma_find_gt(b, q + 1);
    }
}

/// The two searches for a comment's end agree from the third byte on.
proof fn lemma_find_comment_end(b: Seq<u8>, q: nat)
    requires
        q >= 2,
    ensures
        super::independent_prescan::find_comment_end(b, q) == super::spec::find_comment_end(b, q),
    decreases b.len() - q,
{
    if q < b.len() && !(b[q as int] == 0x3E && b[q - 1] == 0x2D && b[q - 2] == 0x2D) {
        lemma_find_comment_end(b, q + 1);
    }
}

// ---------------------------------------------------------------------------
// The prescan
// ---------------------------------------------------------------------------

/// Steps 3 and 4 from `position`: the two texts agree (the other's
/// "out of bytes" is the spec's `None`).
proof fn lemma_loop(b: Seq<u8>, position: nat)
    ensures
        match super::independent_prescan::prescan_loop(b, position) {
            super::independent_prescan::PrescanLoop::OutOfBytes => super::spec::prescan_loop(b, position) is None,
            super::independent_prescan::PrescanLoop::Return(e) => super::spec::prescan_loop(b, position) == Some(e),
        },
    decreases b.len() - position,
{
    if position < b.len() {
        lemma_starts_at_4(b, position, 0x3Cu8, 0x21u8, 0x2Du8, 0x2Du8);
        lemma_starts_at_2(b, position, 0x3Cu8, 0x21u8);
        lemma_starts_at_2(b, position, 0x3Cu8, 0x2Fu8);
        lemma_starts_at_2(b, position, 0x3Cu8, 0x3Fu8);
        if super::independent_prescan::starts_comment(b, position) {
            // The other text searches from the `!`; the bytes `!`, `-`, `-`
            // are not 0x3E, so both search on from the byte after `<!--`.
            assert(super::independent_prescan::find_comment_end(b, position + 1)
                == super::independent_prescan::find_comment_end(b, position + 4)) by {
                assert(b[(position + 1) as int] != 0x3E && b[(position + 2) as int] != 0x3E && b[(position + 3) as int] != 0x3E);
                assert(super::independent_prescan::find_comment_end(b, position + 3)
                    == super::independent_prescan::find_comment_end(b, position + 4));
                assert(super::independent_prescan::find_comment_end(b, position + 2)
                    == super::independent_prescan::find_comment_end(b, position + 3));
            }
            lemma_find_comment_end(b, position + 4);
            super::lemmas::lemma_find_comment_end(b, position + 4);
            match super::spec::find_comment_end(b, position + 4) {
                Some(q) => lemma_loop(b, q + 1),
                None => {},
            }
        } else if super::independent_prescan::starts_meta(b, position) {
            assert(super::spec::starts_meta(b, position));
            assert(Seq::<Seq<u8>>::empty() =~= seq![]);
            let m = super::spec::Meta {
                attribute_list: seq![],
                got_pragma: false,
                need_pragma: None,
                charset: super::spec::Charset::Null,
            };
            lemma_meta(b, position + 5, Seq::empty(), false, None, None);
            lemma_spec_meta_next(b, position + 5, m);
            match super::spec::meta_attributes(b, position + 5, m) {
                super::spec::MetaResult::NextByte(p) => lemma_loop(b, p + 1),
                _ => {},
            }
        } else if super::independent_prescan::starts_tag(b, position) {
            assert(!super::spec::starts_meta(b, position));
            assert(super::spec::starts_tag(b, position));
            // The byte at `position` is 0x3C, not a tag end.
            assert(super::spec::find_tag_end(b, position) == super::spec::find_tag_end(b, position + 1));
            lemma_find_tag_end(b, position + 1);
            match super::spec::find_tag_end(b, position + 1) {
                Some(q) => {
                    lemma_tag_attributes(b, q);
                    lemma_spec_skip_attributes(b, q);
                    match super::spec::skip_attributes(b, q) {
                        Some(p) => lemma_loop(b, p + 1),
                        None => {},
                    }
                },
                None => {},
            }
        } else if super::independent_prescan::starts_markup(b, position) {
            assert(!super::spec::starts_meta(b, position));
            assert(!super::spec::starts_tag(b, position));
            lemma_find_gt(b, position + 1);
            super::lemmas::lemma_find_gt(b, position + 1);
            match super::spec::find_gt(b, position + 1) {
                Some(q) => lemma_loop(b, q + 1),
                None => {},
            }
        } else {
            assert(!super::spec::starts_meta(b, position));
            assert(!super::spec::starts_tag(b, position));
            lemma_loop(b, position + 1);
        }
    }
}

/// The independent transcription of the prescan equals the spec's, on
/// every input.
pub proof fn lemma_prescan_agrees(b: Seq<u8>)
    ensures
        super::independent_prescan::prescan(b) == super::spec::prescan(b),
{
    lemma_starts_at_6(b, 0, 0x3Cu8, 0x00u8, 0x3Fu8, 0x00u8, 0x78u8, 0x00u8);
    lemma_starts_at_6(b, 0, 0x00u8, 0x3Cu8, 0x00u8, 0x3Fu8, 0x00u8, 0x78u8);
    lemma_loop(b, 0);
}

} // verus!
