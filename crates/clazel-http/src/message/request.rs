//! The request parser, RFC 9112 §3 and §2.1, as a spec only: it exists for
//! [`theorem_request_round_trip`], that what [`serialize_request`] writes
//! parses back as the same request. The browser never parses requests.
//!
//! Modelling choices, beyond those of [`super::spec`] (whose line and
//! field-section readers, and limits, this uses):
//! - The version must be exactly `HTTP/1.1`, the only one the serializer
//!   writes; a [`Request`] has no version to carry another.
//! - `request-target` (§3.2) is read as the run of `VCHAR` octets after
//!   the method's SP: §3 "No whitespace is allowed in the three
//!   components", and the forms of §3.2 are all made of `VCHAR`s.
//! - The empty lines §2.2 lets a server ignore before a request-line are
//!   not ignored (the serializer writes none).
//! - Only the head is parsed: the requests the serializer writes have no
//!   body, so §6.3 step 7 is not modelled; what follows the empty line is
//!   returned as the rest.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The length of the longest prefix of `s` made of `VCHAR`s.
pub open spec fn vchar_run_len(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && is_vchar(s[0]) {
        1 + vchar_run_len(s.drop_first())
    } else {
        0
    }
}

/// §3: `request-line = method SP request-target SP HTTP-version`, over
/// the whole of `line`, with `method = token` (§3.1) and `HTTP-version`
/// `HTTP/1.1` (see the modelling choices): the method and the target.
pub open spec fn parse_request_line(line: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    // method = token
    let n = run_len(Class::Tchar, line);
    if n > 0 && line.len() > n && line[n as int] == 0x20 {
        // SP request-target
        let after = line.skip((n + 1) as int);
        let m = vchar_run_len(after);
        // SP HTTP-version
        if m > 0 && after.len() == m + 1 + 8 && after[m as int] == 0x20
            && after.skip((m + 1) as int) == lit_http_1_1()
        {
            Some((line.take(n as int), after.take(m as int)))
        } else {
            None
        }
    } else {
        None
    }
}

/// The result of parsing a request.
pub enum RequestParse {
    /// The request, and what follows its head.
    Done {
        /// the request
        request: Request,
        /// what follows the empty line ending its head
        rest: Seq<u8>,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a request this parser reads.
    Invalid,
}

/// §2.1 `HTTP-message = start-line CRLF *( field-line CRLF ) CRLF`, with
/// `start-line = request-line`, at the start of `input`.
pub open spec fn parse_request(input: Seq<u8>) -> RequestParse {
    match read_line(input) {
        LineRead::Incomplete => RequestParse::Incomplete,
        LineRead::TooLong => RequestParse::Invalid,
        LineRead::Line { line, rest } => match parse_request_line(line) {
            None => RequestParse::Invalid,
            Some((method, target)) => match read_section(rest, seq![], None, 0) {
                SectionRead::Done { fields, rest: after } => RequestParse::Done {
                    request: Request { method: method, target: target, fields: fields },
                    rest: after,
                },
                SectionRead::Incomplete => RequestParse::Incomplete,
                SectionRead::Invalid => RequestParse::Invalid,
            },
        },
    }
}

/// Every field line of `fields`, written `name: value`, fits in
/// [`max_line`].
pub open spec fn field_lines_fit(fields: Seq<FieldLine>) -> bool
    decreases fields.len()
{
    fields.len() == 0 || (fields[0].name.len() + 2 + fields[0].value.len() <= max_line()
        && field_lines_fit(fields.drop_first()))
}

/// `r`, serialized, is within the parser's limits: its request line and
/// every field line fit in [`max_line`], and it has at most [`max_lines`]
/// field lines.
pub open spec fn within_limits(r: Request) -> bool {
    r.method.len() + 1 + r.target.len() + 1 + 8 <= max_line()
        && r.fields.len() <= max_lines()
        && field_lines_fit(r.fields)
}

/// Round trip: a valid request within the limits, serialized, parses back
/// as the same request, whatever follows it.
pub proof fn theorem_request_round_trip(r: Request, more: Seq<u8>)
    requires
        is_valid_request(r),
        within_limits(r),
    ensures
        parse_request(serialize_request(r) + more) == (RequestParse::Done { request: r, rest: more }),
{
    let sp = seq![0x20u8];
    let line = r.method + sp + r.target + sp + lit_http_1_1();
    let fields = serialize_fields(r.fields);
    let after = fields + lit_crlf() + more;
    assert(serialize_request(r) + more =~= line + lit_crlf() + after);
    // The request line has no CR, and fits.
    lemma_tchar_no_cr(r.method);
    lemma_vchar_no_cr(r.target);
    assert(no_cr(line)) by {
        assert forall|k: int| 0 <= k < line.len() implies #[trigger] line[k] != 0x0D by {
            if k < r.method.len() {
            } else if k < r.method.len() + 1 {
            } else if k < r.method.len() + 1 + r.target.len() {
                assert(line[k] == r.target[k - r.method.len() - 1]);
            } else {
            }
        }
    }
    lemma_read_line_of(line, after);
    // method SP
    let n = r.method.len();
    lemma_run_len_concat(Class::Tchar, r.method, sp + r.target + sp + lit_http_1_1());
    assert(line =~= r.method + (sp + r.target + sp + lit_http_1_1()));
    assert(run_len(Class::Tchar, sp + r.target + sp + lit_http_1_1()) == 0);
    assert(line[n as int] == 0x20);
    assert(line.take(n as int) =~= r.method);
    // request-target SP HTTP-version
    let rest_of_line = line.skip((n + 1) as int);
    assert(rest_of_line =~= r.target + (sp + lit_http_1_1()));
    lemma_vchar_run_concat(r.target, sp + lit_http_1_1());
    assert(vchar_run_len(sp + lit_http_1_1()) == 0);
    let m = r.target.len();
    assert(rest_of_line[m as int] == 0x20);
    assert(rest_of_line.skip((m + 1) as int) =~= lit_http_1_1());
    assert(rest_of_line.take(m as int) =~= r.target);
    assert(parse_request_line(line) == Some((r.method, r.target)));
    // The field section.
    lemma_section_of(r.fields, more, seq![], None, 0);
    assert(Seq::<FieldLine>::empty() + r.fields =~= r.fields);
}

/// No CR in `s`.
pub open spec fn no_cr(s: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] != 0x0D
}

/// A token has no CR.
pub proof fn lemma_tchar_no_cr(s: Seq<u8>)
    requires
        all_in(s, Class::Tchar),
    ensures
        no_cr(s),
{
    crate::field::lemmas::lemma_all_in_index(s, Class::Tchar);
    assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != 0x0D by {
        assert(in_class(Class::Tchar, s[k]));
    }
}

/// Field content has no CR.
pub proof fn lemma_field_content_no_cr(s: Seq<u8>)
    requires
        all_in(s, Class::FieldContent),
    ensures
        no_cr(s),
{
    crate::field::lemmas::lemma_all_in_index(s, Class::FieldContent);
    assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != 0x0D by {
        assert(in_class(Class::FieldContent, s[k]));
    }
}

/// `VCHAR`s are not CR.
pub proof fn lemma_vchar_no_cr(s: Seq<u8>)
    requires
        all_vchar(s),
    ensures
        no_cr(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_vchar_no_cr(s.drop_first());
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] != 0x0D by {
            if k > 0 {
                assert(s[k] == s.drop_first()[k - 1]);
            }
        }
    }
}

/// The run of a class over `a + b`, `a` all in it.
pub proof fn lemma_run_len_concat(class: Class, a: Seq<u8>, b: Seq<u8>)
    requires
        all_in(a, class),
    ensures
        run_len(class, a + b) == a.len() + run_len(class, b),
    decreases a.len()
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_run_len_concat(class, a.drop_first(), b);
    }
}

/// The `VCHAR` run over `a + b`, `a` all `VCHAR`s.
pub proof fn lemma_vchar_run_concat(a: Seq<u8>, b: Seq<u8>)
    requires
        all_vchar(a),
    ensures
        vchar_run_len(a + b) == a.len() + vchar_run_len(b),
    decreases a.len()
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_vchar_run_concat(a.drop_first(), b);
    }
}

/// The first CRLF in `line` CRLF `rest`, searching from `i`, is the one
/// after `line`, when `line` has no CR.
pub proof fn lemma_find_crlf_line(line: Seq<u8>, rest: Seq<u8>, i: nat)
    requires
        no_cr(line),
        i <= line.len(),
    ensures
        find_crlf_from(line + lit_crlf() + rest, i) == Some(line.len()),
    decreases line.len() - i
{
    let s = line + lit_crlf() + rest;
    if i < line.len() {
        assert(s[i as int] == line[i as int]);
        lemma_find_crlf_line(line, rest, i + 1);
    } else {
        assert(s[i as int] == 0x0D);
        assert(s[(i + 1) as int] == 0x0A);
    }
}

/// Reading a line from `line` CRLF `rest`, `line` without CR and within
/// the limit.
pub proof fn lemma_read_line_of(line: Seq<u8>, rest: Seq<u8>)
    requires
        no_cr(line),
        line.len() <= max_line(),
    ensures
        read_line(line + lit_crlf() + rest) == (LineRead::Line { line: line, rest: rest }),
{
    lemma_find_crlf_line(line, rest, 0);
    let s = line + lit_crlf() + rest;
    assert(s.take(line.len() as int) =~= line);
    assert(s.skip((line.len() + 2) as int) =~= rest);
}

/// A field value, after one SP, is read back unchanged.
pub proof fn lemma_finish_written(name: Seq<u8>, value: Seq<u8>)
    requires
        is_field_value(value),
    ensures
        finish_field_line(FieldLine { name: name, value: seq![0x20u8] + value }) == Some(FieldLine { name: name, value: value }),
{
    crate::field::lemmas::lemma_strip_ows_leading_sp(value);
    crate::field::lemmas::lemma_strip_ows_of_trimmed(value);
}

/// The field section the serializer writes, with the empty line after it,
/// reads back as its field lines, after the finished lines `acc` and the
/// pending one.
pub proof fn lemma_section_of(fields: Seq<FieldLine>, more: Seq<u8>, acc: Seq<FieldLine>, pending: Option<FieldLine>, count: nat)
    requires
        all_valid_fields(fields),
        field_lines_fit(fields),
        count + fields.len() <= max_lines(),
        flush_pending(acc, pending) is Some,
    ensures
        read_section(serialize_fields(fields) + lit_crlf() + more, acc, pending, count)
            == (SectionRead::Done { fields: flush_pending(acc, pending)->Some_0 + fields, rest: more }),
    decreases fields.len()
{
    if fields.len() == 0 {
        assert(serialize_fields(fields) + lit_crlf() + more =~= Seq::<u8>::empty() + lit_crlf() + more);
        assert(no_cr(Seq::<u8>::empty()));
        lemma_read_line_of(Seq::<u8>::empty(), more);
        assert(flush_pending(acc, pending)->Some_0 + fields =~= flush_pending(acc, pending)->Some_0);
    } else {
        let f = fields[0];
        let tail = fields.drop_first();
        let line = f.name + seq![0x3Au8, 0x20u8] + f.value;
        let after = serialize_fields(tail) + lit_crlf() + more;
        assert(serialize_fields(fields) + lit_crlf() + more =~= line + lit_crlf() + after);
        // The line has no CR, and fits.
        lemma_tchar_no_cr(f.name);
        lemma_field_content_no_cr(f.value);
        assert(no_cr(line)) by {
            assert forall|k: int| 0 <= k < line.len() implies #[trigger] line[k] != 0x0D by {
                if k >= f.name.len() + 2 {
                    assert(line[k] == f.value[k - f.name.len() - 2]);
                }
            }
        }
        lemma_read_line_of(line, after);
        // It is not a continuation line, and starts a field line.
        assert(line[0] == f.name[0]);
        crate::field::lemmas::lemma_all_in_index(f.name, Class::Tchar);
        assert(in_class(Class::Tchar, f.name[0]));
        lemma_run_len_concat(Class::Tchar, f.name, seq![0x3Au8, 0x20u8] + f.value);
        assert(line =~= f.name + (seq![0x3Au8, 0x20u8] + f.value));
        assert(run_len(Class::Tchar, seq![0x3Au8, 0x20u8] + f.value) == 0);
        let n = f.name.len();
        assert(line[n as int] == 0x3A);
        assert(line.take(n as int) =~= f.name);
        assert(line.skip((n + 1) as int) =~= seq![0x20u8] + f.value);
        let raw = FieldLine { name: f.name, value: seq![0x20u8] + f.value };
        assert(parse_field_line_start(line) == Some(raw));
        let acc2 = flush_pending(acc, pending)->Some_0;
        lemma_finish_written(f.name, f.value);
        assert(flush_pending(acc2, Some(raw)) == Some(acc2.push(f)));
        lemma_section_of(tail, more, acc2, Some(raw), count + 1);
        assert(acc2.push(f) + tail =~= acc2 + fields);
    }
}

} // verus!
