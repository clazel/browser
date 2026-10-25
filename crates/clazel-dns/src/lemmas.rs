//! Facts proven about the spec itself ([`super::spec`]). They are evidence
//! that the transcription is right, not part of what the implementation
//! must meet. The ones that matter:
//!
//! - [`lemma_decode_encode_query`]: decoding a query that [`encode_query`]
//!   built gives the query back;
//! - [`lemma_decode_message_names`]: every name of a decoded message has at
//!   most 255 octets and labels of at most 63;
//! - [`lemma_answer_addresses_in_answers`]: [`answer_addresses`] returns
//!   only addresses of records of the answer section;
//! - [`lemma_decode_alloc_bound`]: a decoded message never holds more
//!   records than the input has octets.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Network byte order.
// ---------------------------------------------------------------------------

/// 256 to the power `n`: the number of values `n` octets can hold.
pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        256 * pow256((n - 1) as nat)
    }
}

/// `n` octets spell a number below 256^n.
pub proof fn lemma_be_value_bound(s: Seq<u8>)
    ensures
        be_value(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_be_value_bound(s.drop_last());
        assert(be_value(s) == be_value(s.drop_last()) * 256 + s.last() as nat);
        assert(pow256(s.len()) == 256 * pow256((s.len() - 1) as nat));
    }
}

/// Sixteen octets hold exactly the values of a `u128`.
pub proof fn lemma_pow256_16()
    ensures
        pow256(16) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000,
{
    assert(pow256(16) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000) by (compute_only);
}

/// Up to sixteen octets fit in a `u128`.
pub proof fn lemma_pow256_up_to_16(n: nat)
    requires
        n <= 16,
    ensures
        pow256(n) <= 0x1_0000_0000_0000_0000_0000_0000_0000_0000,
    decreases 16 - n,
{
    if n < 16 {
        lemma_pow256_up_to_16(n + 1);
        assert(pow256(n + 1) == 256 * pow256(n));
        assert(pow256(n) >= 1) by {
            lemma_pow256_positive(n);
        }
    } else {
        lemma_pow256_16();
    }
}

/// 256^n is at least 1.
pub proof fn lemma_pow256_positive(n: nat)
    ensures
        pow256(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow256_positive((n - 1) as nat);
    }
}

// ---------------------------------------------------------------------------
// Names: what a decoded name looks like.
// ---------------------------------------------------------------------------

/// Appending a sequence of labels to one keeps it a sequence of labels.
pub proof fn lemma_is_labels_append(a: Seq<u8>, c: Seq<u8>)
    requires
        is_labels(a),
        is_labels(c),
    ensures
        is_labels(a + c),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
    } else {
        let l = 1 + a[0] as int;
        assert((a + c)[0] == a[0]);
        assert((a + c).skip(l) =~= a.skip(l) + c);
        lemma_is_labels_append(a.skip(l), c);
    }
}

/// One label (a length octet from 1 to 63, then that many octets) is a
/// sequence of labels.
pub proof fn lemma_one_label(s: Seq<u8>)
    requires
        1 <= s.len(),
        1 <= s[0] <= 63,
        s.len() == 1 + s[0] as nat,
    ensures
        is_labels(s),
{
    assert(s.skip(1 + s[0] as int) =~= Seq::<u8>::empty());
    assert(is_labels(Seq::<u8>::empty()));
    assert(s.len() >= 1 + s[0] as nat);
    assert(is_labels(s.skip(1 + s[0] as int)));
}

/// Reading a name never ends before it starts, ends within `limit`, and,
/// once a pointer has been followed, ends where that pointer ended.
pub proof fn lemma_read_name_end(b: Seq<u8>, pos: nat, limit: nat, acc: Seq<u8>, end: Option<nat>)
    ensures
        match read_name(b, pos, limit, acc, end) {
            Some((w, e)) => (match end {
                Some(e0) => e == e0,
                None => pos < e && e <= limit && limit <= b.len(),
            }) && w.len() > acc.len(),
            None => true,
        },
    decreases limit, limit - pos,
{
    if pos >= limit || limit > b.len() {
    } else {
        let len = b[pos as int];
        if len == 0 {
        } else if len < 64 {
            if pos + 1 + len as nat > limit || acc.len() + 1 + len as nat > 254 {
            } else {
                lemma_read_name_end(b, pos + 1 + len as nat, limit, acc + b.subrange(pos as int, pos as int + 1 + len as int), end);
            }
        } else if len >= 192 {
            if pos + 2 > limit {
            } else {
                let target: nat = ((len as nat - 192) * 256 + b[pos as int + 1] as nat) as nat;
                if target >= pos {
                } else {
                    let end2 = Some(match end {
                        Some(e) => e,
                        None => pos + 2,
                    });
                    lemma_read_name_end(b, target, pos, acc, end2);
                }
            }
        }
    }
}

/// What a name read keeps: the name read is a sequence of labels once the
/// zero octet is dropped, if `acc` was, and short enough: so every decoded
/// name is a wire name (labels of 1 to 63 octets, 255 octets in all).
pub proof fn lemma_read_name_wire(b: Seq<u8>, pos: nat, limit: nat, acc: Seq<u8>, end: Option<nat>)
    requires
        is_labels(acc),
        acc.len() <= 254,
    ensures
        match read_name(b, pos, limit, acc, end) {
            Some((w, e)) => is_wire_name(w),
            None => true,
        },
    decreases limit, limit - pos,
{
    if pos >= limit || limit > b.len() {
    } else {
        let len = b[pos as int];
        if len == 0 {
            assert(acc.push(0).drop_last() =~= acc);
        } else if len < 64 {
            if pos + 1 + len as nat > limit || acc.len() + 1 + len as nat > 254 {
            } else {
                let piece = b.subrange(pos as int, pos as int + 1 + len as int);
                lemma_one_label(piece);
                lemma_is_labels_append(acc, piece);
                lemma_read_name_wire(b, pos + 1 + len as nat, limit, acc + piece, end);
            }
        } else if len >= 192 {
            if pos + 2 > limit {
            } else {
                let target: nat = ((len as nat - 192) * 256 + b[pos as int + 1] as nat) as nat;
                if target >= pos {
                } else {
                    let end2 = Some(match end {
                        Some(e) => e,
                        None => pos + 2,
                    });
                    lemma_read_name_wire(b, target, pos, acc, end2);
                }
            }
        }
    }
}

/// A decoded name has at most 255 octets and its labels at most 63
/// (§2.3.4).
pub proof fn lemma_decode_name_wire(b: Seq<u8>, pos: nat)
    ensures
        match decode_name(b, pos) {
            Some((w, e)) => is_wire_name(w),
            None => true,
        },
{
    lemma_read_name_wire(b, pos, b.len(), seq![], None);
}

// ---------------------------------------------------------------------------
// Records: how far a question or a record reaches.
// ---------------------------------------------------------------------------

/// A question takes at least five octets (a name of one octet, QTYPE and
/// QCLASS) and ends within the message.
pub proof fn lemma_read_question_progress(b: Seq<u8>, pos: nat)
    ensures
        match read_question(b, pos) {
            Some((q, e)) => e >= pos + 5 && e <= b.len() && is_wire_name(q.name),
            None => true,
        },
{
    lemma_read_name_end(b, pos, b.len(), seq![], None);
    lemma_decode_name_wire(b, pos);
}

/// The names in a record's RDATA are wire names, too.
pub proof fn lemma_decode_rdata_names(b: Seq<u8>, rtype: u16, rclass: u16, rstart: nat, rend: nat)
    ensures
        match decode_rdata(b, rtype, rclass, rstart, rend) {
            Some(Rdata::Cname(t)) => is_wire_name(t),
            _ => true,
        },
{
    lemma_read_name_wire(b, rstart, rend, seq![], None);
}

/// Every name of a record is a wire name: its owner, and the target of a
/// CNAME.
pub open spec fn rr_names_ok(r: Rr) -> bool {
    is_wire_name(r.name) && match r.rdata {
        Rdata::Cname(t) => is_wire_name(t),
        _ => true,
    }
}

/// A record takes at least eleven octets (a name of one octet and the ten
/// fixed octets) and ends within the message.
pub proof fn lemma_read_rr_progress(b: Seq<u8>, pos: nat)
    ensures
        match read_rr(b, pos) {
            Some((r, e)) => e >= pos + 11 && e <= b.len() && rr_names_ok(r),
            None => true,
        },
{
    lemma_read_name_end(b, pos, b.len(), seq![], None);
    lemma_decode_name_wire(b, pos);
    if let Some((name, p)) = decode_name(b, pos) {
        if p + 10 <= b.len() {
            let rdlength = u16_at(b, p + 8);
            let rstart = p + 10;
            let rend = rstart + rdlength;
            if rend <= b.len() {
                lemma_decode_rdata_names(b, u16_at(b, p) as u16, u16_at(b, p + 2) as u16, rstart, rend);
            }
        }
    }
}

/// `n` questions: all of them are read, each takes five octets, they end
/// within the message when there is one, and their names are wire names if
/// the ones before were.
pub proof fn lemma_read_questions(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Question>)
    requires
        forall|i: int| 0 <= i < acc.len() ==> is_wire_name(#[trigger] acc[i].name),
    ensures
        match read_questions(b, pos, n, acc) {
            Some((r, e)) => r.len() == acc.len() + n && e >= pos + 5 * n && (n > 0 ==> e <= b.len()) && forall|i: int|
                0 <= i < r.len() ==> is_wire_name(#[trigger] r[i].name),
            None => true,
        },
    decreases n,
{
    if n > 0 {
        lemma_read_question_progress(b, pos);
        if let Some((q, e)) = read_question(b, pos) {
            let acc2 = acc.push(q);
            assert forall|i: int| 0 <= i < acc2.len() implies is_wire_name(#[trigger] acc2[i].name) by {
                if i < acc.len() {
                    assert(acc2[i] == acc[i]);
                }
            }
            lemma_read_questions(b, e, (n - 1) as nat, acc2);
        }
    }
}

/// `n` records: all of them are read, each takes eleven octets, they end
/// within the message when there is one, and their names are wire names if
/// the ones before were.
pub proof fn lemma_read_rrs(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Rr>)
    requires
        forall|i: int| 0 <= i < acc.len() ==> rr_names_ok(#[trigger] acc[i]),
    ensures
        match read_rrs(b, pos, n, acc) {
            Some((r, e)) => r.len() == acc.len() + n && e >= pos + 11 * n && (n > 0 ==> e <= b.len()) && forall|i: int|
                0 <= i < r.len() ==> rr_names_ok(#[trigger] r[i]),
            None => true,
        },
    decreases n,
{
    if n > 0 {
        lemma_read_rr_progress(b, pos);
        if let Some((r1, e)) = read_rr(b, pos) {
            let acc2 = acc.push(r1);
            assert forall|i: int| 0 <= i < acc2.len() implies rr_names_ok(#[trigger] acc2[i]) by {
                if i < acc.len() {
                    assert(acc2[i] == acc[i]);
                }
            }
            lemma_read_rrs(b, e, (n - 1) as nat, acc2);
        }
    }
}

/// A decoded message holds as many questions and records as its header
/// says, and every name in it is a wire name (§2.3.4: at most 255 octets,
/// labels of at most 63).
pub proof fn lemma_decode_message_names(b: Seq<u8>)
    ensures
        match decode_message(b) {
            Some(m) => m.questions.len() == m.header.qdcount as nat && m.answers.len() == m.header.ancount as nat
                && m.authority.len() == m.header.nscount as nat && m.additional.len() == m.header.arcount as nat
                && (forall|i: int| 0 <= i < m.questions.len() ==> is_wire_name(#[trigger] m.questions[i].name))
                && (forall|i: int| 0 <= i < m.answers.len() ==> rr_names_ok(#[trigger] m.answers[i]))
                && (forall|i: int| 0 <= i < m.authority.len() ==> rr_names_ok(#[trigger] m.authority[i]))
                && (forall|i: int| 0 <= i < m.additional.len() ==> rr_names_ok(#[trigger] m.additional[i])),
            None => true,
        },
{
    if let Some(h) = decode_header(b) {
        if b.len() <= MAX_TCP {
            lemma_read_questions(b, 12, h.qdcount as nat, seq![]);
            if let Some((qs, p1)) = read_questions(b, 12, h.qdcount as nat, seq![]) {
                lemma_read_rrs(b, p1, h.ancount as nat, seq![]);
                if let Some((an, p2)) = read_rrs(b, p1, h.ancount as nat, seq![]) {
                    lemma_read_rrs(b, p2, h.nscount as nat, seq![]);
                    if let Some((ns, p3)) = read_rrs(b, p2, h.nscount as nat, seq![]) {
                        lemma_read_rrs(b, p3, h.arcount as nat, seq![]);
                    }
                }
            }
        }
    }
}

/// A decoded message never holds more records (questions included) than the
/// input has octets, so a decoder that pushes only what it has read never
/// reserves more than the input is long, whatever the header's counts say.
pub proof fn lemma_decode_alloc_bound(b: Seq<u8>)
    ensures
        match decode_message(b) {
            Some(m) => m.questions.len() + m.answers.len() + m.authority.len() + m.additional.len() <= b.len(),
            None => true,
        },
{
    if let Some(h) = decode_header(b) {
        if b.len() <= MAX_TCP {
            lemma_read_questions(b, 12, h.qdcount as nat, seq![]);
            if let Some((qs, p1)) = read_questions(b, 12, h.qdcount as nat, seq![]) {
                lemma_read_rrs(b, p1, h.ancount as nat, seq![]);
                if let Some((an, p2)) = read_rrs(b, p1, h.ancount as nat, seq![]) {
                    lemma_read_rrs(b, p2, h.nscount as nat, seq![]);
                    if let Some((ns, p3)) = read_rrs(b, p2, h.nscount as nat, seq![]) {
                        lemma_read_rrs(b, p3, h.arcount as nat, seq![]);
                        if let Some((ad, p4)) = read_rrs(b, p3, h.arcount as nat, seq![]) {
                            // 5 per question and 11 per record, and the
                            // message ends at p4.
                            assert(p1 >= 12 + 5 * h.qdcount as nat);
                            assert(qs.len() <= 5 * h.qdcount as nat);
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Building a query, and decoding it again.
// ---------------------------------------------------------------------------

/// The labels `dotted_scan` produces are labels (1 to 63 octets each).
pub proof fn lemma_dotted_scan_labels(s: Seq<u8>, i: nat, start: nat, acc: Seq<u8>)
    requires
        is_labels(acc),
        start <= i <= s.len(),
    ensures
        match dotted_scan(s, i, start, acc) {
            Some(w) => is_labels(w) && w.len() >= acc.len(),
            None => true,
        },
    decreases s.len() - i,
{
    if i >= s.len() {
        if i > start && i - start <= MAX_LABEL as nat {
            let piece = seq![(i - start) as u8] + s.subrange(start as int, i as int);
            assert(piece.len() == 1 + (i - start));
            assert(piece[0] == (i - start) as u8);
            lemma_one_label(piece);
            lemma_is_labels_append(acc, piece);
            assert(acc + seq![(i - start) as u8] + s.subrange(start as int, i as int) =~= acc + piece);
        }
    } else if s[i as int] == 46 {
        if i != start && i - start <= MAX_LABEL as nat {
            let piece = seq![(i - start) as u8] + s.subrange(start as int, i as int);
            assert(piece.len() == 1 + (i - start));
            assert(piece[0] == (i - start) as u8);
            lemma_one_label(piece);
            lemma_is_labels_append(acc, piece);
            assert(acc + seq![(i - start) as u8] + s.subrange(start as int, i as int) =~= acc + piece);
            lemma_dotted_scan_labels(s, i + 1, i + 1, acc + piece);
        }
    } else if s[i as int] < 128 {
        lemma_dotted_scan_labels(s, i + 1, start, acc);
    }
}

/// A query name that converts is a wire name: at most 255 octets, labels of
/// at most 63.
pub proof fn lemma_dotted_to_wire_valid(s: Seq<u8>)
    ensures
        match dotted_to_wire(s) {
            Some(w) => is_wire_name(w),
            None => true,
        },
{
    if s.len() == 0 {
    } else if s == seq![46u8] {
        assert(seq![0u8].drop_last() =~= Seq::<u8>::empty());
        assert(is_labels(Seq::<u8>::empty()));
    } else {
        lemma_dotted_scan_labels(s, 0, 0, seq![]);
        if let Some(w) = dotted_scan(s, 0, 0, seq![]) {
            if w.len() + 1 <= MAX_NAME as nat {
                assert((w + seq![0u8]).drop_last() =~= w);
            }
        }
    }
}

/// A label of [`dotted_run`]: each of its octets is not a dot and is ASCII.
pub proof fn lemma_dotted_run_plain(s: Seq<u8>, i: nat)
    requires
        dotted_run(s, i),
    ensures
        forall|m: int| i <= m < s.len() ==> (#[trigger] s[m]) != 46 && s[m] < 128,
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_dotted_run_plain(s, i + 1);
    }
}

/// `dotted_scan` passes over the octets from `i` to `j` of a label (no dot,
/// ASCII) without changing anything but its position.
pub proof fn lemma_dotted_scan_skip(s: Seq<u8>, i: nat, j: nat, start: nat, acc: Seq<u8>)
    requires
        start <= i <= j <= s.len(),
        forall|m: int| i <= m < j ==> (#[trigger] s[m]) != 46 && s[m] < 128,
    ensures
        dotted_scan(s, i, start, acc) == dotted_scan(s, j, start, acc),
    decreases j - i,
{
    if i < j {
        assert(s[i as int] != 46 && s[i as int] < 128);
        lemma_dotted_scan_skip(s, i + 1, j, start, acc);
    }
}

/// Scanning `b` after the prefix `a`, from a label start in `b`, is
/// scanning `b` alone.
pub proof fn lemma_dotted_scan_shift(a: Seq<u8>, b: Seq<u8>, j: nat, k: nat, acc: Seq<u8>)
    requires
        k <= j <= b.len(),
    ensures
        dotted_scan(a + b, a.len() + j, a.len() + k, acc) == dotted_scan(b, j, k, acc),
    decreases b.len() - j,
{
    let s = a + b;
    if j < b.len() {
        assert(s[(a.len() + j) as int] == b[j as int]);
        if b[j as int] == 46 {
            if j != k && j - k <= MAX_LABEL as nat {
                assert(s.subrange((a.len() + k) as int, (a.len() + j) as int) =~= b.subrange(k as int, j as int));
                lemma_dotted_scan_shift(a, b, j + 1, j + 1, acc + seq![(j - k) as u8] + b.subrange(k as int, j as int));
            }
        } else if b[j as int] < 128 {
            lemma_dotted_scan_shift(a, b, j + 1, k, acc);
        }
    } else {
        assert(s.subrange((a.len() + k) as int, (a.len() + j) as int) =~= b.subrange(k as int, j as int));
    }
}

/// Joining is associative when the middle part is not empty: the loop of
/// `wire_to_dotted` adds a label at a time to the front, while `wire_scan`
/// adds it to the rest.
pub proof fn lemma_join_dotted_assoc(a: Seq<u8>, l: Seq<u8>, r: Seq<u8>)
    requires
        l.len() > 0,
    ensures
        join_dotted(a, join_dotted(l, r)) == join_dotted(join_dotted(a, l), r),
{
    if r.len() == 0 {
        assert(join_dotted(l, r) == l);
        assert(join_dotted(join_dotted(a, l), r) == join_dotted(a, l));
    } else if a.len() == 0 {
        assert(join_dotted(a, l) == l);
    } else {
        assert(join_dotted(l, r) == l + seq![46u8] + r);
        assert(join_dotted(a, l) == a + seq![46u8] + l);
        assert(a + seq![46u8] + (l + seq![46u8] + r) =~= a + seq![46u8] + l + seq![46u8] + r);
    }
}

/// The dotted name of a wire name is scanned back to the wire name's
/// labels: if the labels of `w` from `pos` read as the dotted string `d`,
/// then `dotted_scan` of `d` gives those labels, after whatever was
/// accumulated. Also: `w` ends with the zero octet.
pub proof fn lemma_wire_scan_inverts(w: Seq<u8>, pos: nat, acc: Seq<u8>)
    requires
        wire_scan(w, pos) is Some,
    ensures
        pos < w.len(),
        w[w.len() - 1] == 0,
        dotted_scan(wire_scan(w, pos).unwrap(), 0, 0, acc) == Some(acc + w.subrange(pos as int, w.len() - 1)),
    decreases w.len() - pos,
{
    let d = wire_scan(w, pos).unwrap();
    if w[pos as int] == 0 {
        assert(pos + 1 == w.len());
        assert(d =~= Seq::<u8>::empty());
        assert(w.subrange(pos as int, w.len() - 1) =~= Seq::<u8>::empty());
        assert(acc + Seq::<u8>::empty() =~= acc);
    } else {
        let l = w[pos as int] as nat;
        let pos2 = pos + 1 + l;
        let label = w.subrange(pos as int + 1, pos2 as int);
        let rest = wire_scan(w, pos2).unwrap();
        let acc2 = acc + seq![l as u8] + label;
        lemma_wire_scan_inverts(w, pos2, acc2);
        assert(label.len() == l);
        lemma_dotted_run_plain(label, 0);
        assert(w.subrange(pos as int, w.len() - 1) =~= seq![l as u8] + label + w.subrange(pos2 as int, w.len() - 1));
        assert(acc + (seq![l as u8] + label + w.subrange(pos2 as int, w.len() - 1)) =~= acc2 + w.subrange(pos2 as int, w.len() - 1));
        if rest.len() == 0 {
            assert(d =~= label);
            // The scan of the label alone ends at its end.
            lemma_dotted_scan_skip(d, 0, l, 0, acc);
            assert(d.subrange(0, l as int) =~= label);
            // The root label: nothing is left between `pos2` and the zero octet.
            assert(dotted_scan(rest, 0, 0, acc2) == Some(acc2));
            assert(w.subrange(pos2 as int, w.len() - 1).len() == 0);
            assert(acc2 + w.subrange(pos2 as int, w.len() - 1) =~= acc2);
        } else {
            assert(d =~= (label + seq![46u8]) + rest);
            assert forall|m: int| 0 <= m < label.len() implies (#[trigger] d[m]) != 46 && d[m] < 128 by {
                assert(d[m] == label[m]);
            }
            lemma_dotted_scan_skip(d, 0, l, 0, acc);
            assert(d[l as int] == 46);
            assert(d.subrange(0, l as int) =~= label);
            lemma_dotted_scan_shift(label + seq![46u8], rest, 0, 0, acc2);
        }
    }
}

/// A name that [`wire_to_dotted`] spells converts back: [`dotted_to_wire`]
/// of the dotted string is the wire name. (This is the check the network
/// shell used to make at run time.)
pub proof fn lemma_wire_to_dotted_round_trip(w: Seq<u8>)
    requires
        wire_to_dotted(w) is Some,
    ensures
        dotted_to_wire(wire_to_dotted(w).unwrap()) == Some(w),
{
    let d = wire_to_dotted(w).unwrap();
    lemma_wire_scan_inverts(w, 0, seq![]);
    assert(seq![] + w.subrange(0, w.len() - 1) =~= w.drop_last());
    assert(d.len() > 0);
    if d == seq![46u8] {
        // A lone dot is not a scan result: the scan refuses an empty label.
        assert(dotted_scan(d, 0, 0, seq![]) is None);
    }
    assert(d != seq![46u8]);
    assert(w.drop_last() + seq![0u8] =~= w);
}

/// A wire name that is not the root has its first label, and then a wire
/// name.
pub proof fn lemma_wire_name_tail(w: Seq<u8>)
    requires
        is_wire_name(w),
    ensures
        w[0] == 0 ==> w.len() == 1,
        w[0] != 0 ==> (1 <= w[0] <= 63 && w.len() >= 2 + w[0] as nat && is_wire_name(w.skip(1 + w[0] as int))),
{
    let d = w.drop_last();
    if w.len() >= 2 {
        assert(d[0] == w[0]);
        if w[0] != 0 {
            assert(is_labels(d.skip(1 + d[0] as int)));
            let rest = w.skip(1 + w[0] as int);
            assert(rest.drop_last() =~= d.skip(1 + d[0] as int));
            assert(rest.last() == w.last());
        }
    }
}

/// Reading a wire name that lies in the message ending at or before
/// `limit` gives that name, appended to `acc`, and ends after it.
pub proof fn lemma_read_name_of_wire(b: Seq<u8>, pos: nat, limit: nat, acc: Seq<u8>, w: Seq<u8>)
    requires
        is_wire_name(w),
        acc.len() + w.len() <= 255,
        pos + w.len() <= limit,
        limit <= b.len(),
        b.subrange(pos as int, pos as int + w.len() as int) == w,
    ensures
        read_name(b, pos, limit, acc, None) == Some((acc + w, pos + w.len())),
    decreases w.len(),
{
    lemma_wire_name_tail(w);
    assert(b[pos as int] == w[0]);
    if w[0] == 0 {
        assert(w =~= seq![0u8]);
        assert(acc.push(0) =~= acc + w);
    } else {
        let l = w[0] as nat;
        let piece = w.subrange(0, 1 + l as int);
        let rest = w.skip(1 + l as int);
        assert(piece + rest =~= w);
        assert(b.subrange(pos as int, pos as int + 1 + l as int) =~= piece);
        assert(b.subrange(pos as int + 1 + l as int, pos as int + w.len() as int) =~= rest);
        lemma_read_name_of_wire(b, pos + 1 + l, limit, acc + piece, rest);
        assert(acc + piece + rest =~= acc + w);
    }
}

/// The message a query decodes to: the header of a standard query, one
/// question and no records.
pub open spec fn query_message(id: u16, qname: Seq<u8>, qtype: u16) -> Message {
    Message {
        header: query_header(id),
        questions: seq![Question { name: qname, qtype, qclass: CLASS_IN }],
        answers: seq![],
        authority: seq![],
        additional: seq![],
    }
}

/// The octets of an encoded query, by position.
pub proof fn lemma_query_bytes(id: u16, w: Seq<u8>, qtype: u16)
    requires
        is_wire_name(w),
    ensures
        ({
            let b = query_header_bytes(id) + w + be16(qtype as nat) + be16(CLASS_IN as nat);
            &&& b.len() == 16 + w.len()
            &&& b.subrange(12, 12 + w.len() as int) == w
            &&& u16_at(b, 0) == id as nat
            &&& u16_at(b, 2) == 256
            &&& u16_at(b, 4) == 1
            &&& u16_at(b, 6) == 0
            &&& u16_at(b, 8) == 0
            &&& u16_at(b, 10) == 0
            &&& u16_at(b, 12 + w.len()) == qtype as nat
            &&& u16_at(b, 14 + w.len()) == 1
        }),
{
    let h = query_header_bytes(id);
    let b = h + w + be16(qtype as nat) + be16(CLASS_IN as nat);
    assert(h.len() == 12);
    assert(h[0] == (id as nat / 256 % 256) as u8);
    assert(h[1] == (id as nat % 256) as u8);
    assert(h[2] == 1u8 && h[3] == 0u8 && h[4] == 0u8 && h[5] == 1u8);
    assert(h[6] == 0u8 && h[7] == 0u8 && h[8] == 0u8 && h[9] == 0u8 && h[10] == 0u8 && h[11] == 0u8);
    assert(b.subrange(12, 12 + w.len() as int) =~= w);
    assert(b[0] == h[0] && b[1] == h[1]);
    assert(b[12 + w.len() as int] == (qtype as nat / 256 % 256) as u8);
    assert(b[13 + w.len() as int] == (qtype as nat % 256) as u8);
    assert(b[14 + w.len() as int] == 0u8);
    assert(b[15 + w.len() as int] == 1u8);
    assert(u16_at(b, 0) == id as nat) by (nonlinear_arith)
        requires
            b[0] == (id as nat / 256 % 256) as u8,
            b[1] == (id as nat % 256) as u8,
            id <= 65535,
    ;
    assert(u16_at(b, 12 + w.len()) == qtype as nat) by (nonlinear_arith)
        requires
            b[12 + w.len() as int] == (qtype as nat / 256 % 256) as u8,
            b[13 + w.len() as int] == (qtype as nat % 256) as u8,
            qtype <= 65535,
    ;
}

/// The header of an encoded query decodes to the header of a standard
/// query.
pub proof fn lemma_decode_header_query(b: Seq<u8>, id: u16)
    requires
        b.len() >= 12,
        u16_at(b, 0) == id as nat,
        u16_at(b, 2) == 256,
        u16_at(b, 4) == 1,
        u16_at(b, 6) == 0,
        u16_at(b, 8) == 0,
        u16_at(b, 10) == 0,
    ensures
        decode_header(b) == Some(query_header(id)),
{
}

/// The question of an encoded query decodes to the one question.
pub proof fn lemma_read_question_query(b: Seq<u8>, w: Seq<u8>, qtype: u16)
    requires
        is_wire_name(w),
        b.len() == 16 + w.len(),
        b.subrange(12, 12 + w.len() as int) == w,
        u16_at(b, 12 + w.len()) == qtype as nat,
        u16_at(b, 14 + w.len()) == 1,
    ensures
        read_questions(b, 12, 1, seq![]) == Some((seq![Question { name: w, qtype, qclass: CLASS_IN }], b.len())),
{
    lemma_read_name_of_wire(b, 12, b.len(), seq![], w);
    assert(seq![] + w =~= w);
    assert(decode_name(b, 12) == Some((w, 12 + w.len())));
    assert(read_question(b, 12) == Some((Question { name: w, qtype, qclass: CLASS_IN }, 16 + w.len())));
    assert(read_questions(b, 16 + w.len(), 0, seq![Question { name: w, qtype, qclass: CLASS_IN }]) == Some(
        (seq![Question { name: w, qtype, qclass: CLASS_IN }], 16 + w.len()),
    ));
    assert(seq![].push(Question { name: w, qtype, qclass: CLASS_IN }) =~= seq![Question { name: w, qtype, qclass: CLASS_IN }]);
}

/// Decoding a query that [`encode_query`] built gives back the query: the
/// header of a standard query (RD set, nothing else), and the one question
/// with the name in full, QTYPE `qtype` and QCLASS IN; and the name was
/// valid.
pub proof fn lemma_decode_encode_query(id: u16, name: Seq<u8>, qtype: u16)
    ensures
        match encode_query(Query { id, name, qtype }) {
            Some(bytes) => match dotted_to_wire(name) {
                Some(w) => is_wire_name(w) && decode_message(bytes) == Some(query_message(id, w, qtype))
                    && decode_udp(bytes) == Some(query_message(id, w, qtype)),
                None => false,
            },
            None => true,
        },
{
    lemma_dotted_to_wire_valid(name);
    if let Some(w) = dotted_to_wire(name) {
        let b = query_header_bytes(id) + w + be16(qtype as nat) + be16(CLASS_IN as nat);
        lemma_query_bytes(id, w, qtype);
        lemma_decode_header_query(b, id);
        lemma_read_question_query(b, w, qtype);
        assert(b.len() <= MAX_UDP);
        assert(read_rrs(b, b.len(), 0, seq![]) == Some((Seq::<Rr>::empty(), b.len())));
        assert(decode_message(b) == Some(query_message(id, w, qtype)));
    }
}

// ---------------------------------------------------------------------------
// Answer extraction: where the addresses come from.
// ---------------------------------------------------------------------------

/// Every address [`collect`] returns is the address of a record of
/// `answers`.
pub proof fn lemma_collect_in_answers(answers: Seq<Rr>, name: Seq<u8>, qtype: u16)
    ensures
        forall|k: int|
            #![trigger collect(answers, name, qtype)[k]]
            0 <= k < collect(answers, name, qtype).len() ==> exists|i: int|
                0 <= i < answers.len() && rr_addr(#[trigger] answers[i], qtype) == Some(collect(answers, name, qtype)[k]),
    decreases answers.len(),
{
    if answers.len() > 0 {
        let rest_answers = answers.drop_first();
        lemma_collect_in_answers(rest_answers, name, qtype);
        let rest = collect(rest_answers, name, qtype);
        let all = collect(answers, name, qtype);
        assert forall|k: int| #![trigger all[k]] 0 <= k < all.len() implies exists|i: int|
            0 <= i < answers.len() && rr_addr(#[trigger] answers[i], qtype) == Some(all[k]) by {
            let included = match rr_addr(answers[0], qtype) {
                Some(a) => bytes_eq_ci(answers[0].name, name),
                None => false,
            };
            if included {
                if k == 0 {
                    assert(rr_addr(answers[0], qtype) == Some(all[0]));
                } else {
                    assert(all[k] == rest[k - 1]);
                    let i = choose|i: int| 0 <= i < rest_answers.len() && rr_addr(#[trigger] rest_answers[i], qtype) == Some(rest[k - 1]);
                    assert(answers[i + 1] == rest_answers[i]);
                    assert(rr_addr(answers[i + 1], qtype) == Some(all[k]));
                }
            } else {
                assert(all == rest);
                let i = choose|i: int| 0 <= i < rest_answers.len() && rr_addr(#[trigger] rest_answers[i], qtype) == Some(rest[k]);
                assert(answers[i + 1] == rest_answers[i]);
                assert(rr_addr(answers[i + 1], qtype) == Some(all[k]));
            }
        }
    }
}

/// A CNAME target [`cname_next`] returns is the target of a record of
/// `answers`.
pub proof fn lemma_cname_next_in_answers(answers: Seq<Rr>, name: Seq<u8>)
    ensures
        match cname_next(answers, name) {
            Some(t) => exists|i: int| 0 <= i < answers.len() && rr_cname(#[trigger] answers[i]) == Some(t),
            None => true,
        },
    decreases answers.len(),
{
    if answers.len() > 0 {
        lemma_cname_next_in_answers(answers.drop_first(), name);
        if let Some(t) = cname_next(answers, name) {
            if rr_cname(answers[0]) == Some(t) {
                assert(rr_cname(answers[0]) == Some(t));
            } else {
                let rest = answers.drop_first();
                let i = choose|i: int| 0 <= i < rest.len() && rr_cname(#[trigger] rest[i]) == Some(t);
                assert(answers[i + 1] == rest[i]);
            }
        }
    }
}

/// The end of a CNAME chain is the start, or the target of a record of
/// `answers`.
pub proof fn lemma_chain_end_in_answers(answers: Seq<Rr>, cur: Seq<u8>, hops: nat, fuel: nat)
    ensures
        match chain_end(answers, cur, hops, fuel) {
            Some((fin, h)) => h >= hops && (h == hops ==> fin == cur) && (h > hops ==> exists|i: int|
                0 <= i < answers.len() && rr_cname(#[trigger] answers[i]) == Some(fin)),
            None => true,
        },
    decreases fuel,
{
    lemma_cname_next_in_answers(answers, cur);
    if let Some(t) = cname_next(answers, cur) {
        if fuel > 0 {
            lemma_chain_end_in_answers(answers, t, hops + 1, (fuel - 1) as nat);
        }
    }
}

/// What [`answer_addresses`] accepts, and where its result comes from: only
/// a reply with the query's ID, one question equal to the query's, QR set
/// and RCODE 0 or 3 is accepted; every address returned is the address of
/// an A or AAAA record of the answer section (never the authority or the
/// additional section); the name to ask about next, if any, is the target
/// of a CNAME record of the answer section, and then no address is
/// returned.
pub proof fn lemma_answer_addresses_in_answers(q: Query, m: Message)
    ensures
        match answer_addresses(q, m) {
            Some(r) => m.header.id == q.id && m.header.qr && !m.header.tc && m.header.opcode == 0 && (m.header.rcode == 0
                || m.header.rcode == 3) && m.questions.len() == 1 && m.questions[0].qtype == q.qtype
                && m.questions[0].qclass == CLASS_IN && (q.qtype == TYPE_A || q.qtype == TYPE_AAAA) && (forall|k: int|
                #![trigger r.addresses[k]]
                0 <= k < r.addresses.len() ==> exists|i: int|
                0 <= i < m.answers.len() && rr_addr(#[trigger] m.answers[i], q.qtype) == Some(r.addresses[k])) && (r.redirect is Some
                ==> r.addresses.len() == 0 && m.header.rcode == 0 && exists|i: int|
                0 <= i < m.answers.len() && rr_cname(#[trigger] m.answers[i]) == r.redirect),
            None => true,
        },
{
    if let Some(qname) = dotted_to_wire(q.name) {
        if m.header.rcode == 0 && (q.qtype == TYPE_A || q.qtype == TYPE_AAAA) {
            lemma_chain_end_in_answers(m.answers, qname, 0, m.answers.len());
            if let Some((fin, hops)) = chain_end(m.answers, qname, 0, m.answers.len()) {
                lemma_collect_in_answers(m.answers, fin, q.qtype);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// §4.2.2: the TCP length prefix.
// ---------------------------------------------------------------------------

/// A framed message is found again: the length at the start of the frame
/// and anything after it is the message's length, and the message follows
/// the two octets.
pub proof fn lemma_tcp_frame_length(msg: Seq<u8>, rest: Seq<u8>)
    ensures
        match tcp_frame(msg) {
            Some(f) => tcp_message_len(f + rest) == Some(msg.len()) && (f + rest).subrange(2, 2 + msg.len() as int) == msg,
            None => msg.len() > MAX_TCP,
        },
{
    if msg.len() <= MAX_TCP {
        let f = be16(msg.len()) + msg;
        let all = f + rest;
        assert(all[0] == (msg.len() / 256 % 256) as u8);
        assert(all[1] == (msg.len() % 256) as u8);
        assert(u16_at(all, 0) == msg.len()) by (nonlinear_arith)
            requires
                all[0] == (msg.len() / 256 % 256) as u8,
                all[1] == (msg.len() % 256) as u8,
                msg.len() <= 65535,
        ;
        assert(all.subrange(2, 2 + msg.len() as int) =~= msg);
    }
}

} // verus!
