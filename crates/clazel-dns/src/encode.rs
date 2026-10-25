//! The executable query builder and the TCP length prefix, proven to meet
//! [`super::contract`]. Each follows [`super::spec`] (the quotes live
//! there).

use super::decode::{append_range, read_u16};
use super::spec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Scan a dotted name; see `spec::dotted_scan`. The wire format of the
/// labels, without the final zero octet.
fn scan(s: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        super::types::opt_bytes(r) == spec::dotted_scan(s@, 0, 0, seq![]),
{
    let mut i: usize = 0;
    let mut start: usize = 0;
    let mut acc: Vec<u8> = Vec::new();
    while i < s.len()
        invariant
            start <= i <= s.len(),
            acc@.len() == start,
            spec::dotted_scan(s@, i as nat, start as nat, acc@) == spec::dotted_scan(s@, 0, 0, seq![]),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(&c) => c,
            None => return None,
        };
        if c == 46 {
            // i >= start, so this does not saturate.
            let label_len = i.saturating_sub(start);
            if label_len == 0 || label_len > spec::MAX_LABEL {
                return None;
            }
            let ghost old_acc = acc@;
            acc.push(label_len as u8);
            append_range(&mut acc, s, start, i);
            assert(acc@ =~= old_acc + seq![label_len as u8] + s@.subrange(start as int, i as int));
            // i < s.len(), so this does not saturate.
            i = i.saturating_add(1);
            start = i;
        } else if c >= 128 {
            return None;
        } else {
            // i < s.len(), so this does not saturate.
            i = i.saturating_add(1);
        }
    }
    // i == s.len() >= start.
    if i > start {
        let label_len = i.saturating_sub(start);
        if label_len > spec::MAX_LABEL {
            return None;
        }
        let ghost old_acc = acc@;
        acc.push(label_len as u8);
        append_range(&mut acc, s, start, i);
        assert(acc@ =~= old_acc + seq![label_len as u8] + s@.subrange(start as int, i as int));
    }
    Some(acc)
}

/// A host name as a dotted ASCII string, in wire format; see
/// `spec::dotted_to_wire`.
pub fn dotted_to_wire(s: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::dotted_to_wire_ensures(s@, super::types::opt_bytes(output)),
{
    if s.is_empty() {
        return None;
    }
    let is_root = match s.first() {
        Some(&c) => s.len() == 1 && c == 46,
        None => false,
    };
    proof {
        // `s` is the root exactly when it is the single octet ".".
        if is_root {
            assert(s@ =~= seq![46u8]);
        } else if s@.len() == 1 {
            assert(s@[0] != 46);
            assert(s@ != seq![46u8]);
        } else {
            assert(s@ != seq![46u8]);
        }
    }
    if is_root {
        // "." alone is the root.
        let mut root: Vec<u8> = Vec::new();
        append_range(&mut root, [0u8].as_slice(), 0, 1);
        assert(root@ =~= seq![0u8]);
        return Some(root);
    }
    let mut w = scan(s)?;
    // w holds the labels: at most `s.len()` octets, so this does not
    // saturate.
    if w.len().saturating_add(1) > spec::MAX_NAME {
        return None;
    }
    let ghost labels = w@;
    w.push(0);
    assert(w@ =~= labels + seq![0u8]);
    Some(w)
}

/// Whether the octets `w[from..to]` can stand between dots: see
/// `spec::is_dotted_label`.
fn dotted_label(w: &[u8], from: usize, to: usize) -> (r: bool)
    requires
        from <= to <= w.len(),
    ensures
        r == spec::is_dotted_label(w@.subrange(from as int, to as int)),
{
    let ghost label = w@.subrange(from as int, to as int);
    assert(label.len() == to - from);
    let mut k: usize = from;
    while k < to
        invariant
            from <= k <= to,
            to <= w.len(),
            label == w@.subrange(from as int, to as int),
            label.len() == to - from,
            // The octets before `k` are plain, so the label is plain exactly
            // when the rest of it is.
            spec::dotted_run(label, 0) == spec::dotted_run(label, (k - from) as nat),
        decreases to - k,
    {
        let c = match w.get(k) {
            Some(&c) => c,
            None => return false,
        };
        assert(label[(k - from) as int] == w@[k as int]);
        if c == 46 || c >= 128 {
            // The octet at `k` is not plain, so neither is the rest from `k`.
            assert(!spec::dotted_run(label, (k - from) as nat));
            return false;
        }
        // k < to, so this does not saturate.
        k = k.saturating_add(1);
    }
    true
}

/// An uncompressed wire name as a dotted string; see `spec::wire_to_dotted`.
pub fn wire_to_dotted(w: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::wire_to_dotted_ensures(w@, super::types::opt_bytes(output)),
{
    // §2.3.4: names are 255 octets or less. That also keeps every position
    // below small enough that nothing overflows.
    if w.len() > spec::MAX_NAME {
        return None;
    }
    let mut acc: Vec<u8> = Vec::new();
    let mut pos: usize = 0;
    // `acc` is the dotted form of the labels before `pos`; what `wire_scan`
    // makes of the whole name is `acc` joined with what it makes from `pos`.
    loop
        invariant
            pos <= w.len() <= spec::MAX_NAME,
            spec::wire_scan(w@, 0) == match spec::wire_scan(w@, pos as nat) {
                None => None::<Seq<u8>>,
                Some(rest) => Some(spec::join_dotted(acc@, rest)),
            },
        decreases w.len() - pos,
    {
        let len = match w.get(pos) {
            Some(&c) => c as usize,
            // The name ended without the zero octet.
            None => return None,
        };
        if len == 0 {
            if pos.saturating_add(1) != w.len() {
                // Octets after the root label.
                return None;
            }
            // The root label ends the name; the root alone has no label.
            if acc.is_empty() {
                return None;
            }
            return Some(acc);
        }
        let start = pos.saturating_add(1);
        let end = start.saturating_add(len);
        if len > spec::MAX_LABEL || end > w.len() {
            return None;
        }
        if !dotted_label(w, start, end) {
            return None;
        }
        let ghost label = w@.subrange(start as int, end as int);
        proof {
            // The label is not empty, so joining it commutes with joining
            // what follows.
            match spec::wire_scan(w@, end as nat) {
                Some(rest) => super::lemmas::lemma_join_dotted_assoc(acc@, label, rest),
                None => {}
            }
        }
        let ghost old_acc = acc@;
        if !acc.is_empty() {
            acc.push(46);
        }
        append_range(&mut acc, w, start, end);
        assert(acc@ =~= spec::join_dotted(old_acc, label));
        // end > pos, so this does not saturate.
        pos = end;
    }
}

/// A standard query: see `spec::encode_query`.
pub fn encode_query(id: u16, name: &[u8], qtype: u16) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::encode_query_ensures(id, name@, qtype, super::types::opt_bytes(output)),
{
    let w = dotted_to_wire(name)?;
    // The ID, then the flags word 0x0100 (only RD), then QDCOUNT 1 and
    // ANCOUNT, NSCOUNT, ARCOUNT 0.
    let header: [u8; 12] = [(id / 256) as u8, (id % 256) as u8, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0];
    let mut out: Vec<u8> = Vec::new();
    append_range(&mut out, header.as_slice(), 0, 12);
    assert(out@ =~= spec::query_header_bytes(id));
    append_range(&mut out, w.as_slice(), 0, w.len());
    // QTYPE, then QCLASS IN.
    let tail: [u8; 4] = [(qtype / 256) as u8, (qtype % 256) as u8, 0, 1];
    append_range(&mut out, tail.as_slice(), 0, 4);
    assert(out@ =~= spec::query_header_bytes(id) + w@ + spec::be16(qtype as nat) + spec::be16(spec::CLASS_IN as nat));
    Some(out)
}

/// §4.2.2: a message with its two octet length prefix; see
/// `spec::tcp_frame`.
pub fn tcp_frame(msg: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::tcp_frame_ensures(msg@, super::types::opt_bytes(output)),
{
    if msg.len() > spec::MAX_TCP {
        return None;
    }
    let prefix: [u8; 2] = [(msg.len() / 256) as u8, (msg.len() % 256) as u8];
    let mut out: Vec<u8> = Vec::new();
    append_range(&mut out, prefix.as_slice(), 0, 2);
    append_range(&mut out, msg, 0, msg.len());
    assert(out@ =~= spec::be16(msg@.len()) + msg@);
    Some(out)
}

/// §4.2.2: the length of the message at the start of `input`, once the
/// length prefix and the whole message have arrived; see
/// `spec::tcp_message_len`.
pub fn tcp_message_len(input: &[u8]) -> (output: Option<usize>)
    ensures
        super::contract::tcp_message_len_ensures(input@, super::decode::opt_nat(output)),
{
    if input.len() < 2 {
        return None;
    }
    let n = read_u16(input, 0) as usize;
    // n <= 65535, so this does not saturate.
    if input.len() < n.saturating_add(2) {
        return None;
    }
    Some(n)
}

} // verus!
