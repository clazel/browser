//! Termination of the recursive functions in [`super::spec`]. Verus needs
//! these facts to accept the spec's `decreases` clauses (they name `via`
//! functions in `spec.rs`, which only call these); they say nothing else
//! about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A CRLF found at or after `i` is a CRLF, at or after `i`.
pub proof fn lemma_find_crlf_from(s: Seq<u8>, i: nat)
    ensures
        match find_crlf_from(s, i) {
            Some(j) => i <= j && crlf_at(s, j as int),
            None => true,
        },
    decreases s.len() - i
{
    if i + 1 < s.len() && !crlf_at(s, i as int) {
        lemma_find_crlf_from(s, i + 1);
    }
}

/// What follows a line is shorter than its input.
pub proof fn lemma_read_line_rest(s: Seq<u8>)
    ensures
        match read_line(s) {
            LineRead::Line { line: _, rest } => rest.len() < s.len(),
            _ => true,
        },
{
    lemma_find_crlf_from(s, 0);
}

/// Every round of `is_chunk_ext` consumes its ";" and a name.
pub proof fn lemma_chunk_ext_rest(s: Seq<u8>)
    ensures
        s.len() > 0 ==> {
            let a = strip_leading_ows(s);
            a.len() > 0 && a[0] == 0x3B ==> {
                let b = strip_leading_ows(a.drop_first());
                let n = run_len(Class::Tchar, b);
                n > 0 ==> {
                    let c = b.skip(n as int);
                    let d = strip_leading_ows(c);
                    &&& c.len() < s.len()
                    &&& (d.len() > 0 && d[0] == 0x3D ==> match parse_parameter_value(strip_leading_ows(d.drop_first())) {
                        Some((_, rest)) => rest.len() < s.len(),
                        None => true,
                    })
                }
            }
        },
{
    if s.len() > 0 {
        crate::field::termination::lemma_run_len_le(Class::Ows, s);
        let a = strip_leading_ows(s);
        if a.len() > 0 && a[0] == 0x3B {
            crate::field::termination::lemma_run_len_le(Class::Ows, a.drop_first());
            let b = strip_leading_ows(a.drop_first());
            crate::field::termination::lemma_run_len_le(Class::Tchar, b);
            let n = run_len(Class::Tchar, b);
            if n > 0 {
                let c = b.skip(n as int);
                crate::field::termination::lemma_run_len_le(Class::Ows, c);
                let d = strip_leading_ows(c);
                if d.len() > 0 && d[0] == 0x3D {
                    crate::field::termination::lemma_run_len_le(Class::Ows, d.drop_first());
                    crate::field::termination::lemma_parameter_value_rest(strip_leading_ows(d.drop_first()));
                }
            }
        }
    }
}

} // verus!
