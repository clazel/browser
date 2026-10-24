//! Executable parameters (§5.6.6, §10.1.4), `Transfer-Encoding` and
//! `Connection`. Each public function is proven to meet
//! [`super::contract`]; the private ones are proven equal to the spec
//! function of the same name. The step comments are in [`super::spec`].
//!
//! The private readers return what follows as a slice (a suffix of their
//! input), which is how the spec's `Seq::skip` is carried out.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::list::list_elements;
use super::quoted::parse_quoted_string;
use super::string::{at, copy, is_tchar_exec, is_token as is_token_exec, run_len_exec};
use super::types::{ParameterBuf, TransferCodingBuf};

verus! {

/// What follows the first `k` octets of `s`.
fn sub(s: &[u8], k: usize) -> (r: &[u8])
    requires
        k <= s.len(),
    ensures
        r@ == s@.skip(k as int),
{
    vstd::slice::slice_subrange(s, k, s.len())
}

/// The first `n` octets of `s`, copied.
fn take(s: &[u8], n: usize) -> (r: Vec<u8>)
    requires
        n <= s.len(),
    ensures
        r@ == s@.take(n as int),
{
    let out = copy(vstd::slice::slice_subrange(s, 0, n));
    assert(out@ =~= s@.take(n as int));
    out
}

/// `parse_parameter_value` (§5.6.6): the value and what follows it.
pub fn parse_parameter_value_exec(input: &[u8]) -> (out: Option<(Vec<u8>, usize)>)
    ensures
        match out {
            Some((v, k)) => k <= input.len() && parse_parameter_value(input@) == Some((v@, input@.skip(k as int))),
            None => parse_parameter_value(input@) is None,
        },
{
    if at(input, 0) == Some(0x22u8) {
        return parse_quoted_string(input);
    }
    let n = run_len_exec(&Class::Tchar, input);
    if n > 0 {
        Some((take(input, n), n))
    } else {
        None
    }
}

/// `parse_parameter` (§5.6.6, §10.1.4): one parameter and what follows it.
fn parse_parameter_exec<'a>(input: &'a [u8], grammar: &ParameterGrammar) -> (out: Option<(ParameterBuf, &'a [u8])>)
    ensures
        match out {
            Some((p, rest)) => parse_parameter(input@, *grammar) == Some((p@, rest@)),
            None => parse_parameter(input@, *grammar) is None,
        },
{
    let n = run_len_exec(&Class::Tchar, input);
    if n == 0 {
        return None;
    }
    let name = take(input, n);
    let after_name = sub(input, n);
    let before_equals = match grammar {
        ParameterGrammar::Parameters => after_name,
        ParameterGrammar::TransferCoding => sub(after_name, run_len_exec(&Class::Ows, after_name)),
    };
    assert(before_equals@ == match *grammar {
        ParameterGrammar::Parameters => input@.skip(n as int),
        ParameterGrammar::TransferCoding => strip_leading_ows(input@.skip(n as int)),
    }) by {
        assert(after_name@.skip(0) =~= after_name@);
    }
    if at(before_equals, 0) != Some(0x3Du8) {
        return None;
    }
    let after_equals_raw = sub(before_equals, 1);
    assert(after_equals_raw@ =~= before_equals@.drop_first());
    let after_equals = match grammar {
        ParameterGrammar::Parameters => after_equals_raw,
        ParameterGrammar::TransferCoding => sub(after_equals_raw, run_len_exec(&Class::Ows, after_equals_raw)),
    };
    assert(after_equals@ == match *grammar {
        ParameterGrammar::Parameters => before_equals@.drop_first(),
        ParameterGrammar::TransferCoding => strip_leading_ows(before_equals@.drop_first()),
    }) by {
        assert(after_equals_raw@.skip(0) =~= after_equals_raw@);
    }
    match parse_parameter_value_exec(after_equals) {
        Some((value, k)) => Some((ParameterBuf { name, value }, sub(after_equals, k))),
        None => None,
    }
}

/// Is a parameter present after `OWS ";" OWS`, whose rest is `input`?
fn parameter_present_exec(input: &[u8], grammar: &ParameterGrammar) -> (r: bool)
    ensures
        r == parameter_present(input@, *grammar),
{
    match grammar {
        ParameterGrammar::Parameters => match at(input, 0) {
            Some(c) => is_tchar_exec(c),
            None => false,
        },
        ParameterGrammar::TransferCoding => true,
    }
}

/// `parse_parameters` (§5.6.6, §10.1.4): the parameters over all of `input`.
pub fn parse_parameters(input: &[u8], grammar: &ParameterGrammar) -> (out: Option<Vec<ParameterBuf>>)
    ensures
        super::contract::parse_parameters_ensures(input@, *grammar, match out {
            Some(v) => Some(super::types::params_view(v@)),
            None => None,
        }),
{
    let ghost target = super::spec::parse_parameters(input@, *grammar);
    let mut acc: Vec<ParameterBuf> = Vec::new();
    assert(super::types::params_view(acc@) =~= Seq::<Parameter>::empty());
    let mut cur: &[u8] = input;
    loop
        invariant
            target == super::spec::parse_parameters(input@, *grammar),
            target == parameters_loop(cur@, *grammar, super::types::params_view(acc@)),
        decreases cur.len(),
    {
        if cur.is_empty() {
            return Some(acc);
        }
        let leading = run_len_exec(&Class::Ows, cur);
        let after_ows = sub(cur, leading);
        if at(after_ows, 0) != Some(0x3Bu8) {
            return None;
        }
        let after_semicolon = sub(after_ows, 1);
        assert(after_semicolon@ =~= after_ows@.drop_first());
        let spaces = run_len_exec(&Class::Ows, after_semicolon);
        let rest = sub(after_semicolon, spaces);
        proof {
            super::termination::lemma_run_len_le(Class::Ows, cur@);
            super::termination::lemma_run_len_le(Class::Ows, after_semicolon@);
        }
        if parameter_present_exec(rest, grammar) {
            match parse_parameter_exec(rest, grammar) {
                None => return None,
                Some((p, after)) => {
                    proof {
                        super::termination::lemma_parse_parameter_rest(rest@, *grammar);
                    }
                    let ghost before = super::types::params_view(acc@);
                    acc.push(p);
                    assert(super::types::params_view(acc@) =~= before.push(p@));
                    cur = after;
                },
            }
        } else {
            cur = rest;
        }
    }
}

/// `parse_transfer_coding` (§10.1.4) over all of `element`.
fn parse_transfer_coding_exec(element: &[u8]) -> (out: Option<TransferCodingBuf>)
    ensures
        match out {
            Some(c) => parse_transfer_coding(element@) == Some(c@),
            None => parse_transfer_coding(element@) is None,
        },
{
    let n = run_len_exec(&Class::Tchar, element);
    if n == 0 {
        return None;
    }
    let name = take(element, n);
    let parameters = parse_parameters(sub(element, n), &ParameterGrammar::TransferCoding)?;
    Some(TransferCodingBuf { name, parameters })
}

/// `parse_transfer_encoding` (RFC 9112 §6.1, §10.1.4): the codings of the
/// combined `Transfer-Encoding` value, or `None` if an element is not one.
pub fn parse_transfer_encoding(value: &[u8]) -> (out: Option<Vec<TransferCodingBuf>>)
    ensures
        super::contract::parse_transfer_encoding_ensures(value@, match out {
            Some(v) => Some(super::types::codings_view(v@)),
            None => None,
        }),
{
    let elements = list_elements(value);
    let ghost view = super::types::strings_view(elements@);
    assert(view.take(0) =~= Seq::<Seq<u8>>::empty());
    let mut out: Vec<TransferCodingBuf> = Vec::new();
    assert(super::types::codings_view(out@) =~= Seq::<TransferCoding>::empty());
    let mut ok = true;
    let mut i: usize = 0;
    while i < elements.len()
        invariant
            i <= elements.len(),
            view == super::types::strings_view(elements@),
            parse_transfer_codings(view.take(i as int)) == (if ok {
                Some(super::types::codings_view(out@))
            } else {
                None
            }),
        decreases elements.len() - i,
    {
        if let Some(element) = elements.get(i) {
            proof {
                super::lemmas::lemma_codings_push(view.take(i as int), element@);
            }
            assert(view.take(i as int + 1) =~= view.take(i as int).push(element@));
            if ok {
                match parse_transfer_coding_exec(element.as_slice()) {
                    Some(c) => {
                        let ghost before = super::types::codings_view(out@);
                        out.push(c);
                        assert(super::types::codings_view(out@) =~= before.push(c@));
                    },
                    None => {
                        ok = false;
                    },
                }
            }
        }
        // Never saturates: i < elements.len().
        i = i.saturating_add(1);
    }
    assert(view.take(elements.len() as int) =~= view);
    if ok {
        Some(out)
    } else {
        None
    }
}

/// `parse_connection` (§7.6.1): the options of the combined `Connection`
/// value, or `None` if an element is not a token.
pub fn parse_connection(value: &[u8]) -> (out: Option<Vec<Vec<u8>>>)
    ensures
        super::contract::parse_connection_ensures(value@, match out {
            Some(v) => Some(super::types::strings_view(v@)),
            None => None,
        }),
{
    let options = list_elements(value);
    let ghost view = super::types::strings_view(options@);
    proof {
        super::lemmas::lemma_all_tokens_index(view);
    }
    let mut i: usize = 0;
    while i < options.len()
        invariant
            i <= options.len(),
            view == super::types::strings_view(options@),
            view == super::spec::list_elements(value@),
            forall|j: int| 0 <= j < i ==> super::spec::is_token(#[trigger] view[j]),
        decreases options.len() - i,
    {
        let option = match options.get(i) {
            Some(option) => option,
            None => {
                // Unreachable: i < options.len().
                assert(false);
                return None;
            },
        };
        if !is_token_exec(option.as_slice()) {
            assert(view[i as int] == option@);
            assert(!super::spec::is_token(view[i as int]));
            proof {
                super::lemmas::lemma_all_tokens_index(view);
            }
            assert(!all_tokens(view));
            assert(view == super::spec::list_elements(value@));
            assert(super::spec::parse_connection(value@) is None);
            return None;
        }
        // Never saturates: i < options.len().
        i = i.saturating_add(1);
    }
    Some(options)
}

} // verus!
