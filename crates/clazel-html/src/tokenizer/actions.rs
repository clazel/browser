//! The executable actions the states share, each proven to do what its
//! spec function in [`super::spec`] does to every spec tokenizer the exec
//! one stands for ([`super::contract::abstracts`]).

use super::buffer::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A copy of an optional string.
pub fn copy_opt(o: &Option<Vec<u32>>) -> (r: Option<Vec<u32>>)
    ensures
        opt_view(r) == opt_view(*o),
{
    match o {
        Some(v) => {
            let c = copy(v);
            assert(c@ == v@);
            Some(c)
        },
        None => None,
    }
}

/// A copy of an attribute.
pub fn copy_attribute(a: &ExecAttribute) -> (r: ExecAttribute)
    ensures
        r@ == a@,
{
    ExecAttribute { name: copy(&a.name), value: copy(&a.value) }
}

/// A copy of a list of attributes.
pub fn copy_attributes(v: &[ExecAttribute]) -> (r: Vec<ExecAttribute>)
    ensures
        attributes_view(r@) == attributes_view(v@),
{
    let mut r: Vec<ExecAttribute> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            attributes_view(r@) == attributes_view(v@.subrange(0, i as int)),
        decreases v.len() - i,
    {
        if let Some(a) = v.get(i) {
            r.push(copy_attribute(a));
        }
        assert(attributes_view(v@.subrange(0, i + 1)) =~= attributes_view(v@.subrange(0, i as int)).push(
            v@[i as int]@,
        ));
        assert(attributes_view(r@) =~= attributes_view(v@.subrange(0, i + 1)));
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    r
}

/// A copy of a token.
pub fn copy_token(t: &ExecToken) -> (r: ExecToken)
    ensures
        r@ == t@,
{
    match t {
        ExecToken::Doctype { name, public_identifier, system_identifier, force_quirks } => ExecToken::Doctype {
            name: copy_opt(name),
            public_identifier: copy_opt(public_identifier),
            system_identifier: copy_opt(system_identifier),
            force_quirks: *force_quirks,
        },
        ExecToken::StartTag { tag_name, self_closing, attributes } => ExecToken::StartTag {
            tag_name: copy(tag_name),
            self_closing: *self_closing,
            attributes: copy_attributes(attributes),
        },
        ExecToken::EndTag { tag_name, self_closing, attributes } => ExecToken::EndTag {
            tag_name: copy(tag_name),
            self_closing: *self_closing,
            attributes: copy_attributes(attributes),
        },
        ExecToken::Comment { data } => ExecToken::Comment { data: copy(data) },
        ExecToken::ProcessingInstruction { target, data } => ExecToken::ProcessingInstruction {
            target: copy(target),
            data: copy(data),
        },
        ExecToken::Character(c) => ExecToken::Character(*c),
        ExecToken::EndOfFile => ExecToken::EndOfFile,
    }
}

/// Take the current token out of `t`, leaving an empty comment.
fn take_current(t: &mut ExecTokenizer) -> (r: ExecToken)
    ensures
        r@ == old(t)@.current,
        final(t)@ == (Tokenizer { current: empty_comment(), ..old(t)@ }),
{
    let mut r = ExecToken::Comment { data: Vec::new() };
    core::mem::swap(&mut r, &mut t.current);
    assert(t.current@ =~~= empty_comment());
    r
}

/// The next input character: `None` is EOF.
pub fn next_char_exec(input: &[u32], pos: usize) -> (r: Option<u32>)
    ensures
        r == next_char(input@, pos as nat),
{
    if pos < input.len() {
        Some(at32(input, pos))
    } else {
        None
    }
}

/// "Switch to the return state": the state.
pub fn return_state_state(r: &ReturnState) -> (s: State)
    ensures
        s == r.state(),
{
    match r {
        ReturnState::Data => State::Data,
        ReturnState::Rcdata => State::Rcdata,
        ReturnState::AttributeValueDoubleQuoted => State::AttributeValueDoubleQuoted,
        ReturnState::AttributeValueSingleQuoted => State::AttributeValueSingleQuoted,
        ReturnState::AttributeValueUnquoted => State::AttributeValueUnquoted,
    }
}

/// [`new_start_tag`].
pub fn new_start_tag_exec(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(new_start_tag(st), final(t)@),
{
    t.current = ExecToken::StartTag { tag_name: Vec::new(), self_closing: false, attributes: Vec::new() };
    t.attribute_status = AttributeStatus::NoAttribute;
    assert(attributes_view(Seq::<ExecAttribute>::empty()) =~= Seq::<Attribute>::empty());
    assert(t.current@ =~~= new_start_tag(st).current);
}

/// [`new_end_tag`].
pub fn new_end_tag_exec(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(new_end_tag(st), final(t)@),
{
    t.current = ExecToken::EndTag { tag_name: Vec::new(), self_closing: false, attributes: Vec::new() };
    t.attribute_status = AttributeStatus::NoAttribute;
    assert(attributes_view(Seq::<ExecAttribute>::empty()) =~= Seq::<Attribute>::empty());
    assert(t.current@ =~~= new_end_tag(st).current);
}

/// [`append_to_tag_name`].
pub fn append_to_tag_name_exec(t: &mut ExecTokenizer, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_tag_name(st, c), final(t)@),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::StartTag { tag_name, self_closing, attributes } => {
            let mut tag_name = tag_name;
            tag_name.push(c);
            ExecToken::StartTag { tag_name, self_closing, attributes }
        },
        ExecToken::EndTag { tag_name, self_closing, attributes } => {
            let mut tag_name = tag_name;
            tag_name.push(c);
            ExecToken::EndTag { tag_name, self_closing, attributes }
        },
        other => other,
    };
    assert(t.current@ =~~= append_to_tag_name(st, c).current);
}

/// [`set_self_closing`].
pub fn set_self_closing_exec(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(set_self_closing(st), final(t)@),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::StartTag { tag_name, self_closing: _, attributes } => ExecToken::StartTag {
            tag_name,
            self_closing: true,
            attributes,
        },
        ExecToken::EndTag { tag_name, self_closing: _, attributes } => ExecToken::EndTag {
            tag_name,
            self_closing: true,
            attributes,
        },
        other => other,
    };
    assert(t.current@ =~~= set_self_closing(st).current);
}

/// Push the current attribute onto `attributes` if it is on the token
/// ([`attributes_with_current`]), leaving an empty current attribute.
fn commit_attribute(t: &mut ExecTokenizer, attributes: &mut Vec<ExecAttribute>)
    ensures
        attributes_view(final(attributes)@) == attributes_with_current(attributes_view(old(attributes)@), old(t)@),
        final(t)@ == (Tokenizer { current_attribute: empty_attribute(), ..old(t)@ }),
{
    let mut a = ExecAttribute { name: Vec::new(), value: Vec::new() };
    core::mem::swap(&mut a, &mut t.current_attribute);
    assert(t.current_attribute@ =~= empty_attribute());
    if matches!(t.attribute_status, AttributeStatus::Kept) {
        attributes.push(a);
        assert(attributes_view(attributes@) =~= attributes_view(old(attributes)@).push(old(t)@.current_attribute));
    }
}

/// [`start_attribute`], with name `name`.
pub fn start_attribute_exec(t: &mut ExecTokenizer, name: Vec<u32>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(start_attribute(st, name@), final(t)@),
{
    let cur = take_current(t);
    let ghost t1 = t@;
    t.current = match cur {
        ExecToken::StartTag { tag_name, self_closing, attributes } => {
            let mut attributes = attributes;
            commit_attribute(t, &mut attributes);
            ExecToken::StartTag { tag_name, self_closing, attributes }
        },
        ExecToken::EndTag { tag_name, self_closing, attributes } => {
            let mut attributes = attributes;
            commit_attribute(t, &mut attributes);
            ExecToken::EndTag { tag_name, self_closing, attributes }
        },
        other => other,
    };
    t.current_attribute = ExecAttribute { name, value: Vec::new() };
    t.attribute_status = AttributeStatus::Kept;
    assert(t.current@ =~~= start_attribute(st, name@).current);
    assert(t.current_attribute@ =~= start_attribute(st, name@).current_attribute);
}

/// [`append_to_attribute_name`].
pub fn append_to_attribute_name_exec(t: &mut ExecTokenizer, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_attribute_name(st, c), final(t)@),
{
    t.current_attribute.name.push(c);
    assert(t.current_attribute@ =~= append_to_attribute_name(st, c).current_attribute);
}

/// [`append_to_attribute_value`] with one code point.
pub fn append_to_attribute_value_exec(t: &mut ExecTokenizer, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_attribute_value(st, seq![c]), final(t)@),
{
    t.current_attribute.value.push(c);
    assert(st.current_attribute.value + seq![c] =~= st.current_attribute.value.push(c));
    assert(t.current_attribute@ =~~= append_to_attribute_value(st, seq![c]).current_attribute);
}

/// Whether one of `attributes` has the name `name`.
fn has_attribute_named_exec(attributes: &[ExecAttribute], name: &Vec<u32>) -> (r: bool)
    ensures
        r == has_attribute_named(attributes_view(attributes@), name@),
{
    let mut i: usize = 0;
    assert(attributes_view(attributes@).subrange(0, 0) =~= Seq::<Attribute>::empty());
    while i < attributes.len()
        invariant
            i <= attributes.len(),
            !has_attribute_named(attributes_view(attributes@).subrange(0, i as int), name@),
        decreases attributes.len() - i,
    {
        let ghost v = attributes_view(attributes@);
        assert(v.subrange(0, i + 1).drop_last() =~= v.subrange(0, i as int));
        let found = match attributes.get(i) {
            Some(a) => eq_codes(&a.name, name),
            None => false,
        };
        if found {
            assert(has_attribute_named(v.subrange(0, i + 1), name@));
            assert(has_attribute_named(v, name@)) by {
                lemma_has_attribute_named_prefix(v, name@, (i + 1) as int);
            }
            return true;
        }
        // Never saturates: i < attributes.len().
        i = i.saturating_add(1);
    }
    assert(attributes_view(attributes@).subrange(0, i as int) =~= attributes_view(attributes@));
    false
}

/// A name in a prefix of the list is in the list.
proof fn lemma_has_attribute_named_prefix(v: Seq<Attribute>, name: Seq<u32>, k: int)
    requires
        0 <= k <= v.len(),
        has_attribute_named(v.subrange(0, k), name),
    ensures
        has_attribute_named(v, name),
    decreases v.len() - k,
{
    if k < v.len() {
        assert(v.subrange(0, k + 1).drop_last() =~= v.subrange(0, k));
        lemma_has_attribute_named_prefix(v, name, k + 1);
    } else {
        assert(v.subrange(0, k) =~= v);
    }
}

/// [`leave_attribute_name`].
pub fn leave_attribute_name_exec(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(leave_attribute_name(st), final(t)@),
{
    if matches!(t.attribute_status, AttributeStatus::Kept) {
        let dup = match &t.current {
            ExecToken::StartTag { attributes, .. } => has_attribute_named_exec(attributes, &t.current_attribute.name),
            ExecToken::EndTag { attributes, .. } => has_attribute_named_exec(attributes, &t.current_attribute.name),
            _ => false,
        };
        assert(tag_attributes(st.current).len() == match t.current {
            ExecToken::StartTag { attributes, .. } => attributes@.len(),
            ExecToken::EndTag { attributes, .. } => attributes@.len(),
            _ => 0,
        });
        if dup {
            t.attribute_status = AttributeStatus::Removed;
        }
    }
}

/// [`emit_current_tag`]: the current tag token goes to `out`, and stays
/// the current token.
pub fn emit_current_tag_exec(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(emit_current_tag(st, seq![]).0, final(t)@),
        tokens_view(final(out)@) == tokens_view(old(out)@) + emit_current_tag(st, seq![]).1,
{
    let kept = matches!(t.attribute_status, AttributeStatus::Kept);
    let tok = match &t.current {
        ExecToken::StartTag { tag_name, self_closing, attributes } => {
            let mut a = copy_attributes(attributes);
            if kept {
                a.push(copy_attribute(&t.current_attribute));
                assert(attributes_view(a@) =~= attributes_view(a@.drop_last()).push(st.current_attribute));
            }
            assert(attributes_view(a@) == attributes_with_current(attributes_view(attributes@), st));
            ExecToken::StartTag { tag_name: copy(tag_name), self_closing: *self_closing, attributes: a }
        },
        ExecToken::EndTag { tag_name, self_closing, attributes } => {
            let mut a = copy_attributes(attributes);
            if kept {
                a.push(copy_attribute(&t.current_attribute));
                assert(attributes_view(a@) =~= attributes_view(a@.drop_last()).push(st.current_attribute));
            }
            assert(attributes_view(a@) == attributes_with_current(attributes_view(attributes@), st));
            ExecToken::EndTag { tag_name: copy(tag_name), self_closing: *self_closing, attributes: a }
        },
        other => copy_token(other),
    };
    assert(tok@ =~~= emit_current_tag(st, seq![]).1.last());
    if let ExecToken::StartTag { tag_name, .. } = &t.current {
        t.last_start_tag = Some(copy(tag_name));
    }
    if matches!(t.current, ExecToken::StartTag { .. } | ExecToken::EndTag { .. }) {
        t.attribute_status = AttributeStatus::NoAttribute;
    }
    push_token(out, tok);
    assert(emit_current_tag(st, seq![]).1 =~= seq![tok@]);
}

/// [`emit_current`]: the current token goes to `out`, and stays the
/// current token.
pub fn emit_current_exec(t: &ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, t@),
    ensures
        tokens_view(final(out)@) == tokens_view(old(out)@) + emit_current(st, seq![]),
{
    push_token(out, copy_token(&t.current));
    assert(emit_current(st, seq![]) =~= seq![st.current]);
}

/// [`new_comment`] with data `data`.
pub fn new_comment_exec(t: &mut ExecTokenizer, data: Vec<u32>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(new_comment(st, data@), final(t)@),
{
    t.current = ExecToken::Comment { data };
}

/// [`append_to_comment`] with the code points of `s`.
pub fn append_to_comment_exec(t: &mut ExecTokenizer, s: &Vec<u32>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_comment(st, s@), final(t)@),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::Comment { data } => {
            let mut data = data;
            extend(&mut data, s);
            ExecToken::Comment { data }
        },
        other => other,
    };
    assert(t.current@ =~~= append_to_comment(st, s@).current);
}

/// [`append_to_comment`] with one code point.
pub fn append_char_to_comment_exec(t: &mut ExecTokenizer, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_comment(st, seq![c]), final(t)@),
{
    let s = from_slice([c].as_slice());
    assert(s@ =~= seq![c]);
    append_to_comment_exec(t, &s, Ghost(st));
}

/// [`convert_temporary_buffer_to_comment`].
pub fn convert_temporary_buffer_to_comment_exec(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(convert_temporary_buffer_to_comment(st), final(t)@),
{
    let mut data = from_slice([0x3Fu32].as_slice());
    extend(&mut data, &t.temporary_buffer);
    assert(data@ =~= seq![0x3Fu32] + st.temporary_buffer);
    t.current = ExecToken::Comment { data };
}

/// [`new_doctype`] with name `name`.
pub fn new_doctype_exec(t: &mut ExecTokenizer, name: Option<Vec<u32>>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(new_doctype(st, opt_view(name)), final(t)@),
{
    t.current = ExecToken::Doctype { name, public_identifier: None, system_identifier: None, force_quirks: false };
}

/// [`set_force_quirks`].
pub fn set_force_quirks_exec(t: &mut ExecTokenizer, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(set_force_quirks(st), final(t)@),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::Doctype { name, public_identifier, system_identifier, force_quirks: _ } => ExecToken::Doctype {
            name,
            public_identifier,
            system_identifier,
            force_quirks: true,
        },
        other => other,
    };
    assert(t.current@ =~~= set_force_quirks(st).current);
}

/// Push `c` onto an optional string, a missing one becoming `[c]`.
fn push_opt(o: Option<Vec<u32>>, c: u32) -> (r: Option<Vec<u32>>)
    ensures
        opt_view(r) == Some(
            match opt_view(o) {
                Some(v) => v.push(c),
                None => seq![c],
            },
        ),
{
    match o {
        Some(v) => {
            let mut v = v;
            v.push(c);
            Some(v)
        },
        None => {
            let v = from_slice([c].as_slice());
            assert(v@ =~= seq![c]);
            Some(v)
        },
    }
}

/// [`append_to_doctype_name`].
pub fn append_to_doctype_name_exec(t: &mut ExecTokenizer, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_doctype_name(st, c), final(t)@),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::Doctype { name, public_identifier, system_identifier, force_quirks } => ExecToken::Doctype {
            name: push_opt(name, c),
            public_identifier,
            system_identifier,
            force_quirks,
        },
        other => other,
    };
    assert(t.current@ =~~= append_to_doctype_name(st, c).current);
}

/// [`set_public_identifier_empty`] (`public`) or
/// [`set_system_identifier_empty`].
pub fn set_identifier_empty_exec(t: &mut ExecTokenizer, public: bool, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(
            if public {
                set_public_identifier_empty(st)
            } else {
                set_system_identifier_empty(st)
            },
            final(t)@,
        ),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::Doctype { name, public_identifier, system_identifier, force_quirks } => {
            if public {
                ExecToken::Doctype { name, public_identifier: Some(Vec::new()), system_identifier, force_quirks }
            } else {
                ExecToken::Doctype { name, public_identifier, system_identifier: Some(Vec::new()), force_quirks }
            }
        },
        other => other,
    };
    proof {
        if public {
            assert(t.current@ =~~= set_public_identifier_empty(st).current);
        } else {
            assert(t.current@ =~~= set_system_identifier_empty(st).current);
        }
    }
}

/// [`append_to_public_identifier`] (`public`) or
/// [`append_to_system_identifier`].
pub fn append_to_identifier_exec(t: &mut ExecTokenizer, public: bool, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(
            if public {
                append_to_public_identifier(st, c)
            } else {
                append_to_system_identifier(st, c)
            },
            final(t)@,
        ),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::Doctype { name, public_identifier, system_identifier, force_quirks } => {
            if public {
                ExecToken::Doctype {
                    name,
                    public_identifier: push_opt(public_identifier, c),
                    system_identifier,
                    force_quirks,
                }
            } else {
                ExecToken::Doctype {
                    name,
                    public_identifier,
                    system_identifier: push_opt(system_identifier, c),
                    force_quirks,
                }
            }
        },
        other => other,
    };
    proof {
        if public {
            assert(t.current@ =~~= append_to_public_identifier(st, c).current);
        } else {
            assert(t.current@ =~~= append_to_system_identifier(st, c).current);
        }
    }
}

/// [`append_to_pi_data`] with one code point.
pub fn append_to_pi_data_exec(t: &mut ExecTokenizer, c: u32, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(append_to_pi_data(st, seq![c]), final(t)@),
{
    let cur = take_current(t);
    t.current = match cur {
        ExecToken::ProcessingInstruction { target, data } => {
            let mut data = data;
            let ghost d = data@;
            data.push(c);
            assert(d + seq![c] =~= d.push(c));
            ExecToken::ProcessingInstruction { target, data }
        },
        other => other,
    };
    assert(t.current@ =~~= append_to_pi_data(st, seq![c]).current);
}

/// [`consumed_as_part_of_attribute`].
pub fn consumed_as_part_of_attribute_exec(t: &ExecTokenizer) -> (r: bool)
    ensures
        r == consumed_as_part_of_attribute(t@),
{
    !matches!(t.return_state, ReturnState::Data | ReturnState::Rcdata)
}

/// [`flush`].
pub fn flush_exec(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(flush(st).0, final(t)@),
        tokens_view(final(out)@) == tokens_view(old(out)@) + flush(st).1,
{
    if consumed_as_part_of_attribute_exec(t) {
        extend(&mut t.current_attribute.value, &t.temporary_buffer);
        assert(t.current_attribute@ =~= flush(st).0.current_attribute);
        assert(tokens_view(out@) =~= tokens_view(out@) + seq![]);
    } else {
        push_chars(out, &t.temporary_buffer);
    }
}

/// [`flush_and_return`].
pub fn flush_and_return_exec(t: &mut ExecTokenizer, out: &mut Vec<ExecToken>, Ghost(st): Ghost<Tokenizer>)
    requires
        super::contract::abstracts(st, old(t)@),
    ensures
        super::contract::abstracts(flush_and_return(st).0, final(t)@),
        tokens_view(final(out)@) == tokens_view(old(out)@) + flush_and_return(st).1,
{
    flush_exec(t, out, Ghost(st));
    t.state = return_state_state(&t.return_state);
}

} // verus!
