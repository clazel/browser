//! RFC 8446 §4.2's rules on an extension block: the crate's
//! `exts_unique`, `extension_allowed`/`all_allowed` (the table) and the
//! offered-type rule proven equal to the clean-room transcription's
//! `has_duplicate_extension`, `extension_table`/`any_not_specified` and
//! `any_not_offered`, for every block and message: [`theorem_extension_rules_equivalence`].
//!
//! What is not compared: the crate's `ext_body_ok` (the syntax of the bodies
//! of extensions it reads). The transcription decodes only the bodies it acts
//! on; the rest is waiting on a separate clean-room transcription (see the
//! PR), and the step theorems state `all_bodies_ok` as a temporary domain
//! condition.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The crate's message kind as the transcription's table column.
pub open spec fn table_message(m: crate::spec::MsgKind) -> crate::transcription::extensions::TableMessage {
    match m {
        crate::spec::MsgKind::Ch => crate::transcription::extensions::TableMessage::Ch,
        crate::spec::MsgKind::Sh => crate::transcription::extensions::TableMessage::Sh,
        crate::spec::MsgKind::Ee => crate::transcription::extensions::TableMessage::Ee,
        crate::spec::MsgKind::Ct => crate::transcription::extensions::TableMessage::Ct,
        crate::spec::MsgKind::Cr => crate::transcription::extensions::TableMessage::Cr,
        crate::spec::MsgKind::Nst => crate::transcription::extensions::TableMessage::Nst,
        crate::spec::MsgKind::Hrr => crate::transcription::extensions::TableMessage::Hrr,
    }
}

/// A list of `u16` as the transcription's numbers.
pub open spec fn nats(values: Seq<u16>) -> Seq<nat> {
    values.map_values(|v: u16| v as nat)
}

/// §4.2's table, row for row: an extension is allowed in a message on the
/// crate's side exactly when the transcription does not find it recognized
/// but not specified there.
pub proof fn lemma_table(t: u16, m: crate::spec::MsgKind)
    ensures
        crate::spec::extension_allowed(t, m)
            == !crate::transcription::extensions::recognized_but_not_specified(t as nat, table_message(m)),
{
    reveal_with_fuel(crate::transcription::presentation::list_has, 4);
    let tm = table_message(m);
    assert(seq![tm].subrange(1, 1) =~= Seq::<crate::transcription::extensions::TableMessage>::empty());
}

/// `list_has` over a mapped list is `member`/`has` over the original.
pub proof fn lemma_list_has_nats(values: Seq<u16>, v: u16)
    ensures
        crate::transcription::presentation::list_has(nats(values), v as nat) == crate::auth::spec::member(values, v),
    decreases values.len(),
{
    if values.len() > 0 {
        assert(nats(values).subrange(1, nats(values).len() as int) =~= nats(values.skip(1)));
        lemma_list_has_nats(values.skip(1), v);
    }
}

/// The types of a block, mapped.
pub proof fn lemma_types(es: Seq<crate::spec::Ext>)
    ensures
        crate::transcription::extensions::extension_types(super::messages::exts_view(es))
            == es.map_values(|e: crate::spec::Ext| e.etype as nat),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_types(es.skip(1));
    }
    assert(crate::transcription::extensions::extension_types(v) =~= es.map_values(|e: crate::spec::Ext| e.etype as nat));
}

/// `has_ext` is `list_has` of the mapped types.
pub proof fn lemma_has_ext(es: Seq<crate::spec::Ext>, t: u16)
    ensures
        crate::spec::has_ext(es, t)
            == crate::transcription::presentation::list_has(
                crate::transcription::extensions::extension_types(super::messages::exts_view(es)), t as nat),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_has_ext(es.skip(1), t);
        let types = crate::transcription::extensions::extension_types(v);
        assert(types.subrange(1, types.len() as int)
            =~= crate::transcription::extensions::extension_types(super::messages::exts_view(es.skip(1)))) by {
            lemma_types(es);
            lemma_types(es.skip(1));
        }
    }
}

/// §4.2: no duplicates on one side exactly when none on the other.
pub proof fn lemma_unique(es: Seq<crate::spec::Ext>)
    ensures
        crate::spec::exts_unique(es) == !crate::transcription::extensions::has_duplicate_extension(super::messages::exts_view(es)),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_unique(es.skip(1));
        lemma_has_ext(es.skip(1), es[0].etype);
    }
}

/// §4.2's table over a block.
pub proof fn lemma_all_allowed(es: Seq<crate::spec::Ext>, m: crate::spec::MsgKind)
    ensures
        crate::spec::all_allowed(es, m)
            == !crate::transcription::extensions::any_not_specified(super::messages::exts_view(es), table_message(m)),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_all_allowed(es.skip(1), m);
        lemma_table(es[0].etype, m);
    }
}

/// §4.2: every response was offered (the auth layer's rule, for any message
/// but a HelloRetryRequest, whose cookie is exempt).
pub proof fn lemma_offered(es: Seq<crate::spec::Ext>, offers: Seq<u16>, m: crate::spec::MsgKind)
    requires m != crate::spec::MsgKind::Hrr,
    ensures
        crate::auth::spec::extensions_offered(es, offers)
            == !crate::transcription::extensions::any_not_offered(super::messages::exts_view(es), nats(offers), table_message(m)),
    decreases es.len(),
{
    let v = super::messages::exts_view(es);
    if es.len() > 0 {
        assert(v.subrange(1, v.len() as int) =~= super::messages::exts_view(es.skip(1)));
        lemma_offered(es.skip(1), offers, m);
        lemma_list_has_nats(offers, es[0].etype);
    }
}

/// RFC 8446 §4.2, for every extension block, message and offer: the
/// crate's duplicate, table and offered-type rules are the transcription's.
pub proof fn theorem_extension_rules_equivalence()
    ensures
        forall|es: Seq<crate::spec::Ext>| #[trigger] crate::spec::exts_unique(es)
            == !crate::transcription::extensions::has_duplicate_extension(super::messages::exts_view(es)),
        forall|t: u16, m: crate::spec::MsgKind| #[trigger] crate::spec::extension_allowed(t, m)
            == !crate::transcription::extensions::recognized_but_not_specified(t as nat, table_message(m)),
        forall|es: Seq<crate::spec::Ext>, m: crate::spec::MsgKind| #[trigger] crate::spec::all_allowed(es, m)
            == !crate::transcription::extensions::any_not_specified(super::messages::exts_view(es), table_message(m)),
        forall|es: Seq<crate::spec::Ext>, offers: Seq<u16>, m: crate::spec::MsgKind| m != crate::spec::MsgKind::Hrr ==>
            #[trigger] crate::auth::spec::extensions_offered(es, offers)
                == !crate::transcription::extensions::any_not_offered(super::messages::exts_view(es), nats(offers), #[trigger] table_message(m)),
{
    assert forall|es: Seq<crate::spec::Ext>| #[trigger] crate::spec::exts_unique(es)
        == !crate::transcription::extensions::has_duplicate_extension(super::messages::exts_view(es)) by { lemma_unique(es); }
    assert forall|t: u16, m: crate::spec::MsgKind| #[trigger] crate::spec::extension_allowed(t, m)
        == !crate::transcription::extensions::recognized_but_not_specified(t as nat, table_message(m)) by { lemma_table(t, m); }
    assert forall|es: Seq<crate::spec::Ext>, m: crate::spec::MsgKind| #[trigger] crate::spec::all_allowed(es, m)
        == !crate::transcription::extensions::any_not_specified(super::messages::exts_view(es), table_message(m)) by { lemma_all_allowed(es, m); }
    assert forall|es: Seq<crate::spec::Ext>, offers: Seq<u16>, m: crate::spec::MsgKind| m != crate::spec::MsgKind::Hrr implies
        #[trigger] crate::auth::spec::extensions_offered(es, offers)
            == !crate::transcription::extensions::any_not_offered(super::messages::exts_view(es), nats(offers), #[trigger] table_message(m))
    by { lemma_offered(es, offers, m); }
}

} // verus!
