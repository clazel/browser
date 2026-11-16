//! The mapping from the spec's parse results to the independent transcription's,
//! by which [`super::equiv_parser`] states its theorems: the spec's `Seq<u32>` strings
//! are [`ints`], its tokens [`tok_of`], and its component values, declarations and
//! rules are mapped by the functions here, each one a structural recursion.

use super::equiv_base::*;
use super::equiv_tokenizer::*;
use super::parse::*;
use super::*;
use crate::parser::spec as ps;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A component value of the spec as one of the independent transcription.
pub open spec fn cv_of(v: ps::ComponentValue) -> ICv
    decreases v,
{
    match v {
        ps::ComponentValue::Token { token } => ICv::Token(tok_of(token)),
        ps::ComponentValue::Function { name, value } => ICv::Function(ints(name), cvs_of(value)),
        ps::ComponentValue::SimpleBlock { associated_token, value } => ICv::Block(
            tok_of(associated_token),
            cvs_of(value),
        ),
    }
}

/// A list of component values.
pub open spec fn cvs_of(vs: Seq<ps::ComponentValue>) -> Seq<ICv>
    decreases vs,
{
    Seq::new(
        vs.len(),
        |i: int| if 0 <= i < vs.len() { cv_of(vs[i]) } else { ICv::Token(ITok::Eof) },
    )
}

/// A declaration.
pub open spec fn decl_of(d: ps::Declaration) -> IDecl {
    IDecl {
        name: ints(d.name),
        value: cvs_of(d.value),
        important: d.important,
        original_text: match d.original_text {
            Some(text) => Some(ints(text)),
            None => None,
        },
    }
}

/// A list of declarations.
pub open spec fn decls_of(ds: Seq<ps::Declaration>) -> Seq<IDecl> {
    Seq::new(ds.len(), |i: int| decl_of(ds[i]))
}

/// A rule of the spec.
pub open spec fn rule_of(r: ps::Rule) -> IRule
    decreases r,
{
    match r {
        ps::Rule::AtRule { name, prelude, child_rules } => IRule::AtRule {
            name: ints(name),
            prelude: cvs_of(prelude),
            block: match child_rules {
                Some(items) => Some(Seq::new(items.len(), |i: int| if 0 <= i < items.len() { item_of(items[i]) } else { IItem::Decls(seq![]) })),
                None => None,
            },
        },
        ps::Rule::QualifiedRule { prelude, declarations, child_rules } => IRule::QualifiedRule {
            prelude: cvs_of(prelude),
            decls: decls_of(declarations),
            children: Seq::new(child_rules.len(), |i: int| if 0 <= i < child_rules.len() { rule_of(child_rules[i]) } else { IRule::NestedDeclarations { decls: seq![] } }),
        },
        ps::Rule::NestedDeclarationsRule { declarations } => IRule::NestedDeclarations {
            decls: decls_of(declarations),
        },
    }
}

/// An item of the list "consume a block's contents" returns.
pub open spec fn item_of(b: ps::BlockItem) -> IItem
    decreases b,
{
    match b {
        ps::BlockItem::Rule { rule } => IItem::Rule(rule_of(rule)),
        ps::BlockItem::Declarations { declarations } => IItem::Decls(decls_of(declarations)),
    }
}

} // verus!
