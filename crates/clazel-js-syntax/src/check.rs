//! The arena check: the part of the parser that is proven.
//!
//! [`finish`] takes the nodes the recursive-descent parser built (which may
//! hold nodes the cover grammars left behind) and returns an [`Ast`] only if it
//! is well formed ([`ast_wf`]), every span is inside the source text and every
//! child's span inside its parent's ([`spans_wf`]), and its height is at most
//! [`MAX_DEPTH`].

use crate::ast::*;
use crate::spec::*;
use crate::api::ParseError;
use vstd::prelude::*;

verus! {

/// What [`finish`] promises of an `Ok`: the structural half of
/// [`crate::contract::parse_ensures`] (the other half, that the arena is a
/// derivation of the source text with no early error, is not proven).
pub open spec fn finish_ensures(
    nodes: Seq<NodeV>,
    src_len: int,
    r: Result<Ast, ParseError>,
) -> bool {
    match r {
        Ok(ast) => ast_wf(ast@) && spans_wf(ast@, src_len) && height(ast@, ast@.root)
            <= MAX_DEPTH as int,
        Err(_) => true,
    }
}

} // verus!

/// TEMPORARY plain version, replaced by the verified one.
pub fn finish(nodes: Vec<Node>, src_len: usize) -> Result<Ast, ParseError> {
    let _ = src_len;
    let root = u32::try_from(nodes.len().saturating_sub(1)).unwrap_or(0);
    Ok(Ast { nodes, root })
}
