//! The executable parser: [`parse`].
//!
//! The recursive-descent parser ([`crate::parser`] and its grammar modules)
//! proposes an arena; [`compact`] drops the nodes the cover grammars left
//! behind; [`crate::early`] rejects what §16's early errors reject;
//! [`crate::check::finish`] (proven) accepts the arena only if it is well
//! formed, inside the source text and within [`MAX_DEPTH`].

use crate::api::ParseError;
use crate::arena_d::{Derivation, check_derivation_canon};
use crate::ast::{Ast, Node, NodeKind};
use crate::parser::Parser;
use crate::spec::SourceGoal;

/// Parses `src` (code points) as a `Script` or `Module`.
///
/// Total: every `src` and `goal` has a result. See the crate header for what
/// of [`crate::contract::parse_ensures`] is proven and what is only tested.
pub fn parse(src: &[u32], goal: SourceGoal) -> Result<Ast, ParseError> {
    parse_checked(src, goal).map(|(ast, _)| ast)
}

/// [`parse`], and what [`crate::arena_d::check_derivation_canon`] found of the arena:
/// `Failed` (a covered node the grammar does not derive) is an error, so an `Ok`
/// with `Verified` carries a proof of `spec::derives_root` (modulo the lexer), and
/// with `Unsupported` is only tested.
pub fn parse_checked(src: &[u32], goal: SourceGoal) -> Result<(Ast, Derivation), ParseError> {
    parse_checked_early(src, goal).map(|(ast, d, _)| (ast, d))
}

/// [`parse_checked`], and what [`crate::arena_early::check_early_canon`] found of the arena:
/// `Verified` (the third component) means the arena has no early error
/// (`spec::early_errors_ok`), so `Verified` in both means `spec::is_valid_parse` holds, modulo
/// the assumptions of [`crate::arena_d`]; `Unsupported` that a rule or node kind is not covered.
pub fn parse_checked_early(
    src: &[u32],
    goal: SourceGoal,
) -> Result<(Ast, Derivation, Derivation), ParseError> {
    // Recursion is bounded by `MAX_DEPTH` nested nodes, each a few frames; a
    // thread with room for that is cheaper than a stack overflow. Short
    // sources cannot nest that deep.
    const SMALL: usize = 64;
    if src.len() <= SMALL {
        return parse_inner(src, goal);
    }
    let run = || parse_inner(src, goal);
    std::thread::scope(|s| {
        match std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(s, run)
        {
            Ok(h) => h.join().unwrap_or(Err(ParseError::Syntax)),
            // No thread to be had: parse here, on the stack this thread has.
            Err(_) => run(),
        }
    })
}

fn parse_inner(
    src: &[u32],
    goal: SourceGoal,
) -> Result<(Ast, Derivation, Derivation), ParseError> {
    let module = goal == SourceGoal::Module;
    let mut p = Parser::new(src, module)?;
    let root = p.parse_program()?;
    if p.reachable_bad(root) {
        return Err(ParseError::Syntax);
    }
    let nodes = compact(std::mem::take(&mut p.nodes), root);
    // The arena check first: it bounds the height, which bounds the recursion of
    // the early errors.
    let ast = crate::check::finish(nodes, src.len())?;
    crate::early::check(src, &ast, module)?;
    let mut gaps = vec![crate::spec::Ins::None; p.rec.len().saturating_add(1)];
    for (at, ins) in p.gap_events.iter() {
        if let Some(g) = gaps.get_mut(*at) {
            *g = *ins;
        }
    }
    let d = check_derivation_canon(src, &ast.nodes, &p.rec, &gaps, module);
    if d == Derivation::Failed {
        return Err(ParseError::Syntax);
    }
    let early = crate::arena_early::check_early_canon(src, &ast.nodes, &p.rec, &gaps, module);
    Ok((ast, d, early))
}

/// The nodes reachable from `root`, in their original order, renumbered. The
/// order keeps every child before its parent.
pub fn compact(nodes: Vec<Node>, root: u32) -> Vec<Node> {
    let mut keep = vec![false; nodes.len()];
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        let Some(k) = keep.get_mut(id as usize) else {
            continue;
        };
        if *k {
            continue;
        }
        *k = true;
        if let Some(n) = nodes.get(id as usize) {
            stack.extend(n.children.iter().copied());
        }
    }
    let mut remap = vec![u32::MAX; nodes.len()];
    let mut next: u32 = 0;
    for (i, k) in keep.iter().enumerate() {
        if *k {
            if let Some(r) = remap.get_mut(i) {
                *r = next;
            }
            next = next.saturating_add(1);
        }
    }
    let mut out = Vec::new();
    for (i, mut n) in nodes.into_iter().enumerate() {
        if keep.get(i).copied().unwrap_or(false) {
            for c in n.children.iter_mut() {
                *c = remap.get(*c as usize).copied().unwrap_or(u32::MAX);
            }
            out.push(n);
        }
    }
    out
}

/// Whether the node is a root kind.
pub fn is_root_kind(k: NodeKind) -> bool {
    matches!(k, NodeKind::Script | NodeKind::Module)
}
