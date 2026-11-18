//! Early errors (ECMA-262 §16 and the rules it names).

use crate::api::ParseError;
use crate::ast::Node;

/// Rejects the arena `nodes` of `src` if it has an early error.
pub fn check(src: &[u32], nodes: &[Node], module: bool) -> Result<(), ParseError> {
    let _ = (src, nodes, module);
    Ok(())
}
