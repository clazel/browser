//! Kani harnesses for `clazel-js-syntax` (Tier 1): the small total functions
//! and the loops over bounded inputs, checked for panics, overflow and
//! out-of-bounds access with symbolic inputs.
//!
//! Not harnessed, because CBMC does not finish in reasonable time (measured):
//! `token::lex` on one symbolic code point, `exec::parse` on one code point,
//! `Parser::new`/`bump`, and `name_is_reserved`, `name_is_reserved_always`,
//! `name_is_strict_reserved` (each scans the 63-word keyword table). The
//! recursive-descent parser itself is covered by the Verus proofs and tests,
//! not by these harnesses.

use crate::ast::{Node, NodeKind, Op};
use crate::check::finish;
use crate::exec::{compact, is_root_kind};
use crate::parser::Cx;
use crate::token::*;
use clazel_js_lexer::spec::{ElementKind, TemplateKind};

fn node(kind: NodeKind, start: usize, end: usize, children: Vec<u32>) -> Node {
    Node {
        kind,
        op: Op::None,
        flag: false,
        start,
        end,
        children,
    }
}

#[kani::proof]
#[kani::unwind(8)]
fn name_is_total() {
    let a: [u32; 3] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 3);
    let _ = name_is(&a[..n], "await");
}

#[kani::proof]
fn tok_predicates_total() {
    let kinds = [
        ElementKind::IdentifierName,
        ElementKind::Punctuator,
        ElementKind::Template(TemplateKind::Head),
    ];
    let i: usize = kani::any();
    kani::assume(i < 3);
    let t = Tok {
        kind: kinds[i],
        start: kani::any(),
        end: kani::any(),
        nl: kani::any(),
        eof: kani::any(),
        s: "(",
        name: Vec::new(),
        escaped: kani::any(),
        bigint: kani::any(),
        legacy: kani::any(),
        invalid_escape: kani::any(),
    };
    let _ = (t.is_p("("), t.is_w("("), t.is_name());
    let _ = t.is_tpl(TemplateKind::Head);
    let _ = dtok_of(&t);
}

#[kani::proof]
#[kani::unwind(4)]
fn compact_one_node() {
    let c: u32 = kani::any();
    let root: u32 = kani::any();
    kani::assume(root < 2);
    let nodes = vec![node(NodeKind::Absent, 0, 0, vec![c])];
    let out = compact(nodes, root);
    assert!(out.len() <= 1);
}

#[kani::proof]
#[kani::unwind(5)]
fn finish_two_nodes() {
    let c: u32 = kani::any();
    let len: usize = kani::any();
    let (s0, e0, s1, e1): (usize, usize, usize, usize) =
        (kani::any(), kani::any(), kani::any(), kani::any());
    let root_first: bool = kani::any();
    let k0 = if root_first {
        NodeKind::Script
    } else {
        NodeKind::Absent
    };
    let nodes = vec![
        node(k0, s0, e0, Vec::new()),
        node(NodeKind::Script, s1, e1, vec![c]),
    ];
    let _ = finish(nodes, len);
}

#[kani::proof]
fn is_root_kind_total() {
    let _ = is_root_kind(NodeKind::Script);
}

#[kani::proof]
fn parser_cx() {
    let cx = Cx {
        y: kani::any(),
        a: kani::any(),
        i: kani::any(),
        r: kani::any(),
    };
    let _ = cx.with_in(kani::any());
}

#[kani::proof]
#[kani::unwind(6)]
fn has_legacy_escape_total() {
    let a: [u32; 4] = kani::any();
    let n: usize = kani::any();
    kani::assume(n <= 4);
    let _ = has_legacy_escape(&a[..n]);
}
