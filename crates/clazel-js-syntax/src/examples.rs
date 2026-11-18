//! A few small facts about the specification, proven: evidence that the
//! transcription accepts and rejects what the standard says, on inputs small
//! enough to write out. Positive and negative; the larger evidence is the
//! conformance suite and, in the second half of 7.3, the proofs about the parser.
//!
//! This is a module of its own for the reason `clazel-js-lexer`'s is.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A node with no children and no tokens of its own recorded: a leaf.
pub open spec fn node(kind: NodeKind, op: Op, start: int, end: int, children: Seq<int>) -> NodeV {
    NodeV { kind: kind, op: op, flag: false, start: start, end: end, children: children }
}

/// A punctuator token `text` of one code point at `start`.
pub open spec fn punct(text: u32, start: int) -> Tok {
    Tok {
        kind: TokKind::Punctuator,
        start: start,
        end: start + 1,
        text: seq![text],
        name: Seq::empty(),
        escaped: false,
        nl_before: false,
        legacy: false,
        bigint: false,
        invalid_escape: false,
        regexp_valid: false,
    }
}

/// §16.1 `Script : ScriptBody?`: the empty source text is a `Script`, with no
/// statements and no early error.
pub proof fn example_empty_script()
    ensures
        ({
            let a = AstV {
                nodes: seq![node(NodeKind::Script, Op::None, 0, 0, Seq::empty())],
                root: 0,
            };
            let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::None] };
            derives_root(a, ts, SourceGoal::Script) && early_errors_ok(a, ts, SourceGoal::Script)
        }),
{
    let a = AstV { nodes: seq![node(NodeKind::Script, Op::None, 0, 0, Seq::empty())], root: 0 };
    let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::None] };
    assert(ast_wf(a));
    assert(d(a, ts, 0, root_ctx(SourceGoal::Script), 0, 0));
    assert(derives_root(a, ts, SourceGoal::Script));
}

/// §14.4 `EmptyStatement : ;`: the source text `;` is a `Script` of one
/// `EmptyStatement`, whose span is the `;`.
pub proof fn example_empty_statement()
    ensures
        ({
            let a = AstV {
                nodes: seq![
                    node(NodeKind::EmptyStatement, Op::None, 0, 1, Seq::empty()),
                    node(NodeKind::Script, Op::None, 0, 1, seq![0int]),
                ],
                root: 1,
            };
            let ts = Stream { toks: seq![punct(0x3Bu32, 0)], gaps: seq![Ins::None, Ins::None] };
            derives_root(a, ts, SourceGoal::Script)
        }),
{
    let a = AstV {
        nodes: seq![
            node(NodeKind::EmptyStatement, Op::None, 0, 1, Seq::empty()),
            node(NodeKind::Script, Op::None, 0, 1, seq![0int]),
        ],
        root: 1,
    };
    let ts = Stream { toks: seq![punct(0x3Bu32, 0)], gaps: seq![Ins::None, Ins::None] };
    reveal_strlit(";");
    assert(";"@ =~= seq![';']);
    assert(has_parent(a, 0)) by {
        assert(a.nodes[1].children[0] == 0);
    }
    assert(ast_wf(a));
    assert(exists|x: int| 0 <= x < tn(ts) && #[trigger] ts.toks[x].end == a.nodes[0].end) by {
        assert(ts.toks[0].end == 1);
    }
    assert(ed(a, ts, 0, 0) == 1);
    assert(is_p(ts, 0, ";"@));
    assert(d(a, ts, 0, root_ctx(SourceGoal::Script), 0, 1));
    assert(dc(a, ts, 1, 0, root_ctx(SourceGoal::Script), 0, 1));
    let ks = a.nodes[1].children;
    assert(all_items(a, ks)) by {
        assert(ks[0] == 0);
    }
    reveal_with_fuel(dl, 2);
    assert(dl(a, ts, 1, ks, 0, root_ctx(SourceGoal::Script), 0, 1));
    assert(d(a, ts, 1, root_ctx(SourceGoal::Script), 0, 1));
    assert(derives_root(a, ts, SourceGoal::Script));
}

/// §13.13 `CoalesceExpression`: `a ?? b || c` is not derived. The left operand of
/// `||` is a `LogicalORExpression` or tighter, and a `CoalesceExpression` is not.
pub proof fn example_coalesce_does_not_mix_with_or()
    ensures
        ({
            let a = AstV {
                nodes: seq![
                    node(NodeKind::IdentifierReference, Op::None, 0, 1, Seq::empty()),
                    node(NodeKind::IdentifierReference, Op::None, 5, 6, Seq::empty()),
                    node(NodeKind::CoalesceExpression, Op::Coalesce, 0, 6, seq![0int, 1int]),
                    node(NodeKind::IdentifierReference, Op::None, 10, 11, Seq::empty()),
                ],
                root: 3,
            };
            !binary_operands_ok(a, NodeKind::LogicalORExpression, Op::LogicalOr, 2, 3)
                && binary_operands_ok(a, NodeKind::CoalesceExpression, Op::Coalesce, 0, 1)
        }),
{
    let a = AstV {
        nodes: seq![
            node(NodeKind::IdentifierReference, Op::None, 0, 1, Seq::empty()),
            node(NodeKind::IdentifierReference, Op::None, 5, 6, Seq::empty()),
            node(NodeKind::CoalesceExpression, Op::Coalesce, 0, 6, seq![0int, 1int]),
            node(NodeKind::IdentifierReference, Op::None, 10, 11, Seq::empty()),
        ],
        root: 3,
    };
    assert(lvl(a, 2) == 0);
    assert(lvl(a, 0) == 17);
    assert(lvl(a, 3) == 17);
}

/// §13.6 `ExponentiationExpression`: `-a ** b` is not derived: the left operand
/// of `**` is an `UpdateExpression`, and a `UnaryExpression` is not.
pub proof fn example_unary_is_not_an_exponentiation_base()
    ensures
        ({
            let a = AstV {
                nodes: seq![
                    node(NodeKind::IdentifierReference, Op::None, 1, 2, Seq::empty()),
                    node(NodeKind::UnaryExpression, Op::Minus, 0, 2, seq![0int]),
                    node(NodeKind::IdentifierReference, Op::None, 6, 7, Seq::empty()),
                ],
                root: 2,
            };
            !binary_operands_ok(a, NodeKind::ExponentiationExpression, Op::Exp, 1, 2)
        }),
{
    let a = AstV {
        nodes: seq![
            node(NodeKind::IdentifierReference, Op::None, 1, 2, Seq::empty()),
            node(NodeKind::UnaryExpression, Op::Minus, 0, 2, seq![0int]),
            node(NodeKind::IdentifierReference, Op::None, 6, 7, Seq::empty()),
        ],
        root: 2,
    };
    assert(lvl(a, 1) == 12);
}

/// §14.9.1: a `break` that is not in an iteration statement or a `switch` is an
/// early error, in a program with no enclosing statement.
pub proof fn example_break_outside_loop_is_an_early_error()
    ensures
        ({
            let a = AstV {
                nodes: seq![
                    node(NodeKind::Absent, Op::None, 5, 5, Seq::empty()),
                    node(NodeKind::BreakStatement, Op::None, 0, 5, seq![0int]),
                    node(NodeKind::Script, Op::None, 0, 5, seq![1int]),
                ],
                root: 2,
            };
            let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::None] };
            !early_local(a, ts, 1, root_env(a, ts, SourceGoal::Script))
        }),
{
    let a = AstV {
        nodes: seq![
            node(NodeKind::Absent, Op::None, 5, 5, Seq::empty()),
            node(NodeKind::BreakStatement, Op::None, 0, 5, seq![0int]),
            node(NodeKind::Script, Op::None, 0, 5, seq![1int]),
        ],
        root: 2,
    };
    let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::None] };
    let env = root_env(a, ts, SourceGoal::Script);
    assert(!env.in_breakable);
}

/// §14.11.1 `with` in strict mode code is an early error; the same statement in
/// sloppy mode code is not.
pub proof fn example_with_is_an_early_error_in_strict_mode_only()
    ensures
        ({
            let a = AstV {
                nodes: seq![
                    node(NodeKind::EmptyStatement, Op::None, 0, 1, Seq::empty()),
                    node(NodeKind::EmptyStatement, Op::None, 1, 2, Seq::empty()),
                    node(NodeKind::WithStatement, Op::None, 0, 2, seq![0int, 1int]),
                ],
                root: 2,
            };
            let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::None] };
            let strict = EarlyEnv { strict: true, ..root_env(a, ts, SourceGoal::Script) };
            let sloppy = EarlyEnv { strict: false, ..root_env(a, ts, SourceGoal::Script) };
            !early_local(a, ts, 2, strict) && early_local(a, ts, 2, sloppy)
        }),
{
    let a = AstV {
        nodes: seq![
            node(NodeKind::EmptyStatement, Op::None, 0, 1, Seq::empty()),
            node(NodeKind::EmptyStatement, Op::None, 1, 2, Seq::empty()),
            node(NodeKind::WithStatement, Op::None, 0, 2, seq![0int, 1int]),
        ],
        root: 2,
    };
    let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::None] };
    let strict = EarlyEnv { strict: true, ..root_env(a, ts, SourceGoal::Script) };
    let sloppy = EarlyEnv { strict: false, ..root_env(a, ts, SourceGoal::Script) };
    assert(!is_labelled_function(a, 1));
}

/// §12.10.1 rule 1 and §14.7.2: a `;` inserted after the `)` of a `do`-`while`
/// ends the statement in a range that has no token for it.
pub proof fn example_inserted_semicolon_consumes_no_token()
    ensures
        ({
            let ts = Stream { toks: Seq::empty(), gaps: seq![Ins::DoWhile] };
            semi(ts, 0, 0, true) && !semi(ts, 0, 0, false)
        }),
{
}

/// The limit of item 7.3 is a number, and a leaf is one node high.
pub proof fn example_depth_limit()
    ensures
        MAX_DEPTH == 1024,
        ({
            let a = AstV {
                nodes: seq![node(NodeKind::NullLiteral, Op::None, 0, 4, Seq::empty())],
                root: 0,
            };
            height(a, 0) == 1
        }),
{
    let a = AstV { nodes: seq![node(NodeKind::NullLiteral, Op::None, 0, 4, Seq::empty())], root: 0 };
    assert(max_height(a, 0, a.nodes[0].children, 0) == 0);
}

/// An `IdentifierName` token of the one-letter name `a` at `start`.
pub open spec fn name_a(start: int) -> Tok {
    Tok {
        kind: TokKind::IdentifierName,
        start: start,
        end: start + 1,
        text: seq![0x61u32],
        name: seq![0x61u32],
        escaped: false,
        nl_before: false,
        legacy: false,
        bigint: false,
        invalid_escape: false,
        regexp_valid: false,
    }
}

/// The module of `export {a}; export {a}`: two `ExportNamed` items.
pub open spec fn module_export_a_twice() -> AstV {
    AstV {
        nodes: seq![
            node(NodeKind::IdentifierName, Op::None, 8, 9, Seq::empty()),
            node(NodeKind::Absent, Op::None, 9, 9, Seq::empty()),
            node(NodeKind::ExportSpecifier, Op::None, 8, 9, seq![0int, 1int]),
            node(NodeKind::NamedExports, Op::None, 7, 10, seq![2int]),
            node(NodeKind::ExportDeclaration, Op::ExportNamed, 0, 11, seq![3int]),
            node(NodeKind::IdentifierName, Op::None, 27, 28, Seq::empty()),
            node(NodeKind::Absent, Op::None, 28, 28, Seq::empty()),
            node(NodeKind::ExportSpecifier, Op::None, 27, 28, seq![5int, 6int]),
            node(NodeKind::NamedExports, Op::None, 26, 29, seq![7int]),
            node(NodeKind::ExportDeclaration, Op::ExportNamed, 19, 30, seq![8int]),
            node(NodeKind::Module, Op::None, 0, 30, seq![4int, 9int]),
        ],
        root: 10,
    }
}

/// §16.2.1.1: a name exported twice is an early error: `export {a}; export {a}`
/// exports `a` twice.
pub proof fn example_duplicate_export_is_an_early_error()
    ensures
        ({
            let a = module_export_a_twice();
            let ts = Stream { toks: seq![name_a(8), name_a(27)], gaps: seq![Ins::None, Ins::None, Ins::None] };
            !exports_early(a, ts, 10, a.nodes[10].children)
        }),
{
    let a = module_export_a_twice();
    let ts = Stream { toks: seq![name_a(8), name_a(27)], gaps: seq![Ins::None, Ins::None, Ins::None] };
    assert(exists|x: int| 0 <= x < tn(ts) && ts.toks[x].start == a.nodes[0].start) by {
        assert(ts.toks[0].start == 8);
    }
    assert(exists|x: int| 0 <= x < tn(ts) && ts.toks[x].start == a.nodes[5].start) by {
        assert(ts.toks[1].start == 27);
    }
    assert(node_tok(a, ts, 0) == ts.toks[0]);
    assert(node_tok(a, ts, 5) == ts.toks[1]);
    assert(name_of(a, ts, 0) == seq![0x61u32]);
    assert(name_of(a, ts, 5) == seq![0x61u32]);
    let ks = a.nodes[10].children;
    reveal_with_fuel(exported_names_list, 3);
    let n4 = exported_names_item(a, ts, 4);
    let n9 = exported_names_item(a, ts, 9);
    assert(n4 =~= seq![seq![0x61u32]]);
    assert(n9 =~= seq![seq![0x61u32]]);
    let all = exported_names_list(a, ts, ks, 0);
    assert(all =~= seq![seq![0x61u32], seq![0x61u32]]);
    example_repeated_export_names_are_not_unique();
    assert(all == seq![seq![0x61u32], seq![0x61u32]]);
}

/// §16.2.1.1: the same name twice is a duplicate.
pub proof fn example_repeated_export_names_are_not_unique()
    ensures
        !exported_names_unique(seq![seq![0x61u32], seq![0x61u32]]),
{
    let ns = seq![seq![0x61u32], seq![0x61u32]];
    assert(ns[0] == ns[1]);
    assert(name_in(ns, ns[0], 1));
    assert(names_repeat_from(ns, 0));
}

/// §16.2.2.1: a string that holds a lone surrogate is not well formed; a
/// surrogate pair is.
pub proof fn example_lone_surrogate_is_ill_formed()
    ensures
        !well_formed_utf16(seq![0xD800u32]),
        !well_formed_utf16(seq![0xDC00u32]),
        !surrogate_ok_at(seq![0xDC00u32], 0),
        well_formed_utf16(seq![0xD83Du32, 0xDE00u32]),
{
    let lone = seq![0xD800u32];
    assert(!surrogate_ok_at(lone, 0));
    let low = seq![0xDC00u32];
    assert(!surrogate_ok_at(low, 0));
    let pair = seq![0xD83Du32, 0xDE00u32];
    assert forall|k: int| 0 <= k < pair.len() implies #[trigger] surrogate_ok_at(pair, k) by {
        if k == 0 {
        } else {
            assert(k == 1);
        }
    }
}

} // verus!
