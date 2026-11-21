//! A proven check of the early errors over a whole arena (item 7.3): [`check_early`]
//! carries an [`EEnv`] per node (the executable form of `spec::EarlyEnv`), checks that
//! each node's is the one `spec::child_env` gives it from its parent's, and that
//! `spec::early_local` holds at each node, bottom-up. It returns `Verified` only if
//! `spec::early_errors_ok` holds.
//!
//! **Covered.** The environment: every node kind whose `child_env` arm is the default
//! (`[~Tagged]`) or one of the loop, `switch`, object literal, tagged template and
//! template arms, and the function declarations and expressions of every kind, arrow
//! functions and methods of object literals (`env_fn`, and `has_use_strict` of the body,
//! [`crate::arena_names::use_strict_exec`]); the `labels` and `privates` of the
//! environment are empty, so a labelled statement or a class makes the result `Unsupported`.
//! Function code: `function_early` ([`crate::arena_names::function_early_exec`]: Use Strict
//! Directive with non-simple parameters, duplicate parameters, from the BoundNames of
//! [`crate::arena_names::bound_names_all`]) and the statement list of a `FunctionBody`
//! that declares nothing lexically.
//! The rules of `early_local`: every kind with no rule (the `_ => true` arm);
//! `NumericLiteral` and `StringLiteral` (strict mode legacy forms); the three identifier
//! kinds (§13.1.1: strict reserved words, `eval`, `arguments`, `yield`, `await`, the
//! reserved words, `arguments` in field initializers); `TemplateElement`;
//! `SuperProperty`, `SuperCall`, `NewTarget`, `ImportMeta`; `YieldExpression` and
//! `AwaitExpression`; `MemberExpression` (not `.#x`), `OptionalChain` (not `?.#x` or a
//! template), `RelationalExpression` (not `#x in`), `UnaryExpression` (not `delete`);
//! `UpdateExpression` and `AssignmentExpression` with a `~simple~` target (members,
//! `super` properties, identifiers other than strict `eval` and `arguments`, through
//! parentheses) or an assignment pattern; `if`, `while`, `do`-`while`, `with` (no labelled
//! function as the body; no `with`, no function body of an `if` in strict mode); `for ( ; ; )`
//! without a lexical declaration; unlabelled `break` and `continue`; the statement lists
//! of a block and a script whose items declare nothing lexically (so
//! `LexicallyDeclaredNames` is empty).
//!
//! **Not covered** (the result is `Unsupported`): everything else, notably
//! class code, labels, lexical declarations, `for`-`in`/`of`, `switch`, `try`
//! (`catch` parameters), regular expression literals (`regexp_valid` is item 7.10's),
//! private names, a Use Strict Directive in a script, and `Module` roots.
//!
//! **Assumptions**, those of [`crate::arena_d`]: the executable tokens are the
//! specification's (`dtok_matches`, which now also covers `legacy`, `invalid_escape`
//! and `name`, the lexer's contract of item 7.2).

use crate::arena_d::*;
use crate::arena_names::*;
use crate::ast::*;
use crate::spec::*;
use vstd::prelude::*;

verus! {

/// The executable tokens are the specification's stream `ts`.
pub open spec fn toks_match(src: Seq<u32>, toks: Seq<DTok>, ts: Stream) -> bool {
    toks.len() == ts.toks.len() && (forall|k: int|
        0 <= k < toks.len() ==> dtok_matches(src, toks[k], #[trigger] ts.toks[k]))
}

/// The tokens start at increasing positions, so a start names one token.
pub open spec fn starts_inc(ts: Stream) -> bool {
    forall|x: int, y: int|
        0 <= x < y < tn(ts) ==> (#[trigger] ts.toks[x]).start < (#[trigger] ts.toks[y]).start
}

/// The first token of node `n` is `ts.toks[x]`.
pub(crate) proof fn lemma_node_tok_at(a: AstV, ts: Stream, n: int, x: int)
    requires
        starts_inc(ts),
        0 <= n < a.nodes.len(),
        0 <= x < tn(ts),
        ts.toks[x].start == a.nodes[n].start,
    ensures
        node_tok(a, ts, n) == ts.toks[x],
{
    assert(exists|y: int| 0 <= y < tn(ts) && ts.toks[y].start == a.nodes[n].start);
    let y = choose|y: int| 0 <= y < tn(ts) && ts.toks[y].start == a.nodes[n].start;
    if y < x {
        assert(ts.toks[y].start < ts.toks[x].start);
    }
    if y > x {
        assert(ts.toks[x].start < ts.toks[y].start);
    }
}

/// The words of the identifier rules, as code points.
proof fn lemma_words_early()
    ensures
        sv("yield"@) =~= seq![0x79u32, 0x69, 0x65, 0x6C, 0x64],
        sv("await"@) =~= seq![0x61u32, 0x77, 0x61, 0x69, 0x74],
        sv("arguments"@) =~= seq![0x61u32, 0x72, 0x67, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x73],
        sv("eval"@) =~= seq![0x65u32, 0x76, 0x61, 0x6C],
        sv("implements"@) =~= seq![0x69u32, 0x6D, 0x70, 0x6C, 0x65, 0x6D, 0x65, 0x6E, 0x74, 0x73],
        sv("interface"@) =~= seq![0x69u32, 0x6E, 0x74, 0x65, 0x72, 0x66, 0x61, 0x63, 0x65],
        sv("let"@) =~= seq![0x6Cu32, 0x65, 0x74],
        sv("package"@) =~= seq![0x70u32, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65],
        sv("private"@) =~= seq![0x70u32, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65],
        sv("protected"@) =~= seq![0x70u32, 0x72, 0x6F, 0x74, 0x65, 0x63, 0x74, 0x65, 0x64],
        sv("public"@) =~= seq![0x70u32, 0x75, 0x62, 0x6C, 0x69, 0x63],
        sv("static"@) =~= seq![0x73u32, 0x74, 0x61, 0x74, 0x69, 0x63],
{
    reveal_strlit("yield");
    reveal_strlit("await");
    reveal_strlit("arguments");
    reveal_strlit("eval");
    reveal_strlit("implements");
    reveal_strlit("interface");
    reveal_strlit("let");
    reveal_strlit("package");
    reveal_strlit("private");
    reveal_strlit("protected");
    reveal_strlit("public");
    reveal_strlit("static");
    assert("yield"@ =~= seq!['y', 'i', 'e', 'l', 'd']);
    assert("await"@ =~= seq!['a', 'w', 'a', 'i', 't']);
    assert("arguments"@ =~= seq!['a', 'r', 'g', 'u', 'm', 'e', 'n', 't', 's']);
    assert("eval"@ =~= seq!['e', 'v', 'a', 'l']);
    assert("implements"@ =~= seq!['i', 'm', 'p', 'l', 'e', 'm', 'e', 'n', 't', 's']);
    assert("interface"@ =~= seq!['i', 'n', 't', 'e', 'r', 'f', 'a', 'c', 'e']);
    assert("let"@ =~= seq!['l', 'e', 't']);
    assert("package"@ =~= seq!['p', 'a', 'c', 'k', 'a', 'g', 'e']);
    assert("private"@ =~= seq!['p', 'r', 'i', 'v', 'a', 't', 'e']);
    assert("protected"@ =~= seq!['p', 'r', 'o', 't', 'e', 'c', 't', 'e', 'd']);
    assert("public"@ =~= seq!['p', 'u', 'b', 'l', 'i', 'c']);
    assert("static"@ =~= seq!['s', 't', 'a', 't', 'i', 'c']);
}

/// Two slices of code points are the same.
pub(crate) fn seq_eq(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ =~= b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            forall|q: int| 0 <= q < i ==> a@[q] == b@[q],
        decreases a.len() - i,
    {
        let (x, y) = match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => (*x, *y),
            _ => {
                return false;
            },
        };
        if x != y {
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

/// The index of the reserved word `name` is, if it is one.
fn reserved_of(name: &[u32]) -> (r: Option<usize>)
    ensures
        match r {
            Some(w) => w < 38 && name@ =~= reserved_chars(w as int),
            None => forall|w: int| 0 <= w < 38 ==> !(name@ =~= #[trigger] reserved_chars(w)),
        },
{
    let mut w: usize = 0;
    while w < 38
        invariant
            w <= 38,
            forall|q: int| 0 <= q < w ==> !(name@ =~= #[trigger] reserved_chars(q)),
        decreases 38 - w,
    {
        let c = reserved_slice(w);
        if seq_eq(name, c) {
            return Some(w);
        }
        w = w.saturating_add(1);
    }
    None
}

// ---------------------------------------------------------------------
// The environment.
// ---------------------------------------------------------------------

/// The facts about the position of a node that the checked early errors read: the
/// executable form of `spec::EarlyEnv` with no labels and no private names.
#[derive(Clone, Copy)]
pub struct EEnv {
    /// `IsStrict`.
    pub strict: bool,
    /// The goal symbol is `Module`.
    pub module: bool,
    /// `[Yield]`.
    pub yield_: bool,
    /// `[Await]`.
    pub await_: bool,
    /// In an iteration statement.
    pub in_loop: bool,
    /// In an iteration statement or a `switch`.
    pub in_breakable: bool,
    /// `SuperProperty` is allowed.
    pub super_prop: bool,
    /// `SuperCall` is allowed.
    pub super_call: bool,
    /// `new.target` is allowed.
    pub new_target: bool,
    /// `arguments` is not allowed.
    pub no_arguments: bool,
    /// `yield` and `await` expressions are not allowed.
    pub no_yield_await: bool,
    /// `[Tagged]`.
    pub tagged: bool,
    /// The nearest class has a heritage.
    pub derived: bool,
}

/// The specification's environment of an executable one.
pub open spec fn eenv_of(e: EEnv) -> EarlyEnv {
    EarlyEnv {
        strict: e.strict,
        module: e.module,
        yield_: e.yield_,
        await_: e.await_,
        labels: Seq::empty(),
        in_loop: e.in_loop,
        in_breakable: e.in_breakable,
        super_prop: e.super_prop,
        super_call: e.super_call,
        new_target: e.new_target,
        no_arguments: e.no_arguments,
        no_yield_await: e.no_yield_await,
        tagged: e.tagged,
        privates: Seq::empty(),
        derived: e.derived,
    }
}

/// Two environments are the same.
fn eenv_eq(p: &EEnv, q: &EEnv) -> (r: bool)
    ensures
        r == (eenv_of(*p) == eenv_of(*q)),
{
    p.strict == q.strict && p.module == q.module && p.yield_ == q.yield_ && p.await_ == q.await_
        && p.in_loop == q.in_loop && p.in_breakable == q.in_breakable && p.super_prop
        == q.super_prop && p.super_call == q.super_call && p.new_target == q.new_target
        && p.no_arguments == q.no_arguments && p.no_yield_await == q.no_yield_await && p.tagged
        == q.tagged && p.derived == q.derived
}

/// The arguments of `spec::env_fn` that say what the function code allows.
pub struct FnFlags {
    /// `[Yield]`.
    pub y: bool,
    /// `[Await]`.
    pub aw: bool,
    /// `SuperProperty` is allowed.
    pub sp: bool,
    /// `SuperCall` is allowed.
    pub sc: bool,
    /// `new.target` is allowed.
    pub nt: bool,
    /// `arguments` is not allowed.
    pub na: bool,
    /// `yield` and `await` expressions are not allowed.
    pub nya: bool,
}

/// `spec::env_fn`.
fn env_fn_exec(e: &EEnv, strict: bool, f: FnFlags) -> (r: EEnv)
    ensures
        eenv_of(r) == env_fn(eenv_of(*e), strict, f.y, f.aw, f.sp, f.sc, f.nt, f.na, f.nya),
{
    EEnv {
        strict,
        module: e.module,
        yield_: f.y,
        await_: f.aw,
        in_loop: false,
        in_breakable: false,
        super_prop: f.sp,
        super_call: f.sc,
        new_target: f.nt,
        no_arguments: f.na,
        no_yield_await: f.nya,
        tagged: false,
        derived: e.derived,
    }
}

/// `IsStrict` of the code of the function-like node `n` whose body is its third child:
/// the enclosing code's, or a Use Strict Directive of the body.
#[verifier::rlimit(400)]
fn fn_strict_exec(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
    n: usize,
    env_strict: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<bool>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(v) => {
                let a = arena_of(nodes@);
                v == (env_strict || has_use_strict(a, ts, kids(a, kid(a.nodes[n as int].children, 2))))
            },
            None => true,
        },
{
    if env_strict {
        return Some(true);
    }
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(n) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(nd == &nodes@[n as int]);
        assert(a.nodes[n as int].children.len() == nd.children.len());
    }
    match nd.children.as_slice().get(2) {
        Some(b) => {
            let b = *b as usize;
            proof {
                assert(a.nodes[n as int].children[2] == b as int);
                lemma_child_before(a, n as int, 2);
            }
            use_strict_exec(src, nodes, toks, by_start, b, Ghost(ts))
        },
        None => {
            proof {
                assert(kid(a.nodes[n as int].children, 2) == -1int);
                assert(kids(a, -1int) =~= Seq::<int>::empty());
            }
            Some(false)
        },
    }
}

/// `IsStrict` of the code of the arrow function `n`.
#[verifier::rlimit(400)]
fn arrow_strict_exec(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
    n: usize,
    env_strict: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<bool>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(v) => {
                let a = arena_of(nodes@);
                let k1 = kid(a.nodes[n as int].children, 1);
                v == (env_strict || (kd(a, k1) == NodeKind::FunctionBody && has_use_strict(
                    a,
                    ts,
                    kids(a, k1),
                )))
            },
            None => true,
        },
{
    if env_strict {
        return Some(true);
    }
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(n) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(nd == &nodes@[n as int]);
        assert(a.nodes[n as int].children.len() == nd.children.len());
    }
    match kid_kind(nodes, n, 1) {
        Some(NodeKind::FunctionBody) => {
            let b = match nd.children.as_slice().get(1) {
                Some(b) => *b as usize,
                None => {
                    return None;
                },
            };
            proof {
                assert(a.nodes[n as int].children[1] == b as int);
                lemma_child_before(a, n as int, 1);
            }
            use_strict_exec(src, nodes, toks, by_start, b, Ghost(ts))
        },
        Some(_) => Some(false),
        None => None,
    }
}

/// A function declaration or expression of any kind.
pub open spec fn is_function_kind(k: NodeKind) -> bool {
    k == NodeKind::FunctionDeclaration || k == NodeKind::FunctionExpression || k
        == NodeKind::GeneratorDeclaration || k == NodeKind::GeneratorExpression || k
        == NodeKind::AsyncFunctionDeclaration || k == NodeKind::AsyncFunctionExpression || k
        == NodeKind::AsyncGeneratorDeclaration || k == NodeKind::AsyncGeneratorExpression
}

/// `spec::child_env` for a function declaration or expression of any kind.
#[verifier::rlimit(400)]
fn child_env_function(
    tk: &Tk,
    nodes: &[Node],
    n: usize,
    k: usize,
    e: &EEnv,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<EEnv>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        k < nodes@[n as int].children.len(),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
        is_function_kind(nodes@[n as int].kind),
    ensures
        match r {
            Some(c) => eenv_of(c) == child_env(arena_of(nodes@), ts, n as int, k as int, eenv_of(*e)),
            None => true,
        },
{
    let src = tk.src;
    let toks = tk.toks;
    let by_start = tk.by_start;
    let ghost a = arena_of(nodes@);
    let kind = match nodes.get(n) {
        Some(x) => x.kind,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(a.nodes[n as int].kind == kind);
    }
    let strict = match fn_strict_exec(src, nodes, toks, by_start, n, e.strict, Ghost(ts)) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let g = matches!(
        kind,
        NodeKind::GeneratorDeclaration | NodeKind::GeneratorExpression
            | NodeKind::AsyncGeneratorDeclaration | NodeKind::AsyncGeneratorExpression
    );
    let aw = matches!(
        kind,
        NodeKind::AsyncFunctionDeclaration | NodeKind::AsyncFunctionExpression
            | NodeKind::AsyncGeneratorDeclaration | NodeKind::AsyncGeneratorExpression
    );
    let expr = matches!(
        kind,
        NodeKind::FunctionExpression | NodeKind::GeneratorExpression
            | NodeKind::AsyncFunctionExpression | NodeKind::AsyncGeneratorExpression
    );
    if k == 0 {
        Some(
            EEnv {
                strict,
                yield_: if expr {
                    g
                } else {
                    e.yield_
                },
                await_: if expr {
                    aw
                } else {
                    e.await_
                },
                ..*e
            },
        )
    } else {
        Some(env_fn_exec(e, strict, FnFlags { y: g, aw, sp: false, sc: false, nt: true, na: false, nya: k == 1 }))
    }
}

/// `spec::child_env` for a method of an object literal.
#[verifier::rlimit(400)]
fn child_env_method(
    tk: &Tk,
    nodes: &[Node],
    n: usize,
    k: usize,
    e: &EEnv,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<EEnv>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        k < nodes@[n as int].children.len(),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
        nodes@[n as int].kind == NodeKind::MethodDefinition,
    ensures
        match r {
            Some(c) => eenv_of(c) == child_env(arena_of(nodes@), ts, n as int, k as int, eenv_of(*e)),
            None => true,
        },
{
    let src = tk.src;
    let toks = tk.toks;
    let by_start = tk.by_start;
    let ghost a = arena_of(nodes@);
    let op = match nodes.get(n) {
        Some(x) => x.op,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(a.nodes[n as int].op == op);
    }
    if k == 0 {
        return Some(*e);
    }
    // A constructor of a derived class may `super()`: classes are not covered.
    if e.derived {
        return None;
    }
    let strict = match fn_strict_exec(src, nodes, toks, by_start, n, e.strict, Ghost(ts)) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    let mg = matches!(op, Op::GeneratorMethod | Op::AsyncGeneratorMethod);
    let ma = matches!(op, Op::AsyncMethod | Op::AsyncGeneratorMethod);
    Some(env_fn_exec(e, strict, FnFlags { y: mg, aw: ma, sp: true, sc: false, nt: true, na: false, nya: k == 1 }))
}

/// `spec::child_env` for an arrow function.
#[verifier::rlimit(400)]
fn child_env_arrow(
    tk: &Tk,
    nodes: &[Node],
    n: usize,
    k: usize,
    e: &EEnv,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<EEnv>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        k < nodes@[n as int].children.len(),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
        nodes@[n as int].kind == NodeKind::ArrowFunction || nodes@[n as int].kind
            == NodeKind::AsyncArrowFunction,
    ensures
        match r {
            Some(c) => eenv_of(c) == child_env(arena_of(nodes@), ts, n as int, k as int, eenv_of(*e)),
            None => true,
        },
{
    let src = tk.src;
    let toks = tk.toks;
    let by_start = tk.by_start;
    let ghost a = arena_of(nodes@);
    let kind = match nodes.get(n) {
        Some(x) => x.kind,
        None => {
            return None;
        },
    };
    proof {
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(a.nodes[n as int].kind == kind);
    }
    let strict = match arrow_strict_exec(src, nodes, toks, by_start, n, e.strict, Ghost(ts)) {
        Some(v) => v,
        None => {
            return None;
        },
    };
    if matches!(kind, NodeKind::ArrowFunction) {
        if k == 0 {
            Some(env_fn_exec(e, strict, FnFlags { y: e.yield_, aw: e.await_, sp: e.super_prop, sc: e.super_call, nt: e.new_target, na: e.no_arguments, nya: true }))
        } else {
            Some(env_fn_exec(e, strict, FnFlags { y: false, aw: false, sp: e.super_prop, sc: e.super_call, nt: e.new_target, na: e.no_arguments, nya: false }))
        }
    } else if k == 0 {
        let y = match kid_kind(nodes, n, 0) {
            Some(NodeKind::BindingIdentifier) => e.yield_,
            Some(_) => false,
            None => {
                return None;
            },
        };
        Some(env_fn_exec(e, strict, FnFlags { y, aw: true, sp: e.super_prop, sc: e.super_call, nt: e.new_target, na: e.no_arguments, nya: true }))
    } else {
        Some(env_fn_exec(e, strict, FnFlags { y: false, aw: true, sp: e.super_prop, sc: e.super_call, nt: e.new_target, na: e.no_arguments, nya: false }))
    }
}

/// `spec::child_env` for the function-like nodes: child `k` of node `n`.
fn child_env_fnlike(
    tk: &Tk,
    nodes: &[Node],
    n: usize,
    k: usize,
    e: &EEnv,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<EEnv>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        k < nodes@[n as int].children.len(),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(c) => eenv_of(c) == child_env(arena_of(nodes@), ts, n as int, k as int, eenv_of(*e)),
            None => true,
        },
{
    let kind = match nodes.get(n) {
        Some(x) => x.kind,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[n as int] == nodes@[n as int]@);
    }
    match kind {
        NodeKind::FunctionDeclaration | NodeKind::FunctionExpression | NodeKind::GeneratorDeclaration
        | NodeKind::GeneratorExpression | NodeKind::AsyncFunctionDeclaration
        | NodeKind::AsyncFunctionExpression | NodeKind::AsyncGeneratorDeclaration
        | NodeKind::AsyncGeneratorExpression => child_env_function(tk, nodes, n, k, e, Ghost(ts)),
        NodeKind::MethodDefinition => child_env_method(tk, nodes, n, k, e, Ghost(ts)),
        NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction => child_env_arrow(tk, nodes, n, k, e, Ghost(ts)),
        _ => None,
    }
}


/// `spec::child_env` for the node kinds whose arm is simple: child `k` of node `n`.
#[verifier::rlimit(400)]
fn child_env_exec(
    tk: &Tk,
    nodes: &[Node],
    n: usize,
    k: usize,
    e: &EEnv,
    Ghost(ts): Ghost<Stream>,
) -> (r: Option<EEnv>)
    requires
        n < nodes.len(),
        ast_wf(arena_of(nodes@)),
        k < nodes@[n as int].children.len(),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
    ensures
        match r {
            Some(c) => eenv_of(c) == child_env(arena_of(nodes@), ts, n as int, k as int, eenv_of(*e)),
            None => true,
        },
{
    let nd = match nodes.get(n) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let ch = match nd.children.as_slice().get(k) {
        Some(c) => *c as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[n as int] == nodes@[n as int]@);
        assert(nd == &nodes@[n as int]);
        assert(a.nodes[n as int].children[k as int] == ch as int);
        assert(a.nodes[n as int].kind == nd.kind);
    }
    let plain = EEnv { tagged: false, ..*e };
    match nd.kind {
        NodeKind::FunctionDeclaration | NodeKind::FunctionExpression | NodeKind::GeneratorDeclaration
        | NodeKind::GeneratorExpression | NodeKind::AsyncFunctionDeclaration
        | NodeKind::AsyncFunctionExpression | NodeKind::AsyncGeneratorDeclaration
        | NodeKind::AsyncGeneratorExpression | NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction
        | NodeKind::MethodDefinition => child_env_fnlike(tk, nodes, n, k, e, Ghost(ts)),
        NodeKind::FieldDefinition | NodeKind::ClassStaticBlock | NodeKind::ClassDeclaration
        | NodeKind::ClassExpression | NodeKind::ClassBody | NodeKind::LabelledStatement => None,
        NodeKind::ObjectLiteral => Some(EEnv { derived: false, ..*e }),
        NodeKind::DoWhileStatement => if k == 0 {
            Some(EEnv { in_loop: true, in_breakable: true, ..*e })
        } else {
            Some(*e)
        },
        NodeKind::WhileStatement => if k == 1 {
            Some(EEnv { in_loop: true, in_breakable: true, ..*e })
        } else {
            Some(*e)
        },
        NodeKind::ForStatement => if k == 3 {
            Some(EEnv { in_loop: true, in_breakable: true, ..*e })
        } else {
            Some(*e)
        },
        NodeKind::ForInStatement | NodeKind::ForOfStatement => if k == 2 {
            Some(EEnv { in_loop: true, in_breakable: true, ..*e })
        } else {
            Some(*e)
        },
        NodeKind::SwitchStatement => if k >= 1 {
            Some(EEnv { in_breakable: true, ..*e })
        } else {
            Some(*e)
        },
        NodeKind::TaggedTemplate => Some(EEnv { tagged: k == 1, ..*e }),
        NodeKind::TemplateLiteral => {
            let ck = match nodes.get(ch) {
                Some(x) => x.kind,
                None => {
                    return None;
                },
            };
            proof {
                let a = arena_of(nodes@);
                assert(a.nodes[ch as int] == nodes@[ch as int]@);
            }
            if matches!(ck, NodeKind::TemplateElement) {
                Some(*e)
            } else {
                Some(plain)
            }
        },
        _ => Some(plain),
    }
}

// ---------------------------------------------------------------------
// Rules.
// ---------------------------------------------------------------------

/// §13.1.1 the identifier rules in terms of the name, the kind of node and the environment.
pub open spec fn ident_name_ok(nm: Seq<u32>, kind: NodeKind, env: EarlyEnv) -> bool {
    let is_yield = nm =~= sv("yield"@);
    let is_await = nm =~= sv("await"@);
    !(kind == NodeKind::BindingIdentifier && env.strict && (nm =~= sv("arguments"@) || nm
        =~= sv("eval"@))) && !(env.strict && is_strict_reserved(nm)) && !(env.module && is_await)
        && !(env.yield_ && is_yield) && !(env.await_ && is_await) && !(is_reserved_text(nm)
        && !is_yield && !is_await) && !(kind == NodeKind::IdentifierReference && env.no_arguments
        && nm =~= sv("arguments"@))
}

/// `early_identifier_ok` is `ident_name_ok` of the node's name.
proof fn lemma_ident_rule(a: AstV, ts: Stream, c: int, env: EarlyEnv)
    ensures
        early_identifier_ok(a, ts, c, env) == ident_name_ok(name_of(a, ts, c), kd(a, c), env),
{
}

/// §13.1.1 for an identifier of `name`.
fn ident_early(name: &[u32], binding: bool, reference: bool, e: &EEnv) -> (r: bool)
    ensures
        r ==> ident_name_ok(
            name@,
            if binding {
                NodeKind::BindingIdentifier
            } else if reference {
                NodeKind::IdentifierReference
            } else {
                NodeKind::LabelIdentifier
            },
            eenv_of(*e),
        ),
{
    proof {
        lemma_words_early();
    }
    let is_yield = seq_eq(name, &[0x79, 0x69, 0x65, 0x6C, 0x64]);
    let is_await = seq_eq(name, &[0x61, 0x77, 0x61, 0x69, 0x74]);
    let is_args = seq_eq(name, &[0x61, 0x72, 0x67, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x73]);
    let is_eval = seq_eq(name, &[0x65, 0x76, 0x61, 0x6C]);
    let strict_reserved = is_yield || seq_eq(name, &[0x69, 0x6D, 0x70, 0x6C, 0x65, 0x6D, 0x65, 0x6E, 0x74, 0x73])
        || seq_eq(name, &[0x69, 0x6E, 0x74, 0x65, 0x72, 0x66, 0x61, 0x63, 0x65])
        || seq_eq(name, &[0x6C, 0x65, 0x74]) || seq_eq(name, &[0x70, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65])
        || seq_eq(name, &[0x70, 0x72, 0x69, 0x76, 0x61, 0x74, 0x65])
        || seq_eq(name, &[0x70, 0x72, 0x6F, 0x74, 0x65, 0x63, 0x74, 0x65, 0x64])
        || seq_eq(name, &[0x70, 0x75, 0x62, 0x6C, 0x69, 0x63])
        || seq_eq(name, &[0x73, 0x74, 0x61, 0x74, 0x69, 0x63]);
    let reserved = reserved_of(name);
    let is_reserved = reserved.is_some();
    proof {
        if let Some(w) = reserved {
            lemma_reserved_chars(w as int);
            assert(is_reserved_text(name@)) by {
                assert(0 <= w < reserved_words().len() && name@ =~= cps(reserved_words()[w as int]));
            }
        } else {
            assert(!is_reserved_text(name@)) by {
                assert forall|w: int| 0 <= w < reserved_words().len() implies !(name@ =~= cps(
                    #[trigger] reserved_words()[w],
                )) by {
                    lemma_reserved_chars(w);
                }
            }
        }
    }
    !(binding && e.strict && (is_args || is_eval)) && !(e.strict && strict_reserved)
        && !(e.module && is_await) && !(e.yield_ && is_yield) && !(e.await_ && is_await)
        && !(is_reserved && !is_yield && !is_await) && !(reference && e.no_arguments && is_args)
}

/// The statement `c` is not a labelled function (`is_labelled_function`): it is not a label.
fn not_labelled(nodes: &[Node], c: usize) -> (r: bool)
    requires
        c < nodes.len(),
    ensures
        r ==> !is_labelled_function(arena_of(nodes@), c as int),
{
    match nodes.get(c) {
        Some(x) => {
            proof {
                let a = arena_of(nodes@);
                assert(a.nodes[c as int] == nodes@[c as int]@);
            }
            !matches!(x.kind, NodeKind::LabelledStatement)
        },
        None => false,
    }
}

/// The token a node starts at, found from its start.
pub(crate) fn node_token(nodes: &[Node], toks: &[DTok], by_start: &[usize], m: usize) -> (r: Option<usize>)
    requires
        m < nodes.len(),
    ensures
        match r {
            Some(x) => x < toks.len() && toks@[x as int].start as int == nodes@[m as int].start as int,
            None => true,
        },
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let x = match by_start.get(nd.start) {
        Some(x) => *x,
        None => {
            return None;
        },
    };
    match toks.get(x) {
        Some(t) => if t.start == nd.start {
            Some(x)
        } else {
            None
        },
        None => None,
    }
}

/// §8.6.4 the node `c` is a `~simple~` assignment target (through parentheses).
fn target_simple(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    by_start: &[usize],
    c0: usize,
    strict: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: bool)
    requires
        c0 < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
        starts_inc(ts),
    ensures
        r ==> target_type(arena_of(nodes@), ts, c0 as int, strict) == TargetType::Simple,
{
    let _ = src.len();
    let ghost a = arena_of(nodes@);
    let mut c = c0;
    loop
        invariant
            c < nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            toks_match(src@, toks@, ts),
            starts_inc(ts),
            target_type(a, ts, c0 as int, strict) == target_type(a, ts, c as int, strict),
        decreases c,
    {
        let nd = match nodes.get(c) {
            Some(x) => x,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
            assert(nd == &nodes@[c as int]);
            assert(a.nodes[c as int].kind == nd.kind);
        }
        match nd.kind {
            NodeKind::MemberExpression | NodeKind::SuperProperty => {
                return true;
            },
            NodeKind::IdentifierReference => {
                let x = match node_token(nodes, toks, by_start, c) {
                    Some(x) => x,
                    None => {
                        return false;
                    },
                };
                let t = match toks.get(x) {
                    Some(t) => t,
                    None => {
                        return false;
                    },
                };
                let bad = strict && (seq_eq(t.name.as_slice(), &[0x65, 0x76, 0x61, 0x6C])
                    || seq_eq(t.name.as_slice(), &[0x61, 0x72, 0x67, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x73]));
                proof {
                    lemma_words_early();
                    assert(t == &toks@[x as int]);
                    assert(dtok_matches(src@, toks@[x as int], ts.toks[x as int]));
                    lemma_node_tok_at(a, ts, c as int, x as int);
                    assert(name_of(a, ts, c as int) =~= t.name@);
                    assert(a.nodes.len() == nodes@.len());
                    if !bad {
                        assert(a.nodes[c as int].kind == NodeKind::IdentifierReference);
                        assert(!(strict && (name_of(a, ts, c as int) =~= sv("eval"@) || name_of(
                            a,
                            ts,
                            c as int,
                        ) =~= sv("arguments"@))));
                        assert(target_type(a, ts, c as int, strict) == TargetType::Simple);
                    }
                }
                return !bad;
            },
            NodeKind::ParenthesizedExpression => {
                let k0 = match nd.children.as_slice().get(ZERO) {
                    Some(k) => *k as usize,
                    None => {
                        return false;
                    },
                };
                proof {
                    assert(a.nodes[c as int].children[0] == k0 as int);
                }
                if k0 >= c {
                    return false;
                }
                c = k0;
            },
            _ => {
                return false;
            },
        }
    }
}

/// The kinds `early_local` has an arm for (other kinds have none: it is `true`).
fn has_arm(k: NodeKind) -> (r: bool)
    ensures
        !r ==> (k != NodeKind::IdentifierReference && k != NodeKind::BindingIdentifier && k
            != NodeKind::LabelIdentifier && k != NodeKind::NumericLiteral && k
            != NodeKind::StringLiteral && k != NodeKind::RegularExpressionLiteral && k
            != NodeKind::TemplateElement && k != NodeKind::ObjectLiteral && k
            != NodeKind::CoverInitializedName && k != NodeKind::SuperProperty && k
            != NodeKind::SuperCall && k != NodeKind::NewTarget && k != NodeKind::ImportMeta && k
            != NodeKind::MemberExpression && k != NodeKind::OptionalChain && k
            != NodeKind::RelationalExpression && k != NodeKind::UnaryExpression && k
            != NodeKind::UpdateExpression && k != NodeKind::AssignmentExpression && k
            != NodeKind::AssignmentProperty && k != NodeKind::AssignmentElement && k
            != NodeKind::AssignmentRestElement && k != NodeKind::AssignmentRestProperty && k
            != NodeKind::YieldExpression && k != NodeKind::AwaitExpression && k
            != NodeKind::BlockStatement && k != NodeKind::LexicalDeclaration && k
            != NodeKind::IfStatement && k != NodeKind::DoWhileStatement && k
            != NodeKind::WhileStatement && k != NodeKind::ForStatement && k
            != NodeKind::ForInStatement && k != NodeKind::ForOfStatement && k
            != NodeKind::ContinueStatement && k != NodeKind::BreakStatement && k
            != NodeKind::WithStatement && k != NodeKind::SwitchStatement && k
            != NodeKind::LabelledStatement && k != NodeKind::Catch && k != NodeKind::FunctionBody
            && k != NodeKind::FunctionDeclaration && k != NodeKind::FunctionExpression && k
            != NodeKind::GeneratorDeclaration && k != NodeKind::GeneratorExpression && k
            != NodeKind::AsyncFunctionDeclaration && k != NodeKind::AsyncFunctionExpression && k
            != NodeKind::AsyncGeneratorDeclaration && k != NodeKind::AsyncGeneratorExpression && k
            != NodeKind::ArrowFunction && k != NodeKind::AsyncArrowFunction && k
            != NodeKind::MethodDefinition && k != NodeKind::ClassBody && k != NodeKind::Script
            && k != NodeKind::Module && k != NodeKind::WithClause && k != NodeKind::ExportDeclaration
            && k != NodeKind::ExportSpecifier && k != NodeKind::ImportSpecifier),
{
    matches!(
        k,
        NodeKind::IdentifierReference | NodeKind::BindingIdentifier | NodeKind::LabelIdentifier
            | NodeKind::NumericLiteral | NodeKind::StringLiteral | NodeKind::RegularExpressionLiteral
            | NodeKind::TemplateElement | NodeKind::ObjectLiteral | NodeKind::CoverInitializedName
            | NodeKind::SuperProperty | NodeKind::SuperCall | NodeKind::NewTarget | NodeKind::ImportMeta
            | NodeKind::MemberExpression | NodeKind::OptionalChain | NodeKind::RelationalExpression
            | NodeKind::UnaryExpression | NodeKind::UpdateExpression | NodeKind::AssignmentExpression
            | NodeKind::AssignmentProperty | NodeKind::AssignmentElement | NodeKind::AssignmentRestElement
            | NodeKind::AssignmentRestProperty | NodeKind::YieldExpression | NodeKind::AwaitExpression
            | NodeKind::BlockStatement | NodeKind::LexicalDeclaration | NodeKind::IfStatement
            | NodeKind::DoWhileStatement | NodeKind::WhileStatement | NodeKind::ForStatement
            | NodeKind::ForInStatement | NodeKind::ForOfStatement | NodeKind::ContinueStatement
            | NodeKind::BreakStatement | NodeKind::WithStatement | NodeKind::SwitchStatement
            | NodeKind::LabelledStatement | NodeKind::Catch | NodeKind::FunctionBody
            | NodeKind::FunctionDeclaration | NodeKind::FunctionExpression | NodeKind::GeneratorDeclaration
            | NodeKind::GeneratorExpression | NodeKind::AsyncFunctionDeclaration
            | NodeKind::AsyncFunctionExpression | NodeKind::AsyncGeneratorDeclaration
            | NodeKind::AsyncGeneratorExpression | NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction
            | NodeKind::MethodDefinition | NodeKind::ClassBody | NodeKind::Script | NodeKind::Module
            | NodeKind::WithClause | NodeKind::ExportDeclaration | NodeKind::ExportSpecifier
            | NodeKind::ImportSpecifier
    )
}

/// An item whose `LexicallyDeclaredNames` is empty, in a list that is `top` (a script's) or not.
pub open spec fn lex_empty_kind(k: NodeKind, top: bool) -> bool {
    !(k == NodeKind::LexicalDeclaration || k == NodeKind::ClassDeclaration || k
        == NodeKind::ImportDeclaration || k == NodeKind::ExportDeclaration || (!top && (k
        == NodeKind::FunctionDeclaration || k == NodeKind::GeneratorDeclaration || k
        == NodeKind::AsyncFunctionDeclaration || k == NodeKind::AsyncGeneratorDeclaration || k
        == NodeKind::LabelledStatement)))
}

/// The lexically declared names of a list of such items are none.
pub(crate) proof fn lemma_lex_list_empty(a: AstV, ts: Stream, n: int, ks: Seq<int>, k: int, top: bool)
    requires
        forall|j: int| 0 <= j < ks.len() ==> lex_empty_kind(kd(a, #[trigger] ks[j]), top),
    ensures
        lex_names_list(a, ts, n, ks, k, top) =~= Seq::empty(),
    decreases ks.len() - k,
{
    if 0 <= k < ks.len() {
        lemma_lex_list_empty(a, ts, n, ks, k + 1, top);
        if 0 <= ks[k] < n {
            assert(lex_empty_kind(kd(a, ks[k]), top));
            assert(lex_names_item(a, ts, ks[k], top) =~= Seq::empty());
        }
    }
}

/// `list_early` of a list whose items declare nothing lexically.
pub(crate) proof fn lemma_list_early_empty(a: AstV, ts: Stream, n: int, ks: Seq<int>, strict: bool, top: bool)
    requires
        forall|j: int| 0 <= j < ks.len() ==> lex_empty_kind(kd(a, #[trigger] ks[j]), top),
    ensures
        list_early(a, ts, n, ks, strict, top),
{
    lemma_lex_list_empty(a, ts, n, ks, 0, top);
    let lex = lex_names_list(a, ts, n, ks, 0, top);
    assert(lex =~= Seq::empty());
    assert(!has_forbidden_duplicate(lex, strict));
    assert(plain_names(lex) =~= Seq::empty());
    assert(!intersects(plain_names(lex), if top {
        top_var_names_list(a, ts, n, ks, 0)
    } else {
        var_names_list(a, ts, n, ks, 0)
    }));
}

/// The items of node `m` declare nothing lexically.
pub(crate) fn items_lex_empty(nodes: &[Node], m: usize, top: bool) -> (r: bool)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        r ==> forall|j: int|
            0 <= j < arena_of(nodes@).nodes[m as int].children.len() ==> lex_empty_kind(
                kd(arena_of(nodes@), #[trigger] arena_of(nodes@).nodes[m as int].children[j]),
                top,
            ),
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    let len = nd.children.len();
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children.len() == len);
    }
    let mut k: usize = 0;
    while k < len
        invariant
            m < nodes.len(),
            nodes@.len() == nodes.len(),
            a == arena_of(nodes@),
            ast_wf(a),
            nd == &nodes@[m as int],
            len == nd.children.len(),
            len == a.nodes[m as int].children.len(),
            k <= len,
            forall|j: int|
                0 <= j < k ==> lex_empty_kind(kd(a, #[trigger] a.nodes[m as int].children[j]), top),
        decreases len - k,
    {
        let c = match nd.children.as_slice().get(k) {
            Some(x) => *x as usize,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[m as int].children[k as int] == c as int);
            lemma_child_before(a, m as int, k as int);
        }
        let ck = match nodes.get(c) {
            Some(x) => x.kind,
            None => {
                return false;
            },
        };
        proof {
            assert(a.nodes[c as int] == nodes@[c as int]@);
        }
        let ok = !(matches!(
            ck,
            NodeKind::LexicalDeclaration | NodeKind::ClassDeclaration | NodeKind::ImportDeclaration
                | NodeKind::ExportDeclaration
        ) || (!top && matches!(
            ck,
            NodeKind::FunctionDeclaration | NodeKind::GeneratorDeclaration
                | NodeKind::AsyncFunctionDeclaration | NodeKind::AsyncGeneratorDeclaration
                | NodeKind::LabelledStatement
        )));
        if !ok {
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

/// The kind of child `i` of node `m`, `Script` where there is none (`spec::kd(a, kid(ks, i))`).
pub(crate) fn kid_kind(nodes: &[Node], m: usize, i: usize) -> (r: Option<NodeKind>)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
    ensures
        match r {
            Some(k) => i < arena_of(nodes@).nodes[m as int].children.len() && kd(
                arena_of(nodes@),
                arena_of(nodes@).nodes[m as int].children[i as int],
            ) == k,
            None => true,
        },
{
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return None;
        },
    };
    let c = match nd.children.as_slice().get(i) {
        Some(c) => *c as usize,
        None => {
            return None;
        },
    };
    proof {
        let a = arena_of(nodes@);
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].children[i as int] == c as int);
        lemma_child_before(a, m as int, i as int);
    }
    if c >= m {
        return None;
    }
    match nodes.get(c) {
        Some(x) => {
            proof {
                let a = arena_of(nodes@);
                assert(a.nodes[c as int] == nodes@[c as int]@);
            }
            Some(x.kind)
        },
        None => None,
    }
}

/// `early_local` of node `m` in `e`, for the rules this module covers (`false` otherwise).
#[verifier::rlimit(400)]
fn early_local_exec(
    tk: &Tk,
    nodes: &[Node],
    m: usize,
    e: &EEnv,
    Ghost(ts): Ghost<Stream>,
) -> (r: bool)
    requires
        m < nodes.len(),
        ast_wf(arena_of(nodes@)),
        toks_match(tk.src@, tk.toks@, ts),
        starts_inc(ts),
        tk.bn.len() == nodes.len(),
        bn_inv(arena_of(nodes@), ts, tk.toks@, tk.bn@, nodes.len() as int),
    ensures
        r ==> early_local(arena_of(nodes@), ts, m as int, eenv_of(*e)),
{
    let src = tk.src;
    let toks = tk.toks;
    let by_start = tk.by_start;
    let ghost a = arena_of(nodes@);
    let nd = match nodes.get(m) {
        Some(x) => x,
        None => {
            return false;
        },
    };
    proof {
        assert(a.nodes[m as int] == nodes@[m as int]@);
        assert(nd == &nodes@[m as int]);
        assert(a.nodes[m as int].kind == nd.kind);
        assert(a.nodes[m as int].op == nd.op);
        assert(a.nodes[m as int].flag == nd.flag);
    }
    let kind = nd.kind;
    if !has_arm(kind) {
        return true;
    }
    match kind {
        NodeKind::NumericLiteral | NodeKind::StringLiteral | NodeKind::TemplateElement
        | NodeKind::IdentifierReference | NodeKind::BindingIdentifier | NodeKind::LabelIdentifier => {
            let x = match node_token(nodes, toks, by_start, m) {
                Some(x) => x,
                None => {
                    return false;
                },
            };
            let t = match toks.get(x) {
                Some(t) => t,
                None => {
                    return false;
                },
            };
            proof {
                assert(t == &toks@[x as int]);
                assert(dtok_matches(src@, toks@[x as int], ts.toks[x as int]));
                lemma_node_tok_at(a, ts, m as int, x as int);
            }
            match kind {
                NodeKind::NumericLiteral | NodeKind::StringLiteral => !(e.strict && t.legacy),
                NodeKind::TemplateElement => e.tagged || !t.invalid_escape,
                _ => {
                    let ok = ident_early(
                        t.name.as_slice(),
                        matches!(kind, NodeKind::BindingIdentifier),
                        matches!(kind, NodeKind::IdentifierReference),
                        e,
                    );
                    proof {
                        lemma_ident_rule(a, ts, m as int, eenv_of(*e));
                        assert(name_of(a, ts, m as int) =~= t.name@);
                    }
                    ok
                },
            }
        },
        NodeKind::SuperProperty => e.super_prop,
        NodeKind::SuperCall => e.super_call,
        NodeKind::NewTarget => e.new_target,
        NodeKind::ImportMeta => e.module,
        NodeKind::YieldExpression | NodeKind::AwaitExpression => !e.no_yield_await,
        NodeKind::MemberExpression => !matches!(nd.op, Op::PrivateDot),
        NodeKind::OptionalChain => !matches!(nd.op, Op::ChainTemplate | Op::ChainPrivateDot),
        NodeKind::RelationalExpression => match kid_kind(nodes, m, 0) {
            Some(k0) => !matches!(k0, NodeKind::PrivateIdentifier),
            None => false,
        },
        NodeKind::UnaryExpression => !matches!(nd.op, Op::Delete) || !e.strict,
        NodeKind::UpdateExpression => {
            let c = match nd.children.as_slice().get(ZERO) {
                Some(c) => *c as usize,
                None => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[0] == c as int);
                lemma_child_before(a, m as int, 0);
            }
            c < m && target_simple(src, nodes, toks, by_start, c, e.strict, Ghost(ts))
        },
        NodeKind::AssignmentExpression => {
            let c = match nd.children.as_slice().get(ZERO) {
                Some(c) => *c as usize,
                None => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[0] == c as int);
                lemma_child_before(a, m as int, 0);
            }
            if c >= m {
                return false;
            }
            let ck = match nodes.get(c) {
                Some(x) => x.kind,
                None => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[c as int] == nodes@[c as int]@);
            }
            (matches!(nd.op, Op::Assign)
                && matches!(ck, NodeKind::ObjectAssignmentPattern | NodeKind::ArrayAssignmentPattern))
                || target_simple(src, nodes, toks, by_start, c, e.strict, Ghost(ts))
        },
        NodeKind::IfStatement => {
            let (k1, k2) = match (kid_kind(nodes, m, 1), kid_kind(nodes, m, 2)) {
                (Some(x), Some(y)) => (x, y),
                _ => {
                    return false;
                },
            };
            let c1 = match nd.children.as_slice().get(1) {
                Some(c) => *c as usize,
                None => {
                    return false;
                },
            };
            let c2 = match nd.children.as_slice().get(2) {
                Some(c) => *c as usize,
                None => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[1] == c1 as int);
                assert(a.nodes[m as int].children[2] == c2 as int);
                lemma_child_before(a, m as int, 1);
                lemma_child_before(a, m as int, 2);
            }
            c1 < m && c2 < m && not_labelled(nodes, c1) && not_labelled(nodes, c2) && !(e.strict
                && (matches!(k1, NodeKind::FunctionDeclaration) || matches!(k2, NodeKind::FunctionDeclaration)))
        },
        NodeKind::WhileStatement | NodeKind::WithStatement | NodeKind::DoWhileStatement => {
            let which: usize = if matches!(kind, NodeKind::DoWhileStatement) { 0 } else { 1 };
            let c = match nd.children.as_slice().get(which) {
                Some(c) => *c as usize,
                None => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[which as int] == c as int);
                lemma_child_before(a, m as int, which as int);
            }
            c < m && not_labelled(nodes, c) && (!matches!(kind, NodeKind::WithStatement) || !e.strict)
        },
        NodeKind::ForStatement => {
            let c = match nd.children.as_slice().get(3) {
                Some(c) => *c as usize,
                None => {
                    return false;
                },
            };
            let k0 = match kid_kind(nodes, m, 0) {
                Some(k) => k,
                None => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[3] == c as int);
                lemma_child_before(a, m as int, 3);
            }
            c < m && not_labelled(nodes, c) && !matches!(k0, NodeKind::LexicalDeclaration)
        },
        NodeKind::ContinueStatement | NodeKind::BreakStatement => {
            let k0 = match kid_kind(nodes, m, 0) {
                Some(k) => k,
                None => {
                    return false;
                },
            };
            if matches!(k0, NodeKind::LabelIdentifier) {
                return false;
            }
            if matches!(kind, NodeKind::ContinueStatement) {
                e.in_loop
            } else {
                e.in_breakable
            }
        },
        NodeKind::BlockStatement => {
            let ok = items_lex_empty(nodes, m, false);
            proof {
                if ok {
                    lemma_list_early_empty(a, ts, m as int, a.nodes[m as int].children, e.strict, false);
                }
            }
            ok
        },
        NodeKind::Script => {
            let ok = items_lex_empty(nodes, m, true);
            proof {
                if ok {
                    lemma_list_early_empty(a, ts, m as int, a.nodes[m as int].children, e.strict, true);
                }
            }
            ok
        },
        NodeKind::ObjectLiteral => object_literal_exec(tk, nodes, m, Ghost(ts)),
        NodeKind::FunctionBody => {
            let ok = items_lex_empty(nodes, m, true);
            proof {
                if ok {
                    lemma_list_early_empty(a, ts, m as int, a.nodes[m as int].children, e.strict, true);
                }
            }
            ok
        },
        NodeKind::FunctionDeclaration | NodeKind::FunctionExpression | NodeKind::GeneratorDeclaration
        | NodeKind::GeneratorExpression | NodeKind::AsyncFunctionDeclaration
        | NodeKind::AsyncFunctionExpression | NodeKind::AsyncGeneratorDeclaration
        | NodeKind::AsyncGeneratorExpression | NodeKind::MethodDefinition => {
            let (p, b) = match (nd.children.as_slice().get(1), nd.children.as_slice().get(2)) {
                (Some(p), Some(b)) => (*p as usize, *b as usize),
                _ => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[1] == p as int);
                assert(a.nodes[m as int].children[2] == b as int);
                lemma_child_before(a, m as int, 1);
                lemma_child_before(a, m as int, 2);
            }
            function_early_exec(
                tk,
                nodes,
                p,
                Some(b),
                matches!(kind, NodeKind::MethodDefinition),
                e.strict,
                Ghost(ts),
            )
        },
        NodeKind::ArrowFunction | NodeKind::AsyncArrowFunction => {
            let (p, b) = match (nd.children.as_slice().get(ZERO), nd.children.as_slice().get(1)) {
                (Some(p), Some(b)) => (*p as usize, *b as usize),
                _ => {
                    return false;
                },
            };
            proof {
                assert(a.nodes[m as int].children[0] == p as int);
                assert(a.nodes[m as int].children[1] == b as int);
                lemma_child_before(a, m as int, 0);
                lemma_child_before(a, m as int, 1);
            }
            let bk = match kid_kind(nodes, m, 1) {
                Some(k) => k,
                None => {
                    return false;
                },
            };
            function_early_exec(
                tk,
                nodes,
                p,
                if matches!(bk, NodeKind::FunctionBody) {
                    Some(b)
                } else {
                    None
                },
                true,
                e.strict,
                Ghost(ts),
            )
        },
        _ => false,
    }
}


/// [`check_early`] on the canonical stream of the executable tokens and gaps
/// ([`canon_stream`]), which needs no ghost argument.
pub fn check_early_canon(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    gaps: &[Ins],
    module: bool,
) -> (r: Derivation)
    requires
        ast_wf(arena_of(nodes@)),
        gaps@.len() == toks@.len() + 1,
    ensures
        r is Verified ==> early_errors_ok(
            arena_of(nodes@),
            canon_stream(src@, toks@, gaps@),
            goal_of(module),
        ),
{
    let _ = gaps.len();
    let nt = toks.len();
    let mut k: usize = 0;
    while k < nt
        invariant
            nt == toks.len(),
            k <= nt,
            forall|x: int|
                0 <= x < k ==> (#[trigger] toks@[x]).start <= toks@[x].end && toks@[x].end
                    <= src@.len(),
        decreases nt - k,
    {
        let t = match toks.get(k) {
            Some(t) => t,
            None => {
                return Derivation::Unsupported;
            },
        };
        if t.start > t.end || t.end > src.len() {
            return Derivation::Unsupported;
        }
        k = k.saturating_add(1);
    }
    let ghost ts = canon_stream(src@, toks@, gaps@);
    proof {
        assert(toks_match(src@, toks@, ts)) by {
            assert(toks@.len() == ts.toks.len());
            assert forall|x: int| 0 <= x < toks@.len() implies dtok_matches(
                src@,
                toks@[x],
                #[trigger] ts.toks[x],
            ) by {
                assert(ts.toks[x] == canon_tok(src@, toks@[x]));
            }
        }
    }
    check_early(src, nodes, toks, module, Ghost(ts))
}

/// Checks that the arena has no early error (`spec::early_errors_ok`), for the rules and
/// node kinds listed at the top of the module, given the executable tokens (the
/// assumption `toks_match`). `Failed` is never returned; what is not covered is
/// `Unsupported`.
#[verifier::rlimit(400)]
pub fn check_early(
    src: &[u32],
    nodes: &[Node],
    toks: &[DTok],
    module: bool,
    Ghost(ts): Ghost<Stream>,
) -> (r: Derivation)
    requires
        ast_wf(arena_of(nodes@)),
        toks_match(src@, toks@, ts),
    ensures
        r is Verified ==> early_errors_ok(arena_of(nodes@), ts, goal_of(module)),
{
    let n = nodes.len();
    if n == 0 || module {
        return Derivation::Unsupported;
    }
    let last = n.saturating_sub(1);
    let nt = toks.len();
    // The tokens start at increasing positions.
    let mut k: usize = 0;
    while k < nt
        invariant
            nt == toks.len(),
            k <= nt,
            toks_match(src@, toks@, ts),
            forall|x: int, y: int|
                0 <= x < y < k ==> (#[trigger] toks@[x]).start < (#[trigger] toks@[y]).start,
        decreases nt - k,
    {
        if k > 0 {
            let (p, t) = match (toks.get(k.saturating_sub(1)), toks.get(k)) {
                (Some(p), Some(t)) => (p, t),
                _ => {
                    return Derivation::Unsupported;
                },
            };
            if p.start >= t.start {
                return Derivation::Unsupported;
            }
        }
        k = k.saturating_add(1);
    }
    proof {
        assert(starts_inc(ts)) by {
            assert forall|x: int, y: int| 0 <= x < y < tn(ts) implies (#[trigger] ts.toks[x]).start
                < (#[trigger] ts.toks[y]).start by {
                assert(dtok_matches(src@, toks@[x], ts.toks[x]));
                assert(dtok_matches(src@, toks@[y], ts.toks[y]));
            }
        }
    }
    // A hint for finding a token from its start.
    let size = src.len().saturating_add(1);
    let mut by_start: Vec<usize> = Vec::new();
    let mut q: usize = 0;
    while q < size
        invariant
            q <= size,
            by_start.len() == q,
        decreases size - q,
    {
        by_start.push(usize::MAX);
        q = q.saturating_add(1);
    }
    let mut x: usize = 0;
    while x < nt
        invariant
            x <= nt,
            nt == toks.len(),
            by_start.len() == size,
        decreases nt - x,
    {
        let t = match toks.get(x) {
            Some(t) => t,
            None => {
                return Derivation::Unsupported;
            },
        };
        if t.start < by_start.len() {
            by_start.set(t.start, x);
        }
        x = x.saturating_add(1);
    }
    // The names the declarations bind.
    let bn = match bound_names_all(src, nodes, toks, &by_start, Ghost(ts)) {
        Some(bn) => bn,
        None => {
            return Derivation::Unsupported;
        },
    };
    let tk = Tk { src, toks, by_start: by_start.as_slice(), bn: bn.as_slice() };
    // The root's environment: a script, strict if its Directive Prologue has a Use Strict Directive.
    let root_strict = match use_strict_exec(src, nodes, toks, by_start.as_slice(), last, Ghost(ts)) {
        Some(v) => v,
        None => {
            return Derivation::Unsupported;
        },
    };
    let root_e = EEnv {
        strict: root_strict,
        module: false,
        yield_: false,
        await_: false,
        in_loop: false,
        in_breakable: false,
        super_prop: false,
        super_call: false,
        new_target: false,
        no_arguments: false,
        no_yield_await: false,
        tagged: false,
        derived: false,
    };
    let mut envs: Vec<EEnv> = Vec::new();
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n,
            envs.len() == q,
        decreases n - q,
    {
        envs.push(root_e);
        q = q.saturating_add(1);
    }
    let ghost a = arena_of(nodes@);
    proof {
        assert(a.root == nodes.len() as int - 1);
    }
    // Untrusted: the environment each child is to be checked in, from the root down.
    let mut i = n;
    while i > 0
        invariant
            i <= n,
            n == nodes.len(),
            envs.len() == n,
            ast_wf(a),
            a == arena_of(nodes@),
            toks_match(src@, toks@, ts),
            tk.src@ == src@,
            tk.toks@ == toks@,
            starts_inc(ts),
        decreases i,
    {
        i = i.saturating_sub(1);
        let nd = match nodes.get(i) {
            Some(x) => x,
            None => {
                return Derivation::Unsupported;
            },
        };
        let env_i = match envs.get(i) {
            Some(x) => *x,
            None => {
                return Derivation::Unsupported;
            },
        };
        let len = nd.children.len();
        let mut kk: usize = 0;
        while kk < len
            invariant
                kk <= len,
                len == nd.children.len(),
                envs.len() == n,
                n == nodes.len(),
                i < nodes.len(),
                nd == &nodes@[i as int],
                ast_wf(a),
                a == arena_of(nodes@),
                toks_match(src@, toks@, ts),
                tk.src@ == src@,
                tk.toks@ == toks@,
                starts_inc(ts),
                len == nodes@[i as int].children.len(),
            decreases len - kk,
        {
            if let (Some(ce), Some(c)) = (
                child_env_exec(&tk, nodes, i, kk, &env_i, Ghost(ts)),
                nd.children.as_slice().get(kk),
            ) {
                let c = *c as usize;
                if c < n {
                    envs.set(c, ce);
                }
            }
            kk = kk.saturating_add(1);
        }
    }
    // Bottom-up: each node's rules hold, and each child's recorded environment is the
    // one `child_env` gives it.
    let mut m: usize = 0;
    while m < n
        invariant
            m <= n,
            n == nodes.len(),
            envs.len() == n,
            ast_wf(a),
            a == arena_of(nodes@),
            toks_match(src@, toks@, ts),
            tk.src@ == src@,
            tk.toks@ == toks@,
            tk.bn@ == bn@,
            starts_inc(ts),
            bn.len() == n,
            bn_inv(a, ts, toks@, bn@, n as int),
            forall|j: int| 0 <= j < m ==> early(a, ts, j, eenv_of(envs@[j])),
        decreases n - m,
    {
        let nd = match nodes.get(m) {
            Some(x) => x,
            None => {
                return Derivation::Unsupported;
            },
        };
        let env_m = match envs.get(m) {
            Some(x) => *x,
            None => {
                return Derivation::Unsupported;
            },
        };
        if !early_local_exec(&tk, nodes, m, &env_m, Ghost(ts)) {
            return Derivation::Unsupported;
        }
        let len = nd.children.len();
        proof {
            assert(a.nodes[m as int] == nodes@[m as int]@);
            assert(nd == &nodes@[m as int]);
            assert(a.nodes[m as int].children.len() == len);
        }
        let mut kk: usize = 0;
        while kk < len
            invariant
                kk <= len,
                len == nd.children.len(),
                m < n,
                n == nodes.len(),
                envs.len() == n,
                nd == &nodes@[m as int],
                len == a.nodes[m as int].children.len(),
                ast_wf(a),
                a == arena_of(nodes@),
                toks_match(src@, toks@, ts),
                tk.src@ == src@,
                tk.toks@ == toks@,
                tk.bn@ == bn@,
                starts_inc(ts),
                forall|j: int| 0 <= j < m ==> early(a, ts, j, eenv_of(envs@[j])),
                forall|q: int|
                    0 <= q < kk ==> {
                        let c = #[trigger] a.nodes[m as int].children[q];
                        0 <= c < m && early(a, ts, c, child_env(a, ts, m as int, q, eenv_of(env_m)))
                    },
            decreases len - kk,
        {
            let c = match nd.children.as_slice().get(kk) {
                Some(c) => *c as usize,
                None => {
                    return Derivation::Unsupported;
                },
            };
            proof {
                assert(a.nodes[m as int].children[kk as int] == c as int);
                lemma_child_before(a, m as int, kk as int);
            }
            let ce = match child_env_exec(&tk, nodes, m, kk, &env_m, Ghost(ts)) {
                Some(ce) => ce,
                None => {
                    return Derivation::Unsupported;
                },
            };
            let have = match envs.get(c) {
                Some(x) => *x,
                None => {
                    return Derivation::Unsupported;
                },
            };
            if c >= m || !eenv_eq(&have, &ce) {
                return Derivation::Unsupported;
            }
            kk = kk.saturating_add(1);
        }
        proof {
            assert(early(a, ts, m as int, eenv_of(envs@[m as int])));
        }
        m = m.saturating_add(1);
    }
    let root_have = match envs.get(last) {
        Some(x) => *x,
        None => {
            return Derivation::Unsupported;
        },
    };
    if !eenv_eq(&root_have, &root_e) {
        return Derivation::Unsupported;
    }
    proof {
        let g = goal_of(module);
        assert(g == SourceGoal::Script);
        assert(a.root == last as int);
        assert(root_env(a, ts, g) == eenv_of(root_e));
        assert(a.root == last as int);
        assert(early(a, ts, a.root, eenv_of(envs@[a.root])));
    }
    Derivation::Verified
}

} // verus!
