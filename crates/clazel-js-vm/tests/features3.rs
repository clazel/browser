//! Tests of the compiler's third slice: regular expression literals,
//! generators, async functions and `for await`, `with`, direct `eval`,
//! `delete` of a variable, NamedEvaluation and `var arguments`. Each expectation
//! was read against the op docs in `ops.rs` (which cite ECMA-262), not copied
//! from the output.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::{
    Const, EvalBinding, EvalScopeKind, Flavor, FunctionCode, FunctionKind, Instr, Program,
    check_program,
};
use clazel_js_vm::compile::compile_script;

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

fn compile(src: &str) -> Result<Program, String> {
    let c = cps(src);
    let shown: String = src.chars().take(80).collect();
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {shown}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{shown}: {e}"))?;
    check_program(&p).map_err(|e| format!("{shown}: ill-formed bytecode: {e}"))?;
    Ok(p)
}

fn func(p: &Program, i: usize) -> Result<&FunctionCode, String> {
    p.functions.get(i).ok_or_else(|| format!("no function {i}"))
}

fn count(f: &FunctionCode, pred: fn(&Instr) -> bool) -> usize {
    f.instrs.iter().filter(|i| pred(i)).count()
}

fn has(f: &FunctionCode, pred: fn(&Instr) -> bool) -> bool {
    f.instrs.iter().any(pred)
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

/// §13.2.7.3†: each evaluation of a regular expression literal is a new
/// object from the pattern and the flags (`NewRegExp`), whose record is a
/// constant. The body is the text between the first slash and the last, so a
/// `/` inside a class or an escaped one is part of it; the flags follow.
#[test]
fn regex_literals() -> Result<(), String> {
    let p = compile("var r = /a\\/b[/]c/gi;")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::NewRegExp { .. })), 1);
    let site = f.consts.iter().find_map(|c| match c {
        Const::RegExp(s) => Some(s.clone()),
        _ => None,
    });
    let site = site.ok_or("no RegExp constant")?;
    assert_eq!(site.pattern, units("a\\/b[/]c"));
    assert_eq!(site.flags, units("gi"));
    // Two literals with the same text share the constant, but each is an op.
    let p = compile("for (;;) { /x/; /x/y; /x/; }")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::NewRegExp { .. })), 3);
    assert_eq!(
        f.consts
            .iter()
            .filter(|c| matches!(c, Const::RegExp(_)))
            .count(),
        2
    );
    // The empty flags and a literal that contains `//` in a class.
    let p = compile("/[//]/;")?;
    let f = func(&p, 0)?;
    assert!(f.consts.iter().any(
        |c| matches!(c, Const::RegExp(s) if s.pattern == units("[//]") && s.flags.is_empty())
    ));
    Ok(())
}

/// EvaluateGeneratorBody §15.5.2†: the parameters (FunctionDeclarationInstantiation)
/// first, then `GeneratorStart`, then the body; a `yield` is `Yield` followed by
/// the jumps on the resume mode (0 value, 1 throw, 2 return, which is a `return`).
#[test]
fn generator_function() -> Result<(), String> {
    let p = compile("function* g(a) { var x = yield a; return x; }")?;
    let g = func(&p, 1)?;
    assert_eq!(g.flavor, Flavor::Generator);
    assert_eq!(g.kind, FunctionKind::Normal);
    let start = g
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::GeneratorStart))
        .ok_or("no GeneratorStart")?;
    let y = g
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Yield { .. }))
        .ok_or("no Yield")?;
    assert!(start < y);
    // Nothing of the body runs before GeneratorStart but the declarations.
    assert!(
        !g.instrs
            .get(..start)
            .ok_or("short")?
            .iter()
            .any(|i| matches!(i, Instr::Yield { .. } | Instr::Return { .. }))
    );
    let Some(Instr::Yield { src, value, mode }) = g.instrs.get(y).cloned() else {
        return Err("no yield".into());
    };
    // The operand is the parameter, copied to the register the op reads.
    assert!(
        g.instrs
            .get(..y)
            .ok_or("short")?
            .iter()
            .any(|i| matches!(i, Instr::Move { dst, src: 0 } if *dst == src))
    );
    // mode 0 skips ahead; else mode 1 throws the value, else it is returned.
    let Some(Instr::JumpIfFalse { cond, target }) = g.instrs.get(y + 1).cloned() else {
        return Err("no jump on the mode".into());
    };
    assert_eq!(cond, mode);
    assert!(matches!(
        g.instrs.get(y + 4),
        Some(Instr::JumpIfFalse { .. })
    ));
    assert!(matches!(
        g.instrs.get(y + 5),
        Some(Instr::Throw { src }) if *src == value
    ));
    assert!(matches!(
        g.instrs.get(y + 6),
        Some(Instr::Return { src }) if *src == value
    ));
    assert_eq!(target as usize, y + 7);
    // A plain function and a script have none of it.
    let p = compile("function f() { return 1; }")?;
    assert_eq!(func(&p, 1)?.flavor, Flavor::Plain);
    assert!(!has(func(&p, 1)?, |i| matches!(i, Instr::GeneratorStart)));
    Ok(())
}

/// A return resumption of a `yield` inside `try`/`finally` returns through the
/// `finally` block (§27.5.3.4† GeneratorResumeAbrupt with a return completion
/// continues the body as a `return` at the `yield`).
#[test]
fn return_resumption_runs_finally() -> Result<(), String> {
    let p = compile("function* g() { try { yield 1; } finally { cleanup(); } }")?;
    let g = func(&p, 1)?;
    // The resumption's return and the normal exit both enter the one finally
    // block, which is compiled once: one call of `cleanup`.
    assert_eq!(count(g, |i| matches!(i, Instr::Call { .. })), 1);
    assert_eq!(count(g, |i| matches!(i, Instr::Yield { .. })), 1);
    Ok(())
}

/// §15.8.5† and Await §6.2.3.1†: `Await`, then a throw if the mode is 1. An
/// async function has no `GeneratorStart` (its body runs at once, AsyncFunctionStart
/// §27.7.5.1†).
#[test]
fn await_expression() -> Result<(), String> {
    let p = compile("async function f(p) { return (await p) + 1; }")?;
    let f = func(&p, 1)?;
    assert_eq!(f.flavor, Flavor::Async);
    assert!(!has(f, |i| matches!(i, Instr::GeneratorStart)));
    let a = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Await { .. }))
        .ok_or("no Await")?;
    let Some(Instr::Await { src, value, mode }) = f.instrs.get(a).cloned() else {
        return Err("no await".into());
    };
    assert_eq!(src, 0);
    assert!(matches!(
        f.instrs.get(a + 1),
        Some(Instr::JumpIfFalse { cond, target }) if *cond == mode && *target as usize == a + 3
    ));
    assert!(matches!(
        f.instrs.get(a + 2),
        Some(Instr::Throw { src }) if *src == value
    ));
    // The async arrow function keeps the arrow's `this`.
    let p = compile("var h = async (x) => await x;")?;
    let h = func(&p, 1)?;
    assert_eq!(h.flavor, Flavor::Async);
    assert_eq!(h.kind, FunctionKind::Arrow);
    Ok(())
}

/// Async generators: `yield` awaits its operand first (§15.5.5† step 3.b),
/// a return resumption awaits its value (AsyncGeneratorYield §27.6.3.8† step
/// 9), and `return x` awaits `x` (§14.10.1 step 3.b).
#[test]
fn async_generator() -> Result<(), String> {
    let p = compile("async function* g(a) { yield a; return a; }")?;
    let g = func(&p, 1)?;
    assert_eq!(g.flavor, Flavor::AsyncGenerator);
    assert_eq!(count(g, |i| matches!(i, Instr::GeneratorStart)), 1);
    // Await before the yield, on the resumption's return, and before `return a`.
    assert_eq!(count(g, |i| matches!(i, Instr::Await { .. })), 3);
    let y = g
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Yield { .. }))
        .ok_or("no Yield")?;
    assert!(
        g.instrs
            .get(..y)
            .ok_or("short")?
            .iter()
            .any(|i| matches!(i, Instr::Await { .. }))
    );
    // A generator's `return a` is not awaited.
    let p = compile("function* g(a) { return a; }")?;
    assert_eq!(count(func(&p, 1)?, |i| matches!(i, Instr::Await { .. })), 0);
    Ok(())
}

/// Generator, async and async generator methods of an object literal and a
/// class, and in a class's static and private forms.
#[test]
fn generator_and_async_methods() -> Result<(), String> {
    let p = compile(
        "var o = { *g() { yield 1; }, async a() { await 1; }, async *ag() { yield 1; } };
         class C { *g() {} static async m() {} async *#p() {} get x() { return 1; } }",
    )?;
    let flavors: Vec<Flavor> = p.functions.iter().map(|f| f.flavor).collect();
    assert!(flavors.contains(&Flavor::Generator));
    assert!(flavors.contains(&Flavor::Async));
    assert!(flavors.contains(&Flavor::AsyncGenerator));
    for f in &p.functions {
        if f.flavor != Flavor::Plain {
            assert_eq!(f.kind, FunctionKind::Method, "{:?}", f.name);
        }
    }
    Ok(())
}

/// `yield*` in a generator (§15.5.5† step 7): GetIterator, a loop that calls
/// `next`, `throw` or `return` of the inner iterator according to the received
/// mode (`IterCallMethod` 0, 1 and 2), and `YieldDelegate`, which gives the
/// inner result object as it is. Never `Yield`, which wraps a value.
#[test]
fn yield_star_in_a_generator() -> Result<(), String> {
    let p = compile("function* g(it) { var r = yield* it; return r; }")?;
    let g = func(&p, 1)?;
    assert_eq!(count(g, |i| matches!(i, Instr::GetIterator { .. })), 1);
    assert_eq!(count(g, |i| matches!(i, Instr::YieldDelegate { .. })), 1);
    assert!(!has(g, |i| matches!(i, Instr::Yield { .. })));
    assert!(!has(g, |i| matches!(i, Instr::Await { .. })));
    for which in 0..3 {
        assert!(
            g.instrs
                .iter()
                .any(|i| matches!(i, Instr::IterCallMethod { which: w, .. } if *w == which)),
            "IterCallMethod {which}"
        );
    }
    // No `throw` method: the iterator is closed, then a TypeError.
    assert!(has(g, |i| matches!(i, Instr::IterClose { .. })));
    assert!(has(g, |i| matches!(i, Instr::ThrowError { .. })));
    // The loop ends in a back-edge, so a runaway delegate is stoppable.
    assert!(has(g, |i| matches!(i, Instr::Loop { .. })));
    Ok(())
}

/// `yield*` in an async generator: GetIterator with the async hint, each
/// inner result awaited, the value yielded with `Yield` (AsyncGeneratorYield),
/// and a return resumption awaited again.
#[test]
fn yield_star_in_an_async_generator() -> Result<(), String> {
    let p = compile("async function* g(it) { yield* it; }")?;
    let g = func(&p, 1)?;
    assert_eq!(count(g, |i| matches!(i, Instr::GetAsyncIterator { .. })), 1);
    assert!(!has(g, |i| matches!(i, Instr::GetIterator { .. })));
    assert!(!has(g, |i| matches!(i, Instr::YieldDelegate { .. })));
    assert_eq!(count(g, |i| matches!(i, Instr::Yield { .. })), 1);
    // `next`, `throw` and `return` results, the close, the `return`
    // resumption and the missing-`return` case.
    assert!(count(g, |i| matches!(i, Instr::Await { .. })) >= 6);
    Ok(())
}

/// `for await` (§14.7.5.7† with async-iterate): GetIterator with the async
/// hint; each step calls `next` with no argument (`IterCallMethod` 4), awaits
/// the result, checks it (`IterComplete`) and reads `value`; leaving the loop by
/// `break` closes the iterator with `return` (`IterCallMethod` 3) and awaits
/// that, and an Object check of its result.
#[test]
fn for_await() -> Result<(), String> {
    let p = compile("async function f(o) { for await (var x of o) { if (x) break; } }")?;
    let f = func(&p, 1)?;
    assert_eq!(count(f, |i| matches!(i, Instr::GetAsyncIterator { .. })), 1);
    assert!(has(f, |i| matches!(
        i,
        Instr::IterCallMethod { which: 4, .. }
    )));
    assert!(has(f, |i| matches!(i, Instr::IterComplete { .. })));
    assert!(has(f, |i| matches!(i, Instr::IterValue { .. })));
    assert!(has(f, |i| matches!(
        i,
        Instr::IterCallMethod { which: 3, .. }
    )));
    assert!(has(f, |i| matches!(i, Instr::ThrowIfNotObject { .. })));
    // The `next` await, the `break` close's, and the close for a throw.
    assert_eq!(count(f, |i| matches!(i, Instr::Await { .. })), 3);
    // The body is covered by a catch-all that closes and rethrows.
    assert!(!f.handlers.is_empty());
    // A plain `for`-`of` has none of these.
    let p = compile("function f(o) { for (var x of o) { break; } }")?;
    let f = func(&p, 1)?;
    assert!(!has(f, |i| matches!(i, Instr::IterCallMethod { .. })));
    assert!(has(f, |i| matches!(i, Instr::IterNext { .. })));
    Ok(())
}

/// §14.11.2†: ToObject of the expression, a new object environment (an
/// environment object with the object in slot 0), the body inside it. A name
/// the body uses that nothing in it binds is looked up in the object first
/// (`WithHas`), then read (`WithGet`), written (`WithSet`) or called with the
/// object as `this`; a binding declared inside the body is not.
#[test]
fn with_statement() -> Result<(), String> {
    let p = compile("function f(o) { var local = 1; with (o) { x = local; g(); } }")?;
    let f = func(&p, 1)?;
    assert_eq!(count(f, |i| matches!(i, Instr::ToObject { .. })), 1);
    assert!(has(f, |i| matches!(i, Instr::NewEnv { size: 1, .. })));
    // `x`, `g` are looked up; `local` is a binding outside the `with`, so it is
    // looked up too (the object may have a `local` property that shadows it).
    assert_eq!(count(f, |i| matches!(i, Instr::WithHas { .. })), 3);
    assert_eq!(count(f, |i| matches!(i, Instr::WithSet { .. })), 1);
    assert_eq!(count(f, |i| matches!(i, Instr::WithGet { .. })), 2);
    // The call's `this` is the object when the name is found in it.
    let call = f
        .instrs
        .iter()
        .find_map(|i| match i {
            Instr::Call { this, .. } => Some(*this),
            _ => None,
        })
        .ok_or("no call")?;
    assert!(f.instrs.iter().any(|i| matches!(
        i,
        Instr::Move { dst, .. } if *dst == call
    )));
    // A name bound inside the body is not looked up in the object.
    let p = compile("function f(o) { with (o) { let y = 1; y; } }")?;
    let f = func(&p, 1)?;
    assert_eq!(count(f, |i| matches!(i, Instr::WithHas { .. })), 0);
    Ok(())
}

/// A closure made in a `with` body captures its environment, so the name it
/// uses is looked up in the object from inside the closure (one `GetEnvParent`
/// hop to the `with`'s environment), and `typeof` of such a name is `WithGet` or
/// the static `typeof`.
#[test]
fn with_and_closures() -> Result<(), String> {
    let p = compile("function f(o) { with (o) { return function () { return typeof k + z; }; } }")?;
    let inner = func(&p, 2)?;
    assert_eq!(count(inner, |i| matches!(i, Instr::WithHas { .. })), 2);
    assert!(has(inner, |i| matches!(
        i,
        Instr::GetEnvSlot { idx: 0, .. }
    )));
    assert!(has(inner, |i| matches!(
        i,
        Instr::GetGlobalOrUndefined { .. }
    )));
    // The with statement is also fine at the top of a script, in strict-free
    // code, nested, with `delete` and update expressions.
    compile("with ({}) { with ({}) { v++; delete v; v += 1; var w = 2; } }")?;
    Ok(())
}

/// `delete name` (§13.5.1.2† step 5): a global is `DeleteGlobal`, a binding of
/// a function is not deletable (false), a name that a `with` object may have is
/// `WithDelete` first.
#[test]
fn delete_of_a_variable() -> Result<(), String> {
    let p = compile("delete g;")?;
    assert_eq!(
        count(func(&p, 0)?, |i| matches!(i, Instr::DeleteGlobal { .. })),
        1
    );
    let p = compile("function f(a) { return delete a; }")?;
    let f = func(&p, 1)?;
    assert!(!has(f, |i| matches!(i, Instr::DeleteGlobal { .. })));
    assert!(has(f, |i| matches!(i, Instr::LoadBool { flag: false, .. })));
    let p = compile("function f(o) { with (o) { delete q; } }")?;
    let f = func(&p, 1)?;
    assert_eq!(count(f, |i| matches!(i, Instr::WithDelete { .. })), 1);
    assert_eq!(count(f, |i| matches!(i, Instr::DeleteGlobal { .. })), 1);
    Ok(())
}

/// Direct eval (§13.3.6.1† step 6): `DirectEval` with the callee `eval`
/// resolved as a name, the call's `this`, the arguments, the current
/// environment and the record of the scopes. Every binding of the function (and
/// `this`, `new.target`, the function and `arguments`) is in the environment
/// object, by name, in the record; a sloppy function's variable object is a slot
/// with a null-prototype object.
#[test]
fn direct_eval_sloppy() -> Result<(), String> {
    let p = compile("function f(a) { var b = 1; return eval('a + b'); }")?;
    let f = func(&p, 1)?;
    assert_eq!(
        count(f, |i| matches!(i, Instr::DirectEval { argc: 1, .. })),
        1
    );
    assert!(!has(f, |i| matches!(i, Instr::Call { .. })));
    let info = f
        .consts
        .iter()
        .find_map(|c| match c {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .ok_or("no EvalScope")?;
    assert!(!info.strict);
    assert!(info.in_function);
    assert!(!info.in_method);
    assert!(!info.in_derived_constructor);
    let scope = info.scopes.first().ok_or("no scope")?;
    assert_eq!(scope.kind, EvalScopeKind::Function);
    let slot_of = |name: &str| {
        scope
            .names
            .iter()
            .find(|n| n.name == units(name))
            .map(|n| (n.slot, n.kind))
    };
    assert!(matches!(slot_of("a"), Some((_, EvalBinding::Var))));
    assert!(matches!(slot_of("b"), Some((_, EvalBinding::Var))));
    assert!(matches!(
        slot_of("arguments"),
        Some((_, EvalBinding::Arguments))
    ));
    for kind in [
        EvalBinding::This,
        EvalBinding::NewTarget,
        EvalBinding::Callee,
    ] {
        assert!(scope.names.iter().any(|n| n.kind == kind), "{kind:?}");
    }
    // The variable object: created at entry, with a null prototype.
    assert!(scope.var_object.is_some());
    assert!(has(f, |i| matches!(i, Instr::SetLiteralProto { .. })));
    // The record's slots are the environment object's slots: no name shares one.
    let mut slots: Vec<u32> = scope.names.iter().map(|n| n.slot).collect();
    slots.sort_unstable();
    slots.dedup();
    assert_eq!(slots.len(), scope.names.len());
    // A name that the function does not bind is looked up in the variable
    // object first, since eval code may have declared it.
    let p = compile("function f() { eval('var q = 1'); return q; }")?;
    let f = func(&p, 1)?;
    assert!(has(f, |i| matches!(i, Instr::WithHas { .. })));
    assert!(has(f, |i| matches!(i, Instr::GetGlobal { .. })));
    Ok(())
}

/// Strict code has no variable object (the eval code's `var`s are its own,
/// §19.2.1.1† step 24), but still the record.
#[test]
fn direct_eval_strict_and_global() -> Result<(), String> {
    let p = compile("function f(a) { 'use strict'; return eval('a'); }")?;
    let f = func(&p, 1)?;
    assert!(!has(f, |i| matches!(i, Instr::SetLiteralProto { .. })));
    let info = f
        .consts
        .iter()
        .find_map(|c| match c {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .ok_or("no EvalScope")?;
    assert!(info.strict);
    assert_eq!(info.scopes.first().ok_or("scope")?.var_object, None);
    // At the top level of a script: no function scope, the eval's `var`s are
    // global.
    let p = compile("eval('var v = 1'); v;")?;
    let m = func(&p, 0)?;
    assert_eq!(count(m, |i| matches!(i, Instr::DirectEval { .. })), 1);
    assert!(!has(m, |i| matches!(i, Instr::WithHas { .. })));
    // In a method of a class: `super.x` and `new.target` are allowed in eval
    // code; in a derived constructor `super()` too.
    let p = compile(
        "class A {} class B extends A { constructor() { super(); eval('1'); } m() { eval('2'); } }",
    )?;
    let infos: Vec<_> = p
        .functions
        .iter()
        .flat_map(|f| f.consts.iter())
        .filter_map(|c| match c {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(infos.len(), 2);
    assert!(infos.iter().all(|i| i.in_method && i.in_function));
    assert_eq!(infos.iter().filter(|i| i.in_derived_constructor).count(), 1);
    Ok(())
}

/// Only `eval(...)` written as the identifier is direct (§13.3.6.1† step 6:
/// the callee is the IdentifierReference `eval`): a parenthesized `(eval)(x)`
/// is not (the callee is a ParenthesizedExpression), nor are `(0, eval)(x)`,
/// `a.eval(x)` and `eval?.(x)`.
#[test]
fn only_the_plain_name_is_direct() -> Result<(), String> {
    for src in [
        "(eval)('1');",
        "(0, eval)('1');",
        "a.eval('1');",
        "eval?.('1');",
        "eval`1`;",
    ] {
        let p = compile(src)?;
        assert!(
            !p.functions
                .iter()
                .any(|f| has(f, |i| matches!(i, Instr::DirectEval { .. }))),
            "{src}"
        );
    }
    // An arrow function and a nested block inside the eval's function see
    // the same record, one scope per environment object.
    let p = compile("function f(a) { { let b = 1; return () => eval('a + b'); } }")?;
    let arrow = p
        .functions
        .iter()
        .find(|f| f.kind == FunctionKind::Arrow)
        .ok_or("no arrow")?;
    let info = arrow
        .consts
        .iter()
        .find_map(|c| match c {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .ok_or("no EvalScope")?;
    // The arrow's own scope (the variable object), the block's, the function's.
    assert!(info.scopes.len() >= 2);
    assert!(info.scopes.iter().any(|s| s.kind == EvalScopeKind::Block
        && s.names.iter().any(|n| n.name == units("b"))));
    assert!(
        info.scopes
            .iter()
            .any(|s| s.kind == EvalScopeKind::Function
                && s.names.iter().any(|n| n.name == units("a")))
    );
    Ok(())
}

/// NamedEvaluation (§8.4.5†): an anonymous function or class gets the name of
/// the binding, assignment target, property or field it initializes; a named
/// one keeps its own; an anonymous one used otherwise stays anonymous.
#[test]
fn named_evaluation() -> Result<(), String> {
    let p = compile(
        "var a = function () {}; let b = () => 1; const c = class {}; d = function () {};
         var o = { e: function () {}, 'f g': () => 1, [h]: function () {} };
         function k(l = function () {}, { m = () => 2 } = {}, [n = class {}] = []) {}
         var q = function named() {}; (function () {}); var r = (function () {});
         class C { s = function () {}; #t = () => 1; static u = class {}; }
         var v; v ||= function () {}; v &&= () => 1;",
    )?;
    let names: Vec<String> = p
        .functions
        .iter()
        .map(|f| String::from_utf16_lossy(&f.name))
        .collect();
    let want = [
        "a", "b", "c", "d", "e", "f g", "l", "m", "n", "named", "r", "s", "#t", "u", "v",
    ];
    for w in want {
        assert!(
            names.iter().any(|n| n == w),
            "no function named {w}: {names:?}"
        );
    }
    // `[h]: function () {}` is named when the code runs, `(function () {});`
    // is not named: exactly two anonymous functions remain (the script has
    // an empty name too, and the two class initializers of C).
    let anon = p
        .functions
        .iter()
        .filter(|f| f.name.is_empty() && f.kind == FunctionKind::Normal)
        .count();
    assert_eq!(anon, 2, "{names:?}");
    Ok(())
}

/// §10.2.11† step 27.b: a `var arguments` in a function with an `arguments`
/// object shares its binding, which holds the object, not `undefined`. A
/// parameter or a function declaration of that name keeps its own.
#[test]
fn var_arguments() -> Result<(), String> {
    let p = compile("function f() { var arguments; return arguments; }")?;
    let f = func(&p, 1)?;
    assert_eq!(
        count(f, |i| matches!(
            i,
            Instr::CreateMappedArguments { .. } | Instr::CreateUnmappedArguments { .. }
        )),
        1
    );
    let p = compile("function f(arguments) { var arguments; return arguments; }")?;
    let f = func(&p, 1)?;
    assert_eq!(
        count(f, |i| matches!(
            i,
            Instr::CreateMappedArguments { .. } | Instr::CreateUnmappedArguments { .. }
        )),
        0
    );
    // In an arrow function the name is the arrow's own var (no `arguments`).
    let p = compile("var g = () => { var arguments = 1; return arguments; };")?;
    assert_eq!(
        count(func(&p, 1)?, |i| matches!(
            i,
            Instr::CreateMappedArguments { .. } | Instr::CreateUnmappedArguments { .. }
        )),
        0
    );
    Ok(())
}

/// §10.2.11† step 28: with parameter expressions the body's `var`s are in a
/// separate environment, so a closure in a default value does not see them
/// (here `v` is the global, and `a` in the closure is the parameter), while the
/// body does; a `var` that is also a parameter starts with its value.
#[test]
fn separate_environment_for_the_body() -> Result<(), String> {
    let p = compile("function f(a, b = () => v + a) { var v = 1; var a; return b; }")?;
    let arrow = p
        .functions
        .iter()
        .find(|f| f.kind == FunctionKind::Arrow)
        .ok_or("no arrow")?;
    assert!(has(arrow, |i| matches!(i, Instr::GetGlobal { .. })));
    // `a` is the parameter, in the function's environment; `v` is not captured.
    assert_eq!(count(arrow, |i| matches!(i, Instr::GetEnvSlot { .. })), 1);
    // Without parameter expressions there is one scope: the closure sees `v`.
    let p = compile("function f(a, b = 1) { var v = 1; return () => v; }")?;
    let arrow = p
        .functions
        .iter()
        .find(|f| f.kind == FunctionKind::Arrow)
        .ok_or("no arrow")?;
    assert!(!has(arrow, |i| matches!(i, Instr::GetGlobal { .. })));
    // A `var arguments` in such a function starts with the `arguments` object.
    let p = compile("function f(a = 1) { var arguments; return arguments; }")?;
    let f = func(&p, 1)?;
    assert_eq!(
        count(f, |i| matches!(i, Instr::CreateUnmappedArguments { .. })),
        1
    );
    Ok(())
}

/// A corpus of programs with the constructs of this slice, nested in each other
/// and in the earlier slices': every one compiles and passes `check_program`.
#[test]
fn corpus_is_well_formed() -> Result<(), String> {
    let corpus = [
        "async function f() { try { for await (const x of y) { await x; if (x) continue; } } catch (e) { await e; } finally { await 1; } }",
        "async function* g() { try { yield* h(); } finally { await cleanup(); } for await (var a of b) { yield a; } return await 1; }",
        "function* g() { var x = yield; x = yield* [1, 2]; try { yield 1; } catch (e) { yield e; } finally { yield 2; } }",
        "function* g() { for (var x of yield) { switch (x) { case yield: break; default: yield* g(); } } }",
        "var o = { async *[k]() { yield await 1; }, *g() { yield* arguments; }, async m() { return () => await_(this); } };",
        "class C extends D { async m() { super.m(); await 1; } static async *s() { yield super.s(); } *[Symbol.iterator]() { yield this; } }",
        "async () => { for await ([a, b] of c) ; for await (a.b of c) ; for await (let {d} of e) ; };",
        "function f(a = function* () { yield 1; }, b = async () => await a) { with (a) { return b; } }",
        "with (a) { with (b) { c = d; e(); typeof f; delete g; h++; i += 1; for (j in k) ; try { l; } catch (m) { n; } } }",
        "function f() { with (a) { return () => { with (b) { return x; } }; } }",
        "function f(a, b) { eval('1'); { let c; eval('c'); } try { eval(a, b); } catch (e) { eval(e); } return function () { eval('2'); }; }",
        "function f() { 'use strict'; eval('1'); (0, eval)('2'); }",
        "var r = /a/g, s = [/b/y, /c[/]/u], t = { u: /d/s }; if (/e/.test(f)) g = `${/h/}`; for (var m of /i/g[Symbol.matchAll](j)) ;",
        "function f() { var arguments; delete x; delete arguments; delete f; return eval('arguments'); }",
        "label: { var q = async function* named() { yield* arguments; }; }",
        "function f(a, { b = a } = {}, [c = () => b] = [], d = function () { return e; }) { var e = d, a; function g() { return a; } { function h() {} } return eval('a'); }",
        "async function f(a = await_(), ...r) { var r; for await (var x of a) { var a; } }",
    ];
    for src in corpus {
        compile(src)?;
    }
    Ok(())
}
