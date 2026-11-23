//! Unit tests of the compiler: small programs compiled and their bytecode
//! checked against the op list's semantics by hand (each expectation was read
//! against `spec::step` and ECMA-262, not copied from the output), the
//! "not yet compiled" cases, and structural invariants over a corpus.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::{
    Const, ErrorKind, FunctionCode, FunctionKind, GlobalDecls, Handler, Instr, Program, Span,
    VarScoped, check_program,
};
use clazel_js_vm::compile::{CompileError, compile_script};

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

fn text(s: &str) -> Const {
    Const::String(s.encode_utf16().collect())
}

#[test]
fn global_var_and_arithmetic() -> Result<(), String> {
    // `var` at the top of a script is a property of the global object: a
    // reference is a global access, the initializer a SetGlobal, and the
    // variable itself is created by DeclareGlobals (§16.1.7† step 17).
    let p = compile("var x = 1 + 2;")?;
    let f = func(&p, 0)?;
    assert_eq!(f.kind, FunctionKind::Script);
    assert_eq!(
        f.consts,
        vec![
            Const::GlobalDeclarations(GlobalDecls {
                lexical: vec![],
                var_scoped: vec![VarScoped::Var("x".encode_utf16().collect())],
                annexb: vec![],
            }),
            text("x")
        ]
    );
    assert_eq!(
        f.instrs,
        vec![
            Instr::LoadUndefined { dst: 0 },
            Instr::DeclareGlobals { k: 0 },
            Instr::LoadInt { dst: 2, imm: 1 },
            Instr::LoadInt { dst: 3, imm: 2 },
            Instr::Add { dst: 1, a: 2, b: 3 },
            Instr::SetGlobal {
                key: 1,
                src: 1,
                ic: 0
            },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ]
    );
    Ok(())
}

#[test]
fn parameters_are_the_first_registers() -> Result<(), String> {
    let p = compile("function f(a, b) { return a + b; }")?;
    // The script declares `f` on the global object (§16.1.7† step 16).
    let main = func(&p, 0)?;
    assert_eq!(
        main.consts,
        vec![Const::GlobalDeclarations(GlobalDecls {
            lexical: vec![],
            var_scoped: vec![VarScoped::Function {
                name: "f".encode_utf16().collect(),
                func: 1
            }],
            annexb: vec![],
        })]
    );
    assert_eq!(
        main.instrs,
        vec![
            Instr::LoadUndefined { dst: 0 },
            Instr::DeclareGlobals { k: 0 },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ]
    );
    let f = func(&p, 1)?;
    assert_eq!(
        (f.nparams, f.kind, f.strict),
        (2, FunctionKind::Normal, false)
    );
    assert_eq!(f.name, "f".encode_utf16().collect::<Vec<u16>>());
    // `a` and `b` are registers 0 and 1: no environment object, no check.
    assert_eq!(
        f.instrs,
        vec![
            Instr::GetCalleeEnv { dst: 2 },
            Instr::Add { dst: 3, a: 0, b: 1 },
            Instr::Return { src: 3 },
            Instr::LoadUndefined { dst: 3 },
            Instr::Return { src: 3 },
        ]
    );
    Ok(())
}

#[test]
fn captured_binding_lives_in_an_environment() -> Result<(), String> {
    let p = compile("function f() { let x = 1; return function() { return x; }; }")?;
    // `f`: `x` is captured, so its scope creates an environment object whose
    // parent is the callee's, stores into its slot, and closes over it.
    assert_eq!(
        func(&p, 1)?.instrs,
        vec![
            Instr::GetCalleeEnv { dst: 0 },
            Instr::NewEnv {
                dst: 1,
                parent: 0,
                size: 1
            },
            Instr::LoadInt { dst: 2, imm: 1 },
            Instr::SetEnvSlot {
                env: 1,
                idx: 0,
                src: 2
            },
            Instr::NewClosure {
                dst: 2,
                func: 2,
                env: 1
            },
            Instr::Return { src: 2 },
            Instr::LoadUndefined { dst: 2 },
            Instr::Return { src: 2 },
        ]
    );
    // The inner function reads the slot of its callee environment, and the
    // read is checked: a closure may run before `let x` does (§9.1.1.1.6).
    assert_eq!(
        func(&p, 2)?.instrs,
        vec![
            Instr::GetCalleeEnv { dst: 0 },
            Instr::GetEnvSlot {
                dst: 1,
                env: 0,
                idx: 0
            },
            Instr::ThrowIfHole { src: 1 },
            Instr::Return { src: 1 },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ]
    );
    Ok(())
}

#[test]
fn nested_environments_are_reached_by_parent_hops() -> Result<(), String> {
    let p = compile(
        "function f() { var a = 1; return function() { var b = 2; return function() { return a + b; }; }; }",
    )?;
    let inner = func(&p, 3)?;
    // The closure's callee environment is the middle function's, which holds
    // `b` (no hop); `a` is in its parent (one hop).
    let hops = inner
        .instrs
        .iter()
        .filter(|i| matches!(i, Instr::GetEnvParent { env: 0, .. }))
        .count();
    assert_eq!(hops, 1, "{:?}", inner.instrs);
    let slots: Vec<_> = inner
        .instrs
        .iter()
        .filter(|i| matches!(i, Instr::GetEnvSlot { .. }))
        .collect();
    assert_eq!(slots.len(), 2);
    Ok(())
}

#[test]
fn temporal_dead_zone_checks() -> Result<(), String> {
    // After the declaration, in the same function: no check.
    let p = compile("let a = 1; a;")?;
    assert!(
        !func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::ThrowIfHole { .. }))
    );
    // Its own initializer reads it before it exists: checked (§14.3.1.2). At the
    // top level of a script the binding is the global declarative record's: the
    // read is a global read, which throws for an uninitialized binding
    // (§9.1.1.1.6 step 2), and the declaration initializes it
    // (InitializeReferencedBinding).
    let p = compile("let b = b;")?;
    let f = func(&p, 0)?;
    assert_eq!(
        f.instrs,
        vec![
            Instr::LoadUndefined { dst: 0 },
            Instr::DeclareGlobals { k: 0 },
            Instr::GetGlobal {
                dst: 1,
                key: 1,
                ic: 0
            },
            Instr::InitGlobalLexical { key: 1, src: 1 },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ]
    );
    // In a function it is a register, checked.
    let p = compile("function f() { let b = b; }")?;
    assert!(
        func(&p, 1)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::ThrowIfHole { .. }))
    );
    // A `switch` clause can skip a declaration: checked even after it.
    let p = compile("switch (0) { case 0: let s = 1; case 1: s; }")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::ThrowIfHole { .. }))
    );
    // Reading before the declaration, in the same function.
    let p = compile("{ c; let c = 1; }")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::ThrowIfHole { .. }))
    );
    Ok(())
}

#[test]
fn const_assignment_throws_a_type_error() -> Result<(), String> {
    let p = compile("function f() { const c = 1; c = 2; }")?;
    let f = func(&p, 1)?;
    assert!(f.instrs.contains(&Instr::ThrowError {
        kind: ErrorKind::TypeError,
        msg: 0
    }));
    assert_eq!(f.consts, vec![text("Assignment to constant variable.")]);
    // At the top level of a script the constant is in the global declarative
    // record, and the write is a global write (SetMutableBinding §9.1.1.1.5
    // step 5 throws).
    let p = compile("const c = 1; c = 2;")?;
    let f = func(&p, 0)?;
    assert!(
        f.instrs
            .iter()
            .any(|i| matches!(i, Instr::InitGlobalLexical { .. }))
    );
    assert!(
        f.instrs
            .iter()
            .any(|i| matches!(i, Instr::SetGlobal { .. }))
    );
    Ok(())
}

#[test]
fn loops_end_in_loop_ops() -> Result<(), String> {
    let p = compile("var i = 0; while (i < 3) { i++; }")?;
    let f = func(&p, 0)?;
    let backs: Vec<_> = f
        .instrs
        .iter()
        .enumerate()
        .filter(|(_, i)| matches!(i, Instr::Loop { .. }))
        .collect();
    assert_eq!(backs.len(), 1);
    // The back-edge goes to the test, which comes first.
    if let Some((at, Instr::Loop { target })) = backs.first() {
        assert!((*target as usize) < *at);
    }
    // No forward jump is a Loop and no backward jump is a Jump.
    for (at, i) in f.instrs.iter().enumerate() {
        match i {
            Instr::Jump { target } => assert!((*target as usize) > at),
            Instr::Loop { target } => assert!((*target as usize) <= at),
            _ => {}
        }
    }
    Ok(())
}

#[test]
fn for_loop_with_a_local_counter() -> Result<(), String> {
    let p =
        compile("function f(n) { let s = 0; for (let i = 0; i < n; i++) { s += i; } return s; }")?;
    assert_eq!(
        func(&p, 1)?.instrs,
        vec![
            Instr::GetCalleeEnv { dst: 1 },
            Instr::LoadHole { dst: 2 },
            Instr::LoadInt { dst: 2, imm: 0 },
            Instr::LoadHole { dst: 3 },
            Instr::LoadInt { dst: 3, imm: 0 },
            Instr::Lt { dst: 4, a: 3, b: 0 },
            Instr::JumpIfFalse {
                cond: 4,
                target: 10
            },
            Instr::Add { dst: 2, a: 2, b: 3 },
            Instr::Inc { dst: 3, src: 3 },
            Instr::Loop { target: 5 },
            Instr::Return { src: 2 },
            Instr::LoadUndefined { dst: 3 },
            Instr::Return { src: 3 },
        ]
    );
    Ok(())
}

#[test]
fn per_iteration_environments() -> Result<(), String> {
    // A closure over the loop variable gets a copy of the environment per
    // iteration (§14.7.4.4).
    let p = compile("for (let i = 0; i < 3; i++) { fs.push(() => i); }")?;
    let f = func(&p, 0)?;
    let news = f
        .instrs
        .iter()
        .filter(|i| matches!(i, Instr::NewEnv { .. }))
        .count();
    assert_eq!(
        news, 3,
        "one for the scope, one after the initializer, one per iteration"
    );
    Ok(())
}

#[test]
fn try_catch_finally() -> Result<(), String> {
    let p = compile("try { f(); } catch (e) { g(e); } finally { h(); }")?;
    let f = func(&p, 0)?;
    // The try block is covered by the catch, then try block and catch by the
    // finally's own rethrow path; each target begins with GetException.
    assert_eq!(
        f.handlers,
        vec![
            Handler {
                start: 1,
                end: 4,
                target: 5
            },
            Handler {
                start: 1,
                end: 11,
                target: 12
            }
        ]
    );
    for h in &f.handlers {
        assert!(matches!(
            f.instrs.get(h.target as usize),
            Some(Instr::GetException { .. })
        ));
    }
    // The finally block ends by rethrowing if it was entered by an exception.
    assert!(f.instrs.iter().any(|i| matches!(i, Instr::Throw { .. })));
    Ok(())
}

#[test]
fn return_through_finally_goes_through_the_finally() -> Result<(), String> {
    let p = compile("function f() { try { return 1; } finally { g(); } }")?;
    let f = func(&p, 1)?;
    // No `Return` of the 1 before the finally's call: the value is saved, the
    // completion code set and the finally entered; the dispatch returns.
    let first_return = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Return { .. }));
    let call = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Call { .. }));
    assert!(matches!((first_return, call), (Some(r), Some(c)) if c < r));
    Ok(())
}

#[test]
fn break_and_continue_with_labels() -> Result<(), String> {
    let p = compile("l: for (;;) { for (;;) { continue l; } }")?;
    assert_eq!(
        func(&p, 0)?.instrs,
        vec![
            Instr::LoadUndefined { dst: 0 },
            // `continue l` goes to the end of the outer body, which is its back-edge.
            Instr::Jump { target: 3 },
            Instr::Loop { target: 1 },
            Instr::Loop { target: 1 },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ]
    );
    Ok(())
}

#[test]
fn switch_tests_in_order_then_the_default() -> Result<(), String> {
    let p = compile("switch (x) { case 1: a; break; default: b; }")?;
    let f = func(&p, 0)?;
    assert!(f.instrs.contains(&Instr::StrictEq { dst: 3, a: 1, b: 2 }));
    assert!(
        f.instrs
            .iter()
            .any(|i| matches!(i, Instr::JumpIfTrue { .. }))
    );
    Ok(())
}

#[test]
fn member_access_and_calls() -> Result<(), String> {
    let p = compile("o.m(3);")?;
    // `this` is the object (§13.3.6.1), the arguments are consecutive registers.
    assert_eq!(
        func(&p, 0)?.instrs,
        vec![
            Instr::LoadUndefined { dst: 0 },
            Instr::GetGlobal {
                dst: 3,
                key: 0,
                ic: 0
            },
            Instr::GetProp {
                dst: 2,
                obj: 3,
                key: 1,
                ic: 1
            },
            Instr::LoadInt { dst: 4, imm: 3 },
            Instr::Call {
                dst: 1,
                callee: 2,
                this: 3,
                args: 4,
                argc: 1
            },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ]
    );
    let p = compile("f(1);")?;
    assert!(
        func(&p, 0)?
            .instrs
            .contains(&Instr::LoadUndefined { dst: 3 }),
        "this is undefined"
    );
    let p = compile("new F(1, 2);")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::New { argc: 2, .. })),
        "new"
    );
    Ok(())
}

#[test]
fn object_and_array_literals() -> Result<(), String> {
    let p = compile("var a = [1, , 2];")?;
    let f = func(&p, 0)?;
    assert!(f.instrs.contains(&Instr::NewArray { dst: 1, len: 3 }));
    assert!(
        f.instrs.contains(&Instr::LoadHole { dst: 3 }),
        "an elision stores the hole"
    );
    let p = compile("var o = { a: 1, [k]: 2, 3: 4 };")?;
    let f = func(&p, 0)?;
    assert!(f.instrs.contains(&Instr::NewObject { dst: 1 }));
    assert_eq!(
        f.instrs
            .iter()
            .filter(|i| matches!(i, Instr::DefineProp { .. }))
            .count(),
        1
    );
    assert_eq!(
        f.instrs
            .iter()
            .filter(|i| matches!(i, Instr::DefineElem { .. }))
            .count(),
        2
    );
    // CreateDataPropertyOrThrow, never Set: no store op at all.
    assert!(!f.instrs.iter().any(|i| matches!(
        i,
        Instr::SetProp { .. } | Instr::SetElem { .. } | Instr::SetLiteralProto { .. }
    )));
    Ok(())
}

/// `__proto__: v` sets the prototype (§13.2.5.5† step 7); a shorthand, a
/// computed or a method `__proto__` defines a property.
#[test]
fn proto_in_an_object_literal() -> Result<(), String> {
    let count = |src: &str, pred: fn(&Instr) -> bool| -> Result<usize, String> {
        let p = compile(src)?;
        Ok(func(&p, 0)?.instrs.iter().filter(|i| pred(i)).count())
    };
    let setter = |i: &Instr| matches!(i, Instr::SetLiteralProto { .. });
    let define = |i: &Instr| {
        matches!(
            i,
            Instr::DefineProp { .. } | Instr::DefineElem { .. } | Instr::DefineMethod { .. }
        )
    };
    assert_eq!(count("({ __proto__: p });", setter)?, 1);
    assert_eq!(count("({ \"__proto__\": p });", setter)?, 1);
    assert_eq!(count("({ __proto__: p });", define)?, 0);
    assert_eq!(count("({ __proto__ });", setter)?, 0);
    assert_eq!(count("({ ['__proto__']: p });", setter)?, 0);
    assert_eq!(count("({ ['__proto__']: p });", define)?, 1);
    assert_eq!(count("({ __proto__() {} });", setter)?, 0);
    assert_eq!(count("({ __proto__() {} });", define)?, 1);
    Ok(())
}

/// `typeof` of a global does not throw for an undeclared name (§13.5.3.1
/// step 2.a); any other operand reads normally.
#[test]
fn typeof_of_a_global() -> Result<(), String> {
    let p = compile("typeof undeclared;")?;
    let f = func(&p, 0)?;
    assert!(
        f.instrs
            .iter()
            .any(|i| matches!(i, Instr::GetGlobalOrUndefined { .. }))
    );
    assert!(
        !f.instrs
            .iter()
            .any(|i| matches!(i, Instr::GetGlobal { .. }))
    );
    assert!(f.instrs.iter().any(|i| matches!(i, Instr::TypeOf { .. })));
    let p = compile("typeof undeclared.x;")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::GetGlobal { .. }))
    );
    Ok(())
}

/// Unary `+` is ToNumber (§13.5.4.1†), not a multiplication.
#[test]
fn unary_plus_is_to_number() -> Result<(), String> {
    let p = compile("+a;")?;
    let f = func(&p, 0)?;
    assert!(f.instrs.iter().any(|i| matches!(i, Instr::ToNumber { .. })));
    assert!(!f.instrs.iter().any(|i| matches!(i, Instr::Mul { .. })));
    Ok(())
}

/// The declaration record lists the script's `var`s (also those in blocks),
/// functions and Annex B block functions in source order; a script that
/// declares none has no `DeclareGlobals`.
#[test]
fn global_declaration_record() -> Result<(), String> {
    let name = |s: &str| -> Vec<u16> { s.encode_utf16().collect() };
    let p = compile(
        "var a; function f() { var inner; } { function g() {} } if (a) { var b, c; } var a;",
    )?;
    let f = func(&p, 0)?;
    let Some(Const::GlobalDeclarations(d)) = f
        .consts
        .iter()
        .find(|c| matches!(c, Const::GlobalDeclarations(_)))
    else {
        return Err("no record".to_string());
    };
    assert!(d.lexical.is_empty());
    assert_eq!(d.annexb, vec![name("g")]);
    // The top-level `let`, `const` and `class` names are in the record, with
    // whether each is a constant (§16.1.7† step 13), and nothing else is.
    let p =
        compile("let x = 1; const y = 2, z = 3; class C {} { let w; } function g() { let v; }")?;
    let Some(Const::GlobalDeclarations(d)) = func(&p, 0)?
        .consts
        .iter()
        .find(|c| matches!(c, Const::GlobalDeclarations(_)))
    else {
        return Err("no record".to_string());
    };
    assert_eq!(
        d.lexical,
        vec![
            (name("x"), false),
            (name("y"), true),
            (name("z"), true),
            (name("C"), false)
        ]
    );
    let p = compile(
        "var a; function f() { var inner; } { function g() {} } if (a) { var b, c; } var a;",
    )?;
    let f = func(&p, 0)?;
    let Some(Const::GlobalDeclarations(d)) = f
        .consts
        .iter()
        .find(|c| matches!(c, Const::GlobalDeclarations(_)))
    else {
        return Err("no record".to_string());
    };
    let names: Vec<(bool, Vec<u16>)> = d
        .var_scoped
        .iter()
        .map(|v| match v {
            VarScoped::Var(n) => (false, n.clone()),
            VarScoped::Function { name, .. } => (true, name.clone()),
        })
        .collect();
    assert_eq!(
        names,
        vec![
            (false, name("a")),
            (true, name("f")),
            (false, name("b")),
            (false, name("c")),
            (false, name("a")),
        ]
    );
    for src in [
        "1 + 2;",
        "let x = 1;",
        "function f() { var y; }",
        "{ let x = 1; }",
        "function f() { let x; }",
    ] {
        let p = compile(src)?;
        let has = func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::DeclareGlobals { .. }));
        assert_eq!(
            has,
            src.starts_with("function") || src.starts_with("let"),
            "{src}"
        );
    }
    Ok(())
}

#[test]
fn logical_and_conditional_operators() -> Result<(), String> {
    let p = compile("x = y || z;")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::JumpIfTrue { .. }))
    );
    let p = compile("x = y ?? z;")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::JumpIfNotNullish { .. }))
    );
    let p = compile("x &&= 1;")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::JumpIfFalse { .. }))
    );
    Ok(())
}

#[test]
fn evaluation_order_of_a_local_left_operand() -> Result<(), String> {
    // `x + (x = 5)` reads x first: a copy is taken before the assignment.
    let p = compile("function f(x) { return x + (x = 5); }")?;
    let f = func(&p, 1)?;
    assert!(
        f.instrs
            .iter()
            .any(|i| matches!(i, Instr::Move { src: 0, .. })),
        "the old value of x is copied out of its register: {:?}",
        f.instrs
    );
    // Without an assignment on the right, no copy.
    let p = compile("function f(x) { return x + 5; }")?;
    assert!(
        !func(&p, 1)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::Move { .. }))
    );
    Ok(())
}

#[test]
fn arrow_functions_capture_this_lexically() -> Result<(), String> {
    let p = compile("function f() { return () => this; }")?;
    let outer = func(&p, 1)?;
    assert!(
        outer
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::GetThis { .. }))
    );
    assert!(
        outer
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::SetEnvSlot { .. }))
    );
    let inner = func(&p, 2)?;
    assert_eq!(inner.kind, FunctionKind::Arrow);
    assert!(
        !inner
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::GetThis { .. }))
    );
    assert!(
        inner
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::GetEnvSlot { .. }))
    );
    Ok(())
}

#[test]
fn named_function_expression_binds_its_name() -> Result<(), String> {
    let p = compile("var f = function g() { return g; };")?;
    let g = func(&p, 1)?;
    assert!(
        g.instrs
            .iter()
            .any(|i| matches!(i, Instr::GetCallee { .. }))
    );
    assert_eq!(g.name, "g".encode_utf16().collect::<Vec<u16>>());
    // Assigning to it: ignored in sloppy mode, a TypeError in strict mode (§15.2.5).
    let p = compile("(function g() { g = 1; });")?;
    assert!(
        !func(&p, 1)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::ThrowError { .. }))
    );
    let p = compile("(function g() { 'use strict'; g = 1; });")?;
    assert!(func(&p, 1)?.strict);
    assert!(
        func(&p, 1)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::ThrowError { .. }))
    );
    Ok(())
}

#[test]
fn annex_b_block_function_hoisting() -> Result<(), String> {
    // Sloppy: the function is also assigned to a global `h` when evaluated.
    let p = compile("{ function h() {} }")?;
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::SetGlobal { .. }))
    );
    // Strict: block-scoped only.
    let p = compile("'use strict'; { function h() {} }")?;
    assert!(
        !func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::SetGlobal { .. }))
    );
    // Blocked by an enclosing `let`.
    let p = compile("function f() { let h; { function h() {} } }")?;
    assert!(
        !func(&p, 1)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::SetGlobal { .. }))
    );
    Ok(())
}

#[test]
fn every_op_has_a_span_of_its_node() -> Result<(), String> {
    let src = "x = a + b;";
    let p = compile(src)?;
    let f = func(&p, 0)?;
    assert_eq!(f.spans.len(), f.instrs.len());
    let add = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Add { .. }))
        .ok_or("no Add")?;
    assert_eq!(f.spans.get(add), Some(&Span { start: 4, end: 9 }));
    let set = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::SetGlobal { .. }))
        .ok_or("no SetGlobal")?;
    assert_eq!(f.spans.get(set), Some(&Span { start: 0, end: 1 }));
    for s in &f.spans {
        assert!(s.start <= s.end && s.end <= src.chars().count());
    }
    Ok(())
}

#[test]
fn numbers_become_ints_or_constants() -> Result<(), String> {
    let p = compile("x = [1, 1.5, 0x10, -1, -0, 4294967296, 10n];")?;
    let f = func(&p, 0)?;
    assert!(f.instrs.contains(&Instr::LoadInt { dst: 3, imm: 1 }));
    assert!(f.instrs.contains(&Instr::LoadInt { dst: 3, imm: 16 }));
    assert!(f.instrs.contains(&Instr::LoadInt { dst: 3, imm: -1 }));
    assert!(f.consts.contains(&Const::Number(1.5f64.to_bits())));
    assert!(f.consts.contains(&Const::Number((-0.0f64).to_bits())));
    assert!(f.consts.contains(&Const::Number(4294967296.0f64.to_bits())));
    assert!(
        f.consts
            .contains(&Const::BigInt("10".encode_utf16().collect()))
    );
    Ok(())
}

#[test]
fn string_values_resolve_escapes() -> Result<(), String> {
    let p = compile("x = 'a\\u0062\\n';")?;
    assert!(
        func(&p, 0)?
            .consts
            .contains(&Const::String(vec![0x61, 0x62, 0x0A]))
    );
    // A name with an escape is its resolved name.
    let p = compile("var \\u0061b = 1;")?;
    assert!(func(&p, 0)?.consts.contains(&text("ab")));
    Ok(())
}

/// A script and a module are compiled by different entry points: the wrong one
/// is an internal error, never a panic or a wrong program.
#[test]
fn goal_mismatch() -> Result<(), String> {
    let c = cps("export var a = 1;");
    let ast = parse(&c, SourceGoal::Module).map_err(|_| "module does not parse".to_string())?;
    assert!(matches!(
        compile_script(&ast, &c),
        Err(CompileError::Internal(_))
    ));
    let c = cps("var a = 1;");
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "script does not parse".to_string())?;
    assert!(matches!(
        clazel_js_vm::compile::compile_module(&ast, &c),
        Err(CompileError::Internal(_))
    ));
    Ok(())
}

/// A corpus of programs that compile; each result passes `check_program`, and
/// every jump target, span and function index is in range.
#[test]
fn corpus_is_well_formed() -> Result<(), String> {
    let corpus = [
        "",
        ";",
        "var a, b = 1, c = b + 1; a = c;",
        "function f(a, b, a) { return b; }",
        "function f() { var x = 1; { let x = 2; { const x = 3; } } return x; }",
        "function f(n) { return n < 2 ? n : f(n - 1) + f(n - 2); }",
        "function counter() { var n = 0; return { inc: function() { return ++n; }, get: () => n }; }",
        "do { x++; } while (x < 10);",
        "a: { b: { break a; } }",
        "a: while (1) { b: while (2) { if (x) continue a; else break b; } }",
        "switch (v) { case 1: case 2: f(); default: g(); case 3: h(); }",
        "switch (v) { }",
        "switch (v) { default: }",
        "try { a(); } catch (e) { b(e); }",
        "try { a(); } finally { b(); }",
        "try { try { a(); } finally { b(); } } catch { c(); }",
        "function f() { for (var i = 0; i < 3; i++) { try { if (i) continue; if (i > 1) break; return i; } finally { g(); } } }",
        "function f() { try { return 1; } finally { try { return 2; } finally { return 3; } } }",
        "function f() { l: try { break l; } finally { g(); } }",
        "for (var i = 0; i < 3; i++) { for (let j = 0; j < 3; j++) { fs.push(() => i + j); } }",
        "for (;;) { break; }",
        "for (let i = 0, j = 1; i < j; i++, j--) ;",
        "x = a ? b ? 1 : 2 : 3;",
        "x = a && b || c && d;",
        "x ||= y; x &&= y; x ??= y; x += 1; x **= 2; x >>>= 1;",
        "o.a.b.c = o[a][b];",
        "o.a += 1; o[a] -= 1; o.a ||= 2; o[a]++; --o.b;",
        "f(a, b)(c).d[e](f);",
        "new new F(1)(2);",
        "x = typeof a.b + typeof function() {};",
        "x = void 0, y = !z, w = ~v, u = -t, s = +r;",
        "x = a in b; y = a instanceof B; z = a == b != c === d !== e;",
        "x = a << 1 >> 2 >>> 3 & 4 | 5 ^ 6;",
        "x = a ** b ** c % d / e * f;",
        "x = delete o.a + delete o[b] + delete 1;",
        "var f = function() { return this; }; var g = () => () => this;",
        "function f() { var self = this; return function() { return self; }; }",
        "(function() { 'use strict'; var x = 1; return x; })();",
        "x = { a, b: 1, 'c': 2, 3: 3, [4]: 4, m() { return 1; } };",
        "x = [, , 1, , ];",
        "{ function a() {} function a() {} }",
        "function f(a) { { function a() {} } }",
        "function f() { { function g() {} } return g; }",
        "var x; { let y = 1; { function z() { return y; } } }",
        "let x = 1; function f() { return x; } x = 2;",
        "function f() { return function() { return function() { return a; }; }; } var a;",
        "function f(a) { return () => a; }",
        "function f(a, b) { return () => { a = b; }; }",
        "function f() { let a, b; return () => b; }",
        "function f() { l: for (;;) { let x = 1; (() => x)(); continue l; } }",
        "if (a) b; else if (c) d; else e;",
        "throw new Error('x');",
        "x = function() {}, y = () => {};",
        "debugger;",
    ];
    for src in corpus {
        let p = compile(src)?;
        for f in &p.functions {
            assert_eq!(f.spans.len(), f.instrs.len(), "{src}");
        }
        let n = src.chars().count();
        for f in &p.functions {
            for s in &f.spans {
                assert!(s.start <= s.end && s.end <= n, "{src}: span {s:?}");
            }
        }
    }
    Ok(())
}

/// Registers are bounded by the frame: the number of registers is what the
/// function says, never more.
#[test]
fn many_arguments_and_locals() -> Result<(), String> {
    let n: u32 = if cfg!(miri) { 20 } else { 200 };
    let params: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let src = format!(
        "function f({}) {{ return p0 + p{}; }} f({});",
        params.join(", "),
        n.saturating_sub(1),
        (0..n).map(|i| i.to_string()).collect::<Vec<_>>().join(", ")
    );
    let p = compile(&src)?;
    assert_eq!(func(&p, 1)?.nparams, n);
    Ok(())
}

/// The parser allows nesting up to 1024 levels; the compiler recurses on it
/// and must not overflow the stack.
#[test]
fn deeply_nested_programs_compile() -> Result<(), String> {
    // Miri is about a hundred times slower: a shallower program there.
    let depth = if cfg!(miri) { 40 } else { 900 };
    let parens = format!("x = {}1{};", "(".repeat(depth), ")".repeat(depth));
    compile(&parens)?;
    let blocks = format!("{}x;{}", "{".repeat(depth), "}".repeat(depth));
    compile(&blocks)?;
    let sum = format!("x = {};", vec!["a"; depth].join(" + "));
    compile(&sum)?;
    // A call is two nodes deep (the call and its arguments).
    let calls = format!("x = {}a{};", "f(".repeat(depth / 3), ")".repeat(depth / 3));
    compile(&calls)?;
    Ok(())
}
