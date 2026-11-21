//! Tests of the compiler's second slice: destructuring, default and rest
//! parameters, spread, template literals, classes, `for`-`in` and `for`-`of`,
//! the `arguments` object, `new.target` and optional chaining. Each expectation
//! was read against `spec::step`, the op docs in `ops.rs` and ECMA-262 (see the
//! comments), not copied from the output.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::{
    Const, ErrorKind, FunctionCode, FunctionKind, Handler, Instr, Program, check_program,
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

fn count(f: &FunctionCode, pred: fn(&Instr) -> bool) -> usize {
    f.instrs.iter().filter(|i| pred(i)).count()
}

fn has(f: &FunctionCode, pred: fn(&Instr) -> bool) -> bool {
    f.instrs.iter().any(pred)
}

/// An array pattern: `GetIterator`, the `[[Done]]` flag set before each
/// `IterNext` and tested before it (§7.4.9† IteratorStepValue), the iterator
/// closed on normal completion unless done (§8.6.2† step 4: "If
/// iteratorRecord.[[Done]] is false, return ? IteratorClose"), and one catch-all
/// entry that closes it unless done and throws the original value again.
#[test]
fn array_pattern_keeps_done_and_closes_the_iterator() -> Result<(), String> {
    let p = compile("var [a] = b;")?;
    let f = func(&p, 0)?;
    assert_eq!(
        f.instrs.get(2..).ok_or("short")?,
        &[
            Instr::GetGlobal {
                dst: 1,
                key: 1,
                ic: 0
            },
            Instr::GetIterator { dst: 2, src: 1 },
            Instr::LoadBool {
                dst: 3,
                flag: false
            },
            // The element: skip the step when done, else done := true, next().
            Instr::JumpIfTrue { cond: 3, target: 9 },
            Instr::LoadBool { dst: 3, flag: true },
            Instr::IterNext {
                value: 4,
                done: 3,
                iter: 2
            },
            Instr::JumpIfFalse {
                cond: 3,
                target: 10
            },
            Instr::LoadUndefined { dst: 4 },
            Instr::SetGlobal {
                key: 2,
                src: 4,
                ic: 1
            },
            // Normal completion: close unless done.
            Instr::JumpIfTrue {
                cond: 3,
                target: 20
            },
            Instr::IterClose { iter: 2 },
            Instr::Jump { target: 20 },
            // An element threw.
            Instr::GetException { dst: 4 },
            Instr::JumpIfTrue {
                cond: 3,
                target: 17
            },
            Instr::IterClose { iter: 2 },
            Instr::Throw { src: 4 },
            Instr::GetException { dst: 5 },
            Instr::Throw { src: 4 },
            Instr::LoadUndefined { dst: 1 },
            Instr::Return { src: 1 },
        ][..]
    );
    // The close that runs for a throw is covered by its own entry, which comes
    // first (the error of a close is ignored); the element code by the other.
    assert_eq!(
        f.handlers,
        vec![
            Handler {
                start: 16,
                end: 17,
                target: 18
            },
            Handler {
                start: 5,
                end: 11,
                target: 14
            }
        ]
    );
    Ok(())
}

/// An object pattern: RequireObjectCoercible (§7.2.1†), the properties in
/// order with their defaults, and the rest property from the keys of the
/// others, already converted by ToPropertyKey, in consecutive registers
/// (§14.3.3.2† RestBindingInitialization).
#[test]
fn object_pattern_with_defaults_and_rest() -> Result<(), String> {
    let p = compile("function f(o) { let { a, [k]: b = 1, ...r } = o; }")?;
    let f = func(&p, 1)?;
    assert!(has(f, |i| matches!(i, Instr::JumpIfNotNullish { .. })));
    assert!(has(f, |i| matches!(
        i,
        Instr::ThrowError {
            kind: ErrorKind::TypeError,
            ..
        }
    )));
    assert_eq!(count(f, |i| matches!(i, Instr::ToPropertyKey { .. })), 1);
    assert_eq!(
        count(f, |i| matches!(i, Instr::JumpIfNotUndefined { .. })),
        1
    );
    let rest: Vec<&Instr> = f
        .instrs
        .iter()
        .filter(|i| matches!(i, Instr::CopyDataProperties { .. }))
        .collect();
    assert_eq!(rest.len(), 1);
    let Some(&&Instr::CopyDataProperties { nexcl, .. }) = rest.first() else {
        return Err("not a CopyDataProperties".to_string());
    };
    assert_eq!(nexcl, 2, "the keys of `a` and `[k]`");
    assert!(has(f, |i| matches!(i, Instr::NewObject { .. })));
    Ok(())
}

/// Assignment patterns: member targets are evaluated before the value is read
/// (§13.15.5.5† step 1); the expression's value is the right side.
#[test]
fn assignment_pattern_evaluates_the_target_first() -> Result<(), String> {
    let p = compile("var o = {}; [o.a, o[k]] = x; ({ a: o.b = 1 } = x);")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::GetIterator { .. })), 1);
    assert_eq!(count(f, |i| matches!(i, Instr::SetProp { .. })), 2);
    assert_eq!(count(f, |i| matches!(i, Instr::SetElem { .. })), 1);
    // For the first element: `o.a`'s object is copied, then `IterNext`, then the
    // store: a `Move` of the object comes before the first `IterNext`.
    let first_next = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::IterNext { .. }))
        .ok_or("no IterNext")?;
    let first_move = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Move { .. }))
        .ok_or("no Move")?;
    assert!(first_move < first_next);
    Ok(())
}

/// Parameters: `nparams` counts the formal parameters without the rest
/// parameter; `length` stops at the first default (§15.1.5† ExpectedArgumentCount);
/// a non-simple list binds each name in its dead zone (the hole), in order.
#[test]
fn default_and_rest_parameters() -> Result<(), String> {
    let p = compile("function f(a, {b}, c = a, ...r) { return b; }")?;
    let f = func(&p, 1)?;
    assert_eq!((f.nparams, f.length), (3, 2));
    assert_eq!(count(f, |i| matches!(i, Instr::LoadHole { .. })), 4);
    assert!(has(f, |i| matches!(
        i,
        Instr::CreateRestArray { from: 3, .. }
    )));
    assert_eq!(
        count(f, |i| matches!(i, Instr::JumpIfNotUndefined { .. })),
        1
    );
    // A simple list needs none of that.
    let p = compile("function g(a, b) { return a; }")?;
    let g = func(&p, 1)?;
    assert_eq!((g.nparams, g.length), (2, 2));
    assert!(!has(g, |i| matches!(i, Instr::LoadHole { .. })));
    // `length` of an arrow function, a method and a rest-only list.
    let p = compile("var h = (a, b = 1) => 0; var o = { m(x, ...y) {} }; var k = (...z) => 0;")?;
    assert_eq!((func(&p, 1)?.nparams, func(&p, 1)?.length), (2, 1));
    assert_eq!((func(&p, 2)?.nparams, func(&p, 2)?.length), (1, 1));
    assert_eq!((func(&p, 3)?.nparams, func(&p, 3)?.length), (0, 0));
    Ok(())
}

/// A parameter that is read before its own element has run is in its dead zone
/// (§10.2.11† step 21: bindings are created uninitialized for a list with
/// expressions): the reference is checked.
#[test]
fn parameter_dead_zone() -> Result<(), String> {
    let p = compile("function f(a = b, b) { }")?;
    let f = func(&p, 1)?;
    assert!(has(f, |i| matches!(i, Instr::ThrowIfHole { .. })));
    Ok(())
}

/// Spread: a call with a spread argument builds an array by iterating
/// (§13.3.8.1†) and uses `CallSpread`; `new` uses `NewSpread`; an array literal
/// appends with a running index; an object literal copies with
/// `CopyDataProperties` and no excluded keys (§13.2.5.5†).
#[test]
fn spread_in_calls_arrays_and_objects() -> Result<(), String> {
    let p = compile("f(...a, 1); new g(...a); [...a, 1]; ({ ...a, b: 1 });")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::CallSpread { .. })), 1);
    assert_eq!(count(f, |i| matches!(i, Instr::NewSpread { .. })), 1);
    assert_eq!(count(f, |i| matches!(i, Instr::Call { .. })), 0);
    assert_eq!(count(f, |i| matches!(i, Instr::GetIterator { .. })), 3);
    assert!(has(f, |i| matches!(
        i,
        Instr::CopyDataProperties { nexcl: 0, .. }
    )));
    // No spread, no array and no iteration.
    let p = compile("f(1, 2);")?;
    let f = func(&p, 0)?;
    assert!(!has(f, |i| matches!(
        i,
        Instr::NewArray { .. } | Instr::CallSpread { .. }
    )));
    // A trailing elision after a spread sets the length.
    let p = compile("[...a, ,];")?;
    assert!(has(func(&p, 0)?, |i| matches!(i, Instr::SetProp { .. })));
    Ok(())
}

/// Template literals: ToString of each substitution (not `+`'s ToPrimitive),
/// joined with `Add` (§13.2.8.6†); empty strings are not added.
#[test]
fn template_literals() -> Result<(), String> {
    let p = compile("`a${x}b${y}`;")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::ToString { .. })), 2);
    assert_eq!(count(f, |i| matches!(i, Instr::Add { .. })), 3);
    let p = compile("`${x}`;")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::ToString { .. })), 1);
    assert_eq!(
        count(f, |i| matches!(i, Instr::Add { .. })),
        1,
        "empty strings add nothing"
    );
    let p = compile("`plain`;")?;
    assert_eq!(
        count(func(&p, 0)?, |i| matches!(i, Instr::ToString { .. })),
        0
    );
    Ok(())
}

/// A tagged template: the template object comes from `GetTemplateObject` with a
/// site record of cooked and raw strings (§13.2.8.3†, a malformed escape is
/// `undefined` when cooked), and two sites with the same strings are two
/// records (§13.2.8.4†: the cache is per Parse Node).
#[test]
fn tagged_templates_cache_per_site() -> Result<(), String> {
    let p = compile("tag`a${x}\\u{`; tag`a${x}\\u{`;")?;
    let f = func(&p, 0)?;
    let sites: Vec<&Const> = f
        .consts
        .iter()
        .filter(|c| matches!(c, Const::Template(_)))
        .collect();
    assert_eq!(sites.len(), 2, "one record per site");
    let Some(Const::Template(site)) = sites.first().copied() else {
        return Err("not a template".to_string());
    };
    assert_eq!(site.cooked.len(), 2);
    assert_eq!(site.cooked.first(), Some(&Some(vec![u16::from(b'a')])));
    assert_eq!(site.cooked.get(1), Some(&None));
    assert_eq!(
        site.raw.get(1),
        Some(&"\\u{".encode_utf16().collect::<Vec<u16>>())
    );
    assert_eq!(
        count(f, |i| matches!(i, Instr::GetTemplateObject { .. })),
        2
    );
    // The tag's `this` is the object of a member tag.
    let p = compile("o.t`x`;")?;
    assert!(has(func(&p, 0)?, |i| matches!(i, Instr::GetProp { .. })));
    Ok(())
}

/// Object literals: accessors and methods are defined with `DefineMethod`
/// (form 1 getter, 2 setter, 0 method; enumerable), after `SetHomeObject`; a
/// computed key is converted before the value is evaluated (§13.2.5.4†).
#[test]
fn object_literal_accessors_and_computed_keys() -> Result<(), String> {
    let p = compile("({ get a() { return 1; }, set a(v) {}, m() {}, [k]: f() });")?;
    let f = func(&p, 0)?;
    let forms: Vec<u32> = f
        .instrs
        .iter()
        .filter_map(|i| match i {
            Instr::DefineMethod {
                form,
                enumerable: true,
                ..
            } => Some(*form),
            _ => None,
        })
        .collect();
    assert_eq!(forms, vec![1, 2, 0]);
    assert_eq!(count(f, |i| matches!(i, Instr::SetHomeObject { .. })), 3);
    let to_key = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::ToPropertyKey { .. }))
        .ok_or("no ToPropertyKey")?;
    let call = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::Call { .. }))
        .ok_or("no Call")?;
    assert!(to_key < call, "the key is converted before the value runs");
    Ok(())
}

/// A class: the constructor closure, `ClassSetup`, methods defined
/// non-enumerable on the prototype (or the constructor, if static), an
/// initializer for the fields and private methods, and the static elements run
/// once with `this` the class.
#[test]
fn class_with_fields_methods_and_static_block() -> Result<(), String> {
    let p = compile(
        "class A { #p = 1; static s = 2; [k] = 3; m() {} static n() {} get #g() { return 1; } static { this.t = 1; } }",
    )?;
    let f = func(&p, 0)?;
    assert_eq!(
        count(f, |i| matches!(i, Instr::ClassSetup { derived: false, .. })),
        1
    );
    let methods: Vec<(u32, bool)> = f
        .instrs
        .iter()
        .filter_map(|i| match i {
            Instr::DefineMethod {
                form, enumerable, ..
            } => Some((*form, *enumerable)),
            _ => None,
        })
        .collect();
    assert_eq!(methods, vec![(0, false), (0, false)]);
    assert_eq!(count(f, |i| matches!(i, Instr::NewPrivateName { .. })), 2);
    assert_eq!(count(f, |i| matches!(i, Instr::SetInstanceInit { .. })), 1);
    // One call: the static initializer (a static block is run inside it).
    assert_eq!(count(f, |i| matches!(i, Instr::Call { .. })), 1);
    // The constructor is the first function compiled; it is a base class
    // constructor, so it initializes its instance first.
    let c = func(&p, 1)?;
    assert_eq!(c.kind, FunctionKind::Class);
    assert_eq!(String::from_utf16_lossy(&c.name), "A");
    assert_eq!(
        c.instrs,
        vec![
            Instr::GetThis { dst: 0 },
            Instr::GetCallee { dst: 1 },
            Instr::InitInstance { obj: 0, func: 1 },
            Instr::LoadUndefined { dst: 2 },
            Instr::Return { src: 2 },
        ]
    );
    // The instance initializer adds the private getter, then defines the fields
    // in order (§7.3.34† InitializeInstanceElements).
    let inst = p
        .functions
        .iter()
        .find(|g| has(g, |i| matches!(i, Instr::DefinePrivate { form: 2, .. })))
        .ok_or("no instance initializer")?;
    let order: Vec<&str> = inst
        .instrs
        .iter()
        .filter_map(|i| match i {
            Instr::DefinePrivate { form: 2, .. } => Some("getter"),
            Instr::DefinePrivate { form: 0, .. } => Some("private field"),
            Instr::DefineElem { .. } => Some("computed field"),
            _ => None,
        })
        .collect();
    assert_eq!(order, vec!["getter", "private field", "computed field"]);
    Ok(())
}

/// The default constructors: `constructor() {}` initializes the instance, and
/// `constructor(...args) { super(...args); }` hands its arguments to the super
/// constructor without iterating them (§15.7.14† step 14.a).
#[test]
fn default_constructors() -> Result<(), String> {
    let p = compile("class A {} class B extends A {}")?;
    let b = p
        .functions
        .iter()
        .find(|g| g.kind == FunctionKind::Derived)
        .ok_or("no derived constructor")?;
    assert_eq!(
        b.instrs,
        vec![
            Instr::GetCallee { dst: 0 },
            Instr::GetNewTarget { dst: 1 },
            Instr::LoadHole { dst: 2 },
            Instr::CreateRestArray { dst: 3, from: 0 },
            Instr::SuperCallSpread {
                dst: 4,
                func: 0,
                newtarget: 1,
                this: 2,
                args: 3
            },
            Instr::InitInstance { obj: 4, func: 0 },
            Instr::Return { src: 4 },
        ]
    );
    assert!(!has(b, |i| matches!(i, Instr::GetIterator { .. })));
    Ok(())
}

/// A derived constructor: `this` is the hole until `super()` returns, `super()`
/// stores the result and initializes the instance (§13.3.7.1† steps 9 and 10), a
/// `return` goes through `ConstructResult`, and an arrow function reads the same
/// `this` binding with a check.
#[test]
fn derived_constructor_and_super_call() -> Result<(), String> {
    let p = compile("class B extends A { constructor() { super(1); (() => this)(); } }")?;
    let ctor = p
        .functions
        .iter()
        .find(|g| g.kind == FunctionKind::Derived)
        .ok_or("no derived constructor")?;
    assert_eq!(
        count(ctor, |i| matches!(i, Instr::SuperCall { argc: 1, .. })),
        1
    );
    assert_eq!(count(ctor, |i| matches!(i, Instr::InitInstance { .. })), 1);
    assert_eq!(
        count(ctor, |i| matches!(i, Instr::ConstructResult { .. })),
        1
    );
    assert_eq!(count(ctor, |i| matches!(i, Instr::GetThis { .. })), 0);
    let arrow = p
        .functions
        .iter()
        .find(|g| g.kind == FunctionKind::Arrow)
        .ok_or("no arrow")?;
    assert!(has(arrow, |i| matches!(i, Instr::ThrowIfHole { .. })));
    // A spread argument list uses the spread form.
    let p = compile("class B extends A { constructor(...a) { super(...a); } }")?;
    let ctor = p
        .functions
        .iter()
        .find(|g| g.kind == FunctionKind::Derived)
        .ok_or("no derived constructor")?;
    assert_eq!(
        count(ctor, |i| matches!(i, Instr::SuperCallSpread { .. })),
        1
    );
    Ok(())
}

/// `super.x`: `this` first, then the key, then the home object's prototype
/// (§13.3.7.1†); a call keeps `this` as the receiver; assignment is `SetSuper`;
/// `delete super.x` is a ReferenceError.
#[test]
fn super_properties() -> Result<(), String> {
    let p =
        compile("class A extends B { m() { super.x; super[k] = 1; super.f(); delete super.y; } }")?;
    let m = p
        .functions
        .iter()
        .find(|g| has(g, |i| matches!(i, Instr::GetSuperBase { .. })))
        .ok_or("no method")?;
    assert_eq!(count(m, |i| matches!(i, Instr::GetSuperBase { .. })), 4);
    assert_eq!(count(m, |i| matches!(i, Instr::GetSuper { .. })), 2);
    assert_eq!(count(m, |i| matches!(i, Instr::SetSuper { .. })), 1);
    assert!(has(m, |i| matches!(
        i,
        Instr::ThrowError {
            kind: ErrorKind::ReferenceError,
            ..
        }
    )));
    // `this` is read before `GetSuperBase` each time.
    let first_this = m
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::GetThis { .. }))
        .ok_or("no GetThis")?;
    let first_base = m
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::GetSuperBase { .. }))
        .ok_or("no GetSuperBase")?;
    assert!(first_this < first_base);
    // An object literal method has a home object too.
    let p = compile("({ m() { return super.x; } });")?;
    assert!(has(func(&p, 0)?, |i| matches!(
        i,
        Instr::SetHomeObject { .. }
    )));
    Ok(())
}

/// Private names: `#x in o`, reads, writes and compound assignment on `o.#x`.
#[test]
fn private_names() -> Result<(), String> {
    let p = compile("class A { #x = 1; m(o) { o.#x; o.#x = 2; o.#x += 1; o.#x++; o?.#x; } }")?;
    let m = p
        .functions
        .iter()
        .find(|g| has(g, |i| matches!(i, Instr::GetPrivate { .. })))
        .ok_or("no method")?;
    // read, `+=` read, `++` read, `?.` read.
    assert_eq!(count(m, |i| matches!(i, Instr::GetPrivate { .. })), 4);
    // write, `+=` write, `++` write.
    assert_eq!(count(m, |i| matches!(i, Instr::SetPrivate { .. })), 3);
    Ok(())
}

/// `new.target` is `GetNewTarget` in the function itself and a captured binding
/// in an arrow function.
#[test]
fn new_target() -> Result<(), String> {
    let p = compile("function f() { return new.target; }")?;
    assert!(has(func(&p, 1)?, |i| matches!(
        i,
        Instr::GetNewTarget { .. }
    )));
    let p = compile("function f() { return () => new.target; }")?;
    let f = func(&p, 1)?;
    assert!(has(f, |i| matches!(i, Instr::GetNewTarget { .. })));
    let arrow = func(&p, 2)?;
    assert!(!has(arrow, |i| matches!(i, Instr::GetNewTarget { .. })));
    assert!(has(arrow, |i| matches!(i, Instr::GetEnvSlot { .. })));
    Ok(())
}

/// `for`-`of`: the iterator is closed by `break` and `return` with an op that
/// has an exception-table entry of its own (so an error of the close is the
/// completion), by a throw in the body through the loop's catch-all, and never
/// when the loop ends because the iterator is done.
#[test]
fn for_of_closes_the_iterator_on_early_exit() -> Result<(), String> {
    let p = compile("function f(xs) { for (var x of xs) { if (x) break; if (y) return 1; } }")?;
    let f = func(&p, 1)?;
    // A close for `break`, one for `return`, one for a throw (the catch-all).
    assert_eq!(count(f, |i| matches!(i, Instr::IterClose { .. })), 3);
    assert_eq!(count(f, |i| matches!(i, Instr::GetIterator { .. })), 1);
    // Each close but the catch-all's has its own one-op entry, listed before the
    // loop's entry.
    let single: Vec<&Handler> = f.handlers.iter().filter(|h| h.end - h.start == 1).collect();
    assert_eq!(single.len(), 3, "two exits and the catch-all's own close");
    let loop_entry = f
        .handlers
        .iter()
        .position(|h| h.end - h.start > 1)
        .ok_or("no loop entry")?;
    assert_eq!(loop_entry, f.handlers.len() - 1, "inner entries first");
    // `continue` of the loop itself does not close.
    let p = compile("function f(xs) { for (var x of xs) { continue; } }")?;
    assert_eq!(
        count(func(&p, 1)?, |i| matches!(i, Instr::IterClose { .. })),
        1
    );
    Ok(())
}

/// `for`-`in` uses the for-in iterator and never closes it; a lexical head is
/// bound in a fresh environment each iteration when a closure captures it.
#[test]
fn for_in_and_per_iteration_bindings() -> Result<(), String> {
    let p = compile("function f(o) { for (var k in o) ; }")?;
    let f = func(&p, 1)?;
    assert!(has(f, |i| matches!(i, Instr::ForInIterator { .. })));
    assert!(!has(f, |i| matches!(
        i,
        Instr::IterClose { .. } | Instr::GetIterator { .. }
    )));
    assert!(f.handlers.is_empty());
    let p = compile("function f(o) { var fs = []; for (let x of o) fs.push(() => x); }")?;
    let f = func(&p, 1)?;
    // The loop scope's environment is created on entry and again per iteration.
    assert_eq!(count(f, |i| matches!(i, Instr::NewEnv { .. })), 2);
    // `for (let x of x)`: the head's `x` is in its dead zone.
    let p = compile("function f(o) { for (let x of x) ; }")?;
    assert!(has(func(&p, 1)?, |i| matches!(
        i,
        Instr::ThrowIfHole { .. }
    )));
    // A destructuring head, an assignment-target head and a `var` initializer.
    compile("function f(o) { for (var [a, b] of o) ; for ({ c } of o) ; for (o.p in o) ; }")?;
    compile("function f(o) { for (var i = 0 in o) ; }")?;
    Ok(())
}

/// `arguments`: a sloppy function with a simple list gets the mapped object over
/// an environment that holds the parameters; a strict one or one with a
/// non-simple list the unmapped one; an arrow function uses its enclosing
/// function's.
#[test]
fn arguments_objects() -> Result<(), String> {
    let p = compile("function f(a, b) { return arguments; }")?;
    let f = func(&p, 1)?;
    assert!(has(f, |i| matches!(i, Instr::CreateMappedArguments { .. })));
    assert!(
        f.consts
            .contains(&Const::ArgumentsMap(vec![Some(0), Some(1)]))
    );
    let p = compile("function f(a, b) { 'use strict'; return arguments; }")?;
    assert!(has(func(&p, 1)?, |i| matches!(
        i,
        Instr::CreateUnmappedArguments { .. }
    )));
    let p = compile("function f(a = 1) { return arguments; }")?;
    assert!(has(func(&p, 1)?, |i| matches!(
        i,
        Instr::CreateUnmappedArguments { .. }
    )));
    // A repeated parameter name maps only the last one.
    let p = compile("function f(a, a) { return arguments; }")?;
    assert!(
        func(&p, 1)?
            .consts
            .contains(&Const::ArgumentsMap(vec![None, Some(0)]))
    );
    // An arrow function captures the enclosing function's object.
    let p = compile("function f() { return () => arguments; }")?;
    assert!(has(func(&p, 1)?, |i| matches!(
        i,
        Instr::CreateMappedArguments { .. }
    )));
    assert!(!has(func(&p, 2)?, |i| matches!(
        i,
        Instr::CreateMappedArguments { .. } | Instr::CreateUnmappedArguments { .. }
    )));
    // A parameter named `arguments` shadows it; at the top of a script it is a global.
    let p = compile("function f(arguments) { return arguments; }")?;
    assert!(!has(func(&p, 1)?, |i| matches!(
        i,
        Instr::CreateMappedArguments { .. } | Instr::CreateUnmappedArguments { .. }
    )));
    let p = compile("arguments;")?;
    assert!(has(func(&p, 0)?, |i| matches!(i, Instr::GetGlobal { .. })));
    Ok(())
}

/// Optional chaining: each `?.` link tests for `undefined` or `null` and ends
/// the whole chain with `undefined` (§13.3.9.1†); a call keeps `this`.
#[test]
fn optional_chaining() -> Result<(), String> {
    let p = compile("a?.b.c?.[d](e);")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::JumpIfNullish { .. })), 2);
    assert_eq!(count(f, |i| matches!(i, Instr::Call { argc: 1, .. })), 1);
    let nullish: Vec<u32> = f
        .instrs
        .iter()
        .filter_map(|i| match i {
            Instr::JumpIfNullish { target, .. } => Some(*target),
            _ => None,
        })
        .collect();
    let (first, second) = (nullish.first().copied(), nullish.get(1).copied());
    assert_eq!(first, second, "both short-circuit to the same place");
    // The target sets the result to `undefined`.
    assert!(matches!(
        f.instrs.get(first.ok_or("no target")? as usize),
        Some(Instr::LoadUndefined { .. })
    ));
    // `a.b?.()` calls with `this` = a.
    let p = compile("a.b?.();")?;
    assert_eq!(count(func(&p, 0)?, |i| matches!(i, Instr::Call { .. })), 1);
    Ok(())
}

/// Constructs that stay out of scope are still reported, never a panic, also
/// inside the constructs of this slice.
#[test]
fn out_of_scope_constructs_are_not_yet_compiled() -> Result<(), String> {
    let cases: &[(&str, &str)] = &[
        ("class C { *m() {} }", "generator or async methods"),
        ("class C { async m() {} }", "generator or async methods"),
        (
            "class C { static async *m() {} }",
            "generator or async methods",
        ),
        (
            "class C { x = function* () {}; }",
            "generators and async functions",
        ),
        ("var { a = await 1 } = o;", "generators and async functions"),
        ("function f({ a = eval('1') }) {}", "direct eval"),
        ("for (var x of /a/) ;", "regular expression literals"),
        ("`${/a/}`;", "regular expression literals"),
    ];
    for &(src, feature) in cases {
        let c = cps(src);
        let Ok(ast) = parse(&c, SourceGoal::Script) else {
            // `await` outside an async function is not a script the parser accepts.
            continue;
        };
        match compile_script(&ast, &c) {
            Err(CompileError::NotYetCompiled { feature: f, .. }) => assert_eq!(f, feature, "{src}"),
            other => return Err(format!("{src}: expected not yet compiled, got {other:?}")),
        }
    }
    Ok(())
}

/// A corpus of programs with the constructs of this slice, nested in each other
/// and in the first slice's: every one compiles and passes `check_program`.
#[test]
fn corpus_with_the_new_constructs_is_well_formed() -> Result<(), String> {
    let corpus = [
        "var [a, [b, ...c], { d = 1, e: [f] }, ...{ length }] = x;",
        "let { a, ...b } = o, [c = a] = b;",
        "const [{ x }, , y = x] = z; function g({ a, b } = {}, [c] = [], ...[d, e]) {}",
        "function f() { try { for (var [a] of b) { try { continue; } finally { g(); } } } catch ({ message }) { h(message); } }",
        "var o = { a, ...b, get [k]() { return 1; }, set [k](v) {}, async: 1, [k2]: 2 };",
        "var t = tag`x${1}y${[...a]}z`; var u = `${`${a}`}${b}`;",
        "class A { static #p = 1; static m() { return A.#p; } #q() {} get #r() { return 1; } set #r(v) {} t(o) { return #q in o; } }",
        "class B extends (a, b) { x = super.y; static z = this; constructor() { var f = () => super(); f(); } }",
        "class C extends null { static { var self = this; } [Symbol.iterator]() {} 'quoted'() {} 1() {} }",
        "var D = class E { static e = E; m() { return E; } };",
        "function f() { return arguments.length + [...arguments].length; }",
        "function f(a) { a = 2; return arguments[0]; }",
        "function f(a, b) { 'use strict'; return () => arguments; }",
        "a?.b?.[c]?.(d)?.e; a?.[b](c); (a?.b)(); a?.b.c.d(e)(f);",
        "function f() { return new.target ? new new.target(...arguments) : () => new.target; }",
        "outer: for (let a of b) { inner: for (var c in a) { if (c) continue outer; if (a) break inner; } }",
        "function* g() {}",
    ];
    for src in corpus {
        match compile(src) {
            Ok(_) => {}
            Err(e) if e.contains("generators and async functions") => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}
