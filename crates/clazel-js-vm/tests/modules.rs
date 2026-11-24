//! Tests of the compiler's fourth slice: modules, `import()`, `import.meta`,
//! `delete` of an optional chain, direct `eval` with a spread argument, and a
//! function declaration as the body of an `if` or a label. Each expectation was
//! read against the op docs in `ops.rs` and the record's docs in `module.rs`
//! (which cite ECMA-262), not copied from the output.
//!
//! These tests read no files, so they also run under Miri.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::{
    Const, ErrorKind, EvalBinding, EvalScopeKind, Flavor, FunctionCode, FunctionKind, Instr,
    Program, check_program,
};
use clazel_js_vm::compile::{compile_module, compile_script};
use clazel_js_vm::module::{
    ExportImportName, ImportName, ModuleBindingInit, ModuleProgram, check_module,
};

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

/// `v[i]`, as an error instead of a panic.
fn at<T>(v: &[T], i: usize) -> Result<&T, String> {
    v.get(i).ok_or_else(|| format!("no element {i}"))
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn module(src: &str) -> Result<ModuleProgram, String> {
    let c = cps(src);
    let shown: String = src.chars().take(80).collect();
    let ast = parse(&c, SourceGoal::Module).map_err(|_| format!("does not parse: {shown}"))?;
    let m = compile_module(&ast, &c).map_err(|e| format!("{shown}: {e}"))?;
    check_module(&m).map_err(|e| format!("{shown}: ill-formed record: {e}"))?;
    Ok(m)
}

fn script(src: &str) -> Result<Program, String> {
    let c = cps(src);
    let shown: String = src.chars().take(80).collect();
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {shown}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{shown}: {e}"))?;
    check_program(&p).map_err(|e| format!("{shown}: ill-formed bytecode: {e}"))?;
    Ok(p)
}

fn body(m: &ModuleProgram) -> Result<&FunctionCode, String> {
    m.program
        .functions
        .first()
        .ok_or_else(|| "no body".to_string())
}

fn func(p: &Program, i: usize) -> Result<&FunctionCode, String> {
    p.functions.get(i).ok_or_else(|| format!("no function {i}"))
}

fn count(f: &FunctionCode, pred: fn(&Instr) -> bool) -> usize {
    f.instrs.iter().filter(|i| pred(i)).count()
}

fn binding<'a>(
    m: &'a ModuleProgram,
    name: &str,
) -> Result<&'a clazel_js_vm::module::ModuleBinding, String> {
    let n = units(name);
    m.bindings
        .iter()
        .find(|b| b.name == n)
        .ok_or_else(|| format!("no binding {name}"))
}

/// §16.2.1.3† ModuleRequests: the requests of the import and export
/// declarations that have a `from`, in order of first appearance; the same
/// specifier with the same set of attributes is one request.
#[test]
fn requested_modules() -> Result<(), String> {
    let m = module(
        "import a from 'x'; import 'y'; export * from 'x'; export {b} from 'z';\n\
         import c from 'x' with { type: 'json' };\n\
         import d from 'x' with { type: 'json', other: 'v' };\n\
         import e from 'x' with { other: 'v', type: 'json' };",
    )?;
    let specs: Vec<String> = m
        .requested_modules
        .iter()
        .map(|r| r.specifier_lossy())
        .collect();
    assert_eq!(specs, ["x", "y", "z", "x", "x"]);
    assert!(at(&m.requested_modules, 0)?.attributes.is_empty());
    let r3 = at(&m.requested_modules, 3)?;
    assert_eq!(r3.attributes.len(), 1);
    assert_eq!(at(&r3.attributes, 0)?.key, units("type"));
    assert_eq!(at(&r3.attributes, 0)?.value, units("json"));
    // The last two have the same attributes in another order: one request,
    // which keeps the first one's order.
    let r4 = at(&m.requested_modules, 4)?;
    assert_eq!(at(&r4.attributes, 0)?.key, units("type"));
    assert_eq!(r4.attributes.len(), 2);
    // The entries point at them.
    let reqs: Vec<u32> = m.import_entries.iter().map(|e| e.module_request).collect();
    assert_eq!(reqs, [0, 3, 4, 4]);
    Ok(())
}

/// §16.2.2.2† ImportEntries: a default import is the name `default`, a
/// namespace import is `namespace-object`, a named import with no `as` binds the
/// imported name, and a string literal can be the imported name.
#[test]
fn import_entries() -> Result<(), String> {
    let m = module(
        "import d, { a, b as c, 'x y' as z, default as e } from 'm';\n\
         import * as ns from 'n';\n\
         import d2, * as ns2 from 'o';",
    )?;
    let got: Vec<(u32, ImportName, String)> = m
        .import_entries
        .iter()
        .map(|e| {
            (
                e.module_request,
                e.import_name.clone(),
                String::from_utf16_lossy(&e.local_name),
            )
        })
        .collect();
    let name = |s: &str| ImportName::Name(units(s));
    assert_eq!(
        got,
        vec![
            (0, name("default"), "d".to_string()),
            (0, name("a"), "a".to_string()),
            (0, name("b"), "c".to_string()),
            (0, name("x y"), "z".to_string()),
            (0, name("default"), "e".to_string()),
            (1, ImportName::Namespace, "ns".to_string()),
            (2, name("default"), "d2".to_string()),
            (2, ImportName::Namespace, "ns2".to_string()),
        ]
    );
    // Each local name has a binding, an indirect one except a namespace's.
    for (i, e) in m.import_entries.iter().enumerate() {
        let b = m
            .bindings
            .iter()
            .find(|b| b.name == e.local_name)
            .ok_or("an import has no binding")?;
        let i = u32::try_from(i).map_err(|_| "index")?;
        let want = if e.import_name == ImportName::Namespace {
            ModuleBindingInit::Namespace(i)
        } else {
            ModuleBindingInit::Import(i)
        };
        assert_eq!(b.init, want);
    }
    Ok(())
}

/// §16.2.3.2† ExportEntries and ParseModule's partition (§16.2.1.6.1† steps 9
/// and 10): a declaration or `export { a as b }` of a local binding is a local
/// export; a re-export of an import, `export { x } from`, and `export * as n
/// from` are indirect; `export * from` is a star export.
#[test]
fn export_entries() -> Result<(), String> {
    let m = module(
        "export var v = 1, [w] = [2];\n\
         export let l; export const c = 1;\n\
         export function f() {} export class K {}\n\
         export async function af() {} export function* g() {}\n\
         var p = 1; export { p as q, p };\n\
         import { i } from 'a'; export { i }; export { i as j };\n\
         import * as ns from 'b'; export { ns };\n\
         export { x as y, z } from 'c';\n\
         export * as all from 'd';\n\
         export * from 'e';\n\
         export { p as 'str name' };",
    )?;
    let names = |v: &[clazel_js_vm::module::ExportEntry]| -> Vec<String> {
        v.iter()
            .map(|e| {
                e.export_name
                    .as_ref()
                    .map(|n| String::from_utf16_lossy(n))
                    .unwrap_or_else(|| "<null>".to_string())
            })
            .collect()
    };
    assert_eq!(
        names(&m.local_export_entries),
        [
            "v", "w", "l", "c", "f", "K", "af", "g", "q", "p", "ns", "str name"
        ]
    );
    for e in &m.local_export_entries {
        assert!(e.module_request.is_none() && e.import_name.is_none());
        assert!(e.local_name.is_some());
    }
    // `export { p as q }` has export name q and local name p.
    let q = at(&m.local_export_entries, 8)?;
    assert_eq!(q.local_name, Some(units("p")));
    assert_eq!(
        names(&m.indirect_export_entries),
        ["i", "j", "y", "z", "all"]
    );
    // `export { i }` re-exports the import `i` of module 0.
    let i = at(&m.indirect_export_entries, 0)?;
    assert_eq!(i.module_request, Some(0));
    assert_eq!(i.import_name, Some(ExportImportName::Name(units("i"))));
    assert!(i.local_name.is_none());
    // `export { x as y } from 'c'`: request 2, import name x.
    let y = at(&m.indirect_export_entries, 2)?;
    assert_eq!(y.module_request, Some(2));
    assert_eq!(y.import_name, Some(ExportImportName::Name(units("x"))));
    let all = at(&m.indirect_export_entries, 4)?;
    assert_eq!(all.import_name, Some(ExportImportName::All));
    assert_eq!(m.star_export_entries.len(), 1);
    let star = at(&m.star_export_entries, 0)?;
    assert!(star.export_name.is_none());
    assert_eq!(star.import_name, Some(ExportImportName::AllButDefault));
    assert_eq!(star.module_request, Some(4));
    Ok(())
}

/// §16.2.3.7† and §16.2.1.6.4†: what link time puts in each slot: `var` is
/// undefined, `let`, `const` and `class` are in their dead zone, a function is a
/// closure of its template, and every slot is below the environment's size.
#[test]
fn bindings_and_their_initial_state() -> Result<(), String> {
    let m = module("var v; let l; const c = 1; class K {} function f() {} function* g() {}")?;
    assert_eq!(binding(&m, "v")?.init, ModuleBindingInit::Undefined);
    for n in ["l", "c", "K"] {
        assert_eq!(
            binding(&m, n)?.init,
            ModuleBindingInit::Uninitialized,
            "{n}"
        );
    }
    for n in ["f", "g"] {
        match binding(&m, n)?.init {
            ModuleBindingInit::Function(i) => {
                let t = m.program.functions.get(i as usize).ok_or("no template")?;
                assert_eq!(t.name, units(n));
                assert_eq!(t.kind, FunctionKind::Normal);
            }
            ref other => return Err(format!("{n}: {other:?}")),
        }
    }
    assert_eq!(
        m.program
            .functions
            .get(match binding(&m, "g")?.init {
                ModuleBindingInit::Function(i) => i as usize,
                _ => return Err("g".to_string()),
            })
            .map(|f| f.flavor),
        Some(Flavor::Generator)
    );
    assert_eq!(m.bindings.len(), 6);
    assert_eq!(m.env_size, 6);
    // No hoisted function is created by the body (the runtime does it): the one
    // closure is the constructor of the class K.
    let b = body(&m)?;
    assert_eq!(count(b, |i| matches!(i, Instr::NewClosure { .. })), 1);
    assert_eq!(count(b, |i| matches!(i, Instr::NewEnv { .. })), 0);
    assert_eq!(count(b, |i| matches!(i, Instr::DeclareGlobals { .. })), 0);
    Ok(())
}

/// The body of a module: kind Module, strict code (§16.2.1†: module code is
/// strict), run in the module environment (its callee environment, read first),
/// with no global declarations.
#[test]
fn the_body_of_a_module() -> Result<(), String> {
    let m = module("export let a = 1; a = a + 1;")?;
    let b = body(&m)?;
    assert_eq!(b.kind, FunctionKind::Module);
    assert_eq!(b.flavor, Flavor::Plain);
    assert!(b.strict);
    assert_eq!(m.program.main, 0);
    assert!(matches!(b.instrs.first(), Some(Instr::GetCalleeEnv { .. })));
    // The binding is in a slot of the module environment, so other modules read
    // it: the writes are slot writes.
    assert!(count(b, |i| matches!(i, Instr::SetEnvSlot { .. })) >= 2);
    assert!(count(b, |i| matches!(i, Instr::GetEnvSlot { .. })) >= 1);
    // An empty module compiles.
    let e = module("")?;
    assert_eq!(e.env_size, 0);
    assert!(e.bindings.is_empty() && e.requested_modules.is_empty());
    Ok(())
}

/// §9.1.1.5.1† GetBindingValue of an indirect binding: a read of a named or
/// default import is `GetImportBinding` of the slot, in the body and, through
/// the parent hops, in a closure; a namespace import is an ordinary immutable
/// binding.
#[test]
fn reading_imports() -> Result<(), String> {
    let m = module(
        "import d, { a as b } from 'm'; import * as ns from 'n';\n\
         export function f() { return b + d; }\n\
         var x = b; var y = ns;",
    )?;
    let body_f = body(&m)?;
    let slot_of = |n: &str| -> Result<u32, String> { Ok(binding(&m, n)?.slot) };
    let imports: Vec<(u32, u32)> = body_f
        .instrs
        .iter()
        .filter_map(|i| match i {
            Instr::GetImportBinding { env, idx, .. } => Some((*env, *idx)),
            _ => None,
        })
        .collect();
    // `var x = b;` reads b once in the body.
    assert_eq!(imports.len(), 1);
    assert_eq!(at(&imports, 0)?.1, slot_of("b")?);
    // The namespace is read from its slot.
    assert!(body_f.instrs.iter().any(|i| matches!(
        i,
        Instr::GetEnvSlot { idx, .. } if *idx == slot_of("ns").unwrap_or(u32::MAX)
    )));
    // The function reads b and d, in a closure of the module environment (its
    // callee environment, no hops: the function has no scope of its own).
    let f = match binding(&m, "f")?.init {
        ModuleBindingInit::Function(i) => m.program.functions.get(i as usize).ok_or("f")?,
        _ => return Err("f".to_string()),
    };
    let in_f: Vec<u32> = f
        .instrs
        .iter()
        .filter_map(|i| match i {
            Instr::GetImportBinding { idx, .. } => Some(*idx),
            _ => None,
        })
        .collect();
    assert_eq!(in_f, [slot_of("b")?, slot_of("d")?]);
    assert!(matches!(f.instrs.first(), Some(Instr::GetCalleeEnv { .. })));
    Ok(())
}

/// §9.1.1.5.5† CreateImportBinding creates an immutable binding: assigning to an
/// import, or to a namespace import, is a TypeError, after the right side is
/// evaluated.
#[test]
fn assigning_to_an_import_throws() -> Result<(), String> {
    for src in [
        "import { a } from 'm'; a = 1;",
        "import { a } from 'm'; a++;",
        "import * as ns from 'm'; ns = 1;",
        "import d from 'm'; d += 1;",
    ] {
        let m = module(src)?;
        let b = body(&m)?;
        let throws = b.instrs.iter().any(|i| {
            matches!(
                i,
                Instr::ThrowError {
                    kind: ErrorKind::TypeError,
                    ..
                }
            )
        });
        assert!(throws, "{src}");
    }
    Ok(())
}

/// A closure that reads a module binding with a scope of its own between goes
/// up by `GetEnvParent`, as it does for a script's.
#[test]
fn closures_reach_the_module_environment() -> Result<(), String> {
    let m = module(
        "import { a } from 'm'; let n = 0;\n\
         export function f(p) { let q = p; return () => { n = n + q; return a; }; }",
    )?;
    let f = match binding(&m, "f")?.init {
        ModuleBindingInit::Function(i) => m.program.functions.get(i as usize).ok_or("f")?,
        _ => return Err("f".to_string()),
    };
    // f's `q` is captured by the arrow, so f has an environment object, and the
    // arrow reaches the module environment one hop up from its own callee
    // environment (f's).
    assert_eq!(count(f, |i| matches!(i, Instr::NewEnv { .. })), 1);
    let arrow = m
        .program
        .functions
        .iter()
        .find(|g| g.kind == FunctionKind::Arrow)
        .ok_or("no arrow")?;
    assert!(count(arrow, |i| matches!(i, Instr::GetEnvParent { .. })) >= 1);
    assert_eq!(
        count(arrow, |i| matches!(i, Instr::GetImportBinding { .. })),
        1
    );
    Ok(())
}

/// §16.2.3.7† `export default` of an expression: NamedEvaluation of an
/// anonymous function or class with the name "default", then the binding
/// `*default*` is initialized.
#[test]
fn export_default_of_an_expression() -> Result<(), String> {
    let m = module("export default 1 + 2;")?;
    assert_eq!(
        binding(&m, "*default*")?.init,
        ModuleBindingInit::Uninitialized
    );
    assert_eq!(m.local_export_entries.len(), 1);
    let e = at(&m.local_export_entries, 0)?;
    assert_eq!(e.export_name, Some(units("default")));
    assert_eq!(e.local_name, Some(units("*default*")));
    let b = body(&m)?;
    assert!(count(b, |i| matches!(i, Instr::SetEnvSlot { .. })) >= 1);
    // An anonymous arrow, function expression and class get the name "default".
    for (src, kind) in [
        ("export default () => {};", FunctionKind::Arrow),
        ("export default (function () {});", FunctionKind::Normal),
        ("export default (class {});", FunctionKind::Class),
        ("export default (async () => {});", FunctionKind::Arrow),
    ] {
        let m = module(src)?;
        let f = m
            .program
            .functions
            .iter()
            .skip(1)
            .find(|f| f.kind == kind)
            .ok_or_else(|| format!("{src}: no function"))?;
        assert_eq!(f.name, units("default"), "{src}");
    }
    // A named function expression keeps its own name.
    let m = module("export default (function named() {});")?;
    assert_eq!(
        m.program.functions.get(1).map(|f| f.name.clone()),
        Some(units("named"))
    );
    Ok(())
}

/// `export default function () {}` and `export default class {}`: declarations,
/// named "default", bound to `*default*`; a named one binds its own name and
/// exports it as "default".
#[test]
fn export_default_of_a_declaration() -> Result<(), String> {
    let m = module("export default function () {}")?;
    match binding(&m, "*default*")?.init {
        ModuleBindingInit::Function(i) => {
            let f = m.program.functions.get(i as usize).ok_or("f")?;
            assert_eq!(f.name, units("default"));
        }
        ref other => return Err(format!("{other:?}")),
    }
    assert_eq!(
        at(&m.local_export_entries, 0)?.local_name,
        Some(units("*default*"))
    );
    let m = module("export default function* () {}")?;
    assert!(matches!(
        binding(&m, "*default*")?.init,
        ModuleBindingInit::Function(_)
    ));
    let m = module("export default async function () {}")?;
    assert!(matches!(
        binding(&m, "*default*")?.init,
        ModuleBindingInit::Function(_)
    ));
    let m = module("export default class {}")?;
    assert_eq!(
        binding(&m, "*default*")?.init,
        ModuleBindingInit::Uninitialized
    );
    let ctor = m
        .program
        .functions
        .iter()
        .find(|f| f.kind == FunctionKind::Class)
        .ok_or("no constructor")?;
    assert_eq!(ctor.name, units("default"));
    let m = module("export default class extends Object {}")?;
    let ctor = m
        .program
        .functions
        .iter()
        .find(|f| f.kind == FunctionKind::Derived)
        .ok_or("no constructor")?;
    assert_eq!(ctor.name, units("default"));
    // Named ones.
    let m = module("export default function f() {}")?;
    assert!(m.bindings.iter().all(|b| b.name != units("*default*")));
    assert_eq!(
        at(&m.local_export_entries, 0)?.export_name,
        Some(units("default"))
    );
    assert_eq!(at(&m.local_export_entries, 0)?.local_name, Some(units("f")));
    let m = module("export default class C {}")?;
    assert_eq!(at(&m.local_export_entries, 0)?.local_name, Some(units("C")));
    assert_eq!(binding(&m, "C")?.init, ModuleBindingInit::Uninitialized);
    Ok(())
}

/// §16.2.1.6.1† HasTLA: `await` or `for await` outside any function makes the
/// body async (an Await op); one inside a function does not.
#[test]
fn top_level_await() -> Result<(), String> {
    let m = module("await 1; export let a = await Promise.resolve(2);")?;
    assert!(m.has_tla);
    let b = body(&m)?;
    assert_eq!(b.flavor, Flavor::Async);
    assert_eq!(b.kind, FunctionKind::Module);
    assert_eq!(count(b, |i| matches!(i, Instr::Await { .. })), 2);
    let m = module("for await (const x of y) {}")?;
    assert!(m.has_tla);
    assert_eq!(body(&m)?.flavor, Flavor::Async);
    assert!(count(body(&m)?, |i| matches!(i, Instr::Await { .. })) >= 1);
    // Inside a function, an arrow, a method or a nested block of the body.
    let m = module("async function f() { await 1; } export const g = async () => { await 2; };")?;
    assert!(!m.has_tla);
    assert_eq!(body(&m)?.flavor, Flavor::Plain);
    let m = module("if (1) { try { await 1; } catch {} }")?;
    assert!(m.has_tla);
    // `await` as a binding name in a module is an error (the parser's), and a
    // module with no await is plain.
    let m = module("export var a = 1;")?;
    assert!(!m.has_tla);
    Ok(())
}

/// `this` at the top of a module is `undefined` (the runtime gives the body no
/// `this`), and an arrow function there reads it from a binding of the module
/// environment that the body's first ops write: not a user-visible binding.
#[test]
fn this_in_a_module() -> Result<(), String> {
    let m = module("export const t = () => this; var u = this;")?;
    let b = body(&m)?;
    // The body reads `this` for `u` and, to capture it, once more.
    assert!(count(b, |i| matches!(i, Instr::GetThis { .. })) >= 2);
    assert_eq!(m.bindings.len(), 2);
    assert!(m.env_size >= 3);
    assert!(m.bindings.iter().all(|b| b.slot < m.env_size));
    Ok(())
}

/// Direct eval in a module is strict and sees the module's bindings, imports
/// among them, by name.
#[test]
fn direct_eval_in_a_module() -> Result<(), String> {
    let m = module("import { a } from 'm'; let l = 1; var v; eval('l');")?;
    let b = body(&m)?;
    let info = b
        .consts
        .iter()
        .find_map(|c| match c {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .ok_or("no eval record")?;
    assert!(info.strict);
    let scope = info.scopes.last().ok_or("no scope")?;
    assert_eq!(scope.kind, EvalScopeKind::Module);
    assert!(scope.var_object.is_none());
    let kind_of = |n: &str| {
        scope
            .names
            .iter()
            .find(|e| e.name == units(n))
            .map(|e| e.kind)
    };
    assert_eq!(kind_of("a"), Some(EvalBinding::Import));
    assert_eq!(kind_of("l"), Some(EvalBinding::Let));
    assert_eq!(kind_of("v"), Some(EvalBinding::Var));
    Ok(())
}

/// TDZ: an exported `let` read before its declaration in the body is checked, and
/// one read in a function is checked too (the function may run first).
#[test]
fn temporal_dead_zone_in_a_module() -> Result<(), String> {
    let m = module("export function f() { return l; } export let l = 1; l;")?;
    let b = body(&m)?;
    // The read after the declaration, in the same function, needs no check.
    assert_eq!(count(b, |i| matches!(i, Instr::ThrowIfHole { .. })), 0);
    let f = match binding(&m, "f")?.init {
        ModuleBindingInit::Function(i) => m.program.functions.get(i as usize).ok_or("f")?,
        _ => return Err("f".to_string()),
    };
    assert_eq!(count(f, |i| matches!(i, Instr::ThrowIfHole { .. })), 1);
    let m = module("l; export let l = 1;")?;
    assert_eq!(
        count(body(&m)?, |i| matches!(i, Instr::ThrowIfHole { .. })),
        1
    );
    Ok(())
}

/// §13.3.10.1† `import(specifier)`: the specifier, an `undefined` for the
/// absent options, then `ImportCall`; with a second argument, its value. Allowed
/// in a script, in a function and in a module.
#[test]
fn dynamic_import() -> Result<(), String> {
    let p = script("var p = import('./m.js');")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::ImportCall { .. })), 1);
    let at = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::ImportCall { .. }))
        .ok_or("no import call")?;
    // The options register is loaded with undefined just before.
    let (spec, opts) = match f.instrs.get(at) {
        Some(Instr::ImportCall {
            specifier, options, ..
        }) => (*specifier, *options),
        _ => return Err("not an import call".to_string()),
    };
    assert_ne!(spec, opts);
    assert!(
        f.instrs
            .iter()
            .take(at)
            .any(|i| matches!(i, Instr::LoadUndefined { dst } if *dst == opts))
    );
    let p = script(
        "function f(o) { return import('m', o); } import('a', { with: { type: 'json' } });",
    )?;
    assert_eq!(
        count(func(&p, 0)?, |i| matches!(i, Instr::ImportCall { .. })),
        1
    );
    assert_eq!(
        count(func(&p, 1)?, |i| matches!(i, Instr::ImportCall { .. })),
        1
    );
    // The options of the second call are evaluated: an object with a `with`.
    assert!(
        func(&p, 0)?
            .instrs
            .iter()
            .any(|i| matches!(i, Instr::NewObject { .. }))
    );
    let m = module("export const lazy = () => import('./x.js'); await import('y');")?;
    let n: usize = m
        .program
        .functions
        .iter()
        .map(|f| count(f, |i| matches!(i, Instr::ImportCall { .. })))
        .sum();
    assert_eq!(n, 2);
    // The argument's own evaluation order: the specifier first.
    let p = script("import(a(), b());")?;
    let f = func(&p, 0)?;
    let calls: Vec<usize> = f
        .instrs
        .iter()
        .enumerate()
        .filter(|(_, i)| matches!(i, Instr::Call { .. }))
        .map(|(k, _)| k)
        .collect();
    let at = f
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::ImportCall { .. }))
        .ok_or("no import call")?;
    assert_eq!(calls.len(), 2);
    assert!(calls.iter().all(|&c| c < at));
    Ok(())
}

/// §13.3.12.1† `import.meta`: one op, no operand but the destination.
#[test]
fn import_meta() -> Result<(), String> {
    let m = module("export const url = import.meta.url; const f = () => import.meta;")?;
    let n: usize = m
        .program
        .functions
        .iter()
        .map(|f| count(f, |i| matches!(i, Instr::ImportMeta { .. })))
        .sum();
    assert_eq!(n, 2);
    let b = body(&m)?;
    assert!(b.instrs.iter().any(|i| matches!(i, Instr::GetProp { .. })));
    Ok(())
}

/// Every op is emitted with the span of the AST node it was compiled for:
/// `import.meta`'s is the expression's.
#[test]
fn spans_of_import_ops() -> Result<(), String> {
    let m = module("import.meta;")?;
    let b = body(&m)?;
    let at = b
        .instrs
        .iter()
        .position(|i| matches!(i, Instr::ImportMeta { .. }))
        .ok_or("no op")?;
    let sp = b.spans.get(at).ok_or("no span")?;
    assert_eq!((sp.start, sp.end), (0, 11));
    Ok(())
}

/// §13.5.1.2† `delete` of an optional chain: a property reference at the end is
/// deleted (the chain ending early is `true`); a chain that ends in a call is a
/// value, so `true`, after the call.
#[test]
fn delete_of_an_optional_chain() -> Result<(), String> {
    for src in [
        "delete a?.b;",
        "delete a?.[k];",
        "delete a.b?.c;",
        "delete (a?.b);",
    ] {
        let p = script(src)?;
        let f = func(&p, 0)?;
        assert_eq!(
            count(f, |i| matches!(i, Instr::DeleteProp { .. })),
            1,
            "{src}"
        );
        assert!(
            f.instrs
                .iter()
                .any(|i| matches!(i, Instr::JumpIfNullish { .. })),
            "{src}"
        );
        // The short-circuit path gives true.
        assert!(
            f.instrs
                .iter()
                .any(|i| matches!(i, Instr::LoadBool { flag: true, .. })),
            "{src}"
        );
    }
    let p = script("delete a?.b();")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::DeleteProp { .. })), 0);
    assert!(count(f, |i| matches!(i, Instr::Call { .. })) >= 1);
    assert!(
        f.instrs
            .iter()
            .any(|i| matches!(i, Instr::LoadBool { flag: true, .. }))
    );
    // `delete a?.b.c`: the property deleted is `c`, of `a.b`, which is read.
    let p = script("delete a?.b.c;")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::DeleteProp { .. })), 1);
    assert!(count(f, |i| matches!(i, Instr::GetProp { .. })) >= 1);
    Ok(())
}

/// §13.3.6.1† with a spread argument (`eval(...args)`): `DirectEvalSpread` over
/// the array ArgumentListEvaluation built, not `DirectEval`.
#[test]
fn direct_eval_with_a_spread_argument() -> Result<(), String> {
    let p = script("var x = 1; eval(...args); eval('x', ...rest);")?;
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::DirectEvalSpread { .. })), 2);
    assert_eq!(count(f, |i| matches!(i, Instr::DirectEval { .. })), 0);
    assert!(count(f, |i| matches!(i, Instr::NewArray { .. })) >= 2);
    // The scope record is the same as a plain direct eval's.
    let info = f
        .consts
        .iter()
        .find_map(|c| match c {
            Const::EvalScope(i) => Some(i.clone()),
            _ => None,
        })
        .ok_or("no eval record")?;
    assert!(!info.strict);
    // The script has no binding with a slot, so no scope with an environment.
    assert!(info.scopes.is_empty());
    Ok(())
}

/// Annex B.3.4†: a function declaration as the body of an `if` is treated as if
/// it were in a block, so Annex B.3.3.1's hoisting applies: its own binding in
/// the block, the variable of the same name assigned when the declaration is
/// evaluated.
#[test]
fn function_declaration_as_an_if_body() -> Result<(), String> {
    let p = script("if (a) function f() {} else function g() {}")?;
    // Both functions are templates; the global variables f and g are declared.
    let f = func(&p, 0)?;
    assert_eq!(count(f, |i| matches!(i, Instr::NewClosure { .. })), 2);
    let decls = f
        .consts
        .iter()
        .find_map(|c| match c {
            Const::GlobalDeclarations(d) => Some(d.clone()),
            _ => None,
        })
        .ok_or("no declarations")?;
    assert_eq!(decls.annexb, [units("f"), units("g")]);
    // Evaluating each declaration assigns the global.
    assert_eq!(count(f, |i| matches!(i, Instr::SetGlobal { .. })), 2);
    // In a function the variable is a binding of the function.
    let p = script("function h(a) { if (a) function f() {} return f; }")?;
    let h = func(&p, 1)?;
    assert_eq!(count(h, |i| matches!(i, Instr::NewClosure { .. })), 1);
    assert_eq!(count(h, |i| matches!(i, Instr::SetGlobal { .. })), 0);
    Ok(())
}

/// A function declaration as the body of a label (§14.13†, Annex B.3.2): an
/// ordinary function declaration at the position of the label.
#[test]
fn function_declaration_as_a_label_body() -> Result<(), String> {
    let p = script("l: function f() {} function g() { m: function h() {} return h; }")?;
    let f = func(&p, 0)?;
    let decls = f
        .consts
        .iter()
        .find_map(|c| match c {
            Const::GlobalDeclarations(d) => Some(d.clone()),
            _ => None,
        })
        .ok_or("no declarations")?;
    let names: Vec<Vec<u16>> = decls
        .var_scoped
        .iter()
        .filter_map(|v| match v {
            clazel_js_vm::bytecode::VarScoped::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(names, [units("f"), units("g")]);
    // In a function, h is hoisted: a closure at the function's entry.
    let g = p
        .functions
        .iter()
        .find(|f| f.name == units("g"))
        .ok_or("no g")?;
    assert_eq!(count(g, |i| matches!(i, Instr::NewClosure { .. })), 1);
    Ok(())
}

/// Compiling a module twice gives the same record and the same code.
#[test]
fn compilation_is_deterministic() -> Result<(), String> {
    let src = "import a, * as n from 'm'; export { a as b }; export default function () { return n; }\n\
               export const c = await 1; export * from 'z';";
    assert_eq!(module(src)?, module(src)?);
    Ok(())
}

/// A larger module that uses most of the features at once compiles, passes
/// both checks, and its exports are all bindings.
#[test]
fn a_module_with_everything() -> Result<(), String> {
    let m = module(
        "import def, { named, other as alias } from './dep.js';\n\
         import * as ns from './ns.js' with { type: 'json' };\n\
         export { named as renamed } from './dep.js';\n\
         export * from './star.js';\n\
         export * as inner from './inner.js';\n\
         export let counter = 0;\n\
         export function inc() { counter++; return def + named + alias; }\n\
         export class Box { static make() { return new Box(); } #p = ns; get p() { return this.#p; } }\n\
         export default async function () { return await import('./late.js'); }\n\
         for (const k of Object.keys(ns)) { counter += k.length; }\n\
         try { await inc(); } finally { counter = 0; }\n\
         label: for (;;) { break label; }\n\
         export const meta = import.meta.url;",
    )?;
    assert!(m.has_tla);
    assert_eq!(m.requested_modules.len(), 4);
    for e in m
        .local_export_entries
        .iter()
        .filter_map(|e| e.local_name.as_ref())
    {
        assert!(m.bindings.iter().any(|b| &b.name == e));
    }
    Ok(())
}
