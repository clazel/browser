//! Eval code and dynamic functions: the compiler's entries for the host
//! compile paths of `eval` (PerformEval, ECMA-262 §19.2.1.1, through
//! [`crate::ops::Op::DirectEval`] and the `eval` function) and of the
//! `Function` constructors (CreateDynamicFunction, §20.2.1.1.1).
//!
//! # Eval code
//!
//! [`compile_eval`] compiles a parsed eval script against the record of the
//! caller's scopes ([`EvalScopeInfo`]; an indirect eval's has none). Scope
//! analysis ([`scope::analyze_eval`]) puts the caller's scopes around the
//! code's, so its references compile as a nested function's do. The main
//! function of the program is the eval code: the handler runs it as a closure
//! over the call's environment, and it returns the code's completion value.
//!
//! What EvalDeclarationInstantiation (§19.2.1.3) does is split three ways, as
//! the op's text says:
//!
//! - the compiler finds the SyntaxError of step 3.d (a var name that a scope
//!   of the caller between the call and varEnv binds), from the record, and
//!   lists the code's var-scoped declarations ([`EvalDecls`]);
//! - the handler does the checks of steps 3.a, 10 and 12 and makes the
//!   bindings of steps 13, 17 and 18 in varEnv, before the code runs;
//! - the code's prologue ([`Cg::eval_functions`]) instantiates the functions
//!   of step 17 over the code's own scope (lexEnv) and stores each in varEnv.
//!
//! A name that the caller's variable scope binds itself (a parameter, a
//! `var`, `arguments`) is that binding: the code assigns it, and the handler
//! makes nothing for it.
//!
//! # Dynamic functions
//!
//! [`compile_dynamic_function`] compiles the function that CreateDynamicFunction
//! parsed: the source text it built is a script whose one statement declares
//! it, and the program's main function is that function's template, created
//! over the global environment (step 26, env is the realm's GlobalEnv). Its
//! name binds nothing: a reference to `anonymous` inside it is a global
//! reference, as OrdinaryFunctionCreate (step 28) creates no binding for it.

use super::*;

/// The var-scoped declarations of sloppy eval code, as the handler makes their
/// bindings (EvalDeclarationInstantiation §19.2.1.3). Every list is empty for
/// strict eval code, whose declarations are its own (PerformEval step 18).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EvalDecls {
    /// strictEval (PerformEval steps 12 and 13).
    pub strict: bool,
    /// declaredFunctionNames (step 10), in the order of functionsToInitialize,
    /// without the names the caller's variable scope binds.
    pub functions: Vec<Vec<u16>>,
    /// declaredVarNames (step 12), without the names the caller's variable
    /// scope binds.
    pub vars: Vec<Vec<u16>>,
    /// The names of the functions in blocks that the web-compatibility step 13
    /// (Annex B.3.2.3) gives a binding in varEnv, if it has none, and whose
    /// evaluation assigns it. When varEnv is the global environment the handler
    /// leaves out a name with a global lexical declaration or that
    /// CanDeclareGlobalVar refuses (step 13.b.ii.5).
    pub annexb: Vec<Vec<u16>>,
    /// A var name that a scope of the caller between the call and varEnv binds
    /// (step 3.d.i.2.a: a SyntaxError before anything else).
    pub conflict: Option<Vec<u16>>,
}

/// A compiled eval script: the program whose main function is the eval code,
/// and its var-scoped declarations.
#[derive(Clone, Debug)]
pub struct EvalProgram {
    /// The program; its main function runs as the eval code.
    pub program: Program,
    /// What the handler declares in varEnv before the code runs.
    pub decls: EvalDecls,
}

/// Compiles eval code: `ast`, a script parsed from `src` as PerformEval step
/// 11 does (with `clazel_js_syntax::exec::parse_eval`), run by a direct eval
/// whose call recorded `info`, or by an indirect eval (`info` with no scope and
/// not strict). Total, like [`compile_script`].
pub fn compile_eval(
    ast: &Ast,
    src: &[u32],
    info: &EvalScopeInfo,
) -> Result<EvalProgram, CompileError> {
    let info = info.clone();
    with_stack(ast, src, move |ast, src| eval_inner(ast, src, &info))
}

/// Compiles the function of CreateDynamicFunction (§20.2.1.1.1): `ast` is the
/// script parsed from its sourceText, whose one statement is the declaration
/// of the function (the caller checks that). The program's main function is
/// the function's template.
pub fn compile_dynamic_function(ast: &Ast, src: &[u32]) -> Result<Program, CompileError> {
    with_stack(ast, src, dynamic_inner)
}

fn new_cg<'a>(ast: &'a Ast, src: &'a [u32], an: &'a Analysis) -> Cg<'a> {
    Cg {
        ast,
        src,
        an,
        out: Vec::new(),
        loc: vec![None; an.bindings.len()],
        eval_name: eval_name_of(an),
        name_override: None,
        module_fns: Vec::new(),
        module_tla: false,
        f: FnState::new(FunctionKind::Script, false, Span { start: 0, end: 0 }, 0),
    }
}

fn finish(out: Vec<Option<FunctionCode>>, main: u32) -> R<Program> {
    let mut functions = Vec::with_capacity(out.len());
    for f in out {
        functions.push(f.ok_or(CompileError::Internal(
            "a function was reserved but not compiled",
        ))?);
    }
    Ok(Program { functions, main })
}

fn eval_inner(ast: &Ast, src: &[u32], info: &EvalScopeInfo) -> R<EvalProgram> {
    let an = scope::analyze_eval(ast, src, info)?;
    let root = ast.root;
    if ast.nodes.get(root as usize).map(|n| n.kind) != Some(NodeKind::Script) {
        return Err(CompileError::Internal("eval code is not a script"));
    }
    let mut cg = new_cg(ast, src, &an);
    let sc_id = an.own_scope.get(root as usize).copied().unwrap_or(NONE);
    let decls = cg.eval_decls(sc_id)?;
    let main = cg.compile_function(root, FunctionKind::Script)?;
    Ok(EvalProgram {
        program: finish(cg.out, main)?,
        decls,
    })
}

fn dynamic_inner(ast: &Ast, src: &[u32]) -> R<Program> {
    let an = scope::analyze(ast, src)?;
    let root = ast
        .nodes
        .get(ast.root as usize)
        .ok_or(CompileError::Internal("no root"))?;
    let decl = match root.children.as_slice() {
        [d] => *d,
        _ => {
            return Err(CompileError::Internal(
                "a dynamic function is one declaration",
            ));
        }
    };
    let dn = ast
        .nodes
        .get(decl as usize)
        .ok_or(CompileError::Internal("node index out of range"))?;
    if !scope::is_decl_kind(dn.kind) {
        return Err(CompileError::Internal(
            "a dynamic function is one declaration",
        ));
    }
    // The function is created over the global environment (step 26): the
    // script's own scope must not need an environment object.
    let sc = an.own_scope.get(ast.root as usize).copied().unwrap_or(NONE);
    if an.scopes.get(sc as usize).is_some_and(|s| s.has_env()) {
        return Err(CompileError::Internal(
            "a dynamic function's script has an environment",
        ));
    }
    let mut cg = new_cg(ast, src, &an);
    cg.f.cur_scope = sc;
    let main = cg.compile_function(decl, FunctionKind::Normal)?;
    finish(cg.out, main)
}

impl<'a> Cg<'a> {
    /// The caller's scope that is varEnv of sloppy eval code in a function, or
    /// [`NONE`] (not eval code, strict eval code, or varEnv is global).
    pub(super) fn eval_var_scope(&self) -> u32 {
        self.an.eval.as_ref().map_or(NONE, |e| e.var_scope)
    }

    /// A register holding the caller's variable object (varEnv) of sloppy eval
    /// code in a function.
    pub(super) fn eval_var_object(&mut self, sp: Span) -> R<Reg> {
        let vs = self.eval_var_scope();
        let slot = self.dyn_slot(vs)?;
        let env = self.env_for_scope(vs, sp)?;
        let obj = self.alloc()?;
        self.emit(
            Instr::GetEnvSlot {
                dst: obj,
                env,
                idx: slot,
            },
            sp,
        )?;
        Ok(obj)
    }

    /// The binding of `name` in the caller's variable scope that a declaration
    /// of sloppy eval code is: a parameter, a `var`, `arguments` or a function
    /// expression's own name (varEnv.HasBinding is true, so nothing is
    /// created, and SetMutableBinding assigns it).
    fn eval_existing(&self, name: u32) -> R<Option<u32>> {
        let vs = self.eval_var_scope();
        if vs == NONE || self.an.eval.as_ref().is_some_and(|e| e.var_scope_params) {
            return Ok(None);
        }
        match self.scope(vs)?.names.get(&name) {
            Some(&b) => match self.binding(b)?.kind {
                BKind::Var | BKind::Arguments | BKind::FuncName => Ok(Some(b)),
                _ => Ok(None),
            },
            None => Ok(None),
        }
    }

    /// The function declarations of the root scope `sc_id` of sloppy eval code
    /// that functionsToInitialize holds (EvalDeclarationInstantiation step 10:
    /// the last declaration of each name, in the order of those last
    /// declarations).
    fn eval_functions_to_initialize(&self, sc_id: u32) -> R<Vec<(u32, u32)>> {
        let sc = self.scope(sc_id)?;
        let mut out: Vec<(u32, u32)> = Vec::new();
        for &fnode in sc.funcs.iter().rev() {
            let name = self.name_of(self.child(self.node(fnode)?, 0)?);
            if !out.iter().any(|&(_, n)| n == name) {
                out.insert(0, (fnode, name));
            }
        }
        Ok(out)
    }

    /// The declarations of eval code whose root scope is `sc_id` (see
    /// [`EvalDecls`]).
    fn eval_decls(&self, sc_id: u32) -> R<EvalDecls> {
        let Some(ev) = self.an.eval.as_ref() else {
            return Err(CompileError::Internal("eval_decls outside eval code"));
        };
        if ev.strict {
            return Ok(EvalDecls {
                strict: true,
                ..EvalDecls::default()
            });
        }
        let functions = self.eval_functions_to_initialize(sc_id)?;
        let mut fn_names: Vec<u32> = Vec::new();
        for &(_, n) in &functions {
            fn_names.push(n);
        }
        // Step 12: the bound names of the VariableDeclarations, ForBindings and
        // BindingIdentifiers, less the function names.
        let mut var_names: Vec<u32> = Vec::new();
        for &v in &self.an.global_vars {
            let n = self.name_of(v);
            if !fn_names.contains(&n) && !var_names.contains(&n) {
                var_names.push(n);
            }
        }
        // Step 3.d: a scope of the caller between the call and varEnv (not a
        // `with` statement's, and, as the web-compatibility step allows, not a
        // `catch` clause's) that binds a var name; a lexical declaration at the
        // top of the caller's function is in such a scope too (§10.2.11 step
        // 32: a sloppy function's lexEnv is apart from its varEnv), and so is
        // every name of the parameter scope of a call in parameter
        // expressions (step 20: the parameters' environment is apart from
        // varEnv, the function's).
        let mut conflict = None;
        let all: Vec<u32> = fn_names.iter().chain(var_names.iter()).copied().collect();
        let root_parent = self.scope(sc_id)?.parent;
        'names: for &n in &all {
            let mut s = root_parent;
            while s != NONE {
                let sc = self.scope(s)?;
                if s == ev.var_scope {
                    if let Some(&b) = sc.names.get(&n)
                        && (ev.var_scope_params
                            || matches!(self.binding(b)?.kind, BKind::Let | BKind::Const))
                    {
                        conflict = Some(self.name_units(n)?);
                        break 'names;
                    }
                    break;
                }
                if sc.kind != SKind::With
                    && let Some(&b) = sc.names.get(&n)
                    && self.binding(b)?.kind != BKind::Catch
                {
                    conflict = Some(self.name_units(n)?);
                    break 'names;
                }
                s = sc.parent;
            }
        }
        let mut out = EvalDecls {
            strict: false,
            conflict,
            ..EvalDecls::default()
        };
        for &n in &fn_names {
            if self.eval_existing(n)?.is_none() {
                out.functions.push(self.name_units(n)?);
            }
        }
        for &n in &var_names {
            if self.eval_existing(n)?.is_none() {
                out.vars.push(self.name_units(n)?);
            }
        }
        // Step 13 (Annex B.3.2.3): the functions in blocks that scope analysis
        // found may be var-declared, in source order, not already declared.
        let mut annexb: Vec<(usize, u32)> = Vec::new();
        for (&fnode, target) in &self.an.annexb {
            if let Target::Global(g) = *target {
                annexb.push((self.node(fnode)?.start, g));
            }
        }
        annexb.sort_by_key(|e| e.0);
        for (_, g) in annexb {
            let units = self.name_units(g)?;
            if !all.contains(&g) && !out.annexb.contains(&units) {
                out.annexb.push(units);
            }
        }
        Ok(out)
    }

    /// The prologue of sloppy eval code whose root scope is `sc_id`
    /// (EvalDeclarationInstantiation §19.2.1.3 step 17): each function of
    /// functionsToInitialize, instantiated over the code's own scope (lexEnv,
    /// entered already), is stored in varEnv: the caller's binding of the name,
    /// a property of the caller's variable object, or a property of the global
    /// object (CreateGlobalFunctionBinding §9.1.1.4.18 step 5's [[Set]], over
    /// the property the handler defined). Strict eval code's functions are
    /// its own bindings, made when its scope is entered.
    pub(super) fn eval_functions(&mut self, sc_id: u32, sp: Span) -> R<()> {
        if self.an.eval.as_ref().is_none_or(|e| e.strict) {
            return Ok(());
        }
        for (fnode, name) in self.eval_functions_to_initialize(sc_id)? {
            let m = self.mark();
            let t = self.alloc()?;
            self.make_closure(fnode, t, FunctionKind::Normal)?;
            let fsp = self.sp(fnode);
            if let Some(b) = self.eval_existing(name)? {
                if self.binding(b)?.kind != BKind::FuncName {
                    self.init_binding(b, t, fsp)?;
                }
            } else {
                let key = self.konst(Const::String(self.name_units(name)?))?;
                if self.eval_var_scope() != NONE {
                    let obj = self.eval_var_object(sp)?;
                    self.emit(
                        Instr::WithSet {
                            obj,
                            key,
                            val: t,
                            strict: false,
                        },
                        fsp,
                    )?;
                } else {
                    let ic = self.ic();
                    self.emit(Instr::SetGlobal { key, src: t, ic }, fsp)?;
                }
            }
            self.release(m);
        }
        Ok(())
    }
}
