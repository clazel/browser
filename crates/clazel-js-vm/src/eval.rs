//! The handlers of `with` and of `delete` of a variable, and the host compile
//! paths: `eval` (direct, [`crate::ops::Op::DirectEval`], and indirect,
//! [`Vm::perform_eval`]) and the `Function` constructors
//! ([`Vm::create_dynamic_function`]).
//!
//! Spec: ECMA-262 at the pinned commit (`spec.rs`). §9.1.1.2 (Object
//! Environment Records), §13.5.1.2 (`delete`), §19.2.1 (`eval`), §19.2.1.1
//! PerformEval, §19.2.1.3 EvalDeclarationInstantiation and §20.2.1.1.1
//! CreateDynamicFunction were read at that commit; a section number marked †
//! was not.
//!
//! # Differences from the standard, all listed
//!
//! - **HostEnsureCanCompileStrings** (§19.2.1.2) is the default host's: every
//!   string may be compiled. An embedder has no hook for it yet.
//! - **One realm.** The VM has one global environment, so evalRealm and
//!   currentRealm are it.
//! - **Each eval compiles anew** and its functions stay loaded in the VM: the
//!   code table grows with every evaluation of a string, as it does with every
//!   script (no cache, no unloading; the collector of 7.6 does not free code).
//! - **A program too large for the bytecode** (`CompileError::TooLarge`) is a
//!   `RangeError`, and a construct the compiler does not compile is
//!   [`Abrupt::NotYet`]; the standard has neither.
//! - **Annex B.3.2 at the global level**: a function in a block of sloppy
//!   eval code whose var binding the handler does not make (a global lexical
//!   declaration of its name, or a global object that refuses it, step
//!   13.b.ii.5) is still assigned to the global object when its declaration
//!   is evaluated, where the standard leaves the evaluation as it is.
//! - **A named function expression's own name** is a binding of its function
//!   scope (see `crate::scope`), so `var f` in sloppy eval code inside `f`
//!   assigns that immutable binding (silently) where the standard creates a
//!   new variable in the function's varEnv.

use crate::bytecode::{EvalBinding, EvalScopeInfo, EvalScopeKind};
use crate::compile::{CompileError, EvalDecls, compile_dynamic_function, compile_eval};
use crate::interp::{Abrupt, Intrinsic, Vm};
use crate::props::PropDesc;
use clazel_js_heap::shape::Attrs;
use clazel_js_heap::string::{JsString, Key};
use clazel_js_heap::value::Value;
use clazel_js_syntax::ast::NodeKind;
use clazel_js_syntax::exec::{EvalContext, parse, parse_eval};
use clazel_js_syntax::spec::SourceGoal;

/// Which function CreateDynamicFunction makes (its `kind`, §20.2.1.1.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynamicKind {
    /// `Function`: normal.
    Normal,
    /// `GeneratorFunction`: generator.
    Generator,
    /// `AsyncFunction`: async.
    Async,
    /// `AsyncGeneratorFunction`: async-generator.
    AsyncGenerator,
}

impl Vm {
    // -----------------------------------------------------------------
    // Object Environment Records (`with`, and a sloppy function's variable
    // object for direct eval)
    // -----------------------------------------------------------------

    /// HasProperty ( O, P ), §7.3.11, over an object's own properties and
    /// its prototype chain.
    fn has_property_key(&self, obj: Value, key: Key) -> Result<bool, Abrupt> {
        Ok(self.heap.find(obj, key)?.is_some())
    }

    /// HasBinding ( N ) of an Object Environment Record with
    /// [[IsWithEnvironment]] true, §9.1.1.2.1 ([`crate::ops::Op::WithHas`]):
    /// 1. Let bindingObject be envRec.[[BindingObject]].
    /// 2. Let foundBinding be ? HasProperty(bindingObject, N).
    /// 3. If foundBinding is false, return false.
    /// 4. If envRec.[[IsWithEnvironment]] is false, return true.
    /// 5. Let unscopables be ? Get(bindingObject, %Symbol.unscopables%).
    /// 6. If unscopables is an Object, then
    ///    a. Let blocked be ToBoolean(? Get(unscopables, N)).
    ///    b. If blocked is true, return false.
    /// 7. Return true.
    pub(crate) fn with_has(&mut self, obj: Value, key: Key) -> Result<bool, Abrupt> {
        if !self.has_property_key(obj, key)? {
            return Ok(false);
        }
        let ku = self.well_known_key(clazel_js_heap::symbol::UNSCOPABLES)?;
        let unscopables = self.get_value(obj, ku)?;
        if self.heap.is_object(unscopables) {
            let blocked = self.get_value(unscopables, key)?;
            if self.to_boolean(blocked) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// GetBindingValue ( N, S ) of an Object Environment Record, §9.1.1.2.6
    /// ([`crate::ops::Op::WithGet`]):
    /// 1. Let bindingObject be envRec.[[BindingObject]].
    /// 2. Let value be ? HasProperty(bindingObject, N).
    /// 3. If value is false, then
    ///    a. If S is false, return undefined; otherwise throw a ReferenceError
    ///    exception.
    /// 4. Return ? Get(bindingObject, N).
    pub(crate) fn with_get(&mut self, obj: Value, key: Key, strict: bool) -> Result<Value, Abrupt> {
        if !self.has_property_key(obj, key)? {
            if !strict {
                return Ok(Value::UNDEFINED);
            }
            let name = self.key_text(key);
            return Err(self.reference_error(&format!("{name} is not defined")));
        }
        self.get_value(obj, key)
    }

    /// SetMutableBinding ( N, V, S ) of an Object Environment Record,
    /// §9.1.1.2.5 ([`crate::ops::Op::WithSet`]):
    /// 1. Let bindingObject be envRec.[[BindingObject]].
    /// 2. Let stillExists be ? HasProperty(bindingObject, N).
    /// 3. If stillExists is false and S is true, throw a ReferenceError
    ///    exception.
    /// 4. Perform ? Set(bindingObject, N, V, S).
    /// 5. Return unused.
    pub(crate) fn with_set(
        &mut self,
        obj: Value,
        key: Key,
        v: Value,
        strict: bool,
    ) -> Result<(), Abrupt> {
        if !self.has_property_key(obj, key)? && strict {
            let name = self.key_text(key);
            return Err(self.reference_error(&format!("{name} is not defined")));
        }
        self.set_property_with(obj, key, v, None, strict)
    }

    /// DeleteBinding ( N ) of an Object Environment Record, §9.1.1.2.7
    /// ([`crate::ops::Op::WithDelete`]):
    /// 1. Let bindingObject be envRec.[[BindingObject]].
    /// 2. Return ? bindingObject.[[Delete]](N).
    pub(crate) fn with_delete(&mut self, obj: Value, key: Key) -> Result<bool, Abrupt> {
        self.delete_property(obj, key)
    }

    /// `delete name` for a name that no scope binds ([`crate::ops::Op::DeleteGlobal`]):
    /// §13.5.1.2 step 5.c ("If IsUnresolvableReference(ref) is true ... return
    /// true") and DeleteBinding of the global Environment Record, §9.1.1.4.7:
    /// 1. Let DclRec be envRec.[[DeclarativeRecord]].
    /// 2. If ! DclRec.HasBinding(N) is true, then return ! DclRec.DeleteBinding(N)
    ///    (false: a lexical binding of a script cannot be deleted).
    /// 3. Let ObjRec be envRec.[[ObjectRecord]].
    /// 4. Let globalObject be ObjRec.[[BindingObject]].
    /// 5. Let existingProp be ? HasOwnProperty(globalObject, N).
    /// 6. If existingProp is true, then return ? ObjRec.DeleteBinding(N).
    /// 7. Return true.
    ///
    /// A name that is not a property of the global object is an unresolvable
    /// reference, whose `delete` is true too.
    pub(crate) fn delete_global(&mut self, key: Key) -> Result<bool, Abrupt> {
        if self.global_lex.contains_key(&key) {
            return Ok(false);
        }
        let global = self.global;
        if self.get_own_property(global, key)?.is_some() {
            return self.delete_property(global, key);
        }
        Ok(true)
    }

    // -----------------------------------------------------------------
    // eval
    // -----------------------------------------------------------------

    /// The handler of [`crate::ops::Op::DirectEval`] and `DirectEvalSpread`:
    /// CallExpression evaluation, §13.3.6.1 step 6, with `func` the value of
    /// `eval`, `this` the call's `this` value, `args` the argument list, `env`
    /// the current environment object and `consts[k]` the record of the
    /// call's scopes.
    /// a. Let argList be ? ArgumentListEvaluation of arguments.
    /// b. If SameValue(func, %eval%) is true, then
    ///    i. If argList has no elements, return undefined.
    ///    ii. Let evalArg be the first element of argList.
    ///    iii. If IsStrict(this CallExpression) is true, let strictCaller be
    ///         true. Otherwise, let strictCaller be false.
    ///    iv. Return ? PerformEval(evalArg, strictCaller, true).
    /// Otherwise EvaluateCall (§13.3.6.2, steps 7 to 9 of the CallExpression):
    /// a call of `func` with `this` and the arguments.
    pub(crate) fn direct_eval(
        &mut self,
        func: Value,
        this: Value,
        args: &[Value],
        env: Value,
        k: u32,
    ) -> Result<Value, Abrupt> {
        let eval = self.intrinsic(Intrinsic::Eval);
        if eval == Value::UNDEFINED || !self.same_value(func, eval) {
            if !self.heap.is_callable(func) {
                let t = self.type_of(func);
                let t = self.string_text(t).unwrap_or_default();
                return Err(self.type_error(&format!("{t} is not a function")));
            }
            return self.call(func, this, args);
        }
        let Some(&x) = args.first() else {
            return Ok(Value::UNDEFINED);
        };
        let info = {
            let f = self
                .codes
                .get(self.cur)
                .ok_or(Abrupt::Internal("code index"))?;
            let i = usize::try_from(k).map_err(|_| Abrupt::Internal("constant index"))?;
            match f.code.consts.get(i) {
                Some(crate::bytecode::Const::EvalScope(info)) => info.clone(),
                _ => return Err(Abrupt::Internal("DirectEval without a scope record")),
            }
        };
        self.perform_eval_in(x, &info, env)
    }

    /// `eval ( x )`, §19.2.1: "Return ? PerformEval(x, false, false)", the
    /// indirect eval: the code runs in the global environment, sloppy unless
    /// it starts with a Use Strict Directive. The `eval` built-in calls this.
    ///
    /// # Errors
    /// What PerformEval throws: a `SyntaxError` for a string that does not
    /// parse, and what the code throws.
    pub fn perform_eval(&mut self, x: Value) -> Result<Value, Abrupt> {
        let info = EvalScopeInfo {
            strict: false,
            in_function: false,
            in_method: false,
            in_derived_constructor: false,
            in_class_field_initializer: false,
            scopes: Vec::new(),
        };
        self.perform_eval_in(x, &info, Value::UNDEFINED)
    }

    /// PerformEval ( x, strictCaller, direct ), §19.2.1.1, for a direct eval
    /// from the scopes `info` (whose innermost environment is `env`) or an
    /// indirect one (`info` empty, `env` undefined: the global environment).
    fn perform_eval_in(
        &mut self,
        x: Value,
        info: &EvalScopeInfo,
        env: Value,
    ) -> Result<Value, Abrupt> {
        // 2. If x is not a String, return x.
        let Some(text) = self.heap.string(x) else {
            return Ok(x);
        };
        let units: Vec<u16> = text.units().collect();
        let src = crate::literal::from_utf16(&units);
        // 3 to 5: evalRealm is the VM's one realm; HostEnsureCanCompileStrings
        // allows every string (module header).
        // 6 to 10: inFunction, inMethod, inDerivedConstructor and
        // inClassFieldInitializer, which the compiler recorded at the call.
        let mut private_names = Vec::new();
        for s in &info.scopes {
            if s.kind != EvalScopeKind::Class {
                continue;
            }
            for n in &s.names {
                if n.kind == EvalBinding::PrivateName {
                    // The record keeps the `#`, the token's name does not.
                    let units = n.name.strip_prefix(&[u16::from(b'#')]).unwrap_or(&n.name);
                    private_names.push(crate::literal::from_utf16(units));
                }
            }
        }
        let cx = EvalContext {
            strict: info.strict,
            in_function: info.in_function,
            in_method: info.in_method,
            in_derived_constructor: info.in_derived_constructor,
            in_class_field_initializer: info.in_class_field_initializer,
            private_names,
        };
        // 11. ParseText(x, Script) and the early errors of 11.e to 11.h; a
        // List of errors is a SyntaxError (11.b).
        let Ok(ast) = parse_eval(&src, &cx) else {
            return Err(self.syntax_error("Invalid or unexpected token in eval code"));
        };
        // 12 and 13 (strictEval) and the declarations: the compiler.
        let compiled = match compile_eval(&ast, &src, info) {
            Ok(c) => c,
            Err(e) => return Err(self.compile_failure(e)),
        };
        // 16 to 18: the variable environment is the caller's variable object
        // (a sloppy caller in a function), else the global environment; a
        // strict eval's is its own scope, which the code makes.
        let var_object = self.eval_var_object(info, env)?;
        // 28. EvalDeclarationInstantiation: the checks and bindings of varEnv
        // (its step 17's functions are the code's prologue).
        self.eval_declaration_instantiation(&compiled.decls, var_object)?;
        // 19 to 27 and 29: the eval context runs the code, over lexEnv's outer
        // environment `env`; its `this` is the caller's, which the code reads
        // through the record, or the global object's.
        let loaded = self.load(&compiled.program)?;
        let main = usize::try_from(loaded.main).map_err(|_| Abrupt::Internal("script index"))?;
        let closure = self.new_closure(main, env)?;
        let global = self.global;
        // 30. An empty completion is undefined: the code's completion register
        // starts as undefined.
        self.call(closure, global, &[])
    }

    /// The [`Abrupt`] for eval code or a dynamic function the compiler did
    /// not compile.
    fn compile_failure(&mut self, e: CompileError) -> Abrupt {
        match e {
            CompileError::NotYetCompiled { feature, .. } => {
                Abrupt::NotYet(format!("{feature} (in code compiled at run time)"))
            }
            CompileError::TooLarge(what) => {
                self.range_error(&format!("Code compiled at run time is too large: {what}"))
            }
            CompileError::Internal(what) => Abrupt::Internal(what),
        }
    }

    /// The caller's variable object of sloppy eval code in a function: the
    /// slot `var_object` of the first scope of `info` that has one, `env`
    /// being the innermost scope's environment object. `None` when varEnv is
    /// the global environment (or the code is strict, which the caller's
    /// record cannot say: the compiler's declarations are empty then).
    fn eval_var_object(&self, info: &EvalScopeInfo, env: Value) -> Result<Option<Value>, Abrupt> {
        if info.strict {
            return Ok(None);
        }
        let mut e = env;
        for s in &info.scopes {
            if let Some(slot) = s.var_object {
                let i = usize::try_from(slot).map_err(|_| Abrupt::Internal("env slot"))?;
                let v = self
                    .heap
                    .env(e)
                    .and_then(|en| en.slots.get(i))
                    .copied()
                    .ok_or(Abrupt::Internal("eval: no variable object"))?;
                return Ok(Some(v));
            }
            e = self
                .heap
                .env(e)
                .map(|en| en.parent)
                .ok_or(Abrupt::Internal("eval: the environment chain is short"))?;
        }
        Ok(None)
    }

    fn eval_keys(&mut self, names: &[Vec<u16>]) -> Result<Vec<Key>, Abrupt> {
        let mut out = Vec::with_capacity(names.len());
        for n in names {
            let s = JsString::from_units(n).map_err(|_| Abrupt::OutOfMemory)?;
            out.push(self.heap.intern(&s)?);
        }
        Ok(out)
    }

    /// CanDeclareGlobalFunction ( N ), §9.1.1.4.15:
    /// 3. Let existingProp be ? globalObject.[[GetOwnProperty]](N).
    /// 4. If existingProp is undefined, return ? IsExtensible(globalObject).
    /// 5. If existingProp.[[Configurable]] is true, return true.
    /// 6. If IsDataDescriptor(existingProp) is true and existingProp has
    ///    attribute values { [[Writable]]: true, [[Enumerable]]: true }, return
    ///    true.
    /// 7. Return false.
    fn can_declare_global_function(&self, key: Key) -> Result<bool, Abrupt> {
        let global = self.global;
        match self.heap.find(global, key)?.filter(|f| f.own) {
            None => Ok(self.heap.is_extensible(global)),
            Some(f) => {
                let a = f.attrs.0;
                Ok(a & Attrs::CONFIGURABLE != 0
                    || (a & crate::heap::ACCESSOR == 0
                        && a & (Attrs::WRITABLE | Attrs::ENUMERABLE)
                            == (Attrs::WRITABLE | Attrs::ENUMERABLE)))
            }
        }
    }

    /// CanDeclareGlobalVar ( N ), §9.1.1.4.14:
    /// 3. Let hasProperty be ? HasOwnProperty(globalObject, N).
    /// 4. If hasProperty is true, return true.
    /// 5. Return ? IsExtensible(globalObject).
    fn can_declare_global_var(&self, key: Key) -> Result<bool, Abrupt> {
        let global = self.global;
        if self.get_own_property(global, key)?.is_some() {
            return Ok(true);
        }
        Ok(self.heap.is_extensible(global))
    }

    /// CreateGlobalVarBinding ( N, D ) with D true, §9.1.1.4.16:
    /// 3. Let hasProperty be ? HasOwnProperty(globalObject, N).
    /// 4. Let extensible be ? IsExtensible(globalObject).
    /// 5. If hasProperty is false and extensible is true, then
    ///    a. Perform ? ObjRec.CreateMutableBinding(N, D).
    ///    b. Perform ? ObjRec.InitializeBinding(N, undefined).
    /// 6. Return unused.
    ///
    /// The pinned edition has no [[VarNames]]: a var that eval code declares
    /// is configurable, so a later script's `let` of its name is no
    /// HasRestrictedGlobalProperty (§9.1.1.4.13), and the VM's `var_names`
    /// (the scripts' own) does not list it.
    fn create_global_var_binding(&mut self, key: Key) -> Result<(), Abrupt> {
        let global = self.global;
        if self.get_own_property(global, key)?.is_none() && self.heap.is_extensible(global) {
            self.define_property_or_throw(global, key, &PropDesc::all(Value::UNDEFINED))?;
        }
        Ok(())
    }

    /// The property a variable object binding of sloppy eval code is, if it
    /// has none (CreateMutableBinding(N, true) of the function's varEnv, and
    /// InitializeBinding(N, undefined)).
    fn create_var_object_binding(&mut self, obj: Value, key: Key) -> Result<(), Abrupt> {
        if self.get_own_property(obj, key)?.is_none() {
            self.define_property_or_throw(obj, key, &PropDesc::all(Value::UNDEFINED))?;
        }
        Ok(())
    }

    /// EvalDeclarationInstantiation ( body, varEnv, lexEnv, privateEnv, strict ),
    /// §19.2.1.3, the steps the handler does (see [`crate::ops::Op::DirectEval`]):
    /// the SyntaxError the compiler found for step 3.d, the checks of steps
    /// 3.a, 10 and 12 when varEnv is the global environment (`var_object`
    /// `None`), then the bindings of steps 13 (web compatibility), 17 and 18. A
    /// function's binding is made here with the value undefined, and the
    /// code's prologue stores the function object in it (step 17.b to 17.d).
    fn eval_declaration_instantiation(
        &mut self,
        d: &EvalDecls,
        var_object: Option<Value>,
    ) -> Result<(), Abrupt> {
        // 3.d.i.2.a: a var name that a lexical scope of the caller binds.
        if let Some(name) = &d.conflict {
            let name = String::from_utf16_lossy(name);
            return Err(
                self.syntax_error(&format!("Identifier '{name}' has already been declared"))
            );
        }
        if d.strict {
            return Ok(());
        }
        let functions = self.eval_keys(&d.functions)?;
        let vars = self.eval_keys(&d.vars)?;
        let annexb = self.eval_keys(&d.annexb)?;
        let Some(obj) = var_object else {
            // 3.a.i.1: "If HasLexicalDeclaration(varEnv, name) is true, throw a
            // SyntaxError exception."
            for key in functions.iter().chain(vars.iter()) {
                if self.global_lex.contains_key(key) {
                    let name = self.key_text(*key);
                    return Err(self
                        .syntax_error(&format!("Identifier '{name}' has already been declared")));
                }
            }
            // 10.a.iv.1: "Let fnDefinable be ? CanDeclareGlobalFunction(varEnv,
            // fn). If fnDefinable is false, throw a TypeError exception."
            for key in &functions {
                if !self.can_declare_global_function(*key)? {
                    let name = self.key_text(*key);
                    return Err(
                        self.type_error(&format!("Cannot declare global function '{name}'"))
                    );
                }
            }
            // 12.a.i.1.a: "Let vnDefinable be ? CanDeclareGlobalVar(varEnv, vn).
            // If vnDefinable is false, throw a TypeError exception."
            for key in &vars {
                if !self.can_declare_global_var(*key)? {
                    let name = self.key_text(*key);
                    return Err(
                        self.type_error(&format!("Cannot declare global variable '{name}'"))
                    );
                }
            }
            // 13 (web compatibility): "If HasLexicalDeclaration(varEnv, F) is false,
            // then Let fnDefinable be ? CanDeclareGlobalVar(varEnv, F)", and
            // with fnDefinable true "Perform ? CreateGlobalVarBinding(varEnv, F,
            // true)" for a name not declared otherwise (the compiler left those
            // out).
            for key in &annexb {
                if !self.global_lex.contains_key(key) && self.can_declare_global_var(*key)? {
                    self.create_global_var_binding(*key)?;
                }
            }
            // 17.c: CreateGlobalFunctionBinding(varEnv, fn, fo, true), §9.1.1.4.17:
            // "If existingProp is undefined or existingProp.[[Configurable]] is
            // true, then Let desc be the PropertyDescriptor { [[Value]]: V,
            // [[Writable]]: true, [[Enumerable]]: true, [[Configurable]]: D }",
            // else "{ [[Value]]: V }" (a writable property, which the code's
            // [[Set]] writes); "Perform ? DefinePropertyOrThrow(globalObject, N,
            // desc)"; then the [[Set]] (the code's prologue).
            let global = self.global;
            for key in &functions {
                let existing = self.heap.find(global, *key)?.filter(|f| f.own);
                if existing.is_none_or(|f| f.attrs.0 & Attrs::CONFIGURABLE != 0) {
                    self.define_property_or_throw(global, *key, &PropDesc::all(Value::UNDEFINED))?;
                }
            }
            // 18.a: "Perform ? CreateGlobalVarBinding(varEnv, vn, true)."
            for key in &vars {
                self.create_global_var_binding(*key)?;
            }
            return Ok(());
        };
        // varEnv is the caller's variable object: 13 (web compatibility) "If bindingExists
        // is false, then Perform ! varEnv.CreateMutableBinding(F, true). Perform
        // ! varEnv.InitializeBinding(F, undefined)"; 17.d.ii and 18.b.ii the
        // same for each function and variable.
        for key in annexb.iter().chain(functions.iter()).chain(vars.iter()) {
            self.create_var_object_binding(obj, *key)?;
        }
        Ok(())
    }

    // -----------------------------------------------------------------
    // The Function constructors
    // -----------------------------------------------------------------

    /// CreateDynamicFunction ( constructor, newTarget, kind, parameterArgs,
    /// bodyArg ), §20.2.1.1.1, with `constructor` the running native
    /// ([`Vm::active_function`]), `newTarget` [`Vm::new_target`], and `args`
    /// the parameterArgs followed by bodyArg (an empty `args` has an
    /// undefined bodyArg). The constructors of `clazel-js-builtins` call it.
    ///
    /// sourceText is parsed once, as a script whose one statement must be
    /// the function's declaration: its `{` where step 15 puts it and its `}`
    /// last. That is what parsing P as FormalParameters and bodyParseString as
    /// the body (steps 17 to 20) guarantees: P and the body cannot close the
    /// parameter list or the body early, or open a comment or a literal that
    /// spans the text between them, without moving one of the two. The early
    /// errors of the expression (steps 23 and 24) are the declaration's, which are the
    /// same.
    ///
    /// # Errors
    /// What ToString of an argument throws; a `SyntaxError` for text that does
    /// not parse as the function.
    pub fn create_dynamic_function(
        &mut self,
        kind: DynamicKind,
        args: &[Value],
    ) -> Result<Value, Abrupt> {
        // 1. If newTarget is undefined, set newTarget to constructor.
        let mut new_target = self.new_target();
        if new_target == Value::UNDEFINED {
            new_target = self.active_function();
        }
        // 2 to 5: prefix and fallbackProto.
        let (prefix, fallback) = match kind {
            DynamicKind::Normal => ("function", Intrinsic::FunctionPrototype),
            DynamicKind::Generator => ("function*", Intrinsic::GeneratorFunctionPrototype),
            DynamicKind::Async => ("async function", Intrinsic::AsyncFunctionPrototype),
            DynamicKind::AsyncGenerator => (
                "async function*",
                Intrinsic::AsyncGeneratorFunctionPrototype,
            ),
        };
        // 6 to 8: parameterStrings, ToString of each parameterArg in order,
        // then 9: bodyString. With no argument at all, bodyArg is "not
        // present" and is the empty String (`Function` step 2 and its
        // siblings).
        let (params, body) = match args.split_last() {
            Some((b, ps)) => (ps, Some(*b)),
            None => (&[][..], None),
        };
        let mut parameter_strings = Vec::with_capacity(params.len());
        for p in params {
            parameter_strings.push(self.to_js_string(*p)?);
        }
        let body_string = match body {
            Some(b) => self.to_js_string(b)?,
            None => JsString::empty(),
        };
        // 10 and 11: currentRealm; HostEnsureCanCompileStrings allows it.
        // 12 and 13: P, the parameter strings joined by ",".
        let mut p_units: Vec<u16> = Vec::new();
        for (i, s) in parameter_strings.iter().enumerate() {
            if i > 0 {
                p_units.push(u16::from(b','));
            }
            p_units.extend(s.units());
        }
        // 14. bodyParseString: LF, bodyString, LF.
        // 15. sourceString: prefix, " anonymous(", P, LF, ") {",
        //     bodyParseString and "}".
        let mut src: Vec<u32> = Vec::new();
        src.extend(prefix.chars().map(u32::from));
        src.extend(" anonymous(".chars().map(u32::from));
        src.extend(crate::literal::from_utf16(&p_units));
        src.extend("\n) ".chars().map(u32::from));
        let brace = src.len();
        src.push(u32::from(b'{'));
        src.push(0x0A);
        let body_units: Vec<u16> = body_string.units().collect();
        src.extend(crate::literal::from_utf16(&body_units));
        src.push(0x0A);
        src.push(u32::from(b'}'));
        // 16 to 24: the parses (see above).
        let ast = match parse(&src, SourceGoal::Script) {
            Ok(ast) if dynamic_function_shape(&ast, brace, src.len(), kind) => ast,
            _ => return Err(self.syntax_error("Invalid function text")),
        };
        let program = match compile_dynamic_function(&ast, &src) {
            Ok(p) => p,
            Err(e) => return Err(self.compile_failure(e)),
        };
        // 25. Let proto be ? GetPrototypeFromConstructor(newTarget, fallbackProto).
        let proto = self.prototype_from_constructor(new_target, fallback)?;
        // 26 to 29: OrdinaryFunctionCreate over the global environment, named
        // "anonymous" (the declaration's name), and 30 to 32: a generator's
        // and an async generator's `prototype`, MakeConstructor of a normal
        // function (the closure's own, as for any function of its kind).
        let loaded = self.load(&program)?;
        let main = usize::try_from(loaded.main).map_err(|_| Abrupt::Internal("function index"))?;
        let f = self.new_closure(main, Value::UNDEFINED)?;
        if self.heap.is_object(proto) {
            self.heap.set_proto(f, proto)?;
        }
        Ok(f)
    }

    /// GetPrototypeFromConstructor ( constructor, intrinsicDefaultProto ),
    /// §10.1.14: `constructor.prototype` if it is an Object, else the
    /// intrinsic (of the one realm).
    fn prototype_from_constructor(
        &mut self,
        constructor: Value,
        fallback: Intrinsic,
    ) -> Result<Value, Abrupt> {
        if self.heap.is_object(constructor) {
            let kp = self.atoms.k_prototype;
            let p = self.get_value(constructor, kp)?;
            if self.heap.is_object(p) {
                return Ok(p);
            }
        }
        Ok(self.intrinsic(fallback))
    }
}

/// Whether `ast` (parsed from sourceText of `len` code points) is the one
/// declaration CreateDynamicFunction built, of the function kind `kind`, with
/// its body's `{` at `brace` and its `}` last.
fn dynamic_function_shape(
    ast: &clazel_js_syntax::ast::Ast,
    brace: usize,
    len: usize,
    kind: DynamicKind,
) -> bool {
    let Some(root) = ast.nodes.get(ast.root as usize) else {
        return false;
    };
    let [decl] = root.children.as_slice() else {
        return false;
    };
    let Some(d) = ast.nodes.get(*decl as usize) else {
        return false;
    };
    let want = match kind {
        DynamicKind::Normal => NodeKind::FunctionDeclaration,
        DynamicKind::Generator => NodeKind::GeneratorDeclaration,
        DynamicKind::Async => NodeKind::AsyncFunctionDeclaration,
        DynamicKind::AsyncGenerator => NodeKind::AsyncGeneratorDeclaration,
    };
    let body = d.children.last().and_then(|&b| ast.nodes.get(b as usize));
    d.kind == want
        && d.start == 0
        && d.end == len
        && body
            .is_some_and(|b| b.kind == NodeKind::FunctionBody && b.start == brace && b.end == len)
}
