//! Classes (§15.7): ClassDefinitionEvaluation (§15.7.14†), compiled to a
//! constructor closure, [`Instr::ClassSetup`], one definition op per method
//! and accessor, and two synthetic functions per class: the *instance
//! initializer*, which adds the private methods and defines the fields of each
//! new object ([`Instr::InitInstance`] calls it), and the *static initializer*,
//! which runs the static fields and static blocks, in order, once.
//!
//! - **Scopes.** The class scope holds the inner name binding (`const`, in its
//!   dead zone until the class is defined), a binding `#x` for each private name,
//!   and hidden bindings for the key of each computed field name and for the
//!   function of each private instance method; the initializers close over it.
//! - **`super()`** is [`Instr::SuperCall`] (or the spread form), then the
//!   `this` binding is set and [`Instr::InitInstance`] runs; a base class
//!   constructor calls `InitInstance` first thing (see
//!   `Cg::function_prologue`).
//! - **Default constructors** are synthesized: `constructor() {}` and
//!   `constructor(...args) { super(...args); }`, the latter passing the
//!   arguments array to the super constructor without iterating it (§15.7.14†
//!   step 14.a: the default derived constructor does not use `%Array.prototype%
//!   [@@iterator]`).

use super::*;

impl<'a> Cg<'a> {
    /// A class declaration: the class, then the initialization of the binding
    /// it declares (§15.7.15† step 2).
    pub(super) fn class_declaration(&mut self, n: u32) -> R<()> {
        let nd = self.node(n)?;
        let name_node = self.child(nd, 0)?;
        let sp = self.sp(n);
        let m = self.mark();
        let t = self.alloc()?;
        self.class_definition(n, t)?;
        let b = self.res(name_node);
        if b != NONE {
            self.init_binding(b, t, sp)?;
        }
        self.release(m);
        Ok(())
    }

    /// ClassDefinitionEvaluation: the class constructor into `d`.
    pub(super) fn class_definition(&mut self, n: u32, d: Reg) -> R<()> {
        let nd = self.node(n)?;
        let (name_node, heritage, body) =
            (self.child(nd, 0)?, self.child(nd, 1)?, self.child(nd, 2)?);
        let sp = self.sp(n);
        let info = *self
            .an
            .classes
            .get(&n)
            .ok_or(CompileError::Internal("class without scopes"))?;
        let derived = self.node(heritage)?.kind != NodeKind::Absent;
        let class_name: Vec<u16> = if self.node(name_node)?.kind == NodeKind::BindingIdentifier {
            self.name_units(self.name_of(name_node))?
        } else {
            Vec::new()
        };
        let m = self.mark();
        self.enter_scope(info.scope, sp)?;
        let (ctor, proto, her) = (self.alloc()?, self.alloc()?, self.alloc()?);
        if derived {
            self.expr_to(heritage, Some(her), true)?;
        }
        // The constructor.
        let elements: Vec<u32> = self.node(body)?.children.clone();
        let mut ctor_node: Option<u32> = None;
        for &el in &elements {
            if scope::is_constructor_method(self.ast, self.src, el)? {
                ctor_node = Some(el);
            }
        }
        let ckind = if derived {
            FunctionKind::Derived
        } else {
            FunctionKind::Class
        };
        let id = match ctor_node {
            Some(c) => {
                self.name_override = Some(class_name.clone());
                self.compile_function(c, ckind)?
            }
            None => self.default_constructor(n, ckind, class_name)?,
        };
        let env = self.current_env_reg()?;
        self.emit(
            Instr::NewClosure {
                dst: ctor,
                func: id,
                env,
            },
            sp,
        )?;
        self.emit(
            Instr::ClassSetup {
                ctor,
                proto,
                heritage: her,
                derived,
            },
            sp,
        )?;
        // The elements, in order (§15.7.14† step 26).
        let mut inst: Vec<u32> = Vec::new();
        let mut stat: Vec<u32> = Vec::new();
        for &el in &elements {
            if Some(el) == ctor_node {
                continue;
            }
            let en = self.node(el)?;
            let esp = self.sp(el);
            let m2 = self.mark();
            match en.kind {
                NodeKind::MethodDefinition => {
                    let target = if en.flag { ctor } else { proto };
                    let key_node = self.child(en, 0)?;
                    let form = match en.op {
                        AOp::Getter => 1u32,
                        AOp::Setter => 2,
                        _ => 0,
                    };
                    let f = self.alloc()?;
                    if self.node(key_node)?.kind == NodeKind::PrivateIdentifier {
                        self.make_closure(el, f, FunctionKind::Method)?;
                        self.emit(
                            Instr::SetHomeObject {
                                func: f,
                                obj: target,
                            },
                            esp,
                        )?;
                        if en.flag {
                            let name = self.alloc()?;
                            self.read_private_name(key_node, name)?;
                            self.emit(
                                Instr::DefinePrivate {
                                    obj: target,
                                    name,
                                    val: f,
                                    form: form.saturating_add(1),
                                },
                                esp,
                            )?;
                        } else {
                            let h =
                                *self.an.hidden.get(&el).ok_or(CompileError::Internal(
                                    "private method without a slot",
                                ))?;
                            self.init_binding(h, f, esp)?;
                            inst.push(el);
                        }
                    } else {
                        let key = self.alloc()?;
                        self.key_register(key_node, key)?;
                        self.make_closure(el, f, FunctionKind::Method)?;
                        self.emit(
                            Instr::SetHomeObject {
                                func: f,
                                obj: target,
                            },
                            esp,
                        )?;
                        self.emit(
                            Instr::DefineMethod {
                                obj: target,
                                key,
                                func: f,
                                form,
                                enumerable: false,
                            },
                            esp,
                        )?;
                    }
                }
                NodeKind::FieldDefinition => {
                    let key_node = self.child(en, 0)?;
                    if self.node(key_node)?.kind == NodeKind::ComputedPropertyName {
                        let k = self.alloc()?;
                        self.key_register(key_node, k)?;
                        let h = *self
                            .an
                            .hidden
                            .get(&el)
                            .ok_or(CompileError::Internal("computed field without a slot"))?;
                        self.init_binding(h, k, esp)?;
                    }
                    if en.flag {
                        stat.push(el);
                    } else {
                        inst.push(el);
                    }
                }
                NodeKind::ClassStaticBlock => stat.push(el),
                _ => return Err(CompileError::Internal("unexpected class element")),
            }
            self.release(m2);
        }
        // The inner name is initialized before the static elements run
        // (§15.7.14† step 27 comes before steps 31 to 34).
        if self.node(name_node)?.kind == NodeKind::BindingIdentifier {
            let name = self.name_of(name_node);
            if let Some(&b) = self.scope(info.scope)?.names.get(&name) {
                self.init_binding(b, ctor, sp)?;
            }
        }
        if !inst.is_empty() {
            let id = self.class_initializer(n, false, &inst)?;
            let init = self.alloc()?;
            let env = self.current_env_reg()?;
            self.emit(
                Instr::NewClosure {
                    dst: init,
                    func: id,
                    env,
                },
                sp,
            )?;
            self.emit(
                Instr::SetHomeObject {
                    func: init,
                    obj: proto,
                },
                sp,
            )?;
            self.emit(Instr::SetInstanceInit { ctor, init }, sp)?;
        }
        if !stat.is_empty() {
            let id = self.class_initializer(n, true, &stat)?;
            let init = self.alloc()?;
            let env = self.current_env_reg()?;
            self.emit(
                Instr::NewClosure {
                    dst: init,
                    func: id,
                    env,
                },
                sp,
            )?;
            self.emit(
                Instr::SetHomeObject {
                    func: init,
                    obj: ctor,
                },
                sp,
            )?;
            let out = self.alloc()?;
            self.emit(
                Instr::Call {
                    dst: out,
                    callee: init,
                    this: ctor,
                    args: out,
                    argc: 0,
                },
                sp,
            )?;
        }
        self.emit(Instr::Move { dst: d, src: ctor }, sp)?;
        self.exit_scope(info.scope)?;
        self.release(m);
        Ok(())
    }

    /// The constructor of a class that has none: `constructor() {}`, or
    /// `constructor(...args) { super(...args); }` for a derived class.
    fn default_constructor(&mut self, n: u32, kind: FunctionKind, name: Vec<u16>) -> R<u32> {
        let index =
            u32::try_from(self.out.len()).map_err(|_| CompileError::TooLarge("functions"))?;
        self.out.push(None);
        let span = self.sp(n);
        let saved = std::mem::replace(&mut self.f, FnState::new(kind, true, span, 0));
        let r = self.default_constructor_body(kind, span);
        let st = std::mem::replace(&mut self.f, saved);
        r?;
        self.finish_function(
            index,
            st,
            FnMeta {
                name,
                kind,
                nparams: 0,
                length: 0,
                span,
            },
        )?;
        Ok(index)
    }

    fn default_constructor_body(&mut self, kind: FunctionKind, sp: Span) -> R<()> {
        if kind == FunctionKind::Class {
            let (t, c, u) = (self.alloc()?, self.alloc()?, self.alloc()?);
            self.emit(Instr::GetThis { dst: t }, sp)?;
            self.emit(Instr::GetCallee { dst: c }, sp)?;
            self.emit(Instr::InitInstance { obj: t, func: c }, sp)?;
            self.emit(Instr::LoadUndefined { dst: u }, sp)?;
            self.emit(Instr::Return { src: u }, sp)
        } else {
            let (func, nt, this, arr, out) = (
                self.alloc()?,
                self.alloc()?,
                self.alloc()?,
                self.alloc()?,
                self.alloc()?,
            );
            self.emit(Instr::GetCallee { dst: func }, sp)?;
            self.emit(Instr::GetNewTarget { dst: nt }, sp)?;
            self.emit(Instr::LoadHole { dst: this }, sp)?;
            self.emit(Instr::CreateRestArray { dst: arr, from: 0 }, sp)?;
            self.emit(
                Instr::SuperCallSpread {
                    dst: out,
                    func,
                    newtarget: nt,
                    this,
                    args: arr,
                },
                sp,
            )?;
            self.emit(Instr::InitInstance { obj: out, func }, sp)?;
            self.emit(Instr::Return { src: out }, sp)
        }
    }

    /// The instance initializer (`is_static` false: the private methods and the
    /// fields of `elems`, defined on `this`) or the static initializer (the
    /// static fields and blocks of `elems`, run with `this` the class), as a
    /// function of the program. Its scope is the class's synthetic function
    /// scope, so initializer expressions see `this`, `super` and the class's
    /// bindings as a method's would.
    fn class_initializer(&mut self, n: u32, is_static: bool, elems: &[u32]) -> R<u32> {
        let info = *self
            .an
            .classes
            .get(&n)
            .ok_or(CompileError::Internal("class without scopes"))?;
        let sc_id = if is_static {
            info.static_scope
        } else {
            info.inst_scope
        };
        let index =
            u32::try_from(self.out.len()).map_err(|_| CompileError::TooLarge("functions"))?;
        self.out.push(None);
        let span = self.sp(n);
        let mut fresh = FnState::new(FunctionKind::Method, true, span, 0);
        fresh.fscope = sc_id;
        let saved = std::mem::replace(&mut self.f, fresh);
        let r = self.class_initializer_body(sc_id, elems, span);
        let st = std::mem::replace(&mut self.f, saved);
        r?;
        self.finish_function(
            index,
            st,
            FnMeta {
                name: Vec::new(),
                kind: FunctionKind::Method,
                nparams: 0,
                length: 0,
                span,
            },
        )?;
        Ok(index)
    }

    fn class_initializer_body(&mut self, sc_id: u32, elems: &[u32], sp: Span) -> R<()> {
        let base = self.alloc()?;
        self.f.base_env = base;
        self.emit(Instr::GetCalleeEnv { dst: base }, sp)?;
        self.enter_scope(sc_id, sp)?;
        let this = self.alloc()?;
        self.emit(Instr::GetThis { dst: this }, sp)?;
        // §7.3.34† InitializeInstanceElements: the private methods and
        // accessors first (steps 2 and 3).
        for &el in elems {
            let en = self.node(el)?;
            if en.kind != NodeKind::MethodDefinition {
                continue;
            }
            let m = self.mark();
            let esp = self.sp(el);
            let key_node = self.child(en, 0)?;
            let (name, f) = (self.alloc()?, self.alloc()?);
            self.read_private_name(key_node, name)?;
            let h = *self
                .an
                .hidden
                .get(&el)
                .ok_or(CompileError::Internal("private method without a slot"))?;
            self.read_binding(h, 0, f, esp)?;
            let form = match en.op {
                AOp::Getter => 2u32,
                AOp::Setter => 3,
                _ => 1,
            };
            self.emit(
                Instr::DefinePrivate {
                    obj: this,
                    name,
                    val: f,
                    form,
                },
                esp,
            )?;
            self.release(m);
        }
        // Then the fields, and for the static initializer the static blocks, in order.
        for &el in elems {
            let en = self.node(el)?;
            let esp = self.sp(el);
            let m = self.mark();
            match en.kind {
                NodeKind::FieldDefinition => {
                    let (key_node, init) = (self.child(en, 0)?, self.child(en, 1)?);
                    let v = self.alloc()?;
                    if self.node(init)?.kind == NodeKind::Absent {
                        self.emit(Instr::LoadUndefined { dst: v }, esp)?;
                    } else {
                        self.expr_to(init, Some(v), true)?;
                    }
                    let kk = self.node(key_node)?.kind;
                    let key = self.alloc()?;
                    match kk {
                        NodeKind::PrivateIdentifier => {
                            self.read_private_name(key_node, key)?;
                            self.emit(
                                Instr::DefinePrivate {
                                    obj: this,
                                    name: key,
                                    val: v,
                                    form: 0,
                                },
                                esp,
                            )?;
                        }
                        _ => {
                            if kk == NodeKind::ComputedPropertyName {
                                let h = *self.an.hidden.get(&el).ok_or(CompileError::Internal(
                                    "computed field without a slot",
                                ))?;
                                self.read_binding(h, 0, key, esp)?;
                            } else {
                                self.key_register(key_node, key)?;
                            }
                            self.emit(
                                Instr::DefineElem {
                                    obj: this,
                                    idx: key,
                                    val: v,
                                },
                                esp,
                            )?;
                        }
                    }
                }
                NodeKind::ClassStaticBlock => {
                    let f = self.alloc()?;
                    self.make_closure(el, f, FunctionKind::Method)?;
                    self.emit(Instr::SetHomeObject { func: f, obj: this }, esp)?;
                    let out = self.alloc()?;
                    self.emit(
                        Instr::Call {
                            dst: out,
                            callee: f,
                            this,
                            args: out,
                            argc: 0,
                        },
                        esp,
                    )?;
                }
                _ => {}
            }
            self.release(m);
        }
        let u = self.alloc()?;
        self.emit(Instr::LoadUndefined { dst: u }, sp)?;
        self.emit(Instr::Return { src: u }, sp)
    }
}
