//! Calls and arguments (with spread), array and object literals (with spread,
//! accessors and computed names), template literals and tagged templates,
//! optional chaining, `super` and the other expression forms that the first
//! slice left out.

use super::*;

/// An evaluated argument list.
pub(super) enum ArgList {
    /// The arguments in `count` consecutive registers from the first.
    Plain(Reg, u32),
    /// An array holding the arguments (the list has a spread element).
    Spread(Reg),
}

impl<'a> Cg<'a> {
    /// `dst := this`, read through binding `b` of the node (or the frame's
    /// `this` for [`NONE`]); a derived constructor's `this` is checked for the
    /// hole (§9.1.1.3.4† GetThisBinding step 3).
    pub(super) fn read_this(&mut self, b: u32, dst: Reg, sp: Span) -> R<()> {
        if b == NONE {
            return self.emit(Instr::GetThis { dst }, sp);
        }
        self.read_binding(b, 0, dst, sp)?;
        if self.binding(b)?.kind == BKind::DerivedThis {
            self.emit(Instr::ThrowIfHole { src: dst }, sp)?;
        }
        Ok(())
    }

    /// `dst :=` the running function, through binding `b` or the frame.
    fn read_callee(&mut self, b: u32, dst: Reg, sp: Span) -> R<()> {
        if b == NONE {
            self.emit(Instr::GetCallee { dst }, sp)
        } else {
            self.read_binding(b, 0, dst, sp)
        }
    }

    /// `dst := new.target`, through binding `b` or the frame.
    fn read_new_target(&mut self, b: u32, dst: Reg, sp: Span) -> R<()> {
        if b == NONE {
            self.emit(Instr::GetNewTarget { dst }, sp)
        } else {
            self.read_binding(b, 0, dst, sp)
        }
    }

    /// The `this` binding of the current derived constructor, or [`NONE`].
    fn derived_this_binding(&self) -> R<u32> {
        let sc = self.scope(self.f.fscope)?;
        for &b in &sc.bindings {
            if self.binding(b)?.kind == BKind::DerivedThis {
                return Ok(b);
            }
        }
        Ok(NONE)
    }

    /// `return v`. In a derived constructor the value goes through
    /// [`Instr::ConstructResult`] (§10.2.2† [[Construct]] steps 10 to 12).
    pub(super) fn emit_return(&mut self, v: Reg, sp: Span) -> R<()> {
        if self.f.kind == FunctionKind::Derived {
            let m = self.mark();
            let (this, out) = (self.alloc()?, self.alloc()?);
            let b = self.derived_this_binding()?;
            if b == NONE {
                self.emit(Instr::LoadHole { dst: this }, sp)?;
            } else {
                self.read_binding(b, 0, this, sp)?;
            }
            self.emit(
                Instr::ConstructResult {
                    dst: out,
                    val: v,
                    this,
                },
                sp,
            )?;
            self.emit(Instr::Return { src: out }, sp)?;
            self.release(m);
            Ok(())
        } else {
            self.emit(Instr::Return { src: v }, sp)
        }
    }

    /// `dst :=` the Private Name that private identifier node `n` names.
    pub(super) fn read_private_name(&mut self, n: u32, dst: Reg) -> R<()> {
        let b = self.res(n);
        if b == NONE {
            return Err(CompileError::Internal("unresolved private name"));
        }
        self.read_binding(b, 0, dst, self.sp(n))
    }

    /// A pushed constant that is never shared with another (a template site:
    /// §13.2.8.4† GetTemplateObject caches per site, so two sites with the same
    /// strings are two constants).
    fn konst_unique(&mut self, c: Const) -> R<u32> {
        let k =
            u32::try_from(self.f.consts.len()).map_err(|_| CompileError::TooLarge("constants"))?;
        self.f.consts.push(c);
        Ok(k)
    }

    /// The object and the key of a property reference node `t`: a member
    /// expression or a `super` property. `later` are the expressions evaluated
    /// after it that must not see a change to a variable it read.
    pub(super) fn place(&mut self, t: u32, later: &[u32]) -> R<(Reg, Prop)> {
        let tn = self.node(t)?;
        match tn.kind {
            NodeKind::MemberExpression => {
                let before = self.mark();
                let (obj, prop) = (self.child(tn, 0)?, self.child(tn, 1)?);
                let mut l: Vec<u32> = later.to_vec();
                l.push(prop);
                let o = self.operand(obj, &l)?;
                let key = self.property(tn, prop)?;
                let assigns = later.iter().any(|&x| {
                    self.an
                        .contains_assign
                        .get(x as usize)
                        .copied()
                        .unwrap_or(false)
                });
                let key = match key {
                    // Protect a key held in a variable from the right side.
                    Prop::Computed(r) if assigns && r < before => {
                        let c = self.alloc()?;
                        self.emit(Instr::Move { dst: c, src: r }, self.sp(t))?;
                        Prop::Computed(c)
                    }
                    k => k,
                };
                Ok((o, key))
            }
            NodeKind::SuperProperty => {
                // §13.3.7.1† SuperProperty evaluation: GetThisBinding, the key,
                // then MakeSuperPropertyReference (GetSuperBase).
                let sp = self.sp(t);
                let sref = *self
                    .an
                    .special
                    .get(&t)
                    .ok_or(CompileError::Internal("super without its bindings"))?;
                let this = self.alloc()?;
                self.read_this(sref.this_b, this, sp)?;
                let key = self.alloc()?;
                let prop = self.child(tn, 0)?;
                match tn.op {
                    AOp::Dot => {
                        let pn = self.node(prop)?;
                        let units = literal::name_units_at(self.src, pn.start)?;
                        let k = self.konst(Const::String(units))?;
                        self.emit(Instr::LoadConst { dst: key, k }, sp)?;
                    }
                    AOp::Bracket => self.expr_to(prop, Some(key), true)?,
                    _ => return Err(CompileError::Internal("unknown super property")),
                }
                let func = self.alloc()?;
                self.read_callee(sref.callee_b, func, sp)?;
                let base = self.alloc()?;
                self.emit(Instr::GetSuperBase { dst: base, func }, sp)?;
                Ok((this, Prop::Super { base, key, this }))
            }
            _ => Err(CompileError::Internal("not a property reference")),
        }
    }

    /// Evaluates the callee `cn_id` of a call into `fr` and its `this` into
    /// `this` (§13.3.6.1 EvaluateCall: the reference's base for a property
    /// reference, `undefined` otherwise).
    pub(super) fn callee_and_this(&mut self, cn_id: u32, fr: Reg, this: Reg, sp: Span) -> R<()> {
        let cn = self.node(cn_id)?;
        match cn.kind {
            NodeKind::MemberExpression => {
                let (obj, prop) = (self.child(cn, 0)?, self.child(cn, 1)?);
                self.expr_to(obj, Some(this), true)?;
                let key = self.property(cn, prop)?;
                self.load_prop(fr, this, &key, self.sp(cn_id))
            }
            NodeKind::SuperProperty => {
                let (o, key) = self.place(cn_id, &[])?;
                self.load_prop(fr, o, &key, self.sp(cn_id))?;
                if let Prop::Super { this: t, .. } = key {
                    self.emit(Instr::Move { dst: this, src: t }, sp)?;
                }
                Ok(())
            }
            NodeKind::OptionalExpression => self.optional_chain(cn_id, fr, Some(this), sp),
            NodeKind::IdentifierReference if !self.ident_dyn(cn_id)?.is_empty() => {
                // §13.3.6.1 step 3.b: a reference whose base is an object
                // Environment Record of a `with` has WithBaseObject as its `this`
                // (§9.1.1.2.11†), and otherwise `undefined`.
                let m = self.mark();
                let h = self.resolve_dyn(cn_id, Some(this))?;
                self.read_ident_h(cn_id, fr, h)?;
                self.release(m);
                Ok(())
            }
            _ => {
                self.expr_to(cn_id, Some(fr), true)?;
                self.emit(Instr::LoadUndefined { dst: this }, sp)
            }
        }
    }

    /// §13.3.6 calls: the callee, `this`, then the arguments in consecutive
    /// registers (or in an array, with a spread element, §13.3.8.1†).
    pub(super) fn call(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let (callee, args) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let cn_id = self.unparen(callee)?;
        let cn = self.node(cn_id)?;
        if cn.kind == NodeKind::IdentifierReference
            && callee == cn_id
            && self.eval_name != NONE
            && self.name_of(cn_id) == self.eval_name
        {
            return self.direct_eval(cn_id, args, d, sp);
        }
        let m = self.mark();
        let (fr, this) = (self.alloc()?, self.alloc()?);
        self.callee_and_this(cn_id, fr, this, sp)?;
        match self.arg_list(args)? {
            ArgList::Plain(base, argc) => self.emit(
                Instr::Call {
                    dst: d,
                    callee: fr,
                    this,
                    args: base,
                    argc,
                },
                sp,
            )?,
            ArgList::Spread(arr) => self.emit(
                Instr::CallSpread {
                    dst: d,
                    callee: fr,
                    this,
                    args: arr,
                },
                sp,
            )?,
        }
        self.release(m);
        Ok(())
    }

    /// NamedEvaluation (§8.4.5†) of the initializer `e` for the static name
    /// `name`: when `e` is an anonymous function or class definition (§8.4.3†
    /// IsAnonymousFunctionDefinition, which sees through parentheses), the next
    /// function or class compiled gets `name`, which is the `name` property its
    /// SetFunctionName (§10.2.9†) gives it. A name known only when the code runs
    /// (a computed key) is not covered.
    pub(super) fn named(&mut self, e: u32, name: &[u16]) -> R<()> {
        let u = self.unparen(e)?;
        let nd = self.node(u)?;
        let anonymous = |this: &Self| -> R<bool> {
            let first = this.child(nd, 0)?;
            Ok(this.node(first)?.kind != NodeKind::BindingIdentifier)
        };
        let is_anon = match nd.kind {
            k if scope::is_fexpr_kind(k) => anonymous(self)?,
            NodeKind::ClassExpression => anonymous(self)?,
            k if scope::is_arrow_kind(k) => true,
            _ => false,
        };
        if is_anon {
            self.name_override = Some(name.to_vec());
        }
        Ok(())
    }

    /// NamedEvaluation of `e` for the name of identifier node `target`.
    pub(super) fn named_ident(&mut self, e: u32, target: u32) -> R<()> {
        let name = self.name_units(self.name_of(target))?;
        self.named(e, &name)
    }

    /// The static name a class element or property key gives (§8.4.5†
    /// ClassElementName and PropertyName evaluation): an identifier or string
    /// literal, or a private name with its `#`; `None` for a computed or numeric key.
    pub(super) fn static_key_name(&self, key: u32) -> R<Option<Vec<u16>>> {
        let kn = self.node(key)?;
        Ok(match kn.kind {
            NodeKind::IdentifierName | NodeKind::IdentifierReference => {
                Some(literal::name_units_at(self.src, kn.start)?)
            }
            NodeKind::StringLiteral => Some(literal::string_at(self.src, kn.start)?),
            NodeKind::PrivateIdentifier => {
                let mut v: Vec<u16> = vec![u16::from(b'#')];
                v.extend(literal::name_units_at(self.src, kn.start)?);
                Some(v)
            }
            _ => None,
        })
    }

    /// `eval(args)` written as a direct call (§13.3.6.1† step 6): the value of
    /// `eval`, the `this` of the call and the arguments, then
    /// [`Instr::DirectEval`], which compares the callee with %eval% and either
    /// calls it or performs the eval (PerformEval §19.2.1.1†).
    fn direct_eval(&mut self, cn_id: u32, args: u32, d: Reg, sp: Span) -> R<()> {
        let m = self.mark();
        let (fr, this) = (self.alloc()?, self.alloc()?);
        self.callee_and_this(cn_id, fr, this, sp)?;
        match self.arg_list(args)? {
            ArgList::Plain(base, argc) => {
                let info = self.eval_scope_info()?;
                let k = self.konst(Const::EvalScope(info))?;
                let env = self.current_env_reg()?;
                self.emit(
                    Instr::DirectEval {
                        dst: d,
                        callee: fr,
                        this,
                        args: base,
                        argc,
                        env,
                        k,
                    },
                    sp,
                )?;
            }
            ArgList::Spread(arr) => {
                let info = self.eval_scope_info()?;
                let k = self.konst(Const::EvalScope(info))?;
                let env = self.current_env_reg()?;
                self.emit(
                    Instr::DirectEvalSpread {
                        dst: d,
                        callee: fr,
                        this,
                        args: arr,
                        env,
                        k,
                    },
                    sp,
                )?;
            }
        }
        self.release(m);
        Ok(())
    }

    /// What the host compile path needs of the scopes around the current
    /// position (see [`crate::bytecode::EvalScopeInfo`]).
    fn eval_scope_info(&self) -> R<EvalScopeInfo> {
        let cur = self.scope(self.f.cur_scope)?;
        let mut f = cur.func;
        while let Some(fi) = self.an.funcs.get(f as usize) {
            if fi.arrow {
                f = self.scope(fi.parent_scope)?.func;
            } else {
                break;
            }
        }
        let (node_kind, derived) = match self.an.funcs.get(f as usize) {
            Some(fi) => (self.node(fi.node)?.kind, fi.derived_ctor),
            None => return Err(CompileError::Internal("no such function")),
        };
        let in_class_init = matches!(
            node_kind,
            NodeKind::ClassStaticBlock | NodeKind::ClassDeclaration | NodeKind::ClassExpression
        );
        let mut scopes = Vec::new();
        let mut s = self.f.cur_scope;
        while s != NONE {
            let sc = self.scope(s)?;
            if sc.has_env() {
                let mut names = Vec::new();
                for &b in &sc.bindings {
                    let bd = self.binding(b)?;
                    let (kind, named) = match bd.kind {
                        BKind::Var => (EvalBinding::Var, true),
                        BKind::Let => (EvalBinding::Let, true),
                        BKind::Const => (EvalBinding::Const, true),
                        BKind::Catch => (EvalBinding::Catch, true),
                        BKind::FuncName => (EvalBinding::FuncName, true),
                        BKind::Arguments => (EvalBinding::Arguments, true),
                        BKind::PrivateName => (EvalBinding::PrivateName, true),
                        BKind::Import => (EvalBinding::Import, true),
                        BKind::This => (EvalBinding::This, false),
                        BKind::DerivedThis => (EvalBinding::DerivedThis, false),
                        BKind::NewTarget => (EvalBinding::NewTarget, false),
                        BKind::Callee => (EvalBinding::Callee, false),
                        BKind::Hidden | BKind::WithObject | BKind::EvalVars => continue,
                    };
                    names.push(EvalName {
                        name: if named {
                            self.name_units(bd.name)?
                        } else {
                            Vec::new()
                        },
                        slot: bd.slot,
                        kind,
                    });
                }
                let kind = match sc.kind {
                    SKind::Script => EvalScopeKind::Script,
                    SKind::Module => EvalScopeKind::Module,
                    SKind::Function | SKind::Body => EvalScopeKind::Function,
                    SKind::Class => EvalScopeKind::Class,
                    SKind::With => EvalScopeKind::With,
                    SKind::Block | SKind::For | SKind::Switch | SKind::Catch => {
                        EvalScopeKind::Block
                    }
                };
                let var_object = match (sc.kind, self.an.dyn_binding.get(&s)) {
                    (SKind::Function | SKind::Body, Some(&b)) => Some(self.binding(b)?.slot),
                    _ => None,
                };
                scopes.push(EvalScope {
                    kind,
                    var_object,
                    names,
                });
            }
            s = sc.parent;
        }
        Ok(EvalScopeInfo {
            strict: cur.strict,
            in_function: f != 0,
            in_method: matches!(node_kind, NodeKind::MethodDefinition) || in_class_init,
            in_derived_constructor: derived,
            in_class_field_initializer: in_class_init,
            scopes,
        })
    }

    /// Evaluates an `Arguments` node: into consecutive registers, or, if it has
    /// a spread element, into an array.
    pub(super) fn arg_list(&mut self, args: u32) -> R<ArgList> {
        let an = self.node(args)?;
        let mut spread = false;
        for &a in &an.children {
            if self.node(a)?.kind == NodeKind::SpreadElement {
                spread = true;
            }
        }
        if spread {
            let arr = self.alloc()?;
            self.emit(Instr::NewArray { dst: arr, len: 0 }, self.sp(args))?;
            self.elements_into_array(arr, &an.children, self.sp(args))?;
            return Ok(ArgList::Spread(arr));
        }
        let argc =
            u32::try_from(an.children.len()).map_err(|_| CompileError::TooLarge("arguments"))?;
        let base = self.alloc_n(argc)?;
        for (i, &a) in an.children.iter().enumerate() {
            let r = base
                .saturating_add(u32::try_from(i).map_err(|_| CompileError::TooLarge("arguments"))?);
            self.expr_to(a, Some(r), true)?;
        }
        Ok(ArgList::Plain(base, argc))
    }

    /// Appends the `elements` (expressions, spread elements and elisions) of an
    /// array literal or an argument list to the array in `arr`, tracking the
    /// next index in a register (§13.2.4.1† ArrayAccumulation, §13.3.8.1†
    /// ArgumentListEvaluation): a spread element iterates its operand
    /// (§13.2.4.1† SpreadElement: GetIterator, then IteratorStepValue and
    /// CreateDataPropertyOrThrow until done).
    fn elements_into_array(&mut self, arr: Reg, elements: &[u32], sp: Span) -> R<()> {
        let idx = self.alloc()?;
        self.load_int(idx, 0, self.sp(elements.first().copied().unwrap_or(0)))?;
        let mut last_elision = false;
        for &e in elements {
            let en = self.node(e)?;
            let esp = self.sp(e);
            let m = self.mark();
            last_elision = false;
            match en.kind {
                NodeKind::Elision => {
                    let t = self.alloc()?;
                    self.emit(Instr::LoadHole { dst: t }, esp)?;
                    self.emit(
                        Instr::DefineElem {
                            obj: arr,
                            idx,
                            val: t,
                        },
                        esp,
                    )?;
                    self.emit(Instr::Inc { dst: idx, src: idx }, esp)?;
                    last_elision = true;
                }
                NodeKind::SpreadElement => {
                    let inner = self.child(en, 0)?;
                    let v = self.expr_any(inner)?;
                    let (it, val, done) = (self.alloc()?, self.alloc()?, self.alloc()?);
                    self.emit(Instr::GetIterator { dst: it, src: v }, esp)?;
                    let top = self.label();
                    let out = self.label();
                    let out_t = Self::label_id(out)?;
                    self.bind(top)?;
                    self.emit(
                        Instr::IterNext {
                            value: val,
                            done,
                            iter: it,
                        },
                        esp,
                    )?;
                    self.emit(
                        Instr::JumpIfTrue {
                            cond: done,
                            target: out_t,
                        },
                        esp,
                    )?;
                    self.emit(Instr::DefineElem { obj: arr, idx, val }, esp)?;
                    self.emit(Instr::Inc { dst: idx, src: idx }, esp)?;
                    self.jump(top, esp)?;
                    self.bind(out)?;
                }
                _ => {
                    let v = self.expr_any(e)?;
                    self.emit(
                        Instr::DefineElem {
                            obj: arr,
                            idx,
                            val: v,
                        },
                        esp,
                    )?;
                    self.emit(Instr::Inc { dst: idx, src: idx }, esp)?;
                }
            }
            self.release(m);
        }
        if last_elision {
            // Trailing elisions leave no element: the length says they are there.
            let k = self.str_const("length")?;
            let ic = self.ic();
            self.emit(
                Instr::SetProp {
                    obj: arr,
                    key: k,
                    val: idx,
                    ic,
                },
                sp,
            )?;
        }
        Ok(())
    }

    /// §13.3.5.1 `new`.
    pub(super) fn new_expr(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let (callee, args) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let m = self.mark();
        let fr = self.alloc()?;
        self.expr_to(callee, Some(fr), true)?;
        let list = if self.node(args)?.kind == NodeKind::Absent {
            ArgList::Plain(fr, 0)
        } else {
            self.arg_list(args)?
        };
        match list {
            ArgList::Plain(base, argc) => self.emit(
                Instr::New {
                    dst: d,
                    callee: fr,
                    args: base,
                    argc,
                },
                sp,
            )?,
            ArgList::Spread(arr) => self.emit(
                Instr::NewSpread {
                    dst: d,
                    callee: fr,
                    args: arr,
                },
                sp,
            )?,
        }
        self.release(m);
        Ok(())
    }

    /// §13.3.7.1† `super(args)`: the result is bound to `this` and the
    /// instance's fields are initialized (steps 9 and 10).
    pub(super) fn super_call(&mut self, n: u32, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let args = self.child(nd, 0)?;
        let sref = *self
            .an
            .special
            .get(&n)
            .ok_or(CompileError::Internal("super without its bindings"))?;
        let m = self.mark();
        let list = self.arg_list(args)?;
        let (func, nt, this, out) = (self.alloc()?, self.alloc()?, self.alloc()?, self.alloc()?);
        self.read_callee(sref.callee_b, func, sp)?;
        self.read_new_target(sref.nt_b, nt, sp)?;
        // The current value of `this`, after the arguments: BindThisValue
        // throws if `super()` already returned (the hole test is the op's).
        if sref.this_b == NONE {
            return Err(CompileError::Internal(
                "super() outside a derived constructor",
            ));
        }
        self.read_binding(sref.this_b, 0, this, sp)?;
        match list {
            ArgList::Plain(base, argc) => self.emit(
                Instr::SuperCall {
                    dst: out,
                    func,
                    newtarget: nt,
                    this,
                    args: base,
                    argc,
                },
                sp,
            )?,
            ArgList::Spread(arr) => self.emit(
                Instr::SuperCallSpread {
                    dst: out,
                    func,
                    newtarget: nt,
                    this,
                    args: arr,
                },
                sp,
            )?,
        }
        self.init_binding(sref.this_b, out, sp)?;
        self.emit(Instr::InitInstance { obj: out, func }, sp)?;
        self.emit(Instr::Move { dst: d, src: out }, sp)?;
        self.release(m);
        Ok(())
    }

    /// §13.2.4 array literals: `NewArray` and one `DefineElem` per element
    /// (CreateDataPropertyOrThrow); an elision defines the hole, which the
    /// handler leaves absent; with a spread element, the elements are
    /// appended with a running index.
    pub(super) fn array_literal(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let len = u32::try_from(nd.children.len())
            .map_err(|_| CompileError::TooLarge("array literal"))?;
        self.emit(Instr::NewArray { dst: d, len }, sp)?;
        let mut spread = false;
        for &e in &nd.children {
            if self.node(e)?.kind == NodeKind::SpreadElement {
                spread = true;
            }
        }
        if spread {
            return self.elements_into_array(d, &nd.children, sp);
        }
        for (i, &e) in nd.children.iter().enumerate() {
            let m = self.mark();
            let esp = self.sp(e);
            let idx = self.alloc()?;
            let imm = i32::try_from(i).map_err(|_| CompileError::TooLarge("array literal"))?;
            self.load_int(idx, imm, esp)?;
            let v = if self.node(e)?.kind == NodeKind::Elision {
                let t = self.alloc()?;
                self.emit(Instr::LoadHole { dst: t }, esp)?;
                t
            } else {
                self.expr_any(e)?
            };
            self.emit(
                Instr::DefineElem {
                    obj: d,
                    idx,
                    val: v,
                },
                esp,
            )?;
            self.release(m);
        }
        // Trailing elisions leave no element: ArrayAccumulation (§13.2.4.1†)
        // for an Elision adds to the length only, so `length` is stored
        // after the last element.
        if let Some(&last) = nd.children.last()
            && self.node(last)?.kind == NodeKind::Elision
        {
            let m = self.mark();
            let idx = self.alloc()?;
            let imm = i32::try_from(len).map_err(|_| CompileError::TooLarge("array literal"))?;
            self.load_int(idx, imm, sp)?;
            let k = self.str_const("length")?;
            let ic = self.ic();
            self.emit(
                Instr::SetProp {
                    obj: d,
                    key: k,
                    val: idx,
                    ic,
                },
                sp,
            )?;
            self.release(m);
        }
        Ok(())
    }

    /// A property name (`ClassElementName` or `PropertyName`) as a register
    /// holding a key that ToPropertyKey has converted, evaluated before the
    /// value (§13.2.5.4† ComputedPropertyName evaluation).
    pub(super) fn key_register(&mut self, key_node: u32, dst: Reg) -> R<()> {
        let kn = self.node(key_node)?;
        let ksp = self.sp(key_node);
        match kn.kind {
            NodeKind::IdentifierName | NodeKind::IdentifierReference => {
                let units = literal::name_units_at(self.src, kn.start)?;
                let k = self.konst(Const::String(units))?;
                self.emit(Instr::LoadConst { dst, k }, ksp)
            }
            NodeKind::StringLiteral => {
                let units = literal::string_at(self.src, kn.start)?;
                let k = self.konst(Const::String(units))?;
                self.emit(Instr::LoadConst { dst, k }, ksp)
            }
            NodeKind::NumericLiteral => {
                self.load_number(dst, kn, false, ksp)?;
                self.emit(Instr::ToPropertyKey { dst, src: dst }, ksp)
            }
            NodeKind::ComputedPropertyName => {
                let inner = self.child(kn, 0)?;
                self.expr_to(inner, Some(dst), true)?;
                self.emit(Instr::ToPropertyKey { dst, src: dst }, ksp)
            }
            _ => Err(CompileError::Internal("unexpected property name")),
        }
    }

    /// §13.2.5.4 object literals: `NewObject` and one `DefineProp` or
    /// `DefineElem` per property (§13.2.5.5† step 9, CreateDataPropertyOrThrow,
    /// which does not see a setter or a read-only property on the prototype
    /// chain), `SetLiteralProto` for `__proto__: value` (step 7),
    /// `CopyDataProperties` for a spread, and `DefineMethod` for a method or an
    /// accessor, whose function is a method of the object (MakeMethod).
    pub(super) fn object_literal(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        self.emit(Instr::NewObject { dst: d }, sp)?;
        for &p in &nd.children {
            let pn = self.node(p)?;
            let psp = self.sp(p);
            let m = self.mark();
            match pn.kind {
                NodeKind::PropertyDefinition if pn.op == AOp::Spread => {
                    // §13.2.5.5† PropertyDefinition : `...` AssignmentExpression.
                    let inner = self.child(pn, 0)?;
                    let v = self.expr_any(inner)?;
                    self.emit(
                        Instr::CopyDataProperties {
                            obj: d,
                            src: v,
                            excl: d,
                            nexcl: 0,
                        },
                        psp,
                    )?;
                }
                NodeKind::MethodDefinition => {
                    let key = self.alloc()?;
                    self.key_register(self.child(pn, 0)?, key)?;
                    let f = self.alloc()?;
                    self.make_closure(p, f, FunctionKind::Method)?;
                    self.emit(Instr::SetHomeObject { func: f, obj: d }, psp)?;
                    let form = match pn.op {
                        AOp::Getter => 1,
                        AOp::Setter => 2,
                        _ => 0,
                    };
                    self.emit(
                        Instr::DefineMethod {
                            obj: d,
                            key,
                            func: f,
                            form,
                            enumerable: true,
                        },
                        psp,
                    )?;
                }
                NodeKind::PropertyDefinition => {
                    let (key_node, value_node) = match pn.op {
                        AOp::Shorthand => (self.child(pn, 0)?, self.child(pn, 0)?),
                        AOp::KeyValue => (self.child(pn, 0)?, self.child(pn, 1)?),
                        _ => return Err(CompileError::Internal("unknown property definition")),
                    };
                    let kn = self.node(key_node)?;
                    let plain_key: Option<Vec<u16>> = match kn.kind {
                        NodeKind::IdentifierName | NodeKind::IdentifierReference => {
                            Some(literal::name_units_at(self.src, kn.start)?)
                        }
                        NodeKind::StringLiteral => Some(literal::string_at(self.src, kn.start)?),
                        _ => None,
                    };
                    let name_units = plain_key.clone();
                    let proto: Vec<u16> = "__proto__".encode_utf16().collect();
                    // §13.2.5.5† step 3: `__proto__: value`, with a non-computed key.
                    let is_proto_setter =
                        pn.op == AOp::KeyValue && plain_key.as_deref() == Some(proto.as_slice());
                    // The key first (§13.2.5.5 PropertyDefinitionEvaluation: the
                    // property name is evaluated before the value).
                    let key = match plain_key {
                        Some(units) => Prop::Named(self.konst(Const::String(units))?),
                        None => {
                            let r = self.alloc()?;
                            self.key_register(key_node, r)?;
                            Prop::Computed(r)
                        }
                    };
                    if !is_proto_setter
                        && pn.op == AOp::KeyValue
                        && let Some(units) = &name_units
                    {
                        self.named(value_node, units)?;
                    }
                    let v = self.expr_any(value_node)?;
                    if is_proto_setter {
                        self.emit(Instr::SetLiteralProto { obj: d, val: v }, psp)?;
                    } else {
                        match key {
                            Prop::Named(k) => self.emit(
                                Instr::DefineProp {
                                    obj: d,
                                    key: k,
                                    val: v,
                                },
                                psp,
                            )?,
                            Prop::Computed(idx) => self.emit(
                                Instr::DefineElem {
                                    obj: d,
                                    idx,
                                    val: v,
                                },
                                psp,
                            )?,
                            _ => return Err(CompileError::Internal("unexpected key")),
                        }
                    }
                }
                _ => return Err(CompileError::Internal("unexpected object literal member")),
            }
            self.release(m);
        }
        Ok(())
    }

    /// §13.2.8.6† TemplateLiteral evaluation: the first string, then each
    /// substitution converted by ToString and each following string, joined.
    pub(super) fn template_literal(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let first = self.child(nd, 0)?;
        let (cooked, _) = literal::template_at(self.src, self.node(first)?.start)?;
        let units = cooked.ok_or(CompileError::Internal(
            "untagged template with a bad escape",
        ))?;
        let k = self.konst(Const::String(units))?;
        self.emit(Instr::LoadConst { dst: d, k }, sp)?;
        let mut i = 1;
        while i < nd.children.len() {
            let e = self.child(nd, i)?;
            let m = self.mark();
            let v = self.expr_any(e)?;
            let t = self.alloc()?;
            self.emit(Instr::ToString { dst: t, src: v }, self.sp(e))?;
            self.emit(Instr::Add { dst: d, a: d, b: t }, self.sp(e))?;
            let el = self.child(nd, i.saturating_add(1))?;
            let (cooked, _) = literal::template_at(self.src, self.node(el)?.start)?;
            let units = cooked.ok_or(CompileError::Internal(
                "untagged template with a bad escape",
            ))?;
            if !units.is_empty() {
                let k = self.konst(Const::String(units))?;
                self.emit(Instr::LoadConst { dst: t, k }, self.sp(el))?;
                self.emit(Instr::Add { dst: d, a: d, b: t }, self.sp(el))?;
            }
            self.release(m);
            i = i.saturating_add(2);
        }
        Ok(())
    }

    /// §13.3.11 tagged templates: the tag is called with the template object
    /// (GetTemplateObject, §13.2.8.4†, cached per site) and the substitution
    /// values.
    pub(super) fn tagged_template(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let (tag, tl) = (self.child(nd, 0)?, self.child(nd, 1)?);
        let tag = self.unparen(tag)?;
        let tn = self.node(tl)?;
        let m = self.mark();
        let (fr, this) = (self.alloc()?, self.alloc()?);
        self.callee_and_this(tag, fr, this, sp)?;
        let mut cooked = Vec::new();
        let mut raw = Vec::new();
        let mut subs = Vec::new();
        for (i, &c) in tn.children.iter().enumerate() {
            if i % 2 == 0 {
                let (ck, rw) = literal::template_at(self.src, self.node(c)?.start)?;
                cooked.push(ck);
                raw.push(rw);
            } else {
                subs.push(c);
            }
        }
        let argc = u32::try_from(subs.len().saturating_add(1))
            .map_err(|_| CompileError::TooLarge("arguments"))?;
        let base = self.alloc_n(argc)?;
        let k = self.konst_unique(Const::Template(TemplateSite { cooked, raw }))?;
        self.emit(Instr::GetTemplateObject { dst: base, k }, self.sp(tl))?;
        for (i, &e) in subs.iter().enumerate() {
            let r = base.saturating_add(
                u32::try_from(i.saturating_add(1))
                    .map_err(|_| CompileError::TooLarge("arguments"))?,
            );
            self.expr_to(e, Some(r), true)?;
        }
        self.emit(
            Instr::Call {
                dst: d,
                callee: fr,
                this,
                args: base,
                argc,
            },
            sp,
        )?;
        self.release(m);
        Ok(())
    }

    /// §13.3.9 optional chains: each link applies to the value before it, and a
    /// `?.` link whose value is `undefined` or `null` ends the whole chain with
    /// `undefined` (§13.3.9.1† OptionalChain evaluation: "If baseValue is
    /// either undefined or null, return undefined"). `this_out` receives the
    /// `this` a call of the result would have.
    pub(super) fn optional_chain(
        &mut self,
        n: u32,
        d: Reg,
        this_out: Option<Reg>,
        sp: Span,
    ) -> R<()> {
        self.optional_chain_impl(n, d, this_out, false, sp)
    }

    /// [`Self::optional_chain`], or with `del` the `delete` of the chain
    /// (§13.5.1.2†: `delete` of an OptionalExpression evaluates the chain as a
    /// reference; a chain that ends early is `true`, a chain that ends in a
    /// property reference deletes it, and one that ends in a call is a value, so
    /// `true`).
    pub(super) fn optional_chain_impl(
        &mut self,
        n: u32,
        d: Reg,
        this_out: Option<Reg>,
        del: bool,
        sp: Span,
    ) -> R<()> {
        let nd = self.node(n)?;
        let m = self.mark();
        let (cur, this) = (self.alloc()?, self.alloc()?);
        let undef = self.label();
        let end = self.label();
        let undef_t = Self::label_id(undef)?;
        let base = self.child(nd, 0)?;
        let base = self.unparen(base)?;
        self.callee_and_this(base, cur, this, sp)?;
        let last = nd.children.len().saturating_sub(1);
        for (li, &lk) in nd.children.iter().enumerate().skip(1) {
            let ln = self.node(lk)?;
            let lsp = self.sp(lk);
            if ln.flag {
                self.emit(
                    Instr::JumpIfNullish {
                        src: cur,
                        target: undef_t,
                    },
                    lsp,
                )?;
            }
            let m2 = self.mark();
            if del && li == last && matches!(ln.op, AOp::ChainDot | AOp::ChainBracket) {
                let prop = self.child(ln, 0)?;
                let idx = if ln.op == AOp::ChainDot {
                    let pn = self.node(prop)?;
                    let units = literal::name_units_at(self.src, pn.start)?;
                    let k = self.konst(Const::String(units))?;
                    let r = self.alloc()?;
                    self.emit(Instr::LoadConst { dst: r, k }, lsp)?;
                    r
                } else {
                    self.expr_any(prop)?
                };
                self.emit(
                    Instr::DeleteProp {
                        dst: d,
                        obj: cur,
                        idx,
                    },
                    lsp,
                )?;
                self.release(m2);
                self.jump(end, sp)?;
                self.bind(undef)?;
                self.emit(Instr::LoadBool { dst: d, flag: true }, sp)?;
                self.bind(end)?;
                self.release(m);
                return Ok(());
            }
            match ln.op {
                AOp::ChainDot | AOp::ChainBracket | AOp::ChainPrivateDot => {
                    self.emit(
                        Instr::Move {
                            dst: this,
                            src: cur,
                        },
                        lsp,
                    )?;
                    let prop = self.child(ln, 0)?;
                    let key = match ln.op {
                        AOp::ChainDot => {
                            let pn = self.node(prop)?;
                            let units = literal::name_units_at(self.src, pn.start)?;
                            Prop::Named(self.konst(Const::String(units))?)
                        }
                        AOp::ChainBracket => Prop::Computed(self.expr_any(prop)?),
                        _ => {
                            let r = self.alloc()?;
                            self.read_private_name(prop, r)?;
                            Prop::Private(r)
                        }
                    };
                    self.load_prop(cur, this, &key, lsp)?;
                }
                AOp::ChainCall => {
                    let args = self.child(ln, 0)?;
                    match self.arg_list(args)? {
                        ArgList::Plain(base, argc) => self.emit(
                            Instr::Call {
                                dst: cur,
                                callee: cur,
                                this,
                                args: base,
                                argc,
                            },
                            lsp,
                        )?,
                        ArgList::Spread(arr) => self.emit(
                            Instr::CallSpread {
                                dst: cur,
                                callee: cur,
                                this,
                                args: arr,
                            },
                            lsp,
                        )?,
                    }
                    self.emit(Instr::LoadUndefined { dst: this }, lsp)?;
                }
                _ => return Err(CompileError::Internal("unexpected optional chain link")),
            }
            self.release(m2);
        }
        if del {
            // The chain ended in a call, or in a `?.` that was the whole
            // chain: not a property reference, so `delete` is true.
            self.emit(Instr::LoadBool { dst: d, flag: true }, sp)?;
        } else {
            self.emit(Instr::Move { dst: d, src: cur }, sp)?;
        }
        if let Some(t) = this_out {
            self.emit(Instr::Move { dst: t, src: this }, sp)?;
        }
        self.jump(end, sp)?;
        self.bind(undef)?;
        if del {
            self.emit(Instr::LoadBool { dst: d, flag: true }, sp)?;
        } else {
            self.emit(Instr::LoadUndefined { dst: d }, sp)?;
        }
        self.bind(end)?;
        self.release(m);
        Ok(())
    }

    /// `delete operand` (§13.5.1.2).
    pub(super) fn delete_expr(&mut self, operand: u32, d: Reg, sp: Span) -> R<()> {
        let inner = self.unparen(operand)?;
        let inn = self.node(inner)?;
        match inn.kind {
            NodeKind::MemberExpression => {
                let (obj, prop) = (self.child(inn, 0)?, self.child(inn, 1)?);
                let o = self.operand(obj, &[prop])?;
                let idx = match self.property(inn, prop)? {
                    Prop::Computed(r) => r,
                    Prop::Named(k) => {
                        let r = self.alloc()?;
                        self.emit(Instr::LoadConst { dst: r, k }, sp)?;
                        r
                    }
                    _ => return Err(CompileError::Internal("delete of a private name")),
                };
                self.emit(
                    Instr::DeleteProp {
                        dst: d,
                        obj: o,
                        idx,
                    },
                    sp,
                )
            }
            NodeKind::SuperProperty => {
                // §13.5.1.2 step 4: `delete super.x` is a ReferenceError, after
                // `this` and the key were evaluated.
                let _ = self.place(inner, &[])?;
                self.throw_error(
                    ErrorKind::ReferenceError,
                    "Unsupported reference to 'super'.",
                    sp,
                )
            }
            NodeKind::IdentifierReference => {
                // §13.5.1.2† step 5: `delete name` is DeleteBinding on the
                // environment that holds the name. A binding of a function or block
                // scope is not deletable (§9.1.1.1.7†: false), a global is
                // [`Instr::DeleteGlobal`], and the object of a `with` or the
                // variable object of eval is [`Instr::WithDelete`].
                let m = self.mark();
                let h = self.resolve_dyn(inner, None)?;
                let name = self.name_of(inner);
                let key = self.konst(Const::String(self.name_units(name)?))?;
                let (st, end) = (self.label(), self.label());
                if let Some(h) = h {
                    let target = Self::label_id(st)?;
                    self.emit(Instr::JumpIfUndefined { src: h, target }, sp)?;
                    self.emit(
                        Instr::WithDelete {
                            dst: d,
                            obj: h,
                            key,
                        },
                        sp,
                    )?;
                    self.jump(end, sp)?;
                    self.bind(st)?;
                }
                if self.res(inner) == NONE {
                    self.emit(Instr::DeleteGlobal { dst: d, key }, sp)?;
                } else {
                    self.emit(
                        Instr::LoadBool {
                            dst: d,
                            flag: false,
                        },
                        sp,
                    )?;
                }
                if h.is_some() {
                    self.bind(end)?;
                }
                self.release(m);
                Ok(())
            }
            NodeKind::OptionalExpression => self.optional_chain_impl(inner, d, None, true, sp),
            _ => {
                // §13.5.1.2 step 5: `delete` of a non-reference is true,
                // after evaluating the operand.
                self.expr_to(operand, None, true)?;
                self.emit(Instr::LoadBool { dst: d, flag: true }, sp)
            }
        }
    }
}
