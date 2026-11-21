//! Destructuring (phase-7.md item 7.7): binding patterns (§14.3.3†, §8.6.2†
//! BindingInitialization) and assignment patterns (§13.15.5†
//! DestructuringAssignmentEvaluation), and the parameter list of a function
//! that is not a simple one (§10.2.11† FunctionDeclarationInstantiation steps
//! 21 to 26).
//!
//! # Iterator closing
//!
//! An array pattern keeps its own `[[Done]]` flag in a register: it is set
//! before every `IterNext` (so a `next()` that throws leaves it set) and holds
//! the op's `done` result after. When the pattern ends normally the iterator is
//! closed (IteratorClose, §7.4.11†) unless it is done; when an element throws,
//! an exception-table entry catches it, closes the iterator unless it is done,
//! ignoring an error of the close itself (§7.4.11† step 4: a throw completion
//! wins), and throws the original value again.

use super::*;

/// What a destructured value is stored with.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    /// The initialization of a binding (`let`, `const`, a parameter, a `catch`
    /// parameter): no check and no `const` rule.
    Init,
    /// An assignment, PutValue (`var`, an assignment expression, a `for`-`in`
    /// or `for`-`of` head that is not a lexical declaration).
    Write,
}

/// A destructuring target, evaluated before the value is read (§13.15.5.5†
/// step 1: "If DestructuringAssignmentTarget is neither an ObjectLiteral nor an
/// ArrayLiteral, let lref be Evaluation of DestructuringAssignmentTarget").
enum Target {
    /// An identifier: the node.
    Ident(u32),
    /// A property reference: the object register and the key.
    Place(Reg, Prop),
    /// A nested pattern: the node.
    Pattern(u32),
}

impl<'a> Cg<'a> {
    /// Whether `n` is a binding or assignment pattern.
    pub(super) fn is_pattern(&self, n: u32) -> R<bool> {
        Ok(matches!(
            self.node(n)?.kind,
            NodeKind::ObjectBindingPattern
                | NodeKind::ArrayBindingPattern
                | NodeKind::ObjectAssignmentPattern
                | NodeKind::ArrayAssignmentPattern
        ))
    }

    /// `target = init` with `target` a pattern: evaluates `init`, then
    /// destructures it.
    pub(super) fn destructure_init(&mut self, target: u32, init: u32, mode: Mode) -> R<()> {
        let m = self.mark();
        let v = self.expr_any(init)?;
        self.destructure(target, v, mode)?;
        self.release(m);
        Ok(())
    }

    /// Evaluates the reference of destructuring target `t` (see [`Target`]).
    fn prepare_target(&mut self, t: u32) -> R<Target> {
        let t = self.unparen(t)?;
        let tn = self.node(t)?;
        match tn.kind {
            NodeKind::BindingIdentifier | NodeKind::IdentifierReference => Ok(Target::Ident(t)),
            NodeKind::ObjectBindingPattern
            | NodeKind::ArrayBindingPattern
            | NodeKind::ObjectAssignmentPattern
            | NodeKind::ArrayAssignmentPattern => Ok(Target::Pattern(t)),
            NodeKind::MemberExpression | NodeKind::SuperProperty => {
                let (o, key) = self.place(t, &[])?;
                // Copy the object and key out of any variable's register: a later
                // element may assign that variable before this target is stored.
                let oc = self.alloc()?;
                self.emit(Instr::Move { dst: oc, src: o }, self.sp(t))?;
                let key = match key {
                    Prop::Computed(r) => {
                        let c = self.alloc()?;
                        self.emit(Instr::Move { dst: c, src: r }, self.sp(t))?;
                        Prop::Computed(c)
                    }
                    k => k,
                };
                Ok(Target::Place(oc, key))
            }
            _ => self.not_yet("this kind of destructuring target", t),
        }
    }

    /// Stores `val` in the target.
    fn store_target(&mut self, t: &Target, val: Reg, mode: Mode) -> R<()> {
        match *t {
            Target::Ident(n) => {
                let b = self.res(n);
                if mode == Mode::Init && b != NONE {
                    self.init_binding(b, val, self.sp(n))
                } else {
                    self.write_ident(n, val)
                }
            }
            Target::Place(o, ref key) => {
                let sp = self.sp(o.min(self.f.max_reg));
                let _ = sp;
                self.store_prop(o, key, val, Span { start: 0, end: 0 })
            }
            Target::Pattern(p) => self.destructure(p, val, mode),
        }
    }

    /// The target and the initializer of an element: a `BindingElement` or an
    /// `AssignmentElement`, the shorthand `AssignmentProperty`.
    fn element_parts(&self, el: u32) -> R<(u32, Option<u32>)> {
        let en = self.node(el)?;
        let target = self.child(en, 0)?;
        let init = match en.children.get(1) {
            Some(&i) if self.node(i)?.kind != NodeKind::Absent => Some(i),
            _ => None,
        };
        Ok((target, init))
    }

    /// Destructures the value in `val` by pattern `p`.
    pub(super) fn destructure(&mut self, p: u32, val: Reg, mode: Mode) -> R<()> {
        let pn = self.node(p)?;
        match pn.kind {
            NodeKind::ObjectBindingPattern | NodeKind::ObjectAssignmentPattern => {
                self.object_pattern(p, pn, val, mode)
            }
            NodeKind::ArrayBindingPattern | NodeKind::ArrayAssignmentPattern => {
                self.array_pattern(p, pn, val, mode)
            }
            _ => Err(CompileError::Internal("not a pattern")),
        }
    }

    /// The default value: `if t is undefined, t := init` (§14.3.3.3†
    /// SingleNameBinding steps 3 and 4: "If Initializer is present and v is
    /// undefined").
    fn default_value(&mut self, t: Reg, init: Option<u32>) -> R<()> {
        if let Some(i) = init {
            let skip = self.label();
            let target = Self::label_id(skip)?;
            self.emit(Instr::JumpIfNotUndefined { src: t, target }, self.sp(i))?;
            self.expr_to(i, Some(t), true)?;
            self.bind(skip)?;
        }
        Ok(())
    }

    /// §8.6.2† BindingInitialization of an ObjectBindingPattern and §13.15.5.2†
    /// of an ObjectAssignmentPattern: RequireObjectCoercible, then each
    /// property in order, then the rest property.
    fn object_pattern(&mut self, p: u32, pn: &Node, val: Reg, mode: Mode) -> R<()> {
        let sp = self.sp(p);
        // RequireObjectCoercible (§7.2.1†): `undefined` and `null` are a TypeError.
        let ok = self.label();
        let target = Self::label_id(ok)?;
        self.emit(Instr::JumpIfNotNullish { src: val, target }, sp)?;
        self.throw_error(
            ErrorKind::TypeError,
            "Cannot destructure an undefined or null value.",
            sp,
        )?;
        self.bind(ok)?;
        let m = self.mark();
        let rest = match pn.children.last() {
            Some(&r)
                if matches!(
                    self.node(r)?.kind,
                    NodeKind::BindingRestProperty | NodeKind::AssignmentRestProperty
                ) =>
            {
                Some(r)
            }
            _ => None,
        };
        let props: Vec<u32> = pn
            .children
            .iter()
            .copied()
            .take(
                pn.children
                    .len()
                    .saturating_sub(usize::from(rest.is_some())),
            )
            .collect();
        let nprops = u32::try_from(props.len()).map_err(|_| CompileError::TooLarge("pattern"))?;
        let excl = if rest.is_some() {
            self.alloc_n(nprops)?
        } else {
            0
        };
        for (idx, &pr) in props.iter().enumerate() {
            let prn = self.node(pr)?;
            let psp = self.sp(pr);
            let m2 = self.mark();
            let shorthand = prn.op == AOp::Shorthand;
            // The property name, then the element.
            let (key_node, element) = if shorthand {
                (None, self.child(prn, 0)?)
            } else {
                (Some(self.child(prn, 0)?), self.child(prn, 1)?)
            };
            let (target_node, init) = if prn.kind == NodeKind::AssignmentProperty && shorthand {
                // `{ a = 1 }`: the identifier and its initializer are the children.
                let init = match prn.children.get(1) {
                    Some(&i) if self.node(i)?.kind != NodeKind::Absent => Some(i),
                    _ => None,
                };
                (element, init)
            } else {
                self.element_parts(element)?
            };
            let key_reg_slot = excl.saturating_add(u32::try_from(idx).unwrap_or(0));
            let key: Prop = match key_node {
                None => {
                    let name = self.name_units(self.name_of(target_node))?;
                    Prop::Named(self.konst(Const::String(name))?)
                }
                Some(kn_id) => {
                    let kn = self.node(kn_id)?;
                    match kn.kind {
                        NodeKind::IdentifierName => {
                            let name = literal::name_units_at(self.src, kn.start)?;
                            Prop::Named(self.konst(Const::String(name))?)
                        }
                        NodeKind::StringLiteral => {
                            let name = literal::string_at(self.src, kn.start)?;
                            Prop::Named(self.konst(Const::String(name))?)
                        }
                        NodeKind::NumericLiteral => {
                            let r = self.alloc()?;
                            self.load_number(r, kn, false, self.sp(kn_id))?;
                            let k = if rest.is_some() {
                                key_reg_slot
                            } else {
                                self.alloc()?
                            };
                            self.emit(Instr::ToPropertyKey { dst: k, src: r }, self.sp(kn_id))?;
                            Prop::Computed(k)
                        }
                        NodeKind::ComputedPropertyName => {
                            let inner = self.child(kn, 0)?;
                            let r = self.alloc()?;
                            self.expr_to(inner, Some(r), true)?;
                            let k = if rest.is_some() {
                                key_reg_slot
                            } else {
                                self.alloc()?
                            };
                            self.emit(Instr::ToPropertyKey { dst: k, src: r }, self.sp(kn_id))?;
                            Prop::Computed(k)
                        }
                        _ => return Err(CompileError::Internal("unexpected property name")),
                    }
                }
            };
            if rest.is_some()
                && let Prop::Named(k) = key
            {
                self.emit(
                    Instr::LoadConst {
                        dst: key_reg_slot,
                        k,
                    },
                    psp,
                )?;
            }
            let tgt = self.prepare_target(target_node)?;
            let t = self.alloc()?;
            self.load_prop(t, val, &key, psp)?;
            self.default_value(t, init)?;
            self.store_target(&tgt, t, mode)?;
            self.release(m2);
        }
        if let Some(r) = rest {
            let rn = self.node(r)?;
            let rsp = self.sp(r);
            let target_node = self.child(rn, 0)?;
            let tgt = self.prepare_target(target_node)?;
            let obj = self.alloc()?;
            self.emit(Instr::NewObject { dst: obj }, rsp)?;
            self.emit(
                Instr::CopyDataProperties {
                    obj,
                    src: val,
                    excl,
                    nexcl: nprops,
                },
                rsp,
            )?;
            self.store_target(&tgt, obj, mode)?;
        }
        self.release(m);
        Ok(())
    }

    /// One `IteratorStepValue` of a pattern (§7.4.9†): into `dst` (`undefined`
    /// once the iterator is done), keeping the pattern's `[[Done]]` in `done`.
    fn iter_step(&mut self, iter: Reg, done: Reg, dst: Reg, sp: Span) -> R<()> {
        let undef = self.label();
        let end = self.label();
        let undef_t = Self::label_id(undef)?;
        let end_t = Self::label_id(end)?;
        self.emit(
            Instr::JumpIfTrue {
                cond: done,
                target: undef_t,
            },
            sp,
        )?;
        self.emit(
            Instr::LoadBool {
                dst: done,
                flag: true,
            },
            sp,
        )?;
        self.emit(
            Instr::IterNext {
                value: dst,
                done,
                iter,
            },
            sp,
        )?;
        self.emit(
            Instr::JumpIfFalse {
                cond: done,
                target: end_t,
            },
            sp,
        )?;
        self.bind(undef)?;
        self.emit(Instr::LoadUndefined { dst }, sp)?;
        self.bind(end)
    }

    /// §8.6.2† BindingInitialization of an ArrayBindingPattern and §13.15.5.3†
    /// of an ArrayAssignmentPattern, with the iterator closed as the module
    /// header says.
    fn array_pattern(&mut self, p: u32, pn: &Node, val: Reg, mode: Mode) -> R<()> {
        let sp = self.sp(p);
        let m = self.mark();
        let iter = self.alloc()?;
        let done = self.alloc()?;
        self.emit(
            Instr::GetIterator {
                dst: iter,
                src: val,
            },
            sp,
        )?;
        self.emit(
            Instr::LoadBool {
                dst: done,
                flag: false,
            },
            sp,
        )?;
        let start = self.label();
        let end = self.label();
        let catch_l = self.label();
        self.bind(start)?;
        for &el in &pn.children {
            let eln = self.node(el)?;
            let esp = self.sp(el);
            let m2 = self.mark();
            match eln.kind {
                NodeKind::Elision => {
                    let t = self.alloc()?;
                    self.iter_step(iter, done, t, esp)?;
                }
                NodeKind::BindingRestElement | NodeKind::AssignmentRestElement => {
                    let target_node = self.child(eln, 0)?;
                    let tgt = self.prepare_target(target_node)?;
                    let arr = self.alloc()?;
                    let idx = self.alloc()?;
                    let t = self.alloc()?;
                    self.emit(Instr::NewArray { dst: arr, len: 0 }, esp)?;
                    self.load_int(idx, 0, esp)?;
                    let top = self.label();
                    let out = self.label();
                    let out_t = Self::label_id(out)?;
                    self.bind(top)?;
                    self.emit(
                        Instr::JumpIfTrue {
                            cond: done,
                            target: out_t,
                        },
                        esp,
                    )?;
                    self.emit(
                        Instr::LoadBool {
                            dst: done,
                            flag: true,
                        },
                        esp,
                    )?;
                    self.emit(
                        Instr::IterNext {
                            value: t,
                            done,
                            iter,
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
                    self.emit(
                        Instr::DefineElem {
                            obj: arr,
                            idx,
                            val: t,
                        },
                        esp,
                    )?;
                    self.emit(Instr::Inc { dst: idx, src: idx }, esp)?;
                    self.jump(top, esp)?;
                    self.bind(out)?;
                    self.store_target(&tgt, arr, mode)?;
                }
                _ => {
                    let (target_node, init) = self.element_parts(el)?;
                    let tgt = self.prepare_target(target_node)?;
                    let t = self.alloc()?;
                    self.iter_step(iter, done, t, esp)?;
                    self.default_value(t, init)?;
                    self.store_target(&tgt, t, mode)?;
                }
            }
            self.release(m2);
        }
        self.bind(end)?;
        // Normal completion: close the iterator unless it is done.
        let after = self.label();
        let after_t = Self::label_id(after)?;
        self.emit(
            Instr::JumpIfTrue {
                cond: done,
                target: after_t,
            },
            sp,
        )?;
        self.emit(Instr::IterClose { iter }, sp)?;
        self.jump(after, sp)?;
        // An element threw: close the iterator unless it is done, ignoring an
        // error of the close, then throw the original value again.
        self.bind(catch_l)?;
        let e = self.alloc()?;
        self.emit(Instr::GetException { dst: e }, sp)?;
        let rethrow = self.label();
        let rethrow_t = Self::label_id(rethrow)?;
        self.emit(
            Instr::JumpIfTrue {
                cond: done,
                target: rethrow_t,
            },
            sp,
        )?;
        let qs = self.label();
        let qe = self.label();
        let sw = self.label();
        self.bind(qs)?;
        self.emit(Instr::IterClose { iter }, sp)?;
        self.bind(qe)?;
        self.bind(rethrow)?;
        self.emit(Instr::Throw { src: e }, sp)?;
        self.bind(sw)?;
        let ignored = self.alloc()?;
        self.emit(Instr::GetException { dst: ignored }, sp)?;
        self.emit(Instr::Throw { src: e }, sp)?;
        self.f.handlers.push((qs, qe, sw));
        self.f.handlers.push((start, end, catch_l));
        self.bind(after)?;
        self.release(m);
        Ok(())
    }

    /// The number of parameters (the registers of the arguments: every
    /// parameter but the rest parameter) and the function's `length` (the
    /// parameters before the first with an initializer, §15.1.5†
    /// ExpectedArgumentCount) of a `FormalParameters` node.
    pub(super) fn param_counts(&self, fp: u32) -> R<(u32, u32)> {
        let mut n: u32 = 0;
        let mut length: u32 = 0;
        let mut counting = true;
        for &c in &self.node(fp)?.children {
            let cn = self.node(c)?;
            if cn.kind != NodeKind::BindingElement {
                counting = false;
                continue;
            }
            n = n.saturating_add(1);
            let has_init = match cn.children.get(1) {
                Some(&i) => self.node(i)?.kind != NodeKind::Absent,
                None => false,
            };
            if has_init {
                counting = false;
            }
            if counting {
                length = length.saturating_add(1);
            }
        }
        Ok((n, length))
    }

    /// The start of a function's code after its scope is entered: a base class
    /// constructor initializes its instance (§10.2.2† [[Construct]] step 6.b),
    /// then the parameters of a non-simple list are bound in order (§10.2.11†
    /// step 26, IteratorBindingInitialization).
    pub(super) fn function_prologue(&mut self, nd: &Node, sp: Span) -> R<()> {
        if self.f.kind == FunctionKind::Class {
            let m = self.mark();
            let (t, c) = (self.alloc()?, self.alloc()?);
            self.emit(Instr::GetThis { dst: t }, sp)?;
            self.emit(Instr::GetCallee { dst: c }, sp)?;
            self.emit(Instr::InitInstance { obj: t, func: c }, sp)?;
            self.release(m);
        }
        let fp = match nd.kind {
            NodeKind::Script | NodeKind::ClassStaticBlock => return Ok(()),
            NodeKind::ArrowFunction => self.child(nd, 0)?,
            _ => self.child(nd, 1)?,
        };
        if self.node(fp)?.kind != NodeKind::FormalParameters || self.f.simple_params {
            return Ok(());
        }
        let (nparams, _) = self.param_counts(fp)?;
        for (idx, &el) in self.node(fp)?.children.iter().enumerate() {
            let eln = self.node(el)?;
            let esp = self.sp(el);
            let m = self.mark();
            if eln.kind == NodeKind::FunctionRestParameter {
                let target_node = self.child(eln, 0)?;
                let arr = self.alloc()?;
                self.emit(
                    Instr::CreateRestArray {
                        dst: arr,
                        from: nparams,
                    },
                    esp,
                )?;
                let tgt = self.prepare_target(target_node)?;
                self.store_target(&tgt, arr, Mode::Init)?;
            } else {
                let (target_node, init) = self.element_parts(el)?;
                let t = self.alloc()?;
                let src = u32::try_from(idx).map_err(|_| CompileError::TooLarge("parameters"))?;
                self.emit(Instr::Move { dst: t, src }, esp)?;
                self.default_value(t, init)?;
                let tgt = self.prepare_target(target_node)?;
                self.store_target(&tgt, t, Mode::Init)?;
            }
            self.release(m);
        }
        Ok(())
    }
}
