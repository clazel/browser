//! `for`-`in` and `for`-`of` (§14.7.5): the head's evaluation (ForIn/OfHeadEvaluation,
//! §14.7.5.6†), the loop (ForIn/OfBodyEvaluation, §14.7.5.7†) and the closing of
//! the iterator when the loop is left early.
//!
//! The loop of a `for`-`of` has a catch-all exception-table entry over its
//! head binding and body: a throw closes the iterator, ignoring an error of the
//! close (§7.4.11† IteratorClose with a throw completion), and throws again.
//! An exit by `break`, `continue` of an outer loop or `return` closes it with
//! an op that is inside no such entry (see [`Cg::emit_iter_close`]), so an
//! error of that close is the loop's completion, not a second close.

use super::patterns::Mode;
use super::*;

impl<'a> Cg<'a> {
    /// `IterClose` for a loop being left by a `break`, an outer `continue` or a
    /// `return`: the op has its own exception-table entry (which comes before
    /// the loop's, as inner entries do), so that a throw from it is not caught by
    /// the loop's own catch-all.
    pub(super) fn emit_iter_close(&mut self, close: Option<(Reg, usize)>, sp: Span) -> R<()> {
        if let Some((iter, rethrow)) = close {
            let s = self.label();
            let e = self.label();
            self.bind(s)?;
            self.emit(Instr::IterClose { iter }, sp)?;
            self.bind(e)?;
            self.f.handlers.push((s, e, rethrow));
        }
        Ok(())
    }

    /// A fresh environment object for the loop scope `s` (§14.7.5.7†
    /// ForIn/OfBodyEvaluation step 6.g: "Let iterationEnv be NewDeclarativeEnvironment(oldEnv)"),
    /// so a closure made in one iteration keeps that iteration's bindings.
    fn fresh_env(&mut self, s: u32, sp: Span) -> R<()> {
        let sc = self.scope(s)?;
        let env = *self
            .f
            .env_regs
            .get(&s)
            .ok_or(CompileError::Internal("loop scope has no environment"))?;
        let m = self.mark();
        let parent = self.alloc()?;
        self.emit(Instr::GetEnvParent { dst: parent, env }, sp)?;
        self.emit(
            Instr::NewEnv {
                dst: env,
                parent,
                size: sc.env_size,
            },
            sp,
        )?;
        self.release(m);
        Ok(())
    }

    /// §14.7.5 `for ( head in expr ) body` and `for ( head of expr ) body`.
    pub(super) fn for_in_of(&mut self, n: u32, nd: &Node, sp: Span, labels: &[u32]) -> R<()> {
        let (head, expr, body) = (self.child(nd, 0)?, self.child(nd, 1)?, self.child(nd, 2)?);
        let is_of = nd.kind == NodeKind::ForOfStatement;
        let s = self.an.own_scope.get(n as usize).copied().unwrap_or(NONE);
        let m = self.mark();
        // The loop's lexical bindings are in their dead zone while the
        // expression is evaluated (§14.7.5.6† step 2).
        if s != NONE {
            self.enter_scope(s, sp)?;
        }
        let hn = self.node(head)?;
        // Annex B.3.5: `for (var a = init in obj)` assigns the initializer first.
        if hn.kind == NodeKind::ForDeclaration {
            let t = self.child(hn, 0)?;
            if self.node(t)?.kind == NodeKind::VariableDeclaration {
                self.var_declaration(t)?;
            }
        }
        let iter = self.alloc()?;
        {
            let m2 = self.mark();
            let v = self.expr_any(expr)?;
            if is_of {
                self.emit(Instr::GetIterator { dst: iter, src: v }, self.sp(expr))?;
            } else {
                self.emit(Instr::ForInIterator { dst: iter, src: v }, self.sp(expr))?;
            }
            self.release(m2);
        }
        let (val, done, exc) = (self.alloc()?, self.alloc()?, self.alloc()?);
        let top = self.label();
        let end = self.label();
        let region_start = self.label();
        let region_end = self.label();
        let exc_l = self.label();
        let rethrow = self.label();
        self.bind(top)?;
        self.emit(
            Instr::IterNext {
                value: val,
                done,
                iter,
            },
            self.sp(expr),
        )?;
        let end_t = Self::label_id(end)?;
        self.emit(
            Instr::JumpIfTrue {
                cond: done,
                target: end_t,
            },
            self.sp(expr),
        )?;
        self.bind(region_start)?;
        if s != NONE && self.scope(s)?.has_env() {
            self.fresh_env(s, sp)?;
        }
        // The head's binding or assignment target takes the value.
        let hsp = self.sp(head);
        if hn.kind == NodeKind::ForDeclaration {
            let t = self.child(hn, 0)?;
            let tk = self.node(t)?.kind;
            let mode = if hn.op == AOp::Var {
                Mode::Write
            } else {
                Mode::Init
            };
            if tk == NodeKind::VariableDeclaration {
                let id = self.child(self.node(t)?, 0)?;
                self.store_head(id, val, Mode::Write, hsp)?;
            } else {
                self.store_head(t, val, mode, hsp)?;
            }
        } else {
            self.store_head(head, val, Mode::Write, hsp)?;
        }
        self.f.ctl.push(Ctl::Loop {
            labels: labels.to_vec(),
            brk: end,
            cont: top,
            close: if is_of { Some((iter, rethrow)) } else { None },
        });
        self.stmt(body, &[])?;
        self.f.ctl.pop();
        self.bind(region_end)?;
        self.jump(top, sp)?;
        if is_of {
            // A throw in the head binding or the body: close, then throw again.
            self.bind(exc_l)?;
            self.emit(Instr::GetException { dst: exc }, sp)?;
            let (qs, qe, sw) = (self.label(), self.label(), self.label());
            self.bind(qs)?;
            self.emit(Instr::IterClose { iter }, sp)?;
            self.bind(qe)?;
            self.emit(Instr::Throw { src: exc }, sp)?;
            self.bind(sw)?;
            let ignored = self.alloc()?;
            self.emit(Instr::GetException { dst: ignored }, sp)?;
            self.emit(Instr::Throw { src: exc }, sp)?;
            // The stub that an exit's own close falls into if it throws.
            self.bind(rethrow)?;
            let t = self.alloc()?;
            self.emit(Instr::GetException { dst: t }, sp)?;
            self.emit(Instr::Throw { src: t }, sp)?;
            self.f.handlers.push((qs, qe, sw));
            self.f.handlers.push((region_start, region_end, exc_l));
        }
        self.bind(end)?;
        if s != NONE {
            self.exit_scope(s)?;
        }
        self.release(m);
        Ok(())
    }

    /// Stores the iteration value `val` in the loop head's target `t`: a
    /// binding identifier, a pattern, or an assignment target expression.
    fn store_head(&mut self, t: u32, val: Reg, mode: Mode, sp: Span) -> R<()> {
        let t = self.unparen(t)?;
        let tn = self.node(t)?;
        match tn.kind {
            NodeKind::BindingIdentifier | NodeKind::IdentifierReference => {
                if mode == Mode::Init {
                    self.init_ident(t, val, sp)
                } else {
                    self.write_ident(t, val)
                }
            }
            NodeKind::ObjectBindingPattern
            | NodeKind::ArrayBindingPattern
            | NodeKind::ObjectAssignmentPattern
            | NodeKind::ArrayAssignmentPattern => self.destructure(t, val, mode),
            NodeKind::MemberExpression | NodeKind::SuperProperty => {
                let (o, key) = self.place(t, &[])?;
                self.store_prop(o, &key, val, sp)
            }
            _ => self.not_yet("this kind of for-loop target", t),
        }
    }
}
