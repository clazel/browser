//! Generators and async functions (phase-7.md item 7.7: "frames are copied to a
//! heap object on suspend and back on resume"): `await`, `yield`, `yield*` and
//! the async closing of iterators.
//!
//! The compiler writes a suspension as one op ([`Instr::Await`], [`Instr::Yield`]
//! or [`Instr::YieldDelegate`]) that gives a value to the consumer and, when the
//! frame is resumed, writes the sent value and a mode into two registers: 0 for a
//! value, 1 for a throw and 2 for a return. The ops after it are jumps on the
//! mode, so everything a resumption can do (throw at the suspension, return
//! through the enclosing `finally` blocks) is ordinary compiled control flow, and
//! the suspension is the only thing the frame copy has to know about. The
//! registers are the frame, so a suspension keeps all locals.
//!
//! - **`await`** (§15.8.5†): `Await`, then a throw if the mode is 1 (Await
//!   §6.2.3.1† step "If result is a throw completion, return ? result").
//! - **`yield`** (§15.5.5†): in a generator `Yield`; in an async generator the
//!   operand is awaited first and a return resumption awaits its value
//!   (AsyncGeneratorYield §27.6.3.8† step 9). A throw resumption throws at the
//!   `yield`; a return resumption is a `return` statement there, so it runs the
//!   `finally` blocks that enclose it.
//! - **`yield*`** (§15.5.5† YieldExpression : `yield *` AssignmentExpression):
//!   the loop of the standard, with the received completion held as a value and
//!   a mode, calling `next`, `throw` or `return` of the inner iterator
//!   ([`Instr::IterCallMethod`]), and in an async generator awaiting each result.

use super::*;

impl<'a> Cg<'a> {
    /// `dst := await src` (Await §6.2.3.1†): the value, or a throw of the
    /// rejection.
    pub(super) fn emit_await(&mut self, src: Reg, dst: Reg, sp: Span) -> R<()> {
        let m = self.mark();
        let mode = self.alloc()?;
        self.emit(
            Instr::Await {
                src,
                value: dst,
                mode,
            },
            sp,
        )?;
        let ok = self.label();
        self.jump_if_false(mode, ok, sp)?;
        self.emit(Instr::Throw { src: dst }, sp)?;
        self.bind(ok)?;
        self.release(m);
        Ok(())
    }

    /// An `await` whose rejection is ignored (the close of an iterator that is
    /// being closed for a throw, §7.4.13† AsyncIteratorClose step 5: the
    /// completion of the await does not replace the throw).
    fn emit_await_quiet(&mut self, src: Reg, sp: Span) -> R<()> {
        let m = self.mark();
        let (value, mode) = (self.alloc()?, self.alloc()?);
        self.emit(Instr::Await { src, value, mode }, sp)?;
        self.release(m);
        Ok(())
    }

    /// AsyncIteratorClose of an iterator for a normal completion (a `break` out
    /// of a `for await` loop, §7.4.13†): the result of `return` is awaited and
    /// must be an Object, and a throw replaces the completion.
    pub(super) fn emit_async_close(&mut self, iter: Reg, sp: Span) -> R<()> {
        let m = self.mark();
        let (res, found) = (self.alloc()?, self.alloc()?);
        self.emit(
            Instr::IterCallMethod {
                dst: res,
                found,
                iter,
                arg: res,
                which: 3,
            },
            sp,
        )?;
        let skip = self.label();
        self.jump_if_false(found, skip, sp)?;
        self.emit_await(res, res, sp)?;
        self.emit(Instr::ThrowIfNotObject { src: res }, sp)?;
        self.bind(skip)?;
        self.release(m);
        Ok(())
    }

    /// AsyncIteratorClose for a throw completion (§7.4.13† step 5: errors of
    /// the `return` call and of the await are dropped, so the caller's throw
    /// stands; the caller covers this with its own handler for the call).
    pub(super) fn emit_async_close_quiet(&mut self, iter: Reg, sp: Span) -> R<()> {
        let m = self.mark();
        let (res, found) = (self.alloc()?, self.alloc()?);
        self.emit(
            Instr::IterCallMethod {
                dst: res,
                found,
                iter,
                arg: res,
                which: 3,
            },
            sp,
        )?;
        let skip = self.label();
        self.jump_if_false(found, skip, sp)?;
        self.emit_await_quiet(res, sp)?;
        self.bind(skip)?;
        self.release(m);
        Ok(())
    }

    /// What follows a suspension: the mode in `mode` (0 value, 1 throw, 2
    /// return) says whether the value in `rv` is the result of the expression
    /// (jump to `ok`), is thrown, or is returned from the function.
    fn after_yield(&mut self, rv: Reg, mode: Reg, ok: usize, sp: Span) -> R<()> {
        self.jump_if_false(mode, ok, sp)?;
        let m = self.mark();
        let (k, c) = (self.alloc()?, self.alloc()?);
        self.load_int(k, 1, sp)?;
        self.emit(
            Instr::StrictEq {
                dst: c,
                a: mode,
                b: k,
            },
            sp,
        )?;
        let ret = self.label();
        self.jump_if_false(c, ret, sp)?;
        self.emit(Instr::Throw { src: rv }, sp)?;
        self.bind(ret)?;
        if self.f.flavor == Flavor::AsyncGenerator {
            // AsyncGeneratorYield §27.6.3.8† step 9.b: a return resumption
            // awaits its value; a rejection is thrown.
            self.emit_await(rv, rv, sp)?;
        }
        self.emit_exit(Exit::Return, Some(rv), sp)?;
        self.release(m);
        Ok(())
    }

    /// `yield` and `yield*` into `d`.
    pub(super) fn yield_expr(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        if nd.op == AOp::YieldDelegate {
            return self.yield_star(nd, d, sp);
        }
        let arg = self.child(nd, 0)?;
        let m = self.mark();
        let (v, rv, mode) = (self.alloc()?, self.alloc()?, self.alloc()?);
        if self.node(arg)?.kind == NodeKind::Absent {
            self.emit(Instr::LoadUndefined { dst: v }, sp)?;
        } else {
            self.expr_to(arg, Some(v), true)?;
        }
        if self.f.flavor == Flavor::AsyncGenerator {
            // §15.5.5† step 3.b: "Return ? AsyncGeneratorYield(? Await(value))".
            self.emit_await(v, v, sp)?;
        }
        self.emit(
            Instr::Yield {
                src: v,
                value: rv,
                mode,
            },
            sp,
        )?;
        let ok = self.label();
        self.after_yield(rv, mode, ok, sp)?;
        self.bind(ok)?;
        self.emit(Instr::Move { dst: d, src: rv }, sp)?;
        self.release(m);
        Ok(())
    }

    /// `yield* operand`.
    fn yield_star(&mut self, nd: &Node, d: Reg, sp: Span) -> R<()> {
        let asyn = self.f.flavor == Flavor::AsyncGenerator;
        let arg = self.child(nd, 0)?;
        let m = self.mark();
        let iter = self.alloc()?;
        let (rv, mode, res, found, done, val) = (
            self.alloc()?,
            self.alloc()?,
            self.alloc()?,
            self.alloc()?,
            self.alloc()?,
            self.alloc()?,
        );
        {
            let m2 = self.mark();
            let v = self.expr_any(arg)?;
            let ins = if asyn {
                Instr::GetAsyncIterator { dst: iter, src: v }
            } else {
                Instr::GetIterator { dst: iter, src: v }
            };
            self.emit(ins, sp)?;
            self.release(m2);
        }
        // received := NormalCompletion(undefined).
        self.emit(Instr::LoadUndefined { dst: rv }, sp)?;
        self.load_int(mode, 0, sp)?;
        let (top, do_next, do_throw, yield_l, throw_missing, end) = (
            self.label(),
            self.label(),
            self.label(),
            self.label(),
            self.label(),
            self.label(),
        );
        self.bind(top)?;
        // Dispatch on the received completion.
        self.jump_if_false(mode, do_next, sp)?;
        let (k, c) = (self.alloc()?, self.alloc()?);
        self.load_int(k, 1, sp)?;
        self.emit(
            Instr::StrictEq {
                dst: c,
                a: mode,
                b: k,
            },
            sp,
        )?;
        self.jump_if_true(c, do_throw, sp)?;
        // A return completion (step 7.c): `return` of the inner iterator.
        let ret_missing = self.label();
        self.emit(
            Instr::IterCallMethod {
                dst: res,
                found,
                iter,
                arg: rv,
                which: 2,
            },
            sp,
        )?;
        self.jump_if_false(found, ret_missing, sp)?;
        if asyn {
            self.emit_await(res, res, sp)?;
        }
        self.emit(Instr::IterComplete { done, result: res }, sp)?;
        self.jump_if_false(done, yield_l, sp)?;
        self.emit(
            Instr::IterValue {
                dst: val,
                result: res,
            },
            sp,
        )?;
        self.emit_exit(Exit::Return, Some(val), sp)?;
        // No `return` method (step 7.c.iii): return the received value,
        // awaited in an async generator.
        self.bind(ret_missing)?;
        if asyn {
            self.emit_await(rv, rv, sp)?;
        }
        self.emit_exit(Exit::Return, Some(rv), sp)?;
        // A throw completion (step 7.b).
        self.bind(do_throw)?;
        self.emit(
            Instr::IterCallMethod {
                dst: res,
                found,
                iter,
                arg: rv,
                which: 1,
            },
            sp,
        )?;
        self.jump_if_false(found, throw_missing, sp)?;
        if asyn {
            self.emit_await(res, res, sp)?;
        }
        self.emit(Instr::IterComplete { done, result: res }, sp)?;
        self.jump_if_false(done, yield_l, sp)?;
        self.emit(
            Instr::IterValue {
                dst: val,
                result: res,
            },
            sp,
        )?;
        self.jump(end, sp)?;
        // No `throw` method (step 7.b.iii): close the iterator, then a
        // TypeError.
        self.bind(throw_missing)?;
        if asyn {
            self.emit_async_close(iter, sp)?;
        } else {
            self.emit(Instr::IterClose { iter }, sp)?;
        }
        self.throw_error(
            ErrorKind::TypeError,
            "The iterator does not provide a 'throw' method",
            sp,
        )?;
        // A normal completion (step 7.a).
        self.bind(do_next)?;
        self.emit(
            Instr::IterCallMethod {
                dst: res,
                found,
                iter,
                arg: rv,
                which: 0,
            },
            sp,
        )?;
        if asyn {
            self.emit_await(res, res, sp)?;
        }
        self.emit(Instr::IterComplete { done, result: res }, sp)?;
        self.jump_if_false(done, yield_l, sp)?;
        self.emit(
            Instr::IterValue {
                dst: val,
                result: res,
            },
            sp,
        )?;
        self.jump(end, sp)?;
        // The inner result is not done: yield it, and handle the resumption.
        self.bind(yield_l)?;
        let again = self.label();
        if asyn {
            // AsyncGeneratorYield(? IteratorValue(innerResult)), whose return
            // resumption awaits its value (§27.6.3.8† step 9.b); a rejection of
            // that await is the received completion, a throw.
            self.emit(
                Instr::IterValue {
                    dst: val,
                    result: res,
                },
                sp,
            )?;
            self.emit(
                Instr::Yield {
                    src: val,
                    value: rv,
                    mode,
                },
                sp,
            )?;
            self.load_int(k, 2, sp)?;
            self.emit(
                Instr::StrictEq {
                    dst: c,
                    a: mode,
                    b: k,
                },
                sp,
            )?;
            self.jump_if_false(c, again, sp)?;
            let m3 = self.mark();
            let (av, am) = (self.alloc()?, self.alloc()?);
            self.emit(
                Instr::Await {
                    src: rv,
                    value: av,
                    mode: am,
                },
                sp,
            )?;
            self.emit(Instr::Move { dst: rv, src: av }, sp)?;
            self.jump_if_false(am, again, sp)?;
            self.load_int(mode, 1, sp)?;
            self.release(m3);
        } else {
            // GeneratorYield(innerResult): the result object goes out as it is.
            self.emit(
                Instr::YieldDelegate {
                    src: res,
                    value: rv,
                    mode,
                },
                sp,
            )?;
        }
        self.bind(again)?;
        self.jump(top, sp)?;
        self.bind(end)?;
        self.emit(Instr::Move { dst: d, src: val }, sp)?;
        self.release(m);
        Ok(())
    }
}
