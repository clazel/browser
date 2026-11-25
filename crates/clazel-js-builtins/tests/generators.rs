//! Tests of generators, async functions and async generators (§27.3† to
//! §27.7†, §15.5†, §15.6†, §15.8†), and of `for`-`of`, `yield*` and
//! `for await` over them, as small scripts run with the built-ins installed.
//! Each expectation is what ECMA-262 says, written by hand: the script runs,
//! then the job queue is run to empty (a microtask checkpoint), and the result
//! is the global `r` as its ToString. No files are read; under Miri, where
//! one VM with the built-ins costs about 40 s, two groups run their first
//! case and the rest are left to the native run.

use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;
use clazel_js_vm::interp::{Abrupt, Config, Vm};

fn cps(src: &str) -> Vec<u32> {
    src.chars().map(u32::from).collect()
}

fn config() -> Config {
    if cfg!(miri) {
        Config {
            region_slots: 1 << 12,
            heap_cells: 1 << 14,
        }
    } else {
        Config::default()
    }
}

fn r_of(src: &str) -> Result<String, String> {
    let c = cps(src);
    let ast = parse(&c, SourceGoal::Script).map_err(|_| format!("does not parse: {src}"))?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{src}: {e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("install: {e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.set_budget(5_000_000);
    let run = |vm: &mut Vm, e: Abrupt| {
        let d = match e {
            Abrupt::Throw(v) => vm.describe(v),
            other => format!("{other:?}"),
        };
        format!("{src}: {d}")
    };
    if let Err(e) = vm.run(&script) {
        return Err(run(&mut vm, e));
    }
    if let Err(e) = vm.run_jobs() {
        return Err(run(&mut vm, e));
    }
    let errors = vm.take_job_errors();
    if let Some(e) = errors.first() {
        let d = vm.describe(*e);
        return Err(format!("{src}: a job threw {d}"));
    }
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    let s = vm.to_js_string(r).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(s.to_string_lossy())
}

fn check(cases: &[(&str, &str)]) -> Result<(), String> {
    let n = if cfg!(miri) { 1 } else { cases.len() };
    for (src, want) in cases.iter().take(n) {
        let got = r_of(src)?;
        if got != *want {
            return Err(format!("{src}: expected {want:?}, got {got:?}"));
        }
    }
    Ok(())
}

#[test]
fn generators_yield_and_finish() -> Result<(), String> {
    check(&[
        (
            "function* g() { yield 1; yield 2; return 3; } var it = g(); var a = it.next(), b = it.next(), c = it.next(), d = it.next(); var r = [a.value, a.done, b.value, c.value, c.done, d.value, d.done].join();",
            "1,false,2,3,true,,true",
        ),
        // The body does not run before the first `next`.
        (
            "var r = ''; function* g() { r += 'b'; yield; } var it = g(); r += 'a'; it.next(); r += 'c';",
            "abc",
        ),
        // The value sent by `next` is the result of `yield`; the first is dropped.
        (
            "function* g() { var x = yield 'a'; var y = yield x + 1; return x + y; } var it = g(); var r = [it.next(9).value, it.next(10).value, it.next(20).value].join();",
            "a,11,30",
        ),
        // Locals and arguments survive a suspension.
        (
            "function* g(n) { var t = 0; for (var i = 0; i < n; i++) { t += i; yield t; } } var r = ''; var it = g(4); for (var s = it.next(); !s.done; s = it.next()) r += s.value + ';';",
            "0;1;3;6;",
        ),
        (
            "function* g() { yield arguments.length; yield arguments[1]; } var it = g('a', 'b'); var r = it.next().value + it.next().value;",
            "2b",
        ),
        // `for`-`of` over a generator.
        (
            "function* g() { yield 'x'; yield 'y'; } var r = ''; for (var v of g()) r += v;",
            "xy",
        ),
        // Spread and destructuring.
        (
            "function* g() { yield 1; yield 2; yield 3; } var [a, ...b] = g(); var r = [a, b.length, Math.max(...g())].join();",
            "1,2,3",
        ),
        // A generator method, and `this`.
        (
            "var o = { k: 7, *m() { yield this.k; } }; var r = o.m().next().value;",
            "7",
        ),
        // Class methods of each kind.
        (
            "class C { constructor() { this.k = 1; } *g() { yield this.k; } async a() { return this.k + 1; } static *[Symbol.iterator]() { yield 3; } } var c = new C(); var r = [c.g().next().value, c.a() instanceof Promise, [...C][0], typeof C.prototype.g.prototype].join();",
            "1,true,3,object",
        ),
        // Closures over a generator's bindings.
        (
            "function* g() { let k = 1; const f = () => k; yield f; k = 2; yield f; } var it = g(); var f1 = it.next().value; var r = f1() + ',' + it.next().value();",
            "1,2",
        ),
        // A generator expression with a name.
        (
            "var f = function* fib() { var a = 0, b = 1; while (true) { yield a; [a, b] = [b, a + b]; } }; var r = []; for (var v of f()) { if (v > 20) break; r.push(v); } r = r.join();",
            "0,1,1,2,3,5,8,13",
        ),
    ])
}

#[test]
#[cfg_attr(miri, ignore = "one VM per case; the first group covers Miri")]
fn generator_return_and_throw() -> Result<(), String> {
    check(&[
        // `return` runs the enclosing `finally` blocks.
        (
            "var r = ''; function* g() { try { yield 1; yield 2; } finally { r += 'f'; } } var it = g(); it.next(); var x = it.return(5); r += x.value + ',' + x.done + ',' + it.next().done;",
            "f5,true,true",
        ),
        // A `finally` that yields delays the return.
        (
            "function* g() { try { yield 1; } finally { yield 'cleanup'; } } var it = g(); it.next(); var a = it.return(9); var b = it.next(); var r = [a.value, a.done, b.value, b.done].join();",
            "cleanup,false,9,true",
        ),
        // `throw` at the `yield` can be caught.
        (
            "function* g() { while (true) { try { yield 1; } catch (e) { yield 'caught ' + e; } } } var it = g(); it.next(); var r = it.throw('x').value;",
            "caught x",
        ),
        // An uncaught `throw` completes the generator.
        (
            "function* g() { yield 1; } var it = g(); it.next(); var r; try { it.throw('e'); } catch (e) { r = e; } r += it.next().done;",
            "etrue",
        ),
        // `return` and `throw` before the start complete it without running it.
        (
            "var r = ''; function* g() { r += 'ran'; yield 1; } var it = g(); var x = it.return(3); r += x.value + ',' + x.done + ',' + it.next().done; try { g().throw('t'); } catch (e) { r += e; }",
            "3,true,truet",
        ),
        // An exception in the body propagates to `next`, and the generator is done.
        (
            "function* g() { throw 'bad'; } var it = g(); var r; try { it.next(); } catch (e) { r = e; } r += it.next().done;",
            "badtrue",
        ),
        // A running generator cannot be resumed.
        (
            "var it; function* g() { try { it.next(); } catch (e) { yield e.constructor === TypeError; } } it = g(); var r = it.next().value;",
            "true",
        ),
        // Errors in the parameters are thrown by the call.
        (
            "function* g(a = (function () { throw 'p'; })()) { yield 1; } var r; try { g(); } catch (e) { r = e; }",
            "p",
        ),
        // `break` out of `for`-`of` closes the generator.
        (
            "var r = ''; function* g() { try { yield 1; yield 2; } finally { r += 'closed'; } } for (var v of g()) { r += v; break; }",
            "1closed",
        ),
    ])
}

#[test]
#[cfg_attr(miri, ignore = "one VM per case; the first group covers Miri")]
fn yield_star() -> Result<(), String> {
    check(&[
        (
            "function* inner() { var x = yield 1; yield x; return 'ret'; } function* outer() { var v = yield* inner(); yield v; } var it = outer(); var r = [it.next().value, it.next('sent').value, it.next().value, it.next().done].join();",
            "1,sent,ret,true",
        ),
        // Over an array and a string.
        (
            "function* g() { yield* [1, 2]; yield* 'ab'; } var r = [...g()].join();",
            "1,2,a,b",
        ),
        // `throw` and `return` are delegated.
        (
            "var r = ''; function* inner() { try { yield 1; } catch (e) { r += 'in:' + e; yield 2; } } function* outer() { yield* inner(); } var it = outer(); it.next(); var v = it.throw('x').value; r += v;",
            "in:x2",
        ),
        (
            "var r = ''; function* inner() { try { yield 1; } finally { r += 'inner '; } } function* outer() { try { yield* inner(); } finally { r += 'outer'; } } var it = outer(); it.next(); it.return();",
            "inner outer",
        ),
        // The inner result object is given out as it is.
        (
            "var res = { value: 1, done: false }; var inner = { [Symbol.iterator]() { return this; }, next() { return res; } }; function* g() { yield* inner; } var r = g().next() === res;",
            "true",
        ),
        // Recursion.
        (
            "function* walk(t) { if (Array.isArray(t)) { for (var c of t) yield* walk(c); } else yield t; } var r = [...walk([1, [2, [3, 4]], 5])].join();",
            "1,2,3,4,5",
        ),
    ])
}

#[test]
#[cfg_attr(miri, ignore = "one VM per case; the first group covers Miri")]
fn generator_objects() -> Result<(), String> {
    check(&[
        (
            "function* g() {} var GP = Object.getPrototypeOf(g); var r = [Object.getPrototypeOf(g()) === g.prototype, Object.getPrototypeOf(g.prototype) === GP.prototype, GP.prototype[Symbol.toStringTag], GP[Symbol.toStringTag], typeof GP.prototype.next].join();",
            "true,true,Generator,GeneratorFunction,function",
        ),
        // A generator is not a constructor.
        (
            "function* g() {} var r; try { new g(); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        // `prototype` that is not an object gives the intrinsic.
        (
            "function* g() {} g.prototype = null; var GP = Object.getPrototypeOf(g).prototype; var r = Object.getPrototypeOf(g()) === GP;",
            "true",
        ),
        // The generator is its own iterator.
        (
            "function* g() {} var it = g(); var r = it[Symbol.iterator]() === it;",
            "true",
        ),
        // `next` on something else is a TypeError.
        (
            "function* g() {} var r; try { g.prototype.next.call({}); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        (
            "var r = Object.prototype.toString.call((function* () {})());",
            "[object Generator]",
        ),
    ])
}

#[test]
fn async_functions() -> Result<(), String> {
    check(&[
        // The body runs synchronously up to the first `await`.
        (
            "var r = ''; async function f() { r += 'a'; await null; r += 'c'; } f(); r += 'b';",
            "abc",
        ),
        // The result is a promise of the return value.
        (
            "var r; async function f() { return 5; } var p = f(); p.then(function (v) { r = (p instanceof Promise) + ':' + v; });",
            "true:5",
        ),
        // `await` of a value, a promise and a thenable.
        (
            "var r; async function f() { var a = await 1; var b = await Promise.resolve(2); var c = await { then: function (k) { k(3); } }; return a + b + c; } f().then(function (v) { r = v; });",
            "6",
        ),
        // A throw rejects the promise; a rejection throws at the `await`.
        (
            "var r = ''; async function f() { throw 'x'; } f().catch(function (e) { r += e; }); async function g() { try { await Promise.reject('y'); } catch (e) { return 'caught ' + e; } } g().then(function (v) { r += v; });",
            "xcaught y",
        ),
        // Errors in parameters reject.
        (
            "var r; async function f(a = (function () { throw 'p'; })()) {} f().catch(function (e) { r = e; });",
            "p",
        ),
        // Ordering against other jobs.
        (
            "var r = ''; async function f() { r += '1'; await undefined; r += '3'; await undefined; r += '5'; } f(); Promise.resolve().then(function () { r += '4'; }); r += '2';",
            "12345",
        ),
        // Async arrow functions, with a lexical `this`.
        (
            "var r; var o = { v: 'ok', m: function () { return async () => { await 0; return this.v; }; } }; o.m()().then(function (v) { r = v; });",
            "ok",
        ),
        (
            "var r; var add = async (a, b) => (await a) + (await b); add(Promise.resolve(2), 3).then(function (v) { r = v; });",
            "5",
        ),
        // Loops with awaits keep their locals.
        (
            "var r; async function f() { var t = 0; for (var i = 1; i <= 4; i++) t += await i; return t; } f().then(function (v) { r = v; });",
            "10",
        ),
        // Async methods, and the prototype chain.
        (
            "var r; var o = { async m() { return 1; } }; var AF = Object.getPrototypeOf(o.m); r = [AF[Symbol.toStringTag], typeof o.m.prototype, AF === Object.getPrototypeOf(async function () {})].join();",
            "AsyncFunction,undefined,true",
        ),
        (
            "async function f() {} var r; try { new f(); } catch (e) { r = e.constructor === TypeError; }",
            "true",
        ),
        // Nested async calls.
        (
            "var r; async function a() { return (await b()) + 1; } async function b() { await null; return 1; } a().then(function (v) { r = v; });",
            "2",
        ),
        // `finally` runs around an `await`.
        (
            "var r = ''; async function f() { try { await Promise.reject('e'); } finally { r += 'f'; } } f().catch(function (e) { r += e; });",
            "fe",
        ),
        // Called from a native (`call`), the promise comes back.
        (
            "var r; async function f() { await 0; return this.k; } f.call({ k: 'n' }).then(function (v) { r = v; });",
            "n",
        ),
    ])
}

#[test]
#[cfg_attr(miri, ignore = "one VM per case; the first two groups cover Miri")]
fn async_generators_and_for_await() -> Result<(), String> {
    check(&[
        (
            "var r = ''; async function* g() { yield 1; await null; yield 2; } async function main() { for await (var v of g()) r += v; r += 'done'; } main();",
            "12done",
        ),
        // `for await` over a sync iterable awaits each value.
        (
            "var r = ''; async function main() { for await (var v of [Promise.resolve('a'), 'b']) r += v; } main();",
            "ab",
        ),
        // `next` returns promises of iterator results, queued in order.
        (
            "var r = []; async function* g() { yield 'x'; return 'y'; } var it = g(); it.next().then(function (s) { r.push(s.value, s.done); }); it.next().then(function (s) { r.push(s.value, s.done); }); it.next().then(function (s) { r.push(s.value, s.done); r = r.join(); });",
            "x,false,y,true,,true",
        ),
        // `return` on a suspended-start generator awaits its value.
        (
            "var r; async function* g() { yield 1; } g().return(Promise.resolve(7)).then(function (s) { r = s.value + ',' + s.done; });",
            "7,true",
        ),
        // `yield*` over an async generator.
        (
            "var r = ''; async function* inner() { yield 'a'; yield 'b'; } async function* outer() { yield* inner(); yield 'c'; } async function main() { for await (var v of outer()) r += v; } main();",
            "abc",
        ),
        // A throw in the body rejects the request.
        (
            "var r; async function* g() { throw 'bad'; } g().next().catch(function (e) { r = e; });",
            "bad",
        ),
        (
            "var r; async function* g() {} var AG = Object.getPrototypeOf(g.prototype); r = [AG[Symbol.toStringTag], typeof AG[Symbol.asyncIterator]].join();",
            "AsyncGenerator,function",
        ),
        // `break` out of `for await` calls `return`.
        (
            "var r = ''; async function* g() { try { yield 1; yield 2; } finally { r += 'closed'; } } async function main() { for await (var v of g()) { r += v; break; } } main();",
            "1closed",
        ),
        // `yield` awaits its operand.
        (
            "var r; async function* g() { yield Promise.resolve('p'); } g().next().then(function (s) { r = s.value; });",
            "p",
        ),
    ])
}
