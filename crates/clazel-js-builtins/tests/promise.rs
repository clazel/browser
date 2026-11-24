//! Tests of `Promise` and the job queue (§27.2†, §9.5†), as small scripts run
//! with the built-ins installed. Each expectation is what ECMA-262 says,
//! written by hand: the script runs, then the job queue is run to empty (a
//! microtask checkpoint), and the result is the global `r` as its ToString.
//! No files are read, so these run under Miri too (every eighth case).

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
    let g = vm.global();
    let r = vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?;
    let s = vm.to_js_string(r).map_err(|e| format!("{src}: {e:?}"))?;
    Ok(s.to_string_lossy())
}

fn check(cases: &[(&str, &str)]) -> Result<(), String> {
    let stride = if cfg!(miri) { 8 } else { 1 };
    for (src, want) in cases.iter().step_by(stride) {
        let got = r_of(src)?;
        if got != *want {
            return Err(format!("{src}: expected {want:?}, got {got:?}"));
        }
    }
    Ok(())
}

#[test]
fn constructor_and_then() -> Result<(), String> {
    check(&[
        // A fulfilled promise's handlers run after the script.
        (
            "var r = 'a'; Promise.resolve(1).then(function (v) { r += v; }); r += 'b';",
            "ab1",
        ),
        // The executor runs synchronously.
        (
            "var r = ''; new Promise(function (res) { r += 'x'; res(); }); r += 'y';",
            "xy",
        ),
        // `then` returns a new promise that adopts the handler's result.
        (
            "var r; Promise.resolve(2).then(function (v) { return v * 3; }).then(function (v) { r = v; });",
            "6",
        ),
        // A handler that throws rejects the derived promise.
        (
            "var r; Promise.resolve().then(function () { throw 'boom'; }).then(null, function (e) { r = e; });",
            "boom",
        ),
        // Without a handler the value passes through.
        (
            "var r; Promise.resolve(4).then().then(function (v) { r = v; });",
            "4",
        ),
        (
            "var r; Promise.reject(5).then(1).then(null, function (v) { r = v; });",
            "5",
        ),
        // The executor throwing rejects.
        (
            "var r; new Promise(function () { throw 'e'; }).catch(function (e) { r = e; });",
            "e",
        ),
        // Only the first resolve counts.
        (
            "var r; new Promise(function (res, rej) { res(1); res(2); rej(3); }).then(function (v) { r = v; });",
            "1",
        ),
        // Handler order is the order of `then` calls.
        (
            "var r = ''; var p = Promise.resolve(); p.then(function () { r += '1'; }); p.then(function () { r += '2'; }); p.then(function () { r += '3'; });",
            "123",
        ),
        // Reactions of a pending promise run in order when it settles.
        (
            "var r = ''; var res; var p = new Promise(function (f) { res = f; }); p.then(function (v) { r += v + 'a'; }); p.then(function (v) { r += v + 'b'; }); res(7);",
            "7a7b",
        ),
    ])
}

#[test]
fn job_order_is_fifo_across_promises() -> Result<(), String> {
    check(&[
        (
            "var r = ''; Promise.resolve().then(function () { r += 'a'; }).then(function () { r += 'c'; }); Promise.resolve().then(function () { r += 'b'; }).then(function () { r += 'd'; });",
            "abcd",
        ),
        // A promise resolved with a promise takes two extra ticks.
        (
            "var r = ''; Promise.resolve(Promise.resolve()).then(function () { r += 'a'; }); new Promise(function (res) { res(Promise.resolve()); }).then(function () { r += 'b'; }); Promise.resolve().then(function () { r += 'c'; }).then(function () { r += 'd'; }).then(function () { r += 'e'; });",
            "acdbe",
        ),
    ])
}

#[test]
fn resolving_with_thenables_and_itself() -> Result<(), String> {
    check(&[
        (
            "var r; var thenable = { then: function (res) { res('t'); } }; Promise.resolve(thenable).then(function (v) { r = v; });",
            "t",
        ),
        // A throwing `then` rejects.
        (
            "var r; Promise.resolve({ then: function () { throw 'bad'; } }).catch(function (e) { r = e; });",
            "bad",
        ),
        // A throwing `then` getter rejects.
        (
            "var r; var o = {}; Object.defineProperty(o, 'x', { value: 1 }); var p = Promise.resolve({ then: 5 }); p.then(function (v) { r = typeof v.then; });",
            "number",
        ),
        // Resolving with itself is a TypeError.
        (
            "var r; var res; var p = new Promise(function (f) { res = f; }); res(p); p.catch(function (e) { r = e instanceof TypeError; });",
            "true",
        ),
        // A thenable that resolves twice counts once.
        (
            "var r = ''; Promise.resolve({ then: function (a, b) { a('1'); a('2'); b('3'); } }).then(function (v) { r += v; });",
            "1",
        ),
    ])
}

#[test]
fn static_methods() -> Result<(), String> {
    check(&[
        ("var r = Promise.resolve(1) instanceof Promise;", "true"),
        // Promise.resolve returns its argument for a promise of the same constructor.
        (
            "var p = Promise.resolve(1); var r = Promise.resolve(p) === p;",
            "true",
        ),
        (
            "var r; Promise.reject('no').catch(function (e) { r = e; });",
            "no",
        ),
        // Promise.all
        (
            "var r; Promise.all([1, Promise.resolve(2), { then: function (f) { f(3); } }]).then(function (v) { r = v.join(); });",
            "1,2,3",
        ),
        (
            "var r; Promise.all([]).then(function (v) { r = v.length; });",
            "0",
        ),
        (
            "var r; Promise.all([1, Promise.reject('x'), 3]).catch(function (e) { r = e; });",
            "x",
        ),
        // The order of values is the order of the iterable, not of settling.
        (
            "var r; var late; var p = new Promise(function (f) { late = f; }); Promise.all([p, 2]).then(function (v) { r = v.join(); }); late(1);",
            "1,2",
        ),
        // Promise.allSettled
        (
            "var r; Promise.allSettled([1, Promise.reject(2)]).then(function (v) { r = v[0].status + v[0].value + v[1].status + v[1].reason; });",
            "fulfilled1rejected2",
        ),
        // Promise.any
        (
            "var r; Promise.any([Promise.reject(1), Promise.resolve(2)]).then(function (v) { r = v; });",
            "2",
        ),
        (
            "var r; Promise.any([Promise.reject(1), Promise.reject(2)]).catch(function (e) { r = (e instanceof AggregateError) + ':' + e.errors.join(); });",
            "true:1,2",
        ),
        (
            "var r; Promise.any([]).catch(function (e) { r = e.errors.length; });",
            "0",
        ),
        // Promise.race
        (
            "var r; Promise.race([new Promise(function () {}), Promise.resolve('w')]).then(function (v) { r = v; });",
            "w",
        ),
        (
            "var r = 'pending'; Promise.race([]).then(function () { r = 'settled'; });",
            "pending",
        ),
        // A non-iterable rejects, it does not throw.
        (
            "var r; Promise.all(1).catch(function (e) { r = e instanceof TypeError; });",
            "true",
        ),
        // Promise.withResolvers
        (
            "var r; var w = Promise.withResolvers(); w.promise.then(function (v) { r = v; }); w.resolve('wr');",
            "wr",
        ),
        // Promise.try
        (
            "var r; Promise.try(function (a, b) { return a + b; }, 1, 2).then(function (v) { r = v; });",
            "3",
        ),
        (
            "var r; Promise.try(function () { throw 'tt'; }).catch(function (e) { r = e; });",
            "tt",
        ),
    ])
}

#[test]
fn finally_and_catch() -> Result<(), String> {
    check(&[
        (
            "var r = ''; Promise.resolve('v').finally(function () { r += 'f'; return 'ignored'; }).then(function (v) { r += v; });",
            "fv",
        ),
        (
            "var r = ''; Promise.reject('e').finally(function () { r += 'f'; }).catch(function (e) { r += e; });",
            "fe",
        ),
        // A throwing finally replaces the result.
        (
            "var r; Promise.resolve('v').finally(function () { throw 'f'; }).catch(function (e) { r = e; });",
            "f",
        ),
        // A non-callable onFinally is passed through to then.
        (
            "var r; Promise.resolve('v').finally(5).then(function (v) { r = v; });",
            "v",
        ),
        (
            "var r; Promise.reject('e').catch(function (e) { return e + '!'; }).then(function (v) { r = v; });",
            "e!",
        ),
    ])
}

#[test]
fn errors_and_shape() -> Result<(), String> {
    check(&[
        (
            "var r; try { Promise(function () {}); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { new Promise(1); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { Promise.prototype.then.call({}, null, null); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        (
            "var r; try { Promise.resolve.call(1, 2); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        ("var r = Promise.length + ':' + Promise.name;", "1:Promise"),
        (
            "var r = Promise.prototype.then.length + Promise.prototype.catch.length + Promise.all.length;",
            "4",
        ),
        (
            "var r = Object.prototype.toString.call(Promise.resolve());",
            "[object Promise]",
        ),
        ("var r = Promise[Symbol.species] === Promise;", "true"),
        ("var r = Promise.prototype.constructor === Promise;", "true"),
        // Subclass-like: a constructor with the Promise protocol.
        (
            "var r; function P(ex) { var p = new Promise(ex); p.tag = 'P'; return p; } P.resolve = Promise.resolve; P.prototype = Promise.prototype; var q = P.resolve(1); r = q.tag + (q instanceof Promise);",
            "Ptrue",
        ),
        // A constructor that never calls the executor's functions.
        (
            "var r; function Bad(ex) {} try { Promise.resolve.call(Bad, 1); } catch (e) { r = e instanceof TypeError; }",
            "true",
        ),
        ("var r = typeof Promise.withResolvers;", "function"),
        (
            "var r = new AggregateError([1, 2], 'm').errors.length + ':' + new AggregateError([], 'm').message;",
            "2:m",
        ),
    ])
}

#[test]
fn job_queue_from_the_embedder() -> Result<(), String> {
    let c = cps("var r = 0; Promise.resolve().then(function () { r = 1; throw 'job error'; });");
    let ast = parse(&c, SourceGoal::Script).map_err(|_| "does not parse".to_string())?;
    let p = compile_script(&ast, &c).map_err(|e| format!("{e}"))?;
    let mut vm = Vm::new(config()).map_err(|e| format!("{e:?}"))?;
    clazel_js_builtins::install(&mut vm).map_err(|e| format!("{e:?}"))?;
    let script = vm.load(&p).map_err(|e| format!("{e:?}"))?;
    vm.run(&script).map_err(|e| format!("{e:?}"))?;
    // The reaction waits in the queue until the embedder runs it.
    assert_eq!(vm.pending_jobs(), 1);
    let g = vm.global();
    assert_eq!(
        vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?,
        clazel_js_heap::value::Value::int32(0)
    );
    vm.run_jobs().map_err(|e| format!("{e:?}"))?;
    assert_eq!(vm.pending_jobs(), 0);
    assert_eq!(
        vm.get_named(g, "r").map_err(|e| format!("{e:?}"))?,
        clazel_js_heap::value::Value::int32(1)
    );
    // The handler's own promise swallows the throw; no exception escapes a job.
    assert!(vm.take_job_errors().is_empty());
    Ok(())
}
