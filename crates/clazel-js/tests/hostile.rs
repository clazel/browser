//! Hostile pages (phase-7.md 7.19), run through the public embedding API
//! only: none may panic, cross a limit without its error, or hang the host.
//! Each test names the page it stands for and the limit that stops it.
//!
//! Every runtime here uses [`Limits::recommended`] (the limits for untrusted
//! pages on a 2 MiB thread stack, which is what each test runs on), with a
//! smaller heap or value stack where the real size would only make the test
//! slow. Under Miri the inputs are smaller again; each test says how.
//!
//! Not here, because the engine does not have them yet (the PR lists them):
//! `(a+)+b` against a real `RegExp` (there is no RegExp built-in; the
//! matcher's own test is `clazel-js-regexp`'s `tests/limits.rs`), a
//! `MutationObserver` that mutates in its callback (no `MutationObserver`),
//! and a finalizer that resurrects (no `FinalizationRegistry`). The flood of
//! timers is `clazel-web`'s `tests/hostile.rs`, which has the event loop.

use std::time::{Duration, Instant};

use clazel_js::{
    Config, DefaultHost, Error, Key, Limits, Realm, RealmOptions, Result, Runtime, Scope, Source,
};

type Test = core::result::Result<(), Error>;

/// A runtime with `limits` and its realm.
fn runtime(limits: Limits) -> Result<(Runtime, Realm)> {
    let mut rt = Runtime::new(Config::new(limits), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    Ok((rt, realm))
}

/// How a script ended: `Ok(None)` if it returned, `Ok(Some(name))` with the
/// error's name if it threw, and the engine's own error otherwise.
fn outcome(scope: &mut Scope<'_>, realm: &Realm, text: &str) -> Result<Option<String>> {
    match scope.eval_script(realm, Source::new("page.js", text)) {
        Ok(_) => Ok(None),
        Err(Error::Thrown(exception)) => Ok(Some(scope.report(&exception)?.name)),
        Err(other) => Err(other),
    }
}

/// The global `name`, as a string.
fn global_string(scope: &mut Scope<'_>, realm: &Realm, name: &str) -> Result<String> {
    let global = scope.global(realm)?;
    let value = scope.get(global, Key::from(name))?;
    scope.string_to_string_lossy(value)
}

/// The global `name`, as a number.
fn global_number(scope: &mut Scope<'_>, realm: &Realm, name: &str) -> Result<Option<f64>> {
    let global = scope.global(realm)?;
    let value = scope.get(global, Key::from(name))?;
    Ok(scope.as_number(value))
}

/// `while (true) {}`: the embedder's `Terminator`, from a watchdog thread,
/// ends it with `Terminated`, which no `catch` or `finally` sees. The
/// runtime is usable again once the flag is cleared.
#[test]
fn an_endless_loop_is_terminated_from_another_thread() -> Test {
    let (mut rt, realm) = runtime(Limits::recommended())?;
    let terminator = rt.terminator();
    let started = Instant::now();
    let watchdog = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(if cfg!(miri) { 1 } else { 100 }));
        terminator.terminate();
    });
    let result = rt.scope(|scope| {
        outcome(
            scope,
            &realm,
            "var after = 'no';\n\
             try { while (true) {} } catch (e) { after = 'catch'; } finally { after = 'finally'; }",
        )
    });
    let _ = watchdog.join();
    assert!(matches!(result, Err(Error::Terminated)), "{result:?}");
    // Not a hang: the loop ends soon after the flag is set.
    if !cfg!(miri) {
        assert!(started.elapsed() < Duration::from_secs(10));
    }
    rt.terminator().clear();
    let after = rt.scope(|scope| global_string(scope, &realm, "after"))?;
    assert_eq!(after, "no");
    Ok(())
}

/// Unbounded recursion, three ways, each a `RangeError` that JavaScript
/// catches: JS calling JS (the value-stack region), JS calling a native that
/// calls JS (`forEach`: the native depth), and an operation calling JS
/// (`'' + o` calling `o.toString`: the interpreter's re-entries). Without the
/// last two bounds these overflow the 2 MiB host stack and abort the process.
#[test]
fn unbounded_recursion_is_a_range_error() -> Test {
    let limits = Limits {
        // The region is the JS stack; a smaller one is reached sooner.
        value_stack_bytes: if cfg!(miri) { 64 << 10 } else { 4 << 20 },
        ..Limits::recommended()
    };
    let (mut rt, realm) = runtime(limits)?;
    rt.scope(|scope| {
        for page in [
            "function f() { return f() + 1; } f();",
            "function f() { [0].forEach(f); } f();",
            "function f() { return [0].map(f); } f();",
            "var o = {}; o.toString = function () { return '' + o; }; '' + o;",
            "function f() { return f.call(null); } f();",
        ] {
            assert_eq!(
                outcome(scope, &realm, page)?.as_deref(),
                Some("RangeError"),
                "{page}"
            );
            // And `catch` sees it, so the page can go on.
            let caught = format!("var r = 'none'; try {{ {page} }} catch (e) {{ r = e.name; }}");
            assert_eq!(outcome(scope, &realm, &caught)?, None, "{page}");
            assert_eq!(global_string(scope, &realm, "r")?, "RangeError", "{page}");
        }
        Ok(())
    })
}

/// `(a+)+b` on a long input: there is no RegExp built-in yet, so the page
/// gets the API's `NotImplemented` (it neither panics nor runs). The matcher
/// itself is stopped by its bounded stack and interrupt hook in
/// `clazel-js-regexp`'s `tests/limits.rs`.
#[test]
fn a_catastrophic_regexp_is_not_run_yet() -> Test {
    let (mut rt, realm) = runtime(Limits::recommended())?;
    let input = "a".repeat(if cfg!(miri) { 30 } else { 100_000 });
    let page = format!("var r = /(a+)+b/.test('{input}');");
    let result = rt.scope(|scope| outcome(scope, &realm, &page));
    assert!(
        matches!(result, Err(Error::NotImplemented(_))),
        "{result:?}"
    );
    Ok(())
}

/// A string doubled until it would be a gigabyte (`s = s + s` thirty times):
/// the heap limit stops it with a `RangeError`, and the heap never holds
/// more than the limit and its 64 KiB reserve. The page's 1 GiB would need
/// a 1 GiB heap to reach; a 16 MiB heap (256 KiB under Miri) stops the same
/// loop the same way, sooner.
#[test]
fn a_gigabyte_string_build_is_a_range_error() -> Test {
    let heap = if cfg!(miri) { 256 << 10 } else { 16 << 20 };
    let (probe, _) = runtime(Limits::recommended())?;
    let base = probe.heap_used()?;
    let limits = Limits {
        heap_bytes: base + heap,
        ..Limits::recommended()
    };
    let (mut rt, realm) = runtime(limits)?;
    let page = "var s = 'x'; var n = 0; for (var i = 0; i < 30; i++) { s = s + s; n = i; }";
    let name = rt.scope(|scope| outcome(scope, &realm, page))?;
    assert_eq!(name.as_deref(), Some("RangeError"));
    assert!(rt.heap_used()? <= limits.heap_bytes + (64 << 10));
    // It stopped short of thirty doublings.
    let n = rt.scope(|scope| global_number(scope, &realm, "n"))?;
    assert!(n < Some(29.0), "{n:?}");
    Ok(())
}

/// A page that catches the heap limit's `RangeError` and allocates again,
/// for ever: each error comes from the reserve past the limit, and when that
/// is spent the run ends in `OutOfMemory`, which no `catch` sees. It ends;
/// it does not hang.
#[test]
fn catching_the_heap_limit_for_ever_ends_out_of_memory() -> Test {
    let (probe, _) = runtime(Limits::recommended())?;
    let base = probe.heap_used()?;
    let limits = Limits {
        heap_bytes: base + if cfg!(miri) { 16 << 10 } else { 256 << 10 },
        ..Limits::recommended()
    };
    let (mut rt, realm) = runtime(limits)?;
    let page = "var s = 'x'; var caught = 0;\n\
                for (;;) { try { s = s + s; } catch (e) { caught = caught + 1; } }";
    let result = rt.scope(|scope| outcome(scope, &realm, page));
    assert!(matches!(result, Err(Error::OutOfMemory)), "{result:?}");
    let caught = rt.scope(|scope| global_number(scope, &realm, "caught"))?;
    assert!(caught > Some(0.0), "{caught:?}");
    Ok(())
}

/// Objects and arrays grown for ever count against the heap limit too
/// (32 bytes a property), so `push` in an endless loop is a `RangeError`.
#[test]
fn an_array_grown_for_ever_is_a_range_error() -> Test {
    let (probe, _) = runtime(Limits::recommended())?;
    let base = probe.heap_used()?;
    let limits = Limits {
        heap_bytes: base + if cfg!(miri) { 16 << 10 } else { 1 << 20 },
        ..Limits::recommended()
    };
    for page in [
        "var a = []; for (;;) { a.push(a.length); }",
        "var o = {}; var i = 0; for (;;) { o['k' + i] = i; i = i + 1; }",
    ] {
        // A runtime each: nothing is freed, so a full heap stays full, and
        // even compiling the next page would be `OutOfMemory`.
        let (mut rt, realm) = runtime(limits)?;
        let name = rt.scope(|scope| outcome(scope, &realm, page))?;
        assert_eq!(name.as_deref(), Some("RangeError"), "{page}");
        assert!(rt.heap_used()? <= limits.heap_bytes + (64 << 10));
    }
    Ok(())
}

/// 10^6 nested arrays in source: the parser's depth bound makes it a
/// `SyntaxError` before anything runs, and with a lower `nesting_depth` the
/// embedder's limit does the same. Under Miri, 10^4 levels (still past
/// every bound).
#[test]
fn deeply_nested_source_is_a_syntax_error() -> Test {
    let n = if cfg!(miri) { 10_000 } else { 1_000_000 };
    let (mut rt, realm) = runtime(Limits::recommended())?;
    let page = format!("var a = {}{};", "[".repeat(n), "]".repeat(n));
    let name = rt.scope(|scope| outcome(scope, &realm, &page))?;
    assert_eq!(name.as_deref(), Some("SyntaxError"));

    // The embedder's own, lower limit: the height of the parse tree.
    let (mut rt, realm) = runtime(Limits {
        nesting_depth: 64,
        ..Limits::recommended()
    })?;
    rt.scope(|scope| {
        let shallow = format!("var a = {}{};", "[".repeat(5), "]".repeat(5));
        assert_eq!(outcome(scope, &realm, &shallow)?, None);
        let deep = format!("var a = {}{};", "[".repeat(100), "]".repeat(100));
        assert_eq!(
            outcome(scope, &realm, &deep)?.as_deref(),
            Some("SyntaxError")
        );
        Ok(())
    })
}

/// 10^6 nested arrays in JSON: `JSON.parse` throws a `SyntaxError` (the
/// nesting bound of phase-7.md 7.11, lowered by `nesting_depth`), and
/// `JSON.stringify` of a deep object a `RangeError`. Under Miri, 10^4 levels.
#[test]
fn deeply_nested_json_is_an_error() -> Test {
    let n = if cfg!(miri) { 10_000 } else { 1_000_000 };
    let text = format!("{}{}", "[".repeat(n), "]".repeat(n));
    let (mut rt, realm) = runtime(Limits {
        nesting_depth: 16,
        ..Limits::recommended()
    })?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        let deep = scope.string(&text);
        scope.set(global, Key::from("deep"), deep)?;
        let r = outcome(
            scope,
            &realm,
            "var r; try { JSON.parse(deep); r = 'parsed'; } catch (e) { r = e.name; }",
        )?;
        assert_eq!(r, None);
        assert_eq!(global_string(scope, &realm, "r")?, "SyntaxError");
        // Within the embedder's limit of 16 levels, and past it.
        let r = outcome(
            scope,
            &realm,
            "var r = JSON.stringify(JSON.parse('[[[[[[[[[[1]]]]]]]]]]'));",
        )?;
        assert_eq!(r, None);
        assert_eq!(global_string(scope, &realm, "r")?, "[[[[[[[[[[1]]]]]]]]]]");
        assert_eq!(
            outcome(
                scope,
                &realm,
                "JSON.parse('[[[[[[[[[[[[[[[[[[[[1]]]]]]]]]]]]]]]]]]]]');"
            )?
            .as_deref(),
            Some("SyntaxError")
        );
        assert_eq!(
            outcome(
                scope,
                &realm,
                "var o = {}; var c = o; for (var i = 0; i < 1000; i++) { c.a = {}; c = c.a; }\n\
                 JSON.stringify(o);"
            )?
            .as_deref(),
            Some("RangeError")
        );
        Ok(())
    })
}

/// Native functions of the embedder nest within the same limit as the
/// built-ins: a script that recurses through one gets a `RangeError` (not a
/// host stack overflow), and the closure sees the error as `Thrown`.
#[test]
fn recursion_through_an_embedder_native_is_a_range_error() -> Test {
    let (mut rt, realm) = runtime(Limits::recommended())?;
    rt.scope(|scope| {
        let global = scope.global(&realm)?;
        // A native that calls the JS function it is given; JS hands it
        // itself back through a bound function, so the same closure is not
        // re-entered (that is `Busy`, a separate open question).
        for i in 0..64_u32 {
            let relay = scope.function(
                &format!("relay{i}"),
                1,
                clazel_js::Callable::Function,
                move |scope, args| {
                    let this = scope.undefined();
                    let next = scope.number(f64::from(i + 1));
                    scope.call(args.get(0), this, &[next])
                },
            )?;
            scope.set(global, Key::from(format!("relay{i}").as_str()), relay)?;
        }
        let r = outcome(
            scope,
            &realm,
            "function go(i) { return globalThis['relay' + i](go); }\n\
             var r; try { go(0); r = 'returned'; } catch (e) { r = e.name; }",
        )?;
        assert_eq!(r, None);
        assert_eq!(global_string(scope, &realm, "r")?, "RangeError");
        Ok(())
    })
}
