//! `set_inline_parsing`: with it on, the engine makes no thread of its own to
//! parse or compile a large script (a sandboxed renderer's seccomp filter
//! kills the process at `clone`). This file is its own test binary, so the
//! process-wide switch does not reach another test.

use clazel_js::{Config, DefaultHost, Key, Limits, RealmOptions, Runtime, Source};

/// How many statements [`big_script`] has. Each is six AST nodes, so 64 are
/// 384 nodes, half as many again as the compiler's threshold; Miri runs
/// that many, because it parses and compiles the script twice at about
/// 0.7 s of its time a statement (the 200 took 406 s there, measured).
const STATEMENTS: usize = if cfg!(miri) { 64 } else { 200 };

/// A script over both size thresholds (64 code points to parse, 256 AST
/// nodes to compile): if it were under either, the test's count of threads
/// would be short and it would fail.
fn big_script() -> String {
    let mut s = String::new();
    for i in 0..STATEMENTS {
        s.push_str(&format!("var v{i} = {i} + 1;\n"));
    }
    s.push_str(&format!("var r = v{};", STATEMENTS.saturating_sub(1)));
    s
}

fn run() -> Result<String, clazel_js::Error> {
    let mut rt = Runtime::new(Config::new(Limits::unlimited()), DefaultHost::new())?;
    let realm = rt.scope(|scope| scope.create_realm(RealmOptions::default()))?;
    rt.scope(|scope| {
        scope.eval_script(&realm, Source::new("big.js", &big_script()))?;
        let g = scope.global(&realm)?;
        let r = scope.get(g, Key::from("r"))?;
        let s = scope.to_string(r)?;
        scope.string_to_string_lossy(s)
    })
}

#[test]
fn inline_parsing_makes_no_thread_and_the_default_does() -> Result<(), clazel_js::Error> {
    // The default: a big script is parsed on a thread of its own, and so is
    // its compilation (the counter is how this test sees it).
    let before = clazel_js_syntax::exec::big_stack_threads();
    assert_eq!(run()?, STATEMENTS.to_string());
    assert!(
        clazel_js_syntax::exec::big_stack_threads() >= before.saturating_add(2),
        "the default makes a parser thread and a compiler thread"
    );
    // With the switch on: the same script runs and no thread is made.
    clazel_js::set_inline_parsing(true);
    assert!(clazel_js_syntax::exec::inline());
    let before = clazel_js_syntax::exec::big_stack_threads();
    assert_eq!(run()?, STATEMENTS.to_string());
    assert_eq!(
        clazel_js_syntax::exec::big_stack_threads(),
        before,
        "a thread was made with inline parsing on"
    );
    clazel_js::set_inline_parsing(false);
    Ok(())
}
