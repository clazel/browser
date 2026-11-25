//! `exec::set_inline`: with it on, a source over the 64 code points that
//! `parse` hands to a big-stack thread is parsed on the calling thread. A
//! sandboxed renderer cannot make a thread (its seccomp filter kills the
//! process at `clone`). Its own test binary: the switch is process-wide.

use clazel_js_syntax::exec::{big_stack_threads, inline, parse, set_inline};
use clazel_js_syntax::spec::SourceGoal;

fn source() -> Vec<u32> {
    let mut s = String::new();
    for i in 0..100 {
        s.push_str(&format!("var v{i} = {i};\n"));
    }
    s.chars().map(u32::from).collect()
}

#[test]
fn a_large_source_is_parsed_on_a_thread_unless_inline() {
    assert!(!inline(), "off by default");
    let src = source();
    let before = big_stack_threads();
    assert!(parse(&src, SourceGoal::Script).is_ok());
    assert_eq!(big_stack_threads(), before.saturating_add(1));

    set_inline(true);
    let before = big_stack_threads();
    assert!(parse(&src, SourceGoal::Script).is_ok());
    assert_eq!(big_stack_threads(), before, "inline: no thread was made");
    // A small source never needed one.
    let small: Vec<u32> = "var a;".chars().map(u32::from).collect();
    assert!(parse(&small, SourceGoal::Script).is_ok());
    assert_eq!(big_stack_threads(), before);
    set_inline(false);
}
