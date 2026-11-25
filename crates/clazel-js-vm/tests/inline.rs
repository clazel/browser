//! `clazel_js_syntax::exec::set_inline` reaches the compiler: a program over
//! the 256 AST nodes that `compile_script` hands to a big-stack thread is
//! compiled on the calling thread when it is on. Its own test binary: the
//! switch is process-wide.

use clazel_js_syntax::exec::{big_stack_threads, parse, set_inline};
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::compile::compile_script;

#[test]
fn a_large_program_is_compiled_on_a_thread_unless_inline() -> Result<(), String> {
    let mut s = String::new();
    for i in 0..200 {
        s.push_str(&format!("var v{i} = {i} + 1;\n"));
    }
    let src: Vec<u32> = s.chars().map(u32::from).collect();

    // Parsed inline in both phases, so only the compiler's threads are counted.
    set_inline(true);
    let ast = parse(&src, SourceGoal::Script).map_err(|_| "does not parse".to_owned())?;
    assert!(ast.nodes.len() > 256, "over the compiler's threshold");

    set_inline(false);
    let before = big_stack_threads();
    assert!(compile_script(&ast, &src).is_ok());
    assert_eq!(big_stack_threads(), before.saturating_add(1));

    set_inline(true);
    let before = big_stack_threads();
    assert!(compile_script(&ast, &src).is_ok());
    assert_eq!(big_stack_threads(), before, "inline: no thread was made");
    set_inline(false);
    Ok(())
}
