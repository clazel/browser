//! Totality on hostile input: deeply nested and very long sources are
//! rejected (or accepted) without overflowing the stack, and a source that
//! nests more than the limit is [`ParseError::TooDeep`].

use clazel_js_syntax::api::ParseError;
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;

fn run(s: &str) -> Result<(), ParseError> {
    let src: Vec<u32> = s.chars().map(u32::from).collect();
    parse(&src, SourceGoal::Script).map(|_| ())
}

// Each case is 100 000 levels; under Miri one 2 000-token chain already takes
// minutes, and this test ran the CI runner out until it was shut down.
// `a_chain_past_the_limit_is_too_deep` covers the `TooDeep` path under Miri.
#[test]
#[cfg_attr(miri, ignore = "each case takes minutes under Miri")]
fn deeply_nested_is_rejected_not_a_crash() {
    let n = 100_000;
    let cases: Vec<String> = vec![
        "(".repeat(n),
        "[".repeat(n),
        "{".repeat(n),
        format!("{}a", "!".repeat(n)),
        format!("{}a", "- ".repeat(n)),
        format!("{}a", "a+".repeat(n)),
        format!("{}a", "a.".repeat(n)),
        format!("a{}", "(a)".repeat(n)),
        format!("{}a", "a=".repeat(n)),
        format!("{}a", "a?b:".repeat(n)),
        format!("{}x", "x=>".repeat(n)),
        format!("{}a", "new ".repeat(n)),
        format!("{}b", "if(a)".repeat(n)),
        format!("{}a", "a**".repeat(n)),
        format!("{}1", "({a:".repeat(n)),
        format!("{}1", "[".repeat(n)),
        "function f(){".repeat(n),
        "x=function(){".repeat(n),
        "class A{m(){".repeat(n),
        "async()=>{".repeat(n),
        "`${".repeat(n),
        "label:".repeat(n),
        "var [".repeat(n),
        "for(;;)".repeat(n),
        "try{".repeat(n),
    ];
    for (i, c) in cases.iter().enumerate() {
        let r = run(c);
        assert!(r.is_err(), "case {i} was accepted");
    }
}

#[test]
fn a_chain_past_the_limit_is_too_deep() {
    // Left associative: a loop, no recursion, but 1025 nodes high.
    let s = format!("a{}", "+a".repeat(1100));
    assert!(matches!(run(&s), Err(ParseError::TooDeep)));
    let s = format!("a{}", "+a".repeat(1000));
    assert!(run(&s).is_ok());
}

// Sources of 600 000 to 900 000 characters: hours under Miri.
#[test]
#[cfg_attr(miri, ignore = "each case takes minutes under Miri")]
fn long_flat_programs_parse() {
    let s = "a;\n".repeat(200_000);
    assert!(run(&s).is_ok());
    let s = format!("[{}]", "1,".repeat(300_000));
    assert!(run(&s).is_ok());
    let s = format!("f({})", "a,".repeat(300_000));
    assert!(run(&s).is_ok());
}
