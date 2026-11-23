//! The matcher's limits: the bounded backtrack stack, the step budget and the
//! interrupt hook (phase-7.md items 7.10, 7.0(g) and 7.19), on catastrophic
//! patterns. A catastrophic pattern runs until a limit says stop, and ends in
//! an error value, never in a crash or an unbounded allocation.

use clazel_js_regexp::{Flags, Limits, MatchError, Program, compile, parse};

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn build(pattern: &str, flags: &str) -> Result<Program, String> {
    let f = Flags::parse(&units(flags)).map_err(|e| format!("{e:?}"))?;
    let p = parse(&units(pattern), f).map_err(|e| e.to_string())?;
    compile(&p, f).map_err(|e| e.to_string())
}

fn is_match(
    pattern: &str,
    input: &[u16],
    limits: &Limits,
) -> Result<Result<bool, MatchError>, String> {
    let prog = build(pattern, "")?;
    Ok(prog
        .exec(input, 0, false, limits, None)
        .map(|m| m.is_some()))
}

/// How big the pathological inputs are: Miri is about 100 times slower.
fn scale(native: usize, miri: usize) -> usize {
    if cfg!(miri) { miri } else { native }
}

#[test]
fn nested_quantifier_hits_the_step_limit() -> Result<(), String> {
    // (a*)*b on a run of a's: exponentially many ways to split the run, and
    // the empty check keeps the stack shallow, so what stops it is the budget.
    let input = units(&"a".repeat(40));
    let limits = Limits {
        max_stack: 1 << 20,
        max_steps: Some(scale(5_000_000, 20_000) as u64),
    };
    assert_eq!(
        is_match("(a*)*b", &input, &limits)?,
        Err(MatchError::StepLimit)
    );
    assert_eq!(
        is_match("(a+)+b", &input, &limits)?,
        Err(MatchError::StepLimit)
    );
    assert_eq!(
        is_match("(a|a)*b", &input, &limits)?,
        Err(MatchError::StepLimit)
    );
    Ok(())
}

#[test]
fn small_catastrophic_input_still_finishes() -> Result<(), String> {
    // Without a limit the same pattern is just slow: 2^n paths, so n = 14
    // finishes at once and has no match.
    let n = scale(14, 6);
    let input = units(&"a".repeat(n));
    assert_eq!(is_match("(a*)*b", &input, &Limits::default())?, Ok(false));
    let with_b = units(&format!("{}b", "a".repeat(n)));
    assert_eq!(is_match("(a*)*b", &with_b, &Limits::default())?, Ok(true));
    Ok(())
}

#[test]
fn deep_backtracking_hits_the_stack_bound() -> Result<(), String> {
    // (?:a|aa)*b on a long run of a's with no b: every iteration leaves a
    // choice behind, so the first descent is as deep as the input is long. The
    // stack is bounded, so it ends in StackOverflow, with memory never
    // beyond the bound.
    let n = scale(400_000, 2_000);
    let input = units(&"a".repeat(n));
    let limits = Limits {
        max_stack: scale(1 << 20, 1 << 10),
        max_steps: None,
    };
    assert_eq!(
        is_match("(?:a|aa)*b", &input, &limits)?,
        Err(MatchError::StackOverflow)
    );
    assert_eq!(
        is_match("(?:a|b)*c", &input, &limits)?,
        Err(MatchError::StackOverflow)
    );
    // The same bound is what a lookahead in a loop meets.
    assert_eq!(
        is_match("(?:(?=a)a|b)*c", &input, &limits)?,
        Err(MatchError::StackOverflow)
    );
    Ok(())
}

#[test]
fn the_stack_bound_is_exact() -> Result<(), String> {
    // `(?:a|b)*c` needs a number of entries that grows with the input; with a
    // bound just above what it needs it matches, and with half it overflows.
    let input = units(&format!("{}c", "ab".repeat(50)));
    let prog = build("(?:a|b)*c", "")?;
    let run = |max_stack: usize| {
        prog.exec(
            &input,
            0,
            true,
            &Limits {
                max_stack,
                max_steps: None,
            },
            None,
        )
        .map(|m| m.is_some())
    };
    assert_eq!(run(1 << 20), Ok(true));
    let mut need = None;
    for bound in 1..2000 {
        if run(bound) == Ok(true) {
            need = Some(bound);
            break;
        }
    }
    let need = need.ok_or("never matched")?;
    assert_eq!(run(need.saturating_sub(1)), Err(MatchError::StackOverflow));
    // 100 characters, a handful of entries each.
    assert!(need > 100 && need < 1000, "{need}");
    Ok(())
}

#[test]
fn a_zero_bound_overflows_at_the_first_choice() -> Result<(), String> {
    let input = units("ab");
    let limits = Limits {
        max_stack: 0,
        max_steps: None,
    };
    // No choice point, no entry: a plain literal needs no stack.
    assert_eq!(is_match("ab", &input, &limits)?, Ok(true));
    assert_eq!(
        is_match("a|b", &input, &limits)?,
        Err(MatchError::StackOverflow)
    );
    Ok(())
}

#[test]
fn the_interrupt_hook_is_asked_and_can_stop_the_match() -> Result<(), String> {
    let input = units(&"a".repeat(40));
    let prog = build("(a*)*b", "")?;
    let mut asked = 0u32;
    let mut hook = || {
        asked = asked.saturating_add(1);
        asked >= 3
    };
    let r = prog.exec(&input, 0, false, &Limits::default(), Some(&mut hook));
    assert_eq!(r, Err(MatchError::Interrupted));
    assert_eq!(asked, 3);

    // A hook that never says stop does not change the result.
    let short = units("aaab");
    let prog = build("a+b", "")?;
    let mut calls = 0u32;
    let mut hook = || {
        calls = calls.saturating_add(1);
        false
    };
    let r = prog
        .exec(&short, 0, false, &Limits::default(), Some(&mut hook))
        .map_err(|e| e.to_string())?;
    assert!(r.is_some());
    Ok(())
}

#[test]
fn errors_leave_nothing_behind() -> Result<(), String> {
    // The same program is reusable after an error, and gives the same answers.
    let prog = build("(?:a|aa)*b", "")?;
    let long = units(&"a".repeat(scale(100_000, 2_000)));
    let tight = Limits {
        max_stack: 1000,
        max_steps: None,
    };
    assert_eq!(
        prog.exec(&long, 0, false, &tight, None),
        Err(MatchError::StackOverflow)
    );
    let short = units("aab");
    let m = prog
        .exec(&short, 0, false, &Limits::default(), None)
        .map_err(|e| e.to_string())?
        .ok_or("no match")?;
    assert_eq!(m.get(0), Some((0, 3)));
    Ok(())
}

#[test]
fn error_messages_name_the_limit() {
    assert!(MatchError::StackOverflow.to_string().contains("stack"));
    assert!(MatchError::StepLimit.to_string().contains("step"));
    assert!(MatchError::Interrupted.to_string().contains("interrupted"));
}
