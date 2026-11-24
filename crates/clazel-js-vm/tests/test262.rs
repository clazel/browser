//! The compiler over the vendored Test262 sources (`clazel-js-lexer`'s
//! `tests/data/test262/` and its generated table), the evidence the plan asks
//! of item 7.7 at Tier 0.
//!
//! Every test that parses (a test with a `negative:` of phase `parse` or
//! `early` is skipped: there is nothing to compile) is parsed in each mode its
//! flags allow, as `clazel-js-syntax`'s own Test262 test does, and compiled.
//! The harness files (`harness/*.js`) are compiled as scripts. Each source is
//! counted as one of:
//!
//! - **compiled**: [`compile_script`] returned a program, and
//!   [`check_program`] (the executable form of `spec::code_wf`) accepts it;
//! - **not yet compiled**: [`CompileError::NotYetCompiled`], with the
//!   construct named (a histogram is printed);
//! - **failed**: anything else: another [`CompileError`] or a program that
//!   fails the check. This count must be zero.
//!
//! A source that does not parse is counted apart (the parser's own test
//! tracks those).

use clazel_js_syntax::ast::{Ast, NodeKind, Op as AOp};
use clazel_js_syntax::exec::parse;
use clazel_js_syntax::spec::SourceGoal;
use clazel_js_vm::bytecode::{Instr, check_program};
use clazel_js_vm::compile::{CompileError, compile_module, compile_script};
use clazel_js_vm::module::check_module;
use std::collections::BTreeMap;
use std::path::PathBuf;

/// A test's row in the generated table.
struct Case {
    path: &'static str,
    flags: &'static [&'static str],
    features: &'static [&'static str],
    includes: &'static [&'static str],
    negative: Option<(&'static str, &'static str)>,
    expect: Expect,
}

/// Whether a test is expected to pass, and if not why.
enum Expect {
    Run,
    Fail(&'static str),
}

include!("../../clazel-js-lexer/tests/generated/test262.rs");

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../clazel-js-lexer/tests/data/test262/test")
}

/// The runs of a test: its goal and whether to prefix a Use Strict Directive.
fn runs(case: &Case) -> Vec<(SourceGoal, bool)> {
    let has = |f: &str| case.flags.contains(&f);
    if has("module") {
        vec![(SourceGoal::Module, false)]
    } else if has("raw") || has("noStrict") {
        vec![(SourceGoal::Script, false)]
    } else if has("onlyStrict") {
        vec![(SourceGoal::Script, true)]
    } else {
        vec![(SourceGoal::Script, false), (SourceGoal::Script, true)]
    }
}

/// The counts.
#[derive(Default)]
struct Counts {
    compiled: usize,
    not_yet: usize,
    failed: usize,
    no_parse: usize,
    /// Of the compiled sources, the modules.
    modules: usize,
    features: BTreeMap<&'static str, usize>,
    /// For each construct, the number of compiled sources that use it.
    constructs: BTreeMap<&'static str, usize>,
    failures: Vec<String>,
}

/// The constructs of the compiler's second and third slices that `ast` uses.
fn constructs_of(ast: &Ast) -> Vec<&'static str> {
    let mut found = std::collections::BTreeSet::new();
    for (i, n) in ast.nodes.iter().enumerate() {
        let name = match n.kind {
            NodeKind::ObjectBindingPattern
            | NodeKind::ArrayBindingPattern
            | NodeKind::ObjectAssignmentPattern
            | NodeKind::ArrayAssignmentPattern => "destructuring",
            NodeKind::FunctionRestParameter => "rest parameters",
            NodeKind::BindingElement
                if n.children.get(1).is_some_and(|&c| {
                    ast.nodes
                        .get(c as usize)
                        .is_some_and(|x| x.kind != NodeKind::Absent)
                }) && ast.nodes.iter().any(|p| {
                    p.kind == NodeKind::FormalParameters && p.children.contains(&(i as u32))
                }) =>
            {
                "default parameters"
            }
            NodeKind::SpreadElement => "spread",
            NodeKind::PropertyDefinition if n.op == AOp::Spread => "spread",
            NodeKind::TemplateLiteral | NodeKind::TaggedTemplate => "template literals",
            NodeKind::ClassDeclaration | NodeKind::ClassExpression => "classes",
            NodeKind::FieldDefinition => "class fields",
            NodeKind::ClassStaticBlock => "static blocks",
            NodeKind::SuperProperty | NodeKind::SuperCall => "super",
            NodeKind::PrivateIdentifier => "private names",
            NodeKind::NewTarget => "new.target",
            NodeKind::ForInStatement => "for-in",
            NodeKind::ForOfStatement if n.flag => "for await",
            NodeKind::ForOfStatement => "for-of",
            NodeKind::RegularExpressionLiteral => "regex literals",
            NodeKind::GeneratorDeclaration | NodeKind::GeneratorExpression => "generators",
            NodeKind::AsyncFunctionDeclaration
            | NodeKind::AsyncFunctionExpression
            | NodeKind::AsyncArrowFunction => "async functions",
            NodeKind::AsyncGeneratorDeclaration | NodeKind::AsyncGeneratorExpression => {
                "async generators"
            }
            NodeKind::YieldExpression if n.op == AOp::YieldDelegate => "yield*",
            NodeKind::YieldExpression => "yield",
            NodeKind::AwaitExpression => "await",
            NodeKind::WithStatement => "with",
            NodeKind::OptionalExpression => "optional chaining",
            NodeKind::MethodDefinition if matches!(n.op, AOp::Getter | AOp::Setter) => "accessors",
            NodeKind::MethodDefinition
                if matches!(
                    n.op,
                    AOp::GeneratorMethod | AOp::AsyncMethod | AOp::AsyncGeneratorMethod
                ) =>
            {
                "generator and async methods"
            }
            _ => continue,
        };
        found.insert(name);
    }
    found.into_iter().collect()
}

impl Counts {
    fn run(&mut self, name: &str, src: &[u32], goal: SourceGoal) {
        let Ok(ast) = parse(src, goal) else {
            self.no_parse = self.no_parse.saturating_add(1);
            return;
        };
        let compiled = if goal == SourceGoal::Module {
            compile_module(&ast, src).and_then(|m| {
                check_module(&m).map_err(CompileError::Internal)?;
                self.modules = self.modules.saturating_add(1);
                Ok(m.program)
            })
        } else {
            compile_script(&ast, src)
        };
        match compiled {
            Ok(p) => match check_program(&p) {
                Ok(()) => {
                    self.compiled = self.compiled.saturating_add(1);
                    for c in constructs_of(&ast) {
                        let n = self.constructs.entry(c).or_insert(0);
                        *n = n.saturating_add(1);
                    }
                    // The `arguments` object is in the bytecode, not in the AST.
                    let args = p.functions.iter().any(|f| {
                        f.instrs.iter().any(|i| {
                            matches!(
                                i,
                                Instr::CreateMappedArguments { .. }
                                    | Instr::CreateUnmappedArguments { .. }
                            )
                        })
                    });
                    if args {
                        let n = self.constructs.entry("arguments object").or_insert(0);
                        *n = n.saturating_add(1);
                    }
                    // Direct eval and `delete` of a variable are in the bytecode too.
                    for (name, pred) in [
                        (
                            "direct eval",
                            (|i: &Instr| matches!(i, Instr::DirectEval { .. }))
                                as fn(&Instr) -> bool,
                        ),
                        ("delete of a variable", |i: &Instr| {
                            matches!(i, Instr::DeleteGlobal { .. } | Instr::WithDelete { .. })
                        }),
                    ] {
                        if p.functions.iter().any(|f| f.instrs.iter().any(pred)) {
                            let n = self.constructs.entry(name).or_insert(0);
                            *n = n.saturating_add(1);
                        }
                    }
                }
                Err(e) => {
                    self.failed = self.failed.saturating_add(1);
                    self.failures
                        .push(format!("{name}: ill-formed bytecode: {e}"));
                }
            },
            Err(CompileError::NotYetCompiled { feature, .. }) => {
                self.not_yet = self.not_yet.saturating_add(1);
                let n = self.features.entry(feature).or_insert(0);
                *n = n.saturating_add(1);
            }
            Err(e) => {
                self.failed = self.failed.saturating_add(1);
                self.failures.push(format!("{name}: {e}"));
            }
        }
    }
}

fn all_js(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = rd.filter_map(Result::ok).collect();
    entries.sort_by_key(|e| e.path());
    for e in entries {
        let p = e.path();
        if p.is_dir() {
            all_js(&p, out);
        } else if p.extension().is_some_and(|x| x == "js") {
            out.push(p);
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn test262_compiles() -> Result<(), String> {
    assert_eq!(TREE_SHA256.len(), 64);
    let mut counts = Counts::default();
    let (mut tests, mut harness) = (0usize, 0usize);
    let mut test_features = std::collections::BTreeSet::new();
    let mut with_includes = 0usize;
    let mut skipped = std::collections::BTreeSet::new();
    for case in TEST262 {
        test_features.extend(case.features.iter().copied());
        if !case.includes.is_empty() {
            with_includes = with_includes.saturating_add(1);
        }
        if let Expect::Fail(reason) = case.expect {
            skipped.insert(reason);
        }
        if !matches!(case.expect, Expect::Run) {
            continue;
        }
        if matches!(case.negative, Some((phase, _)) if phase == "parse" || phase == "early") {
            continue;
        }
        let path = root().join(case.path);
        let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", case.path))?;
        let body: Vec<u32> = text.chars().map(u32::from).collect();
        tests = tests.saturating_add(1);
        for (goal, strict) in runs(case) {
            let mut src: Vec<u32> = Vec::new();
            if strict {
                src.extend("\"use strict\";\n".chars().map(u32::from));
            }
            src.extend(body.iter().copied());
            counts.run(case.path, &src, goal);
        }
    }
    let mut files = Vec::new();
    all_js(&root().join("../harness"), &mut files);
    for f in &files {
        let text = std::fs::read_to_string(f).map_err(|e| e.to_string())?;
        let src: Vec<u32> = text.chars().map(u32::from).collect();
        harness = harness.saturating_add(1);
        counts.run(&f.display().to_string(), &src, SourceGoal::Script);
    }
    let total = counts.compiled + counts.not_yet + counts.failed;
    println!(
        "{} features, {with_includes} tests with includes, {} reasons for skipped tests",
        test_features.len(),
        skipped.len()
    );
    println!(
        "{tests} tests and {harness} harness files, {total} sources parsed and compiled: {} compiled, {} not yet compiled, {} failed ({} did not parse)",
        counts.compiled, counts.not_yet, counts.failed, counts.no_parse
    );
    let mut by_count: Vec<_> = counts.features.iter().collect();
    by_count.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (feature, n) in by_count {
        println!("  not yet: {n:6}  {feature}");
    }
    println!("  of the compiled sources, {} are modules", counts.modules);
    for (construct, n) in &counts.constructs {
        println!("  compiled with: {n:6}  {construct}");
    }
    assert!(harness > 20, "the harness files were not found");
    assert!(counts.compiled > 0);
    assert!(
        counts.failures.is_empty(),
        "{} sources failed to compile:\n{}",
        counts.failures.len(),
        counts
            .failures
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    Ok(())
}
