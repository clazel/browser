//! Token-level scanner for constructs banned by `CLAUDE.md`.
//!
//! It works on the lexed token stream rather than on text or a syntax tree:
//! comments and string literals are single tokens (or dropped), so they can
//! never produce false hits, and `verus! { ... }` bodies, which are not valid
//! Rust syntax, are still scanned token by token.

use proc_macro2::{Delimiter, TokenStream, TokenTree};

/// What rule a finding breaks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A proof escape hatch (CLAUDE.md rule 4).
    EscapeHatch,
    /// A lint override (CLAUDE.md rule 2).
    LintOverride,
    /// The `unsafe` keyword (CLAUDE.md rule 1).
    Unsafe,
}

/// One banned construct.
#[derive(Debug)]
pub struct Finding {
    pub kind: Kind,
    /// 1-based source line.
    pub line: usize,
    pub what: String,
}

/// Everything the scanner learned about one file.
#[derive(Debug, Default)]
pub struct Scan {
    pub findings: Vec<Finding>,
    /// Number of `#[kani::proof]` harnesses.
    pub kani_proofs: usize,
    /// Every `unsafe` block, as (first line, last line): from the `unsafe`
    /// keyword to the closing brace of the next `{ }` group (a function or
    /// `impl` body, an `unsafe extern` block, or a block expression).
    pub unsafe_spans: Vec<(usize, usize)>,
}

/// `#[verifier::X]` attributes that make Verus trust instead of check.
const BANNED_VERIFIER_ATTRS: &[&str] = &[
    "external_body",
    "external",
    "external_fn_specification",
    "exec_allows_no_decreases_clause",
];

/// The only lint override allowed: `#[allow(unused_imports)]` directly on
/// one of these imports. Ghost items are erased from normal builds, so these
/// imports look unused there.
const ALLOWED_GHOST_IMPORTS: &[&str] = &["vstd::prelude::*", "super::spec::*"];

/// Scan one Rust source file.
pub fn scan(source: &str) -> Result<Scan, String> {
    let stream: TokenStream = source
        .parse()
        .map_err(|e: proc_macro2::LexError| format!("cannot tokenize: {e}"))?;
    let mut out = Scan::default();
    scan_stream(stream, &mut out);
    Ok(out)
}

/// The names of the `proof fn`s defined in a source file, `verus!` bodies
/// included. Comments and strings are not tokens, so a name in one is not a
/// definition.
pub fn proof_fn_names(source: &str) -> Result<Vec<String>, String> {
    let stream: TokenStream = source
        .parse()
        .map_err(|e: proc_macro2::LexError| format!("cannot tokenize: {e}"))?;
    let mut out = Vec::new();
    collect_proof_fns(stream, &mut out);
    Ok(out)
}

fn collect_proof_fns(stream: TokenStream, out: &mut Vec<String>) {
    let tokens: Vec<TokenTree> = stream.into_iter().collect();
    for (k, tt) in tokens.iter().enumerate() {
        match tt {
            TokenTree::Ident(id) if *id == "proof" => {
                if let (Some(TokenTree::Ident(f)), Some(TokenTree::Ident(name))) = (
                    tokens.get(k.saturating_add(1)),
                    tokens.get(k.saturating_add(2)),
                ) && *f == "fn"
                {
                    out.push(name.to_string());
                }
            }
            TokenTree::Group(g) => collect_proof_fns(g.stream(), out),
            _ => {}
        }
    }
}

fn scan_stream(stream: TokenStream, out: &mut Scan) {
    let tokens: Vec<TokenTree> = stream.into_iter().collect();
    let mut k = 0usize;
    while let Some(tt) = tokens.get(k) {
        let mut next = k.saturating_add(1);
        match tt {
            TokenTree::Punct(p) if p.as_char() == '#' => {
                let inner =
                    matches!(tokens.get(next), Some(TokenTree::Punct(b)) if b.as_char() == '!');
                let at = if inner { next.saturating_add(1) } else { next };
                if let Some(TokenTree::Group(g)) = tokens.get(at)
                    && g.delimiter() == Delimiter::Bracket
                {
                    let after = at.saturating_add(1);
                    let rest = tokens.get(after..).unwrap_or(&[]);
                    check_attribute(g.stream(), inner, rest, line_of(tt), out);
                    next = after;
                }
            }
            TokenTree::Ident(id) => {
                let name = id.to_string();
                match name.as_str() {
                    "assume" | "admit"
                        if is_call(&tokens, k) && !qualified_by(&tokens, k, "kani") =>
                    {
                        push(out, Kind::EscapeHatch, tt, format!("{name}(...)"));
                    }
                    "assume_specification" => push(out, Kind::EscapeHatch, tt, name),
                    "unsafe" => {
                        push(out, Kind::Unsafe, tt, name);
                        // `unsafe extern "C" fn(..)` is a function pointer type, not
                        // a block: it is still a finding, but not counted as one.
                        if !fn_pointer_type(&tokens, k) {
                            out.unsafe_spans.push(unsafe_span(&tokens, k));
                        }
                    }
                    _ => {}
                }
            }
            TokenTree::Group(g) => scan_stream(g.stream(), out),
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
        }
        k = next;
    }
}

/// The `unsafe` at `k` starts a function pointer type: `unsafe extern "ABI" fn`.
fn fn_pointer_type(tokens: &[TokenTree], k: usize) -> bool {
    let at = |i: usize| tokens.get(k.saturating_add(i));
    matches!(at(1), Some(TokenTree::Ident(e)) if *e == "extern")
        && matches!(at(2), Some(TokenTree::Literal(_)))
        && matches!(at(3), Some(TokenTree::Ident(f)) if *f == "fn")
}

/// Lines covered by the `unsafe` at `k`: up to the closing brace of the
/// first `{ }` group after it, unless a `;` comes first.
fn unsafe_span(tokens: &[TokenTree], k: usize) -> (usize, usize) {
    let start = tokens.get(k).map_or(0, line_of);
    let end = tokens
        .get(k.saturating_add(1)..)
        .unwrap_or(&[])
        .iter()
        .find_map(|t| match t {
            TokenTree::Group(g) if g.delimiter() == Delimiter::Brace => {
                Some(Some(g.span_close().end().line))
            }
            TokenTree::Punct(p) if p.as_char() == ';' => Some(None),
            _ => None,
        })
        .flatten()
        .unwrap_or(start);
    (start, end.max(start))
}

/// Check the contents of one `#[...]` / `#![...]`; `rest` is what follows it.
fn check_attribute(
    attr: TokenStream,
    inner: bool,
    rest: &[TokenTree],
    line: usize,
    out: &mut Scan,
) {
    let toks: Vec<TokenTree> = attr.into_iter().collect();
    let bang = if inner { "!" } else { "" };
    let shown = || format!("#{bang}[{}]", compact(&toks));
    if let Some(TokenTree::Ident(head)) = toks.first() {
        match head.to_string().as_str() {
            "allow" | "expect" | "warn" => {
                if inner || !is_ghost_import_allow(&toks, rest) {
                    out.findings.push(Finding {
                        kind: Kind::LintOverride,
                        line,
                        what: shown(),
                    });
                }
            }
            "cfg_attr" if contains_ident(&toks, &["allow", "expect", "warn"]) => {
                out.findings.push(Finding {
                    kind: Kind::LintOverride,
                    line,
                    what: shown(),
                });
            }
            "kani" if compact(&toks) == "kani::proof" => {
                out.kani_proofs = out.kani_proofs.saturating_add(1);
            }
            _ => {}
        }
    }
    if contains_ident(&toks, &["verifier"]) {
        for banned in BANNED_VERIFIER_ATTRS {
            if contains_ident(&toks, &[banned]) {
                out.findings.push(Finding {
                    kind: Kind::EscapeHatch,
                    line,
                    what: format!("#[verifier::{banned}]"),
                });
            }
        }
    }
}

/// `#[allow(unused_imports)]` followed by `use <allowed ghost import>;`.
fn is_ghost_import_allow(attr: &[TokenTree], rest: &[TokenTree]) -> bool {
    let attr_ok = matches!(attr, [TokenTree::Ident(a), TokenTree::Group(g)]
        if *a == "allow" && g.delimiter() == Delimiter::Parenthesis && g.stream().to_string() == "unused_imports");
    let Some((TokenTree::Ident(kw), path)) = rest.split_first() else {
        return false;
    };
    let end = path
        .iter()
        .position(|t| matches!(t, TokenTree::Punct(p) if p.as_char() == ';'))
        .unwrap_or(path.len());
    let path = compact(path.get(..end).unwrap_or(&[]));
    attr_ok && *kw == "use" && ALLOWED_GHOST_IMPORTS.contains(&path.as_str())
}

/// Token `k` is immediately followed by a parenthesised group.
fn is_call(tokens: &[TokenTree], k: usize) -> bool {
    matches!(tokens.get(k.saturating_add(1)), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis)
}

/// Token `k` is written as `qualifier::<token k>`.
fn qualified_by(tokens: &[TokenTree], k: usize, qualifier: &str) -> bool {
    let back = |n: usize| k.checked_sub(n).and_then(|j| tokens.get(j));
    matches!((back(3), back(2), back(1)),
        (Some(TokenTree::Ident(q)), Some(TokenTree::Punct(a)), Some(TokenTree::Punct(b)))
        if *q == qualifier && a.as_char() == ':' && b.as_char() == ':')
}

/// Any identifier in `toks`, at any depth, is one of `names`.
fn contains_ident(toks: &[TokenTree], names: &[&str]) -> bool {
    toks.iter().any(|t| match t {
        TokenTree::Ident(id) => names.iter().any(|n| id == n),
        TokenTree::Group(g) => contains_ident(&g.stream().into_iter().collect::<Vec<_>>(), names),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    })
}

/// Tokens joined without whitespace, e.g. `vstd::prelude::*`.
fn compact(toks: &[TokenTree]) -> String {
    toks.iter().map(ToString::to_string).collect()
}

fn line_of(tt: &TokenTree) -> usize {
    tt.span().start().line
}

fn push(out: &mut Scan, kind: Kind, tt: &TokenTree, what: String) {
    out.findings.push(Finding {
        kind,
        line: line_of(tt),
        what,
    });
}

#[cfg(test)]
mod tests {
    use super::{Kind, scan};

    fn kinds(src: &str) -> Result<Vec<Kind>, String> {
        Ok(scan(src)?.findings.iter().map(|f| f.kind).collect())
    }

    #[test]
    fn finds_escape_hatches_inside_verus_macro() -> Result<(), String> {
        let src = "verus! { proof fn p() ensures false { admit(); } \
                   #[verifier::external_body] fn f() {} \
                   #[verifier(external)] fn g() {} \
                   fn h() { assume(1 == 2); } \
                   pub assume_specification[ core::mem::swap ];  }";
        assert_eq!(kinds(src)?, vec![Kind::EscapeHatch; 5]);
        Ok(())
    }

    #[test]
    fn ignores_comments_strings_and_kani_assume() -> Result<(), String> {
        let src = "// admit() in a comment\n\
                   /// assume(x) in a doc comment\n\
                   fn f() { let s = \"admit() unsafe\"; kani::assume(true); let assume = 1; }";
        assert_eq!(kinds(src)?, vec![]);
        Ok(())
    }

    #[test]
    fn lint_overrides() -> Result<(), String> {
        assert_eq!(
            kinds("#[allow(clippy::unwrap_used)] fn f() {}")?,
            vec![Kind::LintOverride]
        );
        assert_eq!(kinds("#![allow(unsafe_code)]")?, vec![Kind::LintOverride]);
        assert_eq!(
            kinds("#[expect(clippy::panic)] fn f() {}")?,
            vec![Kind::LintOverride]
        );
        assert_eq!(
            kinds("#[warn(clippy::indexing_slicing)] fn f() {}")?,
            vec![Kind::LintOverride]
        );
        assert_eq!(
            kinds("#[cfg_attr(test, allow(clippy::panic))] fn f() {}")?,
            vec![Kind::LintOverride]
        );
        // Wrong lint, or wrong import, on an otherwise allowed pattern.
        assert_eq!(
            kinds("#[allow(dead_code)] use vstd::prelude::*;")?,
            vec![Kind::LintOverride]
        );
        assert_eq!(
            kinds("#[allow(unused_imports)] use std::io::*;")?,
            vec![Kind::LintOverride]
        );
        assert_eq!(
            kinds("#![allow(unused_imports)] use vstd::prelude::*;")?,
            vec![Kind::LintOverride]
        );
        Ok(())
    }

    #[test]
    fn allows_ghost_imports() -> Result<(), String> {
        let src = "#[allow(unused_imports)]\nuse vstd::prelude::*;\n\
                   #[allow(unused_imports)]\nuse super::spec::*;";
        assert_eq!(kinds(src)?, vec![]);
        Ok(())
    }

    #[test]
    fn finds_unsafe_and_counts_kani_proofs() -> Result<(), String> {
        let s = scan("#[kani::proof] fn a() {} #[kani::proof] fn b() {\n unsafe {\n } }")?;
        assert_eq!(s.kani_proofs, 2);
        assert_eq!(s.unsafe_spans, vec![(2, 3)]);
        // A function pointer type is a finding but not a block.
        let t = scan("const F: unsafe extern \"C\" fn() = unsafe {\n x\n };")?;
        assert_eq!(t.unsafe_spans, vec![(1, 3)]);
        assert_eq!(t.findings.len(), 2);
        assert_eq!(
            s.findings.iter().map(|f| f.kind).collect::<Vec<_>>(),
            vec![Kind::Unsafe]
        );
        Ok(())
    }

    #[test]
    fn reports_line_numbers() -> Result<(), String> {
        let s = scan("fn ok() {}\n\nfn bad() { admit(); }")?;
        assert_eq!(s.findings.first().map(|f| f.line), Some(3));
        Ok(())
    }
}
