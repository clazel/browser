//! The `unsafe` policy (Phase 2 item 2.0, CLAUDE.md rule 1).
//!
//! `unsafe` is allowed in exactly one crate, `crates/clazel-sys`, which
//! enters the OS sandbox. This module enforces what "audited" means for it:
//!
//! 1. only that crate overrides the `unsafe_code` lint, and only that lint
//!    (its `[lints]` tables equal the workspace's except `unsafe_code`);
//! 2. its only dependency is `libc`, pinned exactly;
//! 3. every `unsafe` is a block or an `unsafe extern` block, never an
//!    `unsafe fn`, `impl` or `trait`;
//! 4. each `unsafe { }` block holds exactly one call, to a foreign function
//!    on a fixed list ([`FOREIGN_FUNCTIONS`]; `syscall` only with a number
//!    from [`SYSCALLS`]), and no pointer dereference;
//! 5. each `unsafe` has a `// SAFETY:` comment directly above it that cites
//!    a man page (`man 2 prctl`);
//! 6. no raw pointer arithmetic, and no public foreign function: the crate's
//!    public API is safe;
//! 7. the latest row of `docs/SYS-AUDITS.md` carries the SHA-256 of the
//!    crate's source ([`source_hash`]), so every change is audited.
//!
//! And the README's memory-safety sentence states the measured `unsafe` count
//! ([`readme_problems`]).
//!
//! What no machine can check, and CLAUDE.md states as a rule: the session
//! that wrote a change to `clazel-sys` never writes its audit.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};

/// The one crate that may contain `unsafe`, relative to the repository root.
pub const CRATE_DIR: &str = "crates/clazel-sys";
/// The crate's name.
pub const CRATE_NAME: &str = "clazel-sys";
/// The audit log.
pub const AUDITS: &str = "docs/SYS-AUDITS.md";

/// Foreign functions `clazel-sys` may declare or call. `syscall` is the
/// route to `seccomp(2)`, the three `landlock_*` system calls and `ptrace(2)`
/// on Linux (glibc does not wrap the first four, and its `ptrace` is variadic
/// with a request type that differs between libcs); it may only be called with a number from
/// [`SYSCALLS`]. Errno is read with `std::io::Error::last_os_error`, which
/// is safe, so it needs no entry.
pub const FOREIGN_FUNCTIONS: &[&str] = &[
    "sandbox_init",
    "sandbox_free_error",
    "prctl",
    "syscall",
    "unshare",
    // The escape attempts of the sandbox tests (phase-2.md item 2.16): each
    // returns only whether the OS allowed it. `fork`'s child calls `_exit`
    // at once. `ptrace` is a foreign function on macOS; on Linux it is
    // reached through `syscall` with `SYS_ptrace`.
    "fork",
    "_exit",
    "ptrace",
    // Windows (`clazel-sys/src/windows.rs`): start a process inside an
    // AppContainer and a Job Object, check the token, and one escape attempt
    // (`OpenProcess`, the analogue of `ptrace` attach). Each is documented on
    // Microsoft Learn, cited as `docs <function>`.
    "CreateAppContainerProfile",
    "DeriveAppContainerSidFromAppContainerName",
    "GetLengthSid",
    "CopySid",
    "FreeSid",
    "InitializeProcThreadAttributeList",
    "UpdateProcThreadAttribute",
    "DeleteProcThreadAttributeList",
    "CreateProcessW",
    "CloseHandle",
    "CreateJobObjectW",
    "SetInformationJobObject",
    "SetHandleInformation",
    "WaitForSingleObject",
    "GetExitCodeProcess",
    "TerminateProcess",
    "OpenProcess",
    "OpenProcessToken",
    "GetTokenInformation",
];

/// The system call numbers `syscall` may be given (names as in `libc`).
pub const SYSCALLS: &[&str] = &[
    "SYS_seccomp",
    "SYS_landlock_create_ruleset",
    "SYS_landlock_add_rule",
    "SYS_landlock_restrict_self",
    "SYS_ptrace",
];

/// Method and function names that do pointer arithmetic. Banned in the
/// crate, whether or not the receiver is a raw pointer.
const POINTER_ARITHMETIC: &[&str] = &[
    "add",
    "sub",
    "offset",
    "offset_from",
    "offset_from_unsigned",
    "sub_ptr",
    "byte_add",
    "byte_sub",
    "byte_offset",
    "byte_offset_from",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_offset",
    "wrapping_byte_add",
    "wrapping_byte_sub",
    "wrapping_byte_offset",
];

/// Words that may be followed by a parenthesis without being a call.
const NOT_CALLS: &[&str] = &[
    "as", "if", "while", "match", "in", "return", "for", "let", "mut", "const", "move", "else",
    "loop", "break", "ref",
];

/// What the checker learned about one source file of `clazel-sys`.
#[derive(Debug, Default)]
pub struct File {
    /// Violations as (1-based line, what).
    pub violations: Vec<(usize, String)>,
}

/// Check one source file of `clazel-sys` against rules 3 to 6.
pub fn check_source(source: &str) -> Result<File, String> {
    let stream: TokenStream = source
        .parse()
        .map_err(|e: proc_macro2::LexError| format!("cannot tokenize: {e}"))?;
    let tokens: Vec<TokenTree> = stream.into_iter().collect();
    let lines: Vec<&str> = source.lines().collect();
    let mut file = File::default();
    walk(&tokens, None, &lines, &mut file);
    file.violations.sort();
    Ok(file)
}

/// The calls found so far in the `unsafe { }` block being checked.
struct Block {
    calls: Vec<String>,
}

fn flag(file: &mut File, line: usize, what: impl Into<String>) {
    file.violations.push((line, what.into()));
}

fn line_of(tt: &TokenTree) -> usize {
    tt.span().start().line
}

fn is_punct(tt: Option<&TokenTree>, c: char) -> bool {
    matches!(tt, Some(TokenTree::Punct(p)) if p.as_char() == c)
}

fn ident_is(tt: Option<&TokenTree>, name: &str) -> bool {
    matches!(tt, Some(TokenTree::Ident(i)) if *i == name)
}

fn walk(tokens: &[TokenTree], mut block: Option<&mut Block>, lines: &[&str], file: &mut File) {
    let mut k = 0usize;
    while let Some(tt) = tokens.get(k) {
        let next = tokens.get(k.saturating_add(1));
        let prev = k.checked_sub(1).and_then(|j| tokens.get(j));
        let line = line_of(tt);
        match tt {
            TokenTree::Ident(id) => {
                let name = id.to_string();
                if name == "unsafe" {
                    if block.is_some() {
                        flag(file, line, "nested `unsafe` inside an `unsafe` block");
                    } else if let Some(TokenTree::Group(g)) = next
                        && g.delimiter() == Delimiter::Brace
                    {
                        require_safety_comment(lines, line, file);
                        let mut inner = Block { calls: Vec::new() };
                        let body: Vec<TokenTree> = g.stream().into_iter().collect();
                        walk(&body, Some(&mut inner), lines, file);
                        if inner.calls.len() != 1 {
                            flag(
                                file,
                                line,
                                format!(
                                    "an `unsafe` block must hold exactly one foreign call, found {}",
                                    inner.calls.len()
                                ),
                            );
                        }
                        k = k.saturating_add(2);
                        continue;
                    } else if ident_is(next, "extern") {
                        require_safety_comment(lines, line, file);
                        // `unsafe extern "C" { ... }`: skip the ABI string.
                        let rest = tokens.get(k.saturating_add(2)..).unwrap_or(&[]);
                        let at = rest.iter().position(|t| {
                            matches!(t, TokenTree::Group(g) if g.delimiter() == Delimiter::Brace)
                        });
                        match at.and_then(|i| rest.get(i)) {
                            Some(TokenTree::Group(g)) => check_extern(g, file),
                            _ => flag(file, line, "`unsafe extern` without a block"),
                        }
                        k = k.saturating_add(3).saturating_add(at.unwrap_or(0));
                        continue;
                    } else {
                        flag(
                            file,
                            line,
                            "`unsafe` may only start a block or an `unsafe extern` block, \
                             not `unsafe fn`, `impl` or `trait`",
                        );
                    }
                }
                if name == "extern" && !ident_is(prev, "unsafe") {
                    flag(file, line, "`extern` outside an `unsafe extern` block");
                }
                if name == "macro_rules" || name == "include" {
                    flag(
                        file,
                        line,
                        format!("`{name}` could hide `unsafe` from this check"),
                    );
                }
                if POINTER_ARITHMETIC.contains(&name.as_str()) && call_or_turbofish(next, tokens, k)
                {
                    flag(file, line, format!("raw pointer arithmetic: `{name}`"));
                }
                if name == "pub" {
                    check_pub_use(tokens, k, file);
                }
                if let Some(b) = block.as_deref_mut()
                    && let Some(TokenTree::Group(args)) = next
                    && args.delimiter() == Delimiter::Parenthesis
                    && !NOT_CALLS.contains(&name.as_str())
                {
                    check_call(&name, args, line, b, file);
                }
            }
            TokenTree::Punct(p) if p.as_char() == '#' => {
                // `#[path = ".."]` would pull in source this check never reads.
                let at = if is_punct(next, '!') {
                    k.saturating_add(2)
                } else {
                    k.saturating_add(1)
                };
                if let Some(TokenTree::Group(g)) = tokens.get(at)
                    && g.delimiter() == Delimiter::Bracket
                    && matches!(g.stream().into_iter().next(), Some(TokenTree::Ident(i)) if i == "path")
                {
                    flag(file, line, "`#[path]` attribute");
                }
            }
            TokenTree::Punct(p) if p.as_char() == '*' && block.is_some() => {
                let type_position =
                    ident_is(prev, "as") || ident_is(next, "const") || ident_is(next, "mut");
                if !type_position {
                    flag(
                        file,
                        line,
                        "dereference or multiplication inside an `unsafe` block",
                    );
                }
            }
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
            TokenTree::Group(_) => {}
        }
        // Everything inside a group, a call's arguments included, is walked
        // too, so nested calls are seen.
        if let TokenTree::Group(g) = tt {
            let body: Vec<TokenTree> = g.stream().into_iter().collect();
            walk(&body, block.as_deref_mut(), lines, file);
        }
        k = k.saturating_add(1);
    }
}

/// `name(` or `name::<..>(`: the identifier at `k` is being called.
fn call_or_turbofish(next: Option<&TokenTree>, tokens: &[TokenTree], k: usize) -> bool {
    match next {
        Some(TokenTree::Group(g)) => g.delimiter() == Delimiter::Parenthesis,
        Some(TokenTree::Punct(p)) if p.as_char() == ':' => {
            is_punct(tokens.get(k.saturating_add(2)), ':')
                && is_punct(tokens.get(k.saturating_add(3)), '<')
        }
        _ => false,
    }
}

/// A call `name(args)` inside an `unsafe` block: it must be a permitted
/// foreign function, and `syscall` only with a permitted number.
fn check_call(name: &str, args: &Group, line: usize, block: &mut Block, file: &mut File) {
    if !FOREIGN_FUNCTIONS.contains(&name) {
        flag(
            file,
            line,
            format!("`{name}` is not a permitted foreign function (see xtask/src/sys.rs)"),
        );
        return;
    }
    if name == "syscall" {
        let toks: Vec<TokenTree> = args.stream().into_iter().collect();
        let first: Vec<&TokenTree> = toks
            .iter()
            .take_while(|t| !is_punct(Some(t), ','))
            .collect();
        let number = first.iter().rev().find_map(|t| match t {
            TokenTree::Ident(i) => Some(i.to_string()),
            _ => None,
        });
        if !number.as_deref().is_some_and(|n| SYSCALLS.contains(&n)) {
            flag(
                file,
                line,
                format!("`syscall` with {number:?}: only {SYSCALLS:?} are permitted"),
            );
            return;
        }
    }
    block.calls.push(name.to_owned());
}

/// `unsafe extern { ... }`: only private function declarations from the list.
fn check_extern(g: &Group, file: &mut File) {
    let body: Vec<TokenTree> = g.stream().into_iter().collect();
    for (k, tt) in body.iter().enumerate() {
        let TokenTree::Ident(id) = tt else { continue };
        let line = line_of(tt);
        match id.to_string().as_str() {
            "pub" => flag(
                file,
                line,
                "foreign declaration is `pub`: the public API must be safe",
            ),
            "safe" => flag(
                file,
                line,
                "`safe fn` in `unsafe extern` skips the `unsafe` block",
            ),
            "static" | "type" => flag(
                file,
                line,
                "only functions may be declared in `unsafe extern`",
            ),
            "fn" => {
                let name = match body.get(k.saturating_add(1)) {
                    Some(TokenTree::Ident(n)) => n.to_string(),
                    _ => String::new(),
                };
                if !FOREIGN_FUNCTIONS.contains(&name.as_str()) {
                    flag(
                        file,
                        line,
                        format!(
                            "`{name}` is not a permitted foreign function (see xtask/src/sys.rs)"
                        ),
                    );
                }
            }
            _ => {}
        }
    }
}

/// `pub use ...libc...;` would hand callers an unsafe foreign function.
fn check_pub_use(tokens: &[TokenTree], k: usize, file: &mut File) {
    let mut at = k.saturating_add(1);
    if matches!(tokens.get(at), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis)
    {
        at = at.saturating_add(1);
    }
    if !ident_is(tokens.get(at), "use") {
        return;
    }
    let rest = tokens.get(at..).unwrap_or(&[]);
    let end = rest
        .iter()
        .position(|t| is_punct(Some(t), ';'))
        .unwrap_or(rest.len());
    let has_libc = rest
        .get(..end)
        .unwrap_or(&[])
        .iter()
        .any(|t| contains_ident(t, "libc"));
    if has_libc {
        flag(
            file,
            tokens.get(k).map_or(0, line_of),
            "`pub use` of `libc` would export an unsafe function",
        );
    }
}

fn contains_ident(tt: &TokenTree, name: &str) -> bool {
    match tt {
        TokenTree::Ident(i) => *i == name,
        TokenTree::Group(g) => g.stream().into_iter().any(|t| contains_ident(&t, name)),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    }
}

/// Rule 5: the comment lines directly above `line` (1-based) include a
/// `// SAFETY:` line, and the comment cites a man page ("man 2 prctl").
fn require_safety_comment(lines: &[&str], line: usize, file: &mut File) {
    let mut comment = Vec::new();
    let mut idx = line.saturating_sub(1);
    while let Some(above) = idx.checked_sub(1) {
        match lines.get(above) {
            Some(l) if l.trim_start().starts_with("//") => {
                comment.push(l.trim_start());
                idx = above;
            }
            _ => break,
        }
    }
    comment.reverse();
    if !comment.iter().any(|l| l.starts_with("// SAFETY:")) {
        flag(
            file,
            line,
            "`unsafe` without a `// SAFETY:` comment directly above it",
        );
    } else if !cites_man_page(&comment.join(" ")) {
        flag(
            file,
            line,
            "the `// SAFETY:` comment does not cite a man page (e.g. `man 2 prctl`)",
        );
    }
}

/// The text contains `man <section digit> <name>`, or (Windows has no man
/// pages) `docs <FunctionName>`, a Win32 function on Microsoft Learn.
fn cites_man_page(text: &str) -> bool {
    cites_win32_docs(text) || cites_unix_man(text)
}

/// `docs CreateProcessW`: `docs`, a space, then an identifier starting with
/// an uppercase letter.
fn cites_win32_docs(text: &str) -> bool {
    text.match_indices("docs ").any(|(i, _)| {
        text.get(i.saturating_add(5)..)
            .and_then(|rest| rest.chars().next())
            .is_some_and(|c| c.is_ascii_uppercase())
    })
}

fn cites_unix_man(text: &str) -> bool {
    text.match_indices("man ").any(|(i, _)| {
        let mut rest = text.get(i.saturating_add(4)..).unwrap_or("").chars();
        rest.next().is_some_and(|c| c.is_ascii_digit())
            && rest.next() == Some(' ')
            && rest
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
    })
}

// ---------------------------------------------------------------- manifest

/// `[lints.*]` entries of a manifest as (table, key) -> value, whitespace
/// removed. `[workspace.lints.rust]` and `[lints.rust]` are the same table.
fn lint_entries(manifest: &str) -> (BTreeMap<(String, String), String>, bool) {
    let mut entries = BTreeMap::new();
    let mut table = String::new();
    let mut workspace_inherit = false;
    for raw in manifest.lines() {
        let line = strip_comment(raw).trim().to_owned();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            table = line
                .trim_matches(|c| c == '[' || c == ']')
                .trim_start_matches("workspace.")
                .replace(' ', "");
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        let key = key.trim().to_owned();
        let value: String = value.chars().filter(|c| !c.is_whitespace()).collect();
        if table == "lints" && key == "workspace" && value == "true" {
            workspace_inherit = true;
        }
        if table.starts_with("lints.") {
            entries.insert((table.clone(), key), value);
        }
    }
    (entries, workspace_inherit)
}

/// Drop a trailing `# comment` that is not inside a string.
fn strip_comment(line: &str) -> &str {
    let mut quoted = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => quoted = !quoted,
            '#' if !quoted => return line.get(..i).unwrap_or(line),
            _ => {}
        }
    }
    line
}

/// Rule 1: lint overrides in `manifest`, the manifest of the crate at
/// `dir` (repo-relative), given the workspace manifest.
pub fn lint_problems(dir: &str, manifest: &str, workspace: &str) -> Vec<String> {
    let (own, inherits) = lint_entries(manifest);
    let (ws, _) = lint_entries(workspace);
    let mut problems = Vec::new();
    let at = format!("{dir}/Cargo.toml");
    if dir != CRATE_DIR {
        if own.keys().any(|(_, k)| k == "unsafe_code") {
            problems.push(format!(
                "{at}: overrides `unsafe_code`; only {CRATE_DIR} may (CLAUDE.md rule 1)"
            ));
        }
        return problems;
    }
    if inherits {
        problems.push(format!(
            "{at}: must list the workspace lints itself (a crate cannot both inherit them \
             and override `unsafe_code`), not `workspace = true`"
        ));
    }
    let unsafe_key = ("lints.rust".to_owned(), "unsafe_code".to_owned());
    if own.get(&unsafe_key).map(String::as_str) != Some("\"allow\"") {
        problems.push(format!(
            "{at}: [lints.rust] must set unsafe_code = \"allow\""
        ));
    }
    for (key, value) in &ws {
        if *key != unsafe_key && own.get(key) != Some(value) {
            problems.push(format!(
                "{at}: lint {}.{} must equal the workspace's ({value}); only `unsafe_code` may differ",
                key.0, key.1
            ));
        }
    }
    for key in own
        .keys()
        .filter(|k| **k != unsafe_key && !ws.contains_key(*k))
    {
        problems.push(format!(
            "{at}: lint {}.{} is not a workspace lint; only `unsafe_code` may differ",
            key.0, key.1
        ));
    }
    problems
}

/// Rule 2: the crate's dependencies are `libc`, pinned exactly.
pub fn dependency_problems(
    deps: &[(String, String)],
    dev_deps: &[(String, String)],
) -> Vec<String> {
    let mut problems = Vec::new();
    for (name, req) in deps {
        if name != "libc" {
            problems.push(format!(
                "{CRATE_NAME}: dependency {name}; only `libc` is allowed"
            ));
        } else if !req.starts_with('=') {
            problems.push(format!(
                "{CRATE_NAME}: libc must be pinned to an exact version (\"=x.y.z\"), found {req:?}"
            ));
        }
    }
    for (name, _) in dev_deps {
        problems.push(format!(
            "{CRATE_NAME}: dev-dependency {name}; there may be none"
        ));
    }
    problems
}

// ------------------------------------------------------------------- audit

/// SHA-256 of the crate's source, as audited. The files hashed are every
/// regular file under `crates/clazel-sys` except hidden files and
/// directories and `target/`, in byte order of their repo-relative path.
/// For each file one line `<sha256 of the file>  <path>\n` is formed (the
/// output format of `shasum -a 256`), and the audit hash is the SHA-256 of
/// those lines together. To check by hand from the repository root:
///
/// ```sh
/// find crates/clazel-sys -type f -not -path '*/.*' -not -path '*/target/*' \
///   | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256
/// ```
pub fn source_hash(dir: &Path) -> Result<(String, Vec<String>), String> {
    let mut files = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(d) = pending.pop() {
        let entries = std::fs::read_dir(&d).map_err(|e| format!("{}: {e}", d.display()))?;
        for entry in entries {
            let path = entry.map_err(|e| format!("{}: {e}", d.display()))?.path();
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .ok_or_else(|| format!("{}: name is not UTF-8", path.display()))?;
            if name.starts_with('.') || name == "target" {
                continue;
            }
            let kind = std::fs::symlink_metadata(&path)
                .map_err(|e| format!("{}: {e}", path.display()))?
                .file_type();
            if kind.is_symlink() {
                return Err(format!(
                    "{}: symbolic links are not allowed here",
                    path.display()
                ));
            }
            if kind.is_dir() {
                pending.push(path);
            } else {
                files.push(path);
            }
        }
    }
    let mut named: Vec<String> = files
        .iter()
        .map(|p| crate::workspace::relative(p))
        .collect();
    named.sort();
    let mut manifest = String::new();
    for name in &named {
        let hash = crate::reviews::sha256(Path::new(name))?;
        manifest.push_str(&format!("{hash}  {name}\n"));
    }
    Ok((sha256_bytes(manifest.as_bytes())?, named))
}

/// SHA-256 of `data`, via the system's `sha256sum` or `shasum`.
fn sha256_bytes(data: &[u8]) -> Result<String, String> {
    if cfg!(windows) {
        // `certutil` hashes files only.
        let path = std::env::temp_dir().join(format!("clazel-xtask-{}.sha", std::process::id()));
        std::fs::write(&path, data).map_err(|e| format!("{}: {e}", path.display()))?;
        let hash = crate::reviews::sha256(&path);
        let _ = std::fs::remove_file(&path);
        return hash;
    }
    let attempts: [(&str, &[&str]); 2] = [("sha256sum", &[]), ("shasum", &["-a", "256"])];
    for (tool, args) in attempts {
        let Ok(mut child) = Command::new(tool)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
        else {
            continue;
        };
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(data).map_err(|e| format!("{tool}: {e}"))?;
        }
        let out = child
            .wait_with_output()
            .map_err(|e| format!("{tool}: {e}"))?;
        if out.status.success()
            && let Some(hash) = String::from_utf8_lossy(&out.stdout)
                .split_whitespace()
                .next()
        {
            return Ok(hash.to_ascii_lowercase());
        }
    }
    Err("cannot hash (need sha256sum or shasum)".to_owned())
}

/// One audit row.
#[derive(Debug)]
pub struct Audit {
    pub sha256: String,
    pub verdict: String,
}

const BEGIN: &str = "<!-- BEGIN AUDITS";
const END: &str = "<!-- END AUDITS -->";

/// Parse the audit table between the markers; rows are in file order, so
/// the last one is the latest.
pub fn parse_audits(text: &str) -> Result<Vec<Audit>, String> {
    let start = text
        .find(BEGIN)
        .ok_or_else(|| format!("{AUDITS}: no {BEGIN} marker"))?;
    let body = text.get(start..).unwrap_or_default();
    let end = body
        .find(END)
        .ok_or_else(|| format!("{AUDITS}: no {END} marker"))?;
    let mut rows = Vec::new();
    for line in body.get(..end).unwrap_or_default().lines().skip(1) {
        let line = line.trim();
        if !line.starts_with('|') {
            continue;
        }
        let cells: Vec<&str> = line.trim_matches('|').split('|').map(str::trim).collect();
        let [date, sha, auditor, against, verdict] = cells.as_slice() else {
            return Err(format!("{AUDITS}: expected 5 columns in: {line}"));
        };
        if *date == "Date" || date.chars().all(|c| c == '-') {
            continue;
        }
        if !(sha.len() == 64 && sha.chars().all(|c| c.is_ascii_hexdigit())) {
            return Err(format!("{AUDITS}: {date}: SHA-256 must be 64 hex digits"));
        }
        if [date, auditor, against, verdict]
            .iter()
            .any(|c| c.is_empty())
        {
            return Err(format!("{AUDITS}: {date}: every column is required"));
        }
        rows.push(Audit {
            sha256: sha.to_ascii_lowercase(),
            verdict: (*verdict).to_owned(),
        });
    }
    Ok(rows)
}

/// Rule 7: the latest audit approves exactly the current source.
pub fn audit_problems(log: &str, current: &str) -> Vec<String> {
    let rows = match parse_audits(log) {
        Ok(r) => r,
        Err(e) => return vec![e],
    };
    match rows.last() {
        None => vec![format!(
            "{AUDITS}: no audit of {CRATE_DIR}; its source has SHA-256 {current}. \
             A session other than the author's must audit it (CLAUDE.md rule 1)"
        )],
        Some(a) if a.sha256 != current => vec![format!(
            "{AUDITS}: stale audit of {CRATE_DIR}: the latest row covers {}, the source is now \
             {current}. Every change needs a new audit by a session other than the author's",
            a.sha256
        )],
        Some(a) if a.verdict != "approved" => vec![format!(
            "{AUDITS}: the latest audit of {CRATE_DIR} has verdict {:?}, not \"approved\"",
            a.verdict
        )],
        Some(_) => Vec::new(),
    }
}

// ------------------------------------------------------------------ README

const OLD_CLAIM: &str = "100% safe Rust. `unsafe` is forbidden workspace-wide.";
const NEW_CLAIM: &str = "100% safe Rust except `clazel-sys`: ";

/// The README claim says exactly what was measured: with no `unsafe`
/// anywhere, the old sentence; otherwise the new one, with the measured
/// numbers. The sentence is
/// ``100% safe Rust except `clazel-sys`: N `unsafe` blocks (M lines) that enter the OS sandbox, machine-checked and audited.``
pub fn readme_problems(readme: &str, blocks: usize, lines: usize) -> Vec<String> {
    let mut problems = Vec::new();
    let has_old = readme.contains(OLD_CLAIM);
    let new = readme
        .split_once(NEW_CLAIM)
        .map(|(_, rest)| parse_claim(rest));
    if blocks == 0 {
        if !has_old {
            problems.push(format!(
                "README.md: the workspace has no `unsafe`, so it must say \"{OLD_CLAIM}\""
            ));
        }
        if new.is_some() {
            problems.push(
                "README.md: claims `clazel-sys` `unsafe` blocks, but none exist yet; the claim \
                 changes in the commit that adds the first one"
                    .to_owned(),
            );
        }
        return problems;
    }
    if has_old {
        problems.push(format!(
            "README.md: still says \"{OLD_CLAIM}\", but {blocks} `unsafe` blocks exist"
        ));
    }
    match new {
        None => problems.push(format!(
            "README.md: must say \"{NEW_CLAIM}{blocks} `unsafe` blocks ({lines} lines) that \
             enter the OS sandbox, machine-checked and audited.\""
        )),
        Some(Some((n, m))) if n == blocks && m == lines => {}
        Some(Some((n, m))) => problems.push(format!(
            "README.md claims {n} `unsafe` blocks ({m} lines); measured {blocks} ({lines} lines)"
        )),
        Some(None) => problems.push(format!(
            "README.md: the `clazel-sys` sentence must read \"{NEW_CLAIM}N `unsafe` blocks \
             (M lines) that enter the OS sandbox, machine-checked and audited.\""
        )),
    }
    problems
}

/// Parse "N `unsafe` blocks (M lines) that enter the OS sandbox, machine-checked and audited."
fn parse_claim(rest: &str) -> Option<(usize, usize)> {
    let (n, rest) = rest.split_once(" `unsafe` blocks (")?;
    let (m, rest) = rest.split_once(" lines) ")?;
    rest.starts_with("that enter the OS sandbox, machine-checked and audited.")
        .then_some(())?;
    Some((n.parse().ok()?, m.parse().ok()?))
}

#[cfg(test)]
mod tests {
    use super::{
        audit_problems, check_source, cites_man_page, dependency_problems, lint_problems,
        readme_problems,
    };

    const WORKSPACE: &str = "[workspace.lints.rust]\nunsafe_code = \"forbid\"\nmissing_docs = \"warn\"\n\
        [workspace.lints.clippy]\npanic = \"deny\"\n";
    const SYS_MANIFEST: &str = "[lints.rust]\nunsafe_code = \"allow\"\nmissing_docs = \"warn\"\n\
        [lints.clippy]\npanic = \"deny\"\n";
    const SHA_A: &str = "83cafc50284caea07fa8762df04b00cc0af441f25cdf1631d6c30987c65af446";
    const SHA_B: &str = "7f1d2ff4c6e25d8ef7c1b0f7ae5a7b9d5dd1d4f3f2f4ad8a4d0d9e1f2a3b4c5d";

    fn violations(src: &str) -> Result<Vec<String>, String> {
        Ok(check_source(src)?
            .violations
            .into_iter()
            .map(|(line, what)| format!("{line}: {what}"))
            .collect())
    }

    fn good(call: &str) -> String {
        format!(
            "fn f() -> i32 {{\n    // SAFETY: man 2 prctl; the libc declaration matches.\n    unsafe {{ {call} }}\n}}\n"
        )
    }

    #[test]
    fn accepts_a_listed_call_with_a_safety_comment() -> Result<(), String> {
        assert_eq!(
            violations(&good("libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)"))?,
            Vec::<String>::new()
        );
        assert_eq!(
            violations(&good("libc::syscall(libc::SYS_seccomp, 1, 0, p)"))?,
            Vec::<String>::new()
        );
        let multi = "// SAFETY: man 3 sandbox_init. Pointers are valid\n\
                     // for the call.\nlet r = unsafe { sandbox_init(p, 0, e) };\n\
                     // SAFETY: man 3 sandbox_init; declared as in <sandbox.h>.\n\
                     unsafe extern \"C\" { fn sandbox_init(a: i32) -> i32; }";
        assert_eq!(violations(multi)?, Vec::<String>::new());
        Ok(())
    }

    #[test]
    fn planted_unlisted_foreign_function() -> Result<(), String> {
        let v = violations(&good("libc::open(p, 0)"))?;
        assert!(
            v.iter()
                .any(|m| m.contains("`open` is not a permitted foreign function"))
        );
        let v = violations(&good("libc::syscall(libc::SYS_execve, p)"))?;
        assert!(v.iter().any(|m| m.contains("`syscall` with")));
        let decl = "// SAFETY: man 2 open.\nunsafe extern \"C\" { fn open(p: i32) -> i32; }";
        assert!(
            violations(decl)?
                .iter()
                .any(|m| m.contains("`open` is not a permitted"))
        );
        Ok(())
    }

    #[test]
    fn planted_unsafe_without_safety_comment() -> Result<(), String> {
        let none = "fn f() {\n    unsafe { libc::prctl(1) };\n}";
        assert!(
            violations(none)?
                .iter()
                .any(|m| m.contains("without a `// SAFETY:`"))
        );
        // A blank line between the comment and the block breaks "directly above".
        let gap = "// SAFETY: man 2 prctl.\n\nunsafe { libc::prctl(1) };";
        assert!(
            violations(gap)?
                .iter()
                .any(|m| m.contains("without a `// SAFETY:`"))
        );
        // Any other comment does not do.
        let other = "// call prctl\nunsafe { libc::prctl(1) };";
        assert!(
            violations(other)?
                .iter()
                .any(|m| m.contains("without a `// SAFETY:`"))
        );
        let no_man = "// SAFETY: trust me.\nunsafe { libc::prctl(1) };";
        assert!(
            violations(no_man)?
                .iter()
                .any(|m| m.contains("does not cite a man page"))
        );
        Ok(())
    }

    #[test]
    fn one_call_per_block_and_no_other_unsafe_forms() -> Result<(), String> {
        let two = good("libc::prctl(1); libc::prctl(2)");
        assert!(violations(&two)?.iter().any(|m| m.contains("found 2")));
        let none = good("0");
        assert!(violations(&none)?.iter().any(|m| m.contains("found 0")));
        let helper = good("libc::prctl(helper(1))");
        assert!(
            violations(&helper)?
                .iter()
                .any(|m| m.contains("`helper` is not"))
        );
        let deref = good("*p");
        assert!(
            violations(&deref)?
                .iter()
                .any(|m| m.contains("dereference"))
        );
        let nested = good("unsafe { libc::prctl(1) }");
        assert!(violations(&nested)?.iter().any(|m| m.contains("nested")));
        for src in [
            "pub unsafe fn f() {}",
            "unsafe impl Send for X {}",
            "unsafe trait T {}",
        ] {
            assert!(
                violations(src)?
                    .iter()
                    .any(|m| m.contains("may only start a block"))
            );
        }
        assert!(
            violations("pub extern \"C\" fn f() {}")?
                .iter()
                .any(|m| m.contains("outside"))
        );
        Ok(())
    }

    #[test]
    fn no_pointer_arithmetic_and_every_public_function_safe() -> Result<(), String> {
        for src in [
            "fn f(p: *const u8) -> *const u8 { p.add(1) }",
            "fn f(p: *const u8) -> *const u8 { p.wrapping_offset(1) }",
            "fn f(p: *const u8) -> *const u8 { p.byte_add::<>(1) }",
        ] {
            assert!(
                violations(src)?
                    .iter()
                    .any(|m| m.contains("pointer arithmetic")),
                "{src}"
            );
        }
        let public = "// SAFETY: man 3 sandbox_init.\nunsafe extern \"C\" { pub fn sandbox_init(a: i32) -> i32; }";
        assert!(violations(public)?.iter().any(|m| m.contains("`pub`")));
        let safe_fn = "// SAFETY: man 3 sandbox_init.\nunsafe extern \"C\" { safe fn sandbox_init(a: i32) -> i32; }";
        assert!(violations(safe_fn)?.iter().any(|m| m.contains("`safe fn`")));
        assert!(
            violations("pub use libc::prctl;")?
                .iter()
                .any(|m| m.contains("export"))
        );
        assert!(violations("pub use crate::x::Y;")?.is_empty());
        assert!(
            violations("macro_rules! m { () => {} }")?
                .iter()
                .any(|m| m.contains("hide"))
        );
        assert!(
            violations("#[path = \"x.rs\"] mod x;")?
                .iter()
                .any(|m| m.contains("#[path]"))
        );
        Ok(())
    }

    #[test]
    fn man_page_citation_forms() {
        assert!(cites_man_page("SAFETY: man 2 prctl"));
        assert!(cites_man_page("see man 3 sandbox_init for it"));
        assert!(!cites_man_page("a human wrote this"));
        assert!(!cites_man_page("man page"));
    }

    #[test]
    fn planted_second_crate_overriding_unsafe_code() {
        let other = "[package]\nname = \"clazel-evil\"\n[lints.rust]\nunsafe_code = \"allow\"\n";
        let p = lint_problems("crates/clazel-evil", other, WORKSPACE);
        assert_eq!(p.len(), 1, "{p:?}");
        assert!(p.iter().all(|m| m.contains("only crates/clazel-sys may")));
        assert!(
            lint_problems(
                "crates/clazel-url",
                "[lints]\nworkspace = true\n",
                WORKSPACE
            )
            .is_empty()
        );
        // The sys crate itself: fine as listed, wrong if it loosens any other lint.
        assert!(lint_problems("crates/clazel-sys", SYS_MANIFEST, WORKSPACE).is_empty());
        let loose = SYS_MANIFEST.replace("panic = \"deny\"", "panic = \"allow\"");
        assert!(!lint_problems("crates/clazel-sys", &loose, WORKSPACE).is_empty());
        let extra = format!("{SYS_MANIFEST}dead_code = \"allow\"\n");
        assert!(!lint_problems("crates/clazel-sys", &extra, WORKSPACE).is_empty());
        let inherit = "[lints]\nworkspace = true\n";
        assert!(!lint_problems("crates/clazel-sys", inherit, WORKSPACE).is_empty());
        let forbid = SYS_MANIFEST.replace("\"allow\"", "\"warn\"");
        assert!(!lint_problems("crates/clazel-sys", &forbid, WORKSPACE).is_empty());
    }

    #[test]
    fn dependencies_are_libc_pinned() {
        let libc = |r: &str| vec![("libc".to_owned(), r.to_owned())];
        assert!(dependency_problems(&libc("=0.2.190"), &[]).is_empty());
        assert_eq!(dependency_problems(&libc("0.2"), &[]).len(), 1);
        let other = vec![("cc".to_owned(), "=1.0.0".to_owned())];
        assert_eq!(dependency_problems(&other, &[]).len(), 1);
        assert_eq!(dependency_problems(&[], &other).len(), 1);
    }

    fn log(rows: &[(&str, &str)]) -> String {
        let mut s = "<!-- BEGIN AUDITS -->\n| Date | SHA-256 | Auditor | Audited against | Verdict |\n|---|---|---|---|---|\n".to_owned();
        for (sha, verdict) in rows {
            s.push_str(&format!(
                "| 2026-10-22 | {sha} | session | man pages | {verdict} |\n"
            ));
        }
        s.push_str("<!-- END AUDITS -->\n");
        s
    }

    #[test]
    fn planted_stale_audit_hash() {
        assert!(audit_problems(&log(&[(SHA_A, "approved")]), SHA_A).is_empty());
        let stale = audit_problems(&log(&[(SHA_A, "approved")]), SHA_B);
        assert!(stale.iter().any(|m| m.contains("stale audit")), "{stale:?}");
        // Only the latest row counts: an old match does not save a new change.
        let old = audit_problems(&log(&[(SHA_A, "approved"), (SHA_B, "approved")]), SHA_A);
        assert!(old.iter().any(|m| m.contains("stale audit")));
        assert!(
            audit_problems(&log(&[]), SHA_A)
                .iter()
                .any(|m| m.contains("no audit"))
        );
        let rejected = audit_problems(&log(&[(SHA_A, "rejected")]), SHA_A);
        assert!(rejected.iter().any(|m| m.contains("not \"approved\"")));
        assert!(!audit_problems("no markers", SHA_A).is_empty());
        assert!(!audit_problems(&log(&[("abc", "approved")]), SHA_A).is_empty());
    }

    #[test]
    fn planted_wrong_readme_count() {
        let claim = |n: usize, m: usize| {
            format!(
                "- **Memory safe:** 100% safe Rust except `clazel-sys`: {n} `unsafe` blocks \
                 ({m} lines) that enter the OS sandbox, machine-checked and audited.\n"
            )
        };
        assert!(readme_problems(&claim(7, 31), 7, 31).is_empty());
        let wrong_n = readme_problems(&claim(6, 31), 7, 31);
        assert!(
            wrong_n.iter().any(|m| m.contains("claims 6")),
            "{wrong_n:?}"
        );
        assert!(!readme_problems(&claim(7, 30), 7, 31).is_empty());
        // The old sentence is wrong once unsafe exists, and the new one before.
        let old = "- 100% safe Rust. `unsafe` is forbidden workspace-wide.\n";
        assert!(!readme_problems(old, 7, 31).is_empty());
        assert!(readme_problems(old, 0, 0).is_empty());
        assert!(!readme_problems(&claim(0, 0), 0, 0).is_empty());
        assert!(!readme_problems("nothing", 7, 31).is_empty());
        let garbled = "100% safe Rust except `clazel-sys`: many `unsafe` blocks.";
        assert!(!readme_problems(garbled, 7, 31).is_empty());
    }
}
