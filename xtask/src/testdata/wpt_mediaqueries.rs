//! WPT `css/mediaqueries/` (phase-5.md item 5.8): three tables.
//!
//! - **`test_media_queries.html`**: each call of its six helpers (`should_apply`,
//!   `should_not_apply`, `query_should_be_parseable`, `query_should_not_be_parseable`,
//!   `expression_should_be_known`, `expression_should_be_unknown`) written as a statement of
//!   `run()`'s body, outside any loop, condition or nested function, with one string literal
//!   argument that substitutes nothing (the page `eval`s `${…}` inside its strings), is a
//!   case, with the size of the page's iframe at that point. The size starts at an iframe's
//!   default, 300 by 150 (CSS 2.1 §10.3.2 and §10.6.2), and follows the assignments to
//!   `iframe_style.width` and `.height` in `run()`'s body whose value is a string literal or
//!   a `var` holding an integer literal plus `"px"`; after any other assignment to them the
//!   size is unknown and the calls that depend on it are not run. Every other use of a
//!   helper is listed, by line, as not run. This page is read call by call, not as a whole
//!   (as `wpt_css_values.rs` reads its pages), because its calls are independent tests and
//!   most of them are in loops over computed strings: reading only the whole page would run
//!   none of it.
//! - **`match-media-parsing.html`**: each top-level `test_parsing(query, expected?)` call
//!   with literal arguments; the calls inside `test_resolution_parsing()` are not run.
//! - **The reftests**: every `@media` rule of each page's `style` elements, with whether it
//!   must apply in WPT's 800 by 600 viewport. Each page's reference is a green square (or a
//!   green page), and on each page vendored every `@media` rule's block paints either green
//!   (a rule the page needs to apply) or red (one it needs not to apply); the converter
//!   fails if a block names both colours or neither. In XHTML pages (`.xht`) the style
//!   text's CDATA markers are removed, as an XML parser removes them.

use std::fmt::Write as _;
use std::path::Path;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "match-media-parsing.html",
    "media-queries-001.xht",
    "media-queries-002.xht",
    "media-queries-003.xht",
    "min-width-001.xht",
    "mq-deprecated-001.html",
    "mq-invalid-media-type-001.html",
    "mq-invalid-media-type-002.html",
    "mq-invalid-media-type-003.html",
    "mq-invalid-media-type-004.html",
    "mq-invalid-media-type-005.html",
    "mq-invalid-media-type-006.html",
    "mq-invalid-media-type-layer-001.html",
    "mq-invalid-media-type-layer-002.html",
    "mq-negative-range-001.html",
    "mq-negative-range-002.html",
    "mq-range-001.html",
    "negation-001.html",
    "negation-002.html",
    "relative-units-001.html",
    "relative-units-002.html",
    "relative-units-003.html",
    "relative-units-004.html",
    "test_media_queries.html",
];

/// The helpers of `test_media_queries.html`.
const HELPERS: &[&str] = &[
    "should_apply",
    "should_not_apply",
    "query_should_be_parseable",
    "query_should_not_be_parseable",
    "expression_should_be_known",
    "expression_should_be_unknown",
];

/// One token of a script.
#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Word(String),
    /// A string literal's value, or `None` if it holds an escape this does not read.
    Str(Option<String>),
    /// A template literal (never read as a literal here).
    Template,
    /// A regular expression literal.
    Regex,
    Num(String),
    Punct(char),
}

fn is_word_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '$'
}

/// The tokens of `src`, each with its 1-based line.
fn lex(src: &str) -> Result<Vec<(Tok, usize)>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut out: Vec<(Tok, usize)> = Vec::new();
    let mut i = 0usize;
    let mut line = 1usize;
    let at = |i: usize| chars.get(i).copied();
    while let Some(c) = at(i) {
        let next = at(i.saturating_add(1));
        if c == '\n' {
            line = line.saturating_add(1);
            i = i.saturating_add(1);
        } else if c.is_whitespace() {
            i = i.saturating_add(1);
        } else if c == '/' && next == Some('/') {
            while at(i).is_some_and(|c| c != '\n') {
                i = i.saturating_add(1);
            }
        } else if c == '/' && next == Some('*') {
            i = i.saturating_add(2);
            while at(i).is_some() && !(at(i) == Some('*') && at(i.saturating_add(1)) == Some('/')) {
                if at(i) == Some('\n') {
                    line = line.saturating_add(1);
                }
                i = i.saturating_add(1);
            }
            i = i.saturating_add(2);
        } else if c == '/'
            && matches!(
                out.last(),
                None | Some((
                    Tok::Punct(
                        '(' | ',' | '=' | ':' | '[' | '!' | '&' | '|' | '?' | '{' | '}' | ';'
                    ),
                    _
                ))
            )
        {
            // A regular expression literal.
            i = i.saturating_add(1);
            loop {
                match at(i) {
                    None | Some('\n') => return Err(format!("line {line}: unterminated regex")),
                    Some('\\') => i = i.saturating_add(2),
                    Some('/') => break,
                    Some(_) => i = i.saturating_add(1),
                }
            }
            i = i.saturating_add(1);
            while at(i).is_some_and(is_word_char) {
                i = i.saturating_add(1);
            }
            out.push((Tok::Regex, line));
        } else if c == '"' || c == '\'' {
            let start_line = line;
            i = i.saturating_add(1);
            let mut s = Some(String::new());
            loop {
                match at(i) {
                    None | Some('\n') => {
                        return Err(format!("line {start_line}: unterminated string"));
                    }
                    Some(d) if d == c => break,
                    Some('\\') => {
                        let e = match at(i.saturating_add(1)) {
                            Some('n') => Some('\n'),
                            Some('r') => Some('\r'),
                            Some('t') => Some('\t'),
                            Some(e @ ('\\' | '\'' | '"')) => Some(e),
                            _ => None,
                        };
                        match (e, s.as_mut()) {
                            (Some(e), Some(s)) => s.push(e),
                            _ => s = None,
                        }
                        i = i.saturating_add(2);
                    }
                    Some(d) => {
                        if let Some(s) = s.as_mut() {
                            s.push(d);
                        }
                        i = i.saturating_add(1);
                    }
                }
            }
            i = i.saturating_add(1);
            out.push((Tok::Str(s), start_line));
        } else if c == '`' {
            // A template literal: skip it, with any `${ … }` (and the strings and templates
            // inside), as one token.
            let start_line = line;
            i = i.saturating_add(1);
            // Brace depth of each open `${`, innermost last; empty while in template text.
            let mut stack: Vec<usize> = Vec::new();
            let mut in_template = true;
            loop {
                let Some(d) = at(i) else {
                    return Err(format!("line {start_line}: unterminated template"));
                };
                if d == '\n' {
                    line = line.saturating_add(1);
                }
                if in_template {
                    match d {
                        '\\' => i = i.saturating_add(1),
                        '`' if stack.is_empty() => break,
                        '`' => in_template = false,
                        '$' if at(i.saturating_add(1)) == Some('{') => {
                            stack.push(0);
                            in_template = false;
                            i = i.saturating_add(1);
                        }
                        _ => {}
                    }
                } else {
                    match d {
                        '{' => {
                            if let Some(top) = stack.last_mut() {
                                *top = top.saturating_add(1);
                            }
                        }
                        '}' => match stack.last_mut() {
                            Some(0) => {
                                stack.pop();
                                in_template = true;
                            }
                            Some(top) => *top = top.saturating_sub(1),
                            None => {}
                        },
                        '`' => in_template = true,
                        q @ ('"' | '\'') => {
                            i = i.saturating_add(1);
                            while at(i).is_some_and(|e| e != q) {
                                if at(i) == Some('\\') {
                                    i = i.saturating_add(1);
                                }
                                i = i.saturating_add(1);
                            }
                        }
                        _ => {}
                    }
                }
                i = i.saturating_add(1);
            }
            i = i.saturating_add(1);
            out.push((Tok::Template, start_line));
        } else if c.is_ascii_digit() {
            let mut s = String::new();
            while let Some(d) = at(i).filter(|d| d.is_ascii_alphanumeric() || *d == '.') {
                s.push(d);
                i = i.saturating_add(1);
            }
            out.push((Tok::Num(s), line));
        } else if is_word_char(c) {
            let mut s = String::new();
            while let Some(d) = at(i).filter(|d| is_word_char(*d)) {
                s.push(d);
                i = i.saturating_add(1);
            }
            out.push((Tok::Word(s), line));
        } else {
            out.push((Tok::Punct(c), line));
            i = i.saturating_add(1);
        }
    }
    Ok(out)
}

/// The one inline script of a page (the one without `src`).
fn inline_script(text: &str) -> Result<(&str, usize), String> {
    let mut found = None;
    let mut rest = text;
    let mut offset = 0usize;
    while let Some(start) = rest.find("<script") {
        let after = rest.get(start..).unwrap_or_default();
        let open_end = after.find('>').ok_or("unterminated <script>")?;
        let open = after.get(..open_end).unwrap_or_default();
        let body_start = start.saturating_add(open_end).saturating_add(1);
        let body_len = rest
            .get(body_start..)
            .and_then(|b| b.find("</script>"))
            .ok_or("no </script>")?;
        if !open.contains("src=") {
            if found.is_some() {
                return Err("more than one inline script".to_owned());
            }
            let abs = offset.saturating_add(body_start);
            let line = text.get(..abs).unwrap_or_default().matches('\n').count();
            found = Some((
                rest.get(body_start..body_start.saturating_add(body_len))
                    .unwrap_or_default(),
                line,
            ));
        }
        let skip = body_start.saturating_add(body_len);
        offset = offset.saturating_add(skip);
        rest = rest.get(skip..).unwrap_or_default();
    }
    found.ok_or_else(|| "no inline script".to_owned())
}

/// The index after the bracket matching the one at `open`.
fn matching(toks: &[(Tok, usize)], open: usize) -> Result<usize, String> {
    let mut depth = 0usize;
    for (k, (t, _)) in toks.iter().enumerate().skip(open) {
        match t {
            Tok::Punct('(' | '[' | '{') => depth = depth.saturating_add(1),
            Tok::Punct(')' | ']' | '}') => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Ok(k.saturating_add(1));
                }
            }
            _ => {}
        }
    }
    Err("unbalanced brackets".to_owned())
}

/// A helper call or a use of a helper, at token `k` of `body`, which is at statement level
/// if `statement` says so: the literal argument, or why it is not read.
fn literal_call(
    body: &[(Tok, usize)],
    k: usize,
    statement: bool,
    args: usize,
) -> Result<Vec<String>, String> {
    if !statement {
        return Err("inside a loop, a condition, a function or an expression".to_owned());
    }
    if body.get(k.saturating_add(1)).map(|t| &t.0) != Some(&Tok::Punct('(')) {
        return Err("not called directly".to_owned());
    }
    let mut out = Vec::new();
    let mut j = k.saturating_add(2);
    loop {
        match body.get(j).map(|t| &t.0) {
            Some(Tok::Str(Some(s))) if !s.contains("${") => out.push(s.clone()),
            Some(Tok::Str(Some(_))) => return Err("its string substitutes a value".to_owned()),
            _ => return Err("an argument that is not a string literal".to_owned()),
        }
        j = j.saturating_add(1);
        match body.get(j).map(|t| &t.0) {
            Some(Tok::Punct(')')) => break,
            Some(Tok::Punct(',')) => j = j.saturating_add(1),
            _ => return Err("an argument that is not a string literal".to_owned()),
        }
    }
    if out.len() > args || out.is_empty() {
        return Err(format!("{} arguments", out.len()));
    }
    Ok(out)
}

/// Statement-level walking of a block's tokens: true at `k` if the token starts a
/// statement of the block (depth 0) that is not the body of a loop or a condition.
struct Walker {
    depth: usize,
    /// The word before each open `(`, innermost last.
    parens: Vec<Option<String>>,
    /// True if the last `)` at depth 0 closed a control statement's head.
    after_control: bool,
}

const CONTROL: &[&str] = &["if", "for", "while", "with", "switch", "catch"];

impl Walker {
    fn new() -> Walker {
        Walker {
            depth: 0,
            parens: Vec::new(),
            after_control: false,
        }
    }

    /// Whether token `k` starts a statement at depth 0, given the previous token.
    fn starts_statement(&self, body: &[(Tok, usize)], k: usize) -> bool {
        if self.depth != 0 {
            return false;
        }
        match k.checked_sub(1).and_then(|p| body.get(p)).map(|t| &t.0) {
            None | Some(Tok::Punct(';' | '}' | '{')) => true,
            // A statement after one with no semicolon, unless it is a control statement's
            // body.
            Some(Tok::Punct(')')) => !self.after_control,
            Some(Tok::Word(w)) => !matches!(w.as_str(), "else" | "do" | "return" | "function"),
            Some(Tok::Str(_) | Tok::Num(_) | Tok::Template | Tok::Regex) => true,
            _ => false,
        }
    }

    /// Account for token `k`.
    fn step(&mut self, body: &[(Tok, usize)], k: usize) {
        let prev_word = k
            .checked_sub(1)
            .and_then(|p| body.get(p))
            .and_then(|t| match &t.0 {
                Tok::Word(w) => Some(w.clone()),
                _ => None,
            });
        match body.get(k).map(|t| &t.0) {
            Some(Tok::Punct('(')) => {
                self.parens.push(prev_word);
                self.depth = self.depth.saturating_add(1);
            }
            Some(Tok::Punct(')')) => {
                let opener = self.parens.pop().flatten();
                self.depth = self.depth.saturating_sub(1);
                if self.depth == 0 {
                    self.after_control = opener.is_some_and(|w| CONTROL.contains(&w.as_str()));
                }
            }
            Some(Tok::Punct('[' | '{')) => self.depth = self.depth.saturating_add(1),
            Some(Tok::Punct(']' | '}')) => self.depth = self.depth.saturating_sub(1),
            _ => {}
        }
    }
}

/// A size assignment's value in px: `"Npx"`, `"0"`, or `NAME + "px"` with an integer `var`.
fn size_value(body: &[(Tok, usize)], k: usize, vars: &[(String, u32)]) -> Option<(u32, usize)> {
    let px = |s: &str| -> Option<u32> {
        if s == "0" {
            return Some(0);
        }
        s.strip_suffix("px")?.parse().ok()
    };
    match (
        body.get(k).map(|t| &t.0),
        body.get(k.saturating_add(1)).map(|t| &t.0),
    ) {
        (Some(Tok::Str(Some(s))), Some(Tok::Punct(';'))) => Some((px(s)?, k.saturating_add(2))),
        (Some(Tok::Word(name)), Some(Tok::Punct('+'))) => {
            let v = vars.iter().find(|(n, _)| n == name)?.1;
            match (
                body.get(k.saturating_add(2)).map(|t| &t.0),
                body.get(k.saturating_add(3)).map(|t| &t.0),
            ) {
                (Some(Tok::Str(Some(s))), Some(Tok::Punct(';'))) if s == "px" => {
                    Some((v, k.saturating_add(4)))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The cases of `test_media_queries.html`, as table rows, and its uses not run.
fn media_queries_page(text: &str, cases: &mut String, not_run: &mut String) -> Result<(), String> {
    let (script, first_line) = inline_script(text)?;
    let toks: Vec<(Tok, usize)> = lex(script)?
        .into_iter()
        .map(|(t, l)| (t, l.saturating_add(first_line)))
        .collect();
    // `function run() {`
    let run = toks
        .windows(5)
        .position(|w| {
            matches!(
                w,
                [(Tok::Word(f), _), (Tok::Word(r), _), (Tok::Punct('('), _), (Tok::Punct(')'), _), (Tok::Punct('{'), _)]
                    if f == "function" && r == "run"
            )
        })
        .ok_or("no function run()")?;
    let open = run.saturating_add(4);
    let close = matching(&toks, open)?;
    let body = toks
        .get(open.saturating_add(1)..close.saturating_sub(1))
        .ok_or("empty run()")?;
    let mut vars: Vec<(String, u32)> = Vec::new();
    let mut size: Option<(u32, u32)> = Some((300, 150));
    let mut w = Walker::new();
    let mut k = 0usize;
    while k < body.len() {
        let statement = w.starts_statement(body, k);
        let line = body.get(k).map_or(0, |t| t.1);
        match body.get(k).map(|t| &t.0) {
            Some(Tok::Word(v)) if v == "var" && statement => {
                if let (
                    Some(Tok::Word(name)),
                    Some(Tok::Punct('=')),
                    Some(Tok::Num(n)),
                    Some(Tok::Punct(';')),
                ) = (
                    body.get(k.saturating_add(1)).map(|t| &t.0),
                    body.get(k.saturating_add(2)).map(|t| &t.0),
                    body.get(k.saturating_add(3)).map(|t| &t.0),
                    body.get(k.saturating_add(4)).map(|t| &t.0),
                ) && let Ok(n) = n.parse::<u32>()
                {
                    vars.retain(|(m, _)| m != name);
                    vars.push((name.clone(), n));
                }
            }
            Some(Tok::Word(v)) if v == "iframe_style" => {
                let field = match (
                    body.get(k.saturating_add(1)).map(|t| &t.0),
                    body.get(k.saturating_add(2)).map(|t| &t.0),
                    body.get(k.saturating_add(3)).map(|t| &t.0),
                ) {
                    (Some(Tok::Punct('.')), Some(Tok::Word(f)), Some(Tok::Punct('=')))
                        if f == "width" || f == "height" =>
                    {
                        Some(f.clone())
                    }
                    _ => None,
                };
                if let Some(f) = field {
                    let value = statement
                        .then(|| size_value(body, k.saturating_add(4), &vars))
                        .flatten();
                    size = match (value, size) {
                        (Some((v, _)), Some((_, h))) if f == "width" => Some((v, h)),
                        (Some((v, _)), Some((wd, _))) => Some((wd, v)),
                        _ => None,
                    };
                }
            }
            Some(Tok::Word(h)) if HELPERS.contains(&h.as_str()) => {
                let definition = k
                    .checked_sub(1)
                    .and_then(|p| body.get(p))
                    .is_some_and(|t| t.0 == Tok::Word("function".to_owned()));
                if !definition {
                    let sized = !h.starts_with("query_");
                    match literal_call(body, k, statement, 1) {
                        Ok(args) => match (args.first(), size) {
                            (Some(a), Some((width, height))) => writeln!(
                                cases,
                                "    Case {{ line: {line}, helper: {h:?}, input: {a:?}, width: {width}, height: {height} }},"
                            )
                            .map_err(|e| e.to_string())?,
                            (Some(a), None) if !sized => writeln!(
                                cases,
                                "    Case {{ line: {line}, helper: {h:?}, input: {a:?}, width: 0, height: 0 }},"
                            )
                            .map_err(|e| e.to_string())?,
                            _ => writeln!(not_run, "    ({line}, {h:?}, \"the iframe's size is not known here\"),")
                                .map_err(|e| e.to_string())?,
                        },
                        Err(why) => {
                            writeln!(not_run, "    ({line}, {h:?}, {why:?}),").map_err(|e| e.to_string())?;
                        }
                    }
                }
            }
            _ => {}
        }
        w.step(body, k);
        k = k.saturating_add(1);
    }
    Ok(())
}

/// The cases of `match-media-parsing.html`.
fn parsing_page(text: &str, cases: &mut String, not_run: &mut String) -> Result<(), String> {
    let (script, first_line) = inline_script(text)?;
    let toks: Vec<(Tok, usize)> = lex(script)?
        .into_iter()
        .map(|(t, l)| (t, l.saturating_add(first_line)))
        .collect();
    let mut w = Walker::new();
    for k in 0..toks.len() {
        let statement = w.starts_statement(&toks, k);
        if let Some((Tok::Word(h), line)) = toks.get(k)
            && h == "test_parsing"
        {
            let definition = k
                .checked_sub(1)
                .and_then(|p| toks.get(p))
                .is_some_and(|t| t.0 == Tok::Word("function".to_owned()));
            if !definition {
                match literal_call(&toks, k, statement, 2) {
                    Ok(args) => {
                        let query = args.first().cloned().unwrap_or_default();
                        let expected = args.get(1).cloned().unwrap_or_else(|| query.clone());
                        writeln!(cases, "    Parsing {{ line: {line}, query: {query:?}, expected: {expected:?} }},")
                            .map_err(|e| e.to_string())?;
                    }
                    Err(why) => writeln!(not_run, "    ({line}, \"test_parsing\", {why:?}),")
                        .map_err(|e| e.to_string())?,
                }
            }
        }
        w.step(&toks, k);
    }
    Ok(())
}

/// The text of each `style` element of a page, and the line it starts on.
fn style_texts(text: &str, xml: bool) -> Result<Vec<(String, usize)>, String> {
    let mut out = Vec::new();
    let mut offset = 0usize;
    while let Some(start) = text.get(offset..).and_then(|r| r.find("<style")) {
        let start = offset.saturating_add(start);
        let open_end = text
            .get(start..)
            .and_then(|r| r.find('>'))
            .ok_or("unterminated <style>")?;
        let body = start.saturating_add(open_end).saturating_add(1);
        let len = text
            .get(body..)
            .and_then(|r| r.find("</style>"))
            .ok_or("no </style>")?;
        let mut css = text
            .get(body..body.saturating_add(len))
            .unwrap_or_default()
            .to_owned();
        if xml {
            css = css.replace("<![CDATA[", "").replace("]]>", "");
        }
        let line = text
            .get(..body)
            .unwrap_or_default()
            .matches('\n')
            .count()
            .saturating_add(1);
        out.push((css, line));
        offset = body.saturating_add(len);
    }
    Ok(out)
}

/// The top-level `@media` rules of a style sheet's text, in order: the line of each (counted
/// from `first_line`) and whether its block paints green (true) or red (false).
fn media_rules(css: &str, first_line: usize) -> Result<Vec<(usize, bool)>, String> {
    let chars: Vec<char> = css.chars().collect();
    let at = |i: usize| chars.get(i).copied();
    let mut out = Vec::new();
    let mut i = 0usize;
    let mut line = first_line;
    let mut depth = 0usize;
    // The open `@media` rule: its line, the depth of its block, and its block's text.
    let mut current: Option<(usize, usize, String)> = None;
    while let Some(c) = at(i) {
        if c == '/' && at(i.saturating_add(1)) == Some('*') {
            i = i.saturating_add(2);
            while at(i).is_some() && !(at(i) == Some('*') && at(i.saturating_add(1)) == Some('/')) {
                if at(i) == Some('\n') {
                    line = line.saturating_add(1);
                }
                i = i.saturating_add(1);
            }
            i = i.saturating_add(2);
            continue;
        }
        if c == '\n' {
            line = line.saturating_add(1);
        }
        let word: String = chars
            .get(i..i.saturating_add(6))
            .unwrap_or_default()
            .iter()
            .collect();
        if c == '@' && word.eq_ignore_ascii_case("@media") {
            if current.is_some() {
                return Err(format!("line {line}: @media inside @media"));
            }
            if depth == 0 {
                current = Some((line, 1, String::new()));
            }
        }
        match c {
            '{' => depth = depth.saturating_add(1),
            '}' => {
                depth = depth.saturating_sub(1);
                if let Some((l, d, block)) = &current
                    && depth < *d
                {
                    let lower = block.to_ascii_lowercase();
                    let has = |w: &str| {
                        lower
                            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '-')
                            .any(|t| t == w)
                    };
                    let applies = match (has("green"), has("red")) {
                        (true, false) => true,
                        (false, true) => false,
                        _ => {
                            return Err(format!(
                                "line {l}: an @media block with both colours or neither"
                            ));
                        }
                    };
                    out.push((*l, applies));
                    current = None;
                }
            }
            _ => {}
        }
        if let Some((_, _, block)) = current.as_mut()
            && depth >= 1
        {
            block.push(c);
        }
        i = i.saturating_add(1);
    }
    if current.is_some() {
        return Err("unterminated @media".to_owned());
    }
    Ok(out)
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let read = |f: &str| std::fs::read_to_string(dir.join(f)).map_err(|e| format!("{f}: {e}"));
    let mut eval = String::new();
    let mut eval_not_run = String::new();
    media_queries_page(
        &read("test_media_queries.html")?,
        &mut eval,
        &mut eval_not_run,
    )
    .map_err(|e| format!("test_media_queries.html: {e}"))?;
    let mut parsing = String::new();
    let mut parsing_not_run = String::new();
    parsing_page(
        &read("match-media-parsing.html")?,
        &mut parsing,
        &mut parsing_not_run,
    )
    .map_err(|e| format!("match-media-parsing.html: {e}"))?;
    let mut pages = String::new();
    for file in FILES {
        if *file == "test_media_queries.html" || *file == "match-media-parsing.html" {
            continue;
        }
        let text = read(file)?;
        let styles =
            style_texts(&text, file.ends_with(".xht")).map_err(|e| format!("{file}: {e}"))?;
        let mut sheets = Vec::new();
        let mut rules = Vec::new();
        for (css, line) in &styles {
            sheets.push(format!("{css:?}"));
            for (l, applies) in media_rules(css, *line).map_err(|e| format!("{file}: {e}"))? {
                rules.push(format!("({l}, {applies})"));
            }
        }
        if rules.is_empty() {
            return Err(format!("{file}: no @media rule"));
        }
        writeln!(
            pages,
            "    Page {{ file: {file:?}, sheets: &[{}], media: &[{}] }},",
            sheets.join(", "),
            rules.join(", ")
        )
        .map_err(|e| e.to_string())?;
    }
    Ok(format!(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-mediaqueries/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_mediaqueries.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-mediaqueries/SOURCE.md.\n\
         \n\
         // test_media_queries.html: the helper calls read, with the iframe's size.\n\
         const EVAL: &[Case] = &[\n{eval}];\n\
         \n\
         // test_media_queries.html: the helper uses not run: (line, helper, why).\n\
         const EVAL_NOT_RUN: &[(usize, &str, &str)] = &[\n{eval_not_run}];\n\
         \n\
         // match-media-parsing.html: the test_parsing calls read.\n\
         const PARSING: &[Parsing] = &[\n{parsing}];\n\
         \n\
         // match-media-parsing.html: the calls not run: (line, helper, why).\n\
         const PARSING_NOT_RUN: &[(usize, &str, &str)] = &[\n{parsing_not_run}];\n\
         \n\
         // The reftests: each page's style sheets, and each @media rule's line and whether\n\
         // it must apply.\n\
         const PAGES: &[Page] = &[\n{pages}];\n"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn script(body: &str) -> String {
        format!("<script src=a></script>\n<script>\nfunction run() {{\n{body}\n}}\n</script>\n")
    }

    fn run(body: &str) -> Result<(String, String), String> {
        let mut cases = String::new();
        let mut not_run = String::new();
        media_queries_page(&script(body), &mut cases, &mut not_run)?;
        Ok((cases, not_run))
    }

    #[test]
    fn reads_statement_level_literal_calls() -> Result<(), String> {
        let (cases, not_run) = run(
            "function should_apply(q) { test_predicate(q, query_applies, \"x\"); }\n\
             should_apply(\"(width)\");\n\
             query_should_be_parseable('(a)')\n\
             var w = 117;\n\
             iframe_style.width = w + \"px\";\n\
             iframe_style.height = '0';\n\
             should_not_apply(\"(height)\");",
        )?;
        assert_eq!(cases.lines().count(), 3, "{cases}");
        assert!(cases.contains("width: 300, height: 150"));
        assert!(cases.contains("input: \"(height)\", width: 117, height: 0"));
        assert!(not_run.is_empty(), "{not_run}");
        Ok(())
    }

    #[test]
    fn everything_else_is_not_run() -> Result<(), String> {
        let (cases, not_run) = run("for (i in f) { should_apply(\"a\"); }\n\
             for (i in f) should_apply(\"b\");\n\
             if (x) should_apply(\"c\"); else should_apply(\"d\");\n\
             should_apply(\"(w: ${v}px)\");\n\
             should_apply(\"a\" + b);\n\
             (c ? should_apply : should_not_apply)(\"e\");\n\
             iframe_style.width = compute();\n\
             should_apply(\"f\");\n\
             query_should_be_parseable(\"g\");")?;
        assert_eq!(cases.lines().count(), 1, "{cases}");
        assert!(cases.contains("\"g\""));
        assert_eq!(not_run.lines().count(), 9, "{not_run}");
        Ok(())
    }

    #[test]
    fn media_rules_by_colour() -> Result<(), String> {
        let css = "div { color: red }\n@media all { /* not green */ div { background: red } }\n@MEDIA x {\n a { color: GREEN } }";
        assert_eq!(media_rules(css, 1)?, vec![(2, false), (3, true)]);
        assert!(media_rules("@media a { b { color: red; background: green } }", 1).is_err());
        Ok(())
    }
}
