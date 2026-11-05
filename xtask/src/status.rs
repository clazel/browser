//! The status images: a scoreboard that README.md shows and links to
//! docs/STATUS.md, and the detail image at the top of docs/STATUS.md, which
//! places every crate in the component that runs it.
//!
//! Both are drawn from the rows of the status table the same run wrote, so
//! they show exactly what it measured. Nothing in them is typed by hand but
//! where each crate runs ([`PLACES`]) and the wording around the numbers.
//! Tiers are named by what they guarantee (docs/VERIFICATION.md, "Tiers").
//!
//! GitHub shows an SVG in Markdown as an image: no script, no hover and no
//! links inside it, so everything is drawn as plain shapes and text. Colours
//! follow the viewer's `prefers-color-scheme`.

use std::path::Path;

use crate::report::Rows;
use crate::workspace;

/// The scoreboard README.md shows.
pub const SCOREBOARD: &str = "docs/status.svg";
/// The per-component image at the top of docs/STATUS.md.
pub const DETAIL: &str = "docs/status-detail.svg";

/// Where a crate runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Place {
    /// The kernel's state and its decisions.
    Kernel,
    /// The protocol parsers and checks the kernel drives.
    Network,
    /// Code that moves bytes and calls the kernel, deciding nothing.
    Shell,
    /// The sandboxed renderer process.
    Renderer,
    /// Linked into both processes.
    Primitive,
    /// Entering the OS sandbox.
    Os,
}

/// Where each crate runs, read from the crates' dependencies. Within a
/// component this is the order the detail image draws them in. A workspace
/// crate missing here fails `cargo xtask check` until it is placed.
const PLACES: &[(&str, Place)] = &[
    ("clazel-kernel", Place::Kernel),
    ("clazel-fetch", Place::Kernel),
    ("clazel-cookie", Place::Kernel),
    ("clazel-store", Place::Kernel),
    ("clazel-origin", Place::Kernel),
    ("clazel-psl", Place::Kernel),
    ("clazel-http", Place::Network),
    ("clazel-dns", Place::Network),
    ("clazel-tls", Place::Network),
    ("clazel-x509", Place::Network),
    ("clazel-der", Place::Network),
    ("clazel-pkcs1", Place::Network),
    ("clazel-p384", Place::Network),
    ("clazel-crypto", Place::Network),
    ("clazel-net", Place::Shell),
    ("clazel-store-shell", Place::Shell),
    ("clazel", Place::Shell),
    ("clazel-renderer", Place::Renderer),
    ("clazel-html", Place::Renderer),
    ("clazel-treebuilder", Place::Renderer),
    ("clazel-dom", Place::Renderer),
    ("clazel-text", Place::Renderer),
    ("clazel-encoding", Place::Primitive),
    ("clazel-url", Place::Primitive),
    ("clazel-idna", Place::Primitive),
    ("clazel-percent", Place::Primitive),
    ("clazel-base64", Place::Primitive),
    ("clazel-mime", Place::Primitive),
    ("clazel-ipc", Place::Primitive),
    ("clazel-sandbox", Place::Os),
    ("clazel-sys", Place::Os),
];

/// Workspace members that are not part of the browser, so not drawn.
const NOT_DRAWN: &[&str] = &["xtask"];

/// The scoreboard's rows: one per component, the shells sharing the OS's.
const SCOREBOARD_ROWS: &[(&str, &[Place])] = &[
    ("Kernel", &[Place::Kernel]),
    ("Network", &[Place::Network]),
    ("Renderer", &[Place::Renderer]),
    ("Primitives", &[Place::Primitive]),
    ("Shells and OS", &[Place::Shell, Place::Os]),
];

/// Each tier's name, by what it guarantees, and the short form used after
/// an arrow to a crate's target tier.
const TIER: [&str; 3] = ["Memory safe", "Panic-free", "Proven correct"];
const TIER_SHORT: [&str; 3] = ["safe", "panic-free", "correct"];

/// Every workspace crate that is neither placed nor exempt, and every placed
/// name that is no workspace crate.
pub fn placement_problems(names: &[&str]) -> Vec<String> {
    let mut out: Vec<String> = names
        .iter()
        .filter(|n| !NOT_DRAWN.contains(n) && !PLACES.iter().any(|(p, _)| p == *n))
        .map(|n| {
            format!("{n}: not placed in a component for the status images (PLACES in xtask/src/status.rs)")
        })
        .collect();
    out.extend(
        PLACES
            .iter()
            .filter(|(p, _)| !names.contains(p))
            .map(|(p, _)| {
                format!("xtask/src/status.rs: PLACES names {p}, which is no workspace crate")
            }),
    );
    out
}

/// The first sentence of an `axioms.rs`'s module documentation, for the
/// detail image's note on axioms. `None` if the crate has no such file or
/// it has no `//!` comment.
pub fn axiom_summary(dir: &Path) -> Option<String> {
    let files = workspace::rust_files(dir).ok()?;
    let file = files
        .iter()
        .find(|f| f.file_name().is_some_and(|n| n == "axioms.rs"))?;
    let text = std::fs::read_to_string(file).ok()?;
    let para: Vec<&str> = text
        .lines()
        .map(str::trim)
        .take_while(|l| l.starts_with("//!"))
        .map(|l| l.trim_start_matches("//!").trim())
        .take_while(|l| !l.is_empty())
        .collect();
    let joined = para.join(" ").replace(['`', '[', ']'], "");
    let first = joined
        .find(". ")
        .and_then(|i| joined.get(..=i))
        .unwrap_or(&joined)
        .trim();
    (!first.is_empty()).then(|| first.to_owned())
}

/// One table row, as numbers.
#[derive(Debug, Clone)]
struct Row {
    /// The crate name without `clazel-`.
    short: String,
    place: Place,
    tier: usize,
    target: usize,
    verus: u64,
    kani: u64,
    axioms: u64,
    unsafe_blocks: u64,
    lines: Option<Lines>,
    mutations: Option<Mutations>,
    passed: u64,
    cases: u64,
    suites: u64,
    axiom_summary: Option<String>,
}

#[derive(Debug, Clone, Copy)]
struct Lines {
    spec: u64,
    proof: u64,
    exec: u64,
}

#[derive(Debug, Clone, Copy)]
struct Mutations {
    killed: u64,
    incidental: u64,
    survived: u64,
    total: u64,
}

/// The runs of decimal digits in `s`, as numbers.
fn numbers(s: &str) -> Vec<u64> {
    s.split(|c: char| !c.is_ascii_digit())
        .filter(|d| !d.is_empty())
        .filter_map(|d| d.parse().ok())
        .collect()
}

fn parse_row(name: &str, cells: &[String], summary: Option<String>) -> Result<Row, String> {
    let cell = |i: usize| {
        cells
            .get(i)
            .map(String::as_str)
            .ok_or_else(|| format!("{name}: table row has no column {i}"))
    };
    let place = PLACES
        .iter()
        .find(|(p, _)| *p == name)
        .map(|(_, place)| *place)
        .ok_or_else(|| {
            format!("{name}: not placed in a component (PLACES in xtask/src/status.rs)")
        })?;
    let tiers = numbers(cell(1)?);
    let tier_of = |v: Option<&u64>| -> Result<usize, String> {
        v.and_then(|t| usize::try_from(*t).ok())
            .filter(|t| *t < TIER.len())
            .ok_or_else(|| format!("{name}: no tier in {:?}", cells.get(1)))
    };
    let first = |s: &str| numbers(s).first().copied().unwrap_or(0);
    let verus = cell(2)?;
    let kani = cell(3)?;
    let lines = match numbers(cell(6)?).as_slice() {
        [spec, proof, exec] => Some(Lines {
            spec: *spec,
            proof: *proof,
            exec: *exec,
        }),
        _ => None,
    };
    let mutations = match numbers(cell(7)?).as_slice() {
        [killed, incidental, survived, total] => Some(Mutations {
            killed: *killed,
            incidental: *incidental,
            survived: *survived,
            total: *total,
        }),
        _ => None,
    };
    let (mut passed, mut cases, mut suites) = (0u64, 0u64, 0u64);
    let conformance = cell(8)?;
    if conformance != "none" && conformance != "—" {
        for suite in conformance.split("<br>") {
            // Suite names may hold colons; the counts follow the last one.
            let counts = suite
                .rfind(": ")
                .and_then(|i| suite.get(i..))
                .ok_or_else(|| format!("{name}: no counts in suite {suite:?}"))?;
            match numbers(counts).as_slice() {
                [p, t, ..] => {
                    passed = passed.saturating_add(*p);
                    cases = cases.saturating_add(*t);
                    suites = suites.saturating_add(1);
                }
                _ => return Err(format!("{name}: no counts in suite {suite:?}")),
            }
        }
    }
    Ok(Row {
        short: name.strip_prefix("clazel-").unwrap_or(name).to_owned(),
        place,
        tier: tier_of(tiers.first())?,
        target: tier_of(tiers.get(1))?,
        verus: if verus.contains("verified") {
            first(verus)
        } else {
            0
        },
        kani: if kani.contains("total") {
            numbers(kani).last().copied().unwrap_or(0)
        } else {
            0
        },
        axioms: first(cell(4)?),
        unsafe_blocks: first(cell(5)?),
        lines,
        mutations,
        passed,
        cases,
        suites,
        axiom_summary: summary,
    })
}

/// The drawn rows, in [`PLACES`] order.
fn parse(rows: &Rows, summaries: &dyn Fn(&str) -> Option<String>) -> Result<Vec<Row>, String> {
    let mut out = Vec::new();
    for (name, _) in PLACES {
        let cells = rows
            .get(*name)
            .ok_or_else(|| format!("{name}: placed, but has no row in the status table"))?;
        out.push(parse_row(name, cells, summaries(name))?);
    }
    if let Some(extra) = rows
        .keys()
        .find(|n| !NOT_DRAWN.contains(&n.as_str()) && !PLACES.iter().any(|(p, _)| p == n))
    {
        return Err(format!(
            "{extra}: not placed in a component (PLACES in xtask/src/status.rs)"
        ));
    }
    Ok(out)
}

/// What the scoreboard adds up.
#[derive(Debug, Default)]
struct Totals {
    crates: u64,
    correct: u64,
    verus: u64,
    killed: u64,
    mutations: u64,
    passed: u64,
    suites: u64,
    unsafe_blocks: u64,
    axioms: u64,
}

fn totals(rows: &[Row]) -> Totals {
    let mut t = Totals::default();
    for r in rows {
        t.crates = t.crates.saturating_add(1);
        if r.tier == 2 {
            t.correct = t.correct.saturating_add(1);
        }
        t.verus = t.verus.saturating_add(r.verus);
        if let Some(m) = r.mutations {
            t.killed = t.killed.saturating_add(m.killed);
            t.mutations = t.mutations.saturating_add(m.total);
        }
        t.passed = t.passed.saturating_add(r.passed);
        t.suites = t.suites.saturating_add(r.suites);
        t.unsafe_blocks = t.unsafe_blocks.saturating_add(r.unsafe_blocks);
        t.axioms = t.axioms.saturating_add(r.axioms);
    }
    t
}

// ------------------------------------------------------------------ drawing

const SANS: &str = "-apple-system,BlinkMacSystemFont,'Segoe UI',Helvetica,Arial,sans-serif";
const MONO: &str = "ui-monospace,SFMono-Regular,'SF Mono',Consolas,'Liberation Mono',monospace";

/// Colours, as CSS variables, light then dark.
const STYLE: &str = "<style>
:root{--bg:#ffffff;--fg:#1f2328;--mut:#59636e;--line:#d1d9e0;--panel:#f6f8fa;
--t2:#1a7f37;--t2s:#dafbe1;--t1:#0969da;--t1s:#ddf4ff;--t0:#818b98;--t0s:#eff2f5;--gap:#bf8700;
--spec:#8250df;--proof:#1a7f37;--exec:#9ea7b3;--bad:#cf222e}
@media (prefers-color-scheme:dark){:root{--bg:#0d1117;--fg:#e6edf3;--mut:#9198a1;--line:#3d444d;--panel:#151b23;
--t2:#3fb950;--t2s:#0f2d1a;--t1:#4493f8;--t1s:#0c2d6b;--t0:#7d8590;--t0s:#21262d;--gap:#d29922;
--spec:#a371f7;--proof:#3fb950;--exec:#656c76;--bad:#f85149}}
text{font-family:SANS;fill:var(--fg)}
.m{font-family:MONO}.mut{fill:var(--mut)}.b{font-weight:600}
</style>";

fn svg(w: f64, h: f64, title: &str, body: &str) -> String {
    let style = STYLE.replace("SANS", SANS).replace("MONO", MONO);
    format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{h}\" viewBox=\"0 0 {w} {h}\" role=\"img\" aria-labelledby=\"title\">\n\
         <title id=\"title\">{}</title>\n{style}\n\
         <rect width=\"{w}\" height=\"{h}\" rx=\"8\" fill=\"var(--bg)\" stroke=\"var(--line)\"/>\n{body}</svg>\n",
        esc(title)
    )
}

fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// A count as a reader skims it: 912, 1.7k, 82k, 1.37M.
fn short_count(n: u64) -> String {
    let f = n as f64;
    if n >= 1_000_000 {
        format!("{:.2}M", f / 1e6)
    } else if n >= 10_000 {
        format!("{}k", (f / 1e3).round())
    } else if n >= 1_000 {
        format!("{:.1}k", f / 1e3)
    } else {
        n.to_string()
    }
}

fn colour(tier: usize) -> &'static str {
    ["var(--t0)", "var(--t1)", "var(--t2)"]
        .get(tier)
        .copied()
        .unwrap_or("var(--t0)")
}

fn shade(tier: usize) -> &'static str {
    ["var(--t0s)", "var(--t1s)", "var(--t2s)"]
        .get(tier)
        .copied()
        .unwrap_or("var(--t0s)")
}

fn tier_name(tier: usize) -> &'static str {
    TIER.get(tier).copied().unwrap_or("")
}

fn f(n: usize) -> f64 {
    n as f64
}

/// Most proven first: by tier, then (among equals) by the tier still to come.
fn ranked<'a>(rows: &'a [Row], places: &[Place]) -> Vec<&'a Row> {
    let mut v: Vec<&Row> = rows.iter().filter(|r| places.contains(&r.place)).collect();
    v.sort_by(|a, b| b.tier.cmp(&a.tier).then(b.target.cmp(&a.target)));
    v
}

/// The README scoreboard: headline numbers, and one square per crate in
/// each component's row.
fn scoreboard(rows: &[Row]) -> String {
    let (w, h) = (880.0, 186.0);
    let t = totals(rows);
    let mut b = String::new();
    let stats = [
        [
            (
                t.correct.to_string(),
                format!("/{}", t.crates),
                "crates proven correct".to_owned(),
            ),
            (
                short_count(t.verus),
                String::new(),
                "Verus proof obligations".to_owned(),
            ),
            (
                t.killed.to_string(),
                format!("/{}", t.mutations),
                "broken specs caught".to_owned(),
            ),
        ],
        [
            (
                short_count(t.passed),
                String::new(),
                format!("conformance cases, {} suites", t.suites),
            ),
            (
                t.unsafe_blocks.to_string(),
                String::new(),
                "unsafe blocks, all in clazel-sys".to_owned(),
            ),
            (
                t.axioms.to_string(),
                String::new(),
                "axioms, each justified".to_owned(),
            ),
        ],
    ];
    for (i, line) in stats.iter().enumerate() {
        for (j, (value, of, label)) in line.iter().enumerate() {
            let x = 24.0 + f(j) * 158.0;
            let y = 50.0 + f(i) * 64.0;
            b.push_str(&format!(
                "<text x=\"{x}\" y=\"{y}\" font-size=\"24\" class=\"b\">{}<tspan font-size=\"14\" class=\"mut\">{}</tspan></text>\n\
                 <text x=\"{x}\" y=\"{}\" font-size=\"10.5\" class=\"mut\">{}</text>\n",
                esc(value),
                esc(of),
                y + 18.0,
                esc(label)
            ));
        }
    }
    b.push_str(&format!(
        "<line x1=\"500\" x2=\"500\" y1=\"20\" y2=\"{}\" stroke=\"var(--line)\"/>\n",
        h - 20.0
    ));
    let mut y = 22.0;
    for (label, places) in SCOREBOARD_ROWS {
        let crates = ranked(rows, places);
        b.push_str(&format!(
            "<text x=\"516\" y=\"{}\" font-size=\"11\" class=\"mut\">{label}</text>\n",
            y + 12.0
        ));
        for (i, r) in crates.iter().enumerate() {
            let x = 600.0 + f(i) * 20.0;
            if r.target > r.tier {
                b.push_str(&format!(
                    "<rect x=\"{x}\" y=\"{y}\" width=\"16\" height=\"16\" rx=\"4\" fill=\"none\" stroke=\"var(--gap)\" stroke-width=\"1.5\" stroke-dasharray=\"3 2\"/>\
                     <rect x=\"{}\" y=\"{}\" width=\"8\" height=\"8\" rx=\"2\" fill=\"{}\"/>\n",
                    x + 4.0,
                    y + 4.0,
                    colour(r.tier)
                ));
            } else {
                b.push_str(&format!(
                    "<rect x=\"{x}\" y=\"{y}\" width=\"16\" height=\"16\" rx=\"4\" fill=\"{}\"/>\n",
                    colour(r.tier)
                ));
            }
        }
        let correct = crates.iter().filter(|r| r.tier == 2).count();
        b.push_str(&format!(
            "<text x=\"786\" y=\"{}\" font-size=\"10.5\" class=\"mut\">{correct}/{} correct</text>\n",
            y + 12.0,
            crates.len()
        ));
        y += 25.0;
    }
    y += 4.0;
    let mut x = 516.0;
    for (tier, label) in [
        (Some(2), TIER[2]),
        (Some(1), TIER[1]),
        (Some(0), TIER[0]),
        (None, "below target"),
    ] {
        let mark = match tier {
            Some(t) => format!("fill=\"{}\"", colour(t)),
            None => "fill=\"none\" stroke=\"var(--gap)\" stroke-dasharray=\"2 1.5\"".to_owned(),
        };
        b.push_str(&format!(
            "<rect x=\"{x}\" y=\"{y}\" width=\"10\" height=\"10\" rx=\"2\" {mark}/>\
             <text x=\"{}\" y=\"{}\" font-size=\"10.5\" class=\"mut\">{label}</text>\n",
            x + 14.0,
            y + 9.0
        ));
        x += 22.0 + f(label.len()) * 5.4;
    }
    svg(w, h, "Verification status", &b)
}

/// Layout of the detail image's crate tiles.
const TILE_W: f64 = 124.0;
const TILE_H: f64 = 76.0;
const GAP: f64 = 8.0;
const PAD: f64 = 12.0;

/// One crate's tile: name, guarantee, the proof / spec / exec split of its
/// lines, and its two most telling counts.
fn tile(x: f64, y: f64, r: &Row) -> String {
    let below = r.target > r.tier;
    let border = if below {
        "stroke=\"var(--gap)\" stroke-dasharray=\"4 3\"".to_owned()
    } else {
        format!("stroke=\"{}\" stroke-opacity=\".5\"", colour(r.tier))
    };
    let mut s = format!(
        "<rect x=\"{x}\" y=\"{y}\" width=\"{TILE_W}\" height=\"{TILE_H}\" rx=\"6\" fill=\"{}\" {border}/>\n\
         <text x=\"{}\" y=\"{}\" font-size=\"12\" class=\"m b\">{}</text>\n",
        shade(r.tier),
        x + 8.0,
        y + 18.0,
        esc(&r.short)
    );
    let target = if below {
        format!(
            "<tspan font-weight=\"400\" style=\"fill:var(--gap)\"> → {}</tspan>",
            TIER_SHORT.get(r.target).copied().unwrap_or("")
        )
    } else {
        String::new()
    };
    s.push_str(&format!(
        "<text x=\"{}\" y=\"{}\" font-size=\"10.5\" class=\"b\" style=\"fill:{}\">{}{target}</text>\n",
        x + 8.0,
        y + 47.0,
        colour(r.tier),
        tier_name(r.tier)
    ));
    s.push_str(&line_bar(x + 8.0, y + 27.0, TILE_W - 16.0, r.lines));
    let mut facts = Vec::new();
    if r.cases > 0 {
        facts.push(format!("{} cases", short_count(r.cases)));
    }
    if let Some(m) = r.mutations {
        facts.push(format!("{}/{} mut", m.killed, m.total));
    }
    if r.kani > 0 {
        facts.push(format!("{} Kani harnesses", r.kani));
    }
    if r.unsafe_blocks > 0 {
        facts.push(format!("{} unsafe, audited", r.unsafe_blocks));
    }
    if facts.is_empty() {
        facts.push("unverified shell".to_owned());
    }
    for (i, fact) in facts.iter().take(2).enumerate() {
        s.push_str(&format!(
            "<text x=\"{}\" y=\"{}\" font-size=\"10\" class=\"mut\">{}</text>\n",
            x + 8.0,
            y + 60.0 + f(i) * 11.0,
            esc(fact)
        ));
    }
    if r.mutations.is_some_and(|m| m.survived > 0) {
        s.push_str(&format!(
            "<circle cx=\"{}\" cy=\"{}\" r=\"4\" fill=\"var(--bad)\"/>\n",
            x + TILE_W - 10.0,
            y + 14.0
        ));
    }
    s
}

/// A crate's lines as one bar: proof, then spec, then exec. A dashed
/// outline when it has no Verus code.
fn line_bar(x: f64, y: f64, w: f64, lines: Option<Lines>) -> String {
    let Some(l) = lines.filter(|l| l.spec.saturating_add(l.proof).saturating_add(l.exec) > 0)
    else {
        return format!(
            "<rect x=\"{x}\" y=\"{y}\" width=\"{w}\" height=\"6\" rx=\"3\" fill=\"none\" stroke=\"var(--line)\" stroke-dasharray=\"3 2\"/>\n"
        );
    };
    let parts = [
        ("proof", l.proof as f64),
        ("spec", l.spec as f64),
        ("exec", l.exec as f64),
    ];
    let total: f64 = parts.iter().map(|(_, v)| v).sum();
    let mut s = format!(
        "<svg x=\"{x}\" y=\"{y}\" width=\"{w}\" height=\"6\"><rect width=\"{w}\" height=\"6\" rx=\"3\" fill=\"var(--exec)\"/>"
    );
    let mut cx = 0.0;
    for (kind, v) in parts {
        let pw = w * v / total;
        s.push_str(&format!(
            "<rect x=\"{cx:.1}\" width=\"{pw:.1}\" height=\"6\" fill=\"var(--{kind})\"/>"
        ));
        cx += pw;
    }
    s.push_str("</svg>\n");
    s
}

fn grid(x: f64, y: f64, cols: usize, crates: &[&Row]) -> String {
    let mut s = String::new();
    for (i, r) in crates.iter().enumerate() {
        let col = i.checked_rem(cols).unwrap_or(0);
        let row = i.checked_div(cols).unwrap_or(0);
        s.push_str(&tile(
            x + f(col) * (TILE_W + GAP),
            y + f(row) * (TILE_H + GAP),
            r,
        ));
    }
    s
}

/// Height of `n` tiles in `cols` columns.
fn grid_h(n: usize, cols: usize) -> f64 {
    let rows = n.div_ceil(cols.max(1)).max(1);
    f(rows) * (TILE_H + GAP) - GAP
}

fn panel(x: f64, y: f64, w: f64, h: f64, title: &str, sub: &str, dashed: bool) -> String {
    let dash = if dashed {
        " stroke-dasharray=\"6 4\""
    } else {
        ""
    };
    format!(
        "<rect x=\"{x}\" y=\"{y}\" width=\"{w}\" height=\"{h}\" rx=\"10\" fill=\"var(--panel)\" stroke=\"var(--line)\"{dash}/>\n\
         <text x=\"{}\" y=\"{}\" font-size=\"13\" class=\"b\">{}</text>\n\
         <text x=\"{}\" y=\"{}\" font-size=\"11\" class=\"mut\">{}</text>\n",
        x + PAD,
        y + 22.0,
        esc(title),
        x + PAD,
        y + 38.0,
        esc(sub)
    )
}

fn section(x: f64, y: f64, head: &str, text: &str) -> String {
    format!(
        "<text x=\"{x}\" y=\"{}\" font-size=\"10.5\" class=\"mut\"><tspan class=\"b\">{head}</tspan>  {}</text>\n",
        y + 10.0,
        esc(text)
    )
}

fn in_place(rows: &[Row], place: Place) -> Vec<&Row> {
    rows.iter().filter(|r| r.place == place).collect()
}

fn names(rows: &[&Row]) -> String {
    rows.iter()
        .map(|r| r.short.as_str())
        .collect::<Vec<_>>()
        .join(", ")
}

/// The detail image: every crate in the process and component that runs it,
/// then notes on the counts a headline cannot explain.
fn detail(rows: &[Row]) -> String {
    let (w, p) = (904.0, 20.0);
    let mut b = String::new();
    b.push_str(&format!(
        "<text x=\"{p}\" y=\"30\" font-size=\"18\" class=\"b\">Verification status by component</text>\n\
         <text x=\"{p}\" y=\"48\" font-size=\"11.5\" class=\"mut\">Each crate sits where it runs. The colour is what is guaranteed about it; the bar splits its lines into proof, spec and exec.</text>\n"
    ));
    let cols = 5;
    let (kernel, network, shells) = (
        in_place(rows, Place::Kernel),
        in_place(rows, Place::Network),
        in_place(rows, Place::Shell),
    );
    let (renderer, prims, os) = (
        in_place(rows, Place::Renderer),
        in_place(rows, Place::Primitive),
        in_place(rows, Place::Os),
    );
    let host_x = p;
    let host_w = PAD * 2.0 + f(cols) * TILE_W + f(cols.saturating_sub(1)) * GAP;
    let rend_w = PAD * 2.0 + TILE_W;
    let rend_x = w - p - rend_w;
    let top = 64.0;

    // Host process: the kernel, the network, the shells.
    let mut inner = String::new();
    let mut y = top + 48.0;
    for (head, text, crates) in [
        (
            "KERNEL",
            "owns all browser state and decides every change to it",
            &kernel,
        ),
        (
            "NETWORK",
            "parses and checks every byte off the wire: HTTP, DNS, TLS and certificates",
            &network,
        ),
        (
            "SHELLS",
            "move bytes between the OS and the kernel, and decide nothing",
            &shells,
        ),
    ] {
        inner.push_str(&section(host_x + PAD, y, head, text));
        y += 16.0;
        inner.push_str(&grid(host_x + PAD, y, cols, crates));
        y += grid_h(crates.len(), cols) + 14.0;
    }
    let host_h = (y - 14.0 + PAD - top).max(52.0 + grid_h(renderer.len(), 1) + PAD);
    b.push_str(&panel(
        host_x,
        top,
        host_w,
        host_h,
        "Host process",
        "the kernel and the network; the only process with I/O",
        false,
    ));
    b.push_str(&inner);
    b.push_str(&panel(
        rend_x,
        top,
        rend_w,
        host_h,
        "Renderer process",
        "one per tab, sandboxed",
        true,
    ));
    b.push_str(&grid(rend_x + PAD, top + 52.0, 1, &renderer));

    // IPC between the two processes.
    let ay = top + host_h / 2.0;
    b.push_str(&format!(
        "<defs><marker id=\"arrow\" viewBox=\"0 0 10 10\" refX=\"5\" refY=\"5\" markerWidth=\"6\" markerHeight=\"6\" orient=\"auto-start-reverse\"><path d=\"M0 0L10 5L0 10z\" fill=\"var(--fg)\"/></marker></defs>\n\
         <line x1=\"{}\" x2=\"{}\" y1=\"{ay}\" y2=\"{ay}\" stroke=\"var(--fg)\" stroke-width=\"1.5\" marker-start=\"url(#arrow)\" marker-end=\"url(#arrow)\"/>\n\
         <text x=\"{}\" y=\"{}\" font-size=\"10\" class=\"mut\" text-anchor=\"middle\">IPC</text>\n",
        host_x + host_w + 2.0,
        rend_x - 2.0,
        (host_x + host_w + rend_x) / 2.0,
        ay - 6.0
    ));

    // Primitives under the host, the OS boundary under the renderer.
    let low = top + host_h + 16.0;
    let low_h = (52.0 + grid_h(prims.len(), cols)).max(52.0 + grid_h(os.len(), 1)) + PAD;
    b.push_str(&panel(
        host_x,
        low,
        host_w,
        low_h,
        "Shared primitives",
        "linked into both processes",
        false,
    ));
    b.push_str(&grid(host_x + PAD, low + 52.0, cols, &prims));
    b.push_str(&panel(
        rend_x,
        low,
        rend_w,
        low_h,
        "OS boundary",
        "the only unsafe code",
        false,
    ));
    b.push_str(&grid(rend_x + PAD, low + 52.0, 1, &os));

    // Notes: what the scoreboard's mutation and axiom counts leave out.
    let t = totals(rows);
    let incidental: Vec<&Row> = rows
        .iter()
        .filter(|r| r.mutations.is_some_and(|m| m.incidental > 0))
        .collect();
    let survived: Vec<&Row> = rows
        .iter()
        .filter(|r| r.mutations.is_some_and(|m| m.survived > 0))
        .collect();
    let sum = |v: &[&Row], get: fn(Mutations) -> u64| {
        v.iter()
            .filter_map(|r| r.mutations)
            .fold(0u64, |a, m| a.saturating_add(get(m)))
    };
    let mut mutation_lines = Vec::new();
    if !incidental.is_empty() {
        mutation_lines.push(format!(
            "{} more ({}) broke only a proof script: no theorem became false, so they are not counted as coverage.",
            sum(&incidental, |m| m.incidental),
            names(&incidental)
        ));
    }
    if !survived.is_empty() {
        mutation_lines.push(format!(
            "{} ({}) survived: a known gap, recorded in mutations.json with what will close it.",
            sum(&survived, |m| m.survived),
            names(&survived)
        ));
    }
    let with_axioms: Vec<&Row> = rows.iter().filter(|r| r.axioms > 0).collect();
    let mut axiom_lines: Vec<String> = with_axioms
        .iter()
        .map(|r| {
            format!(
                "{}, {}: {}",
                r.short,
                r.axioms,
                r.axiom_summary.as_deref().unwrap_or("see its axioms.rs.")
            )
        })
        .collect();
    if !axiom_lines.is_empty() {
        axiom_lines.push(
            "Each sits in its crate's axioms.rs with its justification; the checker rejects any other assumption."
                .to_owned(),
        );
    }
    let notes: Vec<(String, Vec<String>)> = [
        (
            format!(
                "{} of {} broken specs caught by a theorem",
                t.killed, t.mutations
            ),
            mutation_lines,
        ),
        (
            format!(
                "{} axioms: proofs taken from other verified libraries",
                t.axioms
            ),
            axiom_lines,
        ),
    ]
    .into_iter()
    .filter(|(_, lines)| !lines.is_empty())
    .collect();
    let mut y = low + low_h + 16.0;
    if !notes.is_empty() {
        let h = 14.0
            + notes
                .iter()
                .map(|(_, ls)| 28.0 + f(ls.len()) * 15.0)
                .sum::<f64>();
        b.push_str(&format!(
            "<rect x=\"{p}\" y=\"{y}\" width=\"{}\" height=\"{h}\" rx=\"10\" fill=\"var(--panel)\" stroke=\"var(--line)\"/>\n",
            w - 2.0 * p
        ));
        let mut ty = y + 26.0;
        for (head, lines) in &notes {
            b.push_str(&format!(
                "<text x=\"{}\" y=\"{ty}\" font-size=\"12\" class=\"b\">{}</text>\n",
                p + PAD,
                esc(head)
            ));
            ty += 17.0;
            for line in lines {
                b.push_str(&format!(
                    "<text x=\"{}\" y=\"{ty}\" font-size=\"11\" class=\"mut\">{}</text>\n",
                    p + PAD,
                    esc(line)
                ));
                ty += 15.0;
            }
            ty += 11.0;
        }
        y += h;
    }

    // Legend.
    let mut ly = y + 24.0;
    let mut x = p;
    for (tier, text) in [
        (2, "Proven correct · Verus, unbounded"),
        (1, "Panic-free · Kani, on all inputs to a bound"),
        (0, "Memory safe · safe Rust and tests"),
    ] {
        b.push_str(&format!(
            "<rect x=\"{x}\" y=\"{}\" width=\"20\" height=\"12\" rx=\"3\" fill=\"{}\" stroke=\"{}\"/>\
             <text x=\"{}\" y=\"{ly}\" font-size=\"11\" class=\"mut\">{text}</text>\n",
            ly - 10.0,
            shade(tier),
            colour(tier),
            x + 26.0
        ));
        x += 36.0 + f(text.chars().count()) * 5.6;
    }
    b.push_str(&format!(
        "<rect x=\"{x}\" y=\"{}\" width=\"20\" height=\"12\" rx=\"3\" fill=\"none\" stroke=\"var(--gap)\" stroke-dasharray=\"3 2\"/>\
         <text x=\"{}\" y=\"{ly}\" font-size=\"11\" class=\"mut\">below target tier</text>\n",
        ly - 10.0,
        x + 26.0
    ));
    ly += 20.0;
    x = p;
    for (kind, text) in [("proof", "proof"), ("spec", "spec"), ("exec", "exec lines")] {
        b.push_str(&format!(
            "<rect x=\"{x}\" y=\"{}\" width=\"10\" height=\"8\" rx=\"2\" fill=\"var(--{kind})\"/>\
             <text x=\"{}\" y=\"{ly}\" font-size=\"11\" class=\"mut\">{text}</text>\n",
            ly - 8.0,
            x + 14.0
        ));
        x += 72.0;
    }
    b.push_str(&format!(
        "<circle cx=\"{}\" cy=\"{}\" r=\"4\" fill=\"var(--bad)\"/>\
         <text x=\"{}\" y=\"{ly}\" font-size=\"11\" class=\"mut\">surviving mutant</text>\n\
         <text x=\"{}\" y=\"{ly}\" font-size=\"11\" class=\"mut\" text-anchor=\"end\">every suite and count: the table below</text>\n",
        x + 4.0,
        ly - 4.0,
        x + 14.0,
        w - p
    ));
    svg(w, ly + 16.0, "Verification status by component", &b)
}

/// The scoreboard and the detail image, from the status table's rows.
/// `summaries` gives a crate's axiom summary ([`axiom_summary`]).
pub fn render(
    rows: &Rows,
    summaries: &dyn Fn(&str) -> Option<String>,
) -> Result<(String, String), String> {
    let parsed = parse(rows, summaries)?;
    Ok((scoreboard(&parsed), detail(&parsed)))
}

#[cfg(test)]
mod tests {
    use super::{PLACES, Rows, numbers, placement_problems, render, short_count};

    fn row(cells: &[&str]) -> Vec<String> {
        cells.iter().map(|c| (*c).to_owned()).collect()
    }

    fn table() -> Rows {
        let mut rows = Rows::new();
        for (name, _) in PLACES {
            rows.insert(
                (*name).to_owned(),
                row(&[
                    name,
                    "0 (0)",
                    "not used",
                    "no harnesses",
                    "0",
                    "0 (0)",
                    "—",
                    "—",
                    "none",
                    "no spec files",
                ]),
            );
        }
        rows.insert(
            "clazel-tls".into(),
            row(&[
                "clazel-tls",
                "0 (2)",
                "822 verified, 0 errors",
                "no harnesses",
                "0",
                "0 (0)",
                "7389 / 5520 / 3848",
                "210 / 0 / 1 of 211",
                "a: b: 39 / 40 (1 expected failures)<br>c: 24 / 24",
                "0 of 14 files current",
            ]),
        );
        rows.insert(
            "clazel-crypto".into(),
            row(&[
                "clazel-crypto",
                "0 (0)",
                "81 verified, 0 errors",
                "no harnesses",
                "15",
                "0 (0)",
                "795 / 402 / 418",
                "57 / 9 / 0 of 66",
                "x: 5 / 5",
                "0 of 7 files current",
            ]),
        );
        rows
    }

    #[test]
    fn counts_read_back_from_the_table() -> Result<(), String> {
        let (board, detail) = render(&table(), &|n| {
            (n == "clazel-crypto")
                .then(|| "The trust boundary: every call into libcrux, each one axiom.".to_owned())
        })?;
        // 0 of 31 at Tier 2; 903 Verus obligations; 267 of 277 mutants.
        assert!(board.contains(">0<tspan font-size=\"14\" class=\"mut\">/31</tspan>"));
        assert!(board.contains(">903<"));
        assert!(board.contains(">267<tspan font-size=\"14\" class=\"mut\">/277</tspan>"));
        // 39 + 24 + 5 conformance cases passed in three suites; colons in a
        // suite name do not confuse the counts.
        assert!(board.contains(">68<"));
        assert!(board.contains("conformance cases, 3 suites"));
        assert!(detail.contains("9 more (crypto) broke only a proof script"));
        assert!(detail.contains("1 (tls) survived"));
        assert!(
            detail.contains(
                "crypto, 15: The trust boundary: every call into libcrux, each one axiom."
            )
        );
        assert!(detail.contains(
            "Memory safe<tspan font-weight=\"400\" style=\"fill:var(--gap)\"> → correct</tspan>"
        ));
        Ok(())
    }

    #[test]
    fn every_crate_must_be_placed() {
        let mut names: Vec<&str> = PLACES.iter().map(|(n, _)| *n).collect();
        names.push("xtask");
        assert!(placement_problems(&names).is_empty());
        names.push("clazel-css");
        assert_eq!(placement_problems(&names).len(), 1);
        let mut rows = table();
        rows.insert("clazel-css".into(), row(&["clazel-css"]));
        assert!(render(&rows, &|_| None).is_err());
    }

    #[test]
    fn short_counts() {
        assert_eq!(short_count(912), "912");
        assert_eq!(short_count(1_700), "1.7k");
        assert_eq!(short_count(82_160), "82k");
        assert_eq!(short_count(1_370_000), "1.37M");
        assert_eq!(
            numbers("166 / 167 (1 expected failures)"),
            vec![166, 167, 1]
        );
    }
}
