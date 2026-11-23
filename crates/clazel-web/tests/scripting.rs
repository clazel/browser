//! HTML integration, the script half (phase-7.md item 7.15): pages parsed
//! with the scripting flag on, their scripts run by "prepare the script
//! element" as the parser reaches them, through `clazel-js`.
//!
//! Each test names the algorithm and step it checks. Those marked "WPT"
//! follow the ordering a vendored `html/semantics/scripting-1/
//! the-script-element/execution-timing/` test checks, with `log` as its
//! `testlib.js` `log`; the runs of the vendored pages themselves are in
//! `wpt_execution_timing` below.

#[path = "support/page.rs"]
mod support;

use clazel_encoding::labels::spec::Encoding;
use clazel_js::Result;
use clazel_web::scripting::time::{coarsen_us, performance_now_ms};
use clazel_web::scripting::{Progress, Readiness};
use support::{Harness, engine, exceptions};

// ---- Inline classic scripts -------------------------------------------------

/// WPT 001: inline scripts run in document order, as the parser reaches
/// each `</script>` ("prepare the script element" step 34.3: "immediately
/// execute the script element").
#[test]
fn inline_scripts_run_in_order() -> Result<()> {
    let mut h = Harness::new(
        "<script>log('inline script #1');</script><script>log('inline script #2');</script>",
    )?;
    assert_eq!(h.load()?, Progress::Loaded);
    assert_eq!(h.logged(), ["inline script #1", "inline script #2"]);
    assert!(h.reports.is_empty(), "{:?}", h.reports);
    Ok(())
}

/// A script runs before the parser has seen what follows it: the document
/// it sees ends at its own `</script>` (§13.2.6.4.8: the parser pauses for
/// "prepare the script element"), shown here by `document.write` landing
/// right after the script.
#[test]
fn a_script_runs_before_the_markup_after_it() -> Result<()> {
    let mut h = Harness::new("<p>a</p><script>document.write('<i>w</i>')</script><p>b</p>")?;
    h.load()?;
    assert_eq!(
        h.tree()?,
        "| <html>\n|   <head>\n|   <body>\n|     <p>\n|       \"a\"\n|     <script>\n|       \"document.write('<i>w</i>')\"\n|     <i>\n|       \"w\"\n|     <p>\n|       \"b\"\n"
    );
    Ok(())
}

/// "Prepare the script element" steps 8 to 12: the type string, and which
/// types run.
#[test]
fn script_types() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script>log('none')</script>",
        "<script type=''>log('empty type')</script>",
        "<script type=' text/javascript '>log('padded type')</script>",
        "<script type='TEXT/JAVASCRIPT'>log('uppercase type')</script>",
        "<script language=''>log('empty language')</script>",
        "<script language='javascript'>log('language javascript')</script>",
        "<script language='vbscript'>log('language vbscript')</script>",
        "<script type='text/plain'>log('text/plain')</script>",
        "<script type='application/ecmascript'>log('ecmascript')</script>",
        "<script type='text/javascript;version=1.8'>log('params')</script>",
        "<script type='importmap'>{}</script>",
    ))?;
    h.load()?;
    assert_eq!(
        h.logged(),
        [
            "none",
            "empty type",
            "padded type",
            "uppercase type",
            "empty language",
            "language javascript",
            "ecmascript"
        ]
    );
    assert_eq!(
        engine(&h.reports),
        ["import maps are not supported (Phase 8)"]
    );
    Ok(())
}

/// Step 6: an inline script with no text does nothing; step 18: a classic
/// script with `nomodule` does not run.
#[test]
fn empty_and_nomodule_scripts_do_not_run() -> Result<()> {
    let mut h = Harness::new(
        "<script></script><script nomodule>log('nomodule')</script><script>log('ran')</script>",
    )?;
    h.load()?;
    assert_eq!(h.logged(), ["ran"]);
    Ok(())
}

/// Step 20: `event` and `for` attributes on a classic script.
#[test]
fn event_and_for_attributes() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script for=window event=onload>log('window onload')</script>",
        "<script for=' WINDOW ' event='onload()'>log('window onload()')</script>",
        "<script for=document event=onload>log('document')</script>",
        "<script for=window event=onclick>log('onclick')</script>",
        "<script for=window>log('for alone')</script>",
    ))?;
    h.load()?;
    assert_eq!(
        h.logged(),
        ["window onload", "window onload()", "for alone"]
    );
    Ok(())
}

/// "Run a classic script" step 8: an exception is reported, and the next
/// script still runs; a script that does not parse is reported the same
/// way (its error to rethrow).
#[test]
fn errors_are_reported_and_parsing_goes_on() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script>log('a'); throw new TypeError('boom'); log('not reached')</script>",
        "<script>var = ;</script>",
        "<script>log('b')</script>",
    ))?;
    assert_eq!(h.load()?, Progress::Loaded);
    assert_eq!(h.logged(), ["a", "b"]);
    assert_eq!(
        exceptions(&h.reports),
        ["TypeError: boom", "SyntaxError: invalid script"]
    );
    assert!(
        h.event_names()
            .iter()
            .filter(|e| *e == "Window:error")
            .count()
            == 2
    );
    Ok(())
}

/// What the engine cannot run yet is an engine report, and the page goes
/// on.
#[test]
fn what_the_engine_lacks_is_reported() -> Result<()> {
    let mut h = Harness::new("<script>class A {}</script><script>log('after')</script>")?;
    h.load()?;
    assert_eq!(h.logged(), ["after"]);
    assert_eq!(engine(&h.reports).len(), 1, "{:?}", h.reports);
    Ok(())
}

// ---- document.currentScript --------------------------------------------------

/// "Execute the script element" step 6 (classic): `document.currentScript`
/// is the element while it runs, the same object each time, and null
/// after.
#[test]
fn current_script() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script id=one>var first = document.currentScript; log(first === document.currentScript);</script>",
        "<script>var second = document.currentScript; log(first === second);</script>",
    ))?;
    h.load()?;
    assert_eq!(h.logged(), ["true", "false"]);
    let realm = h.page.realm().clone();
    let (first, second, after) = h.page.runtime().scope(|scope| {
        let global = scope.global(&realm)?;
        let f = scope.get(global, clazel_js::Key::from("first"))?;
        let s = scope.get(global, clazel_js::Key::from("second"))?;
        let d = scope.get(global, clazel_js::Key::from("document"))?;
        let c = scope.get(d, clazel_js::Key::from("currentScript"))?;
        let f = clazel_web::scripting::globals::node_of(scope, f);
        let s = clazel_web::scripting::globals::node_of(scope, s);
        Ok::<_, clazel_js::Error>((f, s, scope.kind(c)))
    })?;
    assert_eq!(after, clazel_js::ValueKind::Null);
    let (Some(first), Some(second)) = (first, second) else {
        return Err(clazel_js::Error::WrongType("currentScript was not a node"));
    };
    let ids = h.page.with_document(|a| {
        let id = |n: usize| match a.kind(n) {
            clazel_dom::exec::ExecKind::Element { attributes, .. } => attributes.first().map(|x| {
                x.value
                    .iter()
                    .map(|c| char::from_u32(*c).unwrap_or('?'))
                    .collect::<String>()
            }),
            _ => None,
        };
        (id(first.node), id(second.node))
    })?;
    assert_eq!(ids, (Some("one".to_owned()), None));
    Ok(())
}

// ---- External scripts ----------------------------------------------------------

/// WPT 002 and 003: a parser-blocking external script (step 33.5) blocks
/// the tokenizer until it has run (§13.2.6.4.8 step 10), so the inline
/// script after it runs after it, however long the fetch takes.
#[test]
fn a_parser_blocking_script_blocks_the_parser() -> Result<()> {
    let mut h =
        Harness::new("<script src=a.js></script><script>log('inline')</script><p>after</p>")?;
    h.script("a.js", "log('external a')");
    assert_eq!(h.run()?, Progress::Waiting);
    assert_eq!(h.requested, ["https://example.test/dir/a.js"]);
    // Blocked: the inline script has not run, nor has the parser gone on.
    assert!(h.logged().is_empty());
    assert!(!h.tree()?.contains("after"));
    assert_eq!(h.answer("https://example.test/dir/a.js")?, Progress::Loaded);
    assert_eq!(h.logged(), ["external a", "inline"]);
    assert!(h.tree()?.contains("after"));
    // "Execute the script element" step 8: load at the element.
    assert!(
        h.event_names()
            .iter()
            .any(|e| e.ends_with(":load") && e.starts_with("Element"))
    );
    Ok(())
}

/// Step 31: the `src` is resolved against the document base URL (a `base`
/// element's), and step 21: a `charset` attribute is the fallback encoding.
#[test]
fn src_resolves_against_the_base_url() -> Result<()> {
    let mut h =
        Harness::new("<base href='/other/'><script src='x.js' charset=windows-1252></script>")?;
    h.files.insert(
        "https://example.test/other/x.js".to_owned(),
        support::File {
            content_type: "text/javascript",
            body: "log('caf\u{e9}')".to_owned(),
        },
    );
    h.run()?;
    assert_eq!(h.requested, ["https://example.test/other/x.js"]);
    h.answer("https://example.test/other/x.js")?;
    // UTF-8 bytes read as windows-1252: the content type names no charset.
    assert_eq!(h.logged(), ["caf\u{c3}\u{a9}"]);
    Ok(())
}

/// A failed fetch: the element's result is null, so "execute the script
/// element" step 4 fires `error` at it, and parsing goes on. Step 31.3: an
/// empty `src` fires `error` and fetches nothing.
#[test]
fn failed_and_empty_src() -> Result<()> {
    let mut h = Harness::new(
        "<script src=''></script><script src=gone.js></script><script src=404.js></script><script>log('after')</script>",
    )?;
    h.run()?;
    assert_eq!(
        h.requested,
        ["https://example.test/dir/gone.js"],
        "the parser is blocked on gone.js"
    );
    h.fail("https://example.test/dir/gone.js")?;
    h.answer("https://example.test/dir/404.js")?;
    assert_eq!(h.logged(), ["after"]);
    let errors = h
        .event_names()
        .into_iter()
        .filter(|e| e.ends_with(":error"))
        .count();
    assert_eq!(errors, 3);
    Ok(())
}

/// WPT 085, 086 and 088: an `async` script runs when its fetch completes,
/// without blocking the parser (step 33.2), and in whatever order the
/// fetches complete; `defer` scripts run after parsing, in document order
/// (step 33.4 and "the end" step 5), before `DOMContentLoaded`; the load
/// event waits for the async ones (steps 7 and 8).
#[test]
fn async_and_defer() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script src=d1.js defer></script>",
        "<script src=a1.js async></script>",
        "<script src=d2.js defer></script>",
        "<script src=a2.js async></script>",
        "<script>log('inline')</script>",
    ))?;
    for n in ["d1", "d2", "a1", "a2"] {
        h.script(&format!("{n}.js"), &format!("log('{n}')"));
    }
    assert_eq!(h.run()?, Progress::Waiting);
    // Not blocked: the parser has finished, and the inline script has run.
    assert_eq!(h.logged(), ["inline"]);
    assert_eq!(h.page.readiness()?, Readiness::Interactive);
    assert_eq!(h.requested.len(), 4);
    // The second async script arrives first and runs at once.
    h.answer("https://example.test/dir/a2.js")?;
    assert_eq!(h.logged(), ["inline", "a2"]);
    // The second defer script arrives before the first: it waits.
    h.answer("https://example.test/dir/d2.js")?;
    assert_eq!(h.logged(), ["inline", "a2"]);
    h.answer("https://example.test/dir/d1.js")?;
    assert_eq!(h.logged(), ["inline", "a2", "d1", "d2"]);
    assert!(
        h.event_names()
            .contains(&"Document:DOMContentLoaded".to_owned())
    );
    // The load event waits for the last async script.
    assert!(!h.event_names().contains(&"Window:load".to_owned()));
    assert_eq!(
        h.answer("https://example.test/dir/a1.js")?,
        Progress::Loaded
    );
    assert_eq!(h.logged(), ["inline", "a2", "d1", "d2", "a1"]);
    assert!(h.event_names().contains(&"Window:load".to_owned()));
    assert_eq!(h.page.readiness()?, Readiness::Complete);
    Ok(())
}

/// WPT 089 and 090: `async` and `defer` do nothing on an inline script
/// (step 33 applies to classic scripts with `src` only).
#[test]
fn async_and_defer_on_inline_scripts_do_nothing() -> Result<()> {
    let mut h = Harness::new(
        "<script async>log('a')</script><script defer>log('b')</script><script>log('c')</script>",
    )?;
    h.load()?;
    assert_eq!(h.logged(), ["a", "b", "c"]);
    Ok(())
}

/// WPT 007: an external script written by `document.write` blocks the
/// parser too (its nesting level is two: step 10 sets the pause flag and
/// the outer script finishes first); its inline text is not run.
#[test]
fn a_written_external_script() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script>log('inline script #1');",
        "document.write('<script src=\"include-1.js\">log(\\'ignore this\\')<\\/script>');",
        "log('end script #1');</script>",
        "<script>log('after')</script>",
    ))?;
    h.script("include-1.js", "log('external script #1')");
    h.load()?;
    assert_eq!(
        h.logged(),
        [
            "inline script #1",
            "end script #1",
            "external script #1",
            "after"
        ]
    );
    Ok(())
}

/// WPT 009 (in part): `document.write` from an external script is ignored
/// ("execute the script element" step 5 raises the ignore-destructive-writes
/// counter, and the document write steps' step 6.1 returns) when the
/// insertion point is undefined, as it is for a script the parser runs
/// once blocked (§13.2.6.4.8 step 10.9 defines it: there the write goes in).
#[test]
fn writes_from_external_scripts() -> Result<()> {
    let mut h = Harness::new(
        "<script src=blocking.js></script><script src=late.js async></script><p>end</p>",
    )?;
    h.script("blocking.js", "document.write('<b>from blocking</b>')");
    h.script(
        "late.js",
        "document.write('<i>from async</i>'); log('async ran')",
    );
    h.run()?;
    h.answer("https://example.test/dir/blocking.js")?;
    h.answer("https://example.test/dir/late.js")?;
    let tree = h.tree()?;
    assert!(tree.contains("from blocking"), "{tree}");
    assert!(!tree.contains("from async"), "{tree}");
    assert_eq!(h.logged(), ["async ran"]);
    Ok(())
}

// ---- document.write ----------------------------------------------------------------

/// The document write steps, step 7 and 8: the text goes in at the
/// insertion point and is parsed before the rest; `writeln` adds a line
/// feed; several arguments are joined.
#[test]
fn write_and_writeln() -> Result<()> {
    let mut h = Harness::new(
        "<pre><script>document.write('a', 'b'); document.writeln('c'); document.write(1, true)</script>z</pre>",
    )?;
    h.load()?;
    assert!(h.tree()?.contains("\"abc\n1truez\""), "{}", h.tree()?);
    Ok(())
}

/// WPT 041 and html5lib `scripted_webkit01.dat` case 1: scripts that write
/// scripts that write. Each written script runs when the parser reaches
/// its end tag, inside the `document.write` that wrote it (the parser is
/// re-entered), and their output lands in order.
#[test]
fn scripts_that_write_scripts() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script>log('outer start');",
        "document.write('<script>log(\"inner 1\"); document.write(\"<b>1</b>\")<\\/script>');",
        "log('between');",
        "document.write('<script>log(\"inner 2\"); document.write(\"<b>2</b>\")<\\/script>');",
        "log('outer end')</script><b>3</b>",
    ))?;
    h.load()?;
    assert_eq!(
        h.logged(),
        ["outer start", "inner 1", "between", "inner 2", "outer end"]
    );
    let tree = h.tree()?;
    let order: Vec<&str> = ["\"1\"", "\"2\"", "\"3\""]
        .into_iter()
        .filter(|t| tree.contains(t))
        .collect();
    assert_eq!(order.len(), 3, "{tree}");
    let p1 = tree.find("\"1\"");
    let p2 = tree.find("\"2\"");
    let p3 = tree.find("\"3\"");
    assert!(p1 < p2 && p2 < p3, "{tree}");
    Ok(())
}

/// A write that leaves a tag open: the tokenizer waits at the insertion
/// point and the next write finishes the tag.
#[test]
fn a_tag_split_across_writes() -> Result<()> {
    let mut h =
        Harness::new("<script>document.write('<a hr'); document.write('ef=x>link</a>')</script>")?;
    h.load()?;
    assert!(
        h.tree()?
            .contains("<a>\n|       href=\"x\"\n|       \"link\""),
        "{}",
        h.tree()?
    );
    Ok(())
}

// ---- document.open and document.close ------------------------------------------------

/// `document.open()` during parsing, from a script the parser runs, does
/// nothing (the document open steps, step 5: an active parser whose script
/// nesting level is above zero), and `document.close()` does nothing either
/// (step 3: no script-created parser).
#[test]
fn open_and_close_during_parsing_do_nothing() -> Result<()> {
    let mut h = Harness::new(
        "<p>kept</p><script>document.open(); document.close(); log(document.open() === document)</script><p>too</p>",
    )?;
    h.load()?;
    assert_eq!(h.logged(), ["true"]);
    let tree = h.tree()?;
    assert!(tree.contains("kept") && tree.contains("too"), "{tree}");
    Ok(())
}

/// After the load, `document.write` with the insertion point undefined
/// runs the document open steps (step 6.2): a new, script-created parser
/// on an empty document, whose tokenizer waits for `document.close()`'s
/// explicit "EOF" (here through a `javascript:` URL, the page's own code).
#[test]
fn write_after_load_replaces_the_document() -> Result<()> {
    let mut h = Harness::new("<p>old</p>")?;
    assert_eq!(h.load()?, Progress::Loaded);
    h.page.evaluate_javascript_url(
        "javascript:document.write('<p>new'); log(document.currentScript)",
    )?;
    assert_eq!(h.page.readiness()?, Readiness::Loading);
    let tree = h.tree()?;
    assert!(!tree.contains("old") && tree.contains("\"new\""), "{tree}");
    h.page
        .evaluate_javascript_url("javascript:document.write(' more'); document.close()")?;
    h.run()?;
    assert_eq!(h.page.readiness()?, Readiness::Complete);
    assert!(h.tree()?.contains("\"new more\""), "{}", h.tree()?);
    assert_eq!(h.logged(), ["null"]);
    Ok(())
}

// ---- javascript: URLs ----------------------------------------------------------------

/// "Evaluate a javascript: URL" steps 1 to 3: the source is the URL after
/// "javascript:", percent-decoded as UTF-8.
#[test]
fn javascript_urls() -> Result<()> {
    use clazel_web::scripting::javascript_url::{is_javascript_url, script_source};
    assert!(is_javascript_url("javascript:void 0"));
    assert!(!is_javascript_url("https://example.test/javascript:x"));
    let src: String = script_source("javascript:log('a%20b%C3%A9')")
        .unwrap_or_default()
        .into_iter()
        .filter_map(char::from_u32)
        .collect();
    assert_eq!(src, "log('a b\u{e9}')");
    let mut h = Harness::new("<p>x</p>")?;
    h.load()?;
    // No completion values yet: never a string, so no navigation.
    assert_eq!(
        h.page.evaluate_javascript_url("javascript:log('a%20b')")?,
        None
    );
    assert_eq!(
        h.page.evaluate_javascript_url("https://example.test/")?,
        None
    );
    assert_eq!(h.logged(), ["a b"]);
    Ok(())
}

// ---- Module scripts ---------------------------------------------------------------------

/// Module scripts reach the engine: an inline one is a `ParseModule`, which
/// `clazel-js` does not have yet (an engine report, and the element's
/// result is null: `error`); an external one is fetched with mode "cors"
/// and goes the same way; `nomodule` classic scripts are skipped and
/// classic scripts after them run.
#[test]
fn module_scripts_reach_the_engine() -> Result<()> {
    let mut h = Harness::new(concat!(
        "<script type=module>log('module')</script>",
        "<script type=module src=m.mjs></script>",
        "<script nomodule>log('nomodule')</script>",
        "<script>log('classic')</script>",
    ))?;
    h.files.insert(
        "https://example.test/dir/m.mjs".to_owned(),
        support::File {
            content_type: "text/javascript",
            body: "log('external module')".to_owned(),
        },
    );
    assert_eq!(h.run()?, Progress::Waiting);
    assert_eq!(h.logged(), ["classic"]);
    assert_eq!(h.requested, ["https://example.test/dir/m.mjs"]);
    assert_eq!(
        h.answer("https://example.test/dir/m.mjs")?,
        Progress::Loaded
    );
    assert_eq!(h.logged(), ["classic"]);
    let refusals = engine(&h.reports);
    assert_eq!(refusals.len(), 2, "{refusals:?}");
    assert!(
        refusals.iter().all(|r| r.contains("parse_module")),
        "{refusals:?}"
    );
    Ok(())
}

/// "Fetch a single module script" step 13.6.2: a module script served with
/// a MIME type that is not JavaScript is null, not run.
#[test]
fn a_module_with_the_wrong_mime_type_is_null() -> Result<()> {
    let mut h = Harness::new("<script type=module src=m.txt></script>")?;
    h.files.insert(
        "https://example.test/dir/m.txt".to_owned(),
        support::File {
            content_type: "text/plain",
            body: "log('no')".to_owned(),
        },
    );
    h.load()?;
    assert!(engine(&h.reports).is_empty(), "{:?}", h.reports);
    assert!(h.event_names().iter().any(|e| e.ends_with(":error")));
    Ok(())
}

// ---- performance.now() -------------------------------------------------------------------

/// `performance.now()` counts from the page's time origin, coarsened to
/// 100 µs.
#[test]
fn performance_now_is_coarsened() -> Result<()> {
    assert_eq!(coarsen_us(0), 0);
    assert_eq!(coarsen_us(99), 0);
    assert_eq!(coarsen_us(100), 100);
    assert_eq!(coarsen_us(12_345), 12_300);
    assert_eq!(performance_now_ms(1_000, 1_000), 0.0);
    assert_eq!(performance_now_ms(1_000, 2_250), 1.2);
    assert_eq!(performance_now_ms(5, 1), 0.0);
    let mut h = Harness::new("<script>var t = performance.now();</script>")?;
    if let Ok(mut now) = h.clock.0.lock() {
        *now = 123_456;
    }
    h.load()?;
    assert_eq!(h.global("t")?, "123.4");
    Ok(())
}

// ---- Encodings ------------------------------------------------------------------------------

/// HTML §13.2.3.4 "change the encoding": with a tentative confidence, a
/// `<meta charset>` naming another encoding stops the page and asks for a
/// reparse.
#[test]
fn a_meta_charset_asks_for_a_reparse() -> Result<()> {
    let mut h = Harness::with(
        "<meta charset=windows-1252><script>log('x')</script>",
        Encoding::Utf8,
        true,
    )?;
    assert_eq!(h.run()?, Progress::Reparse(Encoding::Windows1252));
    assert!(h.logged().is_empty());
    let mut certain = Harness::with(
        "<meta charset=windows-1252><script>log('x')</script>",
        Encoding::Utf8,
        false,
    )?;
    assert_eq!(certain.load()?, Progress::Loaded);
    assert_eq!(certain.logged(), ["x"]);
    Ok(())
}

// ---- html5lib scripted tree construction ---------------------------------------------

/// The html5lib tree-construction cases that need a script engine
/// (`scripted_*.dat`, vendored with the tree builder's suite at its pinned
/// WPT commit), run through the page: parsed with the scripting flag on,
/// scripts run, the tree printed in the suite's format and compared byte for
/// byte. The files are read at compile time (Miri's isolation forbids
/// reading them at run time).
const SCRIPTED: &[(&str, &str)] = &[
    (
        "scripted_adoption01.dat",
        include_str!(
            "../../clazel-treebuilder/tests/data/wpt-tree-construction/scripted_adoption01.dat"
        ),
    ),
    (
        "scripted_ark.dat",
        include_str!("../../clazel-treebuilder/tests/data/wpt-tree-construction/scripted_ark.dat"),
    ),
    (
        "scripted_foster01.dat",
        include_str!(
            "../../clazel-treebuilder/tests/data/wpt-tree-construction/scripted_foster01.dat"
        ),
    ),
    (
        "scripted_webkit01.dat",
        include_str!(
            "../../clazel-treebuilder/tests/data/wpt-tree-construction/scripted_webkit01.dat"
        ),
    ),
];

/// Expected failures, by `file:index`, with the reason.
const SCRIPTED_KNOWN: &[(&str, &str)] = &[
    (
        "scripted_adoption01.dat:0",
        "needs document.getElementById and the id setter (item 7.12's bindings)",
    ),
    (
        "scripted_ark.dat:0",
        "needs document.getElementsByTagName and setAttribute (item 7.12's bindings)",
    ),
    (
        "scripted_foster01.dat:0",
        "needs document.querySelector, Node.remove and appendChild (item 7.12's bindings)",
    ),
    (
        "scripted_foster01.dat:1",
        "needs document.querySelector, Node.remove and appendChild (item 7.12's bindings)",
    ),
];

/// The cases of one `.dat` file: (data, scripting on, expected tree).
fn dat_cases(text: &str) -> Vec<(String, bool, String)> {
    let mut cases = Vec::new();
    for block in text.split("#data\n").skip(1) {
        let mut data = Vec::new();
        let mut doc = Vec::new();
        let mut section = "data";
        let mut scripting = false;
        for line in block.lines() {
            match line {
                "#errors" | "#new-errors" | "#document-fragment" | "#script-off" => {
                    section = "skip"
                }
                "#script-on" => {
                    scripting = true;
                    section = "skip";
                }
                "#document" => section = "document",
                _ => match section {
                    "data" => data.push(line),
                    "document" if line.starts_with('|') => doc.push(line),
                    "document" => {
                        // A continuation of a multi-line text node.
                        doc.push(line);
                    }
                    _ => {}
                },
            }
        }
        while doc.last().is_some_and(|l| l.is_empty()) {
            doc.pop();
        }
        cases.push((data.join("\n"), scripting, doc.join("\n")));
    }
    cases
}

#[test]
fn html5lib_scripted() -> Result<()> {
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut total = 0usize;
    let mut failed = Vec::new();
    let mut stale = Vec::new();
    for (file, text) in SCRIPTED {
        for (index, (data, scripting, expected)) in dat_cases(text).into_iter().enumerate() {
            total += 1;
            assert!(scripting, "{file}:{index} does not name #script-on");
            let id = format!("{file}:{index}");
            let mut h = Harness::new(&data)?;
            h.load()?;
            let tree = h.tree()?;
            let tree = tree.strip_suffix('\n').unwrap_or(&tree);
            let known = SCRIPTED_KNOWN.iter().find(|(k, _)| *k == id);
            if tree == expected {
                pass += 1;
                if known.is_some() {
                    stale.push(id);
                }
            } else if known.is_some() {
                xfail += 1;
            } else {
                failed.push(format!(
                    "{id}\n--- expected\n{expected}\n--- actual\n{tree}\n--- reports {:?}",
                    h.reports
                ));
            }
        }
    }
    for f in &failed {
        println!("MISMATCH {f}\n");
    }
    for (k, why) in SCRIPTED_KNOWN {
        println!("  expected failure {k}: {why}");
    }
    println!(
        "clazel-conformance: suite=\"html5lib tree construction, scripted (WPT)\" pass={pass} xfail={xfail} fail={} total={total}",
        failed.len()
    );
    assert!(stale.is_empty(), "listed as failures but pass: {stale:?}");
    assert!(failed.is_empty(), "{} unexpected mismatches", failed.len());
    Ok(())
}

// ---- WPT execution-timing pages, with a stand-in harness ------------------------------

/// The vendored `execution-timing/` directory, as the tests' URLs see it.
const ET_DIR: &str =
    "https://wpt.test/html/semantics/scripting-1/the-script-element/execution-timing/";

macro_rules! et {
    ($name:literal) => {
        (
            $name,
            include_str!(concat!(
                "data/wpt-web/html/semantics/scripting-1/the-script-element/execution-timing/",
                $name
            )),
        )
    };
}

/// The pages run.
const ET_PAGES: &[(&str, &str)] = &[
    et!("001.html"),
    et!("002.html"),
    et!("003.html"),
    et!("004.html"),
    et!("005.html"),
    et!("006.html"),
    et!("007.html"),
    et!("008.html"),
    et!("009.html"),
    et!("010.html"),
    et!("011.html"),
    et!("028.html"),
    et!("041.html"),
    et!("067.html"),
    et!("068.html"),
    et!("085.html"),
    et!("086.html"),
    et!("087.html"),
    et!("088.html"),
    et!("089.html"),
    et!("090.html"),
];

/// The scripts they load.
const ET_SCRIPTS: &[(&str, &str)] = &[
    et!("scripts/include-1.js"),
    et!("scripts/include-2.js"),
    et!("scripts/include-3.js"),
    et!("scripts/include-4.js"),
    et!("scripts/find-foo.js"),
];

/// Pages expected to fail, with the reason.
const ET_KNOWN: &[(&str, &str)] = &[
    ("006.html", "calls eval, which the engine does not have yet"),
    (
        "028.html",
        "sets window.location (item 7.12's Location) and calls testharness.js's assert_any (not in the stand-in)",
    ),
    (
        "067.html",
        "needs getElementsByTagName, cloneNode and appendChild (item 7.12's bindings)",
    ),
    (
        "068.html",
        "its script needs getElementById (item 7.12) and the test setTimeout (timers are not on the page yet)",
    ),
];

/// The vendored `execution-timing/` pages listed in [`ET_PAGES`], run
/// through the page with their scripts served from the vendored directory.
/// `/resources/testharness.js` and `testlib/testlib.js` are served by a
/// stand-in (`tests/support/standin-testharness.js`, which says why), and
/// the `load` event's dispatch to the page's `onload` is the runner's call
/// of it once the page has loaded (item 7.12 brings event dispatch). A
/// `?pipe=trickle(dN)` script is answered after every other request
/// pending, the larger N the later. A page passes when its `t.done()` ran
/// and nothing threw. This is evidence about the scheduling only: it is
/// not a run of testharness.js.
#[test]
fn wpt_execution_timing() -> Result<()> {
    let harness = include_str!("support/standin-testharness.js");
    let mut pass = 0usize;
    let mut xfail = 0usize;
    let mut failed = Vec::new();
    let mut stale = Vec::new();
    // Under Miri every 11th page (two pages, about 130 s): each builds a
    // runtime and its built-ins, which Miri takes about 60 s for.
    let stride = if cfg!(miri) { 11 } else { 1 };
    for (name, html) in ET_PAGES.iter().step_by(stride) {
        let url = format!("{ET_DIR}{name}");
        let mut h = Harness::at(&url, html, Encoding::Utf8, false)?;
        h.files.insert(
            "https://wpt.test/resources/testharness.js".to_owned(),
            support::File {
                content_type: "text/javascript",
                body: harness.to_owned(),
            },
        );
        h.files.insert(
            "https://wpt.test/resources/testharnessreport.js".to_owned(),
            support::File {
                content_type: "text/javascript",
                body: String::new(),
            },
        );
        h.files.insert(
            format!("{ET_DIR}testlib/testlib.js"),
            support::File {
                content_type: "text/javascript",
                body: "// served by the stand-in testharness.js".to_owned(),
            },
        );
        for (path, body) in ET_SCRIPTS {
            h.files.insert(
                format!("{ET_DIR}{path}"),
                support::File {
                    content_type: "text/javascript",
                    body: (*body).to_owned(),
                },
            );
        }
        let verdict = run_et_page(&mut h)?;
        let known = ET_KNOWN.iter().find(|(k, _)| k == name);
        match (verdict, known) {
            (Ok(()), None) => pass += 1,
            (Ok(()), Some(_)) => stale.push(*name),
            (Err(_), Some(_)) => xfail += 1,
            (Err(why), None) => failed.push(format!("{name}: {why}")),
        }
    }
    for f in &failed {
        println!("FAIL {f}");
    }
    for (k, why) in ET_KNOWN {
        println!("  expected failure {k}: {why}");
    }
    println!(
        "clazel-conformance: suite=\"WPT execution-timing, stand-in harness\" pass={pass} xfail={xfail} fail={} total={}",
        failed.len(),
        ET_PAGES.len()
    );
    assert!(stale.is_empty(), "listed as failures but pass: {stale:?}");
    assert!(failed.is_empty(), "{} unexpected failures", failed.len());
    Ok(())
}

/// The N of a `?pipe=trickle(dN)` URL, or 0.
fn trickle(url: &str) -> u32 {
    url.split("trickle(d")
        .nth(1)
        .and_then(|r| r.split(')').next())
        .and_then(|n| n.parse::<u32>().ok())
        .unwrap_or(0)
}

/// Loads one page, serving trickled scripts last, then calls `onload`.
fn run_et_page(h: &mut Harness) -> Result<core::result::Result<(), String>> {
    let mut p = h.run()?;
    while p != Progress::Loaded {
        let Some(next) = h
            .pending
            .iter()
            .min_by_key(|r| trickle(&r.url))
            .map(|r| r.url.clone())
        else {
            return Ok(Err(format!(
                "stuck before load: {p:?}, reports {:?}",
                h.reports
            )));
        };
        // The server ignores the query (`?pipe=...`).
        let file = next.split('?').next().unwrap_or(&next).to_owned();
        if file != next
            && let Some(f) = h.files.get(&file).cloned()
        {
            h.files.insert(next.clone(), f);
        }
        p = h.answer(&next)?;
    }
    h.call_global("onload")?;
    let done = h.global("__done")? == "true";
    let thrown = exceptions(&h.reports);
    if done && thrown.is_empty() {
        Ok(Ok(()))
    } else {
        Ok(Err(format!(
            "done={done}, exceptions {thrown:?}, engine {:?}, log {:?}",
            engine(&h.reports),
            h.global("eventOrder")?
        )))
    }
}
