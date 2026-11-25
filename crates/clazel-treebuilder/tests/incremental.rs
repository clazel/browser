//! The incremental driver (`exec::incremental`, Phase 7 item 7.15) as a
//! script host drives it: pausing for "prepare the script element",
//! inserting text at the insertion point as `document.write` does, and a
//! script-created parser that waits for its explicit "EOF" character. The
//! scripts themselves are `clazel-web`'s; here the host's edits are made by
//! hand, with the trees the html5lib `scripted_webkit01.dat` cases give.

#[path = "support/dump.rs"]
mod dump;

use clazel_treebuilder::exec::incremental::{Incremental, Pause};
use clazel_treebuilder::exec::types::{EncFnsExec, ExecAction};

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn u32s(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Pumps until the next `ScriptReady`, the insertion point or the stop.
fn next(p: &mut Incremental) -> Pause {
    loop {
        match p.pump(&NoEnc) {
            Pause::Actions(a) if !a.iter().any(|x| matches!(x, ExecAction::ScriptReady(_))) => {}
            other => return other,
        }
    }
}

fn tree(p: &Incremental) -> String {
    dump::dump_children(&p.parser().arena, 0)
}

/// `1<script>document.write("2")</script>3` (scripted_webkit01.dat case 0):
/// the parser pauses after `</script>`, the "script" inserts "2" at the
/// insertion point (just before "3"), the parser runs to the insertion
/// point, the insertion point becomes undefined again, and the rest is
/// parsed.
#[test]
fn a_write_is_parsed_before_the_rest() {
    let mut p = Incremental::new(Vec::new(), true, false, &u32s("1<script>x</script>3"), true);
    assert!(matches!(next(&mut p), Pause::Actions(_)));
    let old = p.insertion_point();
    p.set_insertion_point_to_next();
    assert!(p.insert(&u32s("2")));
    assert!(matches!(next(&mut p), Pause::InsertionPoint));
    p.set_insertion_point(old);
    assert!(matches!(next(&mut p), Pause::Stopped));
    assert_eq!(
        tree(&p),
        "| <html>\n|   <head>\n|   <body>\n|     \"1\"\n|     <script>\n|       \"x\"\n|     \"23\"\n"
    );
}

/// Two writes in one script: the second goes after the first (the
/// insertion point moved past the first's text), and a tag split across
/// them is one tag, since the tokenizer waits at the insertion point.
#[test]
fn writes_follow_one_another_and_a_tag_may_span_them() {
    let mut p = Incremental::new(Vec::new(), true, false, &u32s("<script>x</script>!"), true);
    assert!(matches!(next(&mut p), Pause::Actions(_)));
    p.set_insertion_point_to_next();
    assert!(p.insert(&u32s("<b")));
    assert!(matches!(next(&mut p), Pause::InsertionPoint));
    assert!(p.insert(&u32s(">bold</b>")));
    assert!(matches!(next(&mut p), Pause::InsertionPoint));
    p.set_insertion_point(None);
    assert!(matches!(next(&mut p), Pause::Stopped));
    assert_eq!(
        tree(&p),
        "| <html>\n|   <head>\n|     <script>\n|       \"x\"\n|   <body>\n|     <b>\n|       \"bold\"\n|     \"!\"\n"
    );
}

/// With the insertion point undefined there is nowhere to write.
#[test]
fn no_insertion_point_no_write() {
    let mut p = Incremental::new(Vec::new(), true, false, &u32s("a"), true);
    assert!(!p.insert(&u32s("b")));
    assert!(matches!(next(&mut p), Pause::Stopped));
}

/// A script-created parser (`document.open`): its input is not closed, so
/// the tokenizer waits at the end of what was written, and only the
/// explicit "EOF" character (`document.close`) ends the document.
#[test]
fn a_script_created_parser_waits_for_close() {
    let mut p = Incremental::new(Vec::new(), true, false, &[], false);
    p.set_insertion_point_to_next();
    assert!(p.insert(&u32s("<p>one")));
    assert!(matches!(next(&mut p), Pause::InsertionPoint));
    assert!(!p.stopped());
    assert!(p.insert(&u32s(" two")));
    assert!(matches!(next(&mut p), Pause::InsertionPoint));
    p.close();
    p.set_insertion_point(None);
    assert!(matches!(next(&mut p), Pause::Stopped));
    assert_eq!(
        tree(&p),
        "| <html>\n|   <head>\n|   <body>\n|     <p>\n|       \"one two\"\n"
    );
}

/// Newlines in written text are normalized (§13.2.3.5), CR LF to LF.
#[test]
fn written_text_is_preprocessed() {
    let mut p = Incremental::new(Vec::new(), true, false, &u32s("<pre>"), false);
    assert!(matches!(next(&mut p), Pause::InsertionPoint));
    p.set_insertion_point_to_next();
    assert!(p.insert(&u32s("a\r\nb\rc")));
    p.close();
    p.set_insertion_point(None);
    assert!(matches!(next(&mut p), Pause::Stopped));
    assert_eq!(
        tree(&p),
        "| <html>\n|   <head>\n|   <body>\n|     <pre>\n|       \"a\nb\nc\"\n"
    );
}
