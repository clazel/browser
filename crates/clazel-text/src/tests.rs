//! Unit tests: at least one per rule of the crate docs, on documents built
//! by the real parser (`clazel-treebuilder`'s `exec::driver::parse_real`,
//! scripting off).

use super::*;
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

/// No encoding changes: the documents are already code points.
struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

fn parse(html: &str) -> Arena {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    parse_real(&NoEnc, &input, Vec::new(), false, false).0.arena
}

fn page(html: &str, width: usize) -> Page {
    layout(&parse(html), width)
}

fn lines(html: &str, width: usize) -> Vec<String> {
    page(html, width).lines
}

fn v(s: &[&str]) -> Vec<String> {
    s.iter().map(|x| (*x).to_string()).collect()
}

// Hidden (§15.3.1)

#[test]
fn head_script_style_template_are_hidden() {
    let l = lines(
        "<head><meta charset=x><style>p{}</style><script>var a</script></head>\
         <body>A<script>b()</script><style>x</style><template>T</template>B</body>",
        80,
    );
    assert_eq!(l, v(&["AB"]));
}

#[test]
fn hidden_attribute_hides() {
    assert_eq!(
        lines(
            "<p>a<span hidden>b</span>c<div hidden=until-found>d</div>",
            80
        ),
        v(&["ac"])
    );
}

#[test]
fn hidden_input_and_closed_dialog_and_datalist() {
    assert_eq!(
        lines(
            "x<input type=HIDDEN value=v><dialog>d</dialog><dialog open>o</dialog><datalist>l</datalist>y",
            80
        ),
        v(&["x", "o", "y"])
    );
}

#[test]
fn noscript_is_shown_with_scripting_off() {
    assert_eq!(lines("<body><noscript>no js</noscript>", 80), v(&["no js"]));
}

#[test]
fn title_is_the_page_title_and_not_text() {
    let p = page(
        "<title>  The \n  Title </title><title>second</title><p>body",
        80,
    );
    assert_eq!(p.title, "The Title");
    assert_eq!(p.lines, v(&["body"]));
}

#[test]
fn no_title_is_empty() {
    assert_eq!(page("<p>x", 80).title, "");
}

#[test]
fn svg_script_is_hidden_and_svg_text_is_shown() {
    assert_eq!(
        lines(
            "<svg><script>s</script><text>t</text><title>u</title></svg>",
            80
        ),
        v(&["tu"])
    );
}

// Blocks (§15.3.2, §15.3.3, §15.3.6, §15.3.7, §15.3.8)

#[test]
fn blocks_start_lines_and_inline_does_not() {
    assert_eq!(
        lines(
            "a<div>b</div>c<b>d</b><section>e<article>f</article></section><address>g</address>",
            80
        ),
        v(&["a", "b", "cd", "e", "f", "g"])
    );
}

#[test]
fn paragraphs_and_headings_get_one_empty_line() {
    assert_eq!(
        lines("<h1>Head</h1><p>one</p><p>two</p>tail<div>d</div>", 80),
        v(&["Head", "", "one", "", "two", "", "tail", "d"])
    );
}

#[test]
fn no_empty_line_at_the_top_or_end_or_twice() {
    assert_eq!(
        lines("<p></p><p>a</p><p></p><p></p><p>b</p><p></p>", 80),
        v(&["a", "", "b"])
    );
}

// Text

#[test]
fn whitespace_collapses_and_is_trimmed() {
    assert_eq!(lines("<p>  a \t\n  b  <i> c </i> </p>", 80), v(&["a b c"]));
}

#[test]
fn pre_keeps_whitespace() {
    assert_eq!(
        lines("<pre>a  b\n  c\n\nd</pre>e", 80),
        v(&["a  b", "  c", "", "d", "e"])
    );
}

#[test]
fn textarea_and_listing_keep_whitespace() {
    assert_eq!(lines("<textarea>x  y\nz</textarea>", 80), v(&["x  y", "z"]));
    assert_eq!(lines("<listing>\nl  m</listing>", 80), v(&["l  m"]));
}

#[test]
fn br_breaks_the_line() {
    assert_eq!(lines("a<br>b<br><br>c", 80), v(&["a", "b", "", "c"]));
}

#[test]
fn controls_become_replacement_characters() {
    assert_eq!(
        lines("a&#x1b;[31mb&#x7f;c", 80),
        v(&["a\u{FFFD}[31mb\u{FFFD}c"])
    );
}

// Lists, hr, tables

#[test]
fn list_items_get_markers() {
    assert_eq!(
        lines(
            "<ul><li>a<li>b</ul><ol><li>one<li>two<ul><li>in</ul><li>three</ol>",
            80
        ),
        v(&["* a", "* b", "1. one", "2. two", "* in", "3. three"])
    );
}

#[test]
fn block_in_list_item_stays_on_marker_line() {
    assert_eq!(lines("<ol><li><p>para</p></li></ol>", 80), v(&["1. para"]));
}

#[test]
fn hr_is_a_line_of_hyphens() {
    assert_eq!(lines("a<hr>b", 5), v(&["a", "-----", "b"]));
    assert_eq!(lines("<hr>", 200), v(&[&"-".repeat(HR_MAX)]));
    assert_eq!(lines("<hr>", 0), v(&[&"-".repeat(HR_MAX)]));
}

#[test]
fn table_cells_and_rows() {
    assert_eq!(
        lines(
            "<table><caption>Cap</caption><tr><th>h1<th>h2</tr><tr> <td>a</td> <td>b c</td> </tr></table>",
            80
        ),
        v(&["Cap", "h1  h2", "a  b c"])
    );
}

// Links and images

#[test]
fn links_are_numbered() {
    let p = page(
        "<a href=/x>first</a> and <a>none</a> <a href=''>e</a><iframe src=f.html>fallback</iframe>",
        80,
    );
    assert_eq!(p.lines, v(&["first[1] and none e[2][3]"]));
    assert_eq!(p.links, v(&["/x", "", "f.html"]));
}

#[test]
fn resolver_decides_what_is_a_link() {
    let doc = parse("<a href=good>a</a> <a href=bad>b</a> <a href=good2>c</a>");
    let p = layout_with(&doc, 80, |v| {
        let s: String = v.iter().filter_map(|c| char::from_u32(*c)).collect();
        if s.starts_with("good") {
            Some(format!("https://e.test/{s}"))
        } else {
            None
        }
    });
    assert_eq!(p.lines, v(&["a[1] b c[2]"]));
    assert_eq!(p.links, v(&["https://e.test/good", "https://e.test/good2"]));
}

#[test]
fn images() {
    assert_eq!(
        lines("<img alt='a cat'> <img> <img alt=''>x", 80),
        v(&["[a cat] [image] x"])
    );
}

// Wrapping

#[test]
fn wraps_on_spaces() {
    assert_eq!(lines("aaa bbb ccc dd", 7), v(&["aaa bbb", "ccc dd"]));
}

#[test]
fn long_word_is_broken_at_the_width() {
    assert_eq!(
        lines("x abcdefghij y", 4),
        v(&["x", "abcd", "efgh", "ij y"])
    );
}

#[test]
fn pre_is_broken_at_the_width() {
    assert_eq!(lines("<pre>abcdef</pre>", 4), v(&["abcd", "ef"]));
}

#[test]
fn every_scalar_value_is_one_column() {
    assert_eq!(lines("é漢字 ab", 4), v(&["é漢字", "ab"]));
}

#[test]
fn width_zero_does_not_wrap() {
    let long = "word ".repeat(100);
    let l = lines(&long, 0);
    assert_eq!(l.len(), 1);
    assert_eq!(l.first().map(|s| s.chars().count()), Some(499));
}

#[test]
fn width_one_does_not_panic_and_holds() {
    let l = lines(
        "<ol><li>ab<li><a href=x>c</a><hr><table><tr><td>a<td>b</table>",
        1,
    );
    assert!(l.iter().all(|s| s.chars().count() <= 1), "{l:?}");
}

#[test]
fn empty_document() {
    assert_eq!(page("", 80), Page::default());
}

/// A million nested `div`s, built directly in the arena (the parser is
/// slow on that many open elements): the walk is iterative. Under Miri,
/// which interprets every step, 300 (as `clazel-dom`'s depth test): the
/// walk is the same code at any depth.
#[test]
fn deep_nesting_does_not_overflow_the_stack() {
    let s = |t: &str| t.chars().map(u32::from).collect::<Vec<u32>>();
    let mut doc = Arena::new(Vec::new());
    let mut parent = 0;
    let depth: usize = if cfg!(miri) { 300 } else { 1_000_000 };
    for _ in 0..depth {
        let Some(div) = doc.create(ExecKind::Element {
            namespace: Some(Namespace::Html),
            prefix: None,
            local_name: s("div"),
            attributes: Vec::new(),
            template_contents: None,
            form_owner: None,
        }) else {
            break;
        };
        doc.append(parent, div);
        parent = div;
    }
    if let Some(t) = doc.create(ExecKind::Text { data: s("x") }) {
        doc.append(parent, t);
    }
    assert_eq!(layout(&doc, 80).lines, v(&["x"]));
}
