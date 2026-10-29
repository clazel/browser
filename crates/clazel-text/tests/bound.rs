//! The bound of the crate docs ("The bound") on generated documents: tag
//! soup drawn from the elements the layout treats specially, attributes,
//! whitespace, character references and controls, parsed by the real
//! parser and laid out at several widths, 0 and 1 included. Each layout
//! must not panic, must keep both inequalities, and must have no line
//! longer than a non-zero width. The generator is a fixed linear
//! congruential sequence, so the documents are the same on every run.

mod support;

/// The pieces documents are made of.
const PIECES: &[&str] = &[
    "<p>",
    "</p>",
    "<h2>",
    "</h2>",
    "<div>",
    "</div>",
    "<pre>",
    "</pre>",
    "<textarea>",
    "</textarea>",
    "<listing>",
    "<br>",
    "<hr>",
    "<ol>",
    "</ol>",
    "<ul>",
    "</ul>",
    "<li>",
    "<table>",
    "<tr>",
    "<td>",
    "<th>",
    "</table>",
    "<caption>",
    "<a href=x>",
    "<a href=''>",
    "</a>",
    "<a>",
    "<iframe src=f>",
    "</iframe>",
    "<img>",
    "<img alt=''>",
    "<img alt='a b'>",
    "<span hidden>",
    "</span>",
    "<script>s</script>",
    "<style>t</style>",
    "<title>T </title>",
    "<template>",
    "</template>",
    "<noscript>",
    "<input type=hidden>",
    "<dialog>",
    "<svg>",
    "</svg>",
    "<math>",
    "<b>",
    "</b>",
    "<i>",
    " ",
    "  ",
    "\n",
    "\t",
    "&#12;",
    "&#x1b;",
    "word",
    "longerwordthanthewidth",
    "x",
    "é",
    "漢",
    "&amp;",
    "<!-- c -->",
    "<plaintext>",
];

/// A deterministic sequence (Knuth's MMIX constants).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
}

#[test]
fn bound_holds_on_generated_documents() {
    let mut rng = Lcg(0x5eed);
    let mut failures: Vec<String> = Vec::new();
    for doc_no in 0..400u32 {
        let len = usize::try_from(rng.next() % 120).unwrap_or(0);
        let mut html = String::new();
        for _ in 0..len {
            let i = usize::try_from(rng.next()).unwrap_or(0) % PIECES.len();
            html.push_str(PIECES.get(i).copied().unwrap_or(""));
        }
        let doc = support::parse(&html);
        for width in [0usize, 1, 2, 3, 7, 40, 80, 200] {
            let page = clazel_text::layout(&doc, width);
            if let Err(e) = support::check_bound(&doc, &page, width) {
                failures.push(format!("doc {doc_no} width {width}: {e}\n{html:?}"));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
