//! The pipeline of the 6.15 tests: HTML through the tree builder, the
//! cascade, the box tree, layout in `IdFont` (every glyph a 1em square,
//! ascent 0.8em, descent 0.2em), the editor, and `paint_with_controls`; a
//! rasteriser that turns a display list into a grid of characters (the
//! "pixels" the golden files store); and the golden file check.
//!
//! The documents use a 10px font, so a character is 10px wide and a line
//! 10px high, and each expected position is worked out by hand in the test
//! that uses it.

use std::fmt::Write as _;
use std::path::PathBuf;

use clazel_dom::exec::{Arena, ExecKind};
use clazel_forms_edit::editor::{Action, Editor, Event, Key, Outcome};
use clazel_forms_edit::geometry::LayoutGeometry;
use clazel_layout::boxes::dump::dump as dump_boxes;
use clazel_layout::boxes::{BoxTree, build};
use clazel_layout::flow::{
    BoxFont, FontMetrics, FragmentTree, ShapedGlyph, TextFns, Viewport, layout,
};
use clazel_layout::paint::dump::dump as dump_list;
use clazel_layout::paint::{DisplayList, Item, Target, paint_with_controls};
use clazel_style::cascade::{cascade_with, ua};
use clazel_style::sources::{Device, StyleSheet, collect};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

/// `BoxFont`'s metrics and advances, but glyph id = the character's code, so
/// that a test can tell what was drawn (a bullet from a letter).
#[derive(Debug, Clone, Copy, Default)]
pub struct IdFont;

impl TextFns for IdFont {
    fn metrics(&self, style: &clazel_style::cascade::computed::ComputedStyle) -> FontMetrics {
        BoxFont.metrics(style)
    }

    fn shape(
        &self,
        style: &clazel_style::cascade::computed::ComputedStyle,
        text: &str,
    ) -> Vec<ShapedGlyph> {
        text.char_indices()
            .map(|(cluster, c)| ShapedGlyph {
                face: 0,
                id: u16::try_from(u32::from(c)).unwrap_or(0xFFFF),
                cluster,
                advance: style.font_size.max(0),
                x_offset: 0,
                y_offset: 0,
            })
            .collect()
    }
}

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

/// The user agent sheet of these tests: `display` only (as item 5.16's
/// tests), plus the controls' own: inline blocks, and no box for a Hidden
/// input.
const UA: &str = "html, body, div, p, form { display: block }
head, style, script, title { display: none }
input, button { display: inline-block }
input[type=hidden i] { display: none !important }";

pub const STD: &str = "<!DOCTYPE html><style>html { font-size: 10px } body { margin: 0 }</style>";

/// A laid-out document with an editor.
pub struct Page {
    pub arena: Arena,
    pub tree: BoxTree,
    pub frags: FragmentTree,
    pub table: clazel_style::cascade::ComputedTable,
    pub editor: Editor,
}

pub fn u32s(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

impl Page {
    /// `body` in no-quirks mode, 300 by 120.
    pub fn new(body: &str) -> Page {
        Page::sized(body, 300, 120)
    }

    pub fn sized(body: &str, width: u16, height: u16) -> Page {
        let html = format!("{STD}{body}");
        let arena = parse_real(&NoEncodings, &u32s(&html), Vec::new(), false, false)
            .0
            .arena;
        let sources = collect(&arena);
        let sheets = ua::Sheets {
            ua: StyleSheet::parse(&u32s(UA)),
            ua_quirks: StyleSheet::parse(&[]),
            hints: StyleSheet::parse(&[]),
        };
        let table = cascade_with(
            &sheets,
            &arena,
            &sources,
            Device::screen(u32::from(width), u32::from(height)),
        );
        let tree = build(&arena, &table);
        let frags = layout(&tree, &arena, &table, &IdFont, Viewport::px(width, height));
        let editor = Editor::new(&arena);
        Page {
            arena,
            tree,
            frags,
            table,
            editor,
        }
    }

    /// The node of the element with `id`.
    pub fn id(&self, id: &str) -> usize {
        let want = u32s(id);
        let mut stack = vec![0usize];
        while let Some(n) = stack.pop() {
            if let ExecKind::Element { attributes, .. } = self.arena.kind(n)
                && attributes
                    .iter()
                    .any(|a| a.namespace.is_none() && a.local_name == u32s("id") && a.value == want)
            {
                return n;
            }
            stack.extend(self.arena.children(n).iter().rev());
        }
        unreachable!("no element with id {id}")
    }

    /// The border box of the element with `id`, in whole CSS pixels:
    /// `(x, y, width, height)`.
    pub fn rect(&self, id: &str) -> (i32, i32, i32, i32) {
        let n = self.id(id);
        match clazel_layout::controls::border_box_of(&self.frags, &self.tree, n) {
            Some(r) => (r.x / 64, r.y / 64, r.width / 64, r.height / 64),
            None => unreachable!("{id} has no box"),
        }
    }

    pub fn send(&mut self, e: Event) -> Outcome {
        let geo = LayoutGeometry::new(&self.frags, &self.tree, &self.arena, &self.table, &IdFont);
        self.editor.handle(&self.arena, &geo, e)
    }

    pub fn text(&mut self, s: &str) -> Outcome {
        self.send(Event::Text(s.to_owned()))
    }

    pub fn key(&mut self, key: Key) -> Outcome {
        self.send(Event::Key { key, shift: false })
    }

    pub fn shift(&mut self, key: Key) -> Outcome {
        self.send(Event::Key { key, shift: true })
    }

    /// A click at (`x`, `y`).
    pub fn click(&mut self, x: i32, y: i32) -> Outcome {
        let o = self.send(Event::Press { x, y, shift: false });
        self.send(Event::Release);
        o
    }

    /// A click in the middle of element `id`'s box, `dx` pixels from its
    /// left edge when given.
    pub fn click_in(&mut self, id: &str, dx: Option<i32>) -> Outcome {
        let (x, y, w, h) = self.rect(id);
        self.click(
            x.saturating_add(dx.unwrap_or(w / 2)),
            y.saturating_add(h / 2),
        )
    }

    pub fn focus_id(&self) -> Option<String> {
        let n = self.editor.focus()?;
        match self.arena.kind(n) {
            ExecKind::Element { attributes, .. } => attributes
                .iter()
                .find(|a| a.local_name == u32s("id"))
                .map(|a| a.value.iter().filter_map(|&c| char::from_u32(c)).collect()),
            _ => None,
        }
    }

    /// The value of the control with `id`, as the editor shows it.
    pub fn value(&self, id: &str) -> String {
        self.editor.view(&self.arena, self.id(id)).value
    }

    pub fn paint(&self) -> DisplayList {
        let views = self.editor.views(&self.arena);
        paint_with_controls(
            &self.frags,
            &self.tree,
            &self.arena,
            &self.table,
            &IdFont,
            Target {
                base: None,
                scale: 1,
            },
            &views,
        )
    }

    /// The display list printed.
    pub fn list(&self) -> String {
        dump_list(&self.paint())
    }

    /// The box tree printed.
    pub fn boxes(&self) -> String {
        dump_boxes(&self.tree, &self.arena)
    }

    /// The page as a grid of characters (`raster`), clipped to the rows and
    /// columns given: `(x, y, width, height)`.
    pub fn pixels(&self, x: i32, y: i32, w: i32, h: i32) -> String {
        raster(&self.paint(), (x, y, w, h))
    }

    pub fn entries(&self, form: &str) -> Vec<(String, String)> {
        use clazel_forms::exec::fields::construct_entry_list_exec;
        let f = self.id(form);
        let enc = u32s("UTF-8");
        let text = |v: &[u32]| -> String { v.iter().filter_map(|&c| char::from_u32(c)).collect() };
        construct_entry_list_exec(&self.arena, self.editor.rows(), f, None, &enc, false)
            .unwrap_or_default()
            .iter()
            .map(|e| (text(&e.name), text(&e.value)))
            .collect()
    }
}

/// What a submission `action` is: `submit <form id> by <submitter id>`,
/// `refused <form id> focus <control id>`, or `none`.
pub fn action(p: &Page, a: &Action) -> String {
    let id = |n: usize| -> String {
        match p.arena.kind(n) {
            ExecKind::Element { attributes, .. } => attributes
                .iter()
                .find(|x| x.local_name == u32s("id"))
                .map(|x| x.value.iter().filter_map(|&c| char::from_u32(c)).collect())
                .unwrap_or_else(|| "?".to_owned()),
            _ => "?".to_owned(),
        }
    };
    match a {
        Action::None => "none".to_owned(),
        Action::Submit { form, submitter } => format!("submit {} by {}", id(*form), id(*submitter)),
        Action::Refused { form, focus } => format!("refused {} focus {}", id(*form), id(*focus)),
    }
}

/// The character of an opaque premultiplied colour in the grid.
fn glyph(c: u32) -> char {
    match c & 0x00FF_FFFF {
        0xFFFFFF => '.',
        0x767676 => 'o',
        0x000000 => '#',
        0x0060DF => 'B',
        0xEFEFEF => '-',
        0xE9E9ED => ':',
        0xB3D4FF => 's',
        0x3875D7 => 'H',
        0x757575 => 'p',
        0x6D6D6D => 'd',
        _ => '?',
    }
}

/// A display list drawn at scale 1 into a grid of characters, over the
/// region `(x, y, w, h)`: a fill is its colour's character, text is the
/// boxes `IdFont` draws (each glyph the middle of an em square, 0.8em above the baseline
/// and 0.2em below it), inside the clip in force. Rows end in `|`.
pub fn raster(list: &DisplayList, region: (i32, i32, i32, i32)) -> String {
    let (rx, ry, rw, rh) = region;
    let cols = usize::try_from(rw).unwrap_or(0);
    let rows = usize::try_from(rh).unwrap_or(0);
    let mut grid = vec![vec!['?'; cols]; rows];
    let mut clip: Option<(i64, i64, i64, i64)> = None;
    let plot = |grid: &mut Vec<Vec<char>>,
                clip: Option<(i64, i64, i64, i64)>,
                x0: i64,
                y0: i64,
                x1: i64,
                y1: i64,
                c: char| {
        for y in y0..y1 {
            for x in x0..x1 {
                if let Some((cx0, cy0, cx1, cy1)) = clip
                    && (x < cx0 || x >= cx1 || y < cy0 || y >= cy1)
                {
                    continue;
                }
                let (gx, gy) = (
                    x.saturating_sub(i64::from(rx)),
                    y.saturating_sub(i64::from(ry)),
                );
                if gx < 0 || gy < 0 {
                    continue;
                }
                if let Some(cell) = usize::try_from(gy)
                    .ok()
                    .and_then(|r| grid.get_mut(r))
                    .and_then(|row| row.get_mut(usize::try_from(gx).unwrap_or(usize::MAX)))
                {
                    *cell = c;
                }
            }
        }
    };
    for item in &list.items {
        match item {
            Item::Fill { rect, colour } => plot(
                &mut grid,
                clip,
                i64::from(rect.x),
                i64::from(rect.y),
                rect.right(),
                rect.bottom(),
                glyph(*colour),
            ),
            Item::Text { run, .. } => {
                let size = i64::from(run.size) / 64;
                for g in &run.glyphs {
                    let (x, base) = (i64::from(g.x) / 64, i64::from(g.y) / 64);
                    // The em square, drawn as its middle three fifths so
                    // that what is behind the text and between glyphs shows.
                    let (top, pad) = (base.saturating_sub(size.saturating_mul(4) / 5), size / 5);
                    plot(
                        &mut grid,
                        clip,
                        x.saturating_add(pad),
                        top.saturating_add(pad),
                        x.saturating_add(size).saturating_sub(pad),
                        top.saturating_add(size).saturating_sub(pad),
                        glyph(run.colour),
                    );
                }
            }
            Item::PushClip { rect } => {
                clip = Some((
                    i64::from(rect.x),
                    i64::from(rect.y),
                    rect.right(),
                    rect.bottom(),
                ));
            }
            Item::PopClip => clip = None,
        }
    }
    let mut out = String::new();
    for row in grid {
        out.extend(row);
        let _ = writeln!(out, "|");
    }
    out
}

fn golden_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("golden")
        .join(name)
}

/// Compares `actual` with the stored file `tests/golden/<name>`; with
/// `CLAZEL_BLESS=1` it writes the file instead (review the diff before
/// committing it).
pub fn golden(name: &str, actual: &str) {
    let path = golden_path(name);
    if std::env::var_os("CLAZEL_BLESS").is_some() {
        if let Some(dir) = path.parent() {
            let _ = std::fs::create_dir_all(dir);
        }
        let _ = std::fs::write(&path, actual);
        return;
    }
    let stored = std::fs::read_to_string(&path).unwrap_or_default();
    assert_eq!(
        stored.replace("\r\n", "\n"),
        actual,
        "golden {name} differs (CLAZEL_BLESS=1 to regenerate)"
    );
}
