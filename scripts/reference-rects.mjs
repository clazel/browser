// scripts/reference-rects.mjs: the reference engine's side of phase-5.md
// item 5.25's geometry comparison.
//
// *** THIS SCRIPT HAS NEVER BEEN RUN. ***
// It was written on 2026-11-13 without downloading or starting a browser.
// Expect to fix it the first time it is run. Run it locally, never in CI.
//
// What it does: load one page in a pinned headless Chrome at 800 by 600, scale 1,
// with the repository's font files as the generic families, then write
//   - <out>.json: every element's and text node's client rectangles, in the
//     schema `clazel-client-rects/1` that `crates/clazel-layout/src/rects.rs`
//     states (the one place the schema is defined), with the browser's name,
//     version and the date;
//   - <out>.png: a screenshot of the viewport.
// `clazel_layout::rects::from_json` reads the JSON and `rects::compare` compares
// it with ours (2 px in position, 2 % in width).
//
// Pinned versions (change them deliberately, and record the change):
//   - Chrome for Testing 131.0.6778.85 (headless shell), installed with
//     `npx @puppeteer/browsers@2.6.1 install chrome-headless-shell@131.0.6778.85`;
//   - puppeteer-core 23.10.4 (`npm install puppeteer-core@23.10.4`), which drives it.
// Neither is a dependency of the workspace or of CI.
//
// Fonts: the generic families are mapped to the same files our tests use
// (crates/clazel-font/tests/data/: DejaVu Serif for serif, sans-serif and
// monospace as Generics::for_os(Os::Linux) falls back, and Source Serif 4). On
// Linux, FONTCONFIG_FILE points Chrome at a fonts.conf that lists only that
// directory, so no system font is used; the DevTools protocol's
// Page.setFontFamilies then names the families.
//
// Usage:
//   FONTCONFIG_FILE=$(node scripts/reference-rects.mjs --fonts-conf) \
//   node scripts/reference-rects.mjs --chrome PATH --url http://127.0.0.1:8000/ --out target/reference/fixture
//
// The page is served by any static server over the fixture's directory
// (crates/clazel/tests/fixtures/hn/), so its linked sheet loads as it would
// for us once item 5.19's fetches are wired.

import { writeFileSync, mkdirSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const FONT_DIR = resolve(ROOT, "crates/clazel-font/tests/data");
const WIDTH = 800;
const HEIGHT = 600;

function arg(name) {
  const i = process.argv.indexOf(name);
  return i >= 0 ? process.argv[i + 1] : undefined;
}

// A fonts.conf listing only the repository's font files; prints its path.
if (process.argv.includes("--fonts-conf")) {
  const conf = resolve(ROOT, "target/reference/fonts.conf");
  mkdirSync(dirname(conf), { recursive: true });
  writeFileSync(
    conf,
    `<?xml version="1.0"?>\n<!DOCTYPE fontconfig SYSTEM "fonts.dtd">\n` +
      `<fontconfig><dir>${FONT_DIR}</dir><cachedir>${dirname(conf)}/cache</cachedir></fontconfig>\n`,
  );
  console.log(conf);
  process.exit(0);
}

const chrome = arg("--chrome");
const url = arg("--url");
const out = arg("--out");
if (!chrome || !url || !out) {
  console.error("usage: reference-rects.mjs --chrome PATH --url URL --out PREFIX");
  process.exit(64);
}

const puppeteer = (await import("puppeteer-core")).default;
const browser = await puppeteer.launch({
  executablePath: chrome,
  headless: "shell",
  args: ["--force-device-scale-factor=1", "--font-render-hinting=none", "--disable-gpu"],
});
const page = await browser.newPage();
await page.setViewport({ width: WIDTH, height: HEIGHT, deviceScaleFactor: 1 });
const cdp = await page.createCDPSession();
await cdp.send("Page.setFontFamilies", {
  fontFamilies: {
    standard: "DejaVu Serif",
    serif: "DejaVu Serif",
    sansSerif: "DejaVu Serif",
    fixed: "DejaVu Serif",
  },
});
await page.goto(url, { waitUntil: "load" });

// Every node's client rectangles, in tree order, in the schema.
const rects = await page.evaluate(() => {
  const out = [];
  const sx = window.scrollX;
  const sy = window.scrollY;
  const walk = [[document, ""]];
  while (walk.length > 0) {
    const [node, path] = walk.pop();
    if (node.nodeType === Node.ELEMENT_NODE || node.nodeType === Node.TEXT_NODE) {
      let list;
      if (node.nodeType === Node.ELEMENT_NODE) {
        list = node.getClientRects();
      } else {
        const range = document.createRange();
        range.selectNodeContents(node);
        list = range.getClientRects();
      }
      let i = 0;
      for (const r of list) {
        const rect = {
          node: path,
          kind: node.nodeType === Node.ELEMENT_NODE ? "element" : "text",
          i,
          x: r.left + sx,
          y: r.top + sy,
          w: r.width,
          h: r.height,
        };
        if (node.nodeType === Node.ELEMENT_NODE) rect.name = node.localName;
        out.push(rect);
        i += 1;
      }
    }
    const kids = node.childNodes;
    for (let k = kids.length - 1; k >= 0; k -= 1) {
      walk.push([kids[k], path === "" ? String(k) : `${path}/${k}`]);
    }
  }
  return out;
});

const json = {
  schema: "clazel-client-rects/1",
  engine: {
    name: "chrome",
    version: await browser.version(),
    date: new Date().toISOString().slice(0, 10),
  },
  viewport: { width: WIDTH, height: HEIGHT, scale: 1 },
  rects,
};
mkdirSync(dirname(resolve(out)), { recursive: true });
writeFileSync(`${out}.json`, JSON.stringify(json, null, 1) + "\n");
await page.screenshot({ path: `${out}.png`, fullPage: false });
await browser.close();
console.log(`wrote ${out}.json (${rects.length} rectangles) and ${out}.png`);
