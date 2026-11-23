// scripts/phase6-inventory.mjs: phase-6.md item 6.1's inventory (the Phase 6
// counterpart of phase-5.md item 5.1's inventory, whose script was never
// written: `scripts/` held no such file when 6.1 was built).
//
// Run locally, never in CI:  node scripts/phase6-inventory.mjs [url ...]
// With no arguments it measures the pages 6.1 names. It prints counts and
// shapes as Markdown on stdout and stores nothing: the pages, sheets and
// images are copyrighted (Y Combinator's, its users', Wikipedia's authors'),
// so no byte of them is written to disk. It sends plain GET requests, never
// logs in, posts or votes; a page behind a login redirects to the login page
// and is counted as that.
//
// Counting uses regular expressions over the HTML, which is adequate for
// counting on the pages measured and would not be for anything shipped
// (CLAUDE.md rule 8 is about shipped code: this script never ships).

const UA = "clazel-inventory/1 (counts only; contact via the repository)";
const DEFAULT_PAGES = [
  "https://news.ycombinator.com/",
  "https://news.ycombinator.com/login",
];

async function get(url) {
  const res = await fetch(url, { headers: { "user-agent": UA }, redirect: "follow" });
  const bytes = new Uint8Array(await res.arrayBuffer());
  return { url: res.url, status: res.status, type: res.headers.get("content-type") ?? "", bytes };
}

const text = (b) => new TextDecoder("utf-8", { fatal: false }).decode(b);

// Sniff by signature (the byte patterns of MIME Sniffing §6.1, for counting).
function sniff(b) {
  const at = (i, s) => [...s].every((c, k) => b[i + k] === c.charCodeAt(0));
  if (at(0, "GIF87a") || at(0, "GIF89a")) return "gif";
  if (b[0] === 0x89 && at(1, "PNG")) return "png";
  if (b[0] === 0xff && b[1] === 0xd8 && b[2] === 0xff) return "jpeg";
  if (at(0, "RIFF") && at(8, "WEBP")) return "webp";
  if (b[0] === 0 && b[1] === 0 && b[2] === 1 && b[3] === 0) return "ico";
  if (at(0, "BM")) return "bmp";
  const head = text(b.subarray(0, 512)).trimStart();
  if (/^(<\?xml[^>]*>\s*)?(<!--[\s\S]*?-->\s*)?<svg[\s>]/i.test(head)) return "svg";
  return "other";
}

const extOf = (u) => {
  try {
    const m = new URL(u).pathname.match(/\.([a-z0-9]+)$/i);
    return m ? m[1].toLowerCase() : "(none)";
  } catch {
    return "(bad url)";
  }
};

const bump = (o, k, n = 1) => (o[k] = (o[k] ?? 0) + n);
const fmt = (o) =>
  Object.entries(o).sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k}: ${v}`).join(", ") || "none";

function attrs(tag) {
  const out = {};
  for (const m of tag.matchAll(/([a-zA-Z_:][-a-zA-Z0-9_:.]*)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+)))?/g)) {
    if (m.index === 0) continue;
    if (m[1].toLowerCase() === tag.slice(1).match(/^[a-zA-Z0-9]+/)[0].toLowerCase() && m.index === 1) continue;
    out[m[1].toLowerCase()] = m[2] ?? m[3] ?? m[4] ?? "";
  }
  return out;
}

async function measure(pageUrl) {
  const page = await get(pageUrl);
  const html = text(page.bytes);
  const r = [`### ${pageUrl}${page.url !== pageUrl ? ` (redirected to ${page.url})` : ""}`, ""];
  r.push(`- status ${page.status}, ${page.bytes.length} bytes, content-type \`${page.type}\``);

  // img elements
  const imgs = [...html.matchAll(/<img\b[^>]*>/gi)].map((m) => attrs(m[0]));
  const byExt = {}, attrCount = {}, sizes = {};
  for (const a of imgs) {
    bump(byExt, extOf(new URL(a.src ?? "", page.url).href));
    for (const k of Object.keys(a)) bump(attrCount, k);
    bump(sizes, `${a.width ?? "-"}x${a.height ?? "-"}`);
  }
  r.push(`- \`img\` elements: ${imgs.length}; by URL extension: ${fmt(byExt)}`);
  r.push(`- \`img\` attributes: ${fmt(attrCount)}`);
  r.push(`- \`img\` width x height attribute shapes: ${fmt(sizes)}`);
  r.push(`- \`srcset\`: ${imgs.filter((a) => "srcset" in a).length} on img, ${(html.match(/<source\b/gi) ?? []).length} \`source\`, ${(html.match(/<picture\b/gi) ?? []).length} \`picture\``);
  r.push(`- inline \`<svg>\`: ${(html.match(/<svg\b/gi) ?? []).length}; \`<object>\`/\`<embed>\`/\`<canvas>\`/\`<video>\`/\`<audio>\`: ${["object", "embed", "canvas", "video", "audio"].map((t) => (html.match(new RegExp(`<${t}\\b`, "gi")) ?? []).length).join("/")}`);
  r.push(`- inline \`style\` attributes with \`url(\`: ${(html.match(/style\s*=\s*"[^"]*url\(/gi) ?? []).length}; \`<link rel=icon>\`: ${(html.match(/<link\b[^>]*rel\s*=\s*["']?(?:shortcut )?icon/gi) ?? []).length}`);

  // sheets and their url() uses
  const sheets = [...html.matchAll(/<link\b[^>]*>/gi)].map((m) => attrs(m[0])).filter((a) => /stylesheet/i.test(a.rel ?? ""));
  const sheetTexts = [...html.matchAll(/<style\b[^>]*>([\s\S]*?)<\/style>/gi)].map((m) => ({ name: "(inline)", css: m[1] }));
  for (const s of sheets) {
    const u = new URL(s.href, page.url).href;
    sheetTexts.push({ name: u, css: text((await get(u)).bytes) });
  }
  const bgUses = [], urlExts = {}, bgProps = {};
  const assetUrls = new Set();
  for (const { name, css } of sheetTexts) {
    for (const m of css.matchAll(/([a-z-]*background[a-z-]*|list-style-image|content|cursor|border-image[a-z-]*)\s*:\s*([^;}]*url\([^)]*\)[^;}]*)/gi)) {
      bump(bgProps, m[1].toLowerCase());
      const u = m[2].match(/url\(\s*["']?([^"')]+)/i);
      if (u) {
        bump(urlExts, extOf(new URL(u[1], name.startsWith("http") ? name : page.url).href));
        if (!u[1].startsWith("data:")) assetUrls.add(new URL(u[1], name.startsWith("http") ? name : page.url).href);
      }
      bgUses.push(m[0]);
    }
  }
  r.push(`- style sheets: ${sheetTexts.length} (${sheetTexts.map((s) => `${s.name.startsWith("http") ? "linked" : "inline"} ${s.css.length} bytes`).join(", ")})`);
  r.push(`- CSS declarations holding \`url()\`: ${bgUses.length}; by property: ${fmt(bgProps)}; by URL extension: ${fmt(urlExts)}`);
  r.push(`- \`background-repeat\`/\`background-position\`/\`background-size\` in sheets: ${sheetTexts.map((s) => (s.css.match(/background-repeat/g) ?? []).length).reduce((a, b) => a + b, 0)}/${sheetTexts.map((s) => (s.css.match(/background-position/g) ?? []).length).reduce((a, b) => a + b, 0)}/${sheetTexts.map((s) => (s.css.match(/background-size/g) ?? []).length).reduce((a, b) => a + b, 0)}; gradients: ${sheetTexts.map((s) => (s.css.match(/-gradient\(/g) ?? []).length).reduce((a, b) => a + b, 0)}`);

  // fetch each distinct image once, sniff, and for SVG count elements
  const distinct = new Set(imgs.map((a) => a.src).filter(Boolean).map((s) => new URL(s, page.url).href));
  for (const u of assetUrls) distinct.add(u);
  const sniffed = {}, mismatch = [], svgs = [];
  for (const u of [...distinct].slice(0, 40)) {
    try {
      const f = await get(u);
      const kind = sniff(f.bytes);
      bump(sniffed, kind);
      if (kind !== extOf(u) && !(kind === "jpeg" && extOf(u) === "jpg")) mismatch.push(`${extOf(u)}->${kind}`);
      if (kind === "svg") {
        const s = text(f.bytes);
        const els = {}, atts = {};
        for (const m of s.matchAll(/<([a-zA-Z][-a-zA-Z0-9:]*)\b([^>]*)>/g)) {
          bump(els, m[1]);
          for (const a of m[2].matchAll(/([a-zA-Z:][-a-zA-Z0-9:]*)\s*=/g)) bump(atts, a[1]);
        }
        svgs.push(`  - \`${extOf(u) === "svg" ? new URL(u).pathname.split("/").pop() : u}\`, ${f.bytes.length} bytes; elements: ${fmt(els)}; attributes: ${fmt(atts)}`);
      }
    } catch (e) {
      bump(sniffed, "fetch-failed");
    }
  }
  r.push(`- distinct image URLs fetched (img src plus CSS url(), at most 40): ${distinct.size}; by sniffed signature: ${fmt(sniffed)}; extension/signature disagreements: ${mismatch.join(", ") || "none"}`);
  if (svgs.length) r.push(`- SVG files:`, ...svgs);

  // forms
  const forms = [...html.matchAll(/<form\b[^>]*>([\s\S]*?)<\/form>/gi)];
  r.push(`- forms: ${forms.length}`);
  for (const m of forms) {
    const fa = attrs(m[0].slice(0, m[0].indexOf(">") + 1));
    const ctl = {};
    for (const c of m[1].matchAll(/<(input|textarea|select|button)\b[^>]*>/gi)) {
      const ca = attrs(c[0]);
      bump(ctl, c[1].toLowerCase() === "input" ? `input[${(ca.type ?? "text").toLowerCase()}]` : c[1].toLowerCase());
    }
    r.push(`  - method=${fa.method ?? "(default get)"}, enctype=${fa.enctype ?? "(default)"}, action=${fa.action === undefined ? "(none)" : /^[a-z]+:/i.test(fa.action) ? "absolute URL" : `relative \`${fa.action.replace(/[?&=].*/, "")}\``}, other attributes: ${Object.keys(fa).filter((k) => !["method", "enctype", "action"].includes(k)).join(", ") || "none"}; controls: ${fmt(ctl)}`);
  }
  const strayControls = (html.match(/<(input|textarea|select|button)\b/gi) ?? []).length;
  r.push(`- all form controls on the page, owned or not: ${strayControls}`);
  r.push("");
  return r.join("\n");
}

const pages = process.argv.length > 2 ? process.argv.slice(2) : DEFAULT_PAGES;
console.log(`## Inventory, run ${new Date().toISOString().slice(0, 10)}\n`);
for (const p of pages) {
  try {
    console.log(await measure(p));
  } catch (e) {
    console.log(`### ${p}\n\n- failed: ${e.message}\n`);
  }
}
