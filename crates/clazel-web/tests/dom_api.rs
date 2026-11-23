//! The DOM API through the generated bindings (phase-7.md item 7.13):
//! `innerHTML` and `outerHTML` with fragment parsing, `insertAdjacent*`,
//! `Attr`, `NamedNodeMap`, `dataset`, `Range`, `MutationObserver`, and the
//! `Node` members `normalize`, `isEqualNode`, `compareDocumentPosition`,
//! `splitText`, `importNode` and `adoptNode`. Each test parses a document
//! with `clazel-treebuilder`, runs script through `clazel-js`, and reads the
//! global `r`. Checks that come from a WPT `dom/` test name it; those files
//! need `testharness.js`, which the engine cannot run yet (see
//! `tests/wpt_dom.rs` for the stand-in run).

use clazel_js::{Config, Error, Key, Limits, Realm, Runtime};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
use clazel_web::page::mutation::notify_mutation_observers;
use clazel_web::page::{HookCall, LogLevel, NoHooks, Page, run_script};

struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

type Test = core::result::Result<(), Error>;

const URL: &str = "https://example.org/dir/page.html?q=1#top";

fn page(html: &str) -> clazel_js::Result<(Runtime, Realm)> {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    let url: Vec<u32> = URL.chars().map(u32::from).collect();
    let (parsed, _) = parse_real(&NoEnc, &input, url, true, false);
    Page::new(parsed.arena, URL, Box::new(NoHooks)).into_runtime(Config::new(Limits::unlimited()))
}

fn run(rt: &mut Runtime, realm: &Realm, script: &str) -> clazel_js::Result<String> {
    if let Err(e) = run_script(rt, realm, "test.js", script) {
        let log = rt.scope(|scope| Ok(scope.host_mut::<Page>()?.hook_calls().to_vec()))?;
        let last = log.into_iter().rev().find_map(|c| match c {
            HookCall::Log(LogLevel::Error, t) => Some(t),
            _ => None,
        });
        return Err(match last {
            Some(t) => Error::WrongType(Box::leak(t.into_boxed_str())),
            None => e,
        });
    }
    read_r(rt, realm)
}

fn read_r(rt: &mut Runtime, realm: &Realm) -> clazel_js::Result<String> {
    rt.scope(|scope| {
        let g = scope.global(realm)?;
        let r = scope.get(g, Key::Str("r"))?;
        let s = scope.to_string(r)?;
        scope.string_to_string_lossy(s)
    })
}

const DOC: &str = "<!DOCTYPE html><html><head><title>t</title></head><body><div id=a class='x y'><p>one</p><p>two</p></div><span id=b>t</span><!--c--></body></html>";

#[test]
fn inner_html_gets_and_sets() -> Test {
    // WPT html/dom/elements/elements-in-the-dom ... innerHTML; the cases
    // are the fragment parser's: context-dependent insertion modes.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var a = document.getElementById('a');\n\
         var r = [a.innerHTML];\n\
         a.innerHTML = '<b>x</b>y<!--z--><i a=\"1\">&amp;&lt;</i>';\n\
         r.push(a.innerHTML, a.childNodes.length, a.firstChild.tagName, a.firstChild.firstChild.data,\n\
                a.lastChild.getAttribute('a'), a.lastChild.textContent);\n\
         a.innerHTML = '';\n\
         r.push(a.childNodes.length);\n\
         var t = document.createElement('table'); t.innerHTML = '<tr><td>c';\n\
         r.push(t.innerHTML);\n\
         var s = document.createElement('select'); s.innerHTML = '<option>1<option>2';\n\
         r.push(s.children.length);\n\
         var tpl = document.createElement('template'); tpl.innerHTML = '<td>x</td>';\n\
         r.push(tpl.childNodes.length, tpl.innerHTML);\n\
         r.push(document.body.innerHTML.length > 10);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "<p>one</p><p>two</p>|<b>x</b>y<!--z--><i a=\"1\">&amp;&lt;</i>|4|B|x|1|&<|0|<tbody><tr><td>c</td></tr></tbody>|2|0|<td>x</td>|true"
    );
    Ok(())
}

#[test]
fn outer_html_sets() -> Test {
    // DOM Parsing §outerHTML.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, b = d.getElementById('b');\n\
         var r = [b.outerHTML];\n\
         b.outerHTML = '<u>1</u><u>2</u>';\n\
         r.push(d.getElementById('b'), d.body.innerHTML);\n\
         var x = ''; try { d.documentElement.outerHTML = 'x'; } catch (e) { x = e.name; } r.push(x);\n\
         var f = d.createDocumentFragment(), e = d.createElement('i'); f.appendChild(e);\n\
         e.outerHTML = '<em>a</em>'; r.push(f.firstChild.tagName);\n\
         var lone = d.createElement('p'); lone.outerHTML = 'ignored'; r.push(lone.outerHTML);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "<span id=\"b\">t</span>||<div id=\"a\" class=\"x y\"><p>one</p><p>two</p></div><u>1</u><u>2</u><!--c-->|NoModificationAllowedError|EM|<p></p>"
    );
    Ok(())
}

#[test]
fn insert_adjacent() -> Test {
    // WPT dom/nodes/Element-insertAdjacentElement.html,
    // Element-insertAdjacentText.html and html/dom/insertAdjacentHTML.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), r = [];\n\
         r.push(a.insertAdjacentElement('beforebegin', d.createElement('i')).tagName);\n\
         a.insertAdjacentText('AFTERBEGIN', 'T');\n\
         a.insertAdjacentHTML('beforeEnd', '<b>B</b>');\n\
         a.insertAdjacentHTML('afterend', '<em>E</em>');\n\
         r.push(a.previousSibling.tagName, a.firstChild.data, a.lastChild.tagName, a.nextSibling.tagName);\n\
         var x = []; try { a.insertAdjacentText('bogus', 'x'); } catch (e) { x.push(e.name); }\n\
         try { a.insertAdjacentHTML('nope', 'x'); } catch (e) { x.push(e.name); }\n\
         try { d.documentElement.insertAdjacentHTML('beforebegin', 'x'); } catch (e) { x.push(e.name); }\n\
         r.push(x.join(','));\n\
         var lone = d.createElement('div');\n\
         r.push(String(lone.insertAdjacentElement('afterend', d.createElement('p'))));\n\
         d.documentElement.insertAdjacentHTML('afterbegin', '<!--k-->');\n\
         r.push(d.documentElement.firstChild.nodeType);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "I|I|T|B|EM|SyntaxError,SyntaxError,NoModificationAllowedError|null|8"
    );
    Ok(())
}

#[test]
fn character_data_and_text_nodes() -> Test {
    // WPT dom/nodes/Text-splitText.html, Text-wholeText.html,
    // Node-normalize.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, p = d.createElement('p'), r = [];\n\
         var t = d.createTextNode('abcdef'); p.appendChild(t);\n\
         var u = t.splitText(2);\n\
         r.push(t.data, u.data, t.nextSibling === u, p.childNodes.length, t.wholeText, u.wholeText);\n\
         var x = ''; try { t.splitText(9); } catch (e) { x = e.name; } r.push(x);\n\
         p.appendChild(d.createTextNode('')); p.appendChild(d.createElement('b'));\n\
         p.appendChild(d.createTextNode('x')); p.appendChild(d.createTextNode('y'));\n\
         p.normalize();\n\
         r.push(p.childNodes.length, p.firstChild.data, p.lastChild.data, p.childNodes[1]);\n\
         var lone = d.createTextNode('q'); var w = lone.splitText(1); r.push(w.data === '', w.parentNode);\n\
         r = r.join('|');",
    )?;
    // p.childNodes[1] is undefined: indexed access needs the engine's
    // exotic dispatch (clazel-webidl's README), so it joins as "".
    assert_eq!(
        r,
        "ab|cdef|true|2|abcdef|abcdef|IndexSizeError|3|abcdef|xy||true|"
    );
    Ok(())
}

#[test]
fn equality_and_position() -> Test {
    // WPT dom/nodes/Node-isEqualNode.html, Node-compareDocumentPosition.html,
    // Node-lookupNamespaceURI.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), b = d.getElementById('b'), r = [];\n\
         r.push(a.isEqualNode(a.cloneNode(true)), a.isEqualNode(a.cloneNode(false)), a.isEqualNode(null),\n\
                a.isEqualNode(b), d.createTextNode('x').isEqualNode(d.createTextNode('x')),\n\
                d.createComment('x').isEqualNode(d.createTextNode('x')));\n\
         var c = a.cloneNode(true); c.setAttribute('class', 'y x'); r.push(a.isEqualNode(c));\n\
         c.setAttribute('class', 'x y'); r.push(a.isEqualNode(c));\n\
         r.push(a.compareDocumentPosition(a), a.compareDocumentPosition(b), b.compareDocumentPosition(a),\n\
                a.compareDocumentPosition(a.firstChild), a.firstChild.compareDocumentPosition(a),\n\
                (a.compareDocumentPosition(d.createElement('x')) & 1) === 1);\n\
         r.push(d.documentElement.lookupNamespaceURI(null), d.isDefaultNamespace('http://www.w3.org/1999/xhtml'),\n\
                a.lookupPrefix('http://www.w3.org/1999/xhtml'), a.baseURI);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "true|false|false|false|true|false|false|true|0|4|2|20|10|true|http://www.w3.org/1999/xhtml|true||https://example.org/dir/page.html?q=1#top"
    );
    Ok(())
}

#[test]
fn import_and_adopt() -> Test {
    // WPT dom/nodes/Document-importNode.html, Document-adoptNode.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), r = [];\n\
         var i = d.importNode(a, true), j = d.importNode(a), k = d.importNode(a, {selfOnly: false});\n\
         r.push(i !== a, i.childNodes.length, j.childNodes.length, k.childNodes.length, i.parentNode);\n\
         r.push(d.adoptNode(a) === a, a.parentNode);\n\
         var x = ''; try { d.importNode(d); } catch (e) { x = e.name; } r.push(x);\n\
         x = ''; try { d.adoptNode(d); } catch (e) { x = e.name; } r.push(x);\n\
         r = r.join('|');",
    )?;
    assert_eq!(r, "true|2|0|2||true||NotSupportedError|NotSupportedError");
    Ok(())
}

#[test]
fn attr_and_named_node_map() -> Test {
    // WPT dom/nodes/Attr-*.html, Element-attributes.html (the
    // `attributes` map), Document-createAttribute.html,
    // Element-setAttributeNode*.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), r = [];\n\
         var m = a.attributes;\n\
         r.push(m.length, m.item(0).name, m.item(0).value, m.item(1).name, m.item(2),\n\
                m.getNamedItem('CLASS').value, m.getNamedItem('nope'), m.item(0).ownerElement === a);\n\
         var at = a.getAttributeNode('id'); r.push(at === m.item(0), at.nodeType, at.nodeName, at.nodeValue, at.specified);\n\
         at.value = 'z'; r.push(a.id, at.value, d.getElementById('a'), d.getElementById('z') === a);\n\
         a.setAttribute('id', 'a2'); r.push(at.value);\n\
         var n = d.createAttribute('DATA-x'); n.value = '1'; r.push(n.name, n.ownerElement);\n\
         r.push(a.setAttributeNode(n), a.getAttribute('data-x'), n.ownerElement === a);\n\
         var n2 = d.createAttribute('data-x'); n2.value = '2'; r.push(a.setAttributeNode(n2) === n, n.ownerElement, a.getAttribute('data-x'));\n\
         var e = '';\n\
         try { d.body.setAttributeNode(n2); } catch (x) { e = x.name; } r.push(e);\n\
         r.push(a.removeAttributeNode(n2) === n2, n2.ownerElement, n2.value, a.hasAttribute('data-x'));\n\
         e = ''; try { a.removeAttributeNode(n2); } catch (x) { e = x.name; } r.push(e);\n\
         r.push(m.removeNamedItem('class').value, a.hasAttribute('class'));\n\
         e = ''; try { m.removeNamedItem('class'); } catch (x) { e = x.name; } r.push(e);\n\
         a.setAttributeNS('http://www.w3.org/1999/xlink', 'xlink:href', 'u');\n\
         r.push(a.getAttributeNS('http://www.w3.org/1999/xlink', 'href'), a.hasAttributeNS(null, 'href'),\n\
                a.getAttributeNode('xlink:href').prefix, a.getAttributeNode('xlink:href').localName,\n\
                a.getAttributeNode('xlink:href').namespaceURI);\n\
         e = ''; try { a.setAttributeNS(null, 'p:x', 'v'); } catch (x) { e = x.name; } r.push(e);\n\
         a.removeAttributeNS('http://www.w3.org/1999/xlink', 'href'); r.push(a.attributes.length);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "2|id|a|class||x y||true|true|2|id|a|true|z|z||true|a2|data-x|||1|true|true||2|InUseAttributeError|true||2|false|NotFoundError|x y|false|NotFoundError|u|false|xlink|href|http://www.w3.org/1999/xlink|NamespaceError|1"
    );
    Ok(())
}

#[test]
fn dataset_conversions() -> Test {
    // HTML §3.2.6.6 "dataset": the names, the setter's errors.
    let (mut rt, realm) =
        page("<!DOCTYPE html><div id=a data-foo-bar=1 data-x data-UP=3 data-a-1=4 style=s></div>")?;
    let r = run(
        &mut rt,
        &realm,
        "var a = document.getElementById('a'); var m = a.dataset; var r = [m === a.dataset, m instanceof DOMStringMap]; r = r.join('|');",
    )?;
    assert_eq!(r, "true|true");
    // `dataset` is a platform object whose properties script cannot reach
    // yet (no exotic dispatch); the conversions are Rust functions.
    let names = rt.scope(|scope| {
        let p = scope.host_mut::<Page>()?;
        let e = (0..p.arena().len())
            .find(|&n| {
                matches!(p.arena().kind(n), clazel_dom::exec::ExecKind::Element { local_name, .. }
                    if local_name.iter().copied().eq("div".chars().map(u32::from)))
            })
            .unwrap_or(0);
        let to_s = |v: &[u32]| {
            v.iter()
                .filter_map(|&c| char::from_u32(c))
                .collect::<String>()
        };
        let mut out: Vec<String> = p.dataset_names(e).iter().map(|n| to_s(n)).collect();
        let get = |p: &Page, n: &str| {
            p.dataset_get(e, &n.chars().map(u32::from).collect::<Vec<_>>())
                .map(|v| to_s(&v))
        };
        out.push(format!("{:?}", get(p, "fooBar")));
        out.push(format!("{:?}", get(p, "x")));
        out.push(format!("{:?}", get(p, "a-1")));
        out.push(format!("{:?}", get(p, "up")));
        let set = |p: &mut Page, n: &str, v: &str| {
            p.dataset_set(
                e,
                &n.chars().map(u32::from).collect::<Vec<_>>(),
                v.chars().map(u32::from).collect(),
            )
        };
        out.push(format!("{:?}", set(p, "newName", "v")));
        out.push(format!("{:?}", set(p, "a-b", "v")));
        out.push(format!("{:?}", set(p, "has space", "v")));
        out.push(format!("{:?}", get(p, "newName")));
        p.dataset_delete(e, &"newName".chars().map(u32::from).collect::<Vec<_>>());
        out.push(format!("{:?}", get(p, "newName")));
        Ok(out.join("|"))
    })?;
    assert_eq!(
        names,
        "fooBar|x|up|a-1|Some(\"1\")|Some(\"\")|Some(\"4\")|Some(\"3\")|Ok(())|Err(SyntaxError)|Err(InvalidCharacterError)|Some(\"v\")|None"
    );
    Ok(())
}

#[test]
fn mutation_observer_records() -> Test {
    // WPT dom/nodes/MutationObserver-childList.html, -attributes.html,
    // -characterData.html, -disconnect.html, -takeRecords.html: the
    // record contents for each kind of mutation.
    let (mut rt, realm) = page(DOC)?;
    run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), log = [];\n\
         var mo = new MutationObserver(function (recs, obs) {\n\
           for (var i = 0; i < recs.length; i++) {\n\
             var x = recs[i];\n\
             log.push([x.type, x.target.nodeName, x.addedNodes.length, x.removedNodes.length,\n\
               x.previousSibling && x.previousSibling.nodeName, x.nextSibling && x.nextSibling.nodeName,\n\
               x.attributeName, x.attributeNamespace, x.oldValue].map(String).join(','));\n\
           }\n\
           log.push('batch' + (obs === mo));\n\
         });\n\
         mo.observe(a, {childList: true, attributes: true, attributeOldValue: true, characterData: true, characterDataOldValue: true, subtree: true});\n\
         a.setAttribute('k', 'v'); a.setAttribute('k', 'w'); a.removeAttribute('k');\n\
         var t = d.createTextNode('hi'); a.appendChild(t);\n\
         t.data = 'yo'; t.appendData('!');\n\
         a.insertBefore(d.createElement('em'), a.firstChild);\n\
         a.removeChild(t);\n\
         a.firstChild.nextSibling.setAttribute('z', '1');\n\
         var f = d.createDocumentFragment(); f.append('a', d.createElement('u')); a.append(f);\n\
         a.replaceChildren();\n\
         var r = '';",
    )?;
    assert!(rt.scope(|scope| Ok(scope.host_mut::<Page>()?.has_pending_mutation_observers()))?);
    assert!(notify_mutation_observers(&mut rt)?);
    assert!(!rt.scope(|scope| Ok(scope.host_mut::<Page>()?.has_pending_mutation_observers()))?);
    let r = run(&mut rt, &realm, "var r = log.join(';');")?;
    assert_eq!(
        r,
        [
            "attributes,DIV,0,0,null,null,k,null,null",
            "attributes,DIV,0,0,null,null,k,null,v",
            "attributes,DIV,0,0,null,null,k,null,w",
            "childList,DIV,1,0,P,null,null,null,null",
            "characterData,#text,0,0,null,null,null,null,hi",
            "characterData,#text,0,0,null,null,null,null,yo",
            "childList,DIV,1,0,null,P,null,null,null",
            "childList,DIV,0,1,P,null,null,null,null",
            "attributes,P,0,0,null,null,z,null,null",
            "childList,DIV,2,0,P,null,null,null,null",
            "childList,DIV,0,5,null,null,null,null,null",
            "batchtrue",
        ]
        .join(";")
    );
    Ok(())
}

#[test]
fn mutation_observer_options_and_lifecycle() -> Test {
    let (mut rt, realm) = page(DOC)?;
    run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), b = d.getElementById('b'), r = [];\n\
         var calls = 0;\n\
         var mo = new MutationObserver(function () { calls++; });\n\
         var err = [];\n\
         try { mo.observe(a, {}); } catch (e) { err.push(e.name); }\n\
         try { mo.observe(a, {attributes: false, attributeOldValue: true}); } catch (e) { err.push(e.name); }\n\
         try { mo.observe(a, {characterData: false, characterDataOldValue: true}); } catch (e) { err.push(e.name); }\n\
         try { mo.observe(a, {attributeFilter: ['x'], attributes: false}); } catch (e) { err.push(e.name); }\n\
         try { mo.observe({}, {childList: true}); } catch (e) { err.push(e.name); }\n\
         r.push(err.join(','));\n\
         mo.observe(a, {attributes: true, attributeFilter: ['keep']});\n\
         a.setAttribute('skip', '1'); r.push(mo.takeRecords().length);\n\
         a.setAttribute('keep', '1'); a.setAttributeNS('http://www.w3.org/1999/xlink', 'xlink:keep', 'x');\n\
         var taken = mo.takeRecords(); r.push(taken.length, taken[0].attributeName, taken[0].oldValue);\n\
         r.push(mo.takeRecords().length);\n\
         a.appendChild(d.createElement('q')); r.push(mo.takeRecords().length);\n\
         mo.observe(a, {childList: true}); a.appendChild(d.createElement('q')); r.push(mo.takeRecords().length);\n\
         a.firstChild.setAttribute('keep', '2'); r.push(mo.takeRecords().length);\n\
         mo.observe(a, {childList: true, subtree: true});\n\
         var inner = a.firstChild; var kid = d.createElement('s'); inner.appendChild(kid);\n\
         r.push(mo.takeRecords().length);\n\
         a.removeChild(inner); kid.appendChild(d.createElement('w')); r.push(mo.takeRecords().length);\n\
         mo.disconnect(); a.appendChild(d.createElement('z')); r.push(mo.takeRecords().length);\n\
         r.push(calls);\n\
         r = r.join('|');",
    )?;
    let r = run(&mut rt, &realm, "var r = r;")?;
    assert_eq!(
        r,
        "TypeError,TypeError,TypeError,TypeError,TypeError|0|1|keep||0|0|1|0|1|2|0|0"
    );
    Ok(())
}

#[test]
fn live_ranges() -> Test {
    // WPT dom/ranges/Range-set.html, Range-selectNode.html,
    // Range-compareBoundaryPoints.html, Range-deleteContents.html,
    // Range-extractContents.html, Range-cloneContents.html,
    // Range-insertNode.html, Range-surroundContents.html,
    // Range-mutations-*.html: the same operations on a small tree.
    let (mut rt, realm) =
        page("<!DOCTYPE html><div id=a><p id=p1>hello</p><p id=p2>world</p><b id=b>!</b></div>")?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), p1 = d.getElementById('p1'), p2 = d.getElementById('p2'), r = [];\n\
         var g = d.createRange();\n\
         r.push(g.startContainer === d, g.collapsed, g.startOffset);\n\
         g.setStart(p1.firstChild, 2); g.setEnd(p2.firstChild, 3);\n\
         r.push(g.collapsed, g.commonAncestorContainer === a, g.toString(), g.endOffset);\n\
         var c = g.cloneRange(); c.collapse(true);\n\
         r.push(c.collapsed, c.endContainer === p1.firstChild, g.compareBoundaryPoints(Range.START_TO_START, c),\n\
                g.compareBoundaryPoints(Range.END_TO_END, c), g.comparePoint(p1.firstChild, 0), g.comparePoint(p2.firstChild, 5),\n\
                g.isPointInRange(p2.firstChild, 1), g.intersectsNode(a.lastChild), g.intersectsNode(p1));\n\
         var e = ''; try { g.setStart(p1, 9); } catch (x) { e = x.name; } r.push(e);\n\
         e = ''; try { g.setStart(d.doctype, 0); } catch (x) { e = x.name; } r.push(e);\n\
         var f = g.cloneContents();\n\
         r.push(f.childNodes.length, f.firstChild.nodeName, f.firstChild.textContent, f.lastChild.textContent, a.childNodes.length);\n\
         var x = g.extractContents();\n\
         r.push(x.childNodes.length, p1.textContent, p2.textContent, g.collapsed, g.startContainer === a, g.startOffset);\n\
         g.selectNodeContents(p2); g.deleteContents(); r.push(p2.textContent, p2.childNodes.length);\n\
         g.selectNode(a.lastChild); r.push(g.startOffset, g.endOffset, g.toString());\n\
         var n = d.createElement('i'); n.textContent = 'N'; g.collapse(true); g.insertNode(n);\n\
         r.push(a.childNodes.length, a.childNodes.item(2) === n, g.startContainer === a, g.endOffset);\n\
         var s = d.createRange(); s.selectNodeContents(p1);\n\
         var w = d.createElement('u'); s.surroundContents(w);\n\
         r.push(p1.innerHTML, s.toString());\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "true|true|0|false|true|llowor|3|true|true|0|1|-1|1|true|false|true|IndexSizeError|InvalidNodeTypeError|2|P|llo|wor|3|2|he|ld|true|true|1||0|2|3|!|4|true|true|3|<u>he</u>|he"
    );
    Ok(())
}

#[test]
fn ranges_follow_mutations() -> Test {
    // DOM §4.2.3 insert/remove and §4.10 replace data, steps for live
    // ranges; WPT dom/ranges/Range-mutations-*.html.
    let (mut rt, realm) = page("<!DOCTYPE html><div id=a><p>abcdef</p><p>xy</p></div>")?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), r = [];\n\
         var p = a.firstChild, t = p.firstChild;\n\
         var g = d.createRange(); g.setStart(t, 2); g.setEnd(a, 2);\n\
         t.insertData(0, 'XX'); r.push(g.startOffset);\n\
         t.deleteData(0, 4); r.push(g.startOffset);\n\
         t.replaceData(0, 5, 'Q'); r.push(g.startOffset, t.data);\n\
         var u = t.splitText(1); r.push(g.startContainer === t, g.startOffset);\n\
         a.insertBefore(d.createElement('hr'), a.firstChild); r.push(g.endOffset);\n\
         a.removeChild(a.firstChild); r.push(g.endOffset);\n\
         a.removeChild(p); r.push(g.startContainer === a, g.startOffset, g.endOffset);\n\
         var h = d.createRange(); h.setStart(a.firstChild.firstChild, 1); h.setEnd(a.firstChild.firstChild, 2);\n\
         a.firstChild.normalize(); r.push(h.collapsed);\n\
         a.firstChild.appendChild(d.createTextNode('zz')); a.firstChild.normalize();\n\
         r.push(h.startOffset, h.endOffset, a.firstChild.firstChild.data);\n\
         r = r.join('|');",
    )?;
    assert_eq!(r, "4|0|0|Q|true|0|3|2|true|0|1|false|1|2|xyzz");
    Ok(())
}

#[test]
fn contextual_fragment() -> Test {
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, g = d.createRange(); g.selectNodeContents(d.getElementById('a'));\n\
         var f = g.createContextualFragment('<td>x</td><i>y</i>');\n\
         var h = d.createRange(); h.selectNodeContents(d.createElement('tr'));\n\
         var t = h.createContextualFragment('<td>c</td>');\n\
         var r = [f.childNodes.length, f.firstChild.nodeName, t.firstChild.nodeName, f.nodeType].join('|');",
    )?;
    // In a div the stray <td> tag is dropped and its text kept.
    assert_eq!(r, "2|#text|TD|11");
    Ok(())
}

#[test]
fn tag_name_ns_and_processing_instructions() -> Test {
    // WPT dom/nodes/Document-getElementsByTagNameNS.html and
    // Document-createProcessingInstruction.js.
    let (mut rt, realm) =
        page("<!DOCTYPE html><div id=a><p>1</p><svg><p>2</p><circle></circle></svg></div>")?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), r = [];\n\
         var html = 'http://www.w3.org/1999/xhtml', svg = 'http://www.w3.org/2000/svg';\n\
         var l = a.getElementsByTagNameNS(html, 'p');\n\
         r.push(l.length, d.getElementsByTagNameNS('*', 'p').length, d.getElementsByTagNameNS(svg, '*').length,\n\
                d.getElementsByTagNameNS('*', '*').length > 5, d.getElementsByTagNameNS(null, 'p').length,\n\
                d.getElementsByTagNameNS('', 'p').length);\n\
         a.appendChild(d.createElement('p')); r.push(l.length);\n\
         var pi = d.createProcessingInstruction('xml-stylesheet', 'href=\"x\"');\n\
         r.push(pi.nodeType, pi.target, pi.data, pi.nodeName, pi instanceof ProcessingInstruction, pi instanceof CharacterData);\n\
         var e = []; try { d.createProcessingInstruction('a', 'x?>y'); } catch (x) { e.push(x.name); }\n\
         try { d.createProcessingInstruction('', 'x'); } catch (x) { e.push(x.name); }\n\
         r.push(e.join(','), new ProcessingInstruction('t', 'd').data);\n\
         r = r.join('|');",
    )?;
    // The `p` start tag inside `svg` breaks out of foreign content (HTML
    // §13.2.6.5): two `p` are HTML ones and `*` in the SVG namespace is the
    // `svg` alone.
    assert_eq!(
        r,
        "2|2|1|true|0|0|3|7|xml-stylesheet|href=\"x\"|xml-stylesheet|true|true|InvalidCharacterError,InvalidCharacterError|d"
    );
    Ok(())
}
