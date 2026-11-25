//! The page's platform objects through the generated bindings (items 7.12,
//! 7.13 and 7.15's Window, Location, History, Navigator and console): each
//! test parses a small document with `clazel-treebuilder`, runs script in
//! it through `clazel-js`, and reads back the global `r`. Many checks
//! follow WPT's `dom/nodes`, `dom/events` and `html/browsers` tests (named
//! where they do); those files need `testharness.js`, which needs more of
//! the engine than it has, so the checks are transcribed.

use clazel_js::{Config, Error, Key, Limits, Realm, Runtime};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;
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

/// Runs `script` and returns the global `r` converted to a string; an
/// uncaught exception is returned as `Error::WrongType` with its report.
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
    rt.scope(|scope| {
        let g = scope.global(realm)?;
        let r = scope.get(g, Key::Str("r"))?;
        let s = scope.to_string(r)?;
        scope.string_to_string_lossy(s)
    })
}

fn calls(rt: &mut Runtime) -> clazel_js::Result<Vec<HookCall>> {
    rt.scope(|scope| Ok(scope.host_mut::<Page>()?.hook_calls().to_vec()))
}

const DOC: &str = "<!DOCTYPE html><html><head><title> A  page </title></head><body><div id=a class='x y'><p>one</p><p>two</p></div><span id=b>t</span><!--c--></body></html>";

/// The one binding-page test of this file that runs under Miri (the others
/// are ignored there, each costing about 70 s of Miri time, most of it
/// installing the generated interfaces; measured, 69 s for this one): a
/// page with every interface installed runs a one-line script.
#[test]
fn a_page_with_the_bindings_runs_a_script() -> Test {
    let (mut rt, realm) = page(DOC)?;
    let r = run(&mut rt, &realm, "var r = document.body.firstChild.id;")?;
    assert_eq!(r, "a");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn the_document_and_its_tree() -> Test {
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document;\n\
         var r = [d.nodeType, d.nodeName, d.documentElement.tagName, d.body.nodeName, d.head.localName,\n\
         d.title, d.doctype.name, d.compatMode, d.URL, d.contentType, d.characterSet,\n\
         d instanceof Document, d instanceof Node, d.body instanceof HTMLBodyElement,\n\
         d.getElementById('a') instanceof HTMLDivElement, d.getElementById('a').parentNode === d.body,\n\
         d.body.firstChild.id, d.body.lastChild.nodeType, d.body.lastChild.nodeValue,\n\
         d.defaultView === window, d.ownerDocument, d.body.ownerDocument === d].join('|');",
    )?;
    assert_eq!(
        r,
        "9|#document|HTML|BODY|head|A page|html|CSS1Compat|https://example.org/dir/page.html?q=1#top|text/html|UTF-8|true|true|true|true|true|a|8|c|true||true"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn one_wrapper_per_node() -> Test {
    // A node's wrapper is kept in clazel-dom's wrapper slot: the same node
    // gives the same object, with its expandos, however it is reached.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var a = document.getElementById('a'); a.mark = 7;\n\
         var r = [a === document.body.firstChild, document.querySelector('.x').mark,\n\
         a.childNodes === a.childNodes, a.children.item(0) === a.firstChild,\n\
         document.body.childNodes.length].join('|');",
    )?;
    assert_eq!(r, "true|7|true|true|3");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn tree_mutation() -> Test {
    // WPT dom/nodes/Node-appendChild.html, Node-insertBefore.html,
    // Node-removeChild.html, Node-replaceChild.html, ChildNode-*.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document, a = d.getElementById('a'), b = d.getElementById('b');\n\
         var e = d.createElement('EM'); e.appendChild(d.createTextNode('x'));\n\
         a.appendChild(e);\n\
         var r = [e.tagName, e.parentNode === a, a.lastChild === e, a.textContent];\n\
         a.insertBefore(b, a.firstChild); r.push(a.firstChild === b, b.parentNode === a);\n\
         var old = a.replaceChild(d.createComment('k'), b); r.push(old === b, old.parentNode, a.firstChild.data);\n\
         r.push(a.removeChild(e) === e, e.parentNode);\n\
         var t = ''; try { a.removeChild(d.body); } catch (x) { t = x.name + x.code; } r.push(t);\n\
         try { a.appendChild(d.body); } catch (x) { r.push(x.name); }\n\
         try { a.appendChild(a); } catch (x) { r.push(x.name); }\n\
         try { a.appendChild({}); } catch (x) { r.push(x.name); }\n\
         var f = d.createDocumentFragment(); f.append('p', d.createElement('i'), 'q');\n\
         r.push(f.childNodes.length); a.append(f); r.push(f.childNodes.length, a.lastChild.data);\n\
         a.firstChild.remove(); r.push(a.firstChild.nodeName);\n\
         b.before('<', 'x'); a.lastChild.after(b); r.push(a.lastChild === b);\n\
         b.replaceWith('Z'); r.push(a.lastChild.data, b.parentNode);\n\
         a.prepend(b); r.push(a.firstChild === b);\n\
         a.replaceChildren('only'); r.push(a.childNodes.length, a.textContent);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "EM|true|true|onetwox|true|true|true||k|true||NotFoundError8|HierarchyRequestError|HierarchyRequestError|TypeError|3|0|q|P|true|Z||true|1|only"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn text_content_node_value_and_character_data() -> Test {
    // WPT dom/nodes/Node-textContent.html, CharacterData-*.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var a = document.getElementById('a');\n\
         var r = [a.textContent, a.nodeValue, document.textContent];\n\
         a.textContent = 'new'; r.push(a.childNodes.length, a.firstChild.nodeType, a.innerHTML);\n\
         a.textContent = ''; r.push(a.childNodes.length);\n\
         var t = new Text('hello'); r.push(t.data, t.length, t.nodeValue, t instanceof CharacterData);\n\
         t.appendData(' world'); t.insertData(0, '>'); t.deleteData(1, 1); t.replaceData(0, 1, '<<');\n\
         r.push(t.data, t.substringData(2, 3));\n\
         try { t.substringData(99, 1); } catch (e) { r.push(e.name); }\n\
         t.nodeValue = null; r.push(t.data === '');\n\
         t.data = 'd'; r.push(t.textContent);\n\
         var c = new Comment('cc'); r.push(c.nodeName, c.data);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "onetwo|||1|3|new|0|hello|5|hello|true|<<ello world|ell|IndexSizeError|true|d|#comment|cc"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn elements_and_attributes() -> Test {
    // WPT dom/nodes/attributes.html, Element-classlist.html, Element-*.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var a = document.getElementById('a');\n\
         var r = [a.id, a.className, a.localName, a.namespaceURI, a.prefix, a.hasAttributes(),\n\
         a.getAttributeNames().join(','), a.getAttribute('ID'), a.getAttribute('nope')];\n\
         a.setAttribute('Data-K', 'v'); r.push(a.getAttribute('data-k'), a.hasAttribute('DATA-K'));\n\
         a.id = 'z'; r.push(document.getElementById('z') === a, a.getAttribute('id'));\n\
         r.push(a.toggleAttribute('hidden'), a.hasAttribute('hidden'), a.toggleAttribute('hidden'), a.hasAttribute('hidden'));\n\
         a.removeAttribute('data-k'); r.push(a.hasAttribute('data-k'));\n\
         try { a.setAttribute('a b', ''); } catch (e) { r.push(e.name); }\n\
         var cl = a.classList; r.push(cl === a.classList, cl.length, cl.item(1), cl.contains('x'), String(cl));\n\
         cl.add('w', 'x'); cl.remove('y'); r.push(a.className, cl.toggle('x'), cl.toggle('v', true), a.className);\n\
         r.push(cl.replace('w', 'u'), a.className);\n\
         try { cl.add(''); } catch (e) { r.push(e.name); }\n\
         try { cl.add('a b'); } catch (e) { r.push(e.name); }\n\
         a.classList = 'p q'; r.push(a.className);\n\
         a.title = 'T'; r.push(a.getAttribute('title'), a.title, a.lang);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "a|x y|div|http://www.w3.org/1999/xhtml||true|id,class|a||v|true|true|z|true|true|false|false|false|InvalidCharacterError|true|2|y|true|x y|x w|false|true|w v|true|u v|SyntaxError|InvalidCharacterError|p q|T|T|"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn queries_and_collections() -> Test {
    // WPT dom/nodes/ParentNode-querySelector-All.html,
    // Element-getElementsByClassName.html, getElementsByClassName-*.html,
    // HTMLCollection-*.html.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var d = document;\n\
         var ps = d.getElementsByTagName('P'); var xs = d.getElementsByClassName('y x');\n\
         var r = [ps.length, ps.item(1).textContent, xs.length, d.querySelectorAll('p').length,\n\
         d.querySelector('div > p:last-child').textContent, d.querySelector('nope'),\n\
         d.body.children.length, d.body.firstElementChild.id, d.body.lastElementChild.id, d.body.childElementCount,\n\
         d.getElementById('b').previousElementSibling.id, ps.item(0).matches('div p'), ps.item(0).closest('div').id,\n\
         ps instanceof HTMLCollection, d.querySelectorAll('p') instanceof NodeList, ps.namedItem('b')];\n\
         d.getElementById('a').appendChild(d.createElement('p'));\n\
         r.push(ps.length);\n\
         try { d.querySelector('[[['); } catch (e) { r.push(e.name, e.code); }\n\
         r.push(d.getElementsByTagName('*').length, d.body.children.namedItem('b').id);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "2|two|1|2|two||2|a|b|2|a|true|a|true|true||3|SyntaxError|12|9|b"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn inner_and_outer_html_and_clone() -> Test {
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var a = document.getElementById('a');\n\
         var c = a.cloneNode(true), s = a.cloneNode();\n\
         var r = [a.innerHTML, document.getElementById('b').outerHTML, c.outerHTML, s.outerHTML,\n\
         c.parentNode, c.isSameNode(a), c !== a, document.body.contains(a), document.body.contains(c), a.contains(null),\n\
         a.firstChild.isConnected, c.firstChild.isConnected, c.getRootNode() === c, a.getRootNode() === document].join('|');",
    )?;
    assert_eq!(
        r,
        "<p>one</p><p>two</p>|<span id=\"b\">t</span>|<div id=\"a\" class=\"x y\"><p>one</p><p>two</p></div>|<div id=\"a\" class=\"x y\"></div>||false|true|true|false|false|true|false|true|true"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn events_dispatch_through_the_tree() -> Test {
    // WPT dom/events/Event-dispatch-bubbles-true.html,
    // Event-dispatch-order.html, EventTarget-dispatchEvent.html,
    // Event-constructors.any.js, AddEventListenerOptions-once.any.js.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var log = [], d = document, a = d.getElementById('a'), p = a.firstChild;\n\
         function l(name) { return function (e) { log.push(name + ':' + e.eventPhase + ':' + (e.currentTarget === this)); }; }\n\
         window.addEventListener('x', l('win-c'), true);\n\
         d.addEventListener('x', l('doc-c'), true);\n\
         a.addEventListener('x', l('a-b'));\n\
         p.addEventListener('x', l('p'));\n\
         d.addEventListener('x', l('doc-b'));\n\
         window.addEventListener('x', l('win-b'));\n\
         var e = new Event('x', { bubbles: true, cancelable: true });\n\
         var ok = p.dispatchEvent(e);\n\
         var r = [log.join(','), ok, e.target === p, e.currentTarget, e.eventPhase, e.isTrusted, e.defaultPrevented];\n\
         log = [];\n\
         var once = 0; a.addEventListener('y', function () { once++; }, { once: true });\n\
         a.dispatchEvent(new Event('y')); a.dispatchEvent(new Event('y')); r.push(once);\n\
         var h = { handleEvent: function (ev) { this.seen = ev.type; } }; a.addEventListener('z', h); a.dispatchEvent(new Event('z')); r.push(h.seen);\n\
         a.addEventListener('c', function (ev) { ev.preventDefault(); });\n\
         var ce = new Event('c', { cancelable: true }); r.push(a.dispatchEvent(ce), ce.defaultPrevented);\n\
         var stopped = []; a.addEventListener('s', function (ev) { stopped.push(1); ev.stopImmediatePropagation(); });\n\
         a.addEventListener('s', function () { stopped.push(2); }); a.dispatchEvent(new Event('s')); r.push(stopped.join(''));\n\
         try { e.initEvent('x'); a.dispatchEvent(e); r.push('re-dispatch ok'); } catch (x) { r.push(x.name); }\n\
         var nested = ''; a.addEventListener('outer', function () { a.dispatchEvent(new Event('inner')); nested += 'o'; });\n\
         a.addEventListener('inner', function () { nested += 'i'; }); a.dispatchEvent(new Event('outer')); r.push(nested);\n\
         a.addEventListener('t', function () { throw new Error('boom'); }); a.addEventListener('t', function () { r.push('after-throw'); });\n\
         a.dispatchEvent(new Event('t'));\n\
         var cu = new CustomEvent('cu', { detail: { k: 3 } }); r.push(cu.detail.k, cu instanceof Event, new CustomEvent('q').detail);\n\
         var t = new EventTarget(); var tl = 0; t.addEventListener('q', function () { tl++; }); t.dispatchEvent(new Event('q')); r.push(tl);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "win-c:1:true,doc-c:1:true,p:2:true,a-b:3:true,doc-b:3:true,win-b:3:true|true|true||0|false|false|1|z|false|true|1|re-dispatch ok|io|after-throw|3|true||1"
    );
    // The listener's exception was reported to the host's log.
    let reported = calls(&mut rt)?
        .into_iter()
        .any(|c| matches!(c, HookCall::Log(LogLevel::Error, t) if t.contains("boom")));
    assert!(reported);
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn abort_signals_remove_listeners() -> Test {
    // WPT dom/events/AddEventListenerOptions-signal.any.js, dom/abort/*.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var c = new AbortController(), s = c.signal, n = 0, aborted = 0;\n\
         var a = document.getElementById('a');\n\
         a.addEventListener('k', function () { n++; }, { signal: s });\n\
         s.addEventListener('abort', function (e) { aborted++; });\n\
         a.dispatchEvent(new Event('k'));\n\
         var r = [s.aborted, s === c.signal];\n\
         c.abort(); a.dispatchEvent(new Event('k'));\n\
         r.push(n, s.aborted, aborted, s.reason.name);\n\
         try { s.throwIfAborted(); } catch (e) { r.push(e.name); }\n\
         var t = AbortSignal.abort('why'); r.push(t.aborted, t.reason);\n\
         r = r.join('|');",
    )?;
    assert_eq!(r, "false|true|1|true|1|AbortError|AbortError|true|why");
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn window_location_history_navigator_console() -> Test {
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var l = location;\n\
         var r = [window === self, window.window === window, top === window, frames === window, parent === window,\n\
         window.length, window.document === document, l === document.location, l.href, l.protocol, l.host,\n\
         l.hostname, l.port, l.pathname, l.search, l.hash, l.origin, String(l), window.origin, isSecureContext,\n\
         navigator.userAgent, navigator.appName, navigator.language, navigator.languages.join(','), navigator.onLine,\n\
         navigator.cookieEnabled, navigator.javaEnabled(), navigator === window.clientInformation,\n\
         history.length, history.state, btoa('hi'), atob('aGk=')].join('|');\n\
         console.log('to the', 'log', 1); console.warn('w'); console.assert(1 === 2, 'no'); console.assert(true, 'yes');\n\
         alert('hey');",
    )?;
    assert_eq!(
        r,
        "true|true|true|true|true|0|true|true|https://example.org/dir/page.html?q=1#top|https:|example.org|example.org||/dir/page.html|?q=1|#top|https://example.org|https://example.org/dir/page.html?q=1#top|https://example.org|false|Mozilla/5.0 (compatible) Clazel/0.0|Netscape|en-US|en-US|true|true|false|true|1||aGk=|hi"
    );
    let log = calls(&mut rt)?;
    assert_eq!(
        log,
        vec![
            HookCall::Log(LogLevel::Log, "to the log 1".into()),
            HookCall::Log(LogLevel::Warn, "w".into()),
            HookCall::Log(LogLevel::Error, "Assertion failed: no".into()),
            HookCall::Log(LogLevel::Log, "[alert] hey".into()),
        ]
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn navigation_goes_to_the_hook() -> Test {
    // HTML §7.2.4 Location setters, assign and replace; §7.4 pushState and
    // replaceState.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "location.href = 'other.html'; location.assign('/x'); location.replace('https://example.org/y');\n\
         location.hash = 'h'; location = 'z';\n\
         var r = [];\n\
         try { location.href = 'http://[bad'; } catch (e) { r.push(e.name); }\n\
         history.pushState({ n: 1 }, '', 'pushed?a=b'); r.push(location.href, history.state.n, history.length, document.URL);\n\
         history.replaceState(null, '', '#f'); r.push(location.hash, history.length, history.state);\n\
         try { history.pushState(null, '', 'https://elsewhere.example/'); } catch (e) { r.push(e.name); }\n\
         history.back(); history.go(2);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "SyntaxError|https://example.org/dir/pushed?a=b|1|2|https://example.org/dir/pushed?a=b|#f|2||SecurityError"
    );
    let log = calls(&mut rt)?;
    assert_eq!(
        log,
        vec![
            HookCall::Navigate {
                url: "https://example.org/dir/other.html".into(),
                replace: false
            },
            HookCall::Navigate {
                url: "https://example.org/x".into(),
                replace: false
            },
            HookCall::Navigate {
                url: "https://example.org/y".into(),
                replace: true
            },
            HookCall::Navigate {
                url: "https://example.org/dir/page.html?q=1#h".into(),
                replace: false
            },
            HookCall::Navigate {
                url: "https://example.org/dir/z".into(),
                replace: false
            },
            HookCall::UpdateUrl {
                url: "https://example.org/dir/pushed?a=b".into(),
                replace: false
            },
            HookCall::UpdateUrl {
                url: "https://example.org/dir/pushed?a=b#f".into(),
                replace: true
            },
            HookCall::Traverse(-1),
            HookCall::Traverse(2),
        ]
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn idl_shape_of_the_dom_interfaces() -> Test {
    // What WPT's idlharness.js checks of an interface (dom/idlharness.window.js,
    // html/dom/idlharness.https.html): the interface object, its prototype
    // chain, [LegacyUnforgeable] members on the instance, and illegal
    // constructors.
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var r = [Object.getPrototypeOf(HTMLDivElement) === HTMLElement, Object.getPrototypeOf(HTMLElement.prototype) === Element.prototype,\n\
         Object.getPrototypeOf(Text.prototype) === CharacterData.prototype, Node.ELEMENT_NODE, document.body.TEXT_NODE,\n\
         Event.AT_TARGET, typeof Node.prototype.appendChild, Node.prototype.appendChild.length, Document.prototype.createElement.name,\n\
         location.hasOwnProperty('href'), new Event('e').hasOwnProperty('isTrusted'), window.hasOwnProperty('document'),\n\
         Object.getPrototypeOf(window) === Window.prototype, window instanceof EventTarget];\n\
         try { new Node(); } catch (e) { r.push(e.name); }\n\
         try { new HTMLDivElement(); } catch (e) { r.push(e.name); }\n\
         try { Node.prototype.firstChild; } catch (e) { r.push(e.name); }\n\
         try { document.createElement('1x'); } catch (e) { r.push(e.name); }\n\
         r.push(document.createElement('template').content === undefined, new DocumentFragment().nodeType,\n\
         document.createElement('x-y') instanceof HTMLElement, document.createElement('blink') instanceof HTMLUnknownElement,\n\
         document.createElementNS('http://www.w3.org/2000/svg', 'svg').namespaceURI);\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "true|true|true|1|3|2|function|1|createElement|true|true|true|true|true|TypeError|TypeError|TypeError|InvalidCharacterError|true|11|true|true|http://www.w3.org/2000/svg"
    );
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "builds a page with every generated WebIDL interface installed: about 70 s of Miri time per test (292 s before attribute functions were made lazily and shape lookups indexed), most of it binding installation; a_page_with_the_bindings_runs_a_script stays"
)]
fn unimplemented_members_say_so() -> Test {
    let (mut rt, realm) = page(DOC)?;
    let r = run(
        &mut rt,
        &realm,
        "var r = []; try { document.body.innerHTML = '<b>'; } catch (e) { r.push(e.name, e.message); }\n\
         try { setTimeout(function () {}, 0); } catch (e) { r.push(e.name); }\n\
         r = r.join('|');",
    )?;
    assert_eq!(
        r,
        "NotSupportedError|Element.innerHTML is not implemented|NotSupportedError"
    );
    Ok(())
}
