//! `Window`, `Location`, `History` and `Navigator` (HTML §7.2†, §7.4†,
//! §8.9†), the parts phase-7.md item 7.15 lists, without the event loop and
//! script elements (item 7.15's other half).
//!
//! <https://html.spec.whatwg.org/multipage/nav-history-apis.html>
//!
//! - **Navigation is the renderer's.** `location.href = …`, `assign`,
//!   `replace` and the component setters parse the URL against the
//!   document's and call [`super::PageHooks::navigate`]; the document and
//!   its URL stay as they are until the renderer loads the new one.
//! - **`pushState` and `replaceState`** check "can have its URL rewritten",
//!   set the document's URL, keep the state, and call
//!   [`super::PageHooks::update_url`]. The state is kept as the value
//!   itself: there is no StructuredSerializeForStorage yet, so a later
//!   change to the object shows in `history.state` (a deviation).
//! - **One browsing context, no frames:** `top`, `parent` and `frames` are
//!   the window, `length` is 0, `opener` is null.
//! - **No user-facing dialogs:** HTML lets a user agent not show simple
//!   dialogs ("cannot show simple dialogs"): `alert` does nothing, `confirm`
//!   returns false, `prompt` returns null; each is written to the host's
//!   log.
//! - **The user agent string** is fixed and honest: it names Clazel and no
//!   other engine or operating system ([`USER_AGENT`]).
//! - Not implemented (the generated defaults throw `NotSupportedError`):
//!   `open`, `postMessage`, `structuredClone`, the timers, `queueMicrotask`
//!   and `requestAnimationFrame` (the event loop, item 7.15), `scrollRestoration`.

use clazel_js::{Local, Result, Scope};
use clazel_url::api::setters;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::{ParsedPath, ParsedUrl, clone_url};
use clazel_webidl::convert::DomString;
use clazel_webidl::exception::DomErrorName;
use clazel_webidl::generated::bindings::*;
use clazel_webidl::platform::ObjectKey;

use super::{
    HookCall, LogLevel, Object, Page, WINDOW, dom_error, page, points_to_string, str_points,
    str_units, units_to_points,
};

/// `navigator.userAgent` (HTML §8.9.1.1†: "the default User-Agent value"):
/// the browser's name and version, and nothing it is not.
pub const USER_AGENT: &str = "Mozilla/5.0 (compatible) Clazel/0.0";

/// The `Location` object's key, made on first use.
pub(crate) fn location_key(scope: &mut Scope<'_>) -> Result<ObjectKey> {
    let p = page(scope)?;
    if let Some(k) = p.location {
        return Ok(k);
    }
    let k = p.add_object(Object::Location);
    p.location = Some(k);
    Ok(k)
}

fn history_key(scope: &mut Scope<'_>) -> Result<ObjectKey> {
    let p = page(scope)?;
    if let Some(k) = p.history {
        return Ok(k);
    }
    let k = p.add_object(Object::History);
    p.history = Some(k);
    Ok(k)
}

fn navigator_key(scope: &mut Scope<'_>) -> Result<ObjectKey> {
    let p = page(scope)?;
    if let Some(k) = p.navigator {
        return Ok(k);
    }
    let k = p.add_object(Object::Navigator);
    p.navigator = Some(k);
    Ok(k)
}

fn s(points: &[u32]) -> String {
    points_to_string(points)
}

fn is_special_http(scheme: &[u32]) -> bool {
    ["http", "https"]
        .iter()
        .any(|x| scheme.iter().copied().eq(x.chars().map(u32::from)))
}

/// URL §4.? "host" getter steps: the host serialized, and ":" and the port
/// if there is one.
fn host_text(url: &ParsedUrl) -> String {
    let Some(h) = &url.host else {
        return String::new();
    };
    let mut out = s(&h.serialize());
    if let Some(p) = url.port {
        out.push(':');
        out.push_str(&p.to_string());
    }
    out
}

/// URL §4.? "URL path serializer".
fn path_text(url: &ParsedUrl) -> String {
    match &url.path {
        ParsedPath::Opaque(p) => s(p),
        ParsedPath::List(segments) => {
            let mut out = String::new();
            for seg in segments {
                out.push('/');
                out.push_str(&s(seg));
            }
            out
        }
    }
}

/// URL §4.? the origin of a URL, serialized (HTML §7.1.? "serialization of
/// an origin"): "scheme://host[:port]" for the schemes with a tuple origin,
/// "null" for an opaque one.
fn origin_text(url: &ParsedUrl) -> String {
    let tuple = ["http", "https", "ws", "wss", "ftp"]
        .iter()
        .any(|x| url.scheme.iter().copied().eq(x.chars().map(u32::from)));
    if !tuple || url.host.is_none() {
        return "null".to_owned();
    }
    format!("{}://{}", s(&url.scheme), host_text(url))
}

fn document_url(scope: &mut Scope<'_>) -> Result<ParsedUrl> {
    Ok(clone_url(&page(scope)?.url))
}

/// HTML §2.4.? "encoding-parsing a URL" relative to the document: parse
/// `text` with the document's URL as the base.
fn parse(scope: &mut Scope<'_>, text: &str) -> Result<Option<ParsedUrl>> {
    let base = document_url(scope)?;
    Ok(basic_url_parser(&str_points(text), Some(&base)))
}

/// HTML §7.2.4.? "Location-object navigate" to url: here, the renderer's
/// hook.
fn navigate(scope: &mut Scope<'_>, url: &ParsedUrl, replace: bool) -> Result<()> {
    let text = s(&url.serialize(false));
    page(scope)?.record(HookCall::Navigate { url: text, replace });
    Ok(())
}

/// A Location component setter (HTML §7.2.4.?, e.g. the `host` setter:
/// "4. Let copyURL be a copy of this's url. 5. ... basic URL parse the
/// given value ... with copyURL as url and the state override. 6.
/// Location-object navigate this to copyURL.").
fn set_component(
    scope: &mut Scope<'_>,
    value: &str,
    set: impl FnOnce(&mut ParsedUrl, &[u32]),
) -> Result<()> {
    let mut url = document_url(scope)?;
    set(&mut url, &str_points(value));
    navigate(scope, &url, false)
}

impl WindowImpl for Page {
    fn window<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        Ok(WINDOW)
    }

    fn self_<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        Ok(WINDOW)
    }

    /// HTML §7.2.? `document`: "this's associated Document".
    fn document<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        Ok(Page::node_key(0))
    }

    /// HTML §7.2.? `name`: the browsing context's name (empty at first).
    fn name<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(page(scope)?.window_name.clone())
    }

    fn set_name<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: DomString) -> Result<()> {
        page(scope)?.window_name = value;
        Ok(())
    }

    fn location<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        location_key(scope)
    }

    fn history<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        history_key(scope)
    }

    /// HTML §7.2.? `status`: "the empty string" (no status bar is set).
    fn status<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(Vec::new())
    }

    fn set_status<'s>(_scope: &mut Scope<'s>, _this: ObjectKey, _value: DomString) -> Result<()> {
        Ok(())
    }

    fn closed<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }

    fn frames<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        Ok(WINDOW)
    }

    /// HTML §7.3.? `length`: "the document-tree child navigables" (none).
    fn length<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<u32> {
        Ok(0)
    }

    /// HTML §7.3.? `top`: the top-level traversable's window (this one).
    fn top<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(Some(WINDOW))
    }

    /// HTML §7.2.? `opener`: null (no window opened this one).
    fn opener<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Local<'s>> {
        Ok(scope.null())
    }

    fn set_opener<'s>(_scope: &mut Scope<'s>, _this: ObjectKey, _value: Local<'s>) -> Result<()> {
        Ok(())
    }

    fn parent<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(Some(WINDOW))
    }

    fn frame_element<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Option<ObjectKey>> {
        Ok(None)
    }

    fn navigator<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        navigator_key(scope)
    }

    fn client_information<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<ObjectKey> {
        navigator_key(scope)
    }

    fn origin_agent_cluster<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }

    /// HTML §8.1.? `origin`: "this's relevant settings object's origin,
    /// serialized".
    fn origin<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(origin_text(&page(scope)?.url))
    }

    /// HTML §8.1.? `isSecureContext`: false (secure contexts are not
    /// implemented, and the `[SecureContext]` members are not exposed).
    fn is_secure_context<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }

    fn cross_origin_isolated<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }

    /// HTML §7.2.? `close()`: a window that was not opened by script is not
    /// script-closable, so nothing happens.
    fn close<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        Ok(())
    }

    fn stop<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        Ok(())
    }

    fn focus<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        Ok(())
    }

    fn blur<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        Ok(())
    }

    /// HTML §8.8.1† `alert()`: "If we cannot show simple dialogs for this,
    /// then return."
    fn alert_0<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        page(scope)?.record(HookCall::Log(LogLevel::Log, "[alert]".to_owned()));
        Ok(())
    }

    fn alert_1<'s>(scope: &mut Scope<'s>, _this: ObjectKey, message: DomString) -> Result<()> {
        let text = format!("[alert] {}", String::from_utf16_lossy(&message));
        page(scope)?.record(HookCall::Log(LogLevel::Log, text));
        Ok(())
    }

    /// HTML §8.8.1† `confirm()`: "If we cannot show simple dialogs for this,
    /// then return false."
    fn confirm<'s>(scope: &mut Scope<'s>, _this: ObjectKey, message: DomString) -> Result<bool> {
        let text = format!("[confirm] {}", String::from_utf16_lossy(&message));
        page(scope)?.record(HookCall::Log(LogLevel::Log, text));
        Ok(false)
    }

    /// HTML §8.8.1† `prompt()`: "If we cannot show simple dialogs for this,
    /// then return null."
    fn prompt<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        message: DomString,
        _default: DomString,
    ) -> Result<Option<DomString>> {
        let text = format!("[prompt] {}", String::from_utf16_lossy(&message));
        page(scope)?.record(HookCall::Log(LogLevel::Log, text));
        Ok(None)
    }

    fn print<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        Ok(())
    }

    fn capture_events<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        Ok(())
    }

    /// HTML §8.1.4.? `reportError(e)`: "Report an exception e for this."
    fn report_error<'s>(scope: &mut Scope<'s>, _this: ObjectKey, e: Local<'s>) -> Result<()> {
        let s = scope.to_string(e)?;
        let text = format!("Uncaught {}", scope.string_to_string_lossy(s)?);
        page(scope)?.record(HookCall::Log(LogLevel::Error, text));
        Ok(())
    }

    /// HTML §8.3† `btoa(data)`: "1. If data contains any code point greater
    /// than U+00FF, then throw an InvalidCharacterError. 2. Convert data to
    /// a byte sequence whose nth byte is the eight-bit representation of the
    /// nth code point of data, and then apply forgiving-base64 encode."
    fn btoa<'s>(scope: &mut Scope<'s>, _this: ObjectKey, data: DomString) -> Result<DomString> {
        let mut bytes = Vec::with_capacity(data.len());
        for u in data {
            match u8::try_from(u) {
                Ok(b) => bytes.push(b),
                Err(_) => {
                    return Err(dom_error(
                        scope,
                        DomErrorName::InvalidCharacterError,
                        "btoa: a character is outside Latin-1",
                    ));
                }
            }
        }
        Ok(super::points_to_units(&clazel_base64::encode::encode(
            &bytes,
        )))
    }

    /// HTML §8.3† `atob(data)`: "1. Let decodedData be the result of running
    /// forgiving-base64 decode on data. 2. If decodedData is failure, then
    /// throw an InvalidCharacterError. 3. Return decodedData."
    fn atob<'s>(scope: &mut Scope<'s>, _this: ObjectKey, data: DomString) -> Result<Vec<u8>> {
        match clazel_base64::decode::decode(&units_to_points(&data)) {
            Some(b) => Ok(b),
            None => Err(dom_error(
                scope,
                DomErrorName::InvalidCharacterError,
                "atob: not valid base64",
            )),
        }
    }
}

impl LocationImpl for Page {
    /// HTML §7.2.4.? `href` getter: "this's url, serialized".
    fn href<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(page(scope)?.url())
    }

    /// HTML §7.2.4.? `href` setter: "2. Let url be the result of
    /// encoding-parsing a URL given the given value, relative to the entry
    /// settings object. 3. If url is failure, then throw a SyntaxError
    /// DOMException. 4. Location-object navigate this to url."
    fn set_href<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        match parse(scope, &value)? {
            Some(url) => navigate(scope, &url, false),
            None => Err(dom_error(
                scope,
                DomErrorName::SyntaxError,
                "not a valid URL",
            )),
        }
    }

    fn origin<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(origin_text(&page(scope)?.url))
    }

    /// `protocol` getter: "this's url's scheme, followed by ':'".
    fn protocol<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(format!("{}:", s(&page(scope)?.url.scheme)))
    }

    fn set_protocol<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_protocol)
    }

    fn host<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(host_text(&page(scope)?.url))
    }

    fn set_host<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_host)
    }

    fn hostname<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(page(scope)?
            .url
            .host
            .as_ref()
            .map(|h| s(&h.serialize()))
            .unwrap_or_default())
    }

    fn set_hostname<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_hostname)
    }

    fn port<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(page(scope)?
            .url
            .port
            .map(|p| p.to_string())
            .unwrap_or_default())
    }

    fn set_port<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_port)
    }

    fn pathname<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(path_text(&page(scope)?.url))
    }

    fn set_pathname<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_pathname)
    }

    /// `search` getter: "If this's url's query is either null or the empty
    /// string, return the empty string. Return '?', followed by this's
    /// url's query."
    fn search<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(match &page(scope)?.url.query {
            Some(q) if !q.is_empty() => format!("?{}", s(q)),
            _ => String::new(),
        })
    }

    fn set_search<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_search)
    }

    /// `hash` getter: "If this's url's fragment is either null or the empty
    /// string, return the empty string. Return '#', followed by this's
    /// url's fragment."
    fn hash<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<String> {
        Ok(match &page(scope)?.url.fragment {
            Some(f) if !f.is_empty() => format!("#{}", s(f)),
            _ => String::new(),
        })
    }

    fn set_hash<'s>(scope: &mut Scope<'s>, _this: ObjectKey, value: String) -> Result<()> {
        set_component(scope, &value, setters::set_hash)
    }

    /// `assign(url)`: "2. Let urlRecord be the result of encoding-parsing a
    /// URL given url, relative to the entry settings object. 3. If urlRecord
    /// is failure, then throw a SyntaxError DOMException. 4.
    /// Location-object navigate this to urlRecord."
    fn assign<'s>(scope: &mut Scope<'s>, this: ObjectKey, url: String) -> Result<()> {
        <Page as LocationImpl>::set_href(scope, this, url)
    }

    /// `replace(url)`: as `assign`, with historyHandling "replace".
    fn replace<'s>(scope: &mut Scope<'s>, _this: ObjectKey, url: String) -> Result<()> {
        match parse(scope, &url)? {
            Some(u) => navigate(scope, &u, true),
            None => Err(dom_error(
                scope,
                DomErrorName::SyntaxError,
                "not a valid URL",
            )),
        }
    }

    /// `reload()`: "Reload this's relevant global object's navigable": the
    /// renderer is asked to navigate to the document's URL, replacing it.
    fn reload<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        let url = document_url(scope)?;
        navigate(scope, &url, true)
    }
}

/// HTML §7.4.? "can have its URL rewritten" (document, targetURL): "1. Let
/// documentURL be document's URL. 2. If targetURL and documentURL differ in
/// their scheme, username, password, host, or port components, then return
/// false. 3. If targetURL's scheme is an HTTP(S) scheme, then return true.
/// 4. If targetURL's scheme is "file", then: if targetURL and documentURL
/// differ in their path component, then return false; return true. 5. If
/// targetURL and documentURL differ in their path component or query
/// components, then return false. 6. Return true."
fn can_rewrite(doc: &ParsedUrl, target: &ParsedUrl) -> bool {
    let host = |u: &ParsedUrl| u.host.as_ref().map(|h| h.serialize());
    if doc.scheme != target.scheme
        || doc.username != target.username
        || doc.password != target.password
        || host(doc) != host(target)
        || doc.port != target.port
    {
        return false;
    }
    if is_special_http(&target.scheme) {
        return true;
    }
    let path = |u: &ParsedUrl| path_text(u);
    if target
        .scheme
        .iter()
        .copied()
        .eq("file".chars().map(u32::from))
    {
        return path(doc) == path(target);
    }
    path(doc) == path(target) && doc.query == target.query
}

/// HTML §7.4.? "shared history push/replace state steps" (history, data,
/// url, historyHandling): "4. Let serializedData be
/// StructuredSerializeForStorage(data) (here: the value itself). 5. Let
/// newURL be document's URL. 6. If url is not null or the empty string,
/// then: 1. Set newURL to the result of encoding-parsing a URL given url,
/// relative to the relevant settings object of history. 2. If newURL is
/// failure, then throw a SecurityError DOMException. 3. If document cannot
/// have its URL rewritten to newURL, then throw a SecurityError
/// DOMException. 8. Run the URL and history update steps given document
/// and newURL, with serializedData set to serializedData and
/// historyHandling set to historyHandling."
fn push_or_replace(
    scope: &mut Scope<'_>,
    data: Local<'_>,
    url: Option<String>,
    replace: bool,
) -> Result<()> {
    let doc = document_url(scope)?;
    let new_url = match url.filter(|u| !u.is_empty()) {
        Some(u) => match parse(scope, &u)? {
            Some(n) => n,
            None => {
                return Err(dom_error(
                    scope,
                    DomErrorName::SecurityError,
                    "not a valid URL",
                ));
            }
        },
        None => clone_url(&doc),
    };
    if !can_rewrite(&doc, &new_url) {
        return Err(dom_error(
            scope,
            DomErrorName::SecurityError,
            "the URL cannot be rewritten to another origin or path",
        ));
    }
    let state = scope.persist(data);
    let text = s(&new_url.serialize(false));
    let p = page(scope)?;
    // "URL and history update steps": the document's URL becomes newURL,
    // its history entry's state serializedData; a push adds an entry.
    p.url = new_url;
    p.history_state = Some(state);
    if !replace {
        p.history_length = p.history_length.saturating_add(1);
    }
    p.record(HookCall::UpdateUrl { url: text, replace });
    Ok(())
}

impl HistoryImpl for Page {
    /// HTML §7.4.? `length`: the number of entries (this page's count: the
    /// kernel keeps the session history).
    fn length<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<u32> {
        Ok(page(scope)?.history_length)
    }

    /// HTML §7.4.? `state`: "this's state" (null at first).
    fn state<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Local<'s>> {
        let h = page(scope)?.history_state.clone();
        match h {
            Some(h) => scope.local(&h),
            None => Ok(scope.null()),
        }
    }

    /// HTML §7.4.? `go(delta)`: "If delta is 0, then reload; otherwise
    /// traverse the history by a delta": the renderer's hook.
    fn go<'s>(scope: &mut Scope<'s>, this: ObjectKey, delta: i32) -> Result<()> {
        if delta == 0 {
            return <Page as LocationImpl>::reload(scope, this);
        }
        page(scope)?.record(HookCall::Traverse(delta));
        Ok(())
    }

    fn back<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        page(scope)?.record(HookCall::Traverse(-1));
        Ok(())
    }

    fn forward<'s>(scope: &mut Scope<'s>, _this: ObjectKey) -> Result<()> {
        page(scope)?.record(HookCall::Traverse(1));
        Ok(())
    }

    fn push_state<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        data: Local<'s>,
        _unused: DomString,
        url: Option<String>,
    ) -> Result<()> {
        push_or_replace(scope, data, url, false)
    }

    fn replace_state<'s>(
        scope: &mut Scope<'s>,
        _this: ObjectKey,
        data: Local<'s>,
        _unused: DomString,
        url: Option<String>,
    ) -> Result<()> {
        push_or_replace(scope, data, url, true)
    }
}

impl NavigatorImpl for Page {
    /// HTML §8.9.1.1† `appCodeName`: "Mozilla".
    fn app_code_name<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("Mozilla"))
    }

    /// `appName`: "Netscape".
    fn app_name<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("Netscape"))
    }

    /// `appVersion`: "either the string "4.0" or a string representing the
    /// version of the browser in detail, e.g. "1.0 (VMS; en-US)
    /// Mellblomenator/9000"": the user agent string after "Mozilla/".
    fn app_version<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units(USER_AGENT.trim_start_matches("Mozilla/")))
    }

    /// `platform`: "the empty string or a string representing the platform"
    /// (the empty string: nothing about the machine is disclosed).
    fn platform<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(Vec::new())
    }

    /// `product`: "Gecko".
    fn product<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("Gecko"))
    }

    /// `productSub`: "20030107" (the value for a browser that is not
    /// Firefox's compatibility mode).
    fn product_sub<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("20030107"))
    }

    fn user_agent<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units(USER_AGENT))
    }

    /// `vendor`: "the empty string" is allowed.
    fn vendor<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(Vec::new())
    }

    fn vendor_sub<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(Vec::new())
    }

    fn oscpu<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(Vec::new())
    }

    /// HTML §8.9.1.3† `language`: the user's preferred language; the
    /// browser's fixed locale, `en-US` (7.0(b)).
    fn language<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<DomString> {
        Ok(str_units("en-US"))
    }

    fn languages<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<Vec<DomString>> {
        Ok(vec![str_units("en-US")])
    }

    /// HTML §8.9.1.? `onLine`: true (the renderer is not told otherwise).
    fn on_line<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(true)
    }

    fn cookie_enabled<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(true)
    }

    fn pdf_viewer_enabled<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }

    /// HTML §8.9.? `hardwareConcurrency`: the renderer runs one thread
    /// (7.0(e)), and the true count would identify the machine.
    fn hardware_concurrency<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<u64> {
        Ok(1)
    }

    fn taint_enabled<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }

    fn java_enabled<'s>(_scope: &mut Scope<'s>, _this: ObjectKey) -> Result<bool> {
        Ok(false)
    }
}
