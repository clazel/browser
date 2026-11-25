//! `javascript:` URLs (HTML §7.4.?† "navigate", the `javascript:` URL
//! special case, and "evaluate a javascript: URL").
//!
//! <https://html.spec.whatwg.org/multipage/browsing-the-web.html#evaluate-a-javascript:-url>.
//!
//! Where they run (phase-7.md item 7.15): a `javascript:` URL that the page
//! drew (a link it followed, a `location` it set) runs in the page's own
//! renderer, which evaluates it here and never sends `Navigate` for it; one
//! the user typed is refused by the kernel, so a page never runs code the
//! user typed into the address bar.
//!
//! Modelling choices: the "initiator origin is same origin-domain with the
//! target's" check of navigate is the renderer's (a page only ever follows
//! its own links here); Content Security Policy is not modelled; and the
//! result's "navigate to a response whose body is the string" is the
//! caller's, given the string ([`super::Page::evaluate_javascript_url`]
//! returns it). Until the engine gives a script's completion value
//! (`clazel-js`'s `run_script` returns `undefined`, its README says why),
//! no result is ever a string, so no `javascript:` URL replaces the
//! document yet.

use clazel_js::{Error, Result, Scope, ValueKind};
use clazel_percent::decode::percent_decode_string;

use super::dom;
use super::element::{clean_up_after_running_script, create_classic_script, report};
use super::state::state;

/// Whether `url` (parsed and serialized) is a `javascript:` URL: its scheme
/// is "javascript". The parser lowercases a scheme, so a serialized URL's
/// scheme is compared as written.
pub fn is_javascript_url(url: &str) -> bool {
    url.starts_with("javascript:")
}

/// "Evaluate a javascript: URL" steps 1 to 8 for the serialized `url`: the
/// script's source, or `None` if `url` is not a `javascript:` URL.
pub fn script_source(url: &str) -> Option<Vec<u32>> {
    // 1. "Let urlString be the result of running the URL serializer on url."
    // 2. "Let encodedScriptSource be the result of removing the leading
    //    "javascript:" from urlString."
    let encoded = url.strip_prefix("javascript:")?;
    // 3. "Let scriptSource be the UTF-8 decoding of the percent-decoding of
    //    encodedScriptSource."
    let bytes = percent_decode_string(&dom::cps(encoded));
    Some(
        String::from_utf8_lossy(&bytes)
            .chars()
            .map(u32::from)
            .collect(),
    )
}

/// "Evaluate a javascript: URL" steps 4 to 10 in the page: create a classic
/// script from the source, run it (reporting an exception rather than
/// throwing it), and give the result if it is a string ("If
/// evaluationStatus is a normal completion, and evaluationStatus.[[Value]]
/// is a String, then set result to evaluationStatus.[[Value]]. Otherwise,
/// return null.").
pub(crate) fn evaluate(scope: &mut Scope<'_>, url: &str) -> Result<Option<String>> {
    let Some(source) = script_source(url) else {
        return Ok(None);
    };
    // 4. to 6. Settings, base URL, "create a classic script".
    let base = dom::document_base_url(super::state::arena(scope)?)
        .map(|u| dom::serialize(&u))
        .unwrap_or_default();
    let script = create_classic_script(scope, &source, url.to_owned(), base)?;
    // 7. "Let evaluationStatus be the result of running a classic script
    //    given script and settings." (As "run a classic script", by hand, to
    //    keep the completion value.)
    let st = state(scope)?;
    st.running = st.running.saturating_add(1);
    let status = match (&script.record, script.error.clone()) {
        (Some(record), _) => scope.run_script(record).and_then(|value| {
            if scope.kind(value) == ValueKind::String {
                scope.string_to_string_lossy(value).map(Some)
            } else {
                Ok(None)
            }
        }),
        (None, Some(super::element::ScriptError::Thrown(e))) => Err(Error::Thrown(e)),
        (None, Some(super::element::ScriptError::Engine(m))) => {
            state(scope)?.reports.push(super::state::Report::Engine {
                script: url.to_owned(),
                error: m,
            });
            Ok(None)
        }
        (None, None) => Ok(None),
    };
    let st = state(scope)?;
    st.running = st.running.saturating_sub(1);
    let result = match status {
        Ok(r) => r,
        Err(e @ (Error::Terminated | Error::OutOfMemory)) => return Err(e),
        Err(e) => {
            report(scope, url, e)?;
            None
        }
    };
    clean_up_after_running_script(scope)?;
    // 8. to 10. The string, for the caller to navigate to as a response
    //    whose body it is (text/html;charset=utf-8).
    Ok(result)
}
