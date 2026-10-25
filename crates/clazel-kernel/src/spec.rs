//! The kernel state machine (phase-2.md item 2.10): `step(State, Event) ->
//! (State, Seq<Output>)`. Nothing here runs; it defines what "correct"
//! means, and item 2.11 proves the isolation theorems about it. Each
//! `// N.` comment is the step number in the cited algorithm.
//!
//! Sources:
//! - phase-2.md 2.10 and 2.11 (our policy: one renderer, one origin; requests
//!   answered from the lock and committed URL only).
//! - HTML Standard, Living Standard, last updated 20 October 2026, read on
//!   23 October 2026 (the multipage pages carry no commit hash):
//!   <https://html.spec.whatwg.org/multipage/dom.html#dom-document-cookie>
//!   (the `cookie` getter and setter, "cookie-averse `Document` object"),
//!   <https://html.spec.whatwg.org/multipage/webstorage.html#the-storage-interface>
//!   (§12.2.1 `length`, `key()`, `getItem()`, `setItem()`, `removeItem()`,
//!   `clear()`), and §12.2.3 (the `localStorage` getter's origin check).
//! - RFC 6265bis §5.7 and §5.8 through `clazel-cookie` (item 2.9), the
//!   message schema through `clazel-ipc` (item 2.3), origins through
//!   `clazel-origin` (item 2.5) and cookie roots through `clazel-psl` (2.4).
//!
//! # What the kernel is
//!
//! A pure function. The host shell (item 2.15) reads a frame from a socket,
//! attaches the id of the renderer *whose socket it was*, calls `step`, writes
//! the outputs and spawns or kills processes. No clock, no I/O: the time
//! comes in as a `Tick`.
//!
//! # Modelling choices
//!
//! Each is a deliberate deviation in form, never in meaning, unless it says
//! it fills a gap or makes a policy choice.
//!
//! - **The URL functions are parameters** ([`UrlFns`]), so the proofs never
//!   unfold the URL parser (item 2.13 instantiates them). `origin_of` is the
//!   plan's URL-to-origin function `spec_fn(Seq<u32>) -> Option<Origin>`
//!   (URL §4.7). The plan names only that one, but the kernel needs two more
//!   facts about a URL string, so there are three: `path_of` (the URL's path
//!   serialization, which cookie matching reads; it is the only part of a
//!   URL the cookie request needs that the origin does not hold) and
//!   `resolve` (the URL parser with a base, for a renderer's `Navigate`).
//!   Every theorem quantifies over all three.
//! - **Opaque origins get the renderer's id.** A URL with an opaque origin
//!   is committed with the lock `Origin::Opaque(id)`, `id` the id of the
//!   renderer it is committed in ([`lock_of_origin`]); whatever opaque id
//!   `origin_of` returned is ignored. This is how the kernel passes the
//!   `fresh` of `clazel_origin::spec::url_origin` (it allocates distinct
//!   ids, and a renderer's id is never reused). Hence an opaque-origin
//!   renderer is its own domain ([`crate::domain::domain_of_lock`]).
//! - **A tuple origin must be able to hold cookies to be a lock.** The lock
//!   of a URL whose origin is a tuple needs a null domain and a host that
//!   canonicalizes (RFC 6265bis §5.1.2) to a non-empty name
//!   ([`valid_tuple_origin`]); otherwise the URL is refused (an `OpenTab` or
//!   `NavigateTab` is ignored, a renderer's `Navigate` gets
//!   [`error_bad_url`]). Every tuple origin of a parsed `http`, `https`,
//!   `ws`, `wss` or `ftp` URL qualifies, so no real URL is refused; the
//!   condition lets the cookie root partition the locks.
//! - **Tabs and ids.** A tab id is the id of the first renderer of the tab
//!   and never changes when the tab navigates to another origin (the new
//!   renderer takes the tab). Ids come from one counter, `next_id`, and are
//!   never reused. When a renderer exits, its tab is closed.
//! - **Same-origin navigation keeps the renderer.** The plan's rule is that
//!   a navigation to a *different* origin always spawns a new renderer and
//!   kills the old one. To the *same* tuple origin, the kernel sends a new
//!   `Commit` to the same renderer and updates its committed URL. A
//!   navigation to an opaque-origin URL always spawns (each opaque origin is
//!   new).
//! - **Where a script comes from.** Phase 2 renderers run scripted
//!   operations, not pages (the plan's "Commit { url, script }" does not say
//!   where the script is from). `OpenTab` carries it, since it is what the
//!   user does (the demo of item 2.16 types in a URL and a script; `OpenTab`
//!   is not yet a fetch, see below). Every other document is the body of a
//!   fetch (item 3.7, below): `Commit { url, script }` is sent with the
//!   fetch's body as the script, "for now; Phase 4 gives it a document".
//!   Nothing a renderer or the user sends reaches the script of a navigation:
//!   that is what keeps a navigation from another domain from carrying
//!   anything into the new renderer except the resolved URL (item 2.11's
//!   declassification allows only that).
//! - **A renderer's `Navigate` is a `NavigateTab`.** The kernel decodes the
//!   URL as UTF-8, resolves it against the renderer's committed URL (the
//!   `resolve` function) and then does exactly `NavigateTab(its tab,
//!   resolved)` ([`begin_navigation`] is literally the function both call).
//!   The only difference is the error reply to the sender when the URL
//!   cannot be decoded, resolved or locked.
//! - **A navigation is a fetch, and the fetch is a parameter (item 3.7).**
//!   `NavigateTab` and a renderer's `Navigate` do not commit: the tab's
//!   renderer records the URL it is navigating to ([`Renderer::pending`]) and
//!   the kernel outputs `Fetch { tab, url }`, the request for the network
//!   shell to fetch it. The shell answers with `Fetched { tab, outcome }`,
//!   where the [`NetOutcome`] holds the URL the fetch was started for and
//!   what the network delivered (octets, opaque to the kernel). The kernel
//!   runs the fetch itself, as a pure function of those two ([`FetchFns`],
//!   which item 3.6's transducer instantiates, as [`UrlFns`] is instantiated
//!   by the URL parser): it gives a [`FetchRun`], the result (the final URL
//!   after redirects and the body, or a failure) and the `Set-Cookie` lines
//!   of the response chain with the request each answers ([`HttpStore`]).
//!   The kernel owns the jar: the shell never sees it, and an outcome cannot
//!   set a cookie but through [`apply_stores`], RFC 6265bis §5.7 storage
//!   of those lines. A fetch's result does not depend on the jar (the shell
//!   sees only the `Cookie` field of requests, which 3.6 proves is §5.8's
//!   retrieval, and the kernel replays the response, so the jar affects
//!   nothing the kernel reads from the network). `OpenTab` is not changed:
//!   the new tab's first document is still the user's script (the demo), and
//!   making it a fetch needs the network shell wired in.
//! - **A `Fetched` event answers the navigation in flight, or nothing
//!   ([`fetched`]).** The tab is the event's tab and it must still be open,
//!   its renderer must still be navigating (`pending` is `Some`), and the
//!   outcome's URL must be the one it is navigating to. Otherwise (the tab
//!   was closed, the navigation finished, or the tab has since navigated to
//!   another URL, whose own `Fetched` is still to come) the outcome is
//!   ignored in full: no state change, no output and no cookie stored
//!   (a stale response is not applied to the jar, a deliberate choice: a
//!   cancelled fetch has no effect). A `Fetched` for the same URL as a
//!   newer navigation of the tab is taken for that navigation's. The
//!   kernel's own commit follows [`navigate_tab`] with the final URL and the
//!   body as the script: the final URL must be a string of Unicode scalar
//!   values with a lock, or the navigation fails with [`error_bad_url`]; a
//!   failed fetch gives the tab's renderer [`error_fetch`]; either way the
//!   renderer stays, and is no longer navigating. A redirect lands wherever
//!   the server says: the navigation is the one the user made, and its final
//!   URL is the kernel's to lock (item 2.11 treats a `Navigate` that
//!   resolves as one the user made; a redirect is the same).
//! - **A response's cookies are stored unless the host is a public suffix
//!   ([`store_allowed`]).** A `Set-Cookie` line whose request host is a
//!   public suffix (or has no host) is not stored, as a document on such a
//!   host is cookie-averse (below): RFC 6265bis step 9 would store a
//!   host-only cookie for the suffix itself, and step 16 then reads across
//!   cookie roots. With this choice `jar_no_public_suffix` holds of every
//!   jar the kernel makes, whatever the fetch returns.
//! - **Requests are answered from the lock and the committed URL only.**
//!   The request URL of a cookie call is built from the lock's scheme and
//!   host and the committed URL's path ([`request_url_of`]), and the
//!   request context is `NonHttp` with the lock as both "site for cookies"
//!   and "top-level origin" (the document is a top-level document, §5.2.1).
//!   Nothing in the message other than the cookie string or the storage
//!   arguments is read.
//! - **`document.cookie` and opaque origins.** HTML says: "if the document
//!   is a cookie-averse `Document` object" (its URL's scheme is not an
//!   HTTP(S) scheme), the getter returns the empty string and the setter does
//!   nothing; "Otherwise, if the `Document`'s origin is an opaque origin"
//!   both throw a "SecurityError". The kernel does not hold the document's
//!   URL scheme for an opaque-origin document, but a URL has an opaque origin
//!   only when its scheme is not `http` or `https` (URL §4.7: `file:`,
//!   `blob:` without an http(s) path, and every non-special scheme; a special
//!   URL with no host does not come out of the URL parser), and such a
//!   document is cookie-averse. So [`cookie_averse`] is "the lock is not a
//!   tuple origin with scheme `http` or `https`" (this also covers the tuple
//!   origins of `ws`, `wss` and `ftp`), the SecurityError branch is never
//!   reached, and an opaque origin gets the empty string, or nothing on a
//!   set, as the plan says. The browsing-context-null condition does not
//!   arise (every renderer has a document).
//! - **A document on a public-suffix host is cookie-averse (item 2.11).**
//!   If the lock's host is itself a public suffix (`co.uk`, `github.io`; per
//!   `clazel-psl` with the same `rules`; an IP address is not one), the
//!   getter returns the empty string and the setter does nothing, as
//!   [`cookie_averse`] says. HTML has no such condition; Chrome and Firefox
//!   behave this way. It is a deliberate choice that closes a flow RFC
//!   6265bis itself has: step 9 lets a request to a public-suffix host set a
//!   host-only cookie, and step 16 ("Leave Secure Cookies Alone") scans the
//!   whole jar for a secure cookie whose domain domain-matches the new
//!   cookie's domain or conversely, which crosses cookie roots when one is a
//!   public suffix (`example_public_suffix_overlay_crosses_roots`). With this
//!   choice no cookie with a public-suffix domain is ever created
//!   (`jar_no_public_suffix`, part of `kernel_wf`), so that scan never
//!   crosses a root.
//! - **Cookie calls** are `clazel_cookie::storage::spec::retrieve_cookie_string`
//!   and `jar_after_retrieval` (the getter, "the cookie-string for the
//!   document's URL for a "non-HTTP" API", decoded as UTF-8: the cookie
//!   string is octets and is sent as the text of a `CookieValue`), and
//!   `store_a_set_cookie_string` (the setter, "act as it would when
//!   receiving a set-cookie-string for the document's URL via a "non-HTTP"
//!   API"). The setter has no reply. The Public Suffix List is a parameter
//!   `rules`, as in `clazel-cookie`.
//! - **localStorage** (HTML §12.2.1) is a map from a lock to an ordered list
//!   of key and value pairs ([`StorageEntry`]): the Storage object's map is
//!   an ordered map, `setItem` on an existing key keeps its position, a new
//!   key goes last, and `key(n)` is the n-th key. Only tuple origins have a
//!   map (an opaque-origin renderer gets [`error_security`], as the
//!   `localStorage` getter throws a "SecurityError"); a lock with an empty
//!   map is not in the `Map` ([`set_storage`]), so equal storage is equal
//!   maps. Strings are the UTF-8 octets of the DOMStrings, so equality is
//!   octet equality (the schema's text is valid UTF-8). "If value cannot be
//!   stored, then throw a QuotaExceededError": a map may hold at most
//!   [`max_storage_size`] octets of keys and values together
//!   (HTML's "5 MB" suggestion, in octets), and a `setItem` past it gets
//!   [`error_quota`]. The limit is per origin, so no origin can fill
//!   another's. `setItem`, `removeItem` and `clear` have no reply on
//!   success.
//! - **Storage events are not modelled.** The "broadcast" steps queue a
//!   `storage` event at other documents' global objects with the same
//!   storage type, which would make the kernel send a renderer something it
//!   did not ask for. No renderer receives anything it did not ask for. (A
//!   `Commit` goes to the renderer the user's action or its own `Navigate`
//!   created.)
//! - **Frames.** `FromRenderer`'s bytes are one whole frame (4-byte length,
//!   then one CBOR item), decoded by `clazel_ipc::message::spec::decode_framed`;
//!   a frame over `MAX_FRAME` never reaches `step` (the host shell turns it
//!   into `RendererExited`, item 2.15), and if one did, it would not decode.
//!   Every output is a whole frame ([`reply_frame`]). A message that cannot
//!   be sent (a `Commit` whose script is not UTF-8, or one over the frame
//!   limit) is replaced by [`error_encode`]; the fallback is itself always
//!   encodable.
//! - **Malformed input.** Every defined result depends only on the sender's
//!   own record, the sender's domain's state and the message:
//!   - an id that names no renderer: no state change, no output;
//!   - a frame that does not decode to a message, or that decodes to a
//!     message a renderer may not send (`Commit`, `CookieValue`,
//!     `StorageValue`, `StorageLengthValue`, `Error`): the sender is
//!     killed, `Kill(id)` and its record is removed (a protocol violation is
//!     not recoverable; the host kills the process). The tab is closed;
//!   - a message that decodes but cannot be served (a `Navigate` URL that
//!     fails, a quota, an opaque `localStorage`): an `Error` reply to the
//!     sender with a code.
//! - **Commit goes to the new renderer.** A `Navigate` that spawns a
//!   renderer produces `ToRenderer(new id, Commit)` in the same step. So the
//!   outputs of a `FromRenderer(r, _)` event are addressed to `r`, or to the
//!   renderer spawned in that step (the one with id `next_id` of the state
//!   before). Item 2.11's `theorem_reply_only_to_sender` is stated with that
//!   exception; the plan's text said "only for r".
//! - **Time.** `Tick(time)` sets the time to the later of `time` and the
//!   current time (time never goes backwards) and evicts the expired cookies
//!   ([`clazel_cookie::storage::spec::evict_expired`], which depends on
//!   time only). Every cookie call takes the current time from the state.
//! - **Renderer ids never appear in a byte sent to a renderer.** The
//!   messages built here (`Commit`, `CookieValue`, `StorageValue`,
//!   `StorageLengthValue`, `Error`) have no id field (the schema rule of item
//!   2.3), and their fields are the committed URL and script (inputs of the
//!   user or of the sender's own navigation), cookie strings and storage
//!   values (of the sender's own domain) and constant codes.
//! - **A spawn names a policy.** `Spawn(id, policy)` carries [`Policy`], of
//!   which there is one value (the renderer sandbox of item 2.14); the host
//!   maps it to the platform's policy.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


// ---------------------------------------------------------------------
// The URL functions.
// ---------------------------------------------------------------------

/// The type of [`UrlFns::resolve`].
pub type Resolver = spec_fn(Seq<u32>, Seq<u32>) -> Option<Seq<u32>>;

/// What the kernel needs to know of URL strings (code points). See the first
/// modelling choice. Item 2.13 instantiates these with `url_origin` over the
/// basic URL parser; every theorem holds for all of them.
pub struct UrlFns {
    /// URL §4.7 "origin" of an absolute URL string; `None` if the string
    /// does not parse. An opaque origin it returns is replaced by the
    /// kernel ([`lock_of_origin`]).
    pub origin_of: spec_fn(Seq<u32>) -> Option<clazel_origin::spec::Origin>,
    /// The path of an absolute URL string, serialized (URL §4.5): the
    /// `clazel_cookie::storage::spec::RequestUrl.path` of cookie matching.
    pub path_of: spec_fn(Seq<u32>) -> Seq<u8>,
    /// The basic URL parser with a base: `resolve(base, input)` is the
    /// serialization of the result of parsing `input` against the absolute
    /// URL `base`, or `None` for failure.
    pub resolve: Resolver,
}

// ---------------------------------------------------------------------
// The fetch (item 3.7).
// ---------------------------------------------------------------------

/// What the network shell reports for a fetch: the URL the fetch was started
/// for (the `url` of the `Fetch` output it answers) and the octets the
/// network delivered, which only [`FetchFns::run`] reads.
pub struct NetOutcome {
    /// The URL the fetch was started for.
    pub url: Seq<u32>,
    /// What the network delivered.
    pub net: Seq<u8>,
}

/// How a fetch ended (the `Done` and `Fail` of item 3.6's transducer).
pub enum FetchResult {
    /// The response: the URL it answers, after redirects, and its body.
    Done {
        /// The final URL, absolute.
        url: Seq<u32>,
        /// The body.
        body: Seq<u8>,
    },
    /// The fetch failed (no response, an invalid or unsupported one, or a
    /// redirect to somewhere that is not fetched).
    Failed,
}

/// One `Set-Cookie` line a response carried, with the request it answers:
/// RFC 6265bis §5.7's inputs ("receives a cookie").
pub struct HttpStore {
    /// The `Set-Cookie` field value.
    pub line: Seq<u8>,
    /// The URL of the request the response answers.
    pub url: clazel_cookie::storage::spec::RequestUrl,
    /// The request context ("HTTP", with the redirect chain's same-site
    /// status).
    pub ctx: clazel_cookie::storage::spec::RequestContext,
}

/// What running a fetch gives.
pub struct FetchRun {
    /// How it ended.
    pub result: FetchResult,
    /// The `Set-Cookie` lines of every response of the chain, in order.
    pub stores: Seq<HttpStore>,
}

/// The fetch, as a parameter of the kernel (see the modelling choices):
/// `run(url, net)` is the fetch of `url` given the octets the network
/// delivered. It reads no jar. Item 3.6's transducer, replayed over `net`,
/// instantiates it; the theorems hold for every one.
pub struct FetchFns {
    /// The fetch of `url` over what the network delivered.
    pub run: spec_fn(Seq<u32>, Seq<u8>) -> FetchRun,
}

// ---------------------------------------------------------------------
// State, events and outputs.
// ---------------------------------------------------------------------

/// One key and value pair of a Storage object's map (HTML §12.2.1), as
/// UTF-8 octets.
pub struct StorageEntry {
    /// The key.
    pub key: Seq<u8>,
    /// The value.
    pub value: Seq<u8>,
}

/// A renderer process, from the kernel's side.
pub struct Renderer {
    /// The renderer's id (never sent to any renderer).
    pub id: nat,
    /// The tab it renders (the id of the first renderer of the tab).
    pub tab: nat,
    /// The URL it committed, absolute.
    pub url: Seq<u32>,
    /// Its lock: the origin of `url`, chosen by the kernel
    /// ([`lock_of_url`]). The one origin this renderer ever serves.
    pub lock: clazel_origin::spec::Origin,
    /// The URL its tab is navigating to, while the fetch for it is in flight
    /// (item 3.7); `None` once the navigation commits or fails.
    pub pending: Option<Seq<u32>>,
}

/// The kernel's state.
pub struct State {
    /// The live renderers.
    pub renderers: Seq<Renderer>,
    /// The cookie jar (`clazel-cookie`, item 2.9).
    pub jar: Seq<clazel_cookie::storage::spec::Cookie>,
    /// Web Storage (HTML §12.2.1): an origin's ordered list of key and
    /// value pairs. Only tuple origins with a non-empty list are in the
    /// map ([`set_storage`]).
    pub storage: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>,
    /// The next fresh renderer (and tab) id.
    pub next_id: nat,
    /// The current time, seconds since 1601-01-01T00:00:00Z (the unit of
    /// `clazel-cookie`).
    pub now: int,
}

/// What can happen to the kernel.
pub enum Event {
    /// A whole frame arrived on the socket of renderer `id` (the host shell
    /// attaches `id` from the socket, never from the frame).
    FromRenderer {
        /// The renderer whose socket it was.
        id: nat,
        /// The raw frame bytes.
        bytes: Seq<u8>,
    },
    /// The user typed an absolute URL into a new tab.
    OpenTab {
        /// The URL.
        url: Seq<u32>,
        /// The script the document runs (UTF-8 text).
        script: Seq<u8>,
    },
    /// The user typed an absolute URL into an existing tab.
    NavigateTab {
        /// The tab.
        tab: nat,
        /// The URL.
        url: Seq<u32>,
    },
    /// The network shell finished the fetch the kernel asked for the tab
    /// (item 3.7).
    Fetched {
        /// The tab the fetch was for.
        tab: nat,
        /// What the network delivered.
        outcome: NetOutcome,
    },
    /// The process of renderer `id` exited (or the host killed it).
    RendererExited {
        /// The renderer.
        id: nat,
    },
    /// The clock advanced to `time`.
    Tick {
        /// The time, seconds since 1601-01-01T00:00:00Z.
        time: int,
    },
}

/// The sandbox policy a renderer is spawned under. There is one.
pub enum Policy {
    /// The renderer sandbox: no file, socket or process access (item 2.14).
    Renderer,
}

/// What the kernel does.
pub enum Output {
    /// Send a whole frame to renderer `id`.
    ToRenderer {
        /// The renderer.
        id: nat,
        /// The frame.
        bytes: Seq<u8>,
    },
    /// Start a renderer process with this id and policy.
    Spawn {
        /// The new renderer.
        id: nat,
        /// Its sandbox.
        policy: Policy,
    },
    /// Kill the renderer process with this id.
    Kill {
        /// The renderer.
        id: nat,
    },
    /// Ask the network shell to fetch `url` for `tab` (item 3.7). Addressed
    /// to no renderer: it names a tab, and the shell answers with
    /// `Fetched { tab, outcome }`.
    Fetch {
        /// The tab.
        tab: nat,
        /// The URL, absolute.
        url: Seq<u32>,
    },
}

/// The kernel before anything happens.
pub open spec fn init_state() -> State {
    State { renderers: seq![], jar: seq![], storage: Map::empty(), next_id: 0, now: 0 }
}

// ---------------------------------------------------------------------
// Error codes and frames.
// ---------------------------------------------------------------------

/// `Error` code: a "SecurityError" (`localStorage` of an opaque origin).
pub open spec fn error_security() -> u64 {
    1
}

/// `Error` code: a "QuotaExceededError".
pub open spec fn error_quota() -> u64 {
    2
}

/// `Error` code: the `Navigate` URL could not be decoded, resolved or locked.
pub open spec fn error_bad_url() -> u64 {
    3
}

/// `Error` code: the reply could not be encoded as one frame.
pub open spec fn error_encode() -> u64 {
    4
}

/// `Error` code: the fetch of a navigation failed (item 3.7).
pub open spec fn error_fetch() -> u64 {
    5
}

/// The frame holding `m`, if it can be sent: its tokens are one data item of
/// the CBOR profile and the payload is within `MAX_FRAME`.
pub open spec fn frame_of(m: clazel_ipc::message::spec::Message) -> Option<Seq<u8>> {
    if clazel_ipc::message::spec::message_ok(m) && clazel_ipc::frame::spec::payload_ok(clazel_ipc::message::spec::encode_message(m)) {
        Some(clazel_ipc::frame::spec::encode_frame(clazel_ipc::message::spec::encode_message(m)))
    } else {
        None
    }
}

/// The frame of `Error { code }`.
pub open spec fn error_frame(code: u64) -> Seq<u8> {
    clazel_ipc::frame::spec::encode_frame(clazel_ipc::message::spec::encode_message(clazel_ipc::message::spec::Message::Error { code }))
}

/// The bytes sent for `m`: its frame, or [`error_encode`]'s if it has none.
pub open spec fn reply_frame(m: clazel_ipc::message::spec::Message) -> Seq<u8> {
    match frame_of(m) {
        Some(f) => f,
        None => error_frame(error_encode()),
    }
}

/// The frame of a `Commit` of `url` running `script`. The URL is sent as
/// UTF-8 (the Encoding Standard's encoder).
pub open spec fn commit_frame(url: Seq<u32>, script: Seq<u8>) -> Seq<u8> {
    reply_frame(clazel_ipc::message::spec::Message::Commit { url: clazel_encoding::utf8::spec::utf8_encode(url), script })
}

/// A single `ToRenderer` of `m` to renderer `r`.
pub open spec fn reply(r: Renderer, m: clazel_ipc::message::spec::Message) -> Seq<Output> {
    seq![Output::ToRenderer { id: r.id, bytes: reply_frame(m) }]
}

// ---------------------------------------------------------------------
// Locks.
// ---------------------------------------------------------------------

/// A tuple origin that can hold cookies and storage: a null domain, and a
/// host that canonicalizes to a non-empty name.
pub open spec fn valid_tuple_origin(o: clazel_origin::spec::Origin) -> bool {
    match o {
        clazel_origin::spec::Origin::Opaque(_) => false,
        clazel_origin::spec::Origin::Tuple { host, domain, .. } => domain is None && match clazel_cookie::matching::spec::canonicalize_a_host_name(
            Some(host),
        ) {
            Some(h) => h.name.len() > 0,
            None => false,
        },
    }
}

/// The lock of a renderer with id `id` committed to a URL whose origin is
/// `o`: a valid tuple origin is its own lock; an opaque origin becomes
/// `Opaque(id)`; anything else is refused.
pub open spec fn lock_of_origin(o: clazel_origin::spec::Origin, id: nat) -> Option<clazel_origin::spec::Origin> {
    match o {
        clazel_origin::spec::Origin::Opaque(_) => Some(clazel_origin::spec::Origin::Opaque(id)),
        clazel_origin::spec::Origin::Tuple { .. } => if valid_tuple_origin(o) { Some(o) } else { None },
    }
}

/// The lock of renderer `id` committed to `url`, if the kernel accepts the
/// URL.
pub open spec fn lock_of_url(urls: UrlFns, url: Seq<u32>, id: nat) -> Option<clazel_origin::spec::Origin> {
    match (urls.origin_of)(url) {
        Some(o) => lock_of_origin(o, id),
        None => None,
    }
}

/// The scheme of a tuple lock (empty for an opaque one).
pub open spec fn lock_scheme(lock: clazel_origin::spec::Origin) -> Seq<u32> {
    match lock {
        clazel_origin::spec::Origin::Tuple { scheme, .. } => scheme,
        clazel_origin::spec::Origin::Opaque(_) => seq![],
    }
}

/// The canonicalized host of a tuple lock.
pub open spec fn lock_host(lock: clazel_origin::spec::Origin) -> Option<clazel_cookie::matching::spec::CanonicalHost> {
    match lock {
        clazel_origin::spec::Origin::Tuple { host, .. } => clazel_cookie::matching::spec::canonicalize_a_host_name(Some(host)),
        clazel_origin::spec::Origin::Opaque(_) => None,
    }
}

/// The lock's host is itself a public suffix (over the Public Suffix List
/// `rules`), e.g. `co.uk` or `github.io`. An IP address is not one.
pub open spec fn lock_on_public_suffix(rules: Seq<clazel_psl::spec::Rule>, lock: clazel_origin::spec::Origin) -> bool {
    match lock_host(lock) {
        Some(h) => !h.is_ip_address && clazel_cookie::storage::spec::is_public_suffix_string(rules, h.name),
        None => false,
    }
}

/// HTML's "cookie-averse `Document` object": the document's URL's scheme is
/// not an HTTP(S) scheme (see the modelling choices for why this is a
/// property of the lock), **or the document is on a public-suffix host**
/// (a modelling choice that fills no gap in HTML: Chrome and Firefox do the
/// same, and it keeps RFC 6265bis §5.7 step 16 from reading across cookie
/// roots).
pub open spec fn cookie_averse(rules: Seq<clazel_psl::spec::Rule>, lock: clazel_origin::spec::Origin) -> bool {
    cookie_averse_given(lock, lock_on_public_suffix(rules, lock))
}

/// [`cookie_averse`] given whether the lock's host is a public suffix (split
/// out so that the condition can be evaluated without the host parser).
pub open spec fn cookie_averse_given(lock: clazel_origin::spec::Origin, on_public_suffix: bool) -> bool {
    !(lock is Tuple && (lock_scheme(lock) == clazel_url::url::spec::http_str() || lock_scheme(lock)
        == clazel_url::url::spec::https_str()) && !on_public_suffix)
}

/// The request URL of a `document.cookie` call by a renderer: the lock's
/// scheme and host, and the committed URL's path. Nothing else.
pub open spec fn request_url_of(urls: UrlFns, r: Renderer) -> clazel_cookie::storage::spec::RequestUrl {
    clazel_cookie::storage::spec::RequestUrl {
        scheme: clazel_cookie::matching::spec::narrow(lock_scheme(r.lock)),
        host: lock_host(r.lock),
        path: (urls.path_of)(r.url),
    }
}

/// The request context of a `document.cookie` call: a "non-HTTP" API of a
/// top-level document whose "site for cookies" and top-level origin are the
/// lock.
pub open spec fn document_context(lock: clazel_origin::spec::Origin) -> clazel_cookie::storage::spec::RequestContext {
    clazel_cookie::storage::spec::RequestContext::NonHttp(clazel_cookie::storage::spec::DocumentCall { site_for_cookies: lock, top_level_origin: lock })
}

// ---------------------------------------------------------------------
// Looking renderers up.
// ---------------------------------------------------------------------

/// The index of the first renderer from `i` on with id `id`.
pub open spec fn find_by_id(rs: Seq<Renderer>, id: nat, i: nat) -> Option<int>
    decreases rs.len() - i,
{
    if i >= rs.len() {
        None
    } else if rs[i as int].id == id {
        Some(i as int)
    } else {
        find_by_id(rs, id, i + 1)
    }
}

/// The index of the first renderer from `i` on in tab `tab`.
pub open spec fn find_by_tab(rs: Seq<Renderer>, tab: nat, i: nat) -> Option<int>
    decreases rs.len() - i,
{
    if i >= rs.len() {
        None
    } else if rs[i as int].tab == tab {
        Some(i as int)
    } else {
        find_by_tab(rs, tab, i + 1)
    }
}

// ---------------------------------------------------------------------
// Web Storage (HTML §12.2.1).
// ---------------------------------------------------------------------

/// The most octets of keys and values one origin's map may hold.
pub open spec fn max_storage_size() -> nat {
    5242880
}

/// The octets of the keys and values of the first `n` entries.
pub open spec fn entries_size(list: Seq<StorageEntry>, n: nat) -> nat
    decreases n,
{
    if n == 0 || n > list.len() {
        0
    } else {
        entries_size(list, (n - 1) as nat) + list[n - 1].key.len() + list[n - 1].value.len()
    }
}

/// The map fits the quota.
pub open spec fn within_quota(list: Seq<StorageEntry>) -> bool {
    entries_size(list, list.len()) <= max_storage_size()
}

/// The index of the entry with key `key`, searching from `i`.
pub open spec fn find_key(list: Seq<StorageEntry>, key: Seq<u8>, i: nat) -> Option<int>
    decreases list.len() - i,
{
    if i >= list.len() {
        None
    } else if list[i as int].key == key {
        Some(i as int)
    } else {
        find_key(list, key, i + 1)
    }
}

/// The map of `lock` (empty if it has none).
pub open spec fn storage_of(s: State, lock: clazel_origin::spec::Origin) -> Seq<StorageEntry> {
    if s.storage.dom().contains(lock) {
        s.storage[lock]
    } else {
        seq![]
    }
}

/// `s` with the map of `lock` replaced by `list` (an empty map is removed).
pub open spec fn set_storage(s: State, lock: clazel_origin::spec::Origin, list: Seq<StorageEntry>) -> State {
    State { storage: if list.len() == 0 { s.storage.remove(lock) } else { s.storage.insert(lock, list) }, ..s }
}

/// A `localStorage` call by renderer `r` on a tuple lock, and what the
/// kernel does with it, given the call as a function of the map (HTML
/// §12.2.1). `m` is the renderer-to-kernel message.
pub open spec fn storage_call(s: State, r: Renderer, m: clazel_ipc::message::spec::Message) -> (State, Seq<Output>) {
    let list = storage_of(s, r.lock);
    match m {
        // getItem(key): "1. If this's map[key] does not exist, then return
        // null. 2. Return this's map[key]."
        clazel_ipc::message::spec::Message::StorageGetItem { key } => match find_key(list, key, 0) {
            None => (s, reply(r, clazel_ipc::message::spec::Message::StorageValue { value: None })),
            Some(i) => (s, reply(r, clazel_ipc::message::spec::Message::StorageValue { value: Some(list[i].value) })),
        },
        // setItem(key, value): "1. Let oldValue be null. 2. Let reorder be
        // true. 3. If this's map[key] exists: 3.1. Set oldValue to this's
        // map[key]. 3.2. If oldValue is value, then return. 3.3. Set
        // reorder to false. 4. If value cannot be stored, then throw a
        // QuotaExceededError. 5. Set this's map[key] to value. 6. If reorder
        // is true, then reorder this's map. 7. Broadcast [...]" (a new key
        // goes last; broadcast is not modelled.)
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => match find_key(list, key, 0) {
            Some(i) => if list[i].value == value {
                (s, seq![])
            } else {
                let new_list = list.update(i, StorageEntry { key, value });
                if within_quota(new_list) {
                    (set_storage(s, r.lock, new_list), seq![])
                } else {
                    (s, reply(r, clazel_ipc::message::spec::Message::Error { code: error_quota() }))
                }
            },
            None => {
                let new_list = list.push(StorageEntry { key, value });
                if within_quota(new_list) {
                    (set_storage(s, r.lock, new_list), seq![])
                } else {
                    (s, reply(r, clazel_ipc::message::spec::Message::Error { code: error_quota() }))
                }
            },
        },
        // removeItem(key): "1. If this's map[key] does not exist, then
        // return. 2. Set oldValue to this's map[key]. 3. Remove this's
        // map[key]. 4. Broadcast [...]"
        clazel_ipc::message::spec::Message::StorageRemoveItem { key } => match find_key(list, key, 0) {
            None => (s, seq![]),
            Some(i) => (set_storage(s, r.lock, list.remove(i)), seq![]),
        },
        // clear(): "1. If this's map is empty, then return. 2. Clear this's
        // map. 3. Broadcast [...]"
        clazel_ipc::message::spec::Message::StorageClear => (set_storage(s, r.lock, seq![]), seq![]),
        // key(index): "1. If index is greater than or equal to this's map's
        // size, then return null. 2. Let keys be the result of running get
        // the keys on this's map. 3. Return keys[index]."
        clazel_ipc::message::spec::Message::StorageKey { index } => if index as int >= list.len() {
            (s, reply(r, clazel_ipc::message::spec::Message::StorageValue { value: None }))
        } else {
            (s, reply(r, clazel_ipc::message::spec::Message::StorageValue { value: Some(list[index as int].key) }))
        },
        // length: "The length getter steps are to return this's map's size."
        clazel_ipc::message::spec::Message::StorageLength => (s, reply(r, clazel_ipc::message::spec::Message::StorageLengthValue { length: list.len() as u64 })),
        // Not a storage call.
        _ => (s, seq![]),
    }
}

// ---------------------------------------------------------------------
// The events.
// ---------------------------------------------------------------------

/// The renderer `old` of tab `tab`, at index `i`, commits the document at
/// `url` running `script`: the shared body of a successful `Fetched` (the
/// final URL and the body) and, as item 2.11 states it, what a navigation
/// does to the renderers. The renderer is no longer navigating.
pub open spec fn navigate_tab(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Seq<u8>) -> (State, Seq<Output>) {
    match find_by_tab(s.renderers, tab, 0) {
        // No such tab (or its renderer has exited): nothing to navigate.
        None => (s, seq![]),
        Some(i) => {
            let old = s.renderers[i];
            match lock_of_url(urls, url, s.next_id) {
                // A URL that does not parse, or has no lock: ignored.
                None => (s, seq![]),
                Some(lock) => if lock is Tuple && lock == old.lock {
                    // The same origin: the renderer stays and commits again.
                    let r = Renderer { url, pending: None, ..old };
                    (State { renderers: s.renderers.update(i, r), ..s }, seq![
                        Output::ToRenderer { id: old.id, bytes: commit_frame(url, script) },
                    ])
                } else {
                    // A different origin: one renderer, one origin. A new
                    // renderer in the tab, the old one killed.
                    let id = s.next_id;
                    let r = Renderer { id, tab, url, lock, pending: None };
                    (State { renderers: s.renderers.update(i, r), next_id: id + 1, ..s }, seq![
                        Output::Kill { id: old.id },
                        Output::Spawn { id, policy: Policy::Renderer },
                        Output::ToRenderer { id, bytes: commit_frame(url, script) },
                    ])
                },
            }
        },
    }
}

/// `NavigateTab(tab, url)` (and a renderer's `Navigate`): the tab's renderer
/// starts navigating to `url`, and the kernel asks for it to be fetched. The
/// renderer, its URL and its lock are unchanged; a navigation already in
/// flight is replaced (its `Fetched` will find another URL and be ignored).
pub open spec fn begin_navigation(urls: UrlFns, s: State, tab: nat, url: Seq<u32>) -> (State, Seq<Output>) {
    match find_by_tab(s.renderers, tab, 0) {
        // No such tab (or its renderer has exited): nothing to navigate.
        None => (s, seq![]),
        Some(i) => match lock_of_url(urls, url, s.next_id) {
            // A URL that does not parse, or has no lock: ignored.
            None => (s, seq![]),
            Some(_) => (
                State { renderers: s.renderers.update(i, Renderer { pending: Some(url), ..s.renderers[i] }), ..s },
                seq![Output::Fetch { tab, url }],
            ),
        },
    }
}

/// `OpenTab(url)`: a new tab with a new renderer.
pub open spec fn open_tab(urls: UrlFns, s: State, url: Seq<u32>, script: Seq<u8>) -> (State, Seq<Output>) {
    let id = s.next_id;
    match lock_of_url(urls, url, id) {
        None => (s, seq![]),
        Some(lock) => (
            State { renderers: s.renderers.push(Renderer { id, tab: id, url, lock, pending: None }), next_id: id + 1, ..s },
            seq![Output::Spawn { id, policy: Policy::Renderer }, Output::ToRenderer { id, bytes: commit_frame(url, script) }],
        ),
    }
}

// ---------------------------------------------------------------------
// The fetch's answer (item 3.7).
// ---------------------------------------------------------------------

/// Whether the host of a request URL is a public suffix (an IP address is
/// not one; no host is not).
pub open spec fn store_on_public_suffix(rules: Seq<clazel_psl::spec::Rule>, url: clazel_cookie::storage::spec::RequestUrl) -> bool {
    match url.host {
        Some(h) => !h.is_ip_address && clazel_cookie::storage::spec::is_public_suffix_string(rules, h.name),
        None => false,
    }
}

/// [`store_allowed`] given whether the host is a public suffix (split out so
/// that the condition can be evaluated without the Public Suffix List).
pub open spec fn store_allowed_given(url: clazel_cookie::storage::spec::RequestUrl, on_public_suffix: bool) -> bool {
    match url.host {
        Some(h) => h.name.len() > 0 && !on_public_suffix,
        None => false,
    }
}

/// A response's `Set-Cookie` line is stored only for a request with a
/// non-empty host that is not a public suffix (see the modelling choices).
pub open spec fn store_allowed(rules: Seq<clazel_psl::spec::Rule>, url: clazel_cookie::storage::spec::RequestUrl) -> bool {
    store_allowed_given(url, store_on_public_suffix(rules, url))
}

/// The jar after one `Set-Cookie` line of a response: "act as it would when
/// receiving a set-cookie-string for the request's URL" (RFC 6265bis §5.7
/// through `store_a_set_cookie_string`, with the request's HTTP context), if
/// it is [`store_allowed`]; otherwise unchanged.
pub open spec fn store_one(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, st: HttpStore, now: int) -> Seq<clazel_cookie::storage::spec::Cookie> {
    if store_allowed(rules, st.url) {
        clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, st.line, st.url, st.ctx, now)
    } else {
        jar
    }
}

/// The jar after the `Set-Cookie` lines of a fetch's responses, in order.
pub open spec fn apply_stores(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, stores: Seq<HttpStore>, now: int) -> Seq<clazel_cookie::storage::spec::Cookie>
    decreases stores.len(),
{
    if stores.len() == 0 {
        jar
    } else {
        apply_stores(rules, store_one(rules, jar, stores[0], now), stores.drop_first(), now)
    }
}

/// The fetch a `Fetched { tab, outcome }` event answers, run: `Some` only if
/// the tab is open, its renderer is navigating, and to the URL the outcome
/// was fetched for.
pub open spec fn fetched_run(fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome) -> Option<FetchRun> {
    match find_by_tab(s.renderers, tab, 0) {
        None => None,
        Some(i) => match s.renderers[i].pending {
            None => None,
            Some(p) => if p == outcome.url {
                Some((fetch.run)(p, outcome.net))
            } else {
                None
            },
        },
    }
}

/// The navigation of renderer `old` (at index `i`) ends without a commit:
/// the renderer stays, no longer navigating, and is sent an `Error`.
pub open spec fn fail_navigation(s: State, i: int, old: Renderer, code: u64) -> (State, Seq<Output>) {
    (State { renderers: s.renderers.update(i, Renderer { pending: None, ..old }), ..s }, reply(old, clazel_ipc::message::spec::Message::Error { code }))
}

/// Whether every code point of `s` is a Unicode scalar value: the same as
/// `clazel_encoding::utf8::spec::all_scalar_values` (`lemma_scalar_url`),
/// written by recursion so that Verus can evaluate it on a concrete string.
pub open spec fn scalar_url(s: Seq<u32>) -> bool
    decreases s.len(),
{
    s.len() == 0 || (clazel_encoding::utf8::spec::is_scalar_value(s[0]) && scalar_url(s.drop_first()))
}

/// `Fetched { tab, outcome }`: see the modelling choices. The jar takes the
/// response chain's cookies, then the navigation commits with the final URL
/// and the body, or fails.
pub open spec fn fetched(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome) -> (State, Seq<Output>) {
    match fetched_run(fetch, s, tab, outcome) {
        None => (s, seq![]),
        Some(run) => {
            let i = find_by_tab(s.renderers, tab, 0)->Some_0;
            let old = s.renderers[i];
            let s1 = State { jar: apply_stores(rules, s.jar, run.stores, s.now), ..s };
            match run.result {
                FetchResult::Done { url, body } => if scalar_url(url) && lock_of_url(urls, url, s1.next_id) is Some {
                    navigate_tab(urls, s1, tab, url, body)
                } else {
                    fail_navigation(s1, i, old, error_bad_url())
                },
                FetchResult::Failed => fail_navigation(s1, i, old, error_fetch()),
            }
        },
    }
}

/// `Tick(time)`.
pub open spec fn tick(s: State, time: int) -> (State, Seq<Output>) {
    let now = if time > s.now { time } else { s.now };
    (State { jar: clazel_cookie::storage::spec::evict_expired(s.jar, now), now, ..s }, seq![])
}

/// `RendererExited(id)`: the renderer and its tab are gone.
pub open spec fn renderer_exited(s: State, id: nat) -> (State, Seq<Output>) {
    match find_by_id(s.renderers, id, 0) {
        None => (s, seq![]),
        Some(i) => (State { renderers: s.renderers.remove(i), ..s }, seq![]),
    }
}

/// The message in a frame a renderer sent: it must decode, and be one a
/// renderer may send.
pub open spec fn decode_renderer_frame(bytes: Seq<u8>) -> Option<clazel_ipc::message::spec::Message> {
    match clazel_ipc::message::spec::decode_framed(bytes) {
        Some(m) => if clazel_ipc::message::spec::is_from_renderer(m) { Some(m) } else { None },
        None => None,
    }
}

/// A message that decoded, from the renderer `r`.
pub open spec fn handle_message(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    s: State,
    r: Renderer,
    m: clazel_ipc::message::spec::Message,
) -> (State, Seq<Output>) {
    match m {
        // The getter: "if the document is a cookie-averse Document object,
        // then the user agent must return the empty string. [...]
        // Otherwise, the user agent must return the cookie-string for the
        // document's URL for a "non-HTTP" API".
        clazel_ipc::message::spec::Message::CookieGet => if cookie_averse(rules, r.lock) {
            (s, reply(r, clazel_ipc::message::spec::Message::CookieValue { cookie_string: seq![] }))
        } else {
            let url = request_url_of(urls, r);
            let ctx = document_context(r.lock);
            (
                State { jar: clazel_cookie::storage::spec::jar_after_retrieval(rules, s.jar, url, ctx, s.now), ..s },
                reply(r, clazel_ipc::message::spec::Message::CookieValue { cookie_string: clazel_cookie::storage::spec::retrieve_cookie_string(rules, s.jar, url, ctx, s.now) }),
            )
        },
        // The setter: "if the document is a cookie-averse Document object,
        // then the user agent must do nothing. [...] Otherwise, the user
        // agent must act as it would when receiving a set-cookie-string for
        // the document's URL via a "non-HTTP" API".
        clazel_ipc::message::spec::Message::CookieSet { cookie_string } => if cookie_averse(rules, r.lock) {
            (s, seq![])
        } else {
            let url = request_url_of(urls, r);
            let ctx = document_context(r.lock);
            (State { jar: clazel_cookie::storage::spec::store_a_set_cookie_string(rules, s.jar, cookie_string, url, ctx, s.now), ..s }, seq![])
        },
        // `localStorage`: "Throws a SecurityError DOMException if the
        // Document's origin is an opaque origin".
        clazel_ipc::message::spec::Message::StorageGetItem { .. }
        | clazel_ipc::message::spec::Message::StorageSetItem { .. }
        | clazel_ipc::message::spec::Message::StorageRemoveItem { .. }
        | clazel_ipc::message::spec::Message::StorageClear
        | clazel_ipc::message::spec::Message::StorageKey { .. }
        | clazel_ipc::message::spec::Message::StorageLength => if r.lock is Opaque {
            (s, reply(r, clazel_ipc::message::spec::Message::Error { code: error_security() }))
        } else {
            storage_call(s, r, m)
        },
        // `Navigate { url }`: resolve against the committed URL, then
        // exactly `NavigateTab(its tab, resolved)`.
        clazel_ipc::message::spec::Message::Navigate { url } => match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            None => (s, reply(r, clazel_ipc::message::spec::Message::Error { code: error_bad_url() })),
            Some(relative) => match (urls.resolve)(r.url, relative) {
                None => (s, reply(r, clazel_ipc::message::spec::Message::Error { code: error_bad_url() })),
                Some(resolved) => if lock_of_url(urls, resolved, s.next_id) is None {
                    (s, reply(r, clazel_ipc::message::spec::Message::Error { code: error_bad_url() }))
                } else {
                    begin_navigation(urls, s, r.tab, resolved)
                },
            },
        },
        // A message a renderer may not send: unreachable, see
        // `decode_renderer_frame`.
        _ => (s, seq![]),
    }
}

/// `FromRenderer(id, bytes)`.
pub open spec fn from_renderer(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    s: State,
    id: nat,
    bytes: Seq<u8>,
) -> (State, Seq<Output>) {
    match find_by_id(s.renderers, id, 0) {
        // An id that names no renderer: ignored.
        None => (s, seq![]),
        Some(i) => match decode_renderer_frame(bytes) {
            // A frame that is not a message a renderer may send: the sender
            // is killed.
            None => (State { renderers: s.renderers.remove(i), ..s }, seq![Output::Kill { id }]),
            Some(m) => handle_message(rules, urls, s, s.renderers[i], m),
        },
    }
}

/// The kernel's step function.
pub open spec fn step(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> (State, Seq<Output>) {
    match e {
        Event::FromRenderer { id, bytes } => from_renderer(rules, urls, s, id, bytes),
        Event::OpenTab { url, script } => open_tab(urls, s, url, script),
        Event::NavigateTab { tab, url } => begin_navigation(urls, s, tab, url),
        Event::Fetched { tab, outcome } => fetched(rules, urls, fetch, s, tab, outcome),
        Event::RendererExited { id } => renderer_exited(s, id),
        Event::Tick { time } => tick(s, time),
    }
}

/// The state after running a trace of events from `s`.
pub open spec fn run_state(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>) -> State
    decreases t.len(),
{
    if t.len() == 0 {
        s
    } else {
        run_state(rules, urls, fetch, step(rules, urls, fetch, s, t[0]).0, t.drop_first())
    }
}

/// The outputs of running a trace of events from `s`, in order.
pub open spec fn run_outputs(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>) -> Seq<Output>
    decreases t.len(),
{
    if t.len() == 0 {
        seq![]
    } else {
        let (s1, out) = step(rules, urls, fetch, s, t[0]);
        out + run_outputs(rules, urls, fetch, s1, t.drop_first())
    }
}

/// `s` is reachable: some trace from [`init_state`] leads to it.
pub open spec fn reachable(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State) -> bool {
    exists|t: Seq<Event>| run_state(rules, urls, fetch, init_state(), t) == s
}

} // verus!
