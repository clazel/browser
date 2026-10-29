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
//! - **A navigation is a fetch, and the kernel steps it (item 3.7).**
//!   `NavigateTab` and a renderer's `Navigate` do not commit: they start a
//!   fetch ([`begin_navigation`]). The tab's renderer records a
//!   [`Navigation`] ([`Renderer::pending`]): the URL it is navigating to and
//!   the state of item 3.6's transducer (`clazel_fetch::transducer::spec`),
//!   started at that URL. The kernel itself steps the transducer, so every
//!   byte on the wire is produced by this function; the network shell is a
//!   pipe: it carries out `Connect`, `Send` and `Close` and reports what
//!   happened as `Net { conn, input }`, `input` being the transducer's
//!   `Connected`, `Bytes`, `Closed` or `Error`. The transducer is a parameter
//!   ([`FetchFns`]: its `HttpFns` and `UrlFns`, and the URL parser that turns
//!   a navigation URL into the transducer's [`clazel_url::url::spec::Url`]),
//!   as [`UrlFns`] is; every theorem holds for every one, as those of
//!   `clazel-fetch` do, and the shipped kernel instantiates it with the real
//!   parsers (`clazel_fetch::transducer::real`).
//! - **Connections are kernel state ([`Connection`]).** A connection has an
//!   id the kernel allocates from its own counter ([`State::next_conn`],
//!   never reused), the tab whose fetch opened it (its owner: the only tab
//!   its events and outputs ever concern), the [`Endpoint`] it connects to
//!   and a **partition key**, the [`Domain`] of the renderer that started the
//!   navigation (the domain of the tab's renderer when [`begin_navigation`]
//!   ran). The key is recorded so that pooling, HTTP/1.1 keep-alive, HTTP/2
//!   multiplexing and coalescing can later choose a connection only within
//!   one domain, which is what keeps noninterference between domains
//!   tractable. Today each transducer `Connect` opens a new connection,
//!   carrying one request with `Connection: close`; which connection a
//!   `Connect` uses is one function, [`choose_connection`], and it is the
//!   decision a later item changes (always `None` now: a new connection).
//!   A connection ends when the transducer asks for its `Close`, when the
//!   shell reports it `Closed` or failed (`Error`), when its navigation ends (`Done` or `Fail`: whatever is left of the tab's
//!   connections is closed with it), when the navigation is replaced by
//!   another, or when its renderer exits or is killed; every `Connect` is
//!   matched by a `Close` once its tab's navigation is over. A `Close` for
//!   a connection the peer has already closed is harmless to the shell.
//! - **A `Net` event is attributed to the connection's tab ([`net`]).**
//!   The tab is the connection's owner, as a frame is attributed to the
//!   renderer of its socket. A `Net` for a connection the kernel does not
//!   know (never opened, or closed since), or whose tab is not navigating, is
//!   ignored in full: no state change, no output, no cookie stored (a cancelled
//!   fetch has no effect, as a stale answer had none). Otherwise the kernel
//!   (1) steps the transducer of the tab's navigation with the kernel's jar and
//!   `now`; (2) applies the jar operations it returns to the jar, in order
//!   ([`apply_net_ops`]): `Retrieved` is `jar_after_retrieval`, `Stored` is RFC
//!   6265bis §5.7 storage kept behind [`store_allowed`]; (3) maps the actions to
//!   outputs on the connections ([`carry_out`]): `Connect` to a connection
//!   ([`open_connection`]) and `Connect` output, `Send` to `Send` on the
//!   connection the event is about, `Close` to `Close` of it; (4) on `Done`
//!   the navigation commits: the final URL is serialized by `clazel-url`'s
//!   URL serializer, must be a string of Unicode scalar values with a lock
//!   (else [`error_bad_url`]), and the tab's renderer commits it with the
//!   response's body as the script ([`navigate_tab`]); on `Fail` the tab's
//!   renderer gets [`error_fetch`] and stays (`fail_navigation`). A redirect
//!   lands wherever the server says: the navigation is the one the user made,
//!   and its final URL is the kernel's to lock (item 2.11 treats a `Navigate`
//!   that resolves as one the user made; a redirect is the same). Starting a
//!   navigation on a tab that is already navigating closes the old
//!   navigation's connections (the replaced fetch has no effect).
//!   A navigation URL the fetch's parser rejects, though it has a lock, fails
//!   at once with [`error_bad_url`] (the real parser rejects exactly those
//!   `origin_of` rejects); one the transducer does not fetch (`start` gives
//!   `Fail(NotFetched)`, e.g. `https:` until TLS) fails with [`error_fetch`].
//! - **The network is outside every renderer domain.** What a `Net` event
//!   carries came from a server. A server can echo the cookies it receives
//!   into a body, and a redirect can hand that body, or a `Location`, to the
//!   tab of another site: that is how the web behaves, not a flow through the
//!   kernel, and no theorem here says otherwise. What the kernel proves is
//!   that the only part of the wire derived from the jar is the `Cookie`
//!   field of the request, and that field is §5.8's cookie-string for that
//!   request (`wire_cookies_statement`, from item 3.6's `theorem_wire_cookies`);
//!   and that the shell is never given the jar. The noninterference theorem
//!   treats a `Net` event as an input that belongs to no renderer domain (it
//!   is kept in every observer's purge, see `domain.rs`).
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

/// The state of item 3.6's transducer for one navigation.
pub type FetchState = clazel_fetch::transducer::spec::State;

/// What the network shell reports of a connection: the transducer's `Input`
/// (`Connected`, `Bytes`, `Closed` or `Error`).
pub type NetInput = clazel_fetch::transducer::spec::Input;

/// What the transducer asks for (`Connect`, `Send`, `Close`, `Done`, `Fail`).
pub type NetAction = clazel_fetch::transducer::spec::Action;

/// One `Set-Cookie` line a response carried, with the request it answers:
/// RFC 6265bis §5.7's inputs ("receives a cookie"). The transducer's `Stored`
/// jar operation, as [`store_one`] reads it.
pub struct HttpStore {
    /// The `Set-Cookie` field value.
    pub line: Seq<u8>,
    /// The URL of the request the response answers.
    pub url: clazel_cookie::storage::spec::RequestUrl,
    /// The request context ("HTTP", with the redirect chain's same-site
    /// status).
    pub ctx: clazel_cookie::storage::spec::RequestContext,
}

/// The transducer, as a parameter of the kernel (see the modelling choices).
/// Item 3.6's `step` and `start` are `clazel_fetch::transducer::spec`'s,
/// over these; the theorems hold for every value.
pub struct FetchFns {
    /// The response parser the transducer reads the connection's octets with.
    pub http: clazel_fetch::transducer::spec::HttpFns,
    /// The URL-side functions of the transducer: the redirect `Location`
    /// parser, the URL origin, the cookie request URL and the Public Suffix
    /// List it reads the jar with. (The shipped kernel gives the same list
    /// as the kernel's `rules`.)
    pub urls: clazel_fetch::transducer::spec::UrlFns,
    /// The URL parser on a navigation URL (a string of code points the
    /// kernel has accepted): the URL record the transducer fetches, or
    /// `None` for failure.
    pub parse: spec_fn(Seq<u32>) -> Option<clazel_url::url::spec::Url>,
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
    /// The navigation its tab has in flight (item 3.7); `None` once it
    /// commits or fails.
    pub pending: Option<Navigation>,
}

/// A navigation in flight: the fetch of the URL the tab is navigating to.
pub struct Navigation {
    /// The URL the tab is navigating to (absolute; what `begin_navigation`
    /// locked). The fetch may redirect elsewhere.
    pub url: Seq<u32>,
    /// The state of the fetch: item 3.6's transducer, which only the `Net`
    /// events of this navigation's connections step.
    pub fetch: FetchState,
    /// The domain of the renderer that started the navigation: the
    /// partition key of every connection the fetch opens.
    pub partition: crate::domain::Domain,
}

/// Where a connection goes: the network half of an origin, as the transducer
/// asks for it.
pub struct Endpoint {
    /// The host, as the resolver takes it.
    pub host: Seq<u8>,
    /// The port.
    pub port: nat,
    /// Whether to speak TLS on it.
    pub tls: bool,
}

/// A connection the kernel has asked the network shell for and not closed.
pub struct Connection {
    /// Its id: from [`State::next_conn`], never reused.
    pub id: nat,
    /// The tab whose navigation opened it, and the only tab its events and
    /// outputs concern.
    pub tab: nat,
    /// The origin it connects to.
    pub endpoint: Endpoint,
    /// The partition key: the domain the navigation belongs to. A connection
    /// is chosen for a fetch only within its own partition
    /// ([`choose_connection`]).
    pub partition: crate::domain::Domain,
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
    /// The open connections, each owned by one tab with a navigation in
    /// flight (item 3.7).
    pub conns: Seq<Connection>,
    /// The next fresh connection id.
    pub next_conn: nat,
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
    /// The network shell reports on a connection the kernel asked for
    /// (item 3.7): it is open, bytes arrived, the peer closed it, or it
    /// failed.
    Net {
        /// The connection.
        conn: nat,
        /// What happened to it.
        input: NetInput,
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
    /// Ask the network shell to open connection `conn` (item 3.7). Addressed
    /// to no renderer; the shell reports `Connected` or `Error` as
    /// `Net { conn, .. }`.
    Connect {
        /// The connection.
        conn: nat,
        /// The host, as the resolver takes it.
        host: Seq<u8>,
        /// The port.
        port: nat,
        /// Whether to speak TLS on it.
        tls: bool,
    },
    /// Write these octets to connection `conn`: bytes the kernel built.
    Send {
        /// The connection.
        conn: nat,
        /// The octets.
        bytes: Seq<u8>,
    },
    /// Close connection `conn` (a no-op for the shell if it is already
    /// closed).
    Close {
        /// The connection.
        conn: nat,
    },
}

/// The kernel before anything happens.
pub open spec fn init_state() -> State {
    State { renderers: seq![], jar: seq![], storage: Map::empty(), next_id: 0, conns: seq![], next_conn: 0, now: 0 }
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

/// The index of the first connection from `i` on with id `id`.
pub open spec fn find_conn(cs: Seq<Connection>, id: nat, i: nat) -> Option<int>
    decreases cs.len() - i,
{
    if i >= cs.len() {
        None
    } else if cs[i as int].id == id {
        Some(i as int)
    } else {
        find_conn(cs, id, i + 1)
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
/// `url` running `script`: the shared body of a successful navigation
/// ([`commit_navigation`]: the final URL and the body) and, as item 2.11 states it, what a navigation
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
/// starts navigating to `url`, which starts the fetch (item 3.7). The
/// renderer, its URL and its lock are unchanged; a navigation already in
/// flight is replaced, and its connections are closed.
///
/// The fetch is item 3.6's `start` at the URL the fetch's parser gives. Its
/// actions are carried out as those of a step are ([`carry_out`]): `Connect`
/// for the first request, or `Fail(NotFetched)` for a URL the transducer
/// does not fetch.
pub open spec fn begin_navigation(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    tab: nat,
    url: Seq<u32>,
) -> (State, Seq<Output>) {
    match find_by_tab(s.renderers, tab, 0) {
        // No such tab (or its renderer has exited): nothing to navigate.
        None => (s, seq![]),
        Some(i) => match lock_of_url(urls, url, s.next_id) {
            // A URL that does not parse, or has no lock: ignored.
            None => (s, seq![]),
            Some(_) => {
                let (s0, closes) = close_tab_conns(s, tab);
                let old = s0.renderers[i];
                match (fetch.parse)(url) {
                    // A URL the fetch's parser does not accept.
                    None => {
                        let (s1, out) = fail_navigation(s0, i, old, error_bad_url());
                        (s1, closes + out)
                    },
                    Some(parsed) => {
                        let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                        let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                        let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                        let (s2, out) = carry_out(urls, s1, tab, nav.partition, None, actions);
                        (s2, closes + out)
                    },
                }
            },
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

/// The jar after one jar operation of the transducer: `Retrieved` is RFC
/// 6265bis §5.8.3 step 5's update and the eviction of expired cookies
/// (`jar_after_retrieval`); `Stored` is §5.7 storage of one `Set-Cookie` line
/// ([`store_one`]: only if [`store_allowed`]).
pub open spec fn apply_net_op(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, op: clazel_fetch::transducer::spec::JarOp) -> Seq<clazel_cookie::storage::spec::Cookie> {
    match op {
        clazel_fetch::transducer::spec::JarOp::Retrieved { url, ctx, now } => clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now),
        clazel_fetch::transducer::spec::JarOp::Stored { line, url, ctx, now } => store_one(rules, jar, HttpStore { line, url, ctx }, now),
    }
}

/// The jar after the jar operations of one transducer step, in order.
pub open spec fn apply_net_ops(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, ops: Seq<clazel_fetch::transducer::spec::JarOp>) -> Seq<clazel_cookie::storage::spec::Cookie>
    decreases ops.len(),
{
    if ops.len() == 0 {
        jar
    } else {
        apply_net_ops(rules, apply_net_op(rules, jar, ops[0]), ops.drop_first())
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

// ---------------------------------------------------------------------
// Connections (item 3.7).
// ---------------------------------------------------------------------

/// `conns` without the connections of `tab`.
pub open spec fn without_tab(conns: Seq<Connection>, tab: nat) -> Seq<Connection> {
    conns.filter(|c: Connection| c.tab != tab)
}

/// `conns` without the connection `id`.
pub open spec fn without_conn(conns: Seq<Connection>, id: nat) -> Seq<Connection> {
    conns.filter(|c: Connection| c.id != id)
}

/// `Close` for each connection of `tab`, in order.
pub open spec fn closes_of_tab(conns: Seq<Connection>, tab: nat) -> Seq<Output>
    decreases conns.len(),
{
    if conns.len() == 0 {
        seq![]
    } else {
        (if conns[0].tab == tab {
            seq![Output::Close { conn: conns[0].id }]
        } else {
            seq![]
        }) + closes_of_tab(conns.drop_first(), tab)
    }
}

/// Every connection of `tab` is closed: the navigation that owned them is
/// over, replaced, or gone with its renderer.
pub open spec fn close_tab_conns(s: State, tab: nat) -> (State, Seq<Output>) {
    (State { conns: without_tab(s.conns, tab), ..s }, closes_of_tab(s.conns, tab))
}

/// **The one decision about reusing a connection.** The connection a
/// transducer `Connect` to `endpoint` is carried by, for the navigation of
/// `tab` in `partition`: `Some(id)` is an open connection to use instead of
/// a new one, `None` a new one. Today it is always `None`: each request
/// opens its own connection and carries `Connection: close` (item 3.6), so a
/// connection is used by one tab for one request. HTTP/1.1 keep-alive,
/// HTTP/2 multiplexing and coalescing are changes to this function and to
/// nothing else in the state machine: a connection it returns must be of
/// `partition` (so of one domain), and the ownership and noninterference
/// theorems are then restated over that.
pub open spec fn choose_connection(s: State, tab: nat, partition: crate::domain::Domain, endpoint: Endpoint) -> Option<nat> {
    None
}

/// A transducer `Connect` to `endpoint` for `tab`: the connection that
/// carries it and, if it is new, its record and the `Connect` output.
pub open spec fn open_connection(s: State, tab: nat, partition: crate::domain::Domain, endpoint: Endpoint) -> (State, nat, Seq<Output>) {
    match choose_connection(s, tab, partition, endpoint) {
        Some(id) => (s, id, seq![]),
        None => {
            let id = s.next_conn;
            (
                State { conns: s.conns.push(Connection { id, tab, endpoint, partition }), next_conn: id + 1, ..s },
                id,
                seq![Output::Connect { conn: id, host: endpoint.host, port: endpoint.port, tls: endpoint.tls }],
            )
        },
    }
}

/// The navigation of `tab` ends with the document at the final URL `href`
/// and the response's `body`: its connections are closed, then, if `href`
/// is a string of Unicode scalar values with a lock, the tab's renderer
/// commits it ([`navigate_tab`]); otherwise the navigation fails with
/// [`error_bad_url`].
pub open spec fn commit_navigation(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Seq<u8>) -> (State, Seq<Output>) {
    let (s1, closes) = close_tab_conns(s, tab);
    match find_by_tab(s1.renderers, tab, 0) {
        None => (s1, closes),
        Some(i) => {
            let (s2, out) = if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
                navigate_tab(urls, s1, tab, href, body)
            } else {
                fail_navigation(s1, i, s1.renderers[i], error_bad_url())
            };
            (s2, closes + out)
        },
    }
}

/// The navigation of `tab` fails with `code`: its connections are closed and
/// the renderer stays, with an `Error`.
pub open spec fn abort_navigation(s: State, tab: nat, code: u64) -> (State, Seq<Output>) {
    let (s1, closes) = close_tab_conns(s, tab);
    match find_by_tab(s1.renderers, tab, 0) {
        None => (s1, closes),
        Some(i) => {
            let (s2, out) = fail_navigation(s1, i, s1.renderers[i], code);
            (s2, closes + out)
        },
    }
}

/// What the kernel does for the `actions` the transducer gave the navigation
/// of `tab` (of partition `partition`), in order, to the state `s` (whose jar
/// and navigation are already updated). `cur` is the connection the actions
/// apply to: the event's connection, the one just opened after a `Connect`,
/// none after a `Close`.
///
/// - `Connect`: [`open_connection`]; the actions after it are for the
///   connection it returns;
/// - `Send(bytes)`: `Send { conn: cur, bytes }`, the bytes unchanged;
/// - `Close`: `Close { conn: cur }`, and `cur` leaves the table;
/// - `Done { url, response }`: the navigation commits ([`commit_navigation`])
///   `url` serialized by the URL Standard's URL serializer (§4.5, exclude
///   fragment false) with the response's body as the script;
/// - `Fail(_)`: the navigation fails with [`error_fetch`]
///   ([`abort_navigation`]).
///
/// `Done` and `Fail` end the actions (the transducer gives nothing after
/// them).
pub open spec fn carry_out(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>) -> (State, Seq<Output>)
    decreases actions.len(),
{
    if actions.len() == 0 {
        (s, seq![])
    } else {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (s1, id, out) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                let (s2, out2) = carry_out(urls, s1, tab, partition, Some(id), rest);
                (s2, out + out2)
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => match cur {
                Some(c) => {
                    let (s1, out) = carry_out(urls, s, tab, partition, cur, rest);
                    (s1, seq![Output::Send { conn: c, bytes }] + out)
                },
                None => carry_out(urls, s, tab, partition, cur, rest),
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let (s1, out) = carry_out(urls, State { conns: without_conn(s.conns, c), ..s }, tab, partition, None, rest);
                    (s1, seq![Output::Close { conn: c }] + out)
                },
                None => carry_out(urls, s, tab, partition, cur, rest),
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => commit_navigation(
                urls,
                s,
                tab,
                clazel_url::url::spec::url_serializer(url, false),
                response.body,
            ),
            clazel_fetch::transducer::spec::Action::Fail(_) => abort_navigation(s, tab, error_fetch()),
        }
    }
}

/// The navigation a `Net` event for connection `conn` is about: the
/// connection, the index of its tab's renderer and that renderer's navigation.
/// `None` if the connection is not open, its tab has gone, or its tab is not
/// navigating.
pub open spec fn net_target(s: State, conn: nat) -> Option<(Connection, int, Navigation)> {
    match find_conn(s.conns, conn, 0) {
        None => None,
        Some(ci) => match find_by_tab(s.renderers, s.conns[ci].tab, 0) {
            None => None,
            Some(i) => match s.renderers[i].pending {
                None => None,
                Some(nav) => Some((s.conns[ci], i, nav)),
            },
        },
    }
}

/// The transducer's step for `input` on a navigation, with the kernel's jar
/// and time: item 3.6's `step`, its next state, actions and jar operations.
pub open spec fn net_transducer_step(fetch: FetchFns, s: State, nav: Navigation, input: NetInput) -> (FetchState, Seq<NetAction>, Seq<clazel_fetch::transducer::spec::JarOp>) {
    clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now)
}

/// `Net { conn, input }`: see the modelling choices. If the connection is
/// open and its tab is navigating, the kernel steps the transducer of the
/// navigation with its jar and the time, applies the jar operations to its
/// jar, and carries out the actions on the connections; otherwise the event is
/// ignored.
pub open spec fn net(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput) -> (State, Seq<Output>) {
    match net_target(s, conn) {
        None => (s, seq![]),
        Some((c, i, nav)) => {
            let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
            // The peer closing a connection, or it failing, ends it: the
            // kernel forgets it before anything else (a `Close` the transducer
            // asks for after it is then harmless to the shell).
            let conns = if input is Closed || input is Error {
                without_conn(s.conns, conn)
            } else {
                s.conns
            };
            let s1 = State {
                jar: apply_net_ops(rules, s.jar, ops),
                conns,
                renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] }),
                ..s
            };
            carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions)
        },
    }
}

/// `Tick(time)`.
pub open spec fn tick(s: State, time: int) -> (State, Seq<Output>) {
    let now = if time > s.now { time } else { s.now };
    (State { jar: clazel_cookie::storage::spec::evict_expired(s.jar, now), now, ..s }, seq![])
}

/// `RendererExited(id)`: the renderer and its tab are gone, and the
/// connections of its navigation are closed.
pub open spec fn renderer_exited(s: State, id: nat) -> (State, Seq<Output>) {
    match find_by_id(s.renderers, id, 0) {
        None => (s, seq![]),
        Some(i) => {
            let (s0, closes) = close_tab_conns(s, s.renderers[i].tab);
            (State { renderers: s.renderers.remove(i), ..s0 }, closes)
        },
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
    fetch: FetchFns,
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
                    begin_navigation(rules, urls, fetch, s, r.tab, resolved)
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
    fetch: FetchFns,
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
            None => {
                let (s0, closes) = close_tab_conns(s, s.renderers[i].tab);
                (State { renderers: s.renderers.remove(i), ..s0 }, seq![Output::Kill { id }] + closes)
            },
            Some(m) => handle_message(rules, urls, fetch, s, s.renderers[i], m),
        },
    }
}

/// The kernel's step function.
pub open spec fn step(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> (State, Seq<Output>) {
    match e {
        Event::FromRenderer { id, bytes } => from_renderer(rules, urls, fetch, s, id, bytes),
        Event::OpenTab { url, script } => open_tab(urls, s, url, script),
        Event::NavigateTab { tab, url } => begin_navigation(rules, urls, fetch, s, tab, url),
        Event::Net { conn, input } => net(rules, urls, fetch, s, conn, input),
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
