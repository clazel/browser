//! The exec state, events and outputs of the kernel, each with a `view` to the
//! spec type of [`crate::spec`]. Ids are `u64`s, the jar is `clazel-cookie`'s
//! (item 2.9), and Web Storage is a vector of buckets, one per origin.

#[allow(unused_imports)]
use super::spec::*;
use clazel_cookie::matching::exec::CanonicalHostName;
use clazel_cookie::storage::exec::CookieRecord;
use clazel_fetch::transducer::types::{InputBuf, StateBuf};
use clazel_origin::exec::ParsedOrigin;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Renderers.
// ---------------------------------------------------------------------

/// A renderer process, viewed as [`Renderer`].
pub struct RendererRecord {
    /// The id.
    pub id: u64,
    /// The tab.
    pub tab: u64,
    /// The committed URL, absolute.
    pub url: Vec<u32>,
    /// The lock.
    pub lock: ParsedOrigin,
    /// The navigation its tab has in flight.
    pub pending: Option<NavigationRecord>,
}

impl View for RendererRecord {
    type V = Renderer;

    open spec fn view(&self) -> Renderer {
        Renderer { id: self.id as nat, tab: self.tab as nat, url: self.url@, lock: self.lock@, pending: navigation_opt_view(self.pending) }
    }
}

/// A security domain, viewed as [`crate::domain::Domain`].
pub enum DomainRecord {
    /// The renderers locked to origins with this cookie root.
    Root(CanonicalHostName),
    /// One renderer whose lock is the opaque origin of this id.
    Opaque(u64),
}

impl View for DomainRecord {
    type V = crate::domain::Domain;

    open spec fn view(&self) -> crate::domain::Domain {
        match self {
            DomainRecord::Root(h) => crate::domain::Domain::Root(h@),
            DomainRecord::Opaque(id) => crate::domain::Domain::Opaque(*id as nat),
        }
    }
}

/// A navigation in flight, viewed as [`Navigation`]. The transducer's state
/// is the exec `StateBuf`, whose parser is the one octets are fed into.
pub struct NavigationRecord {
    /// The URL the tab is navigating to.
    pub url: Vec<u32>,
    /// The transducer's state.
    pub fetch: StateBuf,
    /// The partition key.
    pub partition: DomainRecord,
}

impl View for NavigationRecord {
    type V = Navigation;

    open spec fn view(&self) -> Navigation {
        Navigation { url: self.url@, fetch: self.fetch@, partition: self.partition@ }
    }
}

/// The view of an optional navigation.
pub open spec fn navigation_opt_view(o: Option<NavigationRecord>) -> Option<Navigation> {
    match o {
        Some(n) => Some(n@),
        None => None,
    }
}

/// Where a connection goes, viewed as [`Endpoint`].
pub struct EndpointRecord {
    /// The host.
    pub host: Vec<u8>,
    /// The port.
    pub port: u64,
    /// Whether to speak TLS.
    pub tls: bool,
}

impl View for EndpointRecord {
    type V = Endpoint;

    open spec fn view(&self) -> Endpoint {
        Endpoint { host: self.host@, port: self.port as nat, tls: self.tls }
    }
}

/// An open connection, viewed as [`Connection`].
pub struct ConnectionRecord {
    /// Its id.
    pub id: u64,
    /// The tab that owns it.
    pub tab: u64,
    /// Where it goes.
    pub endpoint: EndpointRecord,
    /// The partition key.
    pub partition: DomainRecord,
}

impl View for ConnectionRecord {
    type V = Connection;

    open spec fn view(&self) -> Connection {
        Connection { id: self.id as nat, tab: self.tab as nat, endpoint: self.endpoint@, partition: self.partition@ }
    }
}

/// The view of a table of connections.
pub open spec fn conns_view(v: Seq<ConnectionRecord>) -> Seq<Connection> {
    v.map_values(|c: ConnectionRecord| c@)
}

/// A copy of a domain.
pub fn clone_domain(d: &DomainRecord) -> (r: DomainRecord)
    ensures
        r@ == d@,
{
    match d {
        DomainRecord::Root(h) => DomainRecord::Root(CanonicalHostName { name: vstd::slice::slice_to_vec(h.name.as_slice()), is_ip_address: h.is_ip_address }),
        DomainRecord::Opaque(id) => DomainRecord::Opaque(*id),
    }
}

/// A copy of an endpoint.
pub fn clone_endpoint(e: &EndpointRecord) -> (r: EndpointRecord)
    ensures
        r@ == e@,
{
    EndpointRecord { host: vstd::slice::slice_to_vec(e.host.as_slice()), port: e.port, tls: e.tls }
}

/// A copy of a connection.
pub fn clone_conn(c: &ConnectionRecord) -> (r: ConnectionRecord)
    ensures
        r@ == c@,
{
    ConnectionRecord { id: c.id, tab: c.tab, endpoint: clone_endpoint(&c.endpoint), partition: clone_domain(&c.partition) }
}

/// `conns` without the connections of `tab` ([`without_tab`]).
pub fn without_tab_exec(conns: &[ConnectionRecord], tab: u64) -> (out: Vec<ConnectionRecord>)
    ensures
        conns_view(out@) == without_tab(conns_view(conns@), tab as nat),
{
    let ghost cv = conns_view(conns@);
    let mut out: Vec<ConnectionRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(cv.take(0) =~= Seq::<Connection>::empty());
    }
    while k < conns.len()
        invariant
            k <= conns.len(),
            cv == conns_view(conns@),
            conns_view(out@) == cv.take(k as int).filter(|c: Connection| c.tab != tab as nat),
        decreases conns.len() - k,
    {
        if let Some(c) = conns.get(k) {
            proof {
                reveal(Seq::filter);
                assert(cv.take(k as int + 1).drop_last() =~= cv.take(k as int));
                assert(cv.take(k as int + 1).last() == c@);
            }
            if c.tab != tab {
                out.push(clone_conn(c));
            }
        }
        // Never saturates: k < conns.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(cv.take(conns.len() as int) =~= cv);
    }
    out
}

/// `conns` without the connection `id` ([`without_conn`]).
pub fn without_conn_exec(conns: &[ConnectionRecord], id: u64) -> (out: Vec<ConnectionRecord>)
    ensures
        conns_view(out@) == without_conn(conns_view(conns@), id as nat),
{
    let ghost cv = conns_view(conns@);
    let mut out: Vec<ConnectionRecord> = Vec::new();
    let mut k: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(cv.take(0) =~= Seq::<Connection>::empty());
    }
    while k < conns.len()
        invariant
            k <= conns.len(),
            cv == conns_view(conns@),
            conns_view(out@) == cv.take(k as int).filter(|c: Connection| c.id != id as nat),
        decreases conns.len() - k,
    {
        if let Some(c) = conns.get(k) {
            proof {
                reveal(Seq::filter);
                assert(cv.take(k as int + 1).drop_last() =~= cv.take(k as int));
                assert(cv.take(k as int + 1).last() == c@);
            }
            if c.id != id {
                out.push(clone_conn(c));
            }
        }
        // Never saturates: k < conns.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(cv.take(conns.len() as int) =~= cv);
    }
    out
}

/// Adding a connection adds it to the view.
pub proof fn lemma_conns_view_push(v: Seq<ConnectionRecord>, c: ConnectionRecord)
    ensures
        conns_view(v.push(c)) =~= conns_view(v).push(c@),
{
}

/// The view of a table of renderers.
pub open spec fn renderers_view(v: Seq<RendererRecord>) -> Seq<Renderer> {
    v.map_values(|r: RendererRecord| r@)
}

/// Updating a renderer updates the view.
pub proof fn lemma_renderers_view_update(v: Seq<RendererRecord>, i: int, r: RendererRecord)
    requires
        0 <= i < v.len(),
    ensures
        renderers_view(v.update(i, r)) =~= renderers_view(v).update(i, r@),
{
}

/// Removing a renderer removes it from the view.
pub proof fn lemma_renderers_view_remove(v: Seq<RendererRecord>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        renderers_view(v.remove(i)) =~= renderers_view(v).remove(i),
{
}

/// Adding a renderer adds it to the view.
pub proof fn lemma_renderers_view_push(v: Seq<RendererRecord>, r: RendererRecord)
    ensures
        renderers_view(v.push(r)) =~= renderers_view(v).push(r@),
{
}

// ---------------------------------------------------------------------
// Web Storage.
// ---------------------------------------------------------------------

/// A key and value pair, viewed as [`StorageEntry`].
pub struct StorageEntryRecord {
    /// The key.
    pub key: Vec<u8>,
    /// The value.
    pub value: Vec<u8>,
}

impl View for StorageEntryRecord {
    type V = StorageEntry;

    open spec fn view(&self) -> StorageEntry {
        StorageEntry { key: self.key@, value: self.value@ }
    }
}

/// The view of an ordered list of entries.
pub open spec fn entries_view(v: Seq<StorageEntryRecord>) -> Seq<StorageEntry> {
    v.map_values(|e: StorageEntryRecord| e@)
}

/// One origin's map: the origin and its non-empty ordered list of entries.
pub struct StorageBucket {
    /// The origin (a tuple origin).
    pub origin: ParsedOrigin,
    /// The ordered entries.
    pub entries: Vec<StorageEntryRecord>,
}

/// The origins of the buckets are distinct and each bucket is non-empty.
pub open spec fn buckets_wf(v: Seq<StorageBucket>) -> bool {
    &&& forall|i: int, j: int| 0 <= i < j < v.len() ==> (#[trigger] v[i]).origin@ != (#[trigger] v[j]).origin@
    &&& forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).entries@.len() > 0
}

/// The index of the bucket of `o` (any, if there are several).
pub open spec fn bucket_index(v: Seq<StorageBucket>, o: clazel_origin::spec::Origin) -> int {
    choose|i: int| 0 <= i < v.len() && (#[trigger] v[i]).origin@ == o
}

/// The origins of the buckets.
pub open spec fn bucket_origins(v: Seq<StorageBucket>) -> Seq<clazel_origin::spec::Origin> {
    v.map_values(|b: StorageBucket| b.origin@)
}

/// The view of a vector of buckets: a map from origin to its entries.
pub open spec fn storage_view(v: Seq<StorageBucket>) -> Map<clazel_origin::spec::Origin, Seq<StorageEntry>> {
    Map::new(bucket_origins(v).to_set(), |o: clazel_origin::spec::Origin| entries_view(v[bucket_index(v, o)].entries@))
}

/// The map's domain is the set of the buckets' origins.
pub proof fn lemma_storage_view_dom(v: Seq<StorageBucket>, o: clazel_origin::spec::Origin)
    ensures
        storage_view(v).dom().contains(o) <==> exists|i: int| 0 <= i < v.len() && (#[trigger] v[i]).origin@ == o,
{
    let origins = bucket_origins(v);
    origins.to_set_ensures();
    assert(storage_view(v).dom().contains(o) <==> origins.contains(o));
    if origins.contains(o) {
        let i = choose|i: int| 0 <= i < origins.len() && origins[i] == o;
        assert(v[i].origin@ == o);
    }
    if exists|i: int| 0 <= i < v.len() && (#[trigger] v[i]).origin@ == o {
        let i = choose|i: int| 0 <= i < v.len() && (#[trigger] v[i]).origin@ == o;
        assert(origins[i] == o);
    }
}

// ---------------------------------------------------------------------
// The state.
// ---------------------------------------------------------------------

/// The kernel's state, viewed as [`State`].
pub struct StateRecord {
    /// The live renderers.
    pub renderers: Vec<RendererRecord>,
    /// The cookie jar.
    pub jar: Vec<CookieRecord>,
    /// Web Storage: one bucket per origin.
    pub storage: Vec<StorageBucket>,
    /// The next fresh id.
    pub next_id: u64,
    /// The open connections.
    pub conns: Vec<ConnectionRecord>,
    /// The next fresh connection id.
    pub next_conn: u64,
    /// The current time (seconds since 1601-01-01T00:00:00Z).
    pub now: u64,
}

impl View for StateRecord {
    type V = State;

    open spec fn view(&self) -> State {
        State {
            renderers: renderers_view(self.renderers@),
            jar: clazel_cookie::storage::exec::jar_view(self.jar@),
            storage: storage_view(self.storage@),
            next_id: self.next_id as nat,
            conns: conns_view(self.conns@),
            next_conn: self.next_conn as nat,
            now: self.now as int,
        }
    }
}

impl StateRecord {
    /// What the exec state holds beyond its view: the storage buckets are
    /// distinct and non-empty (so that the view's map has one entry per
    /// bucket), and the transducer of each navigation in flight keeps its
    /// parser's invariant for the HTTP functions `h`. [`init_record`] has it,
    /// and `step` keeps it.
    pub open spec fn exec_wf<F: super::fetch::FetchFnsExec>(&self) -> bool {
        &&& buckets_wf(self.storage@)
        &&& super::step::renderers_ok::<F>(self.renderers@)
    }
}

/// The kernel before anything happens ([`init_state`]).
pub fn init_record<F: super::fetch::FetchFnsExec>() -> (s: StateRecord)
    ensures
        s@ == init_state(),
        s.exec_wf::<F>(),
{
    let s = StateRecord { renderers: Vec::new(), jar: Vec::new(), storage: Vec::new(), next_id: 0, conns: Vec::new(), next_conn: 0, now: 0 };
    proof {
        assert(conns_view(s.conns@) =~= Seq::<Connection>::empty());
        assert(renderers_view(s.renderers@) =~= Seq::<Renderer>::empty());
        assert(clazel_cookie::storage::exec::jar_view(s.jar@) =~= Seq::<clazel_cookie::storage::spec::Cookie>::empty());
        assert(storage_view(s.storage@) =~= Map::<clazel_origin::spec::Origin, Seq<StorageEntry>>::empty());
    }
    s
}

// ---------------------------------------------------------------------
// Events and outputs.
// ---------------------------------------------------------------------

/// An event, viewed as [`Event`].
pub enum EventRecord {
    /// A whole frame from the socket of renderer `id`.
    FromRenderer {
        /// The renderer.
        id: u64,
        /// The frame.
        bytes: Vec<u8>,
    },
    /// The user opens a tab.
    OpenTab {
        /// The URL.
        url: Vec<u32>,
        /// The script (UTF-8 text).
        script: Vec<u8>,
    },
    /// The user navigates a tab.
    NavigateTab {
        /// The tab.
        tab: u64,
        /// The URL.
        url: Vec<u32>,
    },
    /// The network shell reports on a connection.
    Net {
        /// The connection.
        conn: u64,
        /// What happened to it.
        input: InputBuf,
    },
    /// A renderer exited.
    RendererExited {
        /// The renderer.
        id: u64,
    },
    /// The clock advanced.
    Tick {
        /// The time.
        time: u64,
    },
}

impl View for EventRecord {
    type V = Event;

    open spec fn view(&self) -> Event {
        match self {
            EventRecord::FromRenderer { id, bytes } => Event::FromRenderer { id: *id as nat, bytes: bytes@ },
            EventRecord::OpenTab { url, script } => Event::OpenTab { url: url@, script: script@ },
            EventRecord::NavigateTab { tab, url } => Event::NavigateTab { tab: *tab as nat, url: url@ },
            EventRecord::Net { conn, input } => Event::Net { conn: *conn as nat, input: input@ },
            EventRecord::RendererExited { id } => Event::RendererExited { id: *id as nat },
            EventRecord::Tick { time } => Event::Tick { time: *time as int },
        }
    }
}

/// An output, viewed as [`Output`]. A spawn names the one [`Policy`].
pub enum OutputRecord {
    /// Send a whole frame to the renderer.
    ToRenderer {
        /// The renderer.
        id: u64,
        /// The frame.
        bytes: Vec<u8>,
    },
    /// Start a renderer process under the renderer sandbox.
    Spawn {
        /// The new renderer.
        id: u64,
    },
    /// Kill the renderer process.
    Kill {
        /// The renderer.
        id: u64,
    },
    /// Ask the network shell to open a connection.
    Connect {
        /// The connection.
        conn: u64,
        /// The host.
        host: Vec<u8>,
        /// The port.
        port: u64,
        /// Whether to speak TLS.
        tls: bool,
    },
    /// Write these octets to a connection.
    Send {
        /// The connection.
        conn: u64,
        /// The octets.
        bytes: Vec<u8>,
    },
    /// Close a connection.
    Close {
        /// The connection.
        conn: u64,
    },
}

impl View for OutputRecord {
    type V = Output;

    open spec fn view(&self) -> Output {
        match self {
            OutputRecord::ToRenderer { id, bytes } => Output::ToRenderer { id: *id as nat, bytes: bytes@ },
            OutputRecord::Spawn { id } => Output::Spawn { id: *id as nat, policy: Policy::Renderer },
            OutputRecord::Kill { id } => Output::Kill { id: *id as nat },
            OutputRecord::Connect { conn, host, port, tls } => Output::Connect { conn: *conn as nat, host: host@, port: *port as nat, tls: *tls },
            OutputRecord::Send { conn, bytes } => Output::Send { conn: *conn as nat, bytes: bytes@ },
            OutputRecord::Close { conn } => Output::Close { conn: *conn as nat },
        }
    }
}

/// The view of a list of outputs.
pub open spec fn outputs_view(v: Seq<OutputRecord>) -> Seq<Output> {
    v.map_values(|o: OutputRecord| o@)
}

/// No outputs.
pub fn no_outputs() -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == Seq::<Output>::empty(),
{
    let v: Vec<OutputRecord> = Vec::new();
    assert(outputs_view(v@) =~= Seq::<Output>::empty());
    v
}

/// One output.
pub fn one_output(o: OutputRecord) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == seq![o@],
{
    let ghost go = o@;
    let v = vec![o];
    assert(outputs_view(v@) =~= seq![go]);
    v
}

/// The view of a list with an output added.
pub proof fn lemma_outputs_view_push(v: Seq<OutputRecord>, o: OutputRecord)
    ensures
        outputs_view(v.push(o)) =~= outputs_view(v).push(o@),
{
}

/// `o` added to the list.
pub fn push_output(v: &mut Vec<OutputRecord>, o: OutputRecord)
    ensures
        outputs_view(final(v)@) == outputs_view(old(v)@).push(o@),
{
    let ghost before = v@;
    v.push(o);
    proof {
        lemma_outputs_view_push(before, o);
    }
}

/// `a` followed by `b`.
pub fn append_outputs(a: Vec<OutputRecord>, b: Vec<OutputRecord>) -> (v: Vec<OutputRecord>)
    ensures
        outputs_view(v@) == outputs_view(a@) + outputs_view(b@),
{
    let ghost (ga, gb) = (a@, b@);
    let mut v = a;
    let mut b = b;
    v.append(&mut b);
    proof {
        assert(outputs_view(v@) =~= outputs_view(ga) + outputs_view(gb));
    }
    v
}

// ---------------------------------------------------------------------
// Lemmas on the storage view.
// ---------------------------------------------------------------------

/// A bucket of the vector is in the map, with its entries.
pub proof fn lemma_storage_view_at(v: Seq<StorageBucket>, i: int)
    requires
        buckets_wf(v),
        0 <= i < v.len(),
    ensures
        storage_view(v).dom().contains(v[i].origin@),
        storage_view(v)[v[i].origin@] == entries_view(v[i].entries@),
{
    let o = v[i].origin@;
    lemma_storage_view_dom(v, o);
    let j = bucket_index(v, o);
    assert(0 <= j < v.len() && v[j].origin@ == o);
    if j != i {
        if i < j {
            assert(v[i].origin@ != v[j].origin@);
        } else {
            assert(v[j].origin@ != v[i].origin@);
        }
    }
    assert(j == i);
}

/// An origin that no bucket has is not in the map.
pub proof fn lemma_storage_view_none(v: Seq<StorageBucket>, o: clazel_origin::spec::Origin)
    requires
        forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).origin@ != o,
    ensures
        !storage_view(v).dom().contains(o),
{
}

/// Replacing the entries of bucket `i` (keeping its origin, and non-empty)
/// is an insertion into the map.
pub proof fn lemma_storage_view_update(v: Seq<StorageBucket>, i: int, b: StorageBucket)
    requires
        buckets_wf(v),
        0 <= i < v.len(),
        b.origin@ == v[i].origin@,
        b.entries@.len() > 0,
    ensures
        buckets_wf(v.update(i, b)),
        storage_view(v.update(i, b)) == storage_view(v).insert(b.origin@, entries_view(b.entries@)),
{
    let w = v.update(i, b);
    assert(buckets_wf(w)) by {
        assert forall|p: int, q: int| 0 <= p < q < w.len() implies (#[trigger] w[p]).origin@ != (#[trigger] w[q]).origin@ by {
            assert(w[p] == if p == i { b } else { v[p] });
            assert(w[q] == if q == i { b } else { v[q] });
            assert(w[p].origin@ == v[p].origin@);
            assert(w[q].origin@ == v[q].origin@);
        }
        assert forall|p: int| 0 <= p < w.len() implies (#[trigger] w[p]).entries@.len() > 0 by {
            assert(w[p] == if p == i { b } else { v[p] });
        }
    }
    let m1 = storage_view(w);
    let m2 = storage_view(v).insert(b.origin@, entries_view(b.entries@));
    assert forall|o: clazel_origin::spec::Origin| m1.dom().contains(o) <==> m2.dom().contains(o) by {
        lemma_storage_view_dom(w, o);
        lemma_storage_view_dom(v, o);
        if m1.dom().contains(o) {
            let j = bucket_index(w, o);
            assert(0 <= j < w.len() && w[j].origin@ == o);
            assert(w[j].origin@ == v[j].origin@);
            assert(m2.dom().contains(o));
        }
        if m2.dom().contains(o) {
            if o == b.origin@ {
                assert(w[i].origin@ == o);
            } else {
                assert(storage_view(v).dom().contains(o));
                let j = bucket_index(v, o);
                assert(w[j].origin@ == v[j].origin@);
            }
        }
    }
    assert forall|o: clazel_origin::spec::Origin| m1.dom().contains(o) implies m1[o] == m2[o] by {
        lemma_storage_view_dom(w, o);
        lemma_storage_view_dom(v, o);
        let j = bucket_index(w, o);
        assert(0 <= j < w.len() && w[j].origin@ == o);
        assert(w[j].origin@ == v[j].origin@);
        if o == b.origin@ {
            lemma_storage_view_at(w, i);
            if j != i {
                assert(false);
            }
        } else {
            lemma_storage_view_at(v, j);
            lemma_storage_view_at(w, j);
            assert(w[j] == v[j]);
        }
    }
    assert(m1 =~= m2);
}

/// Adding a bucket for a new origin is an insertion into the map.
pub proof fn lemma_storage_view_push(v: Seq<StorageBucket>, b: StorageBucket)
    requires
        buckets_wf(v),
        forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).origin@ != b.origin@,
        b.entries@.len() > 0,
    ensures
        buckets_wf(v.push(b)),
        storage_view(v.push(b)) == storage_view(v).insert(b.origin@, entries_view(b.entries@)),
{
    let w = v.push(b);
    assert(buckets_wf(w)) by {
        assert forall|p: int, q: int| 0 <= p < q < w.len() implies (#[trigger] w[p]).origin@ != (#[trigger] w[q]).origin@ by {
            if q < v.len() {
                assert(w[p] == v[p]);
                assert(w[q] == v[q]);
            } else {
                assert(w[q] == b);
                assert(w[p] == v[p]);
            }
        }
        assert forall|p: int| 0 <= p < w.len() implies (#[trigger] w[p]).entries@.len() > 0 by {
            if p < v.len() {
                assert(w[p] == v[p]);
            }
        }
    }
    let m1 = storage_view(w);
    let m2 = storage_view(v).insert(b.origin@, entries_view(b.entries@));
    assert forall|o: clazel_origin::spec::Origin| m1.dom().contains(o) <==> m2.dom().contains(o) by {
        lemma_storage_view_dom(w, o);
        lemma_storage_view_dom(v, o);
        if m1.dom().contains(o) {
            let j = bucket_index(w, o);
            assert(0 <= j < w.len() && w[j].origin@ == o);
            if j < v.len() {
                assert(w[j] == v[j]);
                assert(storage_view(v).dom().contains(o));
            } else {
                assert(w[j] == b);
            }
        }
        if m2.dom().contains(o) {
            if o == b.origin@ {
                assert(w[v.len() as int] == b);
            } else {
                let j = bucket_index(v, o);
                assert(w[j] == v[j]);
            }
        }
    }
    assert forall|o: clazel_origin::spec::Origin| m1.dom().contains(o) implies m1[o] == m2[o] by {
        lemma_storage_view_dom(w, o);
        lemma_storage_view_dom(v, o);
        let j = bucket_index(w, o);
        assert(0 <= j < w.len() && w[j].origin@ == o);
        if j < v.len() {
            assert(w[j] == v[j]);
            assert(o != b.origin@);
            lemma_storage_view_at(v, j);
            lemma_storage_view_at(w, j);
        } else {
            assert(w[j] == b);
            lemma_storage_view_at(w, j);
        }
    }
    assert(m1 =~= m2);
}

/// Removing bucket `i` removes its origin from the map.
pub proof fn lemma_storage_view_remove(v: Seq<StorageBucket>, i: int)
    requires
        buckets_wf(v),
        0 <= i < v.len(),
    ensures
        buckets_wf(v.remove(i)),
        storage_view(v.remove(i)) == storage_view(v).remove(v[i].origin@),
{
    let w = v.remove(i);
    assert(buckets_wf(w)) by {
        assert forall|p: int, q: int| 0 <= p < q < w.len() implies (#[trigger] w[p]).origin@ != (#[trigger] w[q]).origin@ by {
            assert(w[p] == v[if p < i { p } else { p + 1 }]);
            assert(w[q] == v[if q < i { q } else { q + 1 }]);
        }
        assert forall|p: int| 0 <= p < w.len() implies (#[trigger] w[p]).entries@.len() > 0 by {
            assert(w[p] == v[if p < i { p } else { p + 1 }]);
        }
    }
    let m1 = storage_view(w);
    let m2 = storage_view(v).remove(v[i].origin@);
    assert forall|o: clazel_origin::spec::Origin| m1.dom().contains(o) <==> m2.dom().contains(o) by {
        lemma_storage_view_dom(w, o);
        lemma_storage_view_dom(v, o);
        if m1.dom().contains(o) {
            let j = bucket_index(w, o);
            assert(0 <= j < w.len() && w[j].origin@ == o);
            let k = if j < i { j } else { j + 1 };
            assert(w[j] == v[k]);
            assert(v[k].origin@ == o);
            assert(storage_view(v).dom().contains(o));
            if o == v[i].origin@ {
                assert(k != i);
                if k < i {
                    assert(v[k].origin@ != v[i].origin@);
                } else {
                    assert(v[i].origin@ != v[k].origin@);
                }
            }
        }
        if m2.dom().contains(o) {
            assert(storage_view(v).dom().contains(o));
            assert(o != v[i].origin@);
            let k = bucket_index(v, o);
            assert(k != i);
            let j = if k < i { k } else { k - 1 };
            assert(w[j] == v[k]);
        }
    }
    assert forall|o: clazel_origin::spec::Origin| m1.dom().contains(o) implies m1[o] == m2[o] by {
        lemma_storage_view_dom(w, o);
        lemma_storage_view_dom(v, o);
        let j = bucket_index(w, o);
        assert(0 <= j < w.len() && w[j].origin@ == o);
        let k = if j < i { j } else { j + 1 };
        assert(w[j] == v[k]);
        lemma_storage_view_at(w, j);
        lemma_storage_view_at(v, k);
    }
    assert(m1 =~= m2);
}

} // verus!
