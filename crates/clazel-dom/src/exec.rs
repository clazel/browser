//! The executable arena (Phase 4 item 4.8): a `Vec` of nodes indexed by
//! id, whose view is the spec's [`Document`]. Every mutating method's
//! `requires` and `ensures` are the predicates of [`super::contract`] (and
//! the spec's `insert_requires` and `reparent_children_requires`), so each is
//! proven equal to its spec function, and [`super::lemmas`] proves those keep
//! [`wf`]. Each reader's `ensures` says it returns the spec reader of the
//! same name.
//!
//! Performance (a hostile page may build millions of nodes): a node's
//! children are edited in place (the node is swapped out of the arena with
//! `set_and_swap`, edited and put back), never cloned; `reparent_children`
//! moves the whole list once and then sets each moved child's parent, so it
//! is linear in the number of moved children; nothing recurses, and
//! [`Arena::is_inclusive_ancestor`] walks parents in a loop.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::deep_clone_lemmas::*;
#[cfg(verus_only)]
use super::deep_clone_size_lemmas::*;
#[cfg(verus_only)]
use super::lemmas::*;
#[cfg(verus_only)]
use super::ops_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The node limit, [`max_nodes`].
pub const MAX_NODES: usize = 4_000_000;

/// An attribute ([`Attr`]); strings are code points.
pub struct ExecAttr {
    /// "namespace"
    pub namespace: Option<Namespace>,
    /// "namespace prefix"
    pub prefix: Option<Vec<u32>>,
    /// "local name"
    pub local_name: Vec<u32>,
    /// "value"
    pub value: Vec<u32>,
}

/// The view of an optional string.
pub open spec fn opt_str_view(s: Option<Vec<u32>>) -> Option<Seq<u32>> {
    match s {
        Some(v) => Some(v@),
        None => None,
    }
}

impl View for ExecAttr {
    type V = Attr;

    open spec fn view(&self) -> Attr {
        Attr { namespace: self.namespace, prefix: opt_str_view(self.prefix), local_name: self.local_name@, value: self.value@ }
    }
}

/// The view of an attribute list.
pub open spec fn attrs_view(v: Seq<ExecAttr>) -> Seq<Attr> {
    v.map_values(|a: ExecAttr| a@)
}

/// What a node is ([`NodeKind`]).
pub enum ExecKind {
    /// [`NodeKind::Document`]
    Document {
        /// "mode"
        mode: DocumentMode,
        /// "URL"
        url: Vec<u32>,
        /// the document base URL
        base_url: Vec<u32>,
    },
    /// [`NodeKind::DocumentType`]
    DocumentType {
        /// "name"
        name: Vec<u32>,
        /// "public ID"
        public_id: Vec<u32>,
        /// "system ID"
        system_id: Vec<u32>,
    },
    /// [`NodeKind::Element`]
    Element {
        /// "namespace"
        namespace: Option<Namespace>,
        /// "namespace prefix"
        prefix: Option<Vec<u32>>,
        /// "local name"
        local_name: Vec<u32>,
        /// "attribute list"
        attributes: Vec<ExecAttr>,
        /// "template contents"
        template_contents: Option<usize>,
        /// "form owner"
        form_owner: Option<usize>,
    },
    /// [`NodeKind::Text`]
    Text {
        /// "data"
        data: Vec<u32>,
    },
    /// [`NodeKind::Comment`]
    Comment {
        /// "data"
        data: Vec<u32>,
    },
    /// [`NodeKind::ProcessingInstruction`]
    ProcessingInstruction {
        /// "target"
        target: Vec<u32>,
        /// "data"
        data: Vec<u32>,
    },
    /// [`NodeKind::DocumentFragment`]
    DocumentFragment {
        /// "host"
        host: Option<usize>,
    },
}

impl View for ExecKind {
    type V = NodeKind;

    open spec fn view(&self) -> NodeKind {
        match self {
            ExecKind::Document { mode, url, base_url } => NodeKind::Document { mode: *mode, url: url@, base_url: base_url@ },
            ExecKind::DocumentType { name, public_id, system_id } => NodeKind::DocumentType {
                name: name@,
                public_id: public_id@,
                system_id: system_id@,
            },
            ExecKind::Element { namespace, prefix, local_name, attributes, template_contents, form_owner } => NodeKind::Element {
                namespace: *namespace,
                prefix: opt_str_view(*prefix),
                local_name: local_name@,
                attributes: attrs_view(attributes@),
                template_contents: *template_contents,
                form_owner: *form_owner,
            },
            ExecKind::Text { data } => NodeKind::Text { data: data@ },
            ExecKind::Comment { data } => NodeKind::Comment { data: data@ },
            ExecKind::ProcessingInstruction { target, data } => NodeKind::ProcessingInstruction { target: target@, data: data@ },
            ExecKind::DocumentFragment { host } => NodeKind::DocumentFragment { host: *host },
        }
    }
}

/// A node of the arena ([`Node`]).
pub struct ExecNode {
    kind: ExecKind,
    parent: Option<usize>,
    children: Vec<usize>,
    wrapper: Option<usize>,
}

impl View for ExecNode {
    type V = Node;

    closed spec fn view(&self) -> Node {
        Node {
            kind: self.kind@,
            parent: self.parent,
            children: self.children@,
            wrapper: match self.wrapper {
                Some(w) => Some(w as nat),
                None => None,
            },
        }
    }
}

/// The view of the arena's records.
closed spec fn nodes_view(s: Seq<ExecNode>) -> Seq<Node> {
    s.map_values(|n: ExecNode| n@)
}

/// The arena: the document's nodes, by id.
pub struct Arena {
    nodes: Vec<ExecNode>,
}

impl View for Arena {
    type V = Document;

    closed spec fn view(&self) -> Document {
        Document { nodes: nodes_view(self.nodes@) }
    }
}

/// Replacing one record replaces its view.
proof fn lemma_view_update(s: Seq<ExecNode>, i: int, x: ExecNode)
    requires
        0 <= i < s.len(),
    ensures
        nodes_view(s.update(i, x)) == nodes_view(s).update(i, x@),
{
    assert(nodes_view(s.update(i, x)) =~= nodes_view(s).update(i, x@));
}

/// Pushing a record pushes its view.
proof fn lemma_view_push(s: Seq<ExecNode>, x: ExecNode)
    ensures
        nodes_view(s.push(x)) == nodes_view(s).push(x@),
{
    assert(nodes_view(s.push(x)) =~= nodes_view(s).push(x@));
}

/// A record with nothing in it, to swap a node out of the arena (no
/// allocation).
fn placeholder() -> ExecNode {
    ExecNode { kind: ExecKind::DocumentFragment { host: None }, parent: None, children: Vec::new(), wrapper: None }
}

/// The index of the first `x` in `s` ([`index_of`]), or `None` (-1).
pub fn find(s: &[usize], x: usize) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < s@.len() && i as int == index_of(s@, x),
            None => index_of(s@, x) == -1,
        },
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != x,
        decreases s.len() - i,
    {
        match s.get(i) {
            Some(v) if *v == x => {
                proof {
                    lemma_index_of(s@, x);
                    assert(s@.contains(x));
                }
                return Some(i);
            },
            _ => {},
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_index_of(s@, x);
    }
    None
}

impl Arena {
    /// The number of nodes.
    pub fn len(&self) -> (r: usize)
        ensures
            r == self@.nodes.len(),
    {
        self.nodes.len()
    }

    /// The arena is never empty (it has the document node); for clippy's
    /// `len_without_is_empty`.
    pub fn is_empty(&self) -> (r: bool)
        ensures
            r == (self@.nodes.len() == 0),
    {
        self.nodes.len() == 0
    }

    /// The record of node `n`.
    fn node(&self, n: usize) -> (r: &ExecNode)
        requires
            n < self@.nodes.len(),
        ensures
            r@ == self@.nodes[n as int],
    {
        match self.nodes.get(n) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        }
    }

    /// Replace node `n`'s record by `f(record)`, without copying it: the
    /// record is swapped out, and the caller puts the new one back with
    /// [`Self::put`].
    fn take(&mut self, n: usize) -> (r: ExecNode)
        requires
            n < old(self)@.nodes.len(),
        ensures
            r@ == old(self)@.nodes[n as int],
            final(self).nodes@.len() == old(self).nodes@.len(),
            forall|i: int| 0 <= i < old(self).nodes@.len() && i != n ==> #[trigger] final(self).nodes@[i] == old(self).nodes@[i],
    {
        let mut tmp = placeholder();
        self.nodes.set_and_swap(n, &mut tmp);
        tmp
    }

    /// Put a record taken with [`Self::take`] back: the arena is `s0`, the
    /// one before the `take`, with node `n` replaced by `x`.
    fn put(&mut self, n: usize, x: ExecNode, Ghost(s0): Ghost<Seq<ExecNode>>)
        requires
            n < old(self).nodes@.len(),
            old(self).nodes@.len() == s0.len(),
            forall|i: int| 0 <= i < s0.len() && i != n ==> #[trigger] old(self).nodes@[i] == s0[i],
        ensures
            final(self).nodes@ == s0.update(n as int, x),
    {
        self.nodes.set(n, x);
        assert(self.nodes@ =~= s0.update(n as int, x));
    }

    /// Node `n`'s parent becomes `p`.
    fn set_parent(&mut self, n: usize, p: Option<usize>)
        requires
            n < old(self)@.nodes.len(),
        ensures
            final(self)@.nodes == old(self)@.nodes.update(n as int, Node { parent: p, ..old(self)@.nodes[n as int] }),
    {
        let ghost s0 = self.nodes@;
        let mut x = self.take(n);
        x.parent = p;
        self.put(n, x, Ghost(s0));
        proof {
            lemma_view_update(s0, n as int, x);
            assert(self.nodes@ == s0.update(n as int, x));
        }
    }

    /// Node `n`'s children become `k(children)`, edited in place.
    fn take_children(&mut self, n: usize) -> (r: Vec<usize>)
        requires
            n < old(self)@.nodes.len(),
        ensures
            r@ == old(self)@.nodes[n as int].children,
            final(self)@.nodes == old(self)@.nodes.update(n as int, Node { children: seq![], ..old(self)@.nodes[n as int] }),
    {
        let ghost s0 = self.nodes@;
        let mut x = self.take(n);
        let mut kids = Vec::new();
        core::mem::swap(&mut x.children, &mut kids);
        self.put(n, x, Ghost(s0));
        proof {
            lemma_view_update(s0, n as int, x);
            assert(x@.children =~= Seq::<NodeId>::empty());
            assert(x@ == Node { children: seq![], ..old(self)@.nodes[n as int] });
        }
        kids
    }

    /// Node `n`'s children are replaced by `kids` (the old list is dropped).
    fn set_children(&mut self, n: usize, kids: Vec<usize>)
        requires
            n < old(self)@.nodes.len(),
        ensures
            final(self)@.nodes == old(self)@.nodes.update(n as int, Node { children: kids@, ..old(self)@.nodes[n as int] }),
    {
        let ghost s0 = self.nodes@;
        let mut x = self.take(n);
        x.children = kids;
        self.put(n, x, Ghost(s0));
        proof {
            lemma_view_update(s0, n as int, x);
        }
    }

    // -----------------------------------------------------------------
    // Creating nodes

    /// A new document ([`new_ensures`]).
    pub fn new(url: Vec<u32>) -> (r: Arena)
        ensures
            new_ensures(url@, r@),
    {
        let base_url = vstd::slice::slice_to_vec(url.as_slice());
        let ghost u = url@;
        let doc = ExecNode {
            kind: ExecKind::Document { mode: DocumentMode::NoQuirks, url, base_url },
            parent: None,
            children: Vec::new(),
            wrapper: None,
        };
        let nodes = vec![doc];
        proof {
            assert(doc@.children =~= Seq::<NodeId>::empty());
            assert(nodes_view(nodes@) =~= new_document(u).nodes);
        }
        Arena { nodes }
    }

    /// Create a node of kind `kind`, refused at the node limit
    /// ([`create_ensures`]).
    pub fn create(&mut self, kind: ExecKind) -> (r: Option<usize>)
        requires
            create_requires(old(self)@, kind@),
        ensures
            create_ensures(old(self)@, kind@, final(self)@, r),
    {
        if self.nodes.len() >= MAX_NODES {
            return None;
        }
        let id = self.nodes.len();
        let x = ExecNode { kind, parent: None, children: Vec::new(), wrapper: None };
        let ghost s0 = self.nodes@;
        self.nodes.push(x);
        proof {
            lemma_view_push(s0, x);
            assert(x@.children =~= Seq::<NodeId>::empty());
            assert(self@.nodes == create_node(old(self)@, kind@).0.nodes);
        }
        Some(id)
    }

    /// Create the template contents of element `t`, refused at the node
    /// limit ([`create_template_contents_ensures`]).
    pub fn create_template_contents(&mut self, t: usize) -> (r: Option<usize>)
        requires
            create_template_contents_requires(old(self)@, t),
        ensures
            create_template_contents_ensures(old(self)@, t, final(self)@, r),
    {
        if self.nodes.len() >= MAX_NODES {
            return None;
        }
        let ghost d0 = self@;
        let id = self.nodes.len();
        // 2.
        let f = ExecNode { kind: ExecKind::DocumentFragment { host: Some(t) }, parent: None, children: Vec::new(), wrapper: None };
        let ghost s0 = self.nodes@;
        self.nodes.push(f);
        proof {
            lemma_view_push(s0, f);
            assert(f@.children =~= Seq::<NodeId>::empty());
            assert(self@ == create_node(d0, NodeKind::DocumentFragment { host: Some(t) }).0);
        }
        // 3.
        let ghost d1 = self@;
        let ghost s1 = self.nodes@;
        let mut y = self.take(t);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Element { namespace, prefix, local_name, attributes, form_owner, .. } => ExecKind::Element {
                namespace,
                prefix,
                local_name,
                attributes,
                template_contents: Some(id),
                form_owner,
            },
            other => other,
        };
        self.put(t, y, Ghost(s1));
        proof {
            lemma_view_update(s1, t as int, y);
            assert(self.nodes@ == s1.update(t as int, y));
            assert(y@ == Node { kind: create_template_contents(d0, t).0.nodes[t as int].kind, ..d1.nodes[t as int] });
            assert(self@.nodes =~= create_template_contents(d0, t).0.nodes);
        }
        Some(id)
    }

    // -----------------------------------------------------------------
    // Mutation algorithms

    /// DOM §4.2.3 "remove" ([`remove_ensures`]).
    pub fn remove(&mut self, node: usize)
        requires
            remove_requires(old(self)@, node),
        ensures
            remove_ensures(old(self)@, node, final(self)@),
    {
        let ghost d0 = self@;
        let ghost paths = lemma_wf_witness(d0);
        proof {
            lemma_remove_nodes(d0, paths, node);
        }
        // 1.
        let p = match self.node(node).parent {
            Some(p) => p,
            None => return ,
        };
        // 7.
        let i = match find(self.node(p).children.as_slice(), node) {
            Some(i) => i,
            None => return ,
        };
        let mut kids = self.take_children(p);
        let _removed = kids.remove(i);
        self.set_children(p, kids);
        self.set_parent(node, None);
        proof {
            assert(self@.nodes =~= remove(d0, node).nodes);
        }
    }

    /// DOM §4.5 "adopt" (step 7.1 of "insert" calls it): remove `node` from
    /// its parent, if any ([`adopt_ensures`]).
    pub fn adopt(&mut self, node: usize)
        requires
            adopt_requires(old(self)@, node),
        ensures
            adopt_ensures(old(self)@, node, final(self)@),
    {
        if self.node(node).parent.is_some() {
            self.remove(node);
        }
    }

    /// DOM §4.2.3 "append" ([`append_ensures`]).
    pub fn append(&mut self, parent: usize, node: usize)
        requires
            insert_requires(old(self)@, node, parent, None),
        ensures
            append_ensures(old(self)@, parent, node, final(self)@),
    {
        let ghost d0 = self@;
        let ghost paths = lemma_wf_witness(d0);
        // 7.1
        self.adopt(node);
        proof {
            lemma_insert_attach_requires(d0, paths, node, parent, None);
            lemma_insert_is_attach(d0, node, parent, None);
        }
        let ghost d1 = self@;
        // 7.2
        let mut kids = self.take_children(parent);
        kids.push(node);
        self.set_children(parent, kids);
        self.set_parent(node, Some(parent));
        proof {
            lemma_attach_nodes(
                d1,
                if d0.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths },
                node,
                parent,
                insert_kids(d0, node, parent, None),
            );
            assert(self@.nodes =~= append(d0, parent, node).nodes);
        }
    }

    /// DOM §4.2.3 "pre-insert" before `child` ([`insert_before_ensures`]).
    pub fn insert_before(&mut self, parent: usize, node: usize, child: usize)
        requires
            insert_requires(old(self)@, node, parent, Some(child)),
        ensures
            insert_before_ensures(old(self)@, parent, node, child, final(self)@),
    {
        let ghost d0 = self@;
        let ghost paths = lemma_wf_witness(d0);
        // 7.1
        self.adopt(node);
        let ghost p1 = if d0.nodes[node as int].parent is Some { remove_paths(paths, node) } else { paths };
        proof {
            lemma_insert_attach_requires(d0, paths, node, parent, Some(child));
            lemma_insert_is_attach(d0, node, parent, Some(child));
            lemma_adopt(d0, paths, node, parent, Some(child));
            lemma_listed(self@, p1, node, parent, Some(child));
            lemma_index_of(self@.nodes[parent as int].children, child);
        }
        let ghost d1 = self@;
        // 7.3
        let i = match find(self.node(parent).children.as_slice(), child) {
            Some(i) => i,
            None => return ,
        };
        let mut kids = self.take_children(parent);
        kids.insert(i, node);
        self.set_children(parent, kids);
        self.set_parent(node, Some(parent));
        proof {
            lemma_attach_nodes(d1, p1, node, parent, insert_kids(d0, node, parent, Some(child)));
            assert(self@.nodes =~= insert_before(d0, parent, node, child).nodes);
        }
    }

    /// HTML §13.2.6.4.7 step 4.17: move all of `from`'s children, in order,
    /// to the end of `to`'s ([`reparent_children_ensures`]). Linear in the
    /// number of moved children.
    pub fn reparent_children(&mut self, from: usize, to: usize)
        requires
            reparent_children_requires(old(self)@, from, to),
        ensures
            reparent_children_ensures(old(self)@, from, to, final(self)@),
    {
        let ghost d0 = self@;
        let ghost f = d0.nodes[from as int].children;
        let ghost len = f.len();
        proof {
            lemma_reparent_exec_pre(d0, from, to);
        }
        let mut moved = self.take_children(from);
        proof {
            lemma_exec_state_zero(d0, from, to);
            assert(self@ == reparent_exec_state(d0, from, to, 0));
        }
        let mut i: usize = 0;
        while i < moved.len()
            invariant
                d0.nodes.len() <= max_nodes(),
                valid(d0, from),
                valid(d0, to),
                from != to,
                f == d0.nodes[from as int].children,
                f.no_duplicates(),
                !f.contains(from),
                !f.contains(to),
                forall|j: int| 0 <= j < f.len() ==> (#[trigger] f[j]) < d0.nodes.len(),
                moved@ == f,
                i <= moved.len(),
                self@ == reparent_exec_state(d0, from, to, i as int),
            decreases moved.len() - i,
        {
            if let Some(c) = moved.get(i) {
                proof {
                    lemma_exec_state_step(d0, from, to, i as int);
                }
                self.set_parent(*c, Some(to));
                proof {
                    assert(self@.nodes =~= reparent_exec_state(d0, from, to, i as int + 1).nodes);
                }
            }
            // Never saturates: i < moved.len().
            i = i.saturating_add(1);
        }
        let ghost s1 = self@.nodes;
        let mut kids = self.take_children(to);
        kids.append(&mut moved);
        self.set_children(to, kids);
        proof {
            assert(self@.nodes == s1.update(to as int, Node { children: s1[to as int].children + f, ..s1[to as int] }));
            lemma_reparent_exec_post(d0, from, to);
        }
    }

    // -----------------------------------------------------------------
    // Data and attributes

    /// DOM §4.10 "replace data" at the end of a `Text` node
    /// ([`append_data_ensures`]).
    pub fn append_data(&mut self, n: usize, data: &[u32])
        requires
            append_data_requires(old(self)@, n),
        ensures
            append_data_ensures(old(self)@, n, data@, final(self)@),
    {
        let ghost s0 = self.nodes@;
        let mut y = self.take(n);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Text { data: mut d } => {
                extend(&mut d, data);
                ExecKind::Text { data: d }
            },
            other => other,
        };
        self.put(n, y, Ghost(s0));
        proof {
            lemma_view_update(s0, n as int, y);
            assert(self@.nodes =~= append_data(old(self)@, n, data@).nodes);
        }
    }

    /// DOM §4.9 "append an attribute" ([`append_attribute_ensures`]).
    pub fn append_attribute(&mut self, e: usize, attr: ExecAttr)
        requires
            append_attribute_requires(old(self)@, e),
        ensures
            append_attribute_ensures(old(self)@, e, attr@, final(self)@),
    {
        let ghost s0 = self.nodes@;
        let ghost a = attr@;
        let mut y = self.take(e);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Element { namespace, prefix, local_name, mut attributes, template_contents, form_owner } => {
                let ghost before = attributes@;
                attributes.push(attr);
                proof {
                    assert(attrs_view(attributes@) =~= attrs_view(before).push(a));
                }
                ExecKind::Element { namespace, prefix, local_name, attributes, template_contents, form_owner }
            },
            other => other,
        };
        self.put(e, y, Ghost(s0));
        proof {
            lemma_view_update(s0, e as int, y);
            assert(self@.nodes =~= append_attribute(old(self)@, e, a).nodes);
        }
    }

    /// Set the document's mode ([`set_mode_ensures`]).
    pub fn set_mode(&mut self, mode: DocumentMode)
        requires
            wf(old(self)@),
        ensures
            set_mode_ensures(old(self)@, mode, final(self)@),
    {
        let ghost s0 = self.nodes@;
        let ghost m = mode;
        let mut y = self.take(0);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Document { url, base_url, .. } => ExecKind::Document { mode, url, base_url },
            other => other,
        };
        self.put(0, y, Ghost(s0));
        proof {
            lemma_view_update(s0, 0, y);
            assert(self@.nodes =~= set_mode(old(self)@, m).nodes);
        }
    }

    // -----------------------------------------------------------------
    // Readers

    /// What node `n` is.
    pub fn kind(&self, n: usize) -> (r: &ExecKind)
        requires
            valid(self@, n),
        ensures
            r@ == self@.nodes[n as int].kind,
    {
        &self.node(n).kind
    }

    /// DOM §4.2 "parent".
    pub fn parent(&self, n: usize) -> (r: Option<usize>)
        requires
            valid(self@, n),
        ensures
            r == parent(self@, n),
    {
        self.node(n).parent
    }

    /// DOM §4.2 "children".
    pub fn children(&self, n: usize) -> (r: &[usize])
        requires
            valid(self@, n),
        ensures
            r@ == children(self@, n),
    {
        self.node(n).children.as_slice()
    }

    /// The wrapper slot of node `n` (always none in Phase 4).
    pub fn wrapper(&self, n: usize) -> (r: Option<usize>)
        requires
            valid(self@, n),
        ensures
            self@.nodes[n as int].wrapper == match r {
                Some(w) => Some(w as nat),
                None => None,
            },
    {
        self.node(n).wrapper
    }

    /// DOM §4.2 "last child".
    pub fn last_child(&self, n: usize) -> (r: Option<usize>)
        requires
            valid(self@, n),
        ensures
            r == last_child(self@, n),
    {
        self.node(n).children.last().cloned()
    }

    /// HTML §13.2.6 "has a child".
    pub fn has_child(&self, n: usize) -> (r: bool)
        requires
            valid(self@, n),
        ensures
            r == has_child(self@, n),
    {
        !self.node(n).children.is_empty()
    }

    /// DOM §4.2 "previous sibling".
    pub fn previous_sibling(&self, n: usize) -> (r: Option<usize>)
        requires
            wf(self@),
            valid(self@, n),
        ensures
            r == previous_sibling(self@, n),
    {
        let ghost paths = lemma_wf_witness(self@);
        proof {
            lemma_wf_split(self@, paths);
        }
        let p = self.node(n).parent?;
        let kids = self.node(p).children.as_slice();
        match find(kids, n) {
            Some(i) => match i.checked_sub(1) {
                Some(j) => kids.get(j).cloned(),
                None => None,
            },
            None => None,
        }
    }

    /// DOM §4.2 "inclusive ancestor": `a` is `x` or one of its ancestors.
    /// Walks parents from `x`, at most `len` steps.
    pub fn is_inclusive_ancestor(&self, a: usize, x: usize) -> (r: bool)
        requires
            wf(self@),
            valid(self@, x),
        ensures
            r == is_inclusive_ancestor(self@, a, x),
    {
        let ghost paths = lemma_wf_witness(self@);
        proof {
            lemma_wf_split(self@, paths);
        }
        let fuel = self.nodes.len();
        let mut cur = x;
        let mut steps: usize = 0;
        while steps <= fuel
            invariant
                wf_with(self@, paths),
                fuel == self@.nodes.len(),
                valid(self@, cur),
                steps <= fuel,
                inclusive_ancestor_within(self@, a, x, fuel as nat) == inclusive_ancestor_within(
                    self@,
                    a,
                    cur,
                    (fuel - steps) as nat,
                ),
            decreases fuel - steps,
        {
            if cur == a {
                return true;
            }
            if steps == fuel {
                return false;
            }
            match self.node(cur).parent {
                None => return false,
                Some(p) => {
                    proof {
                        assert(self@.nodes[cur as int].parent is Some);
                    }
                    cur = p;
                },
            }
            // Never saturates: steps < fuel.
            steps = steps.saturating_add(1);
        }
        false
    }
}

/// Append `s` to `out`.
fn extend(out: &mut Vec<u32>, s: &[u32])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost start = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == start + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c);
        }
        assert(s@.subrange(0, i as int).push(s@[i as int]) =~= s@.subrange(0, i as int + 1));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
}

// ---------------------------------------------------------------------
// reparent_children's loop

/// The arena inside [`Arena::reparent_children`]'s loop: `from` has no
/// children and the first `j` of its old children have `to` as their
/// parent; `to`'s children are not moved yet.
pub open spec fn reparent_exec_state(d0: Document, from: NodeId, to: NodeId, j: int) -> Document {
    let f = d0.nodes[from as int].children;
    Document {
        nodes: Seq::new(
            d0.nodes.len(),
            |i: int|
                if i == from {
                    Node { children: seq![], ..d0.nodes[i] }
                } else if f.subrange(0, j).contains(i as NodeId) {
                    Node { parent: Some(to), ..d0.nodes[i] }
                } else {
                    d0.nodes[i]
                },
        ),
    }
}

/// What the loop's invariant needs of the arena before it.
proof fn lemma_reparent_exec_pre(d0: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(d0, from, to),
    ensures
        d0.nodes.len() <= max_nodes(),
        d0.nodes[from as int].children.no_duplicates(),
        !d0.nodes[from as int].children.contains(from),
        !d0.nodes[from as int].children.contains(to),
        forall|j: int| 0 <= j < d0.nodes[from as int].children.len() ==> (#[trigger] d0.nodes[from as int].children[j]) < d0.nodes.len(),
{
    lemma_reparent_facts(d0, from, to);
    let paths = lemma_wf_witness(d0);
}

/// After the loop and the move, the arena is [`reparent_children`]'s.
proof fn lemma_reparent_exec_post(d0: Document, from: NodeId, to: NodeId)
    requires
        reparent_children_requires(d0, from, to),
    ensures
        ({
            let f = d0.nodes[from as int].children;
            let s = reparent_exec_state(d0, from, to, f.len() as int);
            Document { nodes: s.nodes.update(to as int, Node { children: s.nodes[to as int].children + f, ..s.nodes[to as int] }) }
                == reparent_children(d0, from, to)
        }),
{
    lemma_reparent_facts(d0, from, to);
    lemma_exec_state_done(d0, from, to);
    lemma_reparent_n(d0, from, to, d0.nodes[from as int].children.len());
}

/// Before the loop.
proof fn lemma_exec_state_zero(d0: Document, from: NodeId, to: NodeId)
    requires
        valid(d0, from),
    ensures
        d0.nodes.update(from as int, Node { children: seq![], ..d0.nodes[from as int] }) == reparent_exec_state(d0, from, to, 0).nodes,
{
    let f = d0.nodes[from as int].children;
    assert forall|i: int| 0 <= i < d0.nodes.len() implies !f.subrange(0, 0).contains(#[trigger] (i as NodeId)) by {
        if f.subrange(0, 0).contains(i as NodeId) {
            let k = choose|k: int| 0 <= k < 0 && f.subrange(0, 0)[k] == i as NodeId;
        }
    }
    assert(d0.nodes.update(from as int, Node { children: seq![], ..d0.nodes[from as int] }) =~= reparent_exec_state(d0, from, to, 0).nodes);
}

/// One iteration of the loop sets the parent of the `j`th child.
proof fn lemma_exec_state_step(d0: Document, from: NodeId, to: NodeId, j: int)
    requires
        d0.nodes.len() <= max_nodes(),
        valid(d0, from),
        d0.nodes[from as int].children.no_duplicates(),
        !d0.nodes[from as int].children.contains(from),
        forall|k: int| 0 <= k < d0.nodes[from as int].children.len() ==> (#[trigger] d0.nodes[from as int].children[k]) < d0.nodes.len(),
        0 <= j < d0.nodes[from as int].children.len(),
    ensures
        ({
            let c = d0.nodes[from as int].children[j];
            let s = reparent_exec_state(d0, from, to, j);
            &&& c < s.nodes.len()
            &&& s.nodes.update(c as int, Node { parent: Some(to), ..s.nodes[c as int] }) == reparent_exec_state(d0, from, to, j + 1).nodes
        }),
{
    let f = d0.nodes[from as int].children;
    let c = f[j];
    let s = reparent_exec_state(d0, from, to, j);
    let t = reparent_exec_state(d0, from, to, j + 1);
    assert(c < d0.nodes.len());
    if f.subrange(0, j).contains(c) {
        let k = choose|k: int| 0 <= k < j && f.subrange(0, j)[k] == c;
        assert(f[k] == c);
    }
    assert(f.contains(c));
    assert(c != from);
    let u = s.nodes.update(c as int, Node { parent: Some(to), ..s.nodes[c as int] });
    assert forall|i: int| 0 <= i < d0.nodes.len() implies #[trigger] u[i] == t.nodes[i] by {
        let x = i as NodeId;
        let fj1 = f.subrange(0, j + 1);
        if fj1.contains(x) {
            let k = choose|k: int| 0 <= k < fj1.len() && #[trigger] fj1[k] == x;
            if k < j {
                assert(f.subrange(0, j)[k] == x);
            } else {
                assert(x == c);
            }
        }
        if f.subrange(0, j).contains(x) {
            let k = choose|k: int| 0 <= k < j && f.subrange(0, j)[k] == x;
            assert(f.subrange(0, j + 1)[k] == x);
        }
        if i == c {
            assert(f.subrange(0, j + 1)[j] == x);
        }
    }
    assert(u =~= t.nodes);
}

/// After the loop, moving the list to `to` gives [`reparent_partial`] with
/// everything moved.
proof fn lemma_exec_state_done(d0: Document, from: NodeId, to: NodeId)
    requires
        valid(d0, from),
        valid(d0, to),
        from != to,
        !d0.nodes[from as int].children.contains(to),
    ensures
        ({
            let f = d0.nodes[from as int].children;
            let s = reparent_exec_state(d0, from, to, f.len() as int);
            s.nodes.update(to as int, Node { children: s.nodes[to as int].children + f, ..s.nodes[to as int] })
                == reparent_partial(d0, from, to, f.len() as int, f.len() as int).nodes
        }),
{
    let f = d0.nodes[from as int].children;
    let len = f.len() as int;
    let s = reparent_exec_state(d0, from, to, len);
    let r = reparent_partial(d0, from, to, len, len);
    assert(f.subrange(0, len) =~= f);
    assert(f.subrange(len, len) =~= Seq::<NodeId>::empty());
    assert(s.nodes[to as int] == d0.nodes[to as int]);
    assert(s.nodes.update(to as int, Node { children: s.nodes[to as int].children + f, ..s.nodes[to as int] }) =~= r.nodes);
}

// ---------------------------------------------------------------------
// Phase 7 item 7.13: the operations scripts call (see `spec.rs`)

/// The records after setting the parent of each of `ids` to `p`.
pub open spec fn set_parents_spec(s: Seq<Node>, ids: Seq<NodeId>, p: Option<NodeId>) -> Seq<Node> {
    Seq::new(s.len(), |x: int| if ids.contains(x as NodeId) { Node { parent: p, ..s[x] } } else { s[x] })
}

/// One iteration of [`Arena::set_parents`]'s loop.
proof fn lemma_set_parents_step(s: Seq<Node>, ids: Seq<NodeId>, p: Option<NodeId>, i: int)
    requires
        s.len() <= max_nodes(),
        0 <= i < ids.len(),
        ids[i] < s.len(),
    ensures
        ({
            let c = ids[i];
            let a = set_parents_spec(s, ids.subrange(0, i), p);
            a.update(c as int, Node { parent: p, ..a[c as int] }) == set_parents_spec(s, ids.subrange(0, i + 1), p)
        }),
{
    let c = ids[i];
    let a = set_parents_spec(s, ids.subrange(0, i), p);
    let b = set_parents_spec(s, ids.subrange(0, i + 1), p);
    let u = a.update(c as int, Node { parent: p, ..a[c as int] });
    assert(ids.subrange(0, i + 1)[i] == c);
    assert forall|x: int| 0 <= x < s.len() implies #[trigger] u[x] == b[x] by {
        let xn = x as NodeId;
        if x == c {
            assert(ids.subrange(0, i + 1).contains(c));
        } else {
            assert(xn != c);
            if ids.subrange(0, i + 1).contains(xn) {
                let j = choose|j: int| 0 <= j < i + 1 && #[trigger] ids.subrange(0, i + 1)[j] == xn;
                if j == i {
                    assert(ids.subrange(0, i + 1)[i] == c);
                }
                assert(j < i);
                assert(ids.subrange(0, i)[j] == xn);
            }
            if ids.subrange(0, i).contains(xn) {
                let j = choose|j: int| 0 <= j < i && #[trigger] ids.subrange(0, i)[j] == xn;
                assert(ids.subrange(0, i + 1)[j] == xn);
            }
        }
    }
    assert(u =~= b);
}

/// A node's children are nodes of the arena that have it as their parent,
/// without duplicates, and it is not one of them.
proof fn lemma_children_facts(doc: Document, p: NodeId)
    requires
        wf(doc),
        valid(doc, p),
    ensures
        doc.nodes[p as int].children.no_duplicates(),
        !doc.nodes[p as int].children.contains(p),
        forall|j: int|
            0 <= j < doc.nodes[p as int].children.len() ==> (#[trigger] doc.nodes[p as int].children[j]) < doc.nodes.len()
                && doc.nodes[doc.nodes[p as int].children[j] as int].parent == Some(p),
{
    let paths = lemma_wf_witness(doc);
    lemma_wf_split(doc, paths);
    let f = doc.nodes[p as int].children;
    assert forall|j: int| 0 <= j < f.len() implies (#[trigger] f[j]) < doc.nodes.len() && doc.nodes[f[j] as int].parent == Some(p) by {
        assert(doc.nodes[p as int].children[j] == f[j]);
    }
    if f.contains(p) {
        let j = choose|j: int| 0 <= j < f.len() && f[j] == p;
        assert(f[j] == p);
        lemma_parent_not_self(doc, paths, p);
    }
}

/// The arena after taking all of `p`'s children and setting their parents
/// to none is [`removed_prefix`] with everything removed.
proof fn lemma_remove_children_state(d0: Document, p: NodeId)
    requires
        wf(d0),
        valid(d0, p),
    ensures
        set_parents_spec(
            d0.nodes.update(p as int, Node { children: seq![], ..d0.nodes[p as int] }),
            d0.nodes[p as int].children,
            None,
        ) == removed_prefix(d0, p, d0.nodes[p as int].children.len() as int),
{
    lemma_children_facts(d0, p);
    let kids = d0.nodes[p as int].children;
    let len = kids.len();
    let s1 = d0.nodes.update(p as int, Node { children: seq![], ..d0.nodes[p as int] });
    let a = set_parents_spec(s1, kids, None);
    let r = removed_prefix(d0, p, len as int);
    assert(kids.subrange(0, len as int) =~= kids);
    assert(kids.subrange(len as int, len as int) =~= Seq::<NodeId>::empty());
    assert forall|x: int| 0 <= x < d0.nodes.len() implies #[trigger] a[x] == r[x] by {
        if x == p {
            assert(!kids.contains(p));
        }
    }
    assert(a =~= r);
}

/// An empty fragment inserts nothing: the arena is [`fragment_inserted`].
proof fn lemma_fragment_state_empty(d0: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>)
    requires
        insert_any_requires(d0, frag, parent, child),
        d0.nodes[frag as int].kind is DocumentFragment,
        d0.nodes[frag as int].children.len() == 0,
    ensures
        insert_fragment(d0, frag, parent, child) == d0,
{
    assert(d0.nodes[frag as int].children =~= Seq::<NodeId>::empty());
}

/// The arena after steps 4.1 and 7 done in bulk is [`fragment_inserted`].
proof fn lemma_fragment_state(d0: Document, frag: NodeId, parent: NodeId, child: Option<NodeId>, newkids: Seq<NodeId>)
    requires
        insert_any_requires(d0, frag, parent, child),
        d0.nodes[frag as int].kind is DocumentFragment,
        d0.nodes[frag as int].children.len() > 0,
        newkids == list_kids(d0.nodes[parent as int].children, d0.nodes[frag as int].children, child),
    ensures
        ({
            let nodes0 = d0.nodes[frag as int].children;
            let s1 = d0.nodes.update(frag as int, Node { children: seq![], ..d0.nodes[frag as int] });
            let s2 = set_parents_spec(s1, nodes0, Some(parent));
            s2.update(parent as int, Node { children: newkids, ..s2[parent as int] }) == fragment_inserted(d0, frag, parent, child)
        }),
{
    let paths = lemma_wf_witness(d0);
    lemma_wf_split(d0, paths);
    lemma_frag_facts(d0, paths, frag, parent, child);
    let nodes0 = d0.nodes[frag as int].children;
    let s1 = d0.nodes.update(frag as int, Node { children: seq![], ..d0.nodes[frag as int] });
    let s2 = set_parents_spec(s1, nodes0, Some(parent));
    let u = s2.update(parent as int, Node { children: newkids, ..s2[parent as int] });
    let b = fragment_inserted(d0, frag, parent, child);
    assert(d0.nodes.len() <= max_nodes());
    assert(parent != frag);
    assert(!nodes0.contains(parent));
    assert(!nodes0.contains(frag));
    assert forall|x: int| 0 <= x < d0.nodes.len() implies #[trigger] u[x] == b[x] by {
        if x == frag {
            assert(s2[x] == s1[x]);
        } else if x == parent {
            assert(s2[x] == s1[x]);
            assert(s1[x] == d0.nodes[x]);
        } else if nodes0.contains(x as NodeId) {
            assert(s1[x] == d0.nodes[x]);
        } else {
            assert(s1[x] == d0.nodes[x]);
        }
    }
    assert(u =~= b);
}

/// Whether a kind is an element, as a boolean.
fn kind_is(k: &ExecKind, t: &NodeTag) -> (r: bool)
    ensures
        r == has_tag(k@, *t),
{
    match t {
        NodeTag::Element => matches!(k, ExecKind::Element { .. }),
        NodeTag::Text => matches!(k, ExecKind::Text { .. }),
        NodeTag::DocumentType => matches!(k, ExecKind::DocumentType { .. }),
    }
}

/// A kind of a node that may have children.
fn kind_may_have_children(k: &ExecKind) -> (r: bool)
    ensures
        r == may_have_children(k@),
{
    matches!(k, ExecKind::Document { .. } | ExecKind::Element { .. } | ExecKind::DocumentFragment { .. })
}

impl Arena {
    /// Set the parent of each of `ids` to `p`, in one pass.
    fn set_parents(&mut self, ids: &[usize], p: Option<usize>)
        requires
            old(self)@.nodes.len() <= max_nodes(),
            forall|j: int| 0 <= j < ids@.len() ==> (#[trigger] ids@[j]) < old(self)@.nodes.len(),
        ensures
            final(self)@.nodes == set_parents_spec(old(self)@.nodes, ids@, p),
    {
        let ghost s0 = self@.nodes;
        proof {
            assert(ids@.subrange(0, 0) =~= Seq::<NodeId>::empty());
            assert(set_parents_spec(s0, ids@.subrange(0, 0), p) =~= s0) by {
                assert forall|x: int| 0 <= x < s0.len() implies #[trigger] set_parents_spec(s0, ids@.subrange(0, 0), p)[x] == s0[x] by {}
            }
        }
        let mut i: usize = 0;
        while i < ids.len()
            invariant
                i <= ids.len(),
                s0.len() <= max_nodes(),
                s0.len() == self@.nodes.len(),
                forall|j: int| 0 <= j < ids@.len() ==> (#[trigger] ids@[j]) < s0.len(),
                self@.nodes == set_parents_spec(s0, ids@.subrange(0, i as int), p),
            decreases ids.len() - i,
        {
            if let Some(c) = ids.get(i) {
                proof {
                    lemma_set_parents_step(s0, ids@, p, i as int);
                }
                self.set_parent(*c, p);
                proof {
                    assert(self@.nodes =~= set_parents_spec(s0, ids@.subrange(0, i as int + 1), p));
                }
            }
            // Never saturates: i < ids.len().
            i = i.saturating_add(1);
        }
        proof {
            assert(ids@.subrange(0, ids.len() as int) =~= ids@);
        }
    }

    /// DOM §4.2.3 "remove all of `p`'s children, in tree order", in one pass.
    fn remove_children(&mut self, p: usize)
        requires
            wf(old(self)@),
            valid(old(self)@, p),
        ensures
            final(self)@ == remove_children(old(self)@, p),
    {
        let ghost d0 = self@;
        let ghost kids0 = d0.nodes[p as int].children;
        proof {
            lemma_children_facts(d0, p);
            lemma_remove_children_n(d0, p, kids0.len());
            let paths = lemma_wf_witness(d0);
            lemma_wf_split(d0, paths);
        }
        let kids = self.take_children(p);
        self.set_parents(kids.as_slice(), None);
        proof {
            lemma_remove_children_state(d0, p);
            assert(children(d0, p) == kids0);
            assert(self@.nodes == removed_prefix(d0, p, kids0.len() as int));
            assert(self@ == remove_children(d0, p));
        }
    }

    /// DOM §4.2 "next sibling".
    pub fn next_sibling(&self, n: usize) -> (r: Option<usize>)
        requires
            wf(self@),
            valid(self@, n),
        ensures
            r == next_sibling(self@, n),
    {
        let ghost paths = lemma_wf_witness(self@);
        proof {
            lemma_wf_split(self@, paths);
        }
        let p = self.node(n).parent?;
        let kids = self.node(p).children.as_slice();
        match find(kids, n) {
            Some(i) => {
                // Never saturates: i < kids.len().
                let j = i.saturating_add(1);
                if j < kids.len() {
                    let x = kids.get(j)?;
                    Some(*x)
                } else {
                    None
                }
            },
            None => None,
        }
    }

    /// DOM §4.2 "host-including inclusive ancestor": `a` is `x` or one of
    /// its ancestors, or of its root's host's (and so on). Walks from `x`,
    /// at most `len` steps.
    #[verifier::rlimit(50)]
    pub fn is_host_including_inclusive_ancestor(&self, a: usize, x: usize) -> (r: bool)
        requires
            wf(self@),
            valid(self@, x),
        ensures
            r == is_host_including_inclusive_ancestor(self@, a, x),
    {
        let ghost paths = lemma_wf_witness(self@);
        proof {
            lemma_wf_split(self@, paths);
        }
        let fuel = self.nodes.len();
        let mut cur = x;
        let mut steps: usize = 0;
        while steps <= fuel
            invariant
                wf_with(self@, paths),
                fuel == self@.nodes.len(),
                valid(self@, cur),
                steps <= fuel,
                host_including_within(self@, a, x, fuel as nat) == host_including_within(self@, a, cur, (fuel - steps) as nat),
            decreases fuel - steps,
        {
            if cur == a {
                return true;
            }
            if steps == fuel {
                return false;
            }
            match self.node(cur).parent {
                Some(p) => {
                    cur = p;
                },
                None => match &self.node(cur).kind {
                    ExecKind::DocumentFragment { host: Some(h) } => {
                        proof {
                            assert(self@.nodes[cur as int].kind is DocumentFragment);
                        }
                        cur = *h;
                    },
                    _ => return false,
                },
            }
            // Never saturates: steps < fuel.
            steps = steps.saturating_add(1);
        }
        false
    }

    /// How many of `kids[lo..hi]` have the tag `t`, other than `skip`
    /// ([`count_tag`]).
    fn count_tag(&self, kids: &[usize], lo: usize, hi: usize, t: NodeTag, skip: Option<usize>) -> (r: usize)
        requires
            lo <= hi <= kids@.len(),
            forall|j: int| 0 <= j < kids@.len() ==> (#[trigger] kids@[j]) < self@.nodes.len(),
        ensures
            r as nat == count_tag(self@, kids@.subrange(lo as int, hi as int), t, skip),
    {
        let mut count: usize = 0;
        let mut i: usize = lo;
        proof {
            assert(kids@.subrange(lo as int, lo as int) =~= Seq::<NodeId>::empty());
        }
        while i < hi
            invariant
                lo <= i <= hi,
                hi <= kids@.len(),
                forall|j: int| 0 <= j < kids@.len() ==> (#[trigger] kids@[j]) < self@.nodes.len(),
                count <= i - lo,
                count as nat == count_tag(self@, kids@.subrange(lo as int, i as int), t, skip),
            decreases hi - i,
        {
            if let Some(c) = kids.get(i) {
                proof {
                    let sub = kids@.subrange(lo as int, i as int + 1);
                    assert(sub.drop_last() =~= kids@.subrange(lo as int, i as int));
                    assert(sub.last() == kids@[i as int]);
                }
                if kind_is(self.kind(*c), &t) && skip != Some(*c) {
                    // Never saturates: count <= i - lo < hi.
                    count = count.saturating_add(1);
                }
            }
            // Never saturates: i < hi.
            i = i.saturating_add(1);
        }
        count
    }
}

impl Arena {
    /// The statements of step 6 of "ensure pre-insertion validity" about a
    /// document `parent` ([`pre_insert_document_violation`]).
    fn pre_insert_document_violation(&self, node: usize, parent: usize, child: Option<usize>) -> (r: bool)
        requires
            wf(self@),
            valid(self@, node),
            valid(self@, parent),
            match child {
                None => true,
                Some(c) => valid(self@, c) && self@.nodes[c as int].parent == Some(parent),
            },
        ensures
            r == pre_insert_document_violation(self@, node, parent, child),
    {
        let ghost d = self@;
        proof {
            lemma_children_facts(d, parent);
            lemma_children_facts(d, node);
        }
        let kids = self.children(parent);
        let len = kids.len();
        let mut after: usize = 0;
        let mut before: usize = 0;
        let mut child_is_doctype = false;
        if let Some(c) = child {
            proof {
                let paths = lemma_wf_witness(d);
                lemma_wf_split(d, paths);
                assert(d.nodes[parent as int].children.contains(c));
                lemma_index_of(kids@, c);
            }
            let i = match find(kids, c) {
                Some(i) => i,
                None => {
                    proof {
                        assert(false);
                    }
                    return false;
                },
            };
            // Never overflows: i < len.
            let next = i.saturating_add(1);
            after = self.count_tag(kids, next, len, NodeTag::DocumentType, None);
            before = self.count_tag(kids, 0, i, NodeTag::Element, None);
            child_is_doctype = kind_is(self.kind(c), &NodeTag::DocumentType);
        }
        proof {
            assert(kids@.subrange(0, len as int) =~= kids@);
        }
        match self.kind(node) {
            ExecKind::DocumentFragment { .. } => {
                let nk = self.children(node);
                let nlen = nk.len();
                proof {
                    assert(nk@.subrange(0, nlen as int) =~= nk@);
                }
                let elements = self.count_tag(nk, 0, nlen, NodeTag::Element, None);
                let texts = self.count_tag(nk, 0, nlen, NodeTag::Text, None);
                if elements > 1 || texts > 0 {
                    return true;
                }
                if elements == 1 {
                    let pe = self.count_tag(kids, 0, len, NodeTag::Element, None);
                    return pe > 0 || child_is_doctype || after > 0;
                }
                false
            },
            ExecKind::Element { .. } => {
                let pe = self.count_tag(kids, 0, len, NodeTag::Element, None);
                pe > 0 || child_is_doctype || after > 0
            },
            ExecKind::DocumentType { .. } => {
                let pd = self.count_tag(kids, 0, len, NodeTag::DocumentType, None);
                if pd > 0 || before > 0 {
                    return true;
                }
                if child.is_none() {
                    let pe = self.count_tag(kids, 0, len, NodeTag::Element, None);
                    return pe > 0;
                }
                false
            },
            _ => false,
        }
    }

    /// DOM §4.2.3† "ensure pre-insertion validity"
    /// ([`ensure_pre_insertion_validity_ensures`]).
    pub fn ensure_pre_insertion_validity(&self, node: usize, parent: usize, child: Option<usize>) -> (r: Option<DomError>)
        requires
            pre_insert_requires(self@, node, parent, child),
        ensures
            ensure_pre_insertion_validity_ensures(self@, node, parent, child, r),
    {
        let ghost d = self@;
        let pk = self.kind(parent);
        // 1.
        if !kind_may_have_children(pk) {
            return Some(DomError::HierarchyRequest);
        }
        // 2.
        if self.is_host_including_inclusive_ancestor(node, parent) {
            return Some(DomError::HierarchyRequest);
        }
        // 3.
        let not_found = match child {
            Some(c) => self.node(c).parent != Some(parent),
            None => false,
        };
        if not_found {
            return Some(DomError::NotFound);
        }
        let nk = self.kind(node);
        // 4.
        if let ExecKind::Document { .. } = nk {
            return Some(DomError::HierarchyRequest);
        }
        // 5.
        let parent_is_document = matches!(pk, ExecKind::Document { .. });
        let node_is_text = kind_is(nk, &NodeTag::Text);
        let node_is_doctype = kind_is(nk, &NodeTag::DocumentType);
        if (node_is_text && parent_is_document) || (node_is_doctype && !parent_is_document) {
            return Some(DomError::HierarchyRequest);
        }
        // 6.
        if parent_is_document && self.pre_insert_document_violation(node, parent, child) {
            return Some(DomError::HierarchyRequest);
        }
        None
    }

    /// The statements of step 6 of "replace" about a document `parent`
    /// ([`replace_document_violation`]).
    fn replace_document_violation(&self, child: usize, node: usize, parent: usize) -> (r: bool)
        requires
            wf(self@),
            valid(self@, node),
            valid(self@, parent),
            valid(self@, child),
            self@.nodes[child as int].parent == Some(parent),
        ensures
            r == replace_document_violation(self@, child, node, parent),
    {
        let ghost d = self@;
        proof {
            lemma_children_facts(d, parent);
            lemma_children_facts(d, node);
            let paths = lemma_wf_witness(d);
            lemma_wf_split(d, paths);
            assert(d.nodes[parent as int].children.contains(child));
            lemma_index_of(d.nodes[parent as int].children, child);
        }
        let kids = self.children(parent);
        let len = kids.len();
        let i = match find(kids, child) {
            Some(i) => i,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        // Never overflows: i < len.
        let next = i.saturating_add(1);
        let after = self.count_tag(kids, next, len, NodeTag::DocumentType, None);
        let before = self.count_tag(kids, 0, i, NodeTag::Element, None);
        proof {
            assert(kids@.subrange(0, len as int) =~= kids@);
        }
        match self.kind(node) {
            ExecKind::DocumentFragment { .. } => {
                let nk = self.children(node);
                let nlen = nk.len();
                proof {
                    assert(nk@.subrange(0, nlen as int) =~= nk@);
                }
                let elements = self.count_tag(nk, 0, nlen, NodeTag::Element, None);
                let texts = self.count_tag(nk, 0, nlen, NodeTag::Text, None);
                if elements > 1 || texts > 0 {
                    return true;
                }
                if elements == 1 {
                    let pe = self.count_tag(kids, 0, len, NodeTag::Element, Some(child));
                    return pe > 0 || after > 0;
                }
                false
            },
            ExecKind::Element { .. } => {
                let pe = self.count_tag(kids, 0, len, NodeTag::Element, Some(child));
                pe > 0 || after > 0
            },
            ExecKind::DocumentType { .. } => {
                let pd = self.count_tag(kids, 0, len, NodeTag::DocumentType, Some(child));
                pd > 0 || before > 0
            },
            _ => false,
        }
    }

    /// Steps 1 to 6 of DOM §4.2.3† "replace" ([`replace_error`]).
    fn replace_validity(&self, child: usize, node: usize, parent: usize) -> (r: Option<DomError>)
        requires
            replace_requires(self@, child, node, parent),
        ensures
            r == replace_error(self@, child, node, parent),
    {
        let pk = self.kind(parent);
        // 1.
        if !kind_may_have_children(pk) {
            return Some(DomError::HierarchyRequest);
        }
        // 2.
        if self.is_host_including_inclusive_ancestor(node, parent) {
            return Some(DomError::HierarchyRequest);
        }
        // 3.
        if self.node(child).parent != Some(parent) {
            return Some(DomError::NotFound);
        }
        let nk = self.kind(node);
        // 4.
        if let ExecKind::Document { .. } = nk {
            return Some(DomError::HierarchyRequest);
        }
        // 5.
        let parent_is_document = matches!(pk, ExecKind::Document { .. });
        let node_is_text = kind_is(nk, &NodeTag::Text);
        let node_is_doctype = kind_is(nk, &NodeTag::DocumentType);
        if (node_is_text && parent_is_document) || (node_is_doctype && !parent_is_document) {
            return Some(DomError::HierarchyRequest);
        }
        // 6.
        if parent_is_document && self.replace_document_violation(child, node, parent) {
            return Some(DomError::HierarchyRequest);
        }
        None
    }

    /// DOM §4.2.3 "insert" a `DocumentFragment` ([`insert_fragment`]).
    /// Linear in the number of moved children.
    fn insert_fragment(&mut self, frag: usize, parent: usize, child: Option<usize>)
        requires
            insert_any_requires(old(self)@, frag, parent, child),
            old(self)@.nodes[frag as int].kind is DocumentFragment,
        ensures
            final(self)@ == insert_fragment(old(self)@, frag, parent, child),
    {
        let ghost d0 = self@;
        let ghost nodes0 = d0.nodes[frag as int].children;
        let ghost kids0 = d0.nodes[parent as int].children;
        proof {
            lemma_insert_fragment(d0, frag, parent, child);
            lemma_children_facts(d0, frag);
            let paths = lemma_wf_witness(d0);
            lemma_wf_split(d0, paths);
        }
        // 3.
        if self.node(frag).children.is_empty() {
            proof {
                lemma_fragment_state_empty(d0, frag, parent, child);
            }
            return ;
        }
        // 4.1 and 7., in bulk.
        let mut moved = self.take_children(frag);
        self.set_parents(moved.as_slice(), Some(parent));
        let mut kids = self.take_children(parent);
        match child {
            None => {
                kids.append(&mut moved);
            },
            Some(c) => {
                proof {
                    lemma_index_of(kids0, c);
                }
                let i = match find(kids.as_slice(), c) {
                    Some(i) => i,
                    None => {
                        proof {
                            assert(false);
                        }
                        return ;
                    },
                };
                let mut tail = kids.split_off(i);
                kids.append(&mut moved);
                kids.append(&mut tail);
            },
        }
        proof {
            match child {
                None => {
                    assert(kids@ == kids0 + nodes0);
                },
                Some(c) => {
                    let i = index_of(kids0, c);
                    assert(kids@ == kids0.subrange(0, i) + nodes0 + kids0.subrange(i, kids0.len() as int));
                },
            }
            assert(kids@ == list_kids(kids0, nodes0, child));
        }
        self.set_children(parent, kids);
        proof {
            lemma_fragment_state(d0, frag, parent, child, kids@);
            assert(self@.nodes == fragment_inserted(d0, frag, parent, child));
            assert(self@ == insert_fragment(d0, frag, parent, child));
        }
    }

    /// DOM §4.2.3 "insert" for any node ([`insert_any`]).
    fn insert_any(&mut self, node: usize, parent: usize, child: Option<usize>)
        requires
            insert_any_requires(old(self)@, node, parent, child),
        ensures
            final(self)@ == insert_any(old(self)@, node, parent, child),
    {
        let is_fragment = matches!(self.kind(node), ExecKind::DocumentFragment { .. });
        if is_fragment {
            self.insert_fragment(node, parent, child);
        } else {
            match child {
                None => self.append(parent, node),
                Some(c) => self.insert_before(parent, node, c),
            }
        }
    }

    /// DOM §4.2.3† "pre-insert" ([`pre_insert_ensures`]).
    pub fn pre_insert(&mut self, node: usize, parent: usize, child: Option<usize>) -> (err: Option<DomError>)
        requires
            pre_insert_requires(old(self)@, node, parent, child),
        ensures
            pre_insert_ensures(old(self)@, node, parent, child, final(self)@, err),
    {
        let ghost d0 = self@;
        // 1.
        let err = self.ensure_pre_insertion_validity(node, parent, child);
        if err.is_some() {
            return err;
        }
        proof {
            lemma_pre_insert_valid(d0, node, parent, child);
        }
        // 2. and 3.
        let reference_child = if child == Some(node) {
            self.next_sibling(node)
        } else {
            child
        };
        // 4.
        self.insert_any(node, parent, reference_child);
        None
    }

    /// DOM §4.2.3† "replace" ([`replace_ensures`]).
    pub fn replace(&mut self, child: usize, node: usize, parent: usize) -> (err: Option<DomError>)
        requires
            replace_requires(old(self)@, child, node, parent),
        ensures
            replace_ensures(old(self)@, child, node, parent, final(self)@, err),
    {
        let ghost d0 = self@;
        // 1. to 6.
        let err = self.replace_validity(child, node, parent);
        if err.is_some() {
            return err;
        }
        proof {
            lemma_replace_valid(d0, child, node, parent);
            assert(d0.nodes[child as int].parent == Some(parent));
        }
        // 7.
        let reference0 = self.next_sibling(child);
        // 8.
        let reference_child = if reference0 == Some(node) {
            self.next_sibling(node)
        } else {
            reference0
        };
        // 11.
        self.remove(child);
        // 13.
        self.insert_any(node, parent, reference_child);
        None
    }

    /// DOM §4.2.3† "replace all" ([`replace_all_ensures`]).
    pub fn replace_all(&mut self, node: Option<usize>, parent: usize)
        requires
            replace_all_requires(old(self)@, node, parent),
        ensures
            replace_all_ensures(old(self)@, node, parent, final(self)@),
    {
        let ghost d0 = self@;
        proof {
            lemma_replace_all_valid(d0, node, parent);
        }
        // 5.
        self.remove_children(parent);
        // 6.
        if let Some(n) = node {
            self.insert_any(n, parent, None);
        }
    }
}

// ---------------------------------------------------------------------
// Copies of kinds (for "clone a node")

/// A copy of a string.
fn copy_str(s: &Vec<u32>) -> (r: Vec<u32>)
    ensures
        r@ == s@,
{
    vstd::slice::slice_to_vec(s.as_slice())
}

/// A copy of an optional string.
fn copy_opt_str(s: &Option<Vec<u32>>) -> (r: Option<Vec<u32>>)
    ensures
        opt_str_view(r) == opt_str_view(*s),
{
    match s {
        None => None,
        Some(v) => {
            let c = copy_str(v);
            Some(c)
        },
    }
}

/// A copy of an optional namespace.
fn copy_ns(n: &Option<Namespace>) -> (r: Option<Namespace>)
    ensures
        r == *n,
{
    match n {
        None => None,
        Some(Namespace::Html) => Some(Namespace::Html),
        Some(Namespace::MathMl) => Some(Namespace::MathMl),
        Some(Namespace::Svg) => Some(Namespace::Svg),
        Some(Namespace::XLink) => Some(Namespace::XLink),
        Some(Namespace::Xml) => Some(Namespace::Xml),
        Some(Namespace::Xmlns) => Some(Namespace::Xmlns),
    }
}

/// A copy of a document mode.
fn copy_mode(m: &DocumentMode) -> (r: DocumentMode)
    ensures
        r == *m,
{
    match m {
        DocumentMode::NoQuirks => DocumentMode::NoQuirks,
        DocumentMode::Quirks => DocumentMode::Quirks,
        DocumentMode::LimitedQuirks => DocumentMode::LimitedQuirks,
    }
}

/// A copy of an attribute ("clone an attribute").
fn copy_attr(a: &ExecAttr) -> (r: ExecAttr)
    ensures
        r@ == a@,
{
    ExecAttr { namespace: copy_ns(&a.namespace), prefix: copy_opt_str(&a.prefix), local_name: copy_str(&a.local_name), value: copy_str(&a.value) }
}

/// A copy of an attribute list.
fn copy_attrs(v: &[ExecAttr]) -> (r: Vec<ExecAttr>)
    ensures
        attrs_view(r@) == attrs_view(v@),
{
    let mut out: Vec<ExecAttr> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j])@ == v@[j]@,
        decreases v.len() - i,
    {
        if let Some(a) = v.get(i) {
            out.push(copy_attr(a));
        }
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(attrs_view(out@) =~= attrs_view(v@));
    }
    out
}

/// The kind of the copy "clone a node" makes ([`clone_kind`]).
fn clone_kind_exec(k: &ExecKind) -> (r: ExecKind)
    ensures
        r@ == clone_kind(k@),
{
    match k {
        ExecKind::Document { mode, url, base_url } => ExecKind::Document { mode: copy_mode(mode), url: copy_str(url), base_url: copy_str(base_url) },
        ExecKind::DocumentType { name, public_id, system_id } => ExecKind::DocumentType {
            name: copy_str(name),
            public_id: copy_str(public_id),
            system_id: copy_str(system_id),
        },
        ExecKind::Element { namespace, prefix, local_name, attributes, .. } => ExecKind::Element {
            namespace: copy_ns(namespace),
            prefix: copy_opt_str(prefix),
            local_name: copy_str(local_name),
            attributes: copy_attrs(attributes),
            template_contents: None,
            form_owner: None,
        },
        ExecKind::Text { data } => ExecKind::Text { data: copy_str(data) },
        ExecKind::Comment { data } => ExecKind::Comment { data: copy_str(data) },
        ExecKind::ProcessingInstruction { target, data } => ExecKind::ProcessingInstruction { target: copy_str(target), data: copy_str(data) },
        ExecKind::DocumentFragment { .. } => ExecKind::DocumentFragment { host: None },
    }
}

/// A template element ([`is_template`]).
fn is_template_exec(k: &ExecKind) -> (r: bool)
    ensures
        r == is_template(k@),
{
    matches!(k, ExecKind::Element { template_contents: Some(_), .. })
}

/// A template's contents, if `k` is a template ([`is_template`]).
fn template_contents_exec(k: &ExecKind) -> (r: Option<usize>)
    ensures
        is_template(k@) ==> r == Some(k@->Element_template_contents->Some_0),
        !is_template(k@) ==> r is None,
{
    match k {
        ExecKind::Element { template_contents: Some(f), .. } => Some(*f),
        _ => None,
    }
}

impl Arena {
    /// Cut the arena back to its first `len` nodes (a clone that does not
    /// fit is rolled back with it).
    fn truncate(&mut self, len: usize)
        requires
            len <= old(self)@.nodes.len(),
        ensures
            final(self)@ == (Document { nodes: old(self)@.nodes.take(len as int) }),
    {
        let ghost s0 = self.nodes@;
        self.nodes.truncate(len);
        proof {
            assert(self.nodes@ =~= s0.take(len as int));
            assert(nodes_view(self.nodes@) =~= nodes_view(s0).take(len as int));
        }
    }

    /// One step of [`Arena::clone_deep`]: clone the `j`th child of
    /// `order[i]`, append the copy to node `base + i`, and list the source
    /// (and a template's contents). If the copy does not fit, the arena is
    /// cut back to its old length and the result is false.
    #[verifier::rlimit(100)]
    fn deep_step(&mut self, order: &mut Vec<usize>, base: usize, i: usize, j: usize, Ghost(d0): Ghost<Document>, Ghost(node): Ghost<NodeId>) -> (ok: bool)
        requires
            base == d0.nodes.len(),
            deep_inv(d0, node, old(self)@, old(order)@, i as int, j as int),
            i < old(order).len(),
            j < d0.nodes[old(order)@[i as int] as int].children.len(),
            host_acyclic(d0),
        ensures
            ok ==> deep_inv(d0, node, final(self)@, final(order)@, i as int, j as int + 1),
            ok ==> final(self)@.nodes.len() == base + final(order).len(),
            ok ==> forall|k: int| 0 <= k < old(order).len() ==> #[trigger] final(order)@[k] == old(order)@[k],
            !ok ==> final(self)@ == d0,
            !ok ==> !can_create(d0, subtree_size(d0, node)),
    {
        let ghost a = self@;
        let ghost order0 = order@;
        proof {
            lemma_inv_facts(d0, node, a, order0, i as int, j as int);
            assert(a.nodes[order0[i as int] as int] == d0.nodes[order0[i as int] as int]);
        }
        // In bounds by the precondition; `get` keeps the code free of panics.
        let s = match order.get(i) {
            Some(s) => *s,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        let ch = match self.children(s).get(j) {
            Some(c) => *c,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        proof {
            lemma_child_requires(d0, node, a, order0, i as int, j as int, ch);
        }
        match self.clone_node(ch) {
            None => {
                proof {
                    assert(!can_create(a, clone_count(a, ch)));
                    lemma_step_fits(d0, node, a, order0, i as int, j as int, ch);
                    assert(a.nodes[ch as int] == d0.nodes[ch as int]);
                    lemma_deep_rollback(d0, node, self@, order0, i as int, j as int);
                }
                self.truncate(base);
                false
            },
            Some(cc) => {
                proof {
                    assert(can_create(a, clone_count(a, ch)));
                    lemma_step_requires(d0, node, a, order0, i as int, j as int, ch);
                    lemma_step_inv(d0, node, a, order0, i as int, j as int, ch);
                }
                // base + i < self.len() <= MAX_NODES: never saturates.
                self.append(base.saturating_add(i), cc);
                proof {
                    assert(self@.nodes[ch as int] == a.nodes[ch as int]);
                }
                order.push(ch);
                if let Some(f) = template_contents_exec(self.kind(ch)) {
                    order.push(f);
                }
                proof {
                    assert(order@ =~= order_after(d0, order0, ch));
                }
                true
            },
        }
    }

    /// DOM §4.4† "clone a node" with the clone children flag set
    /// ([`clone_deep_ensures`]): a worklist over the source's host-including
    /// subtree. Node `base + i` is the copy of `order[i]`; the cursor `(i,
    /// j)` is at the `j`th child of `order[i]`, which is cloned (shallowly,
    /// with its template contents) and appended to node `base + i`, and
    /// listed. Nothing recurses. If a clone does not fit, the arena is cut
    /// back to its old length.
    #[verifier::rlimit(20)]
    pub fn clone_deep(&mut self, node: usize) -> (r: Option<usize>)
        requires
            clone_deep_requires(old(self)@, node),
        ensures
            clone_deep_ensures(old(self)@, node, final(self)@, r),
    {
        let ghost d0 = self@;
        let base = self.nodes.len();
        let root = match self.clone_node(node) {
            Some(root) => root,
            None => {
                proof {
                    lemma_root_fits(d0, node);
                }
                return None;
            },
        };
        proof {
            assert(can_create(d0, clone_count(d0, node)));
            assert(root == d0.nodes.len());
            lemma_deep_init(d0, node);
            lemma_inv_facts(d0, node, self@, order_after(d0, Seq::empty(), node), 0, 0);
            lemma_wf_bound(self@);
        }
        let mut order: Vec<usize> = Vec::new();
        order.push(node);
        if let Some(f) = template_contents_exec(self.kind(node)) {
            order.push(f);
        }
        proof {
            assert(order@ =~= order_after(d0, Seq::empty(), node));
            lemma_inv_facts(d0, node, self@, order@, 0, 0);
            assert(self@.nodes[node as int] == d0.nodes[node as int]);
        }
        let mut i: usize = 0;
        let mut j: usize = 0;
        let mut nch: usize = self.children(node).len();
        while i < order.len()
            invariant
                d0 == old(self)@,
                base == d0.nodes.len(),
                host_acyclic(d0),
                deep_inv(d0, node, self@, order@, i as int, j as int),
                i < order.len() ==> nch == d0.nodes[order@[i as int] as int].children.len(),
                i < order.len() ==> j <= nch,
                i <= order.len(),
                self@.nodes.len() == base + order.len(),
                self@.nodes.len() <= MAX_NODES,
            decreases MAX_NODES - i, nch - j,
        {
            if j < nch {
                if !self.deep_step(&mut order, base, i, j, Ghost(d0), Ghost(node)) {
                    proof {
                        assert(self@ == d0);
                        assert(d0 == old(self)@);
                    }
                    return None;
                }
                // j < nch <= the node count: never saturates.
                j = j.saturating_add(1);
            } else {
                proof {
                    lemma_advance(d0, node, self@, order@, i as int, j as int);
                }
                // i < order.len(): never saturates.
                i = i.saturating_add(1);
                j = 0;
                match order.get(i) {
                    Some(s) => {
                        proof {
                            lemma_inv_facts(d0, node, self@, order@, i as int, 0);
                            assert(self@.nodes[*s as int] == d0.nodes[*s as int]);
                        }
                        nch = self.children(*s).len();
                    },
                    None => {
                        nch = 0;
                    },
                }
            }
            proof {
                lemma_inv_facts(d0, node, self@, order@, i as int, j as int);
                lemma_wf_bound(self@);
            }
        }
        proof {
            lemma_deep_done(d0, node, self@, order@, i as int, j as int);
            theorem_deep_clone_size(d0, node, self@, order@);
        }
        Some(root)
    }

    /// DOM §4.4† "clone a node", shallow ([`clone_node_ensures`]).
    pub fn clone_node(&mut self, node: usize) -> (r: Option<usize>)
        requires
            clone_requires(old(self)@, node),
        ensures
            clone_node_ensures(old(self)@, node, final(self)@, r),
    {
        let ghost d0 = self@;
        // 2. and 3.
        let kind = clone_kind_exec(self.kind(node));
        let template = is_template_exec(self.kind(node));
        let count: usize = if template {
            2
        } else {
            1
        };
        if self.nodes.len().saturating_add(count) > MAX_NODES {
            return None;
        }
        proof {
            let k = d0.nodes[node as int].kind;
            assert(creatable(d0, clone_kind(k)));
        }
        let id = self.create(kind)?;
        // 5.
        if template {
            proof {
                let k = d0.nodes[node as int].kind;
                theorem_create_node_wf(d0, clone_kind(k));
            }
            let _contents = self.create_template_contents(id);
        }
        Some(id)
    }

    /// DOM §4.9† "change an attribute" ([`change_attribute_ensures`]).
    pub fn change_attribute(&mut self, e: usize, i: usize, value: Vec<u32>)
        requires
            attribute_requires(old(self)@, e, i as nat),
        ensures
            change_attribute_ensures(old(self)@, e, i as nat, value@, final(self)@),
    {
        let ghost s0 = self.nodes@;
        let ghost v = value@;
        let mut y = self.take(e);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Element { namespace, prefix, local_name, mut attributes, template_contents, form_owner } => {
                let ghost before = attributes@;
                let mut old_attr = ExecAttr { namespace: None, prefix: None, local_name: Vec::new(), value: Vec::new() };
                attributes.set_and_swap(i, &mut old_attr);
                old_attr.value = value;
                attributes.set(i, old_attr);
                proof {
                    assert(attrs_view(attributes@) =~= attrs_view(before).update(i as int, Attr { value: v, ..attrs_view(before)[i as int] }));
                }
                ExecKind::Element { namespace, prefix, local_name, attributes, template_contents, form_owner }
            },
            other => other,
        };
        self.put(e, y, Ghost(s0));
        proof {
            lemma_view_update(s0, e as int, y);
            assert(self@.nodes =~= change_attribute(old(self)@, e, i as nat, v).nodes);
        }
    }

    /// DOM §4.9† "remove an attribute" ([`remove_attribute_ensures`]).
    pub fn remove_attribute(&mut self, e: usize, i: usize)
        requires
            attribute_requires(old(self)@, e, i as nat),
        ensures
            remove_attribute_ensures(old(self)@, e, i as nat, final(self)@),
    {
        let ghost s0 = self.nodes@;
        let mut y = self.take(e);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Element { namespace, prefix, local_name, mut attributes, template_contents, form_owner } => {
                let ghost before = attributes@;
                let _removed = attributes.remove(i);
                proof {
                    assert(attrs_view(attributes@) =~= attrs_view(before).remove(i as int));
                }
                ExecKind::Element { namespace, prefix, local_name, attributes, template_contents, form_owner }
            },
            other => other,
        };
        self.put(e, y, Ghost(s0));
        proof {
            lemma_view_update(s0, e as int, y);
            assert(self@.nodes =~= remove_attribute(old(self)@, e, i as nat).nodes);
        }
    }

    /// DOM §4.9† "replace an attribute" ([`replace_attribute_ensures`]).
    pub fn replace_attribute(&mut self, e: usize, i: usize, new_attr: ExecAttr)
        requires
            attribute_requires(old(self)@, e, i as nat),
        ensures
            replace_attribute_ensures(old(self)@, e, i as nat, new_attr@, final(self)@),
    {
        let ghost s0 = self.nodes@;
        let ghost a = new_attr@;
        let mut y = self.take(e);
        let mut kind = ExecKind::DocumentFragment { host: None };
        core::mem::swap(&mut y.kind, &mut kind);
        y.kind = match kind {
            ExecKind::Element { namespace, prefix, local_name, mut attributes, template_contents, form_owner } => {
                let ghost before = attributes@;
                attributes.set(i, new_attr);
                proof {
                    assert(attrs_view(attributes@) =~= attrs_view(before).update(i as int, a));
                }
                ExecKind::Element { namespace, prefix, local_name, attributes, template_contents, form_owner }
            },
            other => other,
        };
        self.put(e, y, Ghost(s0));
        proof {
            lemma_view_update(s0, e as int, y);
            assert(self@.nodes =~= replace_attribute(old(self)@, e, i as nat, a).nodes);
        }
    }
}

} // verus!
