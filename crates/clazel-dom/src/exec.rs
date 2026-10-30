//! The executable arena (Phase 4 item 4.8): a `Vec` of nodes indexed by
//! id, whose view is the spec's [`Document`]. Every method's `requires` and
//! `ensures` are the predicates of [`super::contract`], so each is proven
//! equal to its spec function, and [`super::lemmas`] proves those keep
//! [`wf`].
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
use super::lemmas::*;
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

    /// Steps 7.1 of "insert": adopt `node` (remove it from its parent, if
    /// any).
    fn adopt(&mut self, node: usize)
        requires
            wf(old(self)@),
            valid(old(self)@, node),
        ensures
            final(self)@ == adopt(old(self)@, node),
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

    /// DOM §4.2 "parent" ([`readers_ensures`]).
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

    /// DOM §4.2 "last child" ([`readers_ensures`]).
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

    /// DOM §4.2 "previous sibling" ([`readers_ensures`]).
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

} // verus!
