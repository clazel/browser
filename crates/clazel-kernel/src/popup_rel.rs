//! Item 7.16's popups (`OpenTab` from a renderer): the facts about a
//! domain's transient user activations that the noninterference proof needs
//! (they mirror the document URLs', `url_rel.rs`), and the proofs of
//! `theorem_popup_needs_input` (`popup_theorems.rs` has the step and the
//! trace).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The activations of a domain.
// ---------------------------------------------------------------------

/// Forgetting an activation commutes with taking a domain's.
pub proof fn lemma_acts_forget_commute(rules: Seq<clazel_psl::spec::Rule>, acts: Seq<Activation>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    ensures
        crate::domain::acts_of_domain(rules, forget_activation(acts, id, lock), d) == forget_activation(crate::domain::acts_of_domain(rules, acts, d), id, lock),
{
    crate::surface_rel::lemma_filter_commute(
        acts,
        |x: Activation| !(x.id == id && x.lock == lock),
        |x: Activation| crate::domain::domain_of_lock(rules, x.lock) == d,
    );
}

/// Forgetting an activation under a lock of another domain does not change
/// the domain's.
pub proof fn lemma_acts_forget_other(rules: Seq<clazel_psl::spec::Rule>, acts: Seq<Activation>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) != d,
    ensures
        crate::domain::acts_of_domain(rules, forget_activation(acts, id, lock), d) == crate::domain::acts_of_domain(rules, acts, d),
{
    lemma_acts_forget_commute(rules, acts, id, lock, d);
    let dd = crate::domain::acts_of_domain(rules, acts, d);
    let keep = |x: Activation| !(x.id == id && x.lock == lock);
    let ind = |x: Activation| crate::domain::domain_of_lock(rules, x.lock) == d;
    assert forall|i: int| 0 <= i < dd.len() implies keep(#[trigger] dd[i]) by {
        acts.lemma_filter_pred(ind, i);
    }
    crate::surface_rel::lemma_filter_all(dd, keep);
}

/// Setting an activation under a lock of another domain does not change the
/// domain's.
pub proof fn lemma_acts_set_other(rules: Seq<clazel_psl::spec::Rule>, acts: Seq<Activation>, id: nat, lock: clazel_origin::spec::Origin, left: nat, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) != d,
    ensures
        crate::domain::acts_of_domain(rules, set_activation(acts, id, lock, left), d) == crate::domain::acts_of_domain(rules, acts, d),
{
    lemma_acts_forget_other(rules, acts, id, lock, d);
    crate::surface_rel::lemma_filter_push(forget_activation(acts, id, lock), Activation { id, lock, left }, |x: Activation| crate::domain::domain_of_lock(rules, x.lock) == d);
}

/// Forgetting the same activation in two runs whose domain's agree keeps
/// them agreeing.
pub proof fn lemma_acts_forget_same(
    rules: Seq<clazel_psl::spec::Rule>,
    a1: Seq<Activation>,
    a2: Seq<Activation>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    d: crate::domain::Domain,
)
    requires
        crate::domain::acts_of_domain(rules, a1, d) == crate::domain::acts_of_domain(rules, a2, d),
    ensures
        crate::domain::acts_of_domain(rules, forget_activation(a1, id, lock), d) == crate::domain::acts_of_domain(rules, forget_activation(a2, id, lock), d),
{
    lemma_acts_forget_commute(rules, a1, id, lock, d);
    lemma_acts_forget_commute(rules, a2, id, lock, d);
}

/// Setting the same activation in two runs whose domain's agree keeps them
/// agreeing.
pub proof fn lemma_acts_set_same(
    rules: Seq<clazel_psl::spec::Rule>,
    a1: Seq<Activation>,
    a2: Seq<Activation>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    left: nat,
    d: crate::domain::Domain,
)
    requires
        crate::domain::acts_of_domain(rules, a1, d) == crate::domain::acts_of_domain(rules, a2, d),
    ensures
        crate::domain::acts_of_domain(rules, set_activation(a1, id, lock, left), d) == crate::domain::acts_of_domain(rules, set_activation(a2, id, lock, left), d),
{
    lemma_acts_forget_same(rules, a1, a2, id, lock, d);
    let ind = |x: Activation| crate::domain::domain_of_lock(rules, x.lock) == d;
    crate::surface_rel::lemma_filter_push(forget_activation(a1, id, lock), Activation { id, lock, left }, ind);
    crate::surface_rel::lemma_filter_push(forget_activation(a2, id, lock), Activation { id, lock, left }, ind);
}

/// One tick of the clock keeps an activation's id and lock.
pub open spec fn aged(x: Activation) -> Activation {
    Activation { left: if x.left > 0 { (x.left - 1) as nat } else { 0 }, ..x }
}

/// Ageing adds an entry's aged form at the end.
pub proof fn lemma_age_push(acts: Seq<Activation>, x: Activation)
    ensures
        age_activations(acts.push(x)) == age_activations(acts).push(aged(x)),
{
    assert(age_activations(acts.push(x)) =~= age_activations(acts).push(aged(x)));
}

/// Ageing commutes with taking a domain's activations.
pub proof fn lemma_acts_age_commute(rules: Seq<clazel_psl::spec::Rule>, acts: Seq<Activation>, d: crate::domain::Domain)
    ensures
        crate::domain::acts_of_domain(rules, age_activations(acts), d) == age_activations(crate::domain::acts_of_domain(rules, acts, d)),
    decreases acts.len(),
{
    reveal(Seq::filter);
    let ind = |x: Activation| crate::domain::domain_of_lock(rules, x.lock) == d;
    if acts.len() == 0 {
        assert(age_activations(acts) =~= Seq::<Activation>::empty());
        assert(age_activations(acts.filter(ind)) =~= Seq::<Activation>::empty());
    } else {
        let t = acts.drop_last();
        let x = acts.last();
        assert(acts == t.push(x));
        lemma_acts_age_commute(rules, t, d);
        lemma_age_push(t, x);
        crate::surface_rel::lemma_filter_push(age_activations(t), aged(x), ind);
        crate::surface_rel::lemma_filter_push(t, x, ind);
        assert(ind(aged(x)) == ind(x));
        if ind(x) {
            lemma_age_push(t.filter(ind), x);
        }
    }
}

/// Ageing in two runs whose domain's activations agree keeps them agreeing.
pub proof fn lemma_acts_age_same(rules: Seq<clazel_psl::spec::Rule>, a1: Seq<Activation>, a2: Seq<Activation>, d: crate::domain::Domain)
    requires
        crate::domain::acts_of_domain(rules, a1, d) == crate::domain::acts_of_domain(rules, a2, d),
    ensures
        crate::domain::acts_of_domain(rules, age_activations(a1), d) == crate::domain::acts_of_domain(rules, age_activations(a2), d),
{
    lemma_acts_age_commute(rules, a1, d);
    lemma_acts_age_commute(rules, a2, d);
}

/// The activation of a renderer of domain `d` is read from `d`'s entries
/// alone.
pub proof fn lemma_activation_left_domain(rules: Seq<clazel_psl::spec::Rule>, acts: Seq<Activation>, r: Renderer, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        activation_left(acts, r) == activation_left(crate::domain::acts_of_domain(rules, acts, d), r),
    decreases acts.len(),
{
    let ind = |x: Activation| crate::domain::domain_of_lock(rules, x.lock) == d;
    if acts.len() > 0 {
        let x = acts[0];
        let rest = acts.drop_first();
        assert(acts =~= seq![x] + rest);
        rest.lemma_filter_prepend(x, ind);
        lemma_activation_left_domain(rules, rest, r, d);
        let fr = rest.filter(ind);
        if ind(x) {
            assert(acts.filter(ind) == seq![x] + fr);
            assert((seq![x] + fr)[0] == x);
            assert((seq![x] + fr).drop_first() =~= fr);
        } else {
            assert(acts.filter(ind) =~= fr);
            assert(!(x.id == r.id && x.lock == r.lock));
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Related states give a renderer of `d` the same activation.
pub proof fn lemma_activation_left_rel(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, r: Renderer)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        activation_left(s1.acts, r) == activation_left(s2.acts, r),
{
    lemma_activation_left_domain(rules, s1.acts, r, d);
    lemma_activation_left_domain(rules, s2.acts, r, d);
}

/// [`activation_left`] reads only a renderer's id and lock.
pub proof fn lemma_activation_left_fields(acts: Seq<Activation>, r1: Renderer, r2: Renderer)
    requires
        r1.id == r2.id,
        r1.lock == r2.lock,
    ensures
        activation_left(acts, r1) == activation_left(acts, r2),
    decreases acts.len(),
{
    if acts.len() > 0 {
        lemma_activation_left_fields(acts.drop_first(), r1, r2);
    }
}

// ---------------------------------------------------------------------
// The popup is the host's `OpenTab`.
// ---------------------------------------------------------------------

/// The URL a renderer's `OpenTab { url }` resolves to, if the kernel goes
/// on to open a tab at it: the sender holds a live activation, and the text
/// decodes and resolves against its committed URL.
pub open spec fn popup_resolved(urls: UrlFns, s: State, r: Renderer, url: Seq<u8>) -> Option<Seq<u32>> {
    if activation_left(s.acts, r) == 0 {
        None
    } else {
        match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            None => None,
            Some(relative) => (urls.resolve)(r.url, relative),
        }
    }
}

/// An `OpenTab` frame does nothing, or is the popup of [`popup_resolved`]:
/// the host's `OpenTab` of it, then the activation spent.
pub proof fn lemma_popup_resolved(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, url: Seq<u8>)
    ensures
        handle_message(rules, urls, fetch, s, r, clazel_ipc::message::spec::Message::OpenTab { url }) == (match popup_resolved(urls, s, r, url) {
            None => (s, Seq::<Output>::empty()),
            Some(resolved) => popup_result(rules, urls, fetch, s, r, resolved),
        }),
{
}

/// The frame `bytes` of renderer `id` is a popup the kernel goes on to open:
/// an accepted `OpenTab` whose URL [`popup_resolved`] gives.
pub open spec fn popup_opens(urls: UrlFns, s: State, id: nat, bytes: Seq<u8>) -> bool {
    match find_by_id(s.renderers, id, 0) {
        Some(i) => match accepted_message(s.renderers[i], bytes) {
            Some(clazel_ipc::message::spec::Message::OpenTab { url }) => popup_resolved(urls, s, s.renderers[i], url) is Some,
            _ => false,
        },
        None => false,
    }
}

/// Replacing the activations of two related states by ones that agree on the
/// observer's keeps them related.
pub proof fn lemma_rel_acts_update(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, a1: Seq<Activation>, a2: Seq<Activation>)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::acts_of_domain(rules, a1, d) == crate::domain::acts_of_domain(rules, a2, d),
    ensures
        crate::noninterference::rel(rules, urls, d, State { acts: a1, ..s1 }, State { acts: a2, ..s2 }),
{
    let t1 = State { acts: a1, ..s1 };
    let t2 = State { acts: a2, ..s2 };
    assert(crate::invariant::kernel_wf(rules, urls, t1));
    assert(crate::invariant::kernel_wf(rules, urls, t2));
    assert(t1.renderers == s1.renderers && t2.renderers == s2.renderers);
    assert(crate::noninterference::rel_conn(t1, t2));
}

/// The user's `Input` from related states leaves them related: an
/// activating input sets one entry, of the observed domain in both runs or
/// of another domain in one or both.
pub proof fn lemma_input_rel(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, tab: nat, input: UserInput)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, user_input(s1, tab, input).0, user_input(s2, tab, input).0),
{
    if let Some(i1) = find_by_tab(s1.renderers, tab, 0) {
        crate::net_rel::lemma_same_renderer_by_tab(rules, urls, d, s1, s2, tab);
        let r = s1.renderers[i1];
        let i2 = find_by_tab(s2.renderers, tab, 0)->Some_0;
        assert(s2.renderers[i2] == r);
        if r.committed && is_activating_input(input) {
            if crate::domain::domain_of_renderer(rules, r) == d {
                lemma_acts_set_same(rules, s1.acts, s2.acts, r.id, r.lock, activation_window(), d);
            } else {
                lemma_acts_set_other(rules, s1.acts, r.id, r.lock, activation_window(), d);
                lemma_acts_set_other(rules, s2.acts, r.id, r.lock, activation_window(), d);
            }
            lemma_rel_acts_update(
                rules,
                urls,
                d,
                s1,
                s2,
                set_activation(s1.acts, r.id, r.lock, activation_window()),
                set_activation(s2.acts, r.id, r.lock, activation_window()),
            );
        } else {
            lemma_rel_acts_update(rules, urls, d, s1, s2, s1.acts, s2.acts);
        }
    } else if let Some(i2) = find_by_tab(s2.renderers, tab, 0) {
        crate::unwind_base::lemma_found_contained(s2, tab);
        let r2 = s2.renderers[i2];
        // `r2` is not the observer's: a renderer of `d` in the second run is in
        // the first, where the tab has none.
        assert(crate::domain::domain_of_renderer(rules, r2) != d) by {
            if crate::domain::domain_of_renderer(rules, r2) == d {
                assert(s1.renderers.contains(r2));
                crate::unwind_base::lemma_find_contained(urls, s1, r2);
            }
        }
        if r2.committed && is_activating_input(input) {
            lemma_acts_set_other(rules, s2.acts, r2.id, r2.lock, activation_window(), d);
            lemma_rel_acts_update(rules, urls, d, s1, s2, s1.acts, set_activation(s2.acts, r2.id, r2.lock, activation_window()));
        } else {
            lemma_rel_acts_update(rules, urls, d, s1, s2, s1.acts, s2.acts);
        }
    } else {
        lemma_rel_acts_update(rules, urls, d, s1, s2, s1.acts, s2.acts);
    }
}

/// The outputs of the host's `OpenTab` without a script, as a renderer's
/// popup gives them (item 7.16): a `Spawn` pair for the new renderer, and
/// the start of its tab's fetch, which sends only to it and opens connections
/// of this step, closes none and asks for nothing else.
pub proof fn lemma_open_tab_outputs(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, resolved: Seq<u32>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        ({
            let (s1, out) = open_tab(rules, urls, fetch, s, resolved, None);
            &&& s.next_conn <= s1.next_conn
            &&& forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer }),
                    Output::Spawn { id: x, .. } => x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Gpu }) && out.contains(
                        Output::Spawn { id: x, policy: Policy::Renderer },
                    ),
                    Output::Kill { .. } => false,
                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                    Output::Send { .. } => false,
                    Output::Close { .. } => false,
                    Output::Show { .. } => false,
                    Output::ToGpu { id: x, .. } => x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Gpu }),
                    Output::Paint { .. } => false,
                    Output::GpuStopped { .. } | Output::GpuAllSoftware => false,
                    Output::SubConnect { .. } | Output::SubSend { .. } | Output::SubClose { .. } => false,
                }
        }),
{
    let id = s.next_id;
    let (s1, out) = open_tab(rules, urls, fetch, s, resolved, None);
    if let Some(lock) = lock_of_url(urls, resolved, id) {
        let rn = Renderer { committed: false, id, tab: id, url: resolved, lock, pending: None };
        let sp = State { renderers: s.renderers.push(rn), next_id: id + 1, ..s };
        crate::invariant::lemma_open_tab_push_wf(rules, urls, s, resolved, lock, false);
        crate::net_theorems::lemma_begin_outputs(rules, urls, fetch, sp, id, resolved, clazel_fetch::request::spec::get_req());
        let (sb, ob) = begin_navigation(rules, urls, fetch, sp, id, resolved, clazel_fetch::request::spec::get_req());
        assert(out == seq![Output::Spawn { id, policy: Policy::Gpu }, Output::Spawn { id, policy: Policy::Renderer }] + ob);
        assert(out[0] == Output::Spawn { id, policy: Policy::Gpu });
        assert(out[1] == Output::Spawn { id, policy: Policy::Renderer });
        assert(out.contains(out[0]) && out.contains(out[1]));
        let n = s.renderers.len() as int;
        assert(sp.renderers[n] == rn);
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::ToRenderer { id: x, .. } => x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer }),
            Output::Spawn { id: x, .. } => x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Gpu }) && out.contains(Output::Spawn { id: x, policy: Policy::Renderer }),
            Output::Kill { .. } => false,
            Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
            Output::Send { .. } => false,
            Output::Close { .. } => false,
            Output::Show { .. } => false,
            Output::ToGpu { id: x, .. } => x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Gpu }),
            Output::Paint { .. } => false,
            Output::GpuStopped { .. } | Output::GpuAllSoftware => false,
            Output::SubConnect { .. } | Output::SubSend { .. } | Output::SubClose { .. } => false,
        } by {
            if k >= 2 {
                assert(out[k] == ob[k - 2]);
                match out[k] {
                    Output::ToRenderer { id: x, .. } => {
                        let i = choose|i: int| 0 <= i < sp.renderers.len() && sp.renderers[i].tab == id && sp.renderers[i].id == x;
                        if i < n {
                            assert(sp.renderers[i] == s.renderers[i]);
                            assert(s.renderers[i].tab < s.next_id);
                        } else {
                            assert(i == n);
                        }
                    },
                    Output::Close { conn: x } => {
                        let j = choose|j: int| 0 <= j < sp.conns.len() && sp.conns[j].id == x && sp.conns[j].tab == id;
                        assert(crate::invariant::conn_backed(sp.renderers, sp.conns[j]));
                        let m = choose|m: int| 0 <= m < sp.renderers.len() && (#[trigger] sp.renderers[m]).tab == sp.conns[j].tab && (sp.renderers[m].pending matches Some(nav) && nav.partition == sp.conns[j].partition);
                        if m < n {
                            assert(sp.renderers[m] == s.renderers[m]);
                            assert(s.renderers[m].tab < s.next_id);
                        } else {
                            assert(m == n);
                        }
                    },
                    _ => {},
                }
            }
        }
    } else {
        assert(out =~= Seq::<Output>::empty());
    }
}

} // verus!
