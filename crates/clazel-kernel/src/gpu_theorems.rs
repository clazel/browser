//! Phase 5 item 5.17c's theorems, stated in `statements.rs`: a GPU process's
//! exit changes no other tab's state or output (`theorem_gpu_exit_contained`);
//! a tab's GPU process is restarted in one mode at most twice within five
//! minutes after exits in that mode (`theorem_gpu_restart_bounded`); every
//! tab goes to software only through the host, a refusal before any page
//! reached the process, or hardware exits from three sites within five
//! minutes (`theorem_site_cannot_demote_others`, with
//! `theorem_gpu_sites_wf_kept`); and a frame from an exited GPU process is
//! never painted (`theorem_paint_after_restart`, 5.18's paint theorems
//! restated over restarts). None assumes anything of the GPU process or the
//! page.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `theorem_gpu_exit_contained`.
pub proof fn theorem_gpu_exit_contained(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat)
    ensures
        crate::statements::gpu_exit_contained_statement(rules, urls, fetch, s, id),
{
}

/// `theorem_gpu_restart_bounded`.
pub proof fn theorem_gpu_restart_bounded(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat)
    ensures
        crate::statements::gpu_restart_bounded_statement(rules, urls, fetch, s, id),
{
}

/// `theorem_site_cannot_demote_others`.
pub proof fn theorem_site_cannot_demote_others(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        crate::statements::site_cannot_demote_others_statement(rules, urls, fetch, s, e),
{
}

/// `theorem_gpu_sites_wf_kept`.
pub proof fn theorem_gpu_sites_wf_kept(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        crate::statements::gpu_sites_wf_kept_statement(rules, urls, fetch, s, e),
{
}

/// `theorem_paint_after_restart`.
pub proof fn theorem_paint_after_restart(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    ensures
        crate::statements::paint_after_restart_statement(rules, urls, fetch, s, id, bytes),
{
}

} // verus!
