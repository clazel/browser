# Audits of `clazel-sys`

`clazel-sys` is the only crate that contains `unsafe` (CLAUDE.md rule 1,
[VERIFICATION.md](VERIFICATION.md#the-unsafe-exception)). Machine checks
bound what it can do; this log records the second half of "audited": **every
change to the crate is read by an LLM session other than the one that wrote
it**, and the result is recorded here against the exact source.

**Whoever wrote or edited any file of `clazel-sys` never writes its audit
row**, in that session or a continuation of it. This is a rule, not a machine
check: the checker cannot tell who wrote a row, so it can only make sure a
row exists for the current source. It is also not a proof: an audit is a
second opinion from a model. Do not describe the crate as verified.

## What `cargo xtask check` does with this file

It computes the SHA-256 of the crate's source and compares it with the
**latest** row (the last one in the table). It fails if there is no row, if
the hash differs, or if the latest verdict is not `approved`. Every edit to
any file in the crate therefore needs a new row, and an old matching row does
not help once a later row exists.

### The hash

The files hashed are every regular file under `crates/clazel-sys`, except
hidden files and directories (names starting with `.`) and any `target/`
directory, in byte order of their repo-relative path. For each file one line
`<sha256 of the file>  <path>` (two spaces, the format of `shasum -a 256`) is
formed, and the audit hash is the SHA-256 of those lines, each ended by a
newline. From the repository root, by hand:

```sh
find crates/clazel-sys -type f -not -path '*/.*' -not -path '*/target/*' \
  | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256
```

`cargo xtask check` prints the hash and the files it covers under
"clazel-sys audit". Symbolic links inside the crate are an error.

## How to audit

You are the auditor only if you did not write or edit the code being audited.
If you did, stop: tell the maintainer that another session must audit it.

1. Run `cargo xtask check` and note the hash it prints. Read every file it
   lists, in full, not a diff. Stop if any file is missing from the list that
   should be there.
2. For **each** `unsafe` block, open the man page it cites (`man 2 prctl`,
   `man 2 seccomp`, `man 7 landlock` and the `landlock_*` pages, `man 2
   unshare`, `man 3 sandbox_init`) and the `libc` declaration of the function
   and of every type and constant passed to it (in the pinned `libc` version
   from `docs/DEPENDENCIES.md`). Check:
   - the argument count, types, sizes and signedness match the declaration;
   - every pointer passed is non-null where required, aligned, points to
     initialised memory of the stated size, and outlives the call (a pointer
     taken before the block must not be to a temporary dropped earlier);
   - the structure layout is `libc`'s or `#[repr(C)]` with the kernel's field
     order, and its length argument is computed, not typed;
   - the return value is checked as the man page says (`-1` and `errno`), the
     error is read with nothing in between, and a failure is never reported
     as success;
   - a file descriptor returned is owned exactly once and closed on every
     path (`OwnedFd`), and memory returned by the system is freed exactly
     once (`sandbox_free_error`);
   - the block holds one call, as the checker already requires, and the
     `// SAFETY:` comment states the real reason it is sound, not a restated
     precondition.
3. Check the safe wrapper around each block: that its narrow types make the
   unsound call impossible from safe code (no length that can exceed the
   slice, no string with an interior NUL reaching the call), and that it makes
   no policy decision (it never chooses what to allow).
4. Check what the checker cannot: that nothing in the crate calls a function
   that merely resembles a listed one, that the `cfg` gating matches the
   target of each call, and that tests which call the OS do not weaken the
   test process irreversibly and are skipped under Miri.
5. Add **one row** below, last in the table: date, the hash from step 1,
   which session or tool audited (not who wrote the code), what you audited
   against (man page and `libc` versions, plus what you could not check), and
   a verdict: `approved` or `rejected`. Put findings of any kind in the row or
   in the report; a `rejected` row stays in the log. Never edit or remove an
   earlier row, and never touch a file of `clazel-sys` while auditing: if the
   audit finds a problem, the fix is a change by someone else, which then
   needs its own audit.

<!-- BEGIN AUDITS: checked by `cargo xtask check` -->
| Date | SHA-256 | Auditor | Audited against | Verdict |
|------|---------|---------|-----------------|---------|
| 2026-10-21 | 50caf1f0a799efa775fb021cd4072a04b23c130bd8d91158eb320f6e2de2288f | Claude Sonnet 5.5 audit session on branch phase2/sys-audit (did not write the crate) | man7.org man-pages 6.19 for prctl(2), seccomp(2), landlock(7), landlock_create_ruleset(2), landlock_restrict_self(2), unshare(2); Linux security/landlock/syscalls.c (master); macOS `man 3 sandbox_init` and the CommandLineTools SDK sandbox.h; libc 0.2.190 (`sock_filter`, `sock_fprog`, `prctl`, `syscall`, `unshare`, `SECCOMP_SET_MODE_FILTER`, `PR_SET_NO_NEW_PRIVS`, `CLONE_NEW*`, `SYS_seccomp` 317/277, `SYS_landlock_*` 444-446 on x86_64 and aarch64). Built and clippy-checked for x86_64 and aarch64 linux-gnu; ran the macOS tests (the real `sandbox_init` rejected the bad profile with a syntax error and left the process unconfined). Not run: any Linux call at run time (no Linux host), Miri. Non-blocking findings: (1) `seccomp_set_mode_filter` doc says the filter applies "from every thread created afterwards" but does not say that threads that already exist are NOT covered (no TSYNC; the man page confirms per-thread), so callers must install it before spawning threads; (2) macos.rs SAFETY says flags 0 means SBPL source per the man page, but sandbox.h calls other flag values reserved and the man page never states it: flags 0 as SBPL is de facto (Chromium/Firefox) and observed to work here; (3) `landlock_deny_filesystem` passes size 8 (ABI 1) though the man page says to pass sizeof of the current struct (24); the kernel accepts it via copy_min_struct_from_user with the new fields zero, as wanted; (4) the Landlock ruleset fd (O_CLOEXEC, harmless once enforced) is leaked on every call including when restrict_self fails; (5) the Landlock doc does not mention that restrict_self needs no_new_privs (EPERM otherwise); (6) lib.rs "none panics" ignores allocation failure. | approved |
| 2026-10-21 | 78db3ad94cd36d42999fb0511a01e2a71d2c4a3952ac90de009cdc7cf4635c55 | Claude Sonnet 5.5 audit session on branch phase2/sys-audit-2 (did not write the change) | Incremental audit of the diff on top of the state approved at 50caf1f0 (the tree of commit 1ca6128, the commit that added that row). `git diff 1ca6128..main -- crates/clazel-sys` is one line in `crates/clazel-sys/Cargo.toml`: `"cfg(kani)"` added to the `unexpected_cfgs` `check-cfg` list in `[lints.rust]`, which is now identical to `[workspace.lints.rust]` in the root Cargo.toml (`cargo xtask check` passes its lint-override step). No `.rs` file changed (the diff names only Cargo.toml; git shows exactly one commit, f255361, touching the crate since 1ca6128), so every `unsafe` block, foreign declaration, `// SAFETY:` comment, safe wrapper and the `cfg` gating are byte-identical to what 50caf1f0 approved, and the findings (1)-(6) of that row still stand unchanged. A `check-cfg` entry only declares that the cfg name `kani` is expected so rustc does not warn; it enables no cfg, adds no code, changes no lint level and cannot affect the soundness of any `pub fn`. Hash recomputed by hand with the command in this file and equal to the one `cargo xtask check` prints. Not re-run: man pages and libc declarations (unchanged source), Linux calls at run time, Miri. | approved |
| 2026-10-24 | 98711435d839ac25d988b89e4d2178a4ea6af7b78a39062acc7d10e42b78dc28 | Claude Sonnet 5.5 audit session on branch phase2/fork-ptrace-audit (did not write the change) | Incremental audit of the changes of branch phase2/fork-ptrace to `crates/clazel-sys` over main (state approved at 78db3ad9), reading all 4 files in full. Added: `attempt_fork` and `attempt_ptrace_attach` for Linux and macOS, `Errno::last` now also cfg'd for macOS, and `fork`, `_exit`, `ptrace`, `SYS_ptrace` on the xtask list. macOS declarations checked against the CommandLineTools SDK headers: `pid_t fork(void)` (unistd.h:459), `void _exit(int) __dead2` (unistd.h:442), `int ptrace(int _request, pid_t _pid, caddr_t _addr, int _data)` (sys/ptrace.h:100, not variadic, C ABI), `caddr_t` is `char *`, `PT_ATTACHEXC` is 14 (ptrace.h:90), `EINVAL` is 22 (errno.h:112); the hand-written `unsafe extern "C"` block matches each. Linux checked against libc 0.2.190: `fork() -> pid_t` (unix/mod.rs:1178), `_exit(c_int) -> !` (unix/mod.rs:784), `PTRACE_ATTACH` 16 (`c_uint` on gnu, `c_int` on musl; both convert losslessly through `i64::from` and `c_ulong::try_from`), `SYS_ptrace` 101 on x86_64 and 117 on aarch64; the raw `ptrace` system call with PTRACE_ATTACH takes (request, pid, addr, data) as integers and returns 0 or -1 with errno (the glibc wrapper's extra handling concerns only the PEEK requests). In both `attempt_fork` functions the child path runs only the `pid == 0` test and `_exit(0)`: no allocation, lock, drop or `exit`, so it is sound in a multithreaded process. The child is not reaped: it stays a zombie until the calling process exits, then is reparented and reaped; the callers are the short-lived clazel-adversary processes, so this is negligible. Ran: `cargo xtask check` (failed only on this audit step before this row), clippy on macOS, x86_64-linux-gnu and aarch64-linux-gnu (clean), `cargo test -p clazel-sys` on macOS (4 passed), Miri with nightly-2026-08-21 (3 passed, 1 ignored foreign call). Not run: any Linux call at run time, the Linux unit tests, musl targets. Non-blocking findings: (1) the unit tests of both `attempt_ptrace_attach` only cover the non-positive pid guard, not the call; (2) the Linux doc says the tracee is left stopped, which holds once it handles the SIGSTOP that PTRACE_ATTACH sends; (3) `libc::fork` runs glibc's atfork handlers in the calling thread, which the SAFETY comment does not mention (std registers none). | approved |
<!-- END AUDITS -->
