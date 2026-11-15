//! Cross-checks every number and constant in `src/` against the Linux v6.12
//! files vendored under `vendor/linux/` (see `SOURCE.md` there), so that none
//! of them rests on memory.

use clazel_sandbox::bpf::*;
use clazel_sandbox::landlock as ll;
use clazel_sandbox::namespaces as ns;
use clazel_sandbox::seccomp as sc;
use clazel_sandbox::syscalls::{self, Arch};
use std::collections::HashMap;

fn vendored(name: &str) -> Result<String, String> {
    let path = format!("{}/vendor/linux/{name}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).map_err(|e| format!("{path}: {e}"))
}

/// All `#define NAME value` lines of the given headers, unevaluated.
fn defines(files: &[&str]) -> Result<HashMap<String, String>, String> {
    let mut map = HashMap::new();
    for f in files {
        for line in vendored(f)?.lines() {
            let Some(rest) = line.strip_prefix("#define") else {
                continue;
            };
            let rest = rest.trim_start();
            let name: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            let after = rest.get(name.len()..).unwrap_or("");
            // A function-like macro has `(` straight after its name.
            if name.is_empty() || after.starts_with('(') {
                continue;
            }
            let value = after.split("/*").next().unwrap_or("").trim().to_string();
            if !value.is_empty() {
                map.entry(name).or_insert(value);
            }
        }
    }
    Ok(map)
}

/// Evaluate the small constant expressions the headers use: literals with
/// `U`/`UL`/`ULL` suffixes, identifiers, `|`, `<<` and parentheses.
fn eval(expr: &str, defs: &HashMap<String, String>) -> Result<u64, String> {
    let e = expr.trim();
    let e = e
        .strip_prefix('(')
        .and_then(|r| r.strip_suffix(')'))
        .filter(|inner| balanced(inner))
        .unwrap_or(e)
        .trim();
    if let Some((l, r)) = split_top(e, "|") {
        return Ok(eval(l, defs)? | eval(r, defs)?);
    }
    if let Some((l, r)) = split_top(e, "<<") {
        let shift = u32::try_from(eval(r, defs)?).map_err(|e| e.to_string())?;
        return eval(l, defs)?
            .checked_shl(shift)
            .ok_or_else(|| format!("shift overflow in {expr}"));
    }
    let lit = e.trim_end_matches(['U', 'L', 'u', 'l']);
    if let Some(hex) = lit.strip_prefix("0x") {
        return u64::from_str_radix(hex, 16).map_err(|e| format!("{expr}: {e}"));
    }
    if lit.chars().all(|c| c.is_ascii_digit()) && !lit.is_empty() {
        return lit.parse().map_err(|e| format!("{expr}: {e}"));
    }
    let value = defs.get(e).ok_or_else(|| format!("undefined `{e}`"))?;
    eval(value, defs)
}

fn balanced(s: &str) -> bool {
    let mut depth = 0i32;
    for c in s.chars() {
        match c {
            '(' => depth = depth.saturating_add(1),
            ')' => {
                depth = depth.saturating_sub(1);
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
}

/// Split at the first occurrence of `op` outside parentheses.
fn split_top<'a>(e: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    for (i, c) in e.char_indices() {
        match c {
            '(' => depth = depth.saturating_add(1),
            ')' => depth = depth.saturating_sub(1),
            _ if depth == 0 && e.get(i..).is_some_and(|r| r.starts_with(op)) => {
                return Some((e.get(..i)?, e.get(i.saturating_add(op.len())..)?));
            }
            _ => {}
        }
    }
    None
}

const HEADERS: &[&str] = &[
    "bpf_common.h",
    "filter.h",
    "seccomp.h",
    "audit.h",
    "elf-em.h",
    "landlock.h",
    "sched.h",
];

fn check(defs: &HashMap<String, String>, name: &str, ours: u64) -> Result<(), String> {
    let theirs = eval(name, defs)?;
    if theirs == ours {
        Ok(())
    } else {
        Err(format!("{name}: kernel {theirs:#x}, ours {ours:#x}"))
    }
}

#[test]
#[cfg_attr(miri, ignore)] // reads vendored files, which Miri's isolation forbids
fn bpf_constants_match_headers() -> Result<(), String> {
    let d = defines(HEADERS)?;
    let table: &[(&str, u16)] = &[
        ("BPF_LD", BPF_LD),
        ("BPF_LDX", BPF_LDX),
        ("BPF_ST", BPF_ST),
        ("BPF_STX", BPF_STX),
        ("BPF_ALU", BPF_ALU),
        ("BPF_JMP", BPF_JMP),
        ("BPF_RET", BPF_RET),
        ("BPF_MISC", BPF_MISC),
        ("BPF_W", BPF_W),
        ("BPF_H", BPF_H),
        ("BPF_B", BPF_B),
        ("BPF_IMM", BPF_IMM),
        ("BPF_ABS", BPF_ABS),
        ("BPF_IND", BPF_IND),
        ("BPF_MEM", BPF_MEM),
        ("BPF_LEN", BPF_LEN),
        ("BPF_MSH", BPF_MSH),
        ("BPF_ADD", BPF_ADD),
        ("BPF_SUB", BPF_SUB),
        ("BPF_MUL", BPF_MUL),
        ("BPF_DIV", BPF_DIV),
        ("BPF_OR", BPF_OR),
        ("BPF_AND", BPF_AND),
        ("BPF_LSH", BPF_LSH),
        ("BPF_RSH", BPF_RSH),
        ("BPF_NEG", BPF_NEG),
        ("BPF_MOD", BPF_MOD),
        ("BPF_XOR", BPF_XOR),
        ("BPF_JA", BPF_JA),
        ("BPF_JEQ", BPF_JEQ),
        ("BPF_JGT", BPF_JGT),
        ("BPF_JGE", BPF_JGE),
        ("BPF_JSET", BPF_JSET),
        ("BPF_K", BPF_K),
        ("BPF_X", BPF_X),
        ("BPF_A", BPF_A),
        ("BPF_TAX", BPF_TAX),
        ("BPF_TXA", BPF_TXA),
    ];
    for (name, ours) in table {
        check(&d, name, u64::from(*ours))?;
    }
    check(
        &d,
        "BPF_MAXINSNS",
        u64::try_from(BPF_MAXINSNS).map_err(|e| e.to_string())?,
    )?;
    check(
        &d,
        "BPF_MEMWORDS",
        u64::try_from(BPF_MEMWORDS).map_err(|e| e.to_string())?,
    )
}

#[test]
#[cfg_attr(miri, ignore)] // reads vendored files, which Miri's isolation forbids
fn seccomp_constants_match_headers() -> Result<(), String> {
    let d = defines(HEADERS)?;
    let table: &[(&str, u32)] = &[
        ("SECCOMP_RET_KILL_PROCESS", sc::SECCOMP_RET_KILL_PROCESS),
        ("SECCOMP_RET_KILL_THREAD", sc::SECCOMP_RET_KILL_THREAD),
        ("SECCOMP_RET_TRAP", sc::SECCOMP_RET_TRAP),
        ("SECCOMP_RET_ERRNO", sc::SECCOMP_RET_ERRNO),
        ("SECCOMP_RET_USER_NOTIF", sc::SECCOMP_RET_USER_NOTIF),
        ("SECCOMP_RET_TRACE", sc::SECCOMP_RET_TRACE),
        ("SECCOMP_RET_LOG", sc::SECCOMP_RET_LOG),
        ("SECCOMP_RET_ALLOW", sc::SECCOMP_RET_ALLOW),
        ("SECCOMP_RET_ACTION_FULL", sc::SECCOMP_RET_ACTION_FULL),
        ("__AUDIT_ARCH_64BIT", syscalls::AUDIT_ARCH_64BIT),
        ("__AUDIT_ARCH_LE", syscalls::AUDIT_ARCH_LE),
        ("EM_X86_64", syscalls::EM_X86_64),
        ("EM_AARCH64", syscalls::EM_AARCH64),
        ("AUDIT_ARCH_X86_64", syscalls::AUDIT_ARCH_X86_64),
        ("AUDIT_ARCH_AARCH64", syscalls::AUDIT_ARCH_AARCH64),
    ];
    for (name, ours) in table {
        check(&d, name, u64::from(*ours))?;
    }
    // struct seccomp_data: int nr; __u32 arch; __u64 ip; __u64 args[6];
    // = 4 + 4 + 8 + 48 = 64 bytes, nr at 0 and arch at 4.
    assert_eq!(sc::OFFSET_NR, 0);
    assert_eq!(sc::OFFSET_ARCH, 4);
    assert_eq!(sc::SECCOMP_DATA_LEN, 64);
    let header = vendored("seccomp.h")?;
    let body: Vec<&str> = header
        .lines()
        .skip_while(|l| !l.starts_with("struct seccomp_data {"))
        .take_while(|l| !l.starts_with("};"))
        .map(str::trim)
        .collect();
    assert_eq!(
        body,
        [
            "struct seccomp_data {",
            "int nr;",
            "__u32 arch;",
            "__u64 instruction_pointer;",
            "__u64 args[6];"
        ]
    );
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore)] // reads vendored files, which Miri's isolation forbids
fn landlock_and_namespace_constants_match_headers() -> Result<(), String> {
    let d = defines(HEADERS)?;
    let table: &[(&str, u64)] = &[
        ("LANDLOCK_ACCESS_FS_EXECUTE", ll::ACCESS_FS_EXECUTE),
        ("LANDLOCK_ACCESS_FS_WRITE_FILE", ll::ACCESS_FS_WRITE_FILE),
        ("LANDLOCK_ACCESS_FS_READ_FILE", ll::ACCESS_FS_READ_FILE),
        ("LANDLOCK_ACCESS_FS_READ_DIR", ll::ACCESS_FS_READ_DIR),
        ("LANDLOCK_ACCESS_FS_REMOVE_DIR", ll::ACCESS_FS_REMOVE_DIR),
        ("LANDLOCK_ACCESS_FS_REMOVE_FILE", ll::ACCESS_FS_REMOVE_FILE),
        ("LANDLOCK_ACCESS_FS_MAKE_CHAR", ll::ACCESS_FS_MAKE_CHAR),
        ("LANDLOCK_ACCESS_FS_MAKE_DIR", ll::ACCESS_FS_MAKE_DIR),
        ("LANDLOCK_ACCESS_FS_MAKE_REG", ll::ACCESS_FS_MAKE_REG),
        ("LANDLOCK_ACCESS_FS_MAKE_SOCK", ll::ACCESS_FS_MAKE_SOCK),
        ("LANDLOCK_ACCESS_FS_MAKE_FIFO", ll::ACCESS_FS_MAKE_FIFO),
        ("LANDLOCK_ACCESS_FS_MAKE_BLOCK", ll::ACCESS_FS_MAKE_BLOCK),
        ("LANDLOCK_ACCESS_FS_MAKE_SYM", ll::ACCESS_FS_MAKE_SYM),
        ("LANDLOCK_ACCESS_FS_REFER", ll::ACCESS_FS_REFER),
        ("LANDLOCK_ACCESS_FS_TRUNCATE", ll::ACCESS_FS_TRUNCATE),
        ("LANDLOCK_ACCESS_FS_IOCTL_DEV", ll::ACCESS_FS_IOCTL_DEV),
        ("LANDLOCK_ACCESS_NET_BIND_TCP", ll::ACCESS_NET_BIND_TCP),
        (
            "LANDLOCK_ACCESS_NET_CONNECT_TCP",
            ll::ACCESS_NET_CONNECT_TCP,
        ),
        (
            "LANDLOCK_SCOPE_ABSTRACT_UNIX_SOCKET",
            ll::SCOPE_ABSTRACT_UNIX_SOCKET,
        ),
        ("LANDLOCK_SCOPE_SIGNAL", ll::SCOPE_SIGNAL),
        ("CLONE_NEWNS", u64::from(ns::CLONE_NEWNS)),
        ("CLONE_NEWIPC", u64::from(ns::CLONE_NEWIPC)),
        ("CLONE_NEWUSER", u64::from(ns::CLONE_NEWUSER)),
        ("CLONE_NEWPID", u64::from(ns::CLONE_NEWPID)),
        ("CLONE_NEWNET", u64::from(ns::CLONE_NEWNET)),
    ];
    for (name, ours) in table {
        check(&d, name, *ours)?;
    }
    // The "handled" sets are exactly the rights the header defines: every
    // LANDLOCK_ACCESS_FS_* define, ORed, equals the ABI 5 set.
    let fs_all = d
        .keys()
        .filter(|k| k.starts_with("LANDLOCK_ACCESS_FS_"))
        .try_fold(0u64, |acc, k| eval(k, &d).map(|v| acc | v))?;
    assert_eq!(fs_all, ll::FS_ABI_5);
    let net_all = d
        .keys()
        .filter(|k| k.starts_with("LANDLOCK_ACCESS_NET_"))
        .try_fold(0u64, |acc, k| eval(k, &d).map(|v| acc | v))?;
    assert_eq!(net_all, ll::NET_ABI_4);
    let scope_all = d
        .keys()
        .filter(|k| k.starts_with("LANDLOCK_SCOPE_"))
        .try_fold(0u64, |acc, k| eval(k, &d).map(|v| acc | v))?;
    assert_eq!(scope_all, ll::SCOPE_ABI_6);
    Ok(())
}

/// number of `name` in `syscall_64.tbl` (x86-64 ABIs `common` and `64`).
fn x86_64_number(table: &str, name: &str) -> Option<u32> {
    table.lines().find_map(|l| {
        let mut f = l.split_whitespace();
        let nr = f.next()?.parse().ok()?;
        let abi = f.next()?;
        let n = f.next()?;
        ((abi == "common" || abi == "64") && n == name).then_some(nr)
    })
}

/// number of `name` in the generic table (aarch64).
fn generic_number(defs: &HashMap<String, String>, name: &str) -> Result<u32, String> {
    let direct = format!("__NR_{name}");
    let wide = format!("__NR3264_{name}");
    let v = if defs.contains_key(&direct) && !is_alias(defs, &direct) {
        eval(&direct, defs)?
    } else {
        eval(&wide, defs)?
    };
    u32::try_from(v).map_err(|e| e.to_string())
}

/// `#define __NR_mmap __NR3264_mmap` is an alias, resolved through its target.
fn is_alias(defs: &HashMap<String, String>, name: &str) -> bool {
    defs.get(name).is_some_and(|v| v.starts_with("__NR3264_"))
}

#[test]
#[cfg_attr(miri, ignore)] // reads vendored files, which Miri's isolation forbids
fn allowlist_numbers_match_kernel_tables() -> Result<(), String> {
    let tbl = vendored("syscall_64.tbl")?;
    let generic = defines(&["unistd.h"])?;
    for s in syscalls::ALLOWLIST.iter().chain(syscalls::GPU_EXTRA) {
        let x86 = x86_64_number(&tbl, s.name)
            .ok_or_else(|| format!("{}: not in syscall_64.tbl", s.name))?;
        assert_eq!(s.x86_64, x86, "{} on x86-64", s.name);
        let a64 = generic_number(&generic, s.name)?;
        assert_eq!(s.aarch64, a64, "{} on aarch64", s.name);
    }
    Ok(())
}

#[test]
fn allowlist_has_no_duplicates_and_no_forbidden_names() {
    for arch in Arch::ALL {
        let mut nums = syscalls::numbers(arch);
        nums.sort_unstable();
        let n = nums.len();
        nums.dedup();
        assert_eq!(nums.len(), n, "duplicate number on {arch:?}");
    }
    let forbidden = [
        "open",
        "openat",
        "openat2",
        "creat",
        "socket",
        "socketpair",
        "connect",
        "accept",
        "accept4",
        "bind",
        "listen",
        "clone",
        "clone3",
        "fork",
        "vfork",
        "execve",
        "execveat",
        "ptrace",
        "prctl",
        "ioctl",
        "mount",
        "umount2",
        "unshare",
        "setns",
        "kill",
        "tgkill",
        "tkill",
        "seccomp",
        "bpf",
        "io_uring_setup",
        "perf_event_open",
        "sendmsg",
        "recvmsg",
        "rt_sigaction",
        "pipe",
        "pipe2",
        "dup",
        "dup2",
        "dup3",
        "fcntl",
        "mknod",
        "chroot",
        "pivot_root",
        "ptrace",
        "process_vm_readv",
        "process_vm_writev",
        "memfd_create",
        "userfaultfd",
        "landlock_create_ruleset",
        "landlock_restrict_self",
    ];
    for s in syscalls::ALLOWLIST {
        assert!(
            !forbidden.contains(&s.name),
            "{} must not be allowed",
            s.name
        );
        assert!(!s.reason.is_empty(), "{} has no reason", s.name);
    }
}

/// Item 5.21a: the GPU list has no duplicate, still nothing that opens, connects,
/// executes or changes the sandbox, and says of every addition that it is not
/// measured.
#[test]
fn gpu_list_has_no_duplicates_and_no_forbidden_names() {
    for arch in Arch::ALL {
        let mut nums = syscalls::gpu_numbers(arch);
        nums.sort_unstable();
        let n = nums.len();
        nums.dedup();
        assert_eq!(nums.len(), n, "duplicate number on {arch:?}");
    }
    let forbidden = [
        "open",
        "openat",
        "openat2",
        "creat",
        "socket",
        "socketpair",
        "connect",
        "accept",
        "accept4",
        "bind",
        "listen",
        "fork",
        "vfork",
        "execve",
        "execveat",
        "ptrace",
        "prctl",
        "mount",
        "umount2",
        "unshare",
        "setns",
        "kill",
        "tgkill",
        "tkill",
        "seccomp",
        "bpf",
        "io_uring_setup",
        "perf_event_open",
        "rt_sigaction",
        "chroot",
        "pivot_root",
        "process_vm_readv",
        "process_vm_writev",
        "userfaultfd",
        "landlock_create_ruleset",
        "landlock_restrict_self",
    ];
    for s in syscalls::ALLOWLIST.iter().chain(syscalls::GPU_EXTRA) {
        assert!(
            !forbidden.contains(&s.name),
            "{} must not be allowed",
            s.name
        );
    }
    for s in syscalls::GPU_EXTRA {
        assert!(s.reason.starts_with("not measured: "), "{}", s.name);
    }
}

#[test]
#[cfg_attr(miri, ignore)] // reads vendored files, which Miri's isolation forbids
fn doc_sections_cited_exist() -> Result<(), String> {
    let seccomp = vendored("seccomp_filter.rst")?;
    for heading in ["Usage", "Return values", "Pitfalls"] {
        assert!(seccomp.lines().any(|l| l == heading), "{heading}");
    }
    assert!(seccomp.contains("Always check the arch value!"));
    let filter = vendored("filter.rst")?;
    assert!(filter.contains("BPF engine and instruction set"));
    assert!(filter.contains("op:16, jt:8, jf:8, k:32"));
    let landlock = vendored("landlock.rst")?;
    for heading in [
        "Landlock ABI versions",
        "File truncation (ABI < 3)",
        "TCP bind and connect (ABI < 4)",
        "Device IOCTL (ABI < 5)",
        "Abstract UNIX socket (ABI < 6)",
        "Signal (ABI < 6)",
    ] {
        assert!(landlock.lines().any(|l| l == heading), "{heading}");
    }
    Ok(())
}
