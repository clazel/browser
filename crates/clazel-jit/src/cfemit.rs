//! The executable back end for **structured control flow, memory
//! instructions and `br_table`** (x86-64): [`emit_cf_blob`].
//!
//! **This code is not proven.** [`crate::cfcontract::emit_cf_blob_ensures`]
//! says what it must satisfy: the code it emits is [`crate::cftemplates::ctmpl`],
//! which `crate::cfproofs::lemma_ctmpl_refines` proves refines the program.
//! The equality of this emitter to `ctmpl` is checked by the tests
//! (`tests/validator_cf.rs`: the validator accepts every blob, and the
//! emitter's analysis and sizes agree with the code it emits), and is not a
//! theorem: Verus has no spec for the signed `checked_*` operators or for
//! `i32::try_from(i64)`, and a proof over the `usize` forms was not finished.
//! The code mirrors [`ctmpl`](crate::cftemplates::ctmpl) arm by arm.
//!
//! # Labels
//!
//! A label is an absolute byte position in the body (`labs`, label 0 first).
//! A jump that ends at position `end` to the label at `target` has
//! displacement `target - end`, computed in `i64` with `checked_sub` and
//! narrowed with `i32::try_from` ([`rel32`]), so no operation can wrap and
//! the workspace's `arithmetic_side_effects` lint holds with no `#[allow]`.
//! The program's size is at most [`MAX_SIZE`] (the spec's `max_size`), so
//! every displacement fits; if one did not the emitter would refuse.

use crate::cfspec::{MTy, MemOp, Node};
use crate::emit::{emit_op, op_ok_exec, pops_exec, pushes_exec};
use clazel_x64::encoder::encode_exec;
use clazel_x64::spec::{AluOp, Index, Instr, Mem, Size};

/// The largest body this emitter translates, in bytes (the spec's
/// `cftemplates::max_size`).
pub const MAX_SIZE: usize = 0x2000_0000;

/// The frame's slots (the spec's `max_slots`).
const SLOTS: usize = 31;

/// `trap_code`: the exit code of the bounds check in a `load` or `store`.
const TRAP: u32 = 0xFFFF_FFFF;

/// The most targets of a `br_table` (the spec's `max_targets`).
const MAX_TARGETS: usize = 0x10000;

/// What the analysis says about the end of a node (the spec's `Flow`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Flow {
    /// It can fall through at this stack height.
    Falls(usize),
    /// It always branches or exits.
    Dead,
}

/// The displacement from a jump that ends at `end` to `target`, if it fits a
/// `rel32`.
fn rel32(target: usize, end: usize) -> Option<i32> {
    let t = i64::try_from(target).ok()?;
    let e = i64::try_from(end).ok()?;
    let d = t.checked_sub(e)?;
    i32::try_from(d).ok()
}

/// The length in bytes of the encodings of `code` (saturating).
fn code_bytes(code: &[Instr]) -> usize {
    code.iter()
        .fold(0usize, |a, i| a.saturating_add(encode_exec(i).len()))
}

/// `mov dst, [r15 + 264 + 8 j]`.
fn load_slot(dst: u8, j: usize) -> Option<Instr> {
    let d = i32::try_from(j.checked_mul(8)?.checked_add(264)?).ok()?;
    Some(Instr::MovLoad {
        sz: Size::W64,
        dst,
        mem: Mem {
            base: 15,
            index: None,
            disp: d,
        },
    })
}

/// `mov [r15 + 264 + 8 j], src`.
fn store_slot(j: usize, src: u8) -> Option<Instr> {
    let d = i32::try_from(j.checked_mul(8)?.checked_add(264)?).ok()?;
    Some(Instr::MovStore {
        sz: Size::W64,
        mem: Mem {
            base: 15,
            index: None,
            disp: d,
        },
        src,
    })
}

/// The exit sequence for `c`.
fn exit_seq(c: u32) -> Vec<Instr> {
    vec![
        Instr::MovImm32 { dst: 0, imm_u32: c },
        Instr::MovStore {
            sz: Size::W64,
            mem: Mem {
                base: 15,
                index: None,
                disp: 256,
            },
            src: 0,
        },
        Instr::Ret,
    ]
}

/// `[rsi + rcx]`.
fn ix_mem() -> Mem {
    Mem {
        base: 6,
        index: Some(Index { reg: 1, scale: 0 }),
        disp: 0,
    }
}

/// The operand size of an access.
fn mty_sz(ty: &MTy) -> Size {
    match ty {
        MTy::I32 => Size::W32,
        MTy::I64 | MTy::F64 => Size::W64,
    }
}

/// The number of bytes of an access.
fn mty_size(ty: &MTy) -> usize {
    match ty {
        MTy::I32 => 4,
        MTy::I64 | MTy::F64 => 8,
    }
}

/// The code of a memory instruction: the operands, the validator's bounds
/// check, the access, a `jmp` over the stub, the stub.
fn mem_code(m: &MemOp, nl: usize, h: usize) -> Option<Vec<Instr>> {
    let top = nl.checked_add(h)?.checked_sub(1)?;
    let (region, n, pre, tail, exit_code): (usize, usize, Vec<Instr>, Vec<Instr>, u32) = match m {
        MemOp::BoundsCheck { region, size, code } => {
            (*region, *size, vec![load_slot(1, top)?], Vec::new(), *code)
        }
        MemOp::Load { region, ty } => (
            *region,
            mty_size(ty),
            vec![
                load_slot(1, top)?,
                Instr::MovLoad {
                    sz: Size::W64,
                    dst: 6,
                    mem: base_mem(*region)?,
                },
            ],
            vec![
                Instr::MovLoad {
                    sz: mty_sz(ty),
                    dst: 0,
                    mem: ix_mem(),
                },
                store_slot(top, 0)?,
            ],
            TRAP,
        ),
        MemOp::Store { region, ty } => (
            *region,
            mty_size(ty),
            vec![
                load_slot(7, top)?,
                load_slot(1, top.checked_sub(1)?)?,
                Instr::MovLoad {
                    sz: Size::W64,
                    dst: 6,
                    mem: base_mem(*region)?,
                },
            ],
            vec![Instr::MovStore {
                sz: mty_sz(ty),
                mem: ix_mem(),
                src: 7,
            }],
            TRAP,
        ),
    };
    let stub = exit_seq(exit_code);
    let tail_len = code_bytes(&tail);
    // From the first exit: the check's instructions 3 to 7 (31 bytes), the
    // tail and the jmp; from the second: instructions 5 to 7 (17 bytes).
    let r1 = i32::try_from(tail_len.checked_add(31)?.checked_add(5)?).ok()?;
    let r2 = i32::try_from(tail_len.checked_add(17)?.checked_add(5)?).ok()?;
    let bound_disp = i32::try_from(region.checked_mul(16)?.checked_add(8)?).ok()?;
    let bound = || Mem {
        base: 15,
        index: None,
        disp: bound_disp,
    };
    let mut out = pre;
    out.push(Instr::MovRR {
        sz: Size::W64,
        dst: 2,
        src: 1,
    });
    out.push(Instr::AluRI {
        alu: AluOp::Add,
        sz: Size::W64,
        dst: 2,
        imm: i32::try_from(n).ok()?,
    });
    out.push(Instr::Jcc { cc: 2, rel: r1 });
    out.push(Instr::AluRM {
        alu: AluOp::Cmp,
        sz: Size::W64,
        dst: 2,
        mem: bound(),
    });
    out.push(Instr::Jcc { cc: 7, rel: r2 });
    out.push(Instr::MovImm32 { dst: 0, imm_u32: 0 });
    out.push(Instr::AluRM {
        alu: AluOp::Cmp,
        sz: Size::W64,
        dst: 1,
        mem: bound(),
    });
    out.push(Instr::Cmovcc {
        cc: 3,
        sz: Size::W64,
        dst: 1,
        src: 0,
    });
    out.extend(tail);
    out.push(Instr::Jmp {
        rel: i32::try_from(code_bytes(&stub)).ok()?,
    });
    out.extend(stub);
    Some(out)
}

/// `[r15 + 16 k]`: region `k`'s base.
fn base_mem(k: usize) -> Option<Mem> {
    Some(Mem {
        base: 15,
        index: None,
        disp: i32::try_from(k.checked_mul(16)?).ok()?,
    })
}

/// The condition test, `mov rax, [top]; test eax, eax; jcc cc rel`.
fn cond_pre(nl: usize, h: usize, cc: u8, rel: i32) -> Option<Vec<Instr>> {
    let top = nl.checked_add(h)?.checked_sub(1)?;
    Some(vec![
        load_slot(0, top)?,
        Instr::TestRR {
            sz: Size::W32,
            a: 0,
            b: 0,
        },
        Instr::Jcc { cc, rel },
    ])
}

/// The length of the condition test (it does not depend on the jump).
fn cond_len(nl: usize, h: usize) -> Option<usize> {
    Some(code_bytes(&cond_pre(nl, h, 0, 0)?))
}

/// The code of `br_table ls d` at absolute position `start`.
fn brt_code(
    ls: &[usize],
    d: usize,
    nl: usize,
    h: usize,
    start: usize,
    labs: &[usize],
) -> Option<Vec<Instr>> {
    let top = nl.checked_add(h)?.checked_sub(1)?;
    let first = load_slot(0, top)?;
    let p0 = code_bytes(std::slice::from_ref(&first));
    let mut out = vec![first];
    let mut end = start.checked_add(p0)?;
    for (i, l) in ls.iter().enumerate() {
        let entry = [
            Instr::MovImm32 {
                dst: 2,
                imm_u32: u32::try_from(i).ok()?,
            },
            Instr::AluRR {
                alu: AluOp::Cmp,
                sz: Size::W32,
                dst: 0,
                src: 2,
            },
            Instr::Jcc { cc: 4, rel: 0 },
        ];
        end = end.checked_add(code_bytes(&entry))?;
        let rel = rel32(*labs.get(*l)?, end)?;
        let [a, b, _] = entry;
        out.push(a);
        out.push(b);
        out.push(Instr::Jcc { cc: 4, rel });
    }
    end = end.checked_add(5)?;
    out.push(Instr::Jmp {
        rel: rel32(*labs.get(d)?, end)?,
    });
    Some(out)
}

/// The code of a leaf node (no sub-node), at absolute position `start`.
fn leaf_code(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize]) -> Option<Vec<Instr>> {
    match n {
        crate::cfspec::Node::Op(o) => {
            let mut v = Vec::new();
            emit_op(o, nl, h, &mut v);
            Some(v)
        }
        crate::cfspec::Node::Mem(m) => mem_code(m, nl, h),
        crate::cfspec::Node::Br(l) => Some(vec![Instr::Jmp {
            rel: rel32(*labs.get(*l)?, start.checked_add(5)?)?,
        }]),
        crate::cfspec::Node::BrIf(l) => {
            let p = cond_len(nl, h)?;
            cond_pre(nl, h, 5, rel32(*labs.get(*l)?, start.checked_add(p)?)?)
        }
        crate::cfspec::Node::BrTable(ls, d) => brt_code(ls, *d, nl, h, start, labs),
        crate::cfspec::Node::Exit(c, _) => Some(exit_seq(*c)),
        _ => None,
    }
}

/// The analysis of `n` (the spec's `cf_flow`), entered at height `h` with
/// `nl` locals and `depth` labels in scope, and the size of its code in bytes
/// (the spec's `csize`). `None` if it has no translation, or is larger than
/// [`MAX_SIZE`].
fn analyze(n: &Node, nl: usize, h: usize, depth: usize) -> Option<(Flow, usize)> {
    let room = nl.checked_add(h)? <= SLOTS;
    match n {
        Node::Op(o) => {
            if !op_ok_exec(o, nl, h) {
                return None;
            }
            let h2 = h.checked_sub(pops_exec(o))?.checked_add(pushes_exec(o))?;
            let zeros = vec![0usize; depth];
            let size = code_bytes(&leaf_code(n, nl, h, 0, &zeros)?);
            Some((Flow::Falls(h2), size))
        }
        Node::Mem(m) => {
            let ok = room
                && match m {
                    MemOp::BoundsCheck { region, size, .. } => {
                        h >= 1 && *region < 16 && (1..=8).contains(size)
                    }
                    MemOp::Load { region, .. } => h >= 1 && *region < 16,
                    MemOp::Store { region, .. } => h >= 2 && *region < 16,
                };
            if !ok {
                return None;
            }
            let h2 = match m {
                MemOp::Store { .. } => h.checked_sub(2)?,
                _ => h,
            };
            let size = code_bytes(&mem_code(m, nl, h)?);
            Some((Flow::Falls(h2), size))
        }
        Node::Then(a, b) => {
            let (fa, sa) = analyze(a, nl, h, depth)?;
            match fa {
                Flow::Falls(h1) => {
                    let (fb, sb) = analyze(b, nl, h1, depth)?;
                    let s = sa.checked_add(sb)?;
                    (s <= MAX_SIZE).then_some((fb, s))
                }
                Flow::Dead => match &**b {
                    Node::Op(crate::spec::Op::Nop) => Some((Flow::Dead, sa)),
                    _ => None,
                },
            }
        }
        Node::Block(b) | Node::Loop(b) => {
            let (fb, sb) = analyze(b, nl, h, depth.checked_add(1)?)?;
            match fb {
                Flow::Falls(h1) if h1 != h => None,
                _ => Some((Flow::Falls(h), sb)),
            }
        }
        Node::If(t, e) => {
            if h < 1 || !room {
                return None;
            }
            let h1 = h.checked_sub(1)?;
            let (ft, st) = analyze(t, nl, h1, depth.checked_add(1)?)?;
            let (fe, se) = analyze(e, nl, h1, depth.checked_add(1)?)?;
            let fits = |f: Flow| match f {
                Flow::Falls(x) => x == h1,
                Flow::Dead => true,
            };
            if !fits(ft) || !fits(fe) {
                return None;
            }
            let s = cond_len(nl, h)?
                .checked_add(st)?
                .checked_add(5)?
                .checked_add(se)?;
            (s <= MAX_SIZE).then_some((Flow::Falls(h1), s))
        }
        Node::Br(l) => (*l < depth).then_some((Flow::Dead, 5)),
        Node::BrIf(l) => {
            if *l < depth && h >= 1 && room {
                let size = cond_len(nl, h)?;
                Some((Flow::Falls(h.checked_sub(1)?), size))
            } else {
                None
            }
        }
        Node::BrTable(ls, d) => {
            if *d < depth
                && h >= 1
                && room
                && ls.len() <= MAX_TARGETS
                && ls.iter().all(|l| *l < depth)
            {
                let zeros = vec![0usize; depth];
                let size = code_bytes(&leaf_code(n, nl, h, 0, &zeros)?);
                Some((Flow::Dead, size))
            } else {
                None
            }
        }
        Node::Exit(_, k) => {
            if *k <= h && room {
                Some((Flow::Dead, code_bytes(&exit_seq(0))))
            } else {
                None
            }
        }
    }
}

/// `new` followed by `labs`.
fn push_label(new: usize, labs: &[usize]) -> Vec<usize> {
    let mut v = Vec::with_capacity(labs.len().saturating_add(1));
    v.push(new);
    v.extend_from_slice(labs);
    v
}

/// Append the code of `n` (already analysed) at absolute position `start`,
/// with the labels in scope at the absolute positions `labs`; the size of
/// the code and the flow are returned.
fn emit_node(
    n: &Node,
    nl: usize,
    h: usize,
    start: usize,
    labs: &[usize],
    out: &mut Vec<Instr>,
) -> Option<(Flow, usize)> {
    let depth = labs.len();
    let (flow, size) = analyze(n, nl, h, depth)?;
    match n {
        Node::Then(a, b) => {
            let (fa, sa) = emit_node(a, nl, h, start, labs, out)?;
            if let Flow::Falls(h1) = fa {
                emit_node(b, nl, h1, start.checked_add(sa)?, labs, out)?;
            }
        }
        Node::Block(b) => {
            let (_, sb) = analyze(b, nl, h, depth.checked_add(1)?)?;
            let l = push_label(start.checked_add(sb)?, labs);
            emit_node(b, nl, h, start, &l, out)?;
        }
        Node::Loop(b) => {
            let l = push_label(start, labs);
            emit_node(b, nl, h, start, &l, out)?;
        }
        Node::If(t, e) => {
            let h1 = h.checked_sub(1)?;
            let p = cond_len(nl, h)?;
            let (_, st) = analyze(t, nl, h1, depth.checked_add(1)?)?;
            let (_, se) = analyze(e, nl, h1, depth.checked_add(1)?)?;
            let end = start
                .checked_add(p)?
                .checked_add(st)?
                .checked_add(5)?
                .checked_add(se)?;
            let l = push_label(end, labs);
            let skip = i32::try_from(st.checked_add(5)?).ok()?;
            out.extend(cond_pre(nl, h, 4, skip)?);
            let tstart = start.checked_add(p)?;
            emit_node(t, nl, h1, tstart, &l, out)?;
            out.push(Instr::Jmp {
                rel: i32::try_from(se).ok()?,
            });
            let estart = tstart.checked_add(st)?.checked_add(5)?;
            emit_node(e, nl, h1, estart, &l, out)?;
        }
        _ => {
            out.extend(leaf_code(n, nl, h, start, labs)?);
        }
    }
    Some((flow, size))
}

/// Emit the body of the function `n` with `nl` locals as encoded bytes,
/// followed by the exit sequence for `exit_code`. The function's return label
/// (a `br` to it, and falling off the end) is the exit sequence. `None` if the
/// program has no translation.
pub fn emit_cf_blob(n: &Node, nl: usize, exit_code: u32) -> Option<Vec<u8>> {
    if nl > SLOTS {
        return None;
    }
    let (_, size) = analyze(n, nl, 0, 1)?;
    if size > MAX_SIZE {
        return None;
    }
    let mut body: Vec<Instr> = Vec::new();
    let labs = [size];
    let (_, emitted) = emit_node(n, nl, 0, 0, &labs, &mut body)?;
    // the sizes the analysis computed are the sizes of the code emitted
    if emitted != size || code_bytes(&body) != size {
        return None;
    }
    body.extend(exit_seq(exit_code));
    let mut bytes = Vec::new();
    for i in &body {
        bytes.extend_from_slice(&encode_exec(i));
    }
    Some(bytes)
}
