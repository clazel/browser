//! **Reads are confined** (A64): the part of the A64 confinement proof that
//! says a step's outcome depends only on the bytes of the read area.
//! `execute` reads memory only through [`mem_read`] at the access's address
//! (or decides a fault by whether the bytes of a store are mapped); the
//! lemmas below show that two memories that agree on those bytes give the same
//! outcome. [`lemma_reads_confined`] puts them together with the access facts
//! of the invariant.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The memories `m` and `m2` agree on the `n` bytes at `a`.
pub open spec fn same_bytes(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: int) -> bool {
    forall|x: int|
        a <= x < a + n ==> (#[trigger] m2.dom().contains(x) == m.dom().contains(x) && (
        m.dom().contains(x) ==> m2[x] == m[x]))
}

/// The bytes of a readable range lie in the positive canonical addresses and
/// are in the read area.
pub proof fn lemma_readable_range(c: Cfg, addr: int, n: int)
    requires
        cfg_ok(c),
        readable(c, addr, n),
    ensures
        0 <= addr,
        addr + n <= lim(),
        lim() < p2(64),
        forall|x: int| addr <= x < addr + n ==> #[trigger] read_area(c, x),
{
    lemma_cfg(c);
    lemma_p2();
    if c.ctx <= addr && addr + n <= c.ctx + abi::ctx_size() {
    } else {
        let k = choose|k: int|
            0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + n <= c.bases[k]
                + c.bounds[k];
        lemma_region(c, k);
        assert forall|x: int| addr <= x < addr + n implies #[trigger] read_area(c, x) by {
            assert(in_region(c, x, 1));
        }
    }
}

/// Agreement on the read area, at one byte of it.
pub proof fn lemma_agree_at(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>, x: int)
    requires
        agree_on_read_area(c, m, m2),
        read_area(c, x),
    ensures
        m2.dom().contains(x) == m.dom().contains(x),
        m.dom().contains(x) ==> m2[x] == m[x],
{
    assert(read_area(c, x) ==> (m2.dom().contains(x) == m.dom().contains(x) && (m.dom().contains(
        x,
    ) ==> m2[x] == m[x])));
}

/// Memories that agree on the read area agree on every range of it.
pub proof fn lemma_agree_bytes(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>, addr: int, n: int)
    requires
        agree_on_read_area(c, m, m2),
        forall|x: int| addr <= x < addr + n ==> #[trigger] read_area(c, x),
    ensures
        same_bytes(m, m2, addr, n),
{
    assert forall|x: int| addr <= x < addr + n implies (#[trigger] m2.dom().contains(x)
        == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
        assert(read_area(c, x));
        lemma_agree_at(c, m, m2, x);
    }
}

/// What is writable is readable.
pub proof fn lemma_writable_readable(c: Cfg, addr: int, n: int)
    requires
        writable(c, addr, n),
    ensures
        readable(c, addr, n),
{
}

/// The outcome of a general-register load or store is the same from two
/// memories that agree on its bytes.
pub proof fn lemma_lsg_same(
    s: State,
    m2: Map<int, u8>,
    load: bool,
    t: u8,
    ds: nat,
    address: int,
)
    requires
        0 <= address,
        address + ds / 8 <= p2(64),
        same_bytes(s.mem, m2, address, (ds / 8) as int),
    ensures
        same_outcome(
            load_store_gpr(s, load, t, ds, address),
            load_store_gpr(State { mem: m2, ..s }, load, t, ds, address),
        ),
{
    let s2 = State { mem: m2, ..s };
    if load {
        lemma_mem_read_same(s.mem, m2, address, ds / 8);
    } else {
        lemma_mem_set_some_same(
            s.mem,
            m2,
            address,
            ds / 8,
            x_read(s, t, ds),
        );
        assert(x_read(s2, t, ds) == x_read(s, t, ds));
    }
}

/// The outcome of a vector-register load or store is the same from two
/// memories that agree on its bytes.
pub proof fn lemma_lsf_same(s: State, m2: Map<int, u8>, load: bool, t: u8, address: int)
    requires
        0 <= address,
        address + 8 <= p2(64),
        same_bytes(s.mem, m2, address, 8),
    ensures
        same_outcome(
            load_store_fp(s, load, t, address),
            load_store_fp(State { mem: m2, ..s }, load, t, address),
        ),
{
    let s2 = State { mem: m2, ..s };
    if load {
        lemma_mem_read_same(s.mem, m2, address, 8);
    } else {
        lemma_mem_set_some_same(s.mem, m2, address, 8, v_read(s, t, 64));
        assert(v_read(s2, t, 64) == v_read(s, t, 64));
    }
}

/// `execute` of an instruction that makes no memory access does not depend on
/// memory, one lemma for each integer instruction (so that each is small).
pub proof fn lemma_exec_nomem_add_sub_reg(s: State, m2: Map<int, u8>, sf: Width, sub_op: bool, setflags: bool, d: u8, n: u8, m: u8, shift_type: ShiftType, shift_amount: u8)
    ensures
        same_outcome(
            execute(s, Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount }),
            execute(State { mem: m2, ..s }, Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount }),
        ),
{
}

pub proof fn lemma_exec_nomem_add_sub_imm(s: State, m2: Map<int, u8>, sf: Width, sub_op: bool, setflags: bool, d: u8, n: u8, imm12: u16, sh: bool)
    ensures
        same_outcome(
            execute(s, Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh }),
            execute(State { mem: m2, ..s }, Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh }),
        ),
{
}

pub proof fn lemma_exec_nomem_mul_add_sub(s: State, m2: Map<int, u8>, sf: Width, sub_op: bool, d: u8, n: u8, m: u8, a: u8)
    ensures
        same_outcome(
            execute(s, Instr::MulAddSub { sf, sub_op, d, n, m, a }),
            execute(State { mem: m2, ..s }, Instr::MulAddSub { sf, sub_op, d, n, m, a }),
        ),
{
}

pub proof fn lemma_exec_nomem_div(s: State, m2: Map<int, u8>, sf: Width, is_unsigned: bool, d: u8, n: u8, m: u8)
    ensures
        same_outcome(
            execute(s, Instr::Div { sf, is_unsigned, d, n, m }),
            execute(State { mem: m2, ..s }, Instr::Div { sf, is_unsigned, d, n, m }),
        ),
{
}

pub proof fn lemma_exec_nomem_logical(s: State, m2: Map<int, u8>, sf: Width, opc: LogicalOpc, d: u8, n: u8, m: u8, shift_type: ShiftType, shift_amount: u8)
    ensures
        same_outcome(
            execute(s, Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount }),
            execute(State { mem: m2, ..s }, Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount }),
        ),
{
}

pub proof fn lemma_exec_nomem_shift_var(s: State, m2: Map<int, u8>, sf: Width, shift_type: ShiftType, d: u8, n: u8, m: u8)
    ensures
        same_outcome(
            execute(s, Instr::ShiftVariable { sf, shift_type, d, n, m }),
            execute(State { mem: m2, ..s }, Instr::ShiftVariable { sf, shift_type, d, n, m }),
        ),
{
}

pub proof fn lemma_exec_nomem_move_wide(s: State, m2: Map<int, u8>, sf: Width, opcode: MoveWideOp, d: u8, imm16: u16, hw: u8)
    ensures
        same_outcome(
            execute(s, Instr::MoveWide { sf, opcode, d, imm16, hw }),
            execute(State { mem: m2, ..s }, Instr::MoveWide { sf, opcode, d, imm16, hw }),
        ),
{
}

pub proof fn lemma_exec_nomem_cond_select(s: State, m2: Map<int, u8>, sf: Width, else_inv: bool, else_inc: bool, d: u8, n: u8, m: u8, cond: u8)
    ensures
        same_outcome(
            execute(s, Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond }),
            execute(State { mem: m2, ..s }, Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond }),
        ),
{
}

/// [`lemma_exec_nomem_add_sub_reg`] and the others, for the integer instructions.
pub proof fn lemma_exec_nomem_int(s: State, m2: Map<int, u8>, i: Instr)
    requires
        i is AddSubShiftedReg || i is AddSubImm || i is MulAddSub || i is Div || i is
            LogicalShiftedReg || i is ShiftVariable || i is MoveWide || i is CondSelect,
    ensures
        same_outcome(execute(s, i), execute(State { mem: m2, ..s }, i)),
{
    match i {
        Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } => lemma_exec_nomem_add_sub_reg(s, m2, sf, sub_op, setflags, d, n, m, shift_type, shift_amount),
        Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } => lemma_exec_nomem_add_sub_imm(s, m2, sf, sub_op, setflags, d, n, imm12, sh),
        Instr::MulAddSub { sf, sub_op, d, n, m, a } => lemma_exec_nomem_mul_add_sub(s, m2, sf, sub_op, d, n, m, a),
        Instr::Div { sf, is_unsigned, d, n, m } => lemma_exec_nomem_div(s, m2, sf, is_unsigned, d, n, m),
        Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } => lemma_exec_nomem_logical(s, m2, sf, opc, d, n, m, shift_type, shift_amount),
        Instr::ShiftVariable { sf, shift_type, d, n, m } => lemma_exec_nomem_shift_var(s, m2, sf, shift_type, d, n, m),
        Instr::MoveWide { sf, opcode, d, imm16, hw } => lemma_exec_nomem_move_wide(s, m2, sf, opcode, d, imm16, hw),
        Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } => lemma_exec_nomem_cond_select(s, m2, sf, else_inv, else_inc, d, n, m, cond),
        _ => {},
    }
}

/// [`lemma_exec_nomem_int`] for `SBFM`/`UBFM`.
pub proof fn lemma_exec_nomem_bitfield(s: State, m2: Map<int, u8>, i: Instr)
    requires
        i is Bitfield,
    ensures
        same_outcome(execute(s, i), execute(State { mem: m2, ..s }, i)),
{
}

/// [`lemma_exec_nomem_int`] for the floating-point instructions.
pub proof fn lemma_exec_nomem_fp(s: State, m2: Map<int, u8>, i: Instr)
    requires
        i is FAddSub || i is FMul || i is FDiv || i is FUnary || i is FCmp || i is FMovGen || i is
            Scvtf || i is Fcvtzs,
    ensures
        same_outcome(execute(s, i), execute(State { mem: m2, ..s }, i)),
{
    match i {
        Instr::FAddSub { .. } => {},
        Instr::FMul { .. } => {},
        Instr::FDiv { .. } => {},
        Instr::FUnary { .. } => {},
        Instr::FCmp { .. } => {},
        Instr::FMovGen { .. } => {},
        Instr::Scvtf { .. } => {},
        Instr::Fcvtzs { .. } => {},
        _ => {},
    }
}

/// `execute` of an instruction that makes no memory access does not depend on
/// memory.
pub proof fn lemma_exec_nomem(s: State, m2: Map<int, u8>, i: Instr)
    requires
        mem_access(i) is None,
    ensures
        same_outcome(execute(s, i), execute(State { mem: m2, ..s }, i)),
{
    match i {
        Instr::Bitfield { .. } => lemma_exec_nomem_bitfield(s, m2, i),
        Instr::LoadStoreImm { .. } => {
            assert(false);
        },
        Instr::LoadStoreReg { .. } => {
            assert(false);
        },
        Instr::FpLoadStoreImm { .. } => {
            assert(false);
        },
        Instr::FpLoadStoreReg { .. } => {
            assert(false);
        },
        Instr::B { .. } => {},
        Instr::BCond { .. } => {},
        Instr::CompareBranch { .. } => {},
        Instr::Ret => {},
        Instr::FAddSub { .. } | Instr::FMul { .. } | Instr::FDiv { .. } | Instr::FUnary { .. }
        | Instr::FCmp { .. } | Instr::FMovGen { .. } | Instr::Scvtf { .. } | Instr::Fcvtzs { .. } =>
            lemma_exec_nomem_fp(s, m2, i),
        _ => lemma_exec_nomem_int(s, m2, i),
    }
}

/// `branch_to` keeps agreement apart from memory.
pub proof fn lemma_branch_same(o: Option<State>, o2: Option<State>, target: int)
    requires
        same_outcome(o, o2),
    ensures
        same_outcome(
            match o {
                Some(s1) => Some(branch_to(s1, target)),
                None => None,
            },
            match o2 {
                Some(s1) => Some(branch_to(s1, target)),
                None => None,
            },
        ),
{
}

/// **Reads are confined**: for a valid instruction whose accesses are
/// permitted, the step's outcome (apart from memory) is the same from every
/// memory that agrees with the state's on the read area.
pub proof fn lemma_reads_confined(c: Cfg, s: State, i: Instr)
    requires
        cfg_ok(c),
        valid_instr(i),
        loads_ok(c, s, i),
        stores_ok(c, s, i),
    ensures
        reads_confined(c, s, i),
{
    assert forall|m2: Map<int, u8>| agree_on_read_area(c, s.mem, m2) implies #[trigger] same_outcome(
        step(s, i),
        step(State { mem: m2, ..s }, i),
    ) by {
        let s2 = State { mem: m2, ..s };
        match mem_access(i) {
            None => {
                lemma_exec_nomem(s, m2, i);
                match i {
                    Instr::B { .. } => {},
                    Instr::BCond { .. } => {},
                    Instr::CompareBranch { .. } => {},
                    Instr::Ret => {},
                    _ => {
                        lemma_branch_same(
                            execute(s, i),
                            execute(s2, i),
                            s.pc as int + 4,
                        );
                    },
                }
            },
            Some(a) => {
                let addr = eff_addr(s, a);
                assert(eff_addr(s2, a) == addr);
                if a.store {
                    lemma_writable_readable(c, addr, a.size);
                }
                lemma_readable_range(c, addr, a.size);
                lemma_agree_bytes(c, s.mem, m2, addr, a.size);
                match i {
                    Instr::LoadStoreImm { sf, load, t, n, imm12 } => {
                        lemma_lsg_same(s, m2, load, t, datasize(sf), addr);
                        lemma_branch_same(execute(s, i), execute(s2, i), s.pc as int + 4);
                    },
                    Instr::LoadStoreReg { sf, load, t, n, m, s: sbit } => {
                        lemma_lsg_same(s, m2, load, t, datasize(sf), addr);
                        lemma_branch_same(execute(s, i), execute(s2, i), s.pc as int + 4);
                    },
                    Instr::FpLoadStoreImm { load, t, n, imm12 } => {
                        lemma_lsf_same(s, m2, load, t, addr);
                        lemma_branch_same(execute(s, i), execute(s2, i), s.pc as int + 4);
                    },
                    Instr::FpLoadStoreReg { load, t, n, m, s: sbit } => {
                        lemma_lsf_same(s, m2, load, t, addr);
                        lemma_branch_same(execute(s, i), execute(s2, i), s.pc as int + 4);
                    },
                    _ => {
                        assert(false);
                    },
                }
            },
        }
    }
}

} // verus!
