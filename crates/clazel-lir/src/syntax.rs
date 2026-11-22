//! LIR's abstract syntax (docs/phases/jit.md item J.5): types, values and
//! instructions. Meaning is in [`crate::spec`], typing in [`crate::typing`].
//!
//! The syntax mirrors WebAssembly's structured instruction set (Wasm core
//! specification 2.0, §2.4 "Instructions" and §2.3 "Types"), restricted to
//! what the JIT needs, with LIR's own additions: regions and `bounds_check`
//! (jit.md, "Regions are the only memory") and `exit` (jit.md, "Generated
//! code never calls anything").

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A region number: an index into the layout (the table of (base, bound)
/// pairs the blob is entered with).
pub type RegionId = nat;

/// A value type. Wasm core §2.3.1 "Number Types" has `i32`, `i64`, `f32`,
/// `f64`; LIR has no `f32` (see the crate docs).
pub enum Ty {
    /// `i32`.
    I32,
    /// `i64`.
    I64,
    /// `f64`.
    F64,
    /// **LIR's addition, not in Wasm.** An `i64` that has been bounds-checked
    /// for `size` bytes of `region`: its value `i` satisfies
    /// `i + size <= bound(region)`. Only `bounds_check` makes one, and
    /// `load` and `store` take only this type, so an access without a
    /// check does not type. It is a subtype of `i64`, and of `Idx` of the
    /// same region with a smaller size.
    Idx(RegionId, nat),
}

/// A runtime value. Wasm core §4.2.1 "Values" (`i32.const`, `i64.const`,
/// `f64.const`). An `f64` is its IEEE 754 bit pattern, so NaN payloads are
/// kept (§4.3.3.1).
pub enum Val {
    /// An `i32`: 32 bits, no signedness.
    I32(u32),
    /// An `i64`.
    I64(u64),
    /// An `f64`, as bits.
    F64(u64),
}

/// A block type with parameters. Wasm core §2.4.8 "Control Instructions"
/// (`blocktype`), in its general form `[t1*] -> [t2*]` (the 2.0 spec allows a
/// type index; we write the function type inline).
pub struct BlockType {
    /// The values the block consumes.
    pub params: Seq<Ty>,
    /// The values the block leaves.
    pub results: Seq<Ty>,
}

/// Integer binary operators, for `i32` and `i64` alike. Wasm core §2.4.1
/// "Numeric Instructions", `ibinop`. LIR omits `div` and `rem`, which trap
/// in Wasm; the JIT does not need them yet.
pub enum IBin {
    /// `add`.
    Add,
    /// `sub`.
    Sub,
    /// `mul`.
    Mul,
    /// `and`.
    And,
    /// `or`.
    Or,
    /// `xor`.
    Xor,
    /// `shl`.
    Shl,
    /// `shr_s`.
    ShrS,
    /// `shr_u`.
    ShrU,
    /// `rotl`.
    Rotl,
    /// `rotr`.
    Rotr,
}

/// Integer comparisons (`irelop`, giving an `i32`).
pub enum ICmp {
    /// `eq`.
    Eq,
    /// `ne`.
    Ne,
    /// `lt_s`.
    LtS,
    /// `lt_u`.
    LtU,
    /// `gt_s`.
    GtS,
    /// `gt_u`.
    GtU,
    /// `le_s`.
    LeS,
    /// `le_u`.
    LeU,
    /// `ge_s`.
    GeS,
    /// `ge_u`.
    GeU,
}

/// `f64` binary operators (`fbinop`). LIR omits `min`, `max`, `copysign`.
pub enum FBin {
    /// `add`.
    Add,
    /// `sub`.
    Sub,
    /// `mul`.
    Mul,
    /// `div`.
    Div,
}

/// `f64` comparisons (`frelop`, giving an `i32`).
pub enum FCmp {
    /// `eq`.
    Eq,
    /// `ne`.
    Ne,
    /// `lt`.
    Lt,
    /// `gt`.
    Gt,
    /// `le`.
    Le,
    /// `ge`.
    Ge,
}

/// A binary numeric operator: two operands of one type, one result.
pub enum BinOp {
    /// An `i32` operator.
    I32(IBin),
    /// An `i64` operator.
    I64(IBin),
    /// An `i32` comparison.
    I32Cmp(ICmp),
    /// An `i64` comparison.
    I64Cmp(ICmp),
    /// An `f64` operator.
    F64(FBin),
    /// An `f64` comparison.
    F64Cmp(FCmp),
}

/// A unary numeric operator: Wasm core §2.4.1 `testop` (`eqz`), `funop`
/// (`neg`, `abs`, `sqrt`) and `cvtop` (conversions).
pub enum UnOp {
    /// `i32.eqz`.
    I32Eqz,
    /// `i64.eqz`.
    I64Eqz,
    /// `f64.neg`.
    F64Neg,
    /// `f64.abs`.
    F64Abs,
    /// `f64.sqrt`.
    F64Sqrt,
    /// `i32.wrap_i64`.
    I32WrapI64,
    /// `i64.extend_i32_s`.
    I64ExtendI32S,
    /// `i64.extend_i32_u`.
    I64ExtendI32U,
    /// `f64.convert_i32_s`.
    F64ConvertI32S,
    /// `f64.convert_i32_u`.
    F64ConvertI32U,
    /// `f64.convert_i64_s`.
    F64ConvertI64S,
    /// `f64.convert_i64_u`.
    F64ConvertI64U,
    /// `f64.reinterpret_i64`.
    F64ReinterpretI64,
    /// `i64.reinterpret_f64`.
    I64ReinterpretF64,
}

/// An instruction. Wasm core §2.4 "Instructions"; one recursive type, with
/// `Then` for sequencing (Wasm's `instr*`) and `Box`ed bodies for the
/// structured instructions.
///
/// There are no calls and no indirect branches (jit.md): every branch names
/// an enclosing label.
pub enum Instr {
    /// `nop`.
    Nop,
    /// Sequencing: `a`, then `b`.
    Then(Box<Instr>, Box<Instr>),
    /// `t.const`.
    Const(Val),
    /// `local.get x`.
    LocalGet(nat),
    /// `local.set x`.
    LocalSet(nat),
    /// `local.tee x`.
    LocalTee(nat),
    /// `drop`.
    Drop,
    /// `select` (the untyped form, restricted to operands of one type).
    Select,
    /// A numeric instruction with two operands.
    Bin(BinOp),
    /// A numeric instruction with one operand.
    Un(UnOp),
    /// **LIR's addition.** Pops an `i64` index `i`. If `i + size` is at most
    /// the bound of `region`, pushes `i`, now of type `Idx(region, size)`.
    /// Otherwise it is an exit with `code` and no operands: the bounds
    /// failure is a runtime service, not a trap.
    BoundsCheck {
        /// The region checked against.
        region: RegionId,
        /// The number of bytes the checked index must leave room for.
        size: nat,
        /// The exit code if the check fails.
        code: nat,
    },
    /// `t.load` from `region` (Wasm core §2.4.7 "Memory Instructions"), with
    /// no offset and no narrow forms. Takes an `Idx(region, size of ty)`.
    Load {
        /// The region read.
        region: RegionId,
        /// The type loaded.
        ty: Ty,
    },
    /// `t.store` to `region`. Takes an `Idx(region, size of ty)` and a value.
    Store {
        /// The region written.
        region: RegionId,
        /// The type stored.
        ty: Ty,
    },
    /// `block bt body end`.
    Block(BlockType, Box<Instr>),
    /// `loop bt body end`.
    Loop(BlockType, Box<Instr>),
    /// `if bt then else end`.
    If(BlockType, Box<Instr>, Box<Instr>),
    /// `br l`.
    Br(nat),
    /// `br_if l`.
    BrIf(nat),
    /// `br_table l* l_default`.
    BrTable(Seq<nat>, nat),
    /// **LIR's addition.** Stops the blob and returns to the enter stub with
    /// `code` and the top `operands.len()` values, whose types are given.
    Exit(nat, Seq<Ty>),
}

} // verus!
