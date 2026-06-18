// Instruction semantics definitions
#[derive(Clone, Debug)]
pub enum Expr {
    /// Constant bits (eg imm8)
    Const {
        value: u64,
        width: u16
    },

    Operand(OperandRef),

    ReadRegister(Box<Expr>),
    ReadMemory {
        address: Box<Expr>,
        width: u16,
    },

    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),

    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Xor(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),

    ShiftLeft(Box<Expr>, Box<Expr>),
    LogicalShiftRight(Box<Expr>, Box<Expr>),
    ArithmeticShiftRight(Box<Expr>, Box<Expr>),

    Equal(Box<Expr>, Box<Expr>),
    UnsignedLessThan(Box<Expr>, Box<Expr>),
    SignedLessThan(Box<Expr>, Box<Expr>),

    Extract {
        value: Box<Expr>,
        high: u16,
        low: u16,
    },

    Concat(Vec<Expr>),

    ZeroExtend {
        value: Box<Expr>,
        to_width: u16,
    },

    SignExtend {
        value: Box<Expr>,
        to_width: u16,
    },

    Select {
        condition: Box<Expr>,
        when_true: Box<Expr>,
        when_false: Box<Expr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FieldName(pub String);

#[derive(Clone, Debug)]
pub enum OperandRef {
    RegisterField(RegisterRef),
    ImmediateField(FieldName),
}

#[derive(Clone, Debug)]
pub enum RegisterRef {
    Fixed { register: Register, width: u16 },
    FromField(FieldName)
}

/// Register struct which defines enumerated fixed registers
/// This does not necessarily need to match with the exact ISA definition of registers
/// For example, for an ISA with only 16 general purpose registers, you may still choose to define Register(20)
/// if there is some value stored in state that needs to be stored.
/// This should be used for ALL state that isn't memory (including eg flags).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Register(pub u8);

/// Effect of an instruction
/// Every effect is either on a register or memory
/// This is sufficient to encapsulate the whole system because you can effectively create
/// "virtual" register addresses
/// For example, while ARM, in reality, only has r0-r15, it also has the NZCV flags.
/// The behavior of these can be modeled by saying that the register with FieldId = 16 is eg the negative flag
#[derive(Clone, Debug)]
pub enum Effect {
    WriteRegister {
        register: Expr,
        value: Expr,
    },

    WriteMemory {
        address: Expr,
        value: Expr,
        width: u16,
    },
}

pub struct Semantics {
    pub effects: Vec<Effect>
}