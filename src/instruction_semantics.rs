// Instruction semantics definitions
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// Constant bits (eg imm8)
    Const {
        value: u64,
        width: u16
    },

    Operand(OperandRef),

    DerivedValue(ValueName),

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
pub struct ValueName(pub String);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FieldName(pub String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperandRef {
    RegisterField(RegisterRef),
    ImmediateField(FieldName),
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Effect {
    WriteRegister {
        guard: Expr,
        register: Expr,
        value: Expr,
    },

    WriteMemory {
        guard: Expr,
        address: Expr,
        value: Expr,
        width: u16,
    },
}

impl Effect {
    pub fn write_register(register: Expr, value: Expr) -> Self {
        Self::WriteRegister { guard: bool_const(true), register, value }
    }

    pub fn write_register_if(guard: Expr, register: Expr, value: Expr) -> Self {
        Self::WriteRegister { guard, register, value }
    }

    pub fn write_memory(address: Expr, value: Expr, width: u16) -> Self {
        Self::WriteMemory { guard: bool_const(true), address, value, width }
    }

    pub fn write_memory_if(guard: Expr, address: Expr, value: Expr, width: u16) -> Self {
        Self::WriteMemory { guard, address, value, width }
    }
}

pub fn field_name(name: &str) -> FieldName {
    FieldName(name.to_owned())
}

pub fn constant(value: u64, width: u16) -> Expr {
    Expr::Const { value, width }
}

pub fn bool_const(value: bool) -> Expr {
    constant(value as u64, 1)
}

pub fn immediate_field(name: &str) -> Expr {
    Expr::Operand(OperandRef::ImmediateField(field_name(name)))
}

/// Produces an expression representing the register number contained in
/// an instruction field. It does not read that register.
pub fn register_field(name: &str) -> Expr {
    Expr::Operand(OperandRef::RegisterField(
        RegisterRef::FromField(field_name(name)),
    ))
}

/// Produces an expression representing a fixed architectural or virtual register.
pub fn fixed_register(register: Register, width: u16) -> Expr {
    Expr::Operand(OperandRef::RegisterField(
        RegisterRef::Fixed { register, width },
    ))
}

pub fn read_register(register: Expr) -> Expr {
    Expr::ReadRegister(Box::new(register))
}

pub fn read_register_field(name: &str) -> Expr {
    read_register(register_field(name))
}

pub fn read_fixed_register(register: Register, width: u16) -> Expr {
    read_register(fixed_register(register, width))
}

pub fn equal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Equal(Box::new(lhs), Box::new(rhs))
}

pub fn and_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::And(Box::new(lhs), Box::new(rhs))
}

pub fn or_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Or(Box::new(lhs), Box::new(rhs))
}

pub fn not_expr(value: Expr) -> Expr {
    Expr::Not(Box::new(value))
}

pub fn select(condition: Expr, when_true: Expr, when_false: Expr) -> Expr {
    Expr::Select {
        condition: Box::new(condition),
        when_true: Box::new(when_true),
        when_false: Box::new(when_false),
    }
}

pub fn field_is(name: &str, value: u64, width: u16) -> Expr {
    equal(immediate_field(name), constant(value, width))
}