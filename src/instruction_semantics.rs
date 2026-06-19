use std::collections::HashMap;

use crate::{
    instruction_semantics::OperandRef::{ImmediateField, RegisterField},
    isa_specification::{DecodedInstruction, DerivedValue},
};

/// Symbolic expression used to describe instruction semantics.
///
/// An `Expr` is not evaluated when an instruction is decoded. Instead, it is an
/// architecture-neutral expression tree that names the values an instruction
/// would read, compute, compare, and write. Instruction forms can bind
/// `DerivedValue`s such as `operand2` or `address`, and instruction effects can
/// refer to those derived values when describing register and memory updates.
///
/// Widths are intentionally carried by the leaves and by operations that change
/// width. Most operators are expected to be used on compatible bit-vector
/// widths. Boolean conditions are represented as 1-bit expressions where `1`
/// means true and `0` means false.
///
/// Importantly, all Exprs with multiple operands *must* have the same bit-width for all values
/// This will not necessarily be strictly enforced unless something evaluates to a Const, but it should
/// still be kept in mind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// Literal bit-vector value with an explicit width.
    ///
    /// `value` is interpreted modulo `2^width`; callers should pass values that
    /// fit in the requested width to keep semantics readable. This is used for
    /// immediate constants, fixed offsets, boolean literals, and masks.
    Const { value: u128, width: u16 },

    /// Value taken directly from the decoded instruction.
    ///
    /// Register operands represent register numbers, not register contents.
    /// Immediate operands represent the bit-vector stored in an instruction
    /// field. Use `ReadRegister` to turn a register-number operand into the
    /// current register value.
    Operand(OperandRef),

    /// Reference to a value computed by the matching instruction form.
    ///
    /// This lets several forms share one instruction-level effect. For example,
    /// ARM data-processing effects can use `operand2` while each form defines
    /// whether `operand2` came from an immediate, an immediate-shifted register,
    /// or a register-shifted register.
    DerivedValue(ValueName),

    /// Read the current value of a register.
    ///
    /// The inner expression evaluates to a register identifier, commonly an
    /// `Operand(RegisterField(_))` or a fixed virtual register. Register reads
    /// are part of the pre-instruction state; effects describe writes separately.
    ReadRegister(Box<Expr>),

    /// Read a bit-vector from memory.
    ///
    /// `address` is the byte address expression. `width` is the number of bits
    /// loaded from memory, such as 8, 16, 32, or 64. Endianness/alignment
    /// policies are intentionally left to the ISA specification that builds the
    /// expression.
    ReadMemory { address: Box<Expr>, width: u16 },

    /// Wrapping bit-vector addition.
    Add(Box<Expr>, Box<Expr>),

    /// Wrapping bit-vector subtraction.
    Sub(Box<Expr>, Box<Expr>),

    /// Bit-vector multiplication, producing the generic product of two numbers of width w,
    /// where the product also has width w. Importantly, that means if you want to
    /// multiply two 16 bit numbers to get a signed 32 bit number, you must sign extend
    /// both 16 bit numbers to 32 bits, or else the result of Expr::Mul will be assumed to be
    /// 16 bits. This is to avoid needing a separate signed and unsigned multiplication.
    ///
    /// ISA specs should explicitly `Extract`, `ZeroExtend`, or `SignExtend`
    /// around multiplication when a fixed architectural width matters.
    Mul(Box<Expr>, Box<Expr>),

    /// Bitwise AND. Also used for boolean conjunction on 1-bit expressions.
    And(Box<Expr>, Box<Expr>),

    /// Bitwise OR. Also used for boolean disjunction on 1-bit expressions.
    Or(Box<Expr>, Box<Expr>),

    /// Bitwise XOR. Also used for boolean inequality on 1-bit expressions.
    Xor(Box<Expr>, Box<Expr>),

    /// Bitwise NOT. On a 1-bit expression, this is boolean negation.
    Not(Box<Expr>),

    /// Logical left shift of a bit-vector by an unsigned shift amount.
    ShiftLeft(Box<Expr>, Box<Expr>),

    /// Logical right shift of a bit-vector by an unsigned shift amount.
    LogicalShiftRight(Box<Expr>, Box<Expr>),

    /// Arithmetic right shift of a signed bit-vector by an unsigned shift
    /// amount, preserving the input sign bit.
    ArithmeticShiftRight(Box<Expr>, Box<Expr>),

    /// Rotate a bit-vector right by an unsigned amount.
    ///
    /// The intended semantics are the usual bit-vector rotate: the amount is
    /// effectively taken modulo the width of the value being rotated.
    RotateRight(Box<Expr>, Box<Expr>),

    /// Equality comparison, returning a 1-bit boolean expression.
    Equal(Box<Expr>, Box<Expr>),

    /// Unsigned less-than comparison, returning a 1-bit boolean expression.
    UnsignedLessThan(Box<Expr>, Box<Expr>),

    /// Signed less-than comparison, returning a 1-bit boolean expression.
    SignedLessThan(Box<Expr>, Box<Expr>),

    /// Extract a contiguous bit range from a bit-vector.
    ///
    /// `high` and `low` are inclusive bit indices, with bit 0 as the least
    /// significant bit. The result width is `high - low + 1`.
    ///
    Extract {
        value: Box<Expr>,
        high: u16,
        low: u16,
    },

    /// Concatenate bit-vectors from most-significant chunk to least-significant
    /// chunk.
    ///
    /// For example, `Concat([a, b])` places `a` above `b`; if both are 16 bits,
    /// the result is a 32-bit value with `a` in bits 31:16.
    ///
    /// Concat is the exception to the rule that all operand expressions must have the same bit width
    /// You can eg concatenate a 4 bit and 12 bit vector to make 16 bits.
    Concat(Vec<Expr>),

    /// Zero-extend a bit-vector to `to_width` bits.
    ///
    /// The input width must be less than or equal to `to_width`.
    ZeroExtend { value: Box<Expr>, to_width: u16 },

    /// Sign-extend a bit-vector to `to_width` bits.
    ///
    /// The input's most significant bit is replicated into the new high bits.
    /// The input width must be less than or equal to `to_width`.
    SignExtend { value: Box<Expr>, to_width: u16 },

    /// Count the number of set bits in a bit-vector.
    ///
    /// This is useful for instruction forms such as register-list transfers.
    /// Consumers should choose an output width large enough for the source width.
    CountOnes(Box<Expr>),

    /// Carry-out bit from `lhs + rhs + carry_in` at `width` bits.
    ///
    /// Returns a 1-bit boolean expression. `carry_in` is expected to be 1 bit.
    /// This models unsigned carry for flag updates without requiring the full
    /// widened sum to be materialized elsewhere in the expression tree.
    AddCarryOut {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        carry_in: Box<Expr>,
        width: u16,
    },

    /// Signed overflow bit from `lhs + rhs + carry_in` at `width` bits.
    ///
    /// Returns a 1-bit boolean expression. `carry_in` is expected to be 1 bit.
    /// This models two's-complement overflow for flag updates.
    AddOverflow {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        carry_in: Box<Expr>,
        width: u16,
    },

    /// Carry-out bit from `lhs - rhs - borrow_in` at `width` bits.
    ///
    /// Returns a 1-bit boolean expression. `borrow_in` is expected to be 1 bit.
    /// Architectures such as ARM define the subtraction carry flag as "not
    /// borrow", so this expression returns the architectural carry-out, not the
    /// raw borrow bit.
    SubCarryOut {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow_in: Box<Expr>,
        width: u16,
    },

    /// Signed overflow bit from `lhs - rhs - borrow_in` at `width` bits.
    ///
    /// Returns a 1-bit boolean expression. `borrow_in` is expected to be 1 bit.
    /// This models two's-complement overflow for subtraction-style flag updates.
    SubOverflow {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        borrow_in: Box<Expr>,
        width: u16,
    },

    /// Conditional expression.
    ///
    /// `condition` is a 1-bit boolean expression. The two value arms should have
    /// the same width; the result has that shared width. This is the main way to
    /// encode opcode tables, conditional execution, addressing mode choices, and
    /// ISA-specific special cases while keeping the AST purely functional.
    Select {
        condition: Box<Expr>,
        when_true: Box<Expr>,
        when_false: Box<Expr>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AssocCommOp {
    Add,
    Mul,
    And,
    Or,
    Xor,
}

impl Expr {
    fn assert_valid_width(width: u16) {
        if width == 0 || width > 128 {
            panic!("Bit-vector width must be in 1..=128, got {width}");
        }
    }

    fn bit_mask(width: u16) -> u128 {
        Self::assert_valid_width(width);
        if width == 128 {
            !0u128
        } else {
            (1u128 << width) - 1
        }
    }

    fn sign_bit(width: u16) -> u128 {
        Self::assert_valid_width(width);
        1u128 << (width - 1)
    }

    fn canonical(value: u128, width: u16) -> u128 {
        value & Self::bit_mask(width)
    }

    fn const_bits(value: u128, width: u16) -> Self {
        Expr::Const {
            value: Self::canonical(value, width),
            width,
        }
    }

    fn expect_same_width(lhs_width: u16, rhs_width: u16) -> u16 {
        if lhs_width != rhs_width {
            panic!(
                "Width of operands for binary operation must match. Consider explicitly defining how to sign extend operands in the semantics."
            );
        }
        Self::assert_valid_width(lhs_width);
        lhs_width
    }

    fn expect_bool_const(value: u128, width: u16, name: &str) -> u128 {
        if width != 1 {
            panic!("{name} must have width 1, got width = {width}");
        }
        Self::canonical(value, width)
    }

    fn sign_extend_to_u128(value: u128, width: u16) -> u128 {
        let value = Self::canonical(value, width);
        if value & Self::sign_bit(width) == 0 {
            value
        } else {
            value | !Self::bit_mask(width)
        }
    }

    fn signed_value(value: u128, width: u16) -> i128 {
        Self::sign_extend_to_u128(value, width) as i128
    }

    fn zero_extend_const(value: u128, from_width: u16, to_width: u16) -> u128 {
        if from_width > to_width {
            panic!(
                "Zext to_width must be at least value width, but got width = {from_width} and to_width = {to_width}"
            );
        }
        Self::assert_valid_width(to_width);
        Self::canonical(value, from_width)
    }

    fn sign_extend_const(value: u128, from_width: u16, to_width: u16) -> u128 {
        if from_width > to_width {
            panic!(
                "Sign extend to_width must be at least value width, but got width = {from_width} and to_width = {to_width}"
            );
        }
        Self::assert_valid_width(to_width);

        let value = Self::canonical(value, from_width);
        if value & Self::sign_bit(from_width) == 0 {
            value
        } else {
            value | (Self::bit_mask(to_width) ^ Self::bit_mask(from_width))
        }
    }

    fn shift_left_const(value: u128, amount: u128, width: u16) -> u128 {
        if amount >= width as u128 {
            0
        } else {
            Self::canonical(value, width) << amount as u32
        }
    }

    fn logical_shift_right_const(value: u128, amount: u128, width: u16) -> u128 {
        if amount >= width as u128 {
            0
        } else {
            Self::canonical(value, width) >> amount as u32
        }
    }

    fn arithmetic_shift_right_const(value: u128, amount: u128, width: u16) -> u128 {
        let value = Self::canonical(value, width);
        let negative = value & Self::sign_bit(width) != 0;
        if amount >= width as u128 {
            if negative { Self::bit_mask(width) } else { 0 }
        } else {
            ((Self::sign_extend_to_u128(value, width) as i128) >> amount as u32) as u128
        }
    }

    fn rotate_right_const(value: u128, amount: u128, width: u16) -> u128 {
        let value = Self::canonical(value, width);
        let shift = (amount % width as u128) as u32;
        if shift == 0 {
            value
        } else {
            (value >> shift) | (value << (width as u32 - shift))
        }
    }

    fn add_carry_out_const(lhs: u128, rhs: u128, carry_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let carry_in = Self::canonical(carry_in, 1);
        if width == 128 {
            let (sum, carry1) = lhs.overflowing_add(rhs);
            let (_, carry2) = sum.overflowing_add(carry_in);
            carry1 || carry2
        } else {
            lhs + rhs + carry_in > Self::bit_mask(width)
        }
    }

    fn sub_carry_out_const(lhs: u128, rhs: u128, borrow_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let borrow_in = Self::canonical(borrow_in, 1);
        let (diff, borrow1) = lhs.overflowing_sub(rhs);
        let (_, borrow2) = diff.overflowing_sub(borrow_in);
        !(borrow1 || borrow2)
    }

    fn add_overflow_const(lhs: u128, rhs: u128, carry_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let carry_in = Self::canonical(carry_in, 1);
        let result = Self::canonical(lhs.wrapping_add(rhs).wrapping_add(carry_in), width);
        (!(lhs ^ rhs) & (lhs ^ result) & Self::sign_bit(width)) != 0
    }

    fn sub_overflow_const(lhs: u128, rhs: u128, borrow_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let borrow_in = Self::canonical(borrow_in, 1);
        let result = Self::canonical(lhs.wrapping_sub(rhs).wrapping_sub(borrow_in), width);
        ((lhs ^ rhs) & (lhs ^ result) & Self::sign_bit(width)) != 0
    }

    fn make_assoc_comm_expr(op: AssocCommOp, lhs: Expr, rhs: Expr) -> Self {
        match op {
            AssocCommOp::Add => Expr::Add(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::Mul => Expr::Mul(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::And => Expr::And(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::Or => Expr::Or(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::Xor => Expr::Xor(Box::new(lhs), Box::new(rhs)),
        }
    }

    fn flatten_assoc_comm_op(op: AssocCommOp, expr: Expr, terms: &mut Vec<Expr>) {
        match (op, expr) {
            (AssocCommOp::Add, Expr::Add(lhs, rhs))
            | (AssocCommOp::Mul, Expr::Mul(lhs, rhs))
            | (AssocCommOp::And, Expr::And(lhs, rhs))
            | (AssocCommOp::Or, Expr::Or(lhs, rhs))
            | (AssocCommOp::Xor, Expr::Xor(lhs, rhs)) => {
                Self::flatten_assoc_comm_op(op, *lhs, terms);
                Self::flatten_assoc_comm_op(op, *rhs, terms);
            }
            (_, expr) => terms.push(expr),
        }
    }

    fn fold_assoc_comm_const(op: AssocCommOp, lhs: u128, rhs: u128, _width: u16) -> u128 {
        match op {
            AssocCommOp::Add => lhs.wrapping_add(rhs),
            AssocCommOp::Mul => lhs.wrapping_mul(rhs),
            AssocCommOp::And => lhs & rhs,
            AssocCommOp::Or => lhs | rhs,
            AssocCommOp::Xor => lhs ^ rhs,
        }
    }

    fn is_assoc_comm_identity(op: AssocCommOp, value: u128, width: u16) -> bool {
        match op {
            AssocCommOp::Add | AssocCommOp::Or | AssocCommOp::Xor => value == 0,
            AssocCommOp::Mul => value == 1,
            AssocCommOp::And => value == Self::bit_mask(width),
        }
    }

    fn is_assoc_comm_annihilator(op: AssocCommOp, value: u128, width: u16) -> bool {
        match op {
            AssocCommOp::Mul | AssocCommOp::And => value == 0,
            AssocCommOp::Or => value == Self::bit_mask(width),
            AssocCommOp::Add | AssocCommOp::Xor => false,
        }
    }

    fn rebuild_assoc_comm_op(op: AssocCommOp, mut terms: Vec<Expr>) -> Self {
        let first = terms
            .drain(..1)
            .next()
            .expect("Associative/commutative operation must have at least one term");
        terms
            .into_iter()
            .fold(first, |acc, term| Self::make_assoc_comm_expr(op, acc, term))
    }

    fn collapse_assoc_comm_op(
        instruction: &DecodedInstruction,
        op1: Box<Expr>,
        op2: Box<Expr>,
        op: AssocCommOp,
    ) -> Self {
        let mut terms = Vec::new();
        Self::flatten_assoc_comm_op(op, op1.collapse(instruction), &mut terms);
        Self::flatten_assoc_comm_op(op, op2.collapse(instruction), &mut terms);

        let mut non_const_terms = Vec::new();
        let mut folded_const: Option<(u128, u16)> = None;

        for term in terms {
            match term {
                Expr::Const { value, width } => {
                    let value = Self::canonical(value, width);
                    folded_const = Some(match folded_const {
                        Some((acc, acc_width)) => {
                            let width = Self::expect_same_width(acc_width, width);
                            (
                                Self::canonical(
                                    Self::fold_assoc_comm_const(op, acc, value, width),
                                    width,
                                ),
                                width,
                            )
                        }
                        None => (value, width),
                    });
                }
                term => non_const_terms.push(term),
            }
        }

        let Some((const_value, const_width)) = folded_const else {
            return Self::rebuild_assoc_comm_op(op, non_const_terms);
        };

        if Self::is_assoc_comm_annihilator(op, const_value, const_width) {
            return Self::const_bits(const_value, const_width);
        }

        if !Self::is_assoc_comm_identity(op, const_value, const_width) || non_const_terms.is_empty()
        {
            non_const_terms.push(Self::const_bits(const_value, const_width));
        }

        Self::rebuild_assoc_comm_op(op, non_const_terms)
    }

    fn collapse_binary_op<F>(
        instruction: &DecodedInstruction,
        op1: Box<Expr>,
        op2: Box<Expr>,
        rebuild: fn(Box<Expr>, Box<Expr>) -> Expr,
        fold: F,
    ) -> Self
    where
        F: FnOnce(u128, u128, u16) -> u128,
    {
        let op1_collapsed = op1.collapse(instruction);
        let op2_collapsed = op2.collapse(instruction);
        match (op1_collapsed, op2_collapsed) {
            (
                Expr::Const {
                    value: value_op1,
                    width: width_op1,
                },
                Expr::Const {
                    value: value_op2,
                    width: width_op2,
                },
            ) => {
                let width = Self::expect_same_width(width_op1, width_op2);
                Self::const_bits(
                    fold(
                        Self::canonical(value_op1, width),
                        Self::canonical(value_op2, width),
                        width,
                    ),
                    width,
                )
            }
            (op1_collapsed, op2_collapsed) => {
                rebuild(Box::new(op1_collapsed), Box::new(op2_collapsed))
            }
        }
    }

    fn collapse_binary_pred<F>(
        instruction: &DecodedInstruction,
        op1: Box<Expr>,
        op2: Box<Expr>,
        rebuild: fn(Box<Expr>, Box<Expr>) -> Expr,
        pred: F,
    ) -> Self
    where
        F: FnOnce(u128, u128, u16) -> bool,
    {
        let op1_collapsed = op1.collapse(instruction);
        let op2_collapsed = op2.collapse(instruction);
        match (op1_collapsed, op2_collapsed) {
            (
                Expr::Const {
                    value: value_op1,
                    width: width_op1,
                },
                Expr::Const {
                    value: value_op2,
                    width: width_op2,
                },
            ) => {
                let width = Self::expect_same_width(width_op1, width_op2);
                Expr::Const {
                    value: pred(
                        Self::canonical(value_op1, width),
                        Self::canonical(value_op2, width),
                        width,
                    ) as u128,
                    width: 1,
                }
            }
            (op1_collapsed, op2_collapsed) => {
                rebuild(Box::new(op1_collapsed), Box::new(op2_collapsed))
            }
        }
    }

    fn collapse_unary_op<F>(
        instruction: &DecodedInstruction,
        op: Box<Expr>,
        rebuild: fn(Box<Expr>) -> Expr,
        fold: F,
    ) -> Self
    where
        F: FnOnce(u128, u16) -> u128,
    {
        let op_collapsed = op.collapse(instruction);
        match op_collapsed {
            Expr::Const { value, width } => {
                Self::const_bits(fold(Self::canonical(value, width), width), width)
            }
            op_collapsed => rebuild(Box::new(op_collapsed)),
        }
    }

    fn expr_width(&self) -> Option<u16> {
        match self {
            Expr::Const { width, .. } => Some(*width),
            Expr::Operand(RegisterField(RegisterRef::Fixed { width, .. })) => Some(*width),
            Expr::Operand(ImmediateField(_))
            | Expr::Operand(RegisterField(RegisterRef::FromField(_)))
            | Expr::DerivedValue(_)
            | Expr::ReadRegister(_) => None,
            Expr::ReadMemory { width, .. } => Some(*width),
            Expr::Add(lhs, rhs)
            | Expr::Sub(lhs, rhs)
            | Expr::Mul(lhs, rhs)
            | Expr::And(lhs, rhs)
            | Expr::Or(lhs, rhs)
            | Expr::Xor(lhs, rhs)
            | Expr::ShiftLeft(lhs, rhs)
            | Expr::LogicalShiftRight(lhs, rhs)
            | Expr::ArithmeticShiftRight(lhs, rhs)
            | Expr::RotateRight(lhs, rhs) => {
                let lhs_width = lhs.expr_width()?;
                let rhs_width = rhs.expr_width()?;
                (lhs_width == rhs_width).then_some(lhs_width)
            }
            Expr::Not(value) => value.expr_width(),
            Expr::Equal(_, _)
            | Expr::UnsignedLessThan(_, _)
            | Expr::SignedLessThan(_, _)
            | Expr::AddCarryOut { .. }
            | Expr::AddOverflow { .. }
            | Expr::SubCarryOut { .. }
            | Expr::SubOverflow { .. } => Some(1),
            Expr::Extract { high, low, .. } => {
                if high >= low {
                    Some(high - low + 1)
                } else {
                    None
                }
            }
            Expr::Concat(values) => {
                let mut width = 0u16;
                for value in values {
                    width = width.checked_add(value.expr_width()?)?;
                    if width > 128 {
                        return None;
                    }
                }
                Some(width)
            }
            Expr::ZeroExtend { to_width, .. } | Expr::SignExtend { to_width, .. } => {
                Some(*to_width)
            }
            Expr::CountOnes(value) => value.expr_width(),
            Expr::Select {
                when_true,
                when_false,
                ..
            } => {
                let true_width = when_true.expr_width()?;
                let false_width = when_false.expr_width()?;
                (true_width == false_width).then_some(true_width)
            }
        }
    }

    fn canonical_sort_key(expr: &Expr) -> String {
        format!("{expr:?}")
    }

    fn canonicalize_shift_like_op(
        value: &Expr,
        amount: &Expr,
        rebuild: fn(Box<Expr>, Box<Expr>) -> Expr,
    ) -> Self {
        let value = value.canonicalize();
        let amount = amount.canonicalize();
        match (&value, &amount) {
            (
                _,
                Expr::Const {
                    value: amount_value,
                    width: amount_width,
                },
            ) if Self::canonical(*amount_value, *amount_width) == 0 => value,
            (
                Expr::Const {
                    value: value_value,
                    width: value_width,
                },
                _,
            ) if Self::canonical(*value_value, *value_width) == 0 => {
                Self::const_bits(0, *value_width)
            }
            _ => rebuild(Box::new(value), Box::new(amount)),
        }
    }

    fn canonicalize_flag_expr(
        lhs: &Expr,
        rhs: &Expr,
        flag_in: &Expr,
        width: u16,
        rebuild: fn(Expr, Expr, Expr, u16) -> Expr,
    ) -> Self {
        rebuild(
            lhs.canonicalize(),
            rhs.canonicalize(),
            flag_in.canonicalize(),
            width,
        )
    }

    fn canonicalize_assoc_comm_op(op: AssocCommOp, lhs: &Expr, rhs: &Expr) -> Self {
        let mut terms = Vec::new();
        Self::flatten_assoc_comm_op(op, lhs.canonicalize(), &mut terms);
        Self::flatten_assoc_comm_op(op, rhs.canonicalize(), &mut terms);

        let mut non_const_terms = Vec::new();
        let mut folded_const: Option<(u128, u16)> = None;

        for term in terms {
            match term {
                Expr::Const { value, width } => {
                    let value = Self::canonical(value, width);
                    folded_const = Some(match folded_const {
                        Some((acc, acc_width)) => {
                            let width = Self::expect_same_width(acc_width, width);
                            (
                                Self::canonical(
                                    Self::fold_assoc_comm_const(op, acc, value, width),
                                    width,
                                ),
                                width,
                            )
                        }
                        None => (value, width),
                    });
                }
                term => non_const_terms.push(term),
            }
        }

        non_const_terms.sort_by_key(Self::canonical_sort_key);

        match op {
            AssocCommOp::And | AssocCommOp::Or => {
                non_const_terms.dedup();
            }
            AssocCommOp::Xor => {
                let mut reduced_terms = Vec::new();
                let mut cancelled_width = folded_const.map(|(_, width)| width);
                let mut index = 0;
                while index < non_const_terms.len() {
                    let term = non_const_terms[index].clone();
                    let mut count = 1;
                    while index + count < non_const_terms.len()
                        && non_const_terms[index + count] == term
                    {
                        count += 1;
                    }

                    if count % 2 == 1 {
                        reduced_terms.push(term.clone());
                    } else if let Some(width) = term.expr_width() {
                        cancelled_width = Some(width);
                    } else {
                        reduced_terms.push(term.clone());
                        reduced_terms.push(term);
                    }

                    index += count;
                }
                non_const_terms = reduced_terms;

                if folded_const.is_none()
                    && non_const_terms.is_empty()
                    && let Some(width) = cancelled_width
                {
                    folded_const = Some((0, width));
                }
            }
            AssocCommOp::Add | AssocCommOp::Mul => {}
        }

        let Some((const_value, const_width)) = folded_const else {
            return match non_const_terms.len() {
                0 => {
                    panic!("Associative/commutative operation has no terms after canonicalization")
                }
                1 => non_const_terms
                    .into_iter()
                    .next()
                    .expect("Length is 1, so there should be one term"),
                _ => Self::rebuild_assoc_comm_op(op, non_const_terms),
            };
        };

        if Self::is_assoc_comm_annihilator(op, const_value, const_width) {
            return Self::const_bits(const_value, const_width);
        }

        if !Self::is_assoc_comm_identity(op, const_value, const_width) || non_const_terms.is_empty()
        {
            non_const_terms.push(Self::const_bits(const_value, const_width));
        }

        match non_const_terms.len() {
            0 => Self::const_bits(const_value, const_width),
            1 => non_const_terms
                .into_iter()
                .next()
                .expect("Length is 1, so there should be one term"),
            _ => Self::rebuild_assoc_comm_op(op, non_const_terms),
        }
    }

    pub fn collapse_and_canonicalize(&self, instruction: &DecodedInstruction) -> Self {
        self.collapse(instruction).canonicalize()
    }

    pub fn canonicalize(&self) -> Self {
        match self {
            Expr::Const { value, width } => Self::const_bits(*value, *width),
            Expr::Operand(_) | Expr::DerivedValue(_) => self.clone(),
            Expr::ReadRegister(register) => Expr::ReadRegister(Box::new(register.canonicalize())),
            Expr::ReadMemory { address, width } => Expr::ReadMemory {
                address: Box::new(address.canonicalize()),
                width: *width,
            },
            Expr::Add(lhs, rhs) => Self::canonicalize_assoc_comm_op(AssocCommOp::Add, lhs, rhs),
            Expr::Sub(lhs, rhs) => {
                let lhs = lhs.canonicalize();
                let rhs = rhs.canonicalize();
                if matches!(
                    &rhs,
                    Expr::Const { value, width } if Self::canonical(*value, *width) == 0
                ) {
                    lhs
                } else if lhs == rhs {
                    if let Some(width) = lhs.expr_width() {
                        Self::const_bits(0, width)
                    } else {
                        Expr::Sub(Box::new(lhs), Box::new(rhs))
                    }
                } else {
                    Expr::Sub(Box::new(lhs), Box::new(rhs))
                }
            }
            Expr::Mul(lhs, rhs) => Self::canonicalize_assoc_comm_op(AssocCommOp::Mul, lhs, rhs),
            Expr::And(lhs, rhs) => Self::canonicalize_assoc_comm_op(AssocCommOp::And, lhs, rhs),
            Expr::Or(lhs, rhs) => Self::canonicalize_assoc_comm_op(AssocCommOp::Or, lhs, rhs),
            Expr::Xor(lhs, rhs) => Self::canonicalize_assoc_comm_op(AssocCommOp::Xor, lhs, rhs),
            Expr::Not(value) => {
                let value = value.canonicalize();
                match value {
                    Expr::Not(inner) => *inner,
                    value => Expr::Not(Box::new(value)),
                }
            }
            Expr::ShiftLeft(value, amount) => {
                Self::canonicalize_shift_like_op(value, amount, Expr::ShiftLeft)
            }
            Expr::LogicalShiftRight(value, amount) => {
                Self::canonicalize_shift_like_op(value, amount, Expr::LogicalShiftRight)
            }
            Expr::ArithmeticShiftRight(value, amount) => {
                Self::canonicalize_shift_like_op(value, amount, Expr::ArithmeticShiftRight)
            }
            Expr::RotateRight(value, amount) => {
                Self::canonicalize_shift_like_op(value, amount, Expr::RotateRight)
            }
            Expr::Equal(lhs, rhs) => {
                let lhs = lhs.canonicalize();
                let rhs = rhs.canonicalize();
                if lhs == rhs {
                    bool_const(true)
                } else if Self::canonical_sort_key(&lhs) <= Self::canonical_sort_key(&rhs) {
                    Expr::Equal(Box::new(lhs), Box::new(rhs))
                } else {
                    Expr::Equal(Box::new(rhs), Box::new(lhs))
                }
            }
            Expr::UnsignedLessThan(lhs, rhs) => {
                let lhs = lhs.canonicalize();
                let rhs = rhs.canonicalize();
                if lhs == rhs {
                    bool_const(false)
                } else {
                    Expr::UnsignedLessThan(Box::new(lhs), Box::new(rhs))
                }
            }
            Expr::SignedLessThan(lhs, rhs) => {
                let lhs = lhs.canonicalize();
                let rhs = rhs.canonicalize();
                if lhs == rhs {
                    bool_const(false)
                } else {
                    Expr::SignedLessThan(Box::new(lhs), Box::new(rhs))
                }
            }
            Expr::Extract { value, high, low } => {
                if high < low {
                    panic!("Expr::Extract high must be >= low, got high = {high} and low = {low}");
                }

                let value = value.canonicalize();
                let out_width = high - low + 1;
                Self::assert_valid_width(out_width);
                if let Some(value_width) = value.expr_width() {
                    if *high >= value_width {
                        panic!(
                            "Expr::Extract high index {high} is outside value width {value_width}"
                        );
                    }
                    if *low == 0 && out_width == value_width {
                        return value;
                    }
                }

                Expr::Extract {
                    value: Box::new(value),
                    high: *high,
                    low: *low,
                }
            }
            Expr::Concat(values) => {
                let mut new_values = Vec::new();
                for value in values {
                    let value = value.canonicalize();
                    match value {
                        Expr::Const { value, width } => {
                            Self::assert_valid_width(width);
                            if let Some(Expr::Const {
                                value: previous_value,
                                width: previous_width,
                            }) = new_values.last_mut()
                            {
                                let combined_width = *previous_width + width;
                                Self::assert_valid_width(combined_width);
                                *previous_value = Self::canonical(
                                    (Self::canonical(*previous_value, *previous_width) << width)
                                        | Self::canonical(value, width),
                                    combined_width,
                                );
                                *previous_width = combined_width;
                            } else {
                                new_values.push(Self::const_bits(value, width));
                            }
                        }
                        value => new_values.push(value),
                    }
                }
                if new_values.len() == 1 {
                    new_values
                        .into_iter()
                        .next()
                        .expect("Length is 1, so there should be one value")
                } else {
                    Expr::Concat(new_values)
                }
            }
            Expr::ZeroExtend { value, to_width } => {
                let value = value.canonicalize();
                if let Some(value_width) = value.expr_width() {
                    if value_width > *to_width {
                        panic!(
                            "Zext to_width must be at least value width, but got width = {value_width} and to_width = {to_width}"
                        );
                    }
                    if value_width == *to_width {
                        return value;
                    }
                }

                match value {
                    Expr::ZeroExtend { value, .. } => Expr::ZeroExtend {
                        value,
                        to_width: *to_width,
                    },
                    value => Expr::ZeroExtend {
                        value: Box::new(value),
                        to_width: *to_width,
                    },
                }
            }
            Expr::SignExtend { value, to_width } => {
                let value = value.canonicalize();
                if let Some(value_width) = value.expr_width() {
                    if value_width > *to_width {
                        panic!(
                            "Sign extend to_width must be at least value width, but got width = {value_width} and to_width = {to_width}"
                        );
                    }
                    if value_width == *to_width {
                        return value;
                    }
                }

                match value {
                    Expr::SignExtend { value, .. } => Expr::SignExtend {
                        value,
                        to_width: *to_width,
                    },
                    value => Expr::SignExtend {
                        value: Box::new(value),
                        to_width: *to_width,
                    },
                }
            }
            Expr::CountOnes(value) => Expr::CountOnes(Box::new(value.canonicalize())),
            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => Self::canonicalize_flag_expr(lhs, rhs, carry_in, *width, add_carry_out),
            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => Self::canonicalize_flag_expr(lhs, rhs, carry_in, *width, add_overflow),
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                width,
            } => Self::canonicalize_flag_expr(lhs, rhs, borrow_in, *width, sub_carry_out),
            Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                width,
            } => Self::canonicalize_flag_expr(lhs, rhs, borrow_in, *width, sub_overflow),
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition = condition.canonicalize();
                let when_true = when_true.canonicalize();
                let when_false = when_false.canonicalize();
                match condition {
                    Expr::Const { value, width } => {
                        let value = Self::expect_bool_const(value, width, "select condition");
                        if value == 1 { when_true } else { when_false }
                    }
                    _ if when_true == when_false => when_true,
                    condition => Expr::Select {
                        condition: Box::new(condition),
                        when_true: Box::new(when_true),
                        when_false: Box::new(when_false),
                    },
                }
            }
        }
    }

    /// Evaluates all `Select` statements and `guard`s given the actual instruction, as well as substituting
    /// DerivedValues into the Expr
    pub fn collapse(&self, instruction: &DecodedInstruction) -> Self {
        let collapsed_expr = self.clone();

        let derived_values: HashMap<String, DerivedValue> = instruction
            .form
            .as_ref()
            .expect("DecodedInstruction.form must not be None")
            .derived_values
            .iter()
            .map(|v| (v.name.0.clone(), v.clone()))
            .collect();

        match collapsed_expr {
            Expr::Const { .. } => collapsed_expr,
            Expr::Operand(ImmediateField(field_name)) => {
                let imm = instruction
                    .field_value(&field_name)
                    .unwrap_or_else(|| panic!("Field {field_name} does not exist!"));
                Expr::Const {
                    value: imm.to_int(),
                    width: imm
                        .bits
                        .len()
                        .try_into()
                        .expect("Immediate field too long (>2^16 bit length)"),
                }
            }
            Expr::Operand(RegisterField(RegisterRef::FromField(field_name))) => {
                let reg_ident = instruction
                    .field_value(&field_name)
                    .unwrap_or_else(|| panic!("Field {field_name} does not exist!"));
                Expr::Operand(RegisterField(RegisterRef::Fixed {
                    register: Register(
                        reg_ident
                            .to_int()
                            .try_into()
                            .expect("Register address field must fit into u8"),
                    ),
                    width: reg_ident
                        .bits
                        .len()
                        .try_into()
                        .expect("Register address length value must fit into u16"),
                }))
            }
            Expr::Operand(RegisterField(RegisterRef::Fixed { .. })) => collapsed_expr,
            Expr::DerivedValue(name) => derived_values
                .get(name.0.as_str())
                .unwrap_or_else(|| panic!("Derived value {} does not exist!", name.0))
                .value
                .collapse(instruction),
            Expr::ReadRegister(inner_expr) => {
                Expr::ReadRegister(Box::new(inner_expr.collapse(instruction)))
            }
            Expr::ReadMemory { address, width } => Expr::ReadMemory {
                address: Box::new(address.collapse(instruction)),
                width,
            },
            Expr::Add(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, op1, op2, AssocCommOp::Add)
            }
            Expr::Sub(op1, op2) => {
                Self::collapse_binary_op(instruction, op1, op2, Expr::Sub, |lhs, rhs, _width| {
                    lhs.wrapping_sub(rhs)
                })
            }
            Expr::Mul(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, op1, op2, AssocCommOp::Mul)
            }
            Expr::And(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, op1, op2, AssocCommOp::And)
            }
            Expr::Or(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, op1, op2, AssocCommOp::Or)
            }
            Expr::Xor(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, op1, op2, AssocCommOp::Xor)
            }
            Expr::Not(op) => {
                Self::collapse_unary_op(instruction, op, Expr::Not, |value, _width| !value)
            }
            Expr::ShiftLeft(op1, op2) => Self::collapse_binary_op(
                instruction,
                op1,
                op2,
                Expr::ShiftLeft,
                Self::shift_left_const,
            ),
            Expr::LogicalShiftRight(op1, op2) => Self::collapse_binary_op(
                instruction,
                op1,
                op2,
                Expr::LogicalShiftRight,
                Self::logical_shift_right_const,
            ),
            Expr::ArithmeticShiftRight(op1, op2) => Self::collapse_binary_op(
                instruction,
                op1,
                op2,
                Expr::ArithmeticShiftRight,
                Self::arithmetic_shift_right_const,
            ),
            Expr::RotateRight(op1, op2) => Self::collapse_binary_op(
                instruction,
                op1,
                op2,
                Expr::RotateRight,
                Self::rotate_right_const,
            ),
            Expr::Equal(op1, op2) => Self::collapse_binary_pred(
                instruction,
                op1,
                op2,
                Expr::Equal,
                |lhs, rhs, _width| lhs == rhs,
            ),
            Expr::UnsignedLessThan(op1, op2) => Self::collapse_binary_pred(
                instruction,
                op1,
                op2,
                Expr::UnsignedLessThan,
                |lhs, rhs, _width| lhs < rhs,
            ),
            Expr::SignedLessThan(op1, op2) => Self::collapse_binary_pred(
                instruction,
                op1,
                op2,
                Expr::SignedLessThan,
                |lhs, rhs, width| Self::signed_value(lhs, width) < Self::signed_value(rhs, width),
            ),
            Expr::Extract { value, high, low } => {
                if high < low {
                    panic!("Expr::Extract high must be >= low, got high = {high} and low = {low}");
                }
                let out_width = high - low + 1;
                Self::assert_valid_width(out_width);
                let value_collapsed = value.collapse(instruction);
                match value_collapsed {
                    Expr::Const {
                        value: value_val,
                        width,
                    } => {
                        if high >= width {
                            panic!(
                                "Expr::Extract high index {high} is outside value width {width}"
                            );
                        }
                        Expr::Const {
                            value: (Self::canonical(value_val, width) >> low)
                                & Self::bit_mask(out_width),
                            width: out_width,
                        }
                    }
                    value_collapsed => Expr::Extract {
                        value: Box::new(value_collapsed),
                        high,
                        low,
                    },
                }
            }
            Expr::Concat(exprs) => {
                let mut new_exprs = vec![];
                for expr in exprs {
                    let expr_collapsed = expr.collapse(instruction);
                    match expr_collapsed {
                        Expr::Const { value, width } => {
                            Self::assert_valid_width(width);
                            if let Some(Expr::Const {
                                value: value_2,
                                width: width_2,
                            }) = new_exprs.last_mut()
                            {
                                let combined_width = *width_2 + width;
                                Self::assert_valid_width(combined_width);
                                *value_2 = Self::canonical(
                                    (Self::canonical(*value_2, *width_2) << width)
                                        | Self::canonical(value, width),
                                    combined_width,
                                );
                                *width_2 = combined_width;
                            } else {
                                new_exprs.push(Self::const_bits(value, width))
                            }
                        }
                        expr_collapsed => new_exprs.push(expr_collapsed),
                    }
                }
                // If new_exprs has just one element, return that element
                if new_exprs.len() == 1 {
                    new_exprs
                        .into_iter()
                        .next()
                        .expect("Since the length is 1, there should be a first element")
                } else {
                    Expr::Concat(new_exprs)
                }
            }
            Expr::ZeroExtend { value, to_width } => {
                let value_collapsed = value.collapse(instruction);
                match value_collapsed {
                    Expr::Const {
                        value: value_val,
                        width,
                    } => Expr::Const {
                        value: Self::zero_extend_const(value_val, width, to_width),
                        width: to_width,
                    },
                    value_collapsed => Expr::ZeroExtend {
                        value: Box::new(value_collapsed),
                        to_width,
                    },
                }
            }
            Expr::SignExtend { value, to_width } => {
                let value_collapsed = value.collapse(instruction);
                match value_collapsed {
                    Expr::Const {
                        value: value_val,
                        width,
                    } => Expr::Const {
                        value: Self::sign_extend_const(value_val, width, to_width),
                        width: to_width,
                    },
                    value_collapsed => Expr::SignExtend {
                        value: Box::new(value_collapsed),
                        to_width,
                    },
                }
            }
            Expr::CountOnes(expr) => {
                Self::collapse_unary_op(instruction, expr, Expr::CountOnes, |value, _width| {
                    value.count_ones() as u128
                })
            }
            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs_collapsed = lhs.collapse(instruction);
                let rhs_collapsed = rhs.collapse(instruction);
                let cin_collapsed = carry_in.collapse(instruction);
                if let Expr::Const {
                    value: lhs_val,
                    width: lhs_width,
                } = lhs_collapsed
                    && let Expr::Const {
                        value: rhs_val,
                        width: rhs_width,
                    } = rhs_collapsed
                    && let Expr::Const {
                        value: cin_val,
                        width: cin_width,
                    } = cin_collapsed
                {
                    if !(Self::expect_same_width(lhs_width, rhs_width) == width) {
                        panic!("LHS, RHS, and output must have equal width for AddCarryOut");
                    }
                    let cin_val = Self::expect_bool_const(cin_val, cin_width, "carry_in");
                    let cout_set = Self::add_carry_out_const(lhs_val, rhs_val, cin_val, width);
                    Expr::Const {
                        value: cout_set as u128,
                        width: 1,
                    }
                } else {
                    Expr::AddCarryOut {
                        lhs: Box::new(lhs_collapsed),
                        rhs: Box::new(rhs_collapsed),
                        carry_in: Box::new(cin_collapsed),
                        width: width,
                    }
                }
            }
            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs_collapsed = lhs.collapse(instruction);
                let rhs_collapsed = rhs.collapse(instruction);
                let cin_collapsed = carry_in.collapse(instruction);
                if let Expr::Const {
                    value: lhs_val,
                    width: lhs_width,
                } = lhs_collapsed
                    && let Expr::Const {
                        value: rhs_val,
                        width: rhs_width,
                    } = rhs_collapsed
                    && let Expr::Const {
                        value: cin_val,
                        width: cin_width,
                    } = cin_collapsed
                {
                    if !(Self::expect_same_width(lhs_width, rhs_width) == width) {
                        panic!("LHS, RHS, and output must have equal width for AddOverflow");
                    }
                    let cin_val = Self::expect_bool_const(cin_val, cin_width, "carry_in");
                    let overflow = Self::add_overflow_const(lhs_val, rhs_val, cin_val, width);
                    Expr::Const {
                        value: overflow as u128,
                        width: 1,
                    }
                } else {
                    Expr::AddOverflow {
                        lhs: Box::new(lhs_collapsed),
                        rhs: Box::new(rhs_collapsed),
                        carry_in: Box::new(cin_collapsed),
                        width: width,
                    }
                }
            }
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                width,
            } => {
                let lhs_collapsed = lhs.collapse(instruction);
                let rhs_collapsed = rhs.collapse(instruction);
                let bin_collapsed = borrow_in.collapse(instruction);
                if let Expr::Const {
                    value: lhs_val,
                    width: lhs_width,
                } = lhs_collapsed
                    && let Expr::Const {
                        value: rhs_val,
                        width: rhs_width,
                    } = rhs_collapsed
                    && let Expr::Const {
                        value: bin_val,
                        width: bin_width,
                    } = bin_collapsed
                {
                    if !(Self::expect_same_width(lhs_width, rhs_width) == width) {
                        panic!("LHS, RHS, and output must have equal width for SubCarryOut");
                    }
                    let bin_val = Self::expect_bool_const(bin_val, bin_width, "borrow_in");
                    let cout_set = Self::sub_carry_out_const(lhs_val, rhs_val, bin_val, width);
                    Expr::Const {
                        value: cout_set as u128,
                        width: 1,
                    }
                } else {
                    Expr::SubCarryOut {
                        lhs: Box::new(lhs_collapsed),
                        rhs: Box::new(rhs_collapsed),
                        borrow_in: Box::new(bin_collapsed),
                        width,
                    }
                }
            }
            Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                width,
            } => {
                let lhs_collapsed = lhs.collapse(instruction);
                let rhs_collapsed = rhs.collapse(instruction);
                let bin_collapsed = borrow_in.collapse(instruction);
                if let Expr::Const {
                    value: lhs_val,
                    width: lhs_width,
                } = lhs_collapsed
                    && let Expr::Const {
                        value: rhs_val,
                        width: rhs_width,
                    } = rhs_collapsed
                    && let Expr::Const {
                        value: bin_val,
                        width: bin_width,
                    } = bin_collapsed
                {
                    if !(Self::expect_same_width(lhs_width, rhs_width) == width) {
                        panic!("LHS, RHS, and output must have equal width for SubOverflow");
                    }
                    let bin_val = Self::expect_bool_const(bin_val, bin_width, "borrow_in");
                    let overflow = Self::sub_overflow_const(lhs_val, rhs_val, bin_val, width);
                    Expr::Const {
                        value: overflow as u128,
                        width: 1,
                    }
                } else {
                    Expr::SubOverflow {
                        lhs: Box::new(lhs_collapsed),
                        rhs: Box::new(rhs_collapsed),
                        borrow_in: Box::new(bin_collapsed),
                        width: width,
                    }
                }
            }
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition_collapsed = condition.collapse(instruction);
                let when_true_collapsed = when_true.collapse(instruction);
                let when_false_collapsed = when_false.collapse(instruction);

                if let Expr::Const { value, width } = condition_collapsed {
                    if width != 1 {
                        panic!(
                            "Condition for Expr::Select must have width of 1, had width = {width}"
                        );
                    }
                    // In this case, we can get rid of the select
                    if Self::canonical(value, width) == 1 {
                        when_true_collapsed
                    } else {
                        when_false_collapsed
                    }
                } else {
                    Expr::Select {
                        condition: Box::new(condition_collapsed),
                        when_true: Box::new(when_true_collapsed),
                        when_false: Box::new(when_false_collapsed),
                    }
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueName(pub String);

pub type FieldName = String;

/// A decoded instruction operand that can appear inside an expression.
///
/// Operand references name bits from the instruction encoding. They are not
/// mutable state and do not themselves read architectural registers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperandRef {
    /// Register-number operand.
    ///
    /// This evaluates to the architectural register identifier encoded by the
    /// instruction field, or to a fixed virtual/architectural register. Wrap it
    /// in `ReadRegister` to get the register's current value.
    RegisterField(RegisterRef),

    /// Immediate field operand.
    ///
    /// This evaluates to the raw decoded field bits, with width implied by the
    /// field definition in the matching instruction form.
    ImmediateField(FieldName),
}

/// Source for a register identifier used by `OperandRef::RegisterField`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegisterRef {
    /// A fixed architectural or virtual register identifier.
    ///
    /// `width` is the width of the register identifier expression, not
    /// necessarily the width of the register's stored value.
    Fixed { register: Register, width: u16 },

    /// A register identifier decoded from an instruction field.
    FromField(FieldName),
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
    /// Conditionally write an architectural or virtual register.
    ///
    /// `guard` is a 1-bit boolean expression; if false, the write does not
    /// happen. `register` evaluates to the register identifier to update.
    /// `value` is the bit-vector written to that register.
    WriteRegister {
        guard: Expr,
        register: Expr,
        value: Expr,
    },

    /// Conditionally write memory.
    ///
    /// `guard` is a 1-bit boolean expression; if false, the write does not
    /// happen. `address` is a byte address. `value` supplies the data bits, and
    /// `width` is the number of memory bits written.
    WriteMemory {
        guard: Expr,
        address: Expr,
        value: Expr,
        width: u16,
    },
}

impl Effect {
    pub fn write_register(register: Expr, value: Expr) -> Self {
        Self::WriteRegister {
            guard: bool_const(true),
            register,
            value,
        }
    }

    pub fn write_register_if(guard: Expr, register: Expr, value: Expr) -> Self {
        Self::WriteRegister {
            guard,
            register,
            value,
        }
    }

    pub fn write_memory(address: Expr, value: Expr, width: u16) -> Self {
        Self::WriteMemory {
            guard: bool_const(true),
            address,
            value,
            width,
        }
    }

    pub fn write_memory_if(guard: Expr, address: Expr, value: Expr, width: u16) -> Self {
        Self::WriteMemory {
            guard,
            address,
            value,
            width,
        }
    }
}

pub fn field_name(name: &str) -> FieldName {
    name.to_owned()
}

pub fn constant(value: u128, width: u16) -> Expr {
    Expr::Const { value, width }
}

pub fn bool_const(value: bool) -> Expr {
    constant(value as u128, 1)
}

pub fn immediate_field(name: &str) -> Expr {
    Expr::Operand(OperandRef::ImmediateField(field_name(name)))
}

pub fn derived_value(name: &str) -> Expr {
    Expr::DerivedValue(ValueName(name.to_owned()))
}

/// Produces an expression representing the register number contained in
/// an instruction field. It does not read that register.
pub fn register_field(name: &str) -> Expr {
    Expr::Operand(OperandRef::RegisterField(RegisterRef::FromField(
        field_name(name),
    )))
}

/// Produces an expression representing a fixed architectural or virtual register.
pub fn fixed_register(register: Register, width: u16) -> Expr {
    Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
        register,
        width,
    }))
}

pub fn read_register(register: Expr) -> Expr {
    Expr::ReadRegister(Box::new(register))
}

pub fn read_memory(address: Expr, width: u16) -> Expr {
    Expr::ReadMemory {
        address: Box::new(address),
        width,
    }
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

pub fn unsigned_less_than(lhs: Expr, rhs: Expr) -> Expr {
    Expr::UnsignedLessThan(Box::new(lhs), Box::new(rhs))
}

pub fn signed_less_than(lhs: Expr, rhs: Expr) -> Expr {
    Expr::SignedLessThan(Box::new(lhs), Box::new(rhs))
}

pub fn add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Add(Box::new(lhs), Box::new(rhs))
}

pub fn sub(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Sub(Box::new(lhs), Box::new(rhs))
}

pub fn mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Mul(Box::new(lhs), Box::new(rhs))
}

pub fn and_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::And(Box::new(lhs), Box::new(rhs))
}

pub fn or_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Or(Box::new(lhs), Box::new(rhs))
}

pub fn xor_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Xor(Box::new(lhs), Box::new(rhs))
}

pub fn not_expr(value: Expr) -> Expr {
    Expr::Not(Box::new(value))
}

pub fn shift_left(value: Expr, amount: Expr) -> Expr {
    Expr::ShiftLeft(Box::new(value), Box::new(amount))
}

pub fn logical_shift_right(value: Expr, amount: Expr) -> Expr {
    Expr::LogicalShiftRight(Box::new(value), Box::new(amount))
}

pub fn arithmetic_shift_right(value: Expr, amount: Expr) -> Expr {
    Expr::ArithmeticShiftRight(Box::new(value), Box::new(amount))
}

pub fn rotate_right(value: Expr, amount: Expr) -> Expr {
    Expr::RotateRight(Box::new(value), Box::new(amount))
}

pub fn extract(value: Expr, high: u16, low: u16) -> Expr {
    Expr::Extract {
        value: Box::new(value),
        high,
        low,
    }
}

pub fn concat(values: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::Concat(values.into_iter().collect())
}

pub fn zero_extend(value: Expr, to_width: u16) -> Expr {
    Expr::ZeroExtend {
        value: Box::new(value),
        to_width,
    }
}

pub fn sign_extend(value: Expr, to_width: u16) -> Expr {
    Expr::SignExtend {
        value: Box::new(value),
        to_width,
    }
}

pub fn count_ones(value: Expr) -> Expr {
    Expr::CountOnes(Box::new(value))
}

pub fn add_carry_out(lhs: Expr, rhs: Expr, carry_in: Expr, width: u16) -> Expr {
    Expr::AddCarryOut {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        carry_in: Box::new(carry_in),
        width,
    }
}

pub fn add_overflow(lhs: Expr, rhs: Expr, carry_in: Expr, width: u16) -> Expr {
    Expr::AddOverflow {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        carry_in: Box::new(carry_in),
        width,
    }
}

pub fn sub_carry_out(lhs: Expr, rhs: Expr, borrow_in: Expr, width: u16) -> Expr {
    Expr::SubCarryOut {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        borrow_in: Box::new(borrow_in),
        width,
    }
}

pub fn sub_overflow(lhs: Expr, rhs: Expr, borrow_in: Expr, width: u16) -> Expr {
    Expr::SubOverflow {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        borrow_in: Box::new(borrow_in),
        width,
    }
}

pub fn select(condition: Expr, when_true: Expr, when_false: Expr) -> Expr {
    Expr::Select {
        condition: Box::new(condition),
        when_true: Box::new(when_true),
        when_false: Box::new(when_false),
    }
}

pub fn field_is(name: &str, value: u128, width: u16) -> Expr {
    equal(immediate_field(name), constant(value, width))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bit::BitPattern,
        isa_specification::{
            DerivedValue as IsaDerivedValue, Instruction, InstructionField, InstructionForm,
        },
    };

    fn empty_instruction() -> DecodedInstruction {
        DecodedInstruction {
            name: Some("test".to_owned()),
            form: Some(InstructionForm::new("test")),
            bits: Vec::new(),
            fields: Vec::new(),
        }
    }

    fn decoded_fixture_instruction() -> DecodedInstruction {
        let instruction = Instruction::new("fixture", 8).form(
            InstructionForm::new("imm_form")
                .field(InstructionField::constant("10"))
                .field(InstructionField::variable("rd", 2).merge_mode_uses())
                .field(InstructionField::variable("imm", 4))
                .derived_value(IsaDerivedValue {
                    name: ValueName("expanded".to_owned()),
                    value: add(zero_extend(immediate_field("imm"), 8), constant(1, 8)),
                })
                .derived_value(IsaDerivedValue {
                    name: ValueName("doubled".to_owned()),
                    value: shift_left(derived_value("expanded"), constant(1, 8)),
                }),
        );
        let bits = BitPattern::parse("10110101");
        instruction
            .find_match(&bits.bits)
            .expect("fixture instruction should decode")
    }

    #[test]
    fn collapse_signed_operations_use_declared_width() {
        let instruction = empty_instruction();

        assert_eq!(
            arithmetic_shift_right(constant(0xff, 8), constant(1, 8)).collapse(&instruction),
            constant(0xff, 8)
        );
        assert_eq!(
            signed_less_than(constant(0xff, 8), constant(0x00, 8)).collapse(&instruction),
            bool_const(true)
        );
        assert_eq!(
            signed_less_than(constant(0x7f, 8), constant(0xff, 8)).collapse(&instruction),
            bool_const(false)
        );
    }

    #[test]
    fn collapse_extract_concat_and_large_shifts() {
        let instruction = empty_instruction();

        assert_eq!(
            extract(constant(0xabcd, 16), 11, 4).collapse(&instruction),
            constant(0xbc, 8)
        );
        assert_eq!(
            concat([constant(0xa, 4), constant(0xbc, 8)]).collapse(&instruction),
            constant(0xabc, 12)
        );
        assert_eq!(
            shift_left(constant(1, 8), constant(8, 8)).collapse(&instruction),
            constant(0, 8)
        );
        assert_eq!(
            logical_shift_right(constant(0x80, 8), constant(8, 8)).collapse(&instruction),
            constant(0, 8)
        );
        assert_eq!(
            arithmetic_shift_right(constant(0x80, 8), constant(8, 8)).collapse(&instruction),
            constant(0xff, 8)
        );
    }

    #[test]
    fn collapse_flag_helpers_fold_constants() {
        let instruction = empty_instruction();

        assert_eq!(
            add_carry_out(constant(0xff, 8), constant(0x00, 8), bool_const(true), 8)
                .collapse(&instruction),
            bool_const(true)
        );
        assert_eq!(
            add_overflow(constant(0x7f, 8), constant(0x00, 8), bool_const(true), 8)
                .collapse(&instruction),
            bool_const(true)
        );
        assert_eq!(
            sub_carry_out(constant(0x00, 8), constant(0x01, 8), bool_const(false), 8)
                .collapse(&instruction),
            bool_const(false)
        );
        assert_eq!(
            sub_overflow(constant(0x80, 8), constant(0x00, 8), bool_const(true), 8)
                .collapse(&instruction),
            bool_const(true)
        );
    }

    #[test]
    fn collapse_decoded_instruction_fields_and_derived_values() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            immediate_field("imm").collapse(&instruction),
            constant(5, 4)
        );
        assert_eq!(
            register_field("rd").collapse(&instruction),
            fixed_register(Register(3), 2)
        );
        assert_eq!(
            derived_value("expanded").collapse(&instruction),
            constant(6, 8)
        );
        assert_eq!(
            derived_value("doubled").collapse(&instruction),
            constant(12, 8)
        );
        assert_eq!(
            select(
                field_is("rd", 3, 2),
                derived_value("doubled"),
                constant(0, 8)
            )
            .collapse(&instruction),
            constant(12, 8)
        );
    }

    #[test]
    fn collapse_decoded_instruction_register_and_memory_wrappers() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            read_register(register_field("rd")).collapse(&instruction),
            read_register(fixed_register(Register(3), 2))
        );
        assert_eq!(
            read_memory(
                add(zero_extend(immediate_field("imm"), 32), constant(4, 32)),
                16
            )
            .collapse(&instruction),
            read_memory(constant(9, 32), 16)
        );
    }

    #[test]
    fn collapse_preserves_nonconstant_structure_with_collapsed_children() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            concat([
                constant(0xa, 4),
                read_register(register_field("rd")),
                constant(0x3, 2),
                constant(0x2, 2),
            ])
            .collapse(&instruction),
            concat([
                constant(0xa, 4),
                read_register(fixed_register(Register(3), 2)),
                constant(0xe, 4),
            ])
        );
        assert_eq!(
            select(
                read_register(register_field("rd")),
                derived_value("expanded"),
                sub(constant(0, 8), constant(1, 8)),
            )
            .collapse(&instruction),
            select(
                read_register(fixed_register(Register(3), 2)),
                constant(6, 8),
                constant(0xff, 8),
            )
        );
    }

    #[test]
    fn collapse_canonicalizes_constants_inside_operations() {
        let instruction = empty_instruction();

        assert_eq!(
            equal(constant(0x1ff, 8), constant(0xff, 8)).collapse(&instruction),
            bool_const(true)
        );
        assert_eq!(
            add(constant(0xff, 8), constant(2, 8)).collapse(&instruction),
            constant(1, 8)
        );
        assert_eq!(
            sub(constant(0, 8), constant(1, 8)).collapse(&instruction),
            constant(0xff, 8)
        );
        assert_eq!(
            mul(constant(0x10, 8), constant(0x10, 8)).collapse(&instruction),
            constant(0, 8)
        );
        assert_eq!(
            not_expr(constant(0x1f, 4)).collapse(&instruction),
            constant(0, 4)
        );
        assert_eq!(
            count_ones(constant(0x1ff, 8)).collapse(&instruction),
            constant(8, 8)
        );
    }

    #[test]
    fn collapse_bitwise_comparisons_and_rotates() {
        let instruction = empty_instruction();

        assert_eq!(
            and_expr(constant(0xf0, 8), constant(0x3c, 8)).collapse(&instruction),
            constant(0x30, 8)
        );
        assert_eq!(
            or_expr(constant(0xf0, 8), constant(0x0f, 8)).collapse(&instruction),
            constant(0xff, 8)
        );
        assert_eq!(
            xor_expr(constant(0xaa, 8), constant(0xff, 8)).collapse(&instruction),
            constant(0x55, 8)
        );
        assert_eq!(
            unsigned_less_than(constant(0x100, 8), constant(1, 8)).collapse(&instruction),
            bool_const(true)
        );
        assert_eq!(
            rotate_right(constant(0x96, 8), constant(12, 8)).collapse(&instruction),
            constant(0x69, 8)
        );
    }

    #[test]
    fn collapse_128_bit_edge_cases() {
        let instruction = empty_instruction();
        let sign_bit = 1u128 << 127;

        assert_eq!(
            add(constant(!0u128, 128), constant(1, 128)).collapse(&instruction),
            constant(0, 128)
        );
        assert_eq!(
            sub(constant(0, 128), constant(1, 128)).collapse(&instruction),
            constant(!0u128, 128)
        );
        assert_eq!(
            add_carry_out(
                constant(!0u128, 128),
                constant(0, 128),
                bool_const(true),
                128
            )
            .collapse(&instruction),
            bool_const(true)
        );
        assert_eq!(
            shift_left(constant(1, 128), constant(128, 128)).collapse(&instruction),
            constant(0, 128)
        );
        assert_eq!(
            logical_shift_right(constant(!0u128, 128), constant(128, 128)).collapse(&instruction),
            constant(0, 128)
        );
        assert_eq!(
            arithmetic_shift_right(constant(sign_bit, 128), constant(128, 128))
                .collapse(&instruction),
            constant(!0u128, 128)
        );
        assert_eq!(
            rotate_right(constant(1, 128), constant(127, 128)).collapse(&instruction),
            constant(2, 128)
        );
    }

    #[test]
    fn collapse_extend_and_count_ones_constants() {
        let instruction = empty_instruction();

        assert_eq!(
            zero_extend(constant(0x1ff, 8), 16).collapse(&instruction),
            constant(0x00ff, 16)
        );
        assert_eq!(
            sign_extend(constant(0x80, 8), 16).collapse(&instruction),
            constant(0xff80, 16)
        );
        assert_eq!(
            sign_extend(constant(0x7f, 8), 16).collapse(&instruction),
            constant(0x007f, 16)
        );
        assert_eq!(
            count_ones(constant(0b1010_1100, 8)).collapse(&instruction),
            constant(4, 8)
        );
    }

    #[test]
    fn collapse_assoc_comm_add_folds_nested_constants_preserving_term_order() {
        let instruction = empty_instruction();
        let x = read_register(fixed_register(Register(1), 4));
        let y = read_register(fixed_register(Register(2), 4));

        assert_eq!(
            add(
                add(x.clone(), constant(2, 8)),
                add(constant(3, 8), y.clone())
            )
            .collapse(&instruction),
            add(add(x, y), constant(5, 8))
        );
        assert_eq!(
            add(
                add(constant(250, 8), constant(10, 8)),
                read_fixed_register(Register(3), 4)
            )
            .collapse(&instruction),
            add(read_fixed_register(Register(3), 4), constant(4, 8))
        );
    }

    #[test]
    fn collapse_assoc_comm_multiplication_folds_identities_and_annihilators() {
        let instruction = empty_instruction();
        let x = read_register(fixed_register(Register(1), 4));

        assert_eq!(
            mul(mul(x.clone(), constant(3, 8)), constant(5, 8)).collapse(&instruction),
            mul(x.clone(), constant(15, 8))
        );
        assert_eq!(
            mul(mul(x.clone(), constant(1, 8)), constant(1, 8)).collapse(&instruction),
            x.clone()
        );
        assert_eq!(
            mul(add(x, constant(2, 8)), constant(0, 8)).collapse(&instruction),
            constant(0, 8)
        );
    }

    #[test]
    fn collapse_assoc_comm_bitwise_ops_fold_identities_and_annihilators() {
        let instruction = empty_instruction();
        let x = read_register(fixed_register(Register(1), 4));
        let y = read_register(fixed_register(Register(2), 4));

        assert_eq!(
            and_expr(and_expr(x.clone(), constant(0xff, 8)), y.clone()).collapse(&instruction),
            and_expr(x.clone(), y.clone())
        );
        assert_eq!(
            and_expr(or_expr(x.clone(), constant(1, 8)), constant(0, 8)).collapse(&instruction),
            constant(0, 8)
        );
        assert_eq!(
            or_expr(or_expr(x.clone(), constant(0, 8)), constant(0xff, 8)).collapse(&instruction),
            constant(0xff, 8)
        );
        assert_eq!(
            xor_expr(
                xor_expr(x.clone(), constant(0b1010, 8)),
                constant(0b1100, 8)
            )
            .collapse(&instruction),
            xor_expr(x.clone(), constant(0b0110, 8))
        );
        assert_eq!(
            xor_expr(xor_expr(x, constant(0b1010, 8)), constant(0b1010, 8)).collapse(&instruction),
            read_register(fixed_register(Register(1), 4))
        );
    }

    #[test]
    fn collapse_assoc_comm_simplifies_decoded_instruction_terms() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            add(
                add(
                    zero_extend(immediate_field("imm"), 8),
                    read_register(register_field("rd"))
                ),
                add(constant(9, 8), constant(1, 8)),
            )
            .collapse(&instruction),
            add(
                read_register(fixed_register(Register(3), 2)),
                constant(15, 8)
            )
        );
        assert_eq!(
            xor_expr(
                xor_expr(
                    derived_value("expanded"),
                    read_register(register_field("rd"))
                ),
                constant(6, 8),
            )
            .collapse(&instruction),
            read_register(fixed_register(Register(3), 2))
        );
    }

    #[test]
    fn collapse_assoc_comm_does_not_rewrite_non_commutative_ops() {
        let instruction = empty_instruction();
        let x = read_register(fixed_register(Register(1), 4));

        assert_eq!(
            sub(add(x.clone(), constant(2, 8)), constant(1, 8)).collapse(&instruction),
            sub(add(x.clone(), constant(2, 8)), constant(1, 8))
        );
        assert_eq!(
            shift_left(add(x.clone(), constant(2, 8)), constant(1, 8)).collapse(&instruction),
            shift_left(add(x, constant(2, 8)), constant(1, 8))
        );
    }

    #[test]
    #[should_panic(expected = "Width of operands for binary operation must match")]
    fn collapse_assoc_comm_rejects_mismatched_constant_widths() {
        let instruction = empty_instruction();

        add(
            add(read_fixed_register(Register(1), 4), constant(1, 8)),
            constant(1, 16),
        )
        .collapse(&instruction);
    }

    #[test]
    fn canonicalize_sorts_and_folds_associative_commutative_terms() {
        let x = read_fixed_register(Register(1), 4);
        let y = read_fixed_register(Register(2), 4);

        let expr_1 = add(y.clone(), add(constant(2, 8), x.clone())).canonicalize();
        let expr_2 = add(add(x.clone(), y.clone()), constant(2, 8)).canonicalize();

        assert_eq!(expr_1, expr_2);
        assert_eq!(expr_1, add(add(x, y), constant(2, 8)));
        assert_eq!(
            add(
                add(constant(250, 8), constant(10, 8)),
                read_fixed_register(Register(3), 4)
            )
            .canonicalize(),
            add(read_fixed_register(Register(3), 4), constant(4, 8))
        );
    }

    #[test]
    fn collapse_and_canonicalize_resolves_instruction_fields_before_normalizing() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            add(
                read_register(register_field("rd")),
                add(
                    add(constant(4, 8), zero_extend(immediate_field("imm"), 8)),
                    constant(6, 8),
                ),
            )
            .collapse_and_canonicalize(&instruction),
            add(
                read_register(fixed_register(Register(3), 2)),
                constant(15, 8)
            )
        );
    }

    #[test]
    fn canonicalize_bitwise_deduplicates_and_cancels_terms() {
        let x = fixed_register(Register(1), 4);
        let y = fixed_register(Register(2), 4);

        assert_eq!(
            and_expr(y.clone(), and_expr(x.clone(), x.clone())).canonicalize(),
            and_expr(x.clone(), y.clone())
        );
        assert_eq!(
            or_expr(y.clone(), or_expr(x.clone(), x.clone())).canonicalize(),
            or_expr(x.clone(), y.clone())
        );
        assert_eq!(
            xor_expr(x.clone(), x.clone()).canonicalize(),
            constant(0, 4)
        );
        assert_eq!(
            xor_expr(y.clone(), xor_expr(x.clone(), x.clone())).canonicalize(),
            y
        );
    }

    #[test]
    fn canonicalize_keeps_uncertain_width_xor_cancellation_safe() {
        let x = read_fixed_register(Register(1), 4);

        assert_eq!(
            xor_expr(x.clone(), x.clone()).canonicalize(),
            xor_expr(x.clone(), x)
        );
    }

    #[test]
    fn canonicalize_identities_annihilators_and_local_rules() {
        let x = read_fixed_register(Register(1), 4);

        assert_eq!(add(x.clone(), constant(0, 8)).canonicalize(), x.clone());
        assert_eq!(mul(x.clone(), constant(1, 8)).canonicalize(), x.clone());
        assert_eq!(
            mul(x.clone(), constant(0, 8)).canonicalize(),
            constant(0, 8)
        );
        assert_eq!(
            and_expr(x.clone(), constant(0, 8)).canonicalize(),
            constant(0, 8)
        );
        assert_eq!(
            or_expr(x.clone(), constant(0xff, 8)).canonicalize(),
            constant(0xff, 8)
        );
        assert_eq!(sub(x.clone(), constant(0, 8)).canonicalize(), x.clone());
        assert_eq!(not_expr(not_expr(x.clone())).canonicalize(), x.clone());
        assert_eq!(
            shift_left(x.clone(), constant(0, 8)).canonicalize(),
            x.clone()
        );
        assert_eq!(
            logical_shift_right(constant(0, 8), x.clone()).canonicalize(),
            constant(0, 8)
        );
        assert_eq!(rotate_right(x.clone(), constant(0, 8)).canonicalize(), x);
    }

    #[test]
    fn canonicalize_comparisons_and_selects() {
        let x = read_fixed_register(Register(1), 4);
        let y = read_fixed_register(Register(2), 4);

        assert_eq!(
            equal(y.clone(), x.clone()).canonicalize(),
            equal(x.clone(), y.clone()).canonicalize()
        );
        assert_eq!(equal(x.clone(), x.clone()).canonicalize(), bool_const(true));
        assert_eq!(
            unsigned_less_than(x.clone(), x.clone()).canonicalize(),
            bool_const(false)
        );
        assert_eq!(
            signed_less_than(x.clone(), x.clone()).canonicalize(),
            bool_const(false)
        );
        assert_eq!(
            select(bool_const(true), x.clone(), y.clone()).canonicalize(),
            x.clone()
        );
        assert_eq!(
            select(read_fixed_register(Register(3), 4), x.clone(), x.clone()).canonicalize(),
            x
        );
    }

    #[test]
    fn canonicalize_width_changing_and_structural_ops() {
        let instruction = empty_instruction();
        let x = fixed_register(Register(1), 8);

        assert_eq!(extract(x.clone(), 7, 0).canonicalize(), x.clone());
        assert_eq!(
            extract(constant(0xabcd, 16), 11, 4).collapse_and_canonicalize(&instruction),
            constant(0xbc, 8)
        );
        assert_eq!(
            concat([
                constant(0xa, 4),
                read_fixed_register(Register(1), 4),
                constant(0x3, 2),
                constant(0x2, 2),
            ])
            .canonicalize(),
            concat([
                constant(0xa, 4),
                read_fixed_register(Register(1), 4),
                constant(0xe, 4),
            ])
        );
        assert_eq!(
            zero_extend(fixed_register(Register(2), 8), 8).canonicalize(),
            fixed_register(Register(2), 8)
        );
        assert_eq!(
            sign_extend(sign_extend(fixed_register(Register(2), 8), 16), 32).canonicalize(),
            sign_extend(fixed_register(Register(2), 8), 32)
        );
        assert_eq!(
            count_ones(constant(0b1010_1100, 8)).collapse_and_canonicalize(&instruction),
            constant(4, 8)
        );
    }

    #[test]
    fn canonicalize_recurses_through_effect_helper_expressions() {
        let x = read_fixed_register(Register(1), 4);

        assert_eq!(
            add_carry_out(
                add(x.clone(), constant(0, 8)),
                constant(0xff, 8),
                bool_const(true),
                8
            )
            .canonicalize(),
            add_carry_out(x.clone(), constant(0xff, 8), bool_const(true), 8)
        );
        assert_eq!(
            sub_overflow(
                sub(x.clone(), constant(0, 8)),
                constant(0x80, 8),
                bool_const(false),
                8
            )
            .canonicalize(),
            sub_overflow(x, constant(0x80, 8), bool_const(false), 8)
        );
    }
}
