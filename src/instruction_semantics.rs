use crate::{
    instruction_semantics::OperandRef::{ImmediateField, RegisterField},
    isa_specification::DecodedInstruction,
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
/// Fixed-width arithmetic, logical, comparison, and shift operators require
/// equal operand widths. Exceptions are explicitly modeled: concatenation
/// combines different widths, `Select` has a 1-bit condition plus equal-width
/// result arms, and carry/borrow helpers have a separate 1-bit flag input.
/// Some width errors are detected only after fields have been collapsed.
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
    /// `register` evaluates to a register identifier, commonly an
    /// `Operand(RegisterField(_))` or a fixed virtual register. `width` is the
    /// width of the value read from that register, not the width of the register
    /// identifier expression. Register reads are part of the pre-instruction
    /// state; effects describe writes separately.
    ReadRegister { register: Box<Expr>, width: u16 },

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
/// Associative and commutative operators supported by shared normalization.
enum AssocCommOp {
    Add,
    Mul,
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, Debug)]
/// Carry/overflow helper variants sharing collapse and rebuild behavior.
enum FlagOp {
    AddCarryOut,
    AddOverflow,
    SubCarryOut,
    SubOverflow,
}

#[derive(Clone, Copy, Debug)]
/// Width-extension variants sharing validation and constant folding.
enum ExtensionOp {
    Zero,
    Sign,
}

impl ExtensionOp {
    /// Constructs the extension node represented by this operation.
    fn build(self, value: Expr, to_width: u16) -> Expr {
        match self {
            Self::Zero => zero_extend(value, to_width),
            Self::Sign => sign_extend(value, to_width),
        }
    }

    /// Returns the user-facing operation name used in validation errors.
    fn name(self) -> &'static str {
        match self {
            Self::Zero => "Zero extension",
            Self::Sign => "Sign extension",
        }
    }

    /// Evaluates this extension on a constant input.
    fn fold(self, value: u128, from_width: u16, to_width: u16) -> u128 {
        match self {
            Self::Zero => Expr::zero_extend_const(value, from_width, to_width),
            Self::Sign => Expr::sign_extend_const(value, from_width, to_width),
        }
    }

    /// Removes one nested extension of the same kind.
    fn strip_nested(self, value: Expr) -> Expr {
        match (self, value) {
            (Self::Zero, Expr::ZeroExtend { value, .. })
            | (Self::Sign, Expr::SignExtend { value, .. }) => *value,
            (_, value) => value,
        }
    }
}

impl FlagOp {
    /// Constructs the AST node represented by this flag operation.
    fn build(self, lhs: Expr, rhs: Expr, flag_in: Expr, width: u16) -> Expr {
        match self {
            Self::AddCarryOut => add_carry_out(lhs, rhs, flag_in, width),
            Self::AddOverflow => add_overflow(lhs, rhs, flag_in, width),
            Self::SubCarryOut => sub_carry_out(lhs, rhs, flag_in, width),
            Self::SubOverflow => sub_overflow(lhs, rhs, flag_in, width),
        }
    }

    /// Returns the operation name used in validation errors.
    fn name(self) -> &'static str {
        match self {
            Self::AddCarryOut => "AddCarryOut",
            Self::AddOverflow => "AddOverflow",
            Self::SubCarryOut => "SubCarryOut",
            Self::SubOverflow => "SubOverflow",
        }
    }

    /// Returns the public name of the 1-bit input consumed by this operation.
    fn flag_name(self) -> &'static str {
        match self {
            Self::AddCarryOut | Self::AddOverflow => "carry_in",
            Self::SubCarryOut | Self::SubOverflow => "borrow_in",
        }
    }

    /// Evaluates this flag operation on canonical constant operands.
    fn fold(self, lhs: u128, rhs: u128, flag_in: u128, width: u16) -> bool {
        match self {
            Self::AddCarryOut => Expr::add_carry_out_const(lhs, rhs, flag_in, width),
            Self::AddOverflow => Expr::add_overflow_const(lhs, rhs, flag_in, width),
            Self::SubCarryOut => Expr::sub_carry_out_const(lhs, rhs, flag_in, width),
            Self::SubOverflow => Expr::sub_overflow_const(lhs, rhs, flag_in, width),
        }
    }
}

impl Expr {
    /// Panics unless `width` is representable by the `u128` evaluator.
    fn assert_valid_width(width: u16) {
        if width == 0 || width > 128 {
            panic!("Bit-vector width must be in 1..=128, got {width}");
        }
    }

    /// Returns a mask with the low `width` bits set.
    fn bit_mask(width: u16) -> u128 {
        Self::assert_valid_width(width);
        if width == 128 {
            !0u128
        } else {
            (1u128 << width) - 1
        }
    }

    /// Returns the most-significant bit mask for a value of `width` bits.
    fn sign_bit(width: u16) -> u128 {
        Self::assert_valid_width(width);
        1u128 << (width - 1)
    }

    /// Truncates `value` to the requested bit-vector width.
    fn canonical(value: u128, width: u16) -> u128 {
        value & Self::bit_mask(width)
    }

    /// Constructs a width-validated constant truncated to `width` bits.
    fn const_bits(value: u128, width: u16) -> Self {
        Expr::Const {
            value: Self::canonical(value, width),
            width,
        }
    }

    /// Validates equal nonzero operand widths and returns the shared width.
    fn expect_same_width(lhs_width: u16, rhs_width: u16) -> u16 {
        if lhs_width != rhs_width {
            panic!(
                "Width of operands for binary operation must match. Consider explicitly defining how to sign extend operands in the semantics."
            );
        }
        Self::assert_valid_width(lhs_width);
        lhs_width
    }

    /// Validates a boolean constant and returns its canonical 0/1 value.
    fn expect_bool_const(value: u128, width: u16, name: &str) -> u128 {
        if width != 1 {
            panic!("{name} must have width 1, got width = {width}");
        }
        Self::canonical(value, width)
    }

    /// Sign-extends a width-limited value across all 128 host bits.
    ///
    /// This is an evaluator helper; it does not change an expression's
    /// architectural width.
    fn sign_extend_to_u128(value: u128, width: u16) -> u128 {
        let value = Self::canonical(value, width);
        if value & Self::sign_bit(width) == 0 {
            value
        } else {
            value | !Self::bit_mask(width)
        }
    }

    /// Interprets the low `width` bits of `value` as a signed integer.
    fn signed_value(value: u128, width: u16) -> i128 {
        Self::sign_extend_to_u128(value, width) as i128
    }

    /// Evaluates zero extension after validating that it does not shrink.
    fn zero_extend_const(value: u128, from_width: u16, to_width: u16) -> u128 {
        if from_width > to_width {
            panic!(
                "Zext to_width must be at least value width, but got width = {from_width} and to_width = {to_width}"
            );
        }
        Self::assert_valid_width(to_width);
        Self::canonical(value, from_width)
    }

    /// Evaluates sign extension after validating that it does not shrink.
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

    /// Evaluates a logical left shift, returning zero for oversized amounts.
    fn shift_left_const(value: u128, amount: u128, width: u16) -> u128 {
        if amount >= width as u128 {
            0
        } else {
            Self::canonical(value, width) << amount as u32
        }
    }

    /// Evaluates a logical right shift, returning zero for oversized amounts.
    fn logical_shift_right_const(value: u128, amount: u128, width: u16) -> u128 {
        if amount >= width as u128 {
            0
        } else {
            Self::canonical(value, width) >> amount as u32
        }
    }

    /// Evaluates an arithmetic right shift with sign fill.
    fn arithmetic_shift_right_const(value: u128, amount: u128, width: u16) -> u128 {
        let value = Self::canonical(value, width);
        let negative = value & Self::sign_bit(width) != 0;
        if amount >= width as u128 {
            if negative { Self::bit_mask(width) } else { 0 }
        } else {
            ((Self::sign_extend_to_u128(value, width) as i128) >> amount as u32) as u128
        }
    }

    /// Evaluates rotate-right with the amount reduced modulo `width`.
    fn rotate_right_const(value: u128, amount: u128, width: u16) -> u128 {
        let value = Self::canonical(value, width);
        let shift = (amount % width as u128) as u32;
        if shift == 0 {
            value
        } else {
            (value >> shift) | (value << (width as u32 - shift))
        }
    }

    /// Evaluates unsigned carry-out from `lhs + rhs + carry_in`.
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

    /// Evaluates architectural subtraction carry, meaning “no borrow.”
    fn sub_carry_out_const(lhs: u128, rhs: u128, borrow_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let borrow_in = Self::canonical(borrow_in, 1);
        let (diff, borrow1) = lhs.overflowing_sub(rhs);
        let (_, borrow2) = diff.overflowing_sub(borrow_in);
        !(borrow1 || borrow2)
    }

    /// Evaluates signed overflow from `lhs + rhs + carry_in`.
    fn add_overflow_const(lhs: u128, rhs: u128, carry_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let carry_in = Self::canonical(carry_in, 1);
        let result = Self::canonical(lhs.wrapping_add(rhs).wrapping_add(carry_in), width);
        (!(lhs ^ rhs) & (lhs ^ result) & Self::sign_bit(width)) != 0
    }

    /// Evaluates signed overflow from `lhs - rhs - borrow_in`.
    fn sub_overflow_const(lhs: u128, rhs: u128, borrow_in: u128, width: u16) -> bool {
        let lhs = Self::canonical(lhs, width);
        let rhs = Self::canonical(rhs, width);
        let borrow_in = Self::canonical(borrow_in, 1);
        let result = Self::canonical(lhs.wrapping_sub(rhs).wrapping_sub(borrow_in), width);
        ((lhs ^ rhs) & (lhs ^ result) & Self::sign_bit(width)) != 0
    }

    /// Constructs the binary expression associated with `op`.
    fn make_assoc_comm_expr(op: AssocCommOp, lhs: Expr, rhs: Expr) -> Self {
        match op {
            AssocCommOp::Add => Expr::Add(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::Mul => Expr::Mul(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::And => Expr::And(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::Or => Expr::Or(Box::new(lhs), Box::new(rhs)),
            AssocCommOp::Xor => Expr::Xor(Box::new(lhs), Box::new(rhs)),
        }
    }

    /// Appends the leaves of a same-operator associative tree to `terms`.
    ///
    /// This only flattens `op`; child expressions are otherwise left untouched.
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

    /// Evaluates one associative/commutative operation on two constants.
    fn fold_assoc_comm_const(op: AssocCommOp, lhs: u128, rhs: u128, _width: u16) -> u128 {
        match op {
            AssocCommOp::Add => lhs.wrapping_add(rhs),
            AssocCommOp::Mul => lhs.wrapping_mul(rhs),
            AssocCommOp::And => lhs & rhs,
            AssocCommOp::Or => lhs | rhs,
            AssocCommOp::Xor => lhs ^ rhs,
        }
    }

    /// Reports whether `value` is the neutral element for `op`.
    fn is_assoc_comm_identity(op: AssocCommOp, value: u128, width: u16) -> bool {
        match op {
            AssocCommOp::Add | AssocCommOp::Or | AssocCommOp::Xor => value == 0,
            AssocCommOp::Mul => value == 1,
            AssocCommOp::And => value == Self::bit_mask(width),
        }
    }

    /// Reports whether `value` determines the result of `op`.
    fn is_assoc_comm_annihilator(op: AssocCommOp, value: u128, width: u16) -> bool {
        match op {
            AssocCommOp::Mul | AssocCommOp::And => value == 0,
            AssocCommOp::Or => value == Self::bit_mask(width),
            AssocCommOp::Add | AssocCommOp::Xor => false,
        }
    }

    /// Rebuilds a nonempty left-associated tree from ordered terms.
    fn rebuild_assoc_comm_op(op: AssocCommOp, mut terms: Vec<Expr>) -> Self {
        let first = terms
            .drain(..1)
            .next()
            .expect("Associative/commutative operation must have at least one term");
        terms
            .into_iter()
            .fold(first, |acc, term| Self::make_assoc_comm_expr(op, acc, term))
    }

    /// Collapses an associative/commutative expression and combines constants.
    ///
    /// Unlike `canonicalize_assoc_comm_op`, this preserves the order of
    /// nonconstant terms and performs no sorting, deduplication, cancellation,
    /// complement, or absorption rewrites.
    fn collapse_assoc_comm_op(
        instruction: &DecodedInstruction,
        op1: Expr,
        op2: Expr,
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

    /// Collapses both operands of a binary node and folds a constant pair.
    ///
    /// `fold` receives canonical operand values and their shared width and must
    /// construct the complete replacement expression, including its result
    /// width. Nonconstant operands are rebuilt with `rebuild`.
    fn collapse_binary_op<F>(
        instruction: &DecodedInstruction,
        op1: Expr,
        op2: Expr,
        rebuild: fn(Box<Expr>, Box<Expr>) -> Expr,
        fold: F,
    ) -> Self
    where
        F: FnOnce(u128, u128, u16) -> Expr,
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
                fold(
                    Self::canonical(value_op1, width),
                    Self::canonical(value_op2, width),
                    width,
                )
            }
            (op1_collapsed, op2_collapsed) => {
                rebuild(Box::new(op1_collapsed), Box::new(op2_collapsed))
            }
        }
    }

    /// Collapses a unary node and folds it when its child is constant.
    fn collapse_unary_op<F>(
        instruction: &DecodedInstruction,
        op: Expr,
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

    /// Returns the statically known result width, if all required widths agree.
    ///
    /// This method does not resolve instruction fields or derived values.
    /// Call `collapse` first when width information comes from a decoded
    /// instruction.
    pub fn expr_width(&self) -> Option<u16> {
        match self {
            Expr::Const { width, .. } => Some(*width),
            Expr::Operand(RegisterField(RegisterRef::Fixed {
                identifier_width, ..
            })) => Some(*identifier_width),
            Expr::Operand(ImmediateField(_))
            | Expr::Operand(RegisterField(RegisterRef::FromField(_)))
            | Expr::DerivedValue(_) => None,
            Expr::ReadRegister { width, .. } => Some(*width),
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

    /// Produces a deterministic structural key used to order commutative terms.
    fn canonical_sort_key(expr: &Expr) -> String {
        format!("{expr:?}")
    }

    /// Rebuilds a concatenation while merging adjacent constant chunks.
    ///
    /// Inputs must already have undergone the caller's recursive transform
    /// (`collapse` or `canonicalize`). A single remaining chunk is returned
    /// directly; an empty input remains an empty `Concat`.
    fn rebuild_concat(values: impl IntoIterator<Item = Expr>) -> Self {
        let mut merged = Vec::new();
        for value in values {
            match value {
                Expr::Const { value, width } => {
                    Self::assert_valid_width(width);
                    if let Some(Expr::Const {
                        value: previous_value,
                        width: previous_width,
                    }) = merged.last_mut()
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
                        merged.push(Self::const_bits(value, width));
                    }
                }
                value => merged.push(value),
            }
        }

        match merged.len() {
            1 => merged.into_iter().next().expect("length was checked"),
            _ => Expr::Concat(merged),
        }
    }

    /// Canonicalizes a shift/rotate and removes zero-value identities.
    ///
    /// Both children are canonicalized first. A zero amount returns the input;
    /// a zero input returns a zero constant. Constant evaluation itself is done
    /// by `collapse`.
    fn canonicalize_shift_like_op(
        value: Expr,
        amount: Expr,
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

    /// Canonicalizes the three children of a flag expression and rebuilds it.
    ///
    /// This helper deliberately does not rewrite flag semantics; constant
    /// evaluation remains the responsibility of `collapse`.
    fn canonicalize_flag_expr(lhs: Expr, rhs: Expr, flag_in: Expr, width: u16, op: FlagOp) -> Self {
        op.build(
            lhs.canonicalize(),
            rhs.canonicalize(),
            flag_in.canonicalize(),
            width,
        )
    }

    /// Collapses and constant-folds a carry/overflow helper expression.
    ///
    /// All three children are collapsed first. Folding occurs only when both
    /// arithmetic operands and the 1-bit carry/borrow input are constants.
    fn collapse_flag_expr(
        instruction: &DecodedInstruction,
        lhs: Expr,
        rhs: Expr,
        flag_in: Expr,
        width: u16,
        op: FlagOp,
    ) -> Self {
        let collapsed = (
            lhs.collapse(instruction),
            rhs.collapse(instruction),
            flag_in.collapse(instruction),
        );

        match collapsed {
            (
                Expr::Const {
                    value: lhs,
                    width: lhs_width,
                },
                Expr::Const {
                    value: rhs,
                    width: rhs_width,
                },
                Expr::Const {
                    value: flag_in,
                    width: flag_width,
                },
            ) => {
                if Self::expect_same_width(lhs_width, rhs_width) != width {
                    panic!(
                        "LHS, RHS, and output must have equal width for {}",
                        op.name()
                    );
                }
                let flag_in = Self::expect_bool_const(flag_in, flag_width, op.flag_name());
                bool_const(op.fold(lhs, rhs, flag_in, width))
            }
            (lhs, rhs, flag_in) => op.build(lhs, rhs, flag_in, width),
        }
    }

    /// Canonicalizes an extension and removes redundant nesting.
    ///
    /// The child is canonicalized first. Equal-width extensions disappear,
    /// nested extensions of the same kind collapse to the outer width, and
    /// shrinking a statically known value is rejected.
    fn canonicalize_extension(value: Expr, to_width: u16, op: ExtensionOp) -> Self {
        let value = value.canonicalize();
        if let Some(value_width) = value.expr_width() {
            if value_width > to_width {
                panic!(
                    "{} target width must be at least value width, but got width = {value_width} and to_width = {to_width}",
                    op.name()
                );
            }
            if value_width == to_width {
                return value;
            }
        }

        op.build(op.strip_nested(value), to_width)
    }

    /// Collapses an extension and folds it when its child becomes constant.
    fn collapse_extension(
        instruction: &DecodedInstruction,
        value: Expr,
        to_width: u16,
        op: ExtensionOp,
    ) -> Self {
        match value.collapse(instruction) {
            Expr::Const { value, width } => {
                Self::const_bits(op.fold(value, width, to_width), to_width)
            }
            value => op.build(value, to_width),
        }
    }

    pub(crate) fn visit_children(&self, mut visit: impl FnMut(&Expr)) {
        match self {
            Expr::Const { .. } | Expr::Operand(_) | Expr::DerivedValue(_) => {}
            Expr::ReadRegister { register, .. } => visit(register),
            Expr::ReadMemory { address, .. } => visit(address),
            Expr::Add(lhs, rhs)
            | Expr::Sub(lhs, rhs)
            | Expr::Mul(lhs, rhs)
            | Expr::And(lhs, rhs)
            | Expr::Or(lhs, rhs)
            | Expr::Xor(lhs, rhs)
            | Expr::ShiftLeft(lhs, rhs)
            | Expr::LogicalShiftRight(lhs, rhs)
            | Expr::ArithmeticShiftRight(lhs, rhs)
            | Expr::RotateRight(lhs, rhs)
            | Expr::Equal(lhs, rhs)
            | Expr::UnsignedLessThan(lhs, rhs)
            | Expr::SignedLessThan(lhs, rhs) => {
                visit(lhs);
                visit(rhs);
            }
            Expr::Not(value) | Expr::CountOnes(value) => visit(value),
            Expr::Extract { value, .. }
            | Expr::ZeroExtend { value, .. }
            | Expr::SignExtend { value, .. } => visit(value),
            Expr::Concat(values) => {
                for value in values {
                    visit(value);
                }
            }
            Expr::AddCarryOut {
                lhs, rhs, carry_in, ..
            }
            | Expr::AddOverflow {
                lhs, rhs, carry_in, ..
            } => {
                visit(lhs);
                visit(rhs);
                visit(carry_in);
            }
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                ..
            }
            | Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                ..
            } => {
                visit(lhs);
                visit(rhs);
                visit(borrow_in);
            }
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                visit(condition);
                visit(when_true);
                visit(when_false);
            }
        }
    }

    /// Rebuilds this node after applying `map` to each immediate child.
    ///
    /// This is a one-level traversal: `map` decides whether and how to recurse.
    /// Leaf expressions are returned unchanged. Transformations that need
    /// special handling for a node must match that node before calling this
    /// helper.
    pub(crate) fn map_children(self, mut map: impl FnMut(Expr) -> Expr) -> Self {
        match self {
            Expr::Const { .. } | Expr::Operand(_) | Expr::DerivedValue(_) => self,
            Expr::ReadRegister { register, width } => read_register(map(*register), width),
            Expr::ReadMemory { address, width } => read_memory(map(*address), width),
            Expr::Add(lhs, rhs) => add(map(*lhs), map(*rhs)),
            Expr::Sub(lhs, rhs) => sub(map(*lhs), map(*rhs)),
            Expr::Mul(lhs, rhs) => mul(map(*lhs), map(*rhs)),
            Expr::And(lhs, rhs) => and_expr(map(*lhs), map(*rhs)),
            Expr::Or(lhs, rhs) => or_expr(map(*lhs), map(*rhs)),
            Expr::Xor(lhs, rhs) => xor_expr(map(*lhs), map(*rhs)),
            Expr::Not(value) => not_expr(map(*value)),
            Expr::ShiftLeft(value, amount) => shift_left(map(*value), map(*amount)),
            Expr::LogicalShiftRight(value, amount) => {
                logical_shift_right(map(*value), map(*amount))
            }
            Expr::ArithmeticShiftRight(value, amount) => {
                arithmetic_shift_right(map(*value), map(*amount))
            }
            Expr::RotateRight(value, amount) => rotate_right(map(*value), map(*amount)),
            Expr::Equal(lhs, rhs) => equal(map(*lhs), map(*rhs)),
            Expr::UnsignedLessThan(lhs, rhs) => unsigned_less_than(map(*lhs), map(*rhs)),
            Expr::SignedLessThan(lhs, rhs) => signed_less_than(map(*lhs), map(*rhs)),
            Expr::Extract { value, high, low } => extract(map(*value), high, low),
            Expr::Concat(values) => concat(values.into_iter().map(map)),
            Expr::ZeroExtend { value, to_width } => zero_extend(map(*value), to_width),
            Expr::SignExtend { value, to_width } => sign_extend(map(*value), to_width),
            Expr::CountOnes(value) => count_ones(map(*value)),
            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => add_carry_out(map(*lhs), map(*rhs), map(*carry_in), width),
            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => add_overflow(map(*lhs), map(*rhs), map(*carry_in), width),
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                width,
            } => sub_carry_out(map(*lhs), map(*rhs), map(*borrow_in), width),
            Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                width,
            } => sub_overflow(map(*lhs), map(*rhs), map(*borrow_in), width),
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => select(map(*condition), map(*when_true), map(*when_false)),
        }
    }

    /// Lowers `Or`, `Xor`, and `Select` into the primitive operator set.
    ///
    /// `Or` and `Xor` become combinations of `And` and `Not`. `Select`
    /// sign-extends its 1-bit condition into an all-zero/all-one mask and uses
    /// the same primitive operators. Call this only after child expressions and
    /// same-operator associative terms have been canonicalized.
    fn lower_operators(self) -> Self {
        match self {
            Expr::Or(lhs, rhs) => not_expr(and_expr(not_expr(*lhs), not_expr(*rhs))).canonicalize(),
            Expr::Xor(lhs, rhs) => or_expr(
                and_expr(*lhs.clone(), not_expr(*rhs.clone())),
                and_expr(not_expr(*lhs), *rhs),
            )
            .canonicalize(),
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                if let Some(condition_width) = condition.expr_width()
                    && condition_width != 1
                {
                    panic!(
                        "Expr::Select condition must have width 1, got width = {condition_width}"
                    );
                }
                let width_1 = when_true
                    .expr_width()
                    .expect("when_true should have valid width");
                let width_2 = when_false
                    .expr_width()
                    .expect("when_false should have valid width");
                let width = (width_1 == width_2).then_some(width_2).expect(
                    "Expr::Select -- both when_true and when_false should have matching width",
                );
                let cond_width = sign_extend(*condition, width);
                not_expr(and_expr(
                    not_expr(and_expr(not_expr(cond_width.clone()), *when_false)),
                    not_expr(and_expr(cond_width, *when_true)),
                ))
                .canonicalize()
            }
            expr => expr,
        }
    }

    /// Searches an `op` tree for a term equal to canonical `needle`.
    fn assoc_comm_expr_contains(op: AssocCommOp, expr: &Expr, needle: &Expr) -> bool {
        match (op, expr) {
            (AssocCommOp::Add, Expr::Add(lhs, rhs))
            | (AssocCommOp::Mul, Expr::Mul(lhs, rhs))
            | (AssocCommOp::And, Expr::And(lhs, rhs))
            | (AssocCommOp::Or, Expr::Or(lhs, rhs))
            | (AssocCommOp::Xor, Expr::Xor(lhs, rhs)) => {
                Self::assoc_comm_expr_contains(op, lhs, needle)
                    || Self::assoc_comm_expr_contains(op, rhs, needle)
            }
            (_, expr) => expr.clone().canonicalize() == *needle,
        }
    }

    /// Removes terms made redundant by Boolean absorption.
    ///
    /// For an outer `And`, this removes `x | ...` terms containing another
    /// top-level term `x`; for an outer `Or`, it analogously removes `x & ...`.
    /// This must run before nested `Or` nodes are lowered to `And`/`Not`.
    fn remove_absorbed_terms(op: AssocCommOp, terms: &mut Vec<Expr>) {
        let opposite_op = match op {
            AssocCommOp::And => AssocCommOp::Or,
            AssocCommOp::Or => AssocCommOp::And,
            AssocCommOp::Add | AssocCommOp::Mul | AssocCommOp::Xor => return,
        };

        let canonical_terms: Vec<_> = terms.iter().cloned().map(Expr::canonicalize).collect();
        let mut keep = vec![true; terms.len()];

        for (candidate_index, candidate) in terms.iter().enumerate() {
            if !matches!(
                (opposite_op, candidate),
                (AssocCommOp::And, Expr::And(_, _)) | (AssocCommOp::Or, Expr::Or(_, _))
            ) {
                continue;
            }

            for (needle_index, needle) in canonical_terms.iter().enumerate() {
                if candidate_index != needle_index
                    && Self::assoc_comm_expr_contains(opposite_op, candidate, needle)
                {
                    keep[candidate_index] = false;
                    break;
                }
            }
        }

        let mut index = 0;
        terms.retain(|_| {
            let retain = keep[index];
            index += 1;
            retain
        });
    }

    /// Fully canonicalizes an associative/commutative operation.
    ///
    /// The pass flattens before and after recursively canonicalizing children,
    /// folds constants, sorts terms, removes identities and annihilators,
    /// deduplicates `And`/`Or`, cancels even `Xor` multiplicities, applies
    /// complement laws, and performs Boolean absorption before logical
    /// lowering. Callers lower `Or`/`Xor` only after this returns.
    fn canonicalize_assoc_comm_op(op: AssocCommOp, lhs: Expr, rhs: Expr) -> Self {
        let mut terms = Vec::new();
        Self::flatten_assoc_comm_op(op, lhs, &mut terms);
        Self::flatten_assoc_comm_op(op, rhs, &mut terms);
        Self::remove_absorbed_terms(op, &mut terms);

        let mut canonicalized_terms = Vec::new();
        for term in terms {
            Self::flatten_assoc_comm_op(op, term.canonicalize(), &mut canonicalized_terms);
        }

        let mut non_const_terms = Vec::new();
        let mut folded_const: Option<(u128, u16)> = None;

        for term in canonicalized_terms {
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

        if matches!(op, AssocCommOp::And | AssocCommOp::Or)
            && non_const_terms.iter().enumerate().any(|(index, lhs)| {
                non_const_terms[index + 1..].iter().any(|rhs| {
                    matches!(lhs, Expr::Not(inner) if inner.as_ref() == rhs)
                        || matches!(rhs, Expr::Not(inner) if inner.as_ref() == lhs)
                })
            })
            && let Some(width) = non_const_terms
                .iter()
                .find_map(Expr::expr_width)
                .or_else(|| folded_const.map(|(_, width)| width))
        {
            return match op {
                AssocCommOp::And => Self::const_bits(0, width),
                AssocCommOp::Or => Self::const_bits(Self::bit_mask(width), width),
                _ => unreachable!(),
            };
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

    /// Resolves instruction-dependent values, then canonicalizes the result.
    pub fn collapse_and_canonicalize(self, instruction: &DecodedInstruction) -> Self {
        self.collapse(instruction).canonicalize()
    }

    /// Resolves the current instruction, substitutes prior state writes, then
    /// canonicalizes the resulting expression.
    ///
    /// `previous_effects` must already refer to collapsed expressions in the
    /// same state coordinate system. Substitution intentionally occurs before
    /// canonicalization so inserted `Select` nodes and arithmetic can reduce.
    pub fn collapse_substitute_and_canonicalize(
        self,
        instruction: &DecodedInstruction,
        previous_effects: &[Effect],
    ) -> Self {
        // previous_effects should already be collapsed, which means the collapse only needs to be run on the original Expr
        self.collapse(instruction)
            .substitute(previous_effects)
            .canonicalize()
    }

    /// Replaces register/memory reads with guarded forwarding from prior writes.
    ///
    /// Each read becomes a latest-write-wins select chain. A previous write is
    /// visible only when its guard is true and its destination identifier equals
    /// the read identifier. Newly inserted values are not recursively
    /// substituted. Run this once per instruction-composition step; applying it
    /// repeatedly to the same prior effects can repeatedly wrap the fallback
    /// read.
    pub fn substitute(self, previous_effects: &[Effect]) -> Self {
        match self {
            Expr::ReadRegister { register, width } => {
                let register = register.substitute(previous_effects);
                let mut forwarded = read_register(register.clone(), width);
                for effect in previous_effects {
                    if let Effect::WriteRegister {
                        guard,
                        register: write_register,
                        value,
                    } = effect
                        && value.expr_width() == Some(width)
                    {
                        forwarded = select(
                            and_expr(guard.clone(), equal(register.clone(), write_register.clone())),
                            value.clone(),
                            forwarded,
                        );
                    }
                }
                forwarded
            }
            Expr::ReadMemory { address, width } => {
                let address = address.substitute(previous_effects);
                let mut forwarded = read_memory(address.clone(), width);
                for effect in previous_effects {
                    if let Effect::WriteMemory {
                        guard,
                        address: write_address,
                        value,
                        width: write_width,
                    } = effect
                        && width == *write_width
                    {
                        forwarded = select(
                            and_expr(guard.clone(), equal(address.clone(), write_address.clone())),
                            value.clone(),
                            forwarded,
                        );
                    }
                }
                forwarded
            }
            expr => expr.map_children(|child| child.substitute(previous_effects)),
        }
    }

    /// Reduces multiplies, where one operand is a constant, to a combination of shift and add
    fn canonicalize_mul(self) -> Self {
        let width = self
            .expr_width()
            .expect("Multiply must have established width in decoded instruction");
        match self {
            Expr::Mul(lhs, rhs) => {
                match (*lhs, *rhs) {
                    // Both consts, reduce to const
                    (Expr::Const { value: value1, .. }, Expr::Const { value: value2, .. }) => {
                        constant((value1 * value2) & Expr::bit_mask(width), width)
                    }
                    (Expr::Const { value, .. }, expr2) => {
                        Self::mul_to_shift_add(expr2, value, constant(0, width), width)
                    }
                    (expr, Expr::Const { value, .. }) => {
                        Self::mul_to_shift_add(expr, value, constant(0, width), width)
                    }
                    (expr, expr2) => mul(expr, expr2),
                }
            }
            expr => expr,
        }
    }

    /// Given a variable term x (ie unknown) and a constant term a, convert x * a to
    /// a series of shifts and adds
    fn mul_to_shift_add(
        variable_term: Expr,
        constant_term: u128,
        accumulator: Expr,
        width: u16,
    ) -> Self {
        if constant_term == 0 {
            return accumulator.canonicalize();
        }

        let mut new_term = accumulator;
        // If the LSB of the constant term is 1, shifting it right by one
        // will result in a lost bit, so we need to add 1
        if constant_term & 1 == 1 {
            new_term = add(new_term, variable_term.clone());
        }

        // Now we will shift the variable term
        // If the variable term is already a shift, however, we can just add one to its shift value
        let new_variable_term = if let Expr::ShiftLeft(value, shift_amt) = variable_term {
            shift_left(*value, add(*shift_amt, constant(1, width)))
        } else {
            shift_left(variable_term, constant(1, width))
        };
        Self::mul_to_shift_add(new_variable_term, constant_term >> 1, new_term, width)
    }

    /// Recursively converts an expression to a deterministic reduced form.
    ///
    /// This pass does not resolve decoded fields or derived values and does not
    /// generally evaluate constant operations; call `collapse` first for those
    /// jobs. It normalizes associative operations, rewrites subtraction into
    /// addition, and lowers `Or`, `Xor`, and `Select` to `And`/`Not`.
    ///
    /// Handles the following identities:
    ///
    /// Associative/commutative normalization:
    /// - Flatten and sort nested `Add`, `Mul`, `And`, `Or`, and `Xor` terms.
    /// - Fold constant terms of the same width.
    ///
    /// Neutral elements:
    /// - `x + 0 = x`
    /// - `x * 1 = x`
    /// - `x & all_ones = x`
    /// - `x | 0 = x`
    /// - `x ^ 0 = x`
    /// - `x - 0 = x`
    ///
    /// Absorbing elements:
    /// - `x * 0 = 0`
    /// - `x & 0 = 0`
    /// - `x | all_ones = all_ones`
    ///
    /// Idempotence and cancellation:
    /// - `x & x = x`
    /// - `x | x = x`
    /// - `x ^ x = 0`
    /// - `x - x = 0`
    /// - `x & !x = 0`
    /// - `x | !x = all_ones`
    ///
    /// Absorption:
    /// - `x & (x | y) = x`
    /// - `x | (x & y) = x`
    ///
    /// Arithmetic and logical normalization:
    /// - `x - y = x + !y + 1`
    /// - `!!x = x`
    /// - Fold `!constant`
    ///
    /// Shift and rotate identities:
    /// - Shifting or rotating by zero returns the input.
    /// - Shifting or rotating zero returns zero.
    ///
    /// Comparisons and selection:
    /// - `x == x = true` (constant(1, 1))
    /// - `x < x = false` (constant(0, 1))
    /// - `select(true, x, y) = x`
    /// - `select(false, x, y) = y`
    /// - `select(c, x, x) = x`
    ///
    /// Width and structural identities:
    /// - Extracting x bits of a value of width x returns the value itself
    /// - Extending a value of with x to x bits returns the value itself
    /// - Collapse nested extensions and adjacent constant concatenation terms.
    ///
    /// Multiplication is currently limited to associative ordering, constant
    /// aggregation, and the `0`/`1` rules; it is not expanded into shifts/adds.
    pub fn canonicalize(self) -> Self {
        match self {
            Expr::Const { value, width } => Self::const_bits(value, width),
            Expr::Operand(_) | Expr::DerivedValue(_) => self,
            Expr::ReadRegister { register, width } => Expr::ReadRegister {
                register: Box::new(register.canonicalize()),
                width,
            },
            Expr::ReadMemory { address, width } => Expr::ReadMemory {
                address: Box::new(address.canonicalize()),
                width,
            },
            Expr::Add(lhs, rhs) => {
                Self::canonicalize_assoc_comm_op(AssocCommOp::Add, *lhs, *rhs).canonicalize_mul()
            }
            Expr::Sub(lhs, rhs) => {
                let lhs = lhs.canonicalize();
                let rhs = rhs.canonicalize();
                if matches!(
                    &rhs,
                    Expr::Const { value, width } if Self::canonical(*value, *width) == 0
                ) {
                    lhs
                } else if lhs == rhs {
                    let width = lhs
                        .expr_width()
                        .expect("canonicalized expression must have a known width");
                    Self::const_bits(0, width)
                } else {
                    let width = lhs
                        .expr_width()
                        .expect("canonicalized expression must have a known width");
                    add(add(lhs, not_expr(rhs)), constant(1, width)).canonicalize()
                }
            }
            Expr::Mul(lhs, rhs) => {
                Self::canonicalize_assoc_comm_op(AssocCommOp::Mul, *lhs, *rhs).canonicalize_mul()
            }
            Expr::And(lhs, rhs) => Self::canonicalize_assoc_comm_op(AssocCommOp::And, *lhs, *rhs),
            Expr::Or(lhs, rhs) => {
                Self::canonicalize_assoc_comm_op(AssocCommOp::Or, *lhs, *rhs).lower_operators()
            }
            Expr::Xor(lhs, rhs) => {
                Self::canonicalize_assoc_comm_op(AssocCommOp::Xor, *lhs, *rhs).lower_operators()
            }
            Expr::Not(value) => match value.canonicalize() {
                Expr::Const { value, width } => Self::const_bits(!value, width),
                Expr::Not(inner) => *inner,
                value => Expr::Not(Box::new(value)),
            },
            Expr::ShiftLeft(value, amount) => {
                Self::canonicalize_shift_like_op(*value, *amount, Expr::ShiftLeft)
            }
            Expr::LogicalShiftRight(value, amount) => {
                Self::canonicalize_shift_like_op(*value, *amount, Expr::LogicalShiftRight)
            }
            Expr::ArithmeticShiftRight(value, amount) => {
                Self::canonicalize_shift_like_op(*value, *amount, Expr::ArithmeticShiftRight)
            }
            Expr::RotateRight(value, amount) => {
                Self::canonicalize_shift_like_op(*value, *amount, Expr::RotateRight)
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
                    if high >= value_width {
                        panic!(
                            "Expr::Extract high index {high} is outside value width {value_width}"
                        );
                    }
                    if low == 0 && out_width == value_width {
                        return value;
                    }
                }

                Expr::Extract {
                    value: Box::new(value),
                    high,
                    low,
                }
            }
            Expr::Concat(values) => {
                Self::rebuild_concat(values.into_iter().map(Expr::canonicalize))
            }
            Expr::ZeroExtend { value, to_width } => {
                Self::canonicalize_extension(*value, to_width, ExtensionOp::Zero)
            }
            Expr::SignExtend { value, to_width } => {
                Self::canonicalize_extension(*value, to_width, ExtensionOp::Sign)
            }
            Expr::CountOnes(value) => Expr::CountOnes(Box::new(value.canonicalize())),
            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => Self::canonicalize_flag_expr(*lhs, *rhs, *carry_in, width, FlagOp::AddCarryOut),
            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => Self::canonicalize_flag_expr(*lhs, *rhs, *carry_in, width, FlagOp::AddOverflow),
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                width,
            } => Self::canonicalize_flag_expr(
                *lhs,
                not_expr(*rhs),
                not_expr(*borrow_in),
                width,
                FlagOp::AddCarryOut,
            ),

            Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                width,
            } => Self::canonicalize_flag_expr(
                *lhs,
                not_expr(*rhs),
                not_expr(*borrow_in),
                width,
                FlagOp::AddOverflow,
            ),
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
                    }
                    .lower_operators(),
                }
            }
        }
    }

    /// Resolves instruction-dependent leaves and folds newly constant subtrees.
    ///
    /// Immediate/register fields and `DerivedValue`s are replaced using
    /// `instruction`. Constant arithmetic, comparisons, shifts, extensions,
    /// concatenations, flag helpers, and constant-condition `Select`s are
    /// evaluated recursively. Nonconstant structure and operand order are
    /// preserved; this method does not perform algebraic canonicalization or
    /// prior-state substitution.
    pub fn collapse(self, instruction: &DecodedInstruction) -> Self {
        let derived_values = &instruction
            .form
            .as_ref()
            .expect("DecodedInstruction.form must not be None")
            .derived_values;

        match self {
            constant @ Expr::Const { .. } => constant,
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
                    identifier_width: reg_ident
                        .bits
                        .len()
                        .try_into()
                        .expect("Register address length value must fit into u16"),
                }))
            }
            fixed @ Expr::Operand(RegisterField(RegisterRef::Fixed { .. })) => fixed,
            Expr::DerivedValue(name) => derived_values
                .iter()
                .find(|value| value.name == name)
                .unwrap_or_else(|| panic!("Derived value {} does not exist!", name.0))
                .value
                .clone()
                .collapse(instruction),
            Expr::ReadRegister { register, width } => Expr::ReadRegister {
                register: Box::new(register.collapse(instruction)),
                width,
            },
            Expr::ReadMemory { address, width } => Expr::ReadMemory {
                address: Box::new(address.collapse(instruction)),
                width,
            },
            Expr::Add(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, *op1, *op2, AssocCommOp::Add)
            }
            Expr::Sub(op1, op2) => {
                Self::collapse_binary_op(instruction, *op1, *op2, Expr::Sub, |lhs, rhs, width| {
                    Self::const_bits(lhs.wrapping_sub(rhs), width)
                })
            }
            Expr::Mul(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, *op1, *op2, AssocCommOp::Mul)
            }
            Expr::And(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, *op1, *op2, AssocCommOp::And)
            }
            Expr::Or(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, *op1, *op2, AssocCommOp::Or)
            }
            Expr::Xor(op1, op2) => {
                Self::collapse_assoc_comm_op(instruction, *op1, *op2, AssocCommOp::Xor)
            }
            Expr::Not(op) => {
                Self::collapse_unary_op(instruction, *op, Expr::Not, |value, _width| !value)
            }
            Expr::ShiftLeft(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::ShiftLeft,
                |value, amount, width| {
                    Self::const_bits(Self::shift_left_const(value, amount, width), width)
                },
            ),
            Expr::LogicalShiftRight(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::LogicalShiftRight,
                |value, amount, width| {
                    Self::const_bits(Self::logical_shift_right_const(value, amount, width), width)
                },
            ),
            Expr::ArithmeticShiftRight(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::ArithmeticShiftRight,
                |value, amount, width| {
                    Self::const_bits(
                        Self::arithmetic_shift_right_const(value, amount, width),
                        width,
                    )
                },
            ),
            Expr::RotateRight(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::RotateRight,
                |value, amount, width| {
                    Self::const_bits(Self::rotate_right_const(value, amount, width), width)
                },
            ),
            Expr::Equal(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::Equal,
                |lhs, rhs, _width| bool_const(lhs == rhs),
            ),
            Expr::UnsignedLessThan(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::UnsignedLessThan,
                |lhs, rhs, _width| bool_const(lhs < rhs),
            ),
            Expr::SignedLessThan(op1, op2) => Self::collapse_binary_op(
                instruction,
                *op1,
                *op2,
                Expr::SignedLessThan,
                |lhs, rhs, width| {
                    bool_const(Self::signed_value(lhs, width) < Self::signed_value(rhs, width))
                },
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
                Self::rebuild_concat(exprs.into_iter().map(|expr| expr.collapse(instruction)))
            }
            Expr::ZeroExtend { value, to_width } => {
                Self::collapse_extension(instruction, *value, to_width, ExtensionOp::Zero)
            }
            Expr::SignExtend { value, to_width } => {
                Self::collapse_extension(instruction, *value, to_width, ExtensionOp::Sign)
            }
            Expr::CountOnes(expr) => {
                Self::collapse_unary_op(instruction, *expr, Expr::CountOnes, |value, _width| {
                    value.count_ones() as u128
                })
            }
            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => Self::collapse_flag_expr(
                instruction,
                *lhs,
                *rhs,
                *carry_in,
                width,
                FlagOp::AddCarryOut,
            ),
            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => Self::collapse_flag_expr(
                instruction,
                *lhs,
                *rhs,
                *carry_in,
                width,
                FlagOp::AddOverflow,
            ),
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                width,
            } => Self::collapse_flag_expr(
                instruction,
                *lhs,
                *rhs,
                *borrow_in,
                width,
                FlagOp::SubCarryOut,
            ),
            Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                width,
            } => Self::collapse_flag_expr(
                instruction,
                *lhs,
                *rhs,
                *borrow_in,
                width,
                FlagOp::SubOverflow,
            ),
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

/// Name of a form-local derived semantic value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueName(
    /// Owned identifier used to match a form's derived-value definition.
    pub String,
);

/// Name of a decoded instruction field.
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
    /// `identifier_width` is the width of the register identifier expression, not
    /// the width of the register's stored value.
    /// `identifier_width` must be consistent the ISA's ArchitecturalRegisters
    /// If it is not, the boolean equivalence for the Expr will fail to find
    /// the register.
    Fixed {
        register: Register,
        identifier_width: u16,
    },

    /// A register identifier decoded from an instruction field.
    FromField(FieldName),
}

/// Register struct which defines enumerated fixed registers
/// This does not necessarily need to match with the exact ISA definition of registers
/// For example, for an ISA with only 16 general purpose registers, you may still choose to define Register(20)
/// if there is some value stored in state that needs to be stored.
/// This should be used for ALL state that isn't memory (including eg flags).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Register(
    /// Numeric architectural or virtual register identifier.
    pub u8,
);

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
    /// Creates an unconditional register write.
    pub fn write_register(register: Expr, value: Expr) -> Self {
        Self::WriteRegister {
            guard: bool_const(true),
            register,
            value,
        }
    }

    /// Creates a register write guarded by a 1-bit condition.
    pub fn write_register_if(guard: Expr, register: Expr, value: Expr) -> Self {
        Self::WriteRegister {
            guard,
            register,
            value,
        }
    }

    /// Creates an unconditional memory write of `width` bits.
    pub fn write_memory(address: Expr, value: Expr, width: u16) -> Self {
        Self::WriteMemory {
            guard: bool_const(true),
            address,
            value,
            width,
        }
    }

    /// Creates a memory write guarded by a 1-bit condition.
    pub fn write_memory_if(guard: Expr, address: Expr, value: Expr, width: u16) -> Self {
        Self::WriteMemory {
            guard,
            address,
            value,
            width,
        }
    }
}

/// Allocates an owned instruction-field name.
pub fn field_name(name: &str) -> FieldName {
    name.to_owned()
}

/// Constructs a literal bit-vector.
///
/// The value is truncated when evaluated or canonicalized, not by this
/// lightweight constructor.
pub fn constant(value: u128, width: u16) -> Expr {
    Expr::Const { value, width }
}

/// Constructs a canonical 1-bit boolean literal.
pub fn bool_const(value: bool) -> Expr {
    constant(value as u128, 1)
}

/// References the raw value of an immediate instruction field.
pub fn immediate_field(name: &str) -> Expr {
    Expr::Operand(OperandRef::ImmediateField(field_name(name)))
}

/// References a value defined by the matched instruction form.
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
///
/// `identifier_width` is the bit width of the register identifier expression,
/// not the width of the data stored in that register.
pub fn fixed_register(register: Register, identifier_width: u16) -> Expr {
    Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
        register,
        identifier_width,
    }))
}

/// Constructs a state read from a register-identifier expression.
///
/// `width` is the width of the stored value, not the register identifier.
pub fn read_register(register: Expr, width: u16) -> Expr {
    Expr::ReadRegister {
        register: Box::new(register),
        width,
    }
}

/// Constructs a memory read of `width` bits from a byte-address expression.
pub fn read_memory(address: Expr, width: u16) -> Expr {
    Expr::ReadMemory {
        address: Box::new(address),
        width,
    }
}

/// Reads the register whose identifier is encoded by instruction field `name`.
pub fn read_register_field(name: &str, width: u16) -> Expr {
    read_register(register_field(name), width)
}

/// Reads a fixed register with separate identifier and stored-value widths.
pub fn read_fixed_register(register: Register, identifier_width: u16, data_width: u16) -> Expr {
    read_register(fixed_register(register, identifier_width), data_width)
}

/// Constructs an equality comparison returning one bit.
pub fn equal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Equal(Box::new(lhs), Box::new(rhs))
}

/// Constructs an unsigned less-than comparison returning one bit.
pub fn unsigned_less_than(lhs: Expr, rhs: Expr) -> Expr {
    Expr::UnsignedLessThan(Box::new(lhs), Box::new(rhs))
}

/// Constructs a signed two's-complement less-than comparison returning one bit.
pub fn signed_less_than(lhs: Expr, rhs: Expr) -> Expr {
    Expr::SignedLessThan(Box::new(lhs), Box::new(rhs))
}

/// Constructs wrapping bit-vector addition.
pub fn add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Add(Box::new(lhs), Box::new(rhs))
}

/// Constructs wrapping bit-vector subtraction.
pub fn sub(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Sub(Box::new(lhs), Box::new(rhs))
}

/// Constructs width-preserving wrapping multiplication.
pub fn mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Mul(Box::new(lhs), Box::new(rhs))
}

/// Constructs bitwise AND, or Boolean conjunction for 1-bit operands.
pub fn and_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::And(Box::new(lhs), Box::new(rhs))
}

/// Constructs bitwise OR, or Boolean disjunction for 1-bit operands.
pub fn or_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Or(Box::new(lhs), Box::new(rhs))
}

/// Constructs bitwise XOR, or Boolean inequality for 1-bit operands.
pub fn xor_expr(lhs: Expr, rhs: Expr) -> Expr {
    Expr::Xor(Box::new(lhs), Box::new(rhs))
}

/// Constructs bitwise NOT, or Boolean negation for a 1-bit operand.
pub fn not_expr(value: Expr) -> Expr {
    Expr::Not(Box::new(value))
}

/// Constructs a logical left shift by an unsigned amount.
pub fn shift_left(value: Expr, amount: Expr) -> Expr {
    Expr::ShiftLeft(Box::new(value), Box::new(amount))
}

/// Constructs a zero-filling logical right shift.
pub fn logical_shift_right(value: Expr, amount: Expr) -> Expr {
    Expr::LogicalShiftRight(Box::new(value), Box::new(amount))
}

/// Constructs a sign-filling arithmetic right shift.
pub fn arithmetic_shift_right(value: Expr, amount: Expr) -> Expr {
    Expr::ArithmeticShiftRight(Box::new(value), Box::new(amount))
}

/// Constructs rotate-right; evaluated amounts are reduced modulo value width.
pub fn rotate_right(value: Expr, amount: Expr) -> Expr {
    Expr::RotateRight(Box::new(value), Box::new(amount))
}

/// Extracts inclusive bit range `high..=low`.
///
/// Range validation occurs during `collapse` or `canonicalize`.
pub fn extract(value: Expr, high: u16, low: u16) -> Expr {
    Expr::Extract {
        value: Box::new(value),
        high,
        low,
    }
}

/// Concatenates values from most-significant chunk to least-significant chunk.
pub fn concat(values: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::Concat(values.into_iter().collect())
}

/// Constructs zero extension to `to_width`.
pub fn zero_extend(value: Expr, to_width: u16) -> Expr {
    Expr::ZeroExtend {
        value: Box::new(value),
        to_width,
    }
}

/// Constructs sign extension to `to_width`.
pub fn sign_extend(value: Expr, to_width: u16) -> Expr {
    Expr::SignExtend {
        value: Box::new(value),
        to_width,
    }
}

/// Counts set bits; the expression result retains the input's declared width.
pub fn count_ones(value: Expr) -> Expr {
    Expr::CountOnes(Box::new(value))
}

/// Constructs unsigned carry-out from `lhs + rhs + carry_in`.
pub fn add_carry_out(lhs: Expr, rhs: Expr, carry_in: Expr, width: u16) -> Expr {
    Expr::AddCarryOut {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        carry_in: Box::new(carry_in),
        width,
    }
}

/// Constructs signed overflow from `lhs + rhs + carry_in`.
pub fn add_overflow(lhs: Expr, rhs: Expr, carry_in: Expr, width: u16) -> Expr {
    Expr::AddOverflow {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        carry_in: Box::new(carry_in),
        width,
    }
}

/// Constructs subtraction carry (“no borrow”) from `lhs - rhs - borrow_in`.
pub fn sub_carry_out(lhs: Expr, rhs: Expr, borrow_in: Expr, width: u16) -> Expr {
    Expr::SubCarryOut {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        borrow_in: Box::new(borrow_in),
        width,
    }
}

/// Constructs signed overflow from `lhs - rhs - borrow_in`.
pub fn sub_overflow(lhs: Expr, rhs: Expr, borrow_in: Expr, width: u16) -> Expr {
    Expr::SubOverflow {
        lhs: Box::new(lhs),
        rhs: Box::new(rhs),
        borrow_in: Box::new(borrow_in),
        width,
    }
}

/// Constructs a conditional expression.
///
/// `condition` must be one bit and both result branches must have equal width.
pub fn select(condition: Expr, when_true: Expr, when_false: Expr) -> Expr {
    Expr::Select {
        condition: Box::new(condition),
        when_true: Box::new(when_true),
        when_false: Box::new(when_false),
    }
}

/// Compares an immediate field with a literal of the supplied width.
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

    /// Builds a decoded instruction with no fields or derived values.
    fn empty_instruction() -> DecodedInstruction {
        DecodedInstruction {
            name: Some("test".to_owned()),
            form: Some(InstructionForm::new("test")),
            bits: Vec::new(),
            fields: Vec::new(),
        }
    }

    /// Builds the shared decoded fixture used by field-resolution tests.
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

    /// Asserts recursively that subtraction, OR, and XOR have been lowered.
    fn assert_operator_reduced(expr: &Expr) {
        match expr {
            Expr::Sub(_, _) | Expr::Or(_, _) | Expr::Xor(_, _) => {
                panic!("expression still contains a reduced operator: {expr:?}")
            }
            Expr::Const { .. } | Expr::Operand(_) | Expr::DerivedValue(_) => {}
            Expr::ReadRegister { register, .. } => assert_operator_reduced(register),
            Expr::ReadMemory { address, .. } => assert_operator_reduced(address),
            Expr::Not(value)
            | Expr::CountOnes(value)
            | Expr::Extract { value, .. }
            | Expr::ZeroExtend { value, .. }
            | Expr::SignExtend { value, .. } => assert_operator_reduced(value),
            Expr::Add(lhs, rhs)
            | Expr::Mul(lhs, rhs)
            | Expr::And(lhs, rhs)
            | Expr::ShiftLeft(lhs, rhs)
            | Expr::LogicalShiftRight(lhs, rhs)
            | Expr::ArithmeticShiftRight(lhs, rhs)
            | Expr::RotateRight(lhs, rhs)
            | Expr::Equal(lhs, rhs)
            | Expr::UnsignedLessThan(lhs, rhs)
            | Expr::SignedLessThan(lhs, rhs) => {
                assert_operator_reduced(lhs);
                assert_operator_reduced(rhs);
            }
            Expr::Concat(values) => {
                for value in values {
                    assert_operator_reduced(value);
                }
            }
            Expr::AddCarryOut {
                lhs, rhs, carry_in, ..
            }
            | Expr::AddOverflow {
                lhs, rhs, carry_in, ..
            } => {
                assert_operator_reduced(lhs);
                assert_operator_reduced(rhs);
                assert_operator_reduced(carry_in);
            }
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                ..
            }
            | Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                ..
            } => {
                assert_operator_reduced(lhs);
                assert_operator_reduced(rhs);
                assert_operator_reduced(borrow_in);
            }
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                assert_operator_reduced(condition);
                assert_operator_reduced(when_true);
                assert_operator_reduced(when_false);
            }
        }
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
    fn canonicalized_subtraction_flags_match_original_semantics_exhaustively() {
        let instruction = empty_instruction();

        // Exhaust every possible lhs, rhs, and borrow input for small widths.
        // The original subtraction helpers and their canonicalized addition
        // forms use separate constant evaluators, so this compares behavior
        // rather than merely checking that a particular AST rewrite occurred.
        for width in 1..=8 {
            let value_count = 1u128 << width;
            for lhs in 0..value_count {
                for rhs in 0..value_count {
                    for borrow_in in [false, true] {
                        let lhs = constant(lhs, width);
                        let rhs = constant(rhs, width);
                        let borrow_in = bool_const(borrow_in);

                        let sub_carry =
                            sub_carry_out(lhs.clone(), rhs.clone(), borrow_in.clone(), width);
                        assert_eq!(
                            sub_carry.clone().collapse(&instruction),
                            sub_carry.canonicalize().collapse(&instruction),
                            "SubCarryOut conversion failed for width={width}, lhs={lhs:?}, rhs={rhs:?}, borrow_in={borrow_in:?}"
                        );

                        let sub_overflow =
                            sub_overflow(lhs.clone(), rhs.clone(), borrow_in.clone(), width);
                        assert_eq!(
                            sub_overflow.clone().collapse(&instruction),
                            sub_overflow.canonicalize().collapse(&instruction),
                            "SubOverflow conversion failed for width={width}, lhs={lhs:?}, rhs={rhs:?}, borrow_in={borrow_in:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn canonicalized_subtraction_flags_match_original_semantics_at_wide_boundaries() {
        let instruction = empty_instruction();

        for width in [16, 32, 64, 127, 128] {
            let mask = Expr::bit_mask(width);
            let sign_bit = Expr::sign_bit(width);
            let values = [0, 1, sign_bit - 1, sign_bit, sign_bit + 1, mask - 1, mask];

            for lhs in values {
                for rhs in values {
                    for borrow_in in [false, true] {
                        let lhs = constant(lhs, width);
                        let rhs = constant(rhs, width);
                        let borrow_in = bool_const(borrow_in);

                        let sub_carry =
                            sub_carry_out(lhs.clone(), rhs.clone(), borrow_in.clone(), width);
                        assert_eq!(
                            sub_carry.clone().collapse(&instruction),
                            sub_carry.canonicalize().collapse(&instruction),
                            "wide SubCarryOut conversion failed for width={width}, lhs={lhs:?}, rhs={rhs:?}, borrow_in={borrow_in:?}"
                        );

                        let sub_overflow =
                            sub_overflow(lhs.clone(), rhs.clone(), borrow_in.clone(), width);
                        assert_eq!(
                            sub_overflow.clone().collapse(&instruction),
                            sub_overflow.canonicalize().collapse(&instruction),
                            "wide SubOverflow conversion failed for width={width}, lhs={lhs:?}, rhs={rhs:?}, borrow_in={borrow_in:?}"
                        );
                    }
                }
            }
        }
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
            read_register(register_field("rd"), 8).collapse(&instruction),
            read_register(fixed_register(Register(3), 2), 8)
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
    fn expr_width_tracks_register_reads_and_unresolved_instruction_values() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            read_fixed_register(Register(1), 4, 32).expr_width(),
            Some(32)
        );
        assert_eq!(
            read_register(fixed_register(Register(1), 4), 32).expr_width(),
            Some(32)
        );
        assert_eq!(
            read_register(register_field("rd"), 32)
                .collapse(&instruction)
                .expr_width(),
            Some(32)
        );

        assert_eq!(immediate_field("imm").expr_width(), None);
        assert_eq!(register_field("rd").expr_width(), None);
        assert_eq!(derived_value("expanded").expr_width(), None);
        assert_eq!(
            add(immediate_field("imm"), constant(1, 4)).expr_width(),
            None
        );

        assert_eq!(
            immediate_field("imm").collapse(&instruction).expr_width(),
            Some(4)
        );
        assert_eq!(
            derived_value("expanded")
                .collapse(&instruction)
                .expr_width(),
            Some(8)
        );
    }

    #[test]
    fn collapse_preserves_nonconstant_structure_with_collapsed_children() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            concat([
                constant(0xa, 4),
                read_register(register_field("rd"), 8),
                constant(0x3, 2),
                constant(0x2, 2),
            ])
            .collapse(&instruction),
            concat([
                constant(0xa, 4),
                read_register(fixed_register(Register(3), 2), 8),
                constant(0xe, 4),
            ])
        );
        assert_eq!(
            select(
                read_register(register_field("rd"), 1),
                derived_value("expanded"),
                sub(constant(0, 8), constant(1, 8)),
            )
            .collapse(&instruction),
            select(
                read_register(fixed_register(Register(3), 2), 1),
                constant(6, 8),
                constant(0xff, 8),
            )
        );
    }

    #[test]
    fn substitute_preserves_signed_comparison_kind() {
        let lhs = read_fixed_register(Register(1), 4, 8);
        let rhs = read_fixed_register(Register(2), 4, 8);
        let expression = signed_less_than(lhs, rhs);

        assert!(matches!(
            expression.substitute(&[]),
            Expr::SignedLessThan(_, _)
        ));
    }

    #[test]
    fn substitute_builds_register_forwarding_chain_in_latest_write_order() {
        let selector = read_fixed_register(Register(9), 4, 4);
        let guard_1 = read_fixed_register(Register(10), 4, 1);
        let guard_2 = read_fixed_register(Register(11), 4, 1);
        let guard_3 = read_fixed_register(Register(12), 4, 1);
        let reg_1 = fixed_register(Register(1), 4);
        let reg_2 = fixed_register(Register(2), 4);
        let reg_3 = fixed_register(Register(3), 4);
        let original_read = read_register(selector.clone(), 8);
        let previous_effects = vec![
            Effect::write_register_if(guard_1.clone(), reg_1.clone(), constant(0x11, 8)),
            Effect::write_register_if(guard_2.clone(), reg_2.clone(), constant(0x22, 8)),
            Effect::write_register_if(guard_3.clone(), reg_3.clone(), constant(0x33, 8)),
        ];

        assert_eq!(
            original_read.clone().substitute(&previous_effects),
            select(
                and_expr(guard_3, equal(selector.clone(), reg_3)),
                constant(0x33, 8),
                select(
                    and_expr(guard_2, equal(selector.clone(), reg_2)),
                    constant(0x22, 8),
                    select(
                        and_expr(guard_1, equal(selector, reg_1)),
                        constant(0x11, 8),
                        original_read,
                    ),
                ),
            )
        );
    }

    #[test]
    fn substitute_builds_memory_forwarding_chain_and_ignores_wrong_kind_or_width() {
        let address = read_fixed_register(Register(9), 4, 32);
        let guard_1 = read_fixed_register(Register(10), 4, 1);
        let guard_2 = read_fixed_register(Register(11), 4, 1);
        let address_1 = constant(0x100, 32);
        let address_2 = constant(0x200, 32);
        let original_read = read_memory(address.clone(), 8);
        let previous_effects = vec![
            Effect::write_register(address_1.clone(), constant(0xff, 8)),
            Effect::write_memory(address_1.clone(), constant(0xabcd, 16), 16),
            Effect::write_memory_if(guard_1.clone(), address_1.clone(), constant(0x11, 8), 8),
            Effect::write_memory_if(guard_2.clone(), address_2.clone(), constant(0x22, 8), 8),
        ];

        assert_eq!(
            original_read.clone().substitute(&previous_effects),
            select(
                and_expr(guard_2, equal(address.clone(), address_2)),
                constant(0x22, 8),
                select(
                    and_expr(guard_1, equal(address, address_1)),
                    constant(0x11, 8),
                    original_read,
                ),
            )
        );
    }

    #[test]
    fn substitute_forwards_through_identifiers_before_matching_memory_writes() {
        let previous_effects = vec![
            Effect::write_register(fixed_register(Register(0), 8), constant(0x200, 32)),
            Effect::write_memory(constant(0x200, 32), constant(0xaa, 8), 8),
        ];

        assert_eq!(
            read_memory(read_fixed_register(Register(0), 8, 32), 8)
                .substitute(&previous_effects)
                .canonicalize(),
            constant(0xaa, 8)
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
        let x = read_register(fixed_register(Register(1), 4), 8);
        let y = read_register(fixed_register(Register(2), 4), 8);

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
                read_fixed_register(Register(3), 8, 8)
            )
            .collapse(&instruction),
            add(read_fixed_register(Register(3), 8, 8), constant(4, 8))
        );
    }

    #[test]
    fn collapse_assoc_comm_multiplication_folds_identities_and_annihilators() {
        let instruction = empty_instruction();
        let x = read_register(fixed_register(Register(1), 4), 8);

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
        let x = read_register(fixed_register(Register(1), 4), 8);
        let y = read_register(fixed_register(Register(2), 4), 8);

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
            read_register(fixed_register(Register(1), 4), 8)
        );
    }

    #[test]
    fn collapse_assoc_comm_simplifies_decoded_instruction_terms() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            add(
                add(
                    zero_extend(immediate_field("imm"), 8),
                    read_register(register_field("rd"), 8)
                ),
                add(constant(9, 8), constant(1, 8)),
            )
            .collapse(&instruction),
            add(
                read_register(fixed_register(Register(3), 2), 8),
                constant(15, 8)
            )
        );
        assert_eq!(
            xor_expr(
                xor_expr(
                    derived_value("expanded"),
                    read_register(register_field("rd"), 8)
                ),
                constant(6, 8),
            )
            .collapse(&instruction),
            read_register(fixed_register(Register(3), 2), 8)
        );
    }

    #[test]
    fn collapse_assoc_comm_does_not_rewrite_non_commutative_ops() {
        let instruction = empty_instruction();
        let x = read_register(fixed_register(Register(1), 4), 8);

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
            add(read_fixed_register(Register(1), 8, 8), constant(1, 8)),
            constant(1, 16),
        )
        .collapse(&instruction);
    }

    #[test]
    fn canonicalize_sorts_and_folds_associative_commutative_terms() {
        let x = read_fixed_register(Register(1), 8, 8);
        let y = read_fixed_register(Register(2), 8, 8);

        let expr_1 = add(y.clone(), add(constant(2, 8), x.clone())).canonicalize();
        let expr_2 = add(add(x.clone(), y.clone()), constant(2, 8)).canonicalize();

        assert_eq!(expr_1, expr_2);
        assert_eq!(expr_1, add(add(x, y), constant(2, 8)));
        assert_eq!(
            add(
                add(constant(250, 8), constant(10, 8)),
                read_fixed_register(Register(3), 8, 8)
            )
            .canonicalize(),
            add(read_fixed_register(Register(3), 8, 8), constant(4, 8))
        );
    }

    #[test]
    fn collapse_and_canonicalize_resolves_instruction_fields_before_normalizing() {
        let instruction = decoded_fixture_instruction();

        assert_eq!(
            add(
                read_register(register_field("rd"), 8),
                add(
                    add(constant(4, 8), zero_extend(immediate_field("imm"), 8)),
                    constant(6, 8),
                ),
            )
            .collapse_and_canonicalize(&instruction),
            add(
                read_register(fixed_register(Register(3), 2), 8),
                constant(15, 8)
            )
        );
    }

    #[test]
    fn canonicalize_bitwise_deduplicates_and_cancels_and_xor_terms() {
        let x = fixed_register(Register(1), 4);
        let y = fixed_register(Register(2), 4);

        assert_eq!(
            and_expr(y.clone(), and_expr(x.clone(), x.clone())).canonicalize(),
            and_expr(x.clone(), y.clone())
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
    fn canonicalize_cancels_known_width_register_xor() {
        let x = read_fixed_register(Register(1), 4, 4);

        assert_eq!(
            xor_expr(x.clone(), x.clone()).canonicalize(),
            constant(0, 4)
        );
    }

    #[test]
    fn canonicalize_identities_annihilators_and_local_rules() {
        let x = read_fixed_register(Register(1), 8, 8);

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
        let x = read_fixed_register(Register(1), 4, 4);
        let y = read_fixed_register(Register(2), 4, 4);

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
            select(read_fixed_register(Register(3), 4, 4), x.clone(), x.clone()).canonicalize(),
            x
        );
    }

    #[test]
    fn canonicalize_reduces_boolean_select_to_and_and_not() {
        let condition = read_fixed_register(Register(1), 4, 1);
        let when_true = read_fixed_register(Register(2), 4, 1);
        let when_false = read_fixed_register(Register(3), 4, 1);

        let canonical = select(condition, when_true, when_false).canonicalize();

        assert_operator_reduced(&canonical);
        assert!(!matches!(canonical, Expr::Select { .. }));
        assert_eq!(canonical.expr_width(), Some(1));
        assert_eq!(canonical.clone().canonicalize(), canonical);
    }

    #[test]
    fn canonicalize_boolean_select_matches_sum_of_products() {
        let condition = read_fixed_register(Register(1), 4, 1);
        let when_true = read_fixed_register(Register(2), 4, 1);
        let when_false = read_fixed_register(Register(3), 4, 1);
        let sum_of_products = or_expr(
            and_expr(condition.clone(), when_true.clone()),
            and_expr(not_expr(condition.clone()), when_false.clone()),
        );

        assert_eq!(
            select(condition, when_true, when_false).canonicalize(),
            sum_of_products.canonicalize()
        );
    }

    #[test]
    fn canonicalize_select_preserves_vector_result_width() {
        let condition = read_fixed_register(Register(1), 4, 1);
        let when_true = read_fixed_register(Register(2), 4, 8);
        let when_false = read_fixed_register(Register(3), 4, 8);

        assert_eq!(
            select(condition, when_true, when_false)
                .canonicalize()
                .expr_width(),
            Some(8)
        );
    }

    #[test]
    fn canonicalize_vector_select_matches_masked_sum_of_products() {
        let condition = read_fixed_register(Register(1), 4, 1);
        let when_true = read_fixed_register(Register(2), 4, 8);
        let when_false = read_fixed_register(Register(3), 4, 8);
        let mask = sign_extend(condition.clone(), 8);
        let sum_of_products = or_expr(
            and_expr(mask.clone(), when_true.clone()),
            and_expr(not_expr(mask), when_false.clone()),
        );

        assert_eq!(
            select(condition, when_true, when_false).canonicalize(),
            sum_of_products.canonicalize()
        );
    }

    #[test]
    fn canonicalize_folds_constants_across_nested_bitwise_operations() {
        let x = read_fixed_register(Register(1), 4, 4);

        assert_eq!(
            and_expr(
                constant(0b1110, 4),
                and_expr(x.clone(), constant(0b1001, 4)),
            )
            .canonicalize(),
            and_expr(x.clone(), constant(0b1000, 4))
        );
        assert_eq!(
            and_expr(
                and_expr(constant(0b1111, 4), x.clone()),
                and_expr(constant(0b1101, 4), constant(0b1011, 4)),
            )
            .canonicalize(),
            and_expr(x, constant(0b1001, 4))
        );

        let x = read_fixed_register(Register(1), 4, 4);
        assert_eq!(
            or_expr(constant(0b0100, 4), or_expr(x.clone(), constant(0b0011, 4)),).canonicalize(),
            or_expr(x.clone(), constant(0b0111, 4)).canonicalize()
        );
        assert_eq!(
            xor_expr(
                constant(0b1100, 4),
                xor_expr(x.clone(), constant(0b1010, 4)),
            )
            .canonicalize(),
            xor_expr(x, constant(0b0110, 4)).canonicalize()
        );
    }

    #[test]
    fn canonicalize_folds_not_constants_and_complements() {
        let x = read_fixed_register(Register(1), 4, 8);
        let y = read_fixed_register(Register(2), 4, 8);

        assert_eq!(
            not_expr(constant(0b1010_1100, 8)).canonicalize(),
            constant(0b0101_0011, 8)
        );
        assert_eq!(
            and_expr(x.clone(), not_expr(x.clone())).canonicalize(),
            constant(0, 8)
        );
        assert_eq!(
            and_expr(y.clone(), and_expr(not_expr(x.clone()), x.clone())).canonicalize(),
            constant(0, 8)
        );
        assert_eq!(
            or_expr(x.clone(), not_expr(x.clone())).canonicalize(),
            constant(0xff, 8)
        );
        assert_eq!(
            or_expr(y, or_expr(x.clone(), not_expr(x))).canonicalize(),
            constant(0xff, 8)
        );
    }

    #[test]
    fn canonicalize_applies_boolean_absorption() {
        let x = read_fixed_register(Register(1), 4, 8);
        let y = read_fixed_register(Register(2), 4, 8);
        let z = read_fixed_register(Register(3), 4, 8);

        assert_eq!(
            and_expr(x.clone(), or_expr(x.clone(), y.clone())).canonicalize(),
            x.clone()
        );
        assert_eq!(
            or_expr(x.clone(), and_expr(x.clone(), y.clone())).canonicalize(),
            x.clone()
        );
        assert_eq!(
            and_expr(z.clone(), and_expr(or_expr(y, z.clone()), x.clone()),).canonicalize(),
            and_expr(x, z)
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
                read_fixed_register(Register(1), 4, 4),
                constant(0x3, 2),
                constant(0x2, 2),
            ])
            .canonicalize(),
            concat([
                constant(0xa, 4),
                read_fixed_register(Register(1), 4, 4),
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
        let x = read_fixed_register(Register(1), 8, 8);

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
            add_overflow(x, constant(0x7f, 8), bool_const(true), 8)
        );
    }

    #[test]
    fn canonicalize_equates_logical_normal_forms() {
        let a = read_fixed_register(Register(1), 4, 8);
        let b = read_fixed_register(Register(2), 4, 8);
        let c = read_fixed_register(Register(3), 4, 8);

        let associated_or = or_expr(or_expr(a.clone(), b.clone()), c.clone()).canonicalize();
        let permuted_or = or_expr(c.clone(), or_expr(b.clone(), a.clone())).canonicalize();
        assert_eq!(associated_or, permuted_or);

        let de_morgan_or = not_expr(and_expr(not_expr(a.clone()), not_expr(b.clone())));
        assert_eq!(
            or_expr(a.clone(), b.clone()).canonicalize(),
            de_morgan_or.canonicalize()
        );

        let de_morgan_and = not_expr(or_expr(not_expr(a.clone()), not_expr(b.clone())));
        assert_eq!(
            and_expr(a.clone(), b.clone()).canonicalize(),
            de_morgan_and.canonicalize()
        );

        let xor_sum_of_products = or_expr(
            and_expr(a.clone(), not_expr(b.clone())),
            and_expr(not_expr(a.clone()), b.clone()),
        );
        assert_eq!(
            xor_expr(a.clone(), b.clone()).canonicalize(),
            xor_sum_of_products.canonicalize()
        );

        let associated_xor = xor_expr(xor_expr(a.clone(), b.clone()), c.clone()).canonicalize();
        let permuted_xor = xor_expr(c, xor_expr(b, a)).canonicalize();
        assert_eq!(associated_xor, permuted_xor);

        assert_eq!(associated_or.clone().canonicalize(), associated_or);
        assert_eq!(associated_xor.clone().canonicalize(), associated_xor);
    }

    #[test]
    fn canonicalize_equates_addition_and_subtraction_normal_forms() {
        let x = read_fixed_register(Register(1), 4, 8);
        let y = read_fixed_register(Register(2), 4, 8);
        let z = read_fixed_register(Register(3), 4, 8);

        let associated_add = add(
            add(x.clone(), constant(3, 8)),
            add(y.clone(), constant(5, 8)),
        )
        .canonicalize();
        let permuted_add = add(constant(8, 8), add(y.clone(), x.clone())).canonicalize();
        assert_eq!(associated_add, permuted_add);

        let twos_complement_sub = add(add(x.clone(), not_expr(y.clone())), constant(1, 8));
        assert_eq!(
            sub(x.clone(), y.clone()).canonicalize(),
            twos_complement_sub.canonicalize()
        );

        let add_of_subtraction = add(x.clone(), sub(y.clone(), z.clone())).canonicalize();
        let subtraction_of_add = sub(add(y, x), z).canonicalize();
        assert_eq!(add_of_subtraction, subtraction_of_add);
    }

    #[test]
    fn canonicalize_eliminates_reduced_operators_recursively() {
        let x = read_fixed_register(Register(1), 4, 8);
        let y = read_fixed_register(Register(2), 4, 8);
        let z = read_fixed_register(Register(3), 4, 8);
        let expression = add(
            sub(
                or_expr(x.clone(), z.clone()),
                xor_expr(y.clone(), z.clone()),
            ),
            xor_expr(x.clone(), or_expr(y, sub(z, x))),
        );

        let canonical = expression.canonicalize();
        assert_operator_reduced(&canonical);
        assert_eq!(canonical.clone().canonicalize(), canonical);
    }

    #[test]
    fn canonicalize_reduces_operators_after_resolving_instruction_fields() {
        let instruction = decoded_fixture_instruction();
        let expression = sub(
            or_expr(
                derived_value("expanded"),
                zero_extend(immediate_field("imm"), 8),
            ),
            xor_expr(
                read_register(register_field("rd"), 8),
                derived_value("doubled"),
            ),
        );

        let canonical = expression.collapse_and_canonicalize(&instruction);
        assert_operator_reduced(&canonical);
        assert_eq!(canonical.clone().canonicalize(), canonical);
    }

    #[test]
    fn canonicalize_reduction_handles_identities_before_expansion() {
        let x = read_fixed_register(Register(1), 4, 8);

        assert_eq!(or_expr(x.clone(), x.clone()).canonicalize(), x.clone());
        assert_eq!(or_expr(x.clone(), constant(0, 8)).canonicalize(), x.clone());
        assert_eq!(
            or_expr(x.clone(), constant(0xff, 8)).canonicalize(),
            constant(0xff, 8)
        );
        assert_eq!(
            xor_expr(x.clone(), x.clone()).canonicalize(),
            constant(0, 8)
        );
        assert_eq!(
            xor_expr(x.clone(), constant(0, 8)).canonicalize(),
            x.clone()
        );
        assert_eq!(sub(x.clone(), x.clone()).canonicalize(), constant(0, 8));
        assert_eq!(sub(x.clone(), constant(0, 8)).canonicalize(), x);
    }

    #[test]
    fn canonicalize_reduction_is_idempotent_across_widths() {
        for width in [1, 8, 128] {
            let x = read_fixed_register(Register(1), 4, width);
            let y = read_fixed_register(Register(2), 4, width);
            let canonical =
                sub(xor_expr(x.clone(), y.clone()), or_expr(not_expr(x), y)).canonicalize();

            assert_operator_reduced(&canonical);
            assert_eq!(canonical.clone().canonicalize(), canonical);
        }
    }

    #[test]
    fn canonicalize_equates_multiplicative_and_nested_normal_forms() {
        let x = read_fixed_register(Register(1), 4, 8);
        let y = read_fixed_register(Register(2), 4, 8);
        let z = read_fixed_register(Register(3), 4, 8);

        let associated_mul = mul(
            mul(x.clone(), constant(3, 8)),
            mul(y.clone(), constant(5, 8)),
        )
        .canonicalize();
        let permuted_mul = mul(constant(15, 8), mul(y.clone(), x.clone())).canonicalize();
        assert_eq!(associated_mul, permuted_mul);

        let nested_left = and_expr(
            or_expr(x.clone(), y.clone()),
            not_expr(xor_expr(y.clone(), z.clone())),
        )
        .canonicalize();
        let nested_right = and_expr(
            not_expr(and_expr(not_expr(y.clone()), not_expr(x.clone()))),
            not_expr(or_expr(
                and_expr(y.clone(), not_expr(z.clone())),
                and_expr(not_expr(y), z),
            )),
        )
        .canonicalize();
        assert_eq!(nested_left, nested_right);

        assert_eq!(nested_left.clone().canonicalize(), nested_left);
    }

    #[test]
    fn canonicalize_rewrites_preserve_four_bit_semantics() {
        let instruction = empty_instruction();

        for lhs in 0..16 {
            for rhs in 0..16 {
                let lhs = constant(lhs, 4);
                let rhs = constant(rhs, 4);
                let expressions = [
                    add(lhs.clone(), rhs.clone()),
                    sub(lhs.clone(), rhs.clone()),
                    or_expr(lhs.clone(), rhs.clone()),
                    xor_expr(lhs.clone(), rhs.clone()),
                    xor_expr(
                        or_expr(lhs.clone(), rhs.clone()),
                        and_expr(not_expr(lhs.clone()), rhs.clone()),
                    ),
                    sub(
                        add(lhs.clone(), rhs.clone()),
                        xor_expr(lhs.clone(), rhs.clone()),
                    ),
                ];

                for expression in expressions {
                    let original = expression.clone().collapse(&instruction);
                    let canonical = expression.canonicalize().collapse(&instruction);
                    assert_eq!(canonical, original);
                }
            }
        }
    }

    #[test]
    fn canonicalize_rewrites_preserve_edge_width_semantics() {
        let instruction = empty_instruction();

        for (width, lhs, rhs) in [
            (1, 0, 1),
            (1, 1, 1),
            (8, 0, 0xff),
            (8, 0x80, 0x7f),
            (128, 0, u128::MAX),
            (128, 1 << 127, (1 << 127) - 1),
        ] {
            let lhs = constant(lhs, width);
            let rhs = constant(rhs, width);
            let expressions = [
                sub(lhs.clone(), rhs.clone()),
                or_expr(lhs.clone(), rhs.clone()),
                xor_expr(lhs.clone(), rhs.clone()),
                sub(
                    xor_expr(lhs.clone(), rhs.clone()),
                    or_expr(not_expr(lhs.clone()), rhs.clone()),
                ),
            ];

            for expression in expressions {
                let expected = expression.clone().collapse(&instruction);
                let canonical = expression.canonicalize();
                assert_operator_reduced(&canonical);
                assert_eq!(canonical.collapse(&instruction), expected);
            }
        }
    }

    #[test]
    fn mul_by_two_reduces_to_shift() {
        let instruction = empty_instruction();
        let lhs = read_fixed_register(Register(1), 4, 8);
        let rhs = constant(2, 8);
        let expression = mul(lhs.clone(), rhs);
        assert_eq!(
            expression.collapse_and_canonicalize(&instruction),
            shift_left(lhs, constant(1, 8)).collapse_and_canonicalize(&instruction)
        )
    }

    #[test]
    fn mul_by_three_reduces_to_shift_add() {
        let instruction = empty_instruction();
        let lhs = read_fixed_register(Register(1), 4, 8);
        let rhs = constant(3, 8);
        let expression = mul(lhs.clone(), rhs);
        assert_eq!(
            expression.collapse_and_canonicalize(&instruction),
            add(shift_left(lhs.clone(), constant(1, 8)), lhs)
                .collapse_and_canonicalize(&instruction)
        )
    }

    #[test]
    fn mul_by_seven_reduces_to_shift_add() {
        let instruction = empty_instruction();
        let lhs = read_fixed_register(Register(1), 4, 8);
        let rhs = constant(7, 8);
        let expression = mul(lhs.clone(), rhs);
        assert_eq!(
            expression.collapse_and_canonicalize(&instruction),
            // x * 7 = x << 2 + x << 1 + x
            add(
                shift_left(lhs.clone(), constant(2, 8)),
                add(shift_left(lhs.clone(), constant(1, 8)), lhs)
            )
            .collapse_and_canonicalize(&instruction)
        )
    }

    #[test]
    fn mul_nested() {
        let instruction = empty_instruction();
        let register = read_fixed_register(Register(1), 4, 8);
        let lhs = constant(2, 8);
        let rhs = mul(register.clone(), constant(4, 8));
        let expression = mul(lhs, rhs);

        assert_eq!(
            expression.collapse_and_canonicalize(&instruction),
            // 2 * (x * 4) = x << 3
            shift_left(register, constant(3, 8))
        )
    }

    #[test]
    fn mul_add_identity() {
        let instruction = empty_instruction();
        let register = read_fixed_register(Register(1), 4, 8);
        let expression = add(constant(0, 8), mul(constant(5, 8), register.clone()));
        assert_eq!(
            expression.clone().collapse_and_canonicalize(&instruction),
            // 0 + (x * 5) = x << 2 + x
            add(
                register.clone(),
                shift_left(register.clone(), constant(2, 8))
            )
            .canonicalize()
        );

        // also check another order just for fun
        assert_eq!(
            expression.collapse_and_canonicalize(&instruction),
            // 0 + (x * 5) = x << 2 + x
            add(shift_left(register.clone(), constant(2, 8)), register).canonicalize()
        );
    }
}
