// Contains arm32 specification
// Simply an example of what you can do with isa_specification

// NOTE: for semantics, unaligned memory reads/writes don't work

use std::collections::{HashMap, HashSet};
use std::fs;
use std::time::Instant;

use isa_minimization::bit::{Bit, BitPattern};
use isa_minimization::instruction_semantics::{
    Effect, Expr, FieldName, Register, ValueName, add, add_carry_out, add_overflow, and_expr,
    arithmetic_shift_right, bool_const, concat, constant, count_ones, derived_value, equal,
    extract, field_is, fixed_register, immediate_field, logical_shift_right, mul as mul_expr,
    not_expr, or_expr, read_fixed_register, read_memory, read_register, read_register_field,
    register_field, rotate_right, select, shift_left, sign_extend, sub, sub_carry_out,
    sub_overflow, unsigned_less_than, xor_expr, zero_extend,
};
use isa_minimization::isa_specification::{
    ArchitecturalRegister, BranchOffset, DecodedField, DecodedInstruction, DerivedValue, FieldUses,
    ISA, Instruction, InstructionField, InstructionForm, MergeMode, Predicate, StackDirection,
    StackPointer, and, bit_eq, c, field_eq, field_in,
};
use isa_minimization::semantic_matching::instruction_seq_to_effects;
use isa_minimization::simulator::{GateOutputAssignment, Simulator};

const NETLIST_PATH: &str = "examples/arm32_core_syn.v";
const STDCELL_PATH: &str = "examples/NangateOpenCellLibrary_typical.lib";
const OPTIMIZED_NETLIST_PATH: &str = "outputs/optimized.v";

pub const REG_N: Register = Register(16);
pub const REG_Z: Register = Register(17);
pub const REG_C: Register = Register(18);
pub const REG_V: Register = Register(19);
pub const REG_PC: Register = Register(15);
pub const REG_LR: Register = Register(14);
const ARM_REGISTER_IDENTIFIER_WIDTH: u16 = 4;
const VIRTUAL_REGISTER_IDENTIFIER_WIDTH: u16 = 5;

const SHIFT_TYPE_LSL: u128 = 0b00;
const SHIFT_TYPE_LSR: u128 = 0b01;
const SHIFT_TYPE_ASR: u128 = 0b10;

const DPROC_OPCODE_AND: u128 = 0b0000;
const DPROC_OPCODE_EOR: u128 = 0b0001;
const DPROC_OPCODE_SUB: u128 = 0b0010;
const DPROC_OPCODE_RSB: u128 = 0b0011;
const DPROC_OPCODE_ADD: u128 = 0b0100;
const DPROC_OPCODE_ADC: u128 = 0b0101;
const DPROC_OPCODE_SBC: u128 = 0b0110;
const DPROC_OPCODE_RSC: u128 = 0b0111;
const DPROC_OPCODE_TST: u128 = 0b1000;
const DPROC_OPCODE_TEQ: u128 = 0b1001;
const DPROC_OPCODE_CMP: u128 = 0b1010;
const DPROC_OPCODE_CMN: u128 = 0b1011;
const DPROC_OPCODE_ORR: u128 = 0b1100;
const DPROC_OPCODE_MOV: u128 = 0b1101;
const DPROC_OPCODE_BIC: u128 = 0b1110;
const DPROC_OPCODE_MVN: u128 = 0b1111;

const HWTFR_SH_UNSIGNED_HALFWORD: u128 = 0b01;
const HWTFR_SH_UNSIGNED_HALFWORD_BITS: &str = "01";
const HWTFR_SH_SIGNED_BYTE: u128 = 0b10;
const HWTFR_SH_SIGNED_BYTE_BITS: &str = "10";
const HWTFR_SH_SIGNED_HALFWORD_BITS: &str = "11";

const COND_EQ: u128 = 0b0000;
const COND_NE: u128 = 0b0001;
const COND_CS: u128 = 0b0010;
const COND_CC: u128 = 0b0011;
const COND_MI: u128 = 0b0100;
const COND_PL: u128 = 0b0101;
const COND_VS: u128 = 0b0110;
const COND_VC: u128 = 0b0111;
const COND_HI: u128 = 0b1000;
const COND_LS: u128 = 0b1001;
const COND_GE: u128 = 0b1010;
const COND_LT: u128 = 0b1011;
const COND_GT: u128 = 0b1100;
const COND_LE: u128 = 0b1101;
const COND_AL: u128 = 0b1110;

const BIT_CLEAR: &str = "0";
const BIT_SET: &str = "1";
const REG_ZERO_BITS: &str = "0000";
const REG_PC_BITS: &str = "1111";
const COND_VALID_PATTERNS: [&str; 4] = ["0xxx", "x0xx", "xx0x", "xxx0"];
const REG_NON_PC_PATTERNS: [&str; 4] = ["0xxx", "x0xx", "xx0x", "xxx0"];
const BLOCK_REGLIST_NON_EMPTY_PATTERNS: [&str; 16] = [
    "1xxxxxxxxxxxxxxx",
    "x1xxxxxxxxxxxxxx",
    "xx1xxxxxxxxxxxxx",
    "xxx1xxxxxxxxxxxx",
    "xxxx1xxxxxxxxxxx",
    "xxxxx1xxxxxxxxxx",
    "xxxxxx1xxxxxxxxx",
    "xxxxxxx1xxxxxxxx",
    "xxxxxxxx1xxxxxxx",
    "xxxxxxxxx1xxxxxx",
    "xxxxxxxxxx1xxxxx",
    "xxxxxxxxxxx1xxxx",
    "xxxxxxxxxxxx1xxx",
    "xxxxxxxxxxxxx1xx",
    "xxxxxxxxxxxxxx1x",
    "xxxxxxxxxxxxxxx1",
];

const ENC_BIT_LOW: &str = "0";
const ENC_BIT_HIGH: &str = "1";
const ENC_DATA_PROC_CLASS: &str = "00";
const ENC_DATA_TRANSFER_CLASS: &str = "01";
const ENC_MUL_FIXED_PREFIX: &str = "000000";
const ENC_MUL_FIXED_SUFFIX: &str = "1001";
const ENC_MULL_FIXED_PREFIX: &str = "00001";
const ENC_SWP_FIXED_PREFIX: &str = "00010";
const ENC_SWP_RESERVED: &str = "00";
const ENC_SWP_FIXED_SUFFIX: &str = "00001001";
const ENC_BX_FIXED: &str = "000100101111111111110001";
const ENC_HWTFR_FIXED_PREFIX: &str = "000";
const ENC_HWTFR_REG_MARKER: &str = "00001";
const ENC_BLOCK_TRANSFER_CLASS: &str = "100";
const ENC_BRANCH_CLASS: &str = "101";

fn dv(name: &str, value: Expr) -> DerivedValue {
    DerivedValue {
        name: ValueName(name.to_owned()),
        value,
    }
}

fn with_effects(
    mut instruction: Instruction,
    effects: impl IntoIterator<Item = Effect>,
) -> Instruction {
    for effect in effects {
        instruction = instruction.effect(effect);
    }
    instruction
}

fn reg(register: u8) -> Expr {
    fixed_register(Register(register), ARM_REGISTER_IDENTIFIER_WIDTH)
}

fn read_reg(register: u8) -> Expr {
    read_register(reg(register), 32)
}

fn true_pc() -> Expr {
    read_fixed_register(REG_PC, ARM_REGISTER_IDENTIFIER_WIDTH, 32)
}

fn read_register_field_with_pc_delta(field: &str, pc_delta: u128) -> Expr {
    select(
        field_is(field, 15, 4),
        add(true_pc(), constant(pc_delta, 32)),
        read_register_field(field, 32),
    )
}

fn cond_guard() -> Expr {
    arm_condition_holds()
}

fn if_field(name: &str, value: u128) -> Expr {
    field_is(name, value, 1)
}

fn field_not(name: &str, value: u128, width: u16) -> Expr {
    not_expr(field_is(name, value, width))
}

fn guard_and(lhs: Expr, rhs: Expr) -> Expr {
    and_expr(lhs, rhs)
}

fn guard_all(guards: impl IntoIterator<Item = Expr>) -> Expr {
    guards
        .into_iter()
        .fold(bool_const(true), |acc, guard| and_expr(acc, guard))
}

fn zext32(value: Expr) -> Expr {
    zero_extend(value, 32)
}

fn bit31(value: Expr) -> Expr {
    extract(value, 31, 31)
}

fn is_zero(value: Expr, width: u16) -> Expr {
    equal(value, constant(0, width))
}

fn one_minus_flag(flag: Expr) -> Expr {
    sub(constant(1, 32), zero_extend(flag, 32))
}

fn derived(name: &str) -> Expr {
    derived_value(name)
}

fn field_bit(field: &str, bit: u16) -> Expr {
    extract(immediate_field(field), bit, bit)
}

fn field_bit_is_set(field: &str, bit: u16) -> Expr {
    equal(field_bit(field, bit), bool_const(true))
}

fn sign_fill(value: Expr) -> Expr {
    select(
        bit31(value),
        constant(u32::MAX as u128, 32),
        constant(0, 32),
    )
}

fn rrx(value: Expr) -> Expr {
    concat([
        read_fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1),
        extract(value, 31, 1),
    ])
}

fn select_shift_type(shift_type: Expr, lsl: Expr, lsr: Expr, asr: Expr, ror: Expr) -> Expr {
    select(
        equal(shift_type.clone(), constant(SHIFT_TYPE_LSL, 2)),
        lsl,
        select(
            equal(shift_type.clone(), constant(SHIFT_TYPE_LSR, 2)),
            lsr,
            select(equal(shift_type, constant(SHIFT_TYPE_ASR, 2)), asr, ror),
        ),
    )
}

fn arm_shift(value: Expr, shift_type: Expr, amount: Expr, register_shift: bool) -> Expr {
    let amount_width = if register_shift { 8 } else { 5 };
    let amount32 = zext32(amount.clone());
    let amount_is_zero = equal(amount.clone(), constant(0, amount_width));

    if register_shift {
        let amount_lt_32 = unsigned_less_than(amount.clone(), constant(32, amount_width));

        let lsl = select(
            amount_is_zero.clone(),
            value.clone(),
            select(
                amount_lt_32.clone(),
                shift_left(value.clone(), amount32.clone()),
                constant(0, 32),
            ),
        );
        let lsr = select(
            amount_is_zero.clone(),
            value.clone(),
            select(
                amount_lt_32.clone(),
                logical_shift_right(value.clone(), amount32.clone()),
                constant(0, 32),
            ),
        );
        let asr = select(
            amount_is_zero.clone(),
            value.clone(),
            select(
                amount_lt_32,
                arithmetic_shift_right(value.clone(), amount32.clone()),
                sign_fill(value.clone()),
            ),
        );
        let ror = select(amount_is_zero, value.clone(), rotate_right(value, amount32));

        select_shift_type(shift_type, lsl, lsr, asr, ror)
    } else {
        let lsl = select(
            amount_is_zero.clone(),
            value.clone(),
            shift_left(value.clone(), amount32.clone()),
        );
        let lsr = select(
            amount_is_zero.clone(),
            constant(0, 32),
            logical_shift_right(value.clone(), amount32.clone()),
        );
        let asr = select(
            amount_is_zero.clone(),
            sign_fill(value.clone()),
            arithmetic_shift_right(value.clone(), amount32.clone()),
        );
        let ror = select(
            amount_is_zero,
            rrx(value.clone()),
            rotate_right(value, amount32),
        );

        select_shift_type(shift_type, lsl, lsr, asr, ror)
    }
}

fn arm_shift_carry_out(value: Expr, shift_type: Expr, amount: Expr, register_shift: bool) -> Expr {
    let amount_width = if register_shift { 8 } else { 5 };
    let amount32 = zext32(amount.clone());
    let amount_is_zero = equal(amount.clone(), constant(0, amount_width));
    let old_c = read_fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);

    let lsl_carry_1_to_31 = extract(
        logical_shift_right(value.clone(), sub(constant(32, 32), amount32.clone())),
        0,
        0,
    );
    let right_carry_1_to_31 = extract(
        logical_shift_right(value.clone(), sub(amount32.clone(), constant(1, 32))),
        0,
        0,
    );
    let asr_carry_1_to_31 = extract(
        arithmetic_shift_right(value.clone(), sub(amount32.clone(), constant(1, 32))),
        0,
        0,
    );
    let ror_carry = bit31(rotate_right(value.clone(), amount32));

    if register_shift {
        let amount_lt_32 = unsigned_less_than(amount.clone(), constant(32, amount_width));
        let amount_is_32 = equal(amount, constant(32, amount_width));

        let lsl = select(
            amount_is_zero.clone(),
            old_c.clone(),
            select(
                amount_lt_32.clone(),
                lsl_carry_1_to_31,
                select(
                    amount_is_32.clone(),
                    extract(value.clone(), 0, 0),
                    bool_const(false),
                ),
            ),
        );
        let lsr = select(
            amount_is_zero.clone(),
            old_c.clone(),
            select(
                amount_lt_32.clone(),
                right_carry_1_to_31,
                select(amount_is_32, bit31(value.clone()), bool_const(false)),
            ),
        );
        let asr = select(
            amount_is_zero.clone(),
            old_c.clone(),
            select(amount_lt_32, asr_carry_1_to_31, bit31(value.clone())),
        );
        let ror = select(amount_is_zero, old_c, ror_carry);

        select_shift_type(shift_type, lsl, lsr, asr, ror)
    } else {
        let lsl = select(amount_is_zero.clone(), old_c, lsl_carry_1_to_31);
        let lsr = select(
            amount_is_zero.clone(),
            bit31(value.clone()),
            right_carry_1_to_31,
        );
        let asr = select(
            amount_is_zero.clone(),
            bit31(value.clone()),
            asr_carry_1_to_31,
        );
        let ror = select(amount_is_zero, extract(value, 0, 0), ror_carry);

        select_shift_type(shift_type, lsl, lsr, asr, ror)
    }
}

fn dproc_result() -> Expr {
    let op1 = derived("operand1");
    let op2 = derived("operand2");
    let c = zext32(read_fixed_register(
        REG_C,
        VIRTUAL_REGISTER_IDENTIFIER_WIDTH,
        1,
    ));

    let and_result = and_expr(op1.clone(), op2.clone());
    let eor_result = xor_expr(op1.clone(), op2.clone());
    let sub_result = sub(op1.clone(), op2.clone());
    let rsb_result = sub(op2.clone(), op1.clone());
    let add_result = add(op1.clone(), op2.clone());
    let adc_result = add(add(op1.clone(), op2.clone()), c.clone());
    let sbc_result = sub(
        sub(op1.clone(), op2.clone()),
        one_minus_flag(read_fixed_register(
            REG_C,
            VIRTUAL_REGISTER_IDENTIFIER_WIDTH,
            1,
        )),
    );
    let rsc_result = sub(
        sub(op2.clone(), op1.clone()),
        one_minus_flag(read_fixed_register(
            REG_C,
            VIRTUAL_REGISTER_IDENTIFIER_WIDTH,
            1,
        )),
    );
    let orr_result = or_expr(op1.clone(), op2.clone());
    let bic_result = and_expr(op1.clone(), not_expr(op2.clone()));
    let mvn_result = not_expr(op2.clone());

    let opcode = immediate_field("data_proc_opcode");
    [
        (DPROC_OPCODE_AND, and_result),
        (DPROC_OPCODE_EOR, eor_result),
        (DPROC_OPCODE_SUB, sub_result),
        (DPROC_OPCODE_RSB, rsb_result),
        (DPROC_OPCODE_ADD, add_result),
        (DPROC_OPCODE_ADC, adc_result),
        (DPROC_OPCODE_SBC, sbc_result),
        (DPROC_OPCODE_RSC, rsc_result),
        (DPROC_OPCODE_TST, and_expr(op1.clone(), op2.clone())),
        (DPROC_OPCODE_TEQ, xor_expr(op1.clone(), op2.clone())),
        (DPROC_OPCODE_CMP, sub(op1.clone(), op2.clone())),
        (DPROC_OPCODE_CMN, add(op1.clone(), op2.clone())),
        (DPROC_OPCODE_ORR, orr_result),
        (DPROC_OPCODE_MOV, op2),
        (DPROC_OPCODE_BIC, bic_result),
        (DPROC_OPCODE_MVN, mvn_result),
    ]
    .into_iter()
    .rev()
    .fold(constant(0, 32), |otherwise, (encoding, result)| {
        select(
            equal(opcode.clone(), constant(encoding, 4)),
            result,
            otherwise,
        )
    })
}

fn dproc_arithmetic_carry_out() -> Expr {
    let op1 = derived("operand1");
    let op2 = derived("operand2");
    let c = read_fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);
    let zero = bool_const(false);
    let one = bool_const(true);

    let opcode = immediate_field("data_proc_opcode");
    [
        (
            DPROC_OPCODE_SUB,
            sub_carry_out(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_RSB,
            sub_carry_out(op2.clone(), op1.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_ADD,
            add_carry_out(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_ADC,
            add_carry_out(op1.clone(), op2.clone(), c.clone(), 32),
        ),
        (
            DPROC_OPCODE_SBC,
            sub_carry_out(op1.clone(), op2.clone(), not_expr(c.clone()), 32),
        ),
        (
            DPROC_OPCODE_RSC,
            sub_carry_out(op2.clone(), op1.clone(), not_expr(c.clone()), 32),
        ),
        (
            DPROC_OPCODE_CMP,
            sub_carry_out(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_CMN,
            add_carry_out(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
    ]
    .into_iter()
    .rev()
    .fold(one, |otherwise, (encoding, result)| {
        select(
            equal(opcode.clone(), constant(encoding, 4)),
            result,
            otherwise,
        )
    })
}

fn dproc_arithmetic_overflow() -> Expr {
    let op1 = derived("operand1");
    let op2 = derived("operand2");
    let c = read_fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);
    let zero = bool_const(false);

    let opcode = immediate_field("data_proc_opcode");
    [
        (
            DPROC_OPCODE_SUB,
            sub_overflow(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_RSB,
            sub_overflow(op2.clone(), op1.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_ADD,
            add_overflow(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_ADC,
            add_overflow(op1.clone(), op2.clone(), c.clone(), 32),
        ),
        (
            DPROC_OPCODE_SBC,
            sub_overflow(op1.clone(), op2.clone(), not_expr(c.clone()), 32),
        ),
        (
            DPROC_OPCODE_RSC,
            sub_overflow(op2.clone(), op1.clone(), not_expr(c.clone()), 32),
        ),
        (
            DPROC_OPCODE_CMP,
            sub_overflow(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
        (
            DPROC_OPCODE_CMN,
            add_overflow(op1.clone(), op2.clone(), zero.clone(), 32),
        ),
    ]
    .into_iter()
    .rev()
    .fold(bool_const(false), |otherwise, (encoding, result)| {
        select(
            equal(opcode.clone(), constant(encoding, 4)),
            result,
            otherwise,
        )
    })
}

fn is_dproc_test_opcode() -> Expr {
    let opcode = immediate_field("data_proc_opcode");
    or_expr(
        or_expr(
            equal(opcode.clone(), constant(DPROC_OPCODE_TST, 4)),
            equal(opcode.clone(), constant(DPROC_OPCODE_TEQ, 4)),
        ),
        or_expr(
            equal(opcode.clone(), constant(DPROC_OPCODE_CMP, 4)),
            equal(opcode, constant(DPROC_OPCODE_CMN, 4)),
        ),
    )
}

fn is_dproc_arithmetic_opcode() -> Expr {
    let opcode = immediate_field("data_proc_opcode");
    or_expr(
        or_expr(
            or_expr(
                equal(opcode.clone(), constant(DPROC_OPCODE_SUB, 4)),
                equal(opcode.clone(), constant(DPROC_OPCODE_RSB, 4)),
            ),
            or_expr(
                equal(opcode.clone(), constant(DPROC_OPCODE_ADD, 4)),
                equal(opcode.clone(), constant(DPROC_OPCODE_ADC, 4)),
            ),
        ),
        or_expr(
            or_expr(
                equal(opcode.clone(), constant(DPROC_OPCODE_SBC, 4)),
                equal(opcode.clone(), constant(DPROC_OPCODE_RSC, 4)),
            ),
            or_expr(
                equal(opcode.clone(), constant(DPROC_OPCODE_CMP, 4)),
                equal(opcode, constant(DPROC_OPCODE_CMN, 4)),
            ),
        ),
    )
}

#[derive(Clone, Copy)]
enum FlagMode {
    FromField,
    AlwaysSet,
    AlwaysClear,
}

#[derive(Clone, Copy)]
enum TransferMode {
    Load,
    Store,
}

fn flag_guard(guard: Expr, mode: FlagMode) -> Expr {
    match mode {
        FlagMode::FromField => guard_all([guard, if_field("set_flags", 1)]),
        FlagMode::AlwaysSet => guard,
        FlagMode::AlwaysClear => bool_const(false),
    }
}

fn dproc_effects(flag_mode: FlagMode) -> Vec<Effect> {
    let result = dproc_result();
    let should_execute = cond_guard();
    let writes_result = guard_all([should_execute.clone(), not_expr(is_dproc_test_opcode())]);
    let writes_flags = guard_all([
        flag_guard(should_execute, flag_mode),
        field_not("rd_addr", 15, 4),
    ]);
    let arithmetic_flags = guard_and(writes_flags.clone(), is_dproc_arithmetic_opcode());
    let logical_flags = guard_and(writes_flags.clone(), not_expr(is_dproc_arithmetic_opcode()));

    vec![
        Effect::write_register_if(writes_result, register_field("rd_addr"), result.clone()),
        Effect::write_register_if(
            writes_flags.clone(),
            fixed_register(REG_N, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            bit31(result.clone()),
        ),
        Effect::write_register_if(
            writes_flags.clone(),
            fixed_register(REG_Z, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            is_zero(result, 32),
        ),
        Effect::write_register_if(
            arithmetic_flags.clone(),
            fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            dproc_arithmetic_carry_out(),
        ),
        Effect::write_register_if(
            arithmetic_flags,
            fixed_register(REG_V, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            dproc_arithmetic_overflow(),
        ),
        Effect::write_register_if(
            logical_flags,
            fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            derived("shifter_carry_out"),
        ),
    ]
}

fn mul_result() -> Expr {
    let product = extract(
        mul_expr(
            read_register_field("rm_addr", 32),
            read_register_field("rs_addr", 32),
        ),
        31,
        0,
    );
    select(
        if_field("do_mul_accum", 1),
        add(product.clone(), read_register_field("rn_addr", 32)),
        product,
    )
}

fn mul_effects() -> Vec<Effect> {
    let guard = cond_guard();
    let result = derived("result");
    let flags_guard = guard_all([guard.clone(), if_field("set_flags", 1)]);

    vec![
        Effect::write_register_if(guard, register_field("rd_addr"), result.clone()),
        Effect::write_register_if(
            flags_guard.clone(),
            fixed_register(REG_N, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            bit31(result.clone()),
        ),
        Effect::write_register_if(
            flags_guard,
            fixed_register(REG_Z, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            is_zero(result, 32),
        ),
    ]
}

fn mull_product() -> Expr {
    let rm_unsigned = zero_extend(read_register_field("rm_addr", 32), 64);
    let rs_unsigned = zero_extend(read_register_field("rn_addr", 32), 64);
    let rm_signed = sign_extend(read_register_field("rm_addr", 32), 64);
    let rs_signed = sign_extend(read_register_field("rn_addr", 32), 64);

    select(
        field_is("is_unsigned_mul", 0, 1),
        mul_expr(rm_unsigned, rs_unsigned),
        mul_expr(rm_signed, rs_signed),
    )
}

fn mull_result() -> Expr {
    let product = mull_product();
    let accumulator = concat([
        read_register_field("rdhi_addr", 32),
        read_register_field("rdlo_addr", 32),
    ]);

    select(
        if_field("do_mul_accum", 1),
        add(product.clone(), accumulator),
        product,
    )
}

fn mull_effects() -> Vec<Effect> {
    let guard = cond_guard();
    let result = derived("result");
    let flags_guard = guard_all([guard.clone(), if_field("set_flags", 1)]);

    vec![
        Effect::write_register_if(
            guard.clone(),
            register_field("rdlo_addr"),
            extract(result.clone(), 31, 0),
        ),
        Effect::write_register_if(
            guard,
            register_field("rdhi_addr"),
            extract(result.clone(), 63, 32),
        ),
        Effect::write_register_if(
            flags_guard.clone(),
            fixed_register(REG_N, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            extract(result.clone(), 63, 63),
        ),
        Effect::write_register_if(
            flags_guard,
            fixed_register(REG_Z, VIRTUAL_REGISTER_IDENTIFIER_WIDTH),
            is_zero(result, 64),
        ),
    ]
}

fn offset_address(base: Expr, offset: Expr, up_field: &str) -> Expr {
    select(
        if_field(up_field, 1),
        add(base.clone(), offset.clone()),
        sub(base, offset),
    )
}

fn transfer_address(base: Expr, offset: Expr, pre_field: &str, up_field: &str) -> Expr {
    select(
        if_field(pre_field, 1),
        offset_address(base.clone(), offset, up_field),
        base,
    )
}

fn transfer_writeback_address(base: Expr, offset: Expr, up_field: &str) -> Expr {
    offset_address(base, offset, up_field)
}

fn transfer_writes_back(pre_field: &str, writeback_field: &str) -> Expr {
    or_expr(if_field(pre_field, 0), if_field(writeback_field, 1))
}

fn byte_or_word_load_value(address: Expr) -> Expr {
    select(
        if_field("is_byte_tfr", 1),
        zero_extend(read_memory(address.clone(), 8), 32),
        read_memory(address, 32),
    )
}

fn byte_or_word_store_value() -> Expr {
    let rd_value = read_register_field_with_pc_delta("rd_addr", 4);
    select(
        if_field("is_byte_tfr", 1),
        extract(rd_value.clone(), 7, 0),
        rd_value,
    )
}

fn data_transfer_effects(mode: TransferMode) -> Vec<Effect> {
    let guard = cond_guard();
    let address = derived("address");
    let writeback_address = derived("writeback_address");
    let load_guard = match mode {
        TransferMode::Load => guard.clone(),
        TransferMode::Store => bool_const(false),
    };
    let store_guard = match mode {
        TransferMode::Load => bool_const(false),
        TransferMode::Store => guard.clone(),
    };
    let writeback_guard = guard_all([guard, transfer_writes_back("is_pre_idx", "do_writeback")]);

    // Non-simplified ARM7TDMI word-load behavior for little-endian unaligned addresses:
    // let precise_word = rotate_right(
    //     read_memory(and_expr(address.clone(), constant(0xffff_fffc, 32)), 32),
    //     shift_left(extract(address.clone(), 1, 0), constant(3, 2)),
    // );
    // The simplified semantics below treat memory as byte-addressed and width-aware.
    vec![
        Effect::write_register_if(
            load_guard,
            register_field("rd_addr"),
            byte_or_word_load_value(address.clone()),
        ),
        Effect::write_memory_if(
            guard_all([store_guard.clone(), if_field("is_byte_tfr", 1)]),
            address.clone(),
            extract(byte_or_word_store_value(), 7, 0),
            8,
        ),
        Effect::write_memory_if(
            guard_all([store_guard, if_field("is_byte_tfr", 0)]),
            address,
            byte_or_word_store_value(),
            32,
        ),
        Effect::write_register_if(
            writeback_guard,
            register_field("rn_addr"),
            writeback_address,
        ),
    ]
}

fn hwtfr_load_value(address: Expr) -> Expr {
    select(
        field_is("sh_bits", HWTFR_SH_UNSIGNED_HALFWORD, 2),
        zero_extend(read_memory(address.clone(), 16), 32),
        select(
            field_is("sh_bits", HWTFR_SH_SIGNED_BYTE, 2),
            sign_extend(read_memory(address.clone(), 8), 32),
            sign_extend(read_memory(address, 16), 32),
        ),
    )
}

fn hwtfr_effects(mode: TransferMode) -> Vec<Effect> {
    let guard = cond_guard();
    let address = derived("address");
    let writeback_address = derived("writeback_address");
    let load_guard = match mode {
        TransferMode::Load => guard.clone(),
        TransferMode::Store => bool_const(false),
    };
    let store_guard = match mode {
        TransferMode::Load => bool_const(false),
        TransferMode::Store => guard_all([
            guard.clone(),
            field_is("sh_bits", HWTFR_SH_UNSIGNED_HALFWORD, 2),
        ]),
    };
    let writeback_guard = guard_all([guard, transfer_writes_back("is_pre_idx", "do_writeback")]);

    // Non-simplified ARM7TDMI halfword behavior depends on BIGEND and returns
    // unpredictable data when bit 0 of a halfword address is set. The simplified
    // semantics below model aligned byte-addressed 8/16-bit memory.
    vec![
        Effect::write_register_if(
            load_guard,
            register_field("rd_addr"),
            hwtfr_load_value(address.clone()),
        ),
        Effect::write_memory_if(
            store_guard,
            address,
            extract(read_register_field_with_pc_delta("rd_addr", 4), 15, 0),
            16,
        ),
        Effect::write_register_if(
            writeback_guard,
            register_field("rn_addr"),
            writeback_address,
        ),
    ]
}

fn block_transfer_count() -> Expr {
    count_ones(immediate_field("block_reglist"))
}

fn block_transfer_byte_count() -> Expr {
    shift_left(zero_extend(block_transfer_count(), 32), constant(2, 32))
}

fn block_start_address() -> Expr {
    let base = read_register_field("rn_addr", 32);
    let byte_count = block_transfer_byte_count();
    select(
        if_field("is_up_offset_block", 1),
        select(
            if_field("is_pre_idx_block", 1),
            add(base.clone(), constant(4, 32)),
            base.clone(),
        ),
        select(
            if_field("is_pre_idx_block", 1),
            sub(base.clone(), byte_count.clone()),
            add(sub(base.clone(), byte_count), constant(4, 32)),
        ),
    )
}

fn block_writeback_address() -> Expr {
    let base = read_register_field("rn_addr", 32);
    select(
        if_field("is_up_offset_block", 1),
        add(base.clone(), block_transfer_byte_count()),
        sub(base, block_transfer_byte_count()),
    )
}

fn block_prior_register_count(register: u16) -> Expr {
    if register == 0 {
        constant(0, 16)
    } else {
        count_ones(extract(immediate_field("block_reglist"), register - 1, 0))
    }
}

fn block_register_address(register: u16) -> Expr {
    add(
        derived("start_address"),
        shift_left(
            zero_extend(block_prior_register_count(register), 32),
            constant(2, 32),
        ),
    )
}

fn block_store_register_value(register: u8) -> Expr {
    if register == 15 {
        add(true_pc(), constant(4, 32))
    } else {
        read_reg(register)
    }
}

fn block_tfr_effects(mode: TransferMode) -> Vec<Effect> {
    let guard = cond_guard();
    let load_guard = match mode {
        TransferMode::Load => guard.clone(),
        TransferMode::Store => bool_const(false),
    };
    let store_guard = match mode {
        TransferMode::Load => bool_const(false),
        TransferMode::Store => guard.clone(),
    };
    let writeback_guard = guard_all([guard, if_field("do_writeback_block", 1)]);
    let mut effects = vec![Effect::write_register_if(
        writeback_guard,
        register_field("rn_addr"),
        derived("writeback_address"),
    )];

    for register in 0..16 {
        let register_guard = field_bit_is_set("block_reglist", register);
        let address = block_register_address(register);
        effects.push(Effect::write_register_if(
            guard_all([load_guard.clone(), register_guard.clone()]),
            reg(register as u8),
            read_memory(address.clone(), 32),
        ));
        effects.push(Effect::write_memory_if(
            guard_all([store_guard.clone(), register_guard]),
            address,
            block_store_register_value(register as u8),
            32,
        ));
    }

    effects
}

fn branch_target() -> Expr {
    add(true_pc(), branch_pc_relative_offset())
}

fn branch_pc_relative_offset() -> Expr {
    sign_extend(
        concat([immediate_field("branch_offset"), constant(0, 2)]),
        32,
    )
}

fn branch_effects() -> Vec<Effect> {
    let guard = cond_guard();
    vec![
        Effect::write_register_if(
            guard_all([guard.clone(), if_field("do_link", 1)]),
            fixed_register(REG_LR, ARM_REGISTER_IDENTIFIER_WIDTH),
            derived("link_value"),
        ),
        Effect::write_register_if(
            guard,
            fixed_register(REG_PC, ARM_REGISTER_IDENTIFIER_WIDTH),
            derived("target"),
        ),
    ]
}

fn bx_effects() -> Vec<Effect> {
    vec![Effect::write_register_if(
        cond_guard(),
        fixed_register(REG_PC, ARM_REGISTER_IDENTIFIER_WIDTH),
        derived("target"),
    )]
}

fn swp_effects() -> Vec<Effect> {
    let guard = cond_guard();
    let address = derived("address");
    let load_value = derived("load_value");

    // Non-simplified SWP word loads inherit the LDR unaligned rotate and
    // endian byte-lane behavior. The simplified effects model width-aware memory.
    vec![
        Effect::write_register_if(guard.clone(), register_field("rd_addr"), load_value),
        Effect::write_memory_if(
            guard_all([guard.clone(), if_field("is_byte_tfr", 1)]),
            address.clone(),
            extract(read_register_field("rm_addr", 32), 7, 0),
            8,
        ),
        Effect::write_memory_if(
            guard_all([guard, if_field("is_byte_tfr", 0)]),
            address,
            read_register_field("rm_addr", 32),
            32,
        ),
    ]
}

fn arm_condition_holds() -> Expr {
    let n = read_fixed_register(REG_N, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);
    let z = read_fixed_register(REG_Z, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);
    let c = read_fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);
    let v = read_fixed_register(REG_V, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1);

    let n_equals_v = equal(n.clone(), v.clone());

    let conditions = [
        // EQ: Z
        (COND_EQ, z.clone()),
        // NE: !Z
        (COND_NE, not_expr(z.clone())),
        // CS/HS: C
        (COND_CS, c.clone()),
        // CC/LO: !C
        (COND_CC, not_expr(c.clone())),
        // MI: N
        (COND_MI, n.clone()),
        // PL: !N
        (COND_PL, not_expr(n.clone())),
        // VS: V
        (COND_VS, v.clone()),
        // VC: !V
        (COND_VC, not_expr(v.clone())),
        // HI: C && !Z
        (COND_HI, and_expr(c.clone(), not_expr(z.clone()))),
        // LS: !C || Z
        (COND_LS, or_expr(not_expr(c.clone()), z.clone())),
        // GE: N == V
        (COND_GE, n_equals_v.clone()),
        // LT: N != V
        (COND_LT, not_expr(n_equals_v.clone())),
        // GT: !Z && N == V
        (COND_GT, and_expr(not_expr(z.clone()), n_equals_v.clone())),
        // LE: Z || N != V
        (COND_LE, or_expr(z.clone(), not_expr(n_equals_v))),
        // AL: always
        (COND_AL, bool_const(true)),
    ];

    // cond=1111 is reserved, so the default result is false.
    conditions
        .into_iter()
        .rev()
        .fold(bool_const(false), |otherwise, (encoding, result)| {
            select(field_is("cond", encoding, 4), result, otherwise)
        })
}

// Instruction field definitions

pub fn cond() -> InstructionField {
    InstructionField::variable("cond", 4).merge_mode_uses()
}

pub fn set_flags() -> InstructionField {
    InstructionField::variable("set_flags", 1)
}

pub fn rn_addr() -> InstructionField {
    InstructionField::variable("rn_addr", 4)
        .merge_mode_uses()
        .register_read()
}

pub fn rd_addr() -> InstructionField {
    InstructionField::variable("rd_addr", 4)
        .merge_mode_uses()
        .register_write()
}

pub fn rm_addr() -> InstructionField {
    InstructionField::variable("rm_addr", 4)
        .merge_mode_uses()
        .register_read()
}

pub fn rs_addr() -> InstructionField {
    InstructionField::variable("rs_addr", 4)
        .merge_mode_uses()
        .register_read()
}

pub fn rn_addr_read_write() -> InstructionField {
    InstructionField::variable("rn_addr", 4)
        .merge_mode_uses()
        .register_read_write()
}

pub fn rd_addr_read_write() -> InstructionField {
    InstructionField::variable("rd_addr", 4)
        .merge_mode_uses()
        .register_read_write()
}

pub fn data_proc_opcode() -> InstructionField {
    InstructionField::variable("data_proc_opcode", 4).merge_mode_uses()
}

pub fn op2_imm_shift_amt() -> InstructionField {
    InstructionField::variable("op2_imm_shift_amt", 5).immediate()
}

pub fn op2_shift_type() -> InstructionField {
    InstructionField::variable("op2_shift_type", 2).merge_mode_uses()
}

pub fn imm_ror_amt() -> InstructionField {
    InstructionField::variable("imm_ror_amt", 4).immediate()
}

pub fn imm8() -> InstructionField {
    InstructionField::variable("imm8", 8).immediate()
}

pub fn do_mul_accum() -> InstructionField {
    InstructionField::variable("do_mul_accum", 1)
}

pub fn is_unsigned_mul() -> InstructionField {
    InstructionField::variable("is_unsigned_mul", 1)
}

pub fn rdhi_addr() -> InstructionField {
    InstructionField::variable("rdhi_addr", 4)
        .merge_mode_uses()
        .register_read_write()
}

pub fn rdlo_addr() -> InstructionField {
    InstructionField::variable("rdlo_addr", 4)
        .merge_mode_uses()
        .register_read_write()
}

pub fn is_pre_idx() -> InstructionField {
    InstructionField::variable("is_pre_idx", 1)
}

pub fn is_up_offset() -> InstructionField {
    InstructionField::variable("is_up_offset", 1)
}

pub fn do_writeback() -> InstructionField {
    InstructionField::variable("do_writeback", 1)
}

pub fn sh_bits() -> InstructionField {
    // Cannot have value 00
    InstructionField::variable("sh_bits", 2).merge_mode_uses()
}

pub fn imm8_high() -> InstructionField {
    InstructionField::variable("imm8_high", 4).immediate()
}

pub fn imm8_low() -> InstructionField {
    InstructionField::variable("imm8_low", 4).immediate()
}

pub fn is_byte_tfr() -> InstructionField {
    InstructionField::variable("is_byte_tfr", 1)
}

pub fn imm12() -> InstructionField {
    InstructionField::variable("imm12", 12).immediate()
}

pub fn is_pre_idx_block() -> InstructionField {
    InstructionField::variable("is_pre_idx_block", 1)
}

pub fn is_up_offset_block() -> InstructionField {
    InstructionField::variable("is_up_offset_block", 1)
}

pub fn do_writeback_block() -> InstructionField {
    InstructionField::variable("do_writeback_block", 1)
}

pub fn block_reglist() -> InstructionField {
    InstructionField::variable("block_reglist", 16).immediate()
}

pub fn do_link() -> InstructionField {
    InstructionField::variable("do_link", 1)
}

pub fn branch_offset() -> InstructionField {
    InstructionField::variable("branch_offset", 24).immediate()
}

// Instruction definitions
fn dproc_prefix(
    has_imm_bits: &'static str,
    set_flags_field: InstructionField,
) -> Vec<InstructionField> {
    vec![
        cond(),
        c(ENC_DATA_PROC_CLASS),
        c(has_imm_bits), // I bit: fixed by operand form.
        data_proc_opcode(),
        set_flags_field,
        rn_addr(),
        rd_addr(),
    ]
}

fn data_tfr_prefix(
    has_imm_offset_bits: &'static str,
    is_load_bits: &'static str,
) -> Vec<InstructionField> {
    vec![
        cond(),
        c(ENC_DATA_TRANSFER_CLASS),
        c(has_imm_offset_bits), // I bit: register offset when set, immediate offset when clear.
        is_pre_idx(),
        is_up_offset(),
        is_byte_tfr(),
        do_writeback(),
        c(is_load_bits), // L bit: fixed by the load/store/branch bucket.
        rn_addr_read_write(),
        rd_addr_read_write(),
    ]
}

fn cond_valid_predicate() -> Predicate {
    field_in("cond", COND_VALID_PATTERNS)
}

fn dproc_valid_predicate() -> Predicate {
    cond_valid_predicate()
}

fn data_tfr_valid_predicate() -> Predicate {
    cond_valid_predicate()
}

fn hwtfr_valid_predicate() -> Predicate {
    cond_valid_predicate()
}

fn block_tfr_valid_predicate() -> Predicate {
    and([
        cond_valid_predicate(),
        field_in("block_reglist", BLOCK_REGLIST_NON_EMPTY_PATTERNS),
        field_in("rn_addr", REG_NON_PC_PATTERNS),
    ])
}

fn swp_valid_predicate() -> Predicate {
    and([
        cond_valid_predicate(),
        field_in("rn_addr", REG_NON_PC_PATTERNS),
        field_in("rd_addr", REG_NON_PC_PATTERNS),
        field_in("rm_addr", REG_NON_PC_PATTERNS),
    ])
}

fn data_tfr_normal_base_predicate() -> Predicate {
    field_in("rn_addr", REG_NON_PC_PATTERNS)
}

fn data_tfr_pc_base_predicate() -> Predicate {
    and([
        field_eq("rn_addr", REG_PC_BITS),
        field_eq("is_pre_idx", BIT_SET),
        field_eq("do_writeback", BIT_CLEAR),
    ])
}

fn dproc_operand_predicate(mnemonic: &str) -> Predicate {
    match mnemonic {
        "tst" | "teq" | "cmp" | "cmn" => field_eq("rd_addr", REG_ZERO_BITS),
        "mov" | "mvn" => field_eq("rn_addr", REG_ZERO_BITS),
        _ => Predicate::Always,
    }
}

fn dproc_register_shifted_register_form(
    name: String,
    opcode_bits: &'static str,
    set_flags_field: InstructionField,
    set_flags_predicate: Predicate,
    rd_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields(dproc_prefix(BIT_CLEAR, set_flags_field))
        .fields([
            rs_addr(),
            c(ENC_BIT_LOW),
            op2_shift_type(),
            c(ENC_BIT_HIGH),
            rm_addr(),
        ])
        .derived_value(dv(
            "operand1",
            read_register_field_with_pc_delta("rn_addr", 4),
        ))
        .derived_value(dv(
            "operand2",
            arm_shift(
                read_register_field_with_pc_delta("rm_addr", 4),
                immediate_field("op2_shift_type"),
                extract(read_register_field("rs_addr", 32), 7, 0),
                true,
            ),
        ))
        .derived_value(dv(
            "shifter_carry_out",
            arm_shift_carry_out(
                read_register_field_with_pc_delta("rm_addr", 4),
                immediate_field("op2_shift_type"),
                extract(read_register_field("rs_addr", 32), 7, 0),
                true,
            ),
        ))
        .when(and([
            field_eq("data_proc_opcode", opcode_bits),
            set_flags_predicate,
            rd_predicate,
            dproc_valid_predicate(),
        ]))
}

fn dproc_register_immediate_shift_form(
    name: String,
    opcode_bits: &'static str,
    set_flags_field: InstructionField,
    set_flags_predicate: Predicate,
    rd_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields(dproc_prefix(BIT_CLEAR, set_flags_field))
        .fields([
            op2_imm_shift_amt(),
            op2_shift_type(),
            c(ENC_BIT_LOW),
            rm_addr(),
        ])
        .derived_value(dv("operand1", read_register_field("rn_addr", 32)))
        .derived_value(dv(
            "operand2",
            arm_shift(
                read_register_field("rm_addr", 32),
                immediate_field("op2_shift_type"),
                immediate_field("op2_imm_shift_amt"),
                false,
            ),
        ))
        .derived_value(dv(
            "shifter_carry_out",
            arm_shift_carry_out(
                read_register_field("rm_addr", 32),
                immediate_field("op2_shift_type"),
                immediate_field("op2_imm_shift_amt"),
                false,
            ),
        ))
        .when(and([
            field_eq("data_proc_opcode", opcode_bits),
            set_flags_predicate,
            rd_predicate,
            dproc_valid_predicate(),
        ]))
}

fn dproc_immediate_form(
    name: String,
    opcode_bits: &'static str,
    set_flags_field: InstructionField,
    set_flags_predicate: Predicate,
    rd_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields(dproc_prefix(BIT_SET, set_flags_field))
        .fields([imm_ror_amt(), imm8()])
        .derived_value(dv("operand1", read_register_field("rn_addr", 32)))
        .derived_value(dv(
            "operand2",
            rotate_right(
                zero_extend(immediate_field("imm8"), 32),
                shift_left(
                    zero_extend(immediate_field("imm_ror_amt"), 32),
                    constant(1, 32),
                ),
            ),
        ))
        .derived_value(dv(
            "shifter_carry_out",
            select(
                field_is("imm_ror_amt", 0, 4),
                read_fixed_register(REG_C, VIRTUAL_REGISTER_IDENTIFIER_WIDTH, 1),
                bit31(rotate_right(
                    zero_extend(immediate_field("imm8"), 32),
                    shift_left(
                        zero_extend(immediate_field("imm_ror_amt"), 32),
                        constant(1, 32),
                    ),
                )),
            ),
        ))
        .when(and([
            field_eq("data_proc_opcode", opcode_bits),
            set_flags_predicate,
            rd_predicate,
            dproc_valid_predicate(),
        ]))
}

fn dproc_category_reg_op2(
    name: &str,
    opcodes: &[(&'static str, &'static str)],
    set_flags_bits: &'static str,
    rd_predicate: Predicate,
) -> Instruction {
    let mut instruction = Instruction::new(name, 32);
    for (mnemonic, opcode_bits) in opcodes {
        let extra_predicate = and([rd_predicate.clone(), dproc_operand_predicate(mnemonic)]);
        let set_flags_field = c(set_flags_bits); // S bit: fixed by this data-processing bucket.
        instruction = instruction
            .form(dproc_register_shifted_register_form(
                format!("{mnemonic}_register_shifted_register"),
                opcode_bits,
                set_flags_field.clone(),
                Predicate::Always,
                extra_predicate.clone(),
            ))
            .form(dproc_register_immediate_shift_form(
                format!("{mnemonic}_register_immediate_shift"),
                opcode_bits,
                set_flags_field.clone(),
                Predicate::Always,
                extra_predicate.clone(),
            ));
    }

    let flag_mode = if set_flags_bits == BIT_SET {
        FlagMode::AlwaysSet
    } else {
        FlagMode::AlwaysClear
    };
    with_effects(instruction, dproc_effects(flag_mode))
}

fn dproc_category_imm_op2(
    name: &str,
    opcodes: &[(&'static str, &'static str)],
    set_flags_bits: &'static str,
    rd_predicate: Predicate,
) -> Instruction {
    let mut instruction = Instruction::new(name, 32);
    for (mnemonic, opcode_bits) in opcodes {
        let extra_predicate = and([rd_predicate.clone(), dproc_operand_predicate(mnemonic)]);
        let set_flags_field = c(set_flags_bits); // S bit: fixed by this data-processing bucket.
        instruction = instruction.form(dproc_immediate_form(
            format!("{mnemonic}_immediate"),
            opcode_bits,
            set_flags_field,
            Predicate::Always,
            extra_predicate,
        ));
    }

    let flag_mode = if set_flags_bits == BIT_SET {
        FlagMode::AlwaysSet
    } else {
        FlagMode::AlwaysClear
    };
    with_effects(instruction, dproc_effects(flag_mode))
}

const DPROC_ARITHMETIC_OPCODES: &[(&str, &str)] = &[
    ("sub", "0010"),
    ("rsb", "0011"),
    ("add", "0100"),
    ("adc", "0101"),
    ("sbc", "0110"),
    ("rsc", "0111"),
];

const DPROC_LOGICAL_OPCODES: &[(&str, &str)] = &[
    ("and", "0000"),
    ("eor", "0001"),
    ("orr", "1100"),
    ("bic", "1110"),
];

const DPROC_MOVE_OPCODES: &[(&str, &str)] = &[("mov", "1101"), ("mvn", "1111")];

const DPROC_FLAG_OPCODES: &[(&str, &str)] = &[
    ("and", "0000"),
    ("eor", "0001"),
    ("sub", "0010"),
    ("rsb", "0011"),
    ("add", "0100"),
    ("adc", "0101"),
    ("sbc", "0110"),
    ("rsc", "0111"),
    ("tst", "1000"),
    ("teq", "1001"),
    ("cmp", "1010"),
    ("cmn", "1011"),
    ("orr", "1100"),
    ("mov", "1101"),
    ("bic", "1110"),
    ("mvn", "1111"),
];

const DPROC_RESULT_OPCODES: &[(&str, &str)] = &[
    ("and", "0000"),
    ("eor", "0001"),
    ("sub", "0010"),
    ("rsb", "0011"),
    ("add", "0100"),
    ("adc", "0101"),
    ("sbc", "0110"),
    ("rsc", "0111"),
    ("orr", "1100"),
    ("mov", "1101"),
    ("bic", "1110"),
    ("mvn", "1111"),
];

pub fn arithmetic_s0_reg_op2() -> Instruction {
    dproc_category_reg_op2(
        "arithmetic_s0_reg_op2",
        DPROC_ARITHMETIC_OPCODES,
        BIT_CLEAR,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn arithmetic_s0_imm_op2() -> Instruction {
    dproc_category_imm_op2(
        "arithmetic_s0_imm_op2",
        DPROC_ARITHMETIC_OPCODES,
        BIT_CLEAR,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn logical_s0_reg_op2() -> Instruction {
    dproc_category_reg_op2(
        "logical_s0_reg_op2",
        DPROC_LOGICAL_OPCODES,
        BIT_CLEAR,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn logical_s0_imm_op2() -> Instruction {
    dproc_category_imm_op2(
        "logical_s0_imm_op2",
        DPROC_LOGICAL_OPCODES,
        BIT_CLEAR,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn move_s0_reg_op2() -> Instruction {
    dproc_category_reg_op2(
        "move_s0_reg_op2",
        DPROC_MOVE_OPCODES,
        BIT_CLEAR,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn move_s0_imm_op2() -> Instruction {
    dproc_category_imm_op2(
        "move_s0_imm_op2",
        DPROC_MOVE_OPCODES,
        BIT_CLEAR,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn dproc_s1_reg_op2() -> Instruction {
    dproc_category_reg_op2(
        "dproc_s1_reg_op2",
        DPROC_FLAG_OPCODES,
        BIT_SET,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn dproc_s1_imm_op2() -> Instruction {
    dproc_category_imm_op2(
        "dproc_s1_imm_op2",
        DPROC_FLAG_OPCODES,
        BIT_SET,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn branch_ops_dproc() -> Instruction {
    let mut instruction =
        Instruction::new("branch_ops_dproc", 32).branch_instruction(BranchOffset::Register);
    for set_flags_bits in [BIT_CLEAR, BIT_SET] {
        for (mnemonic, opcode_bits) in DPROC_RESULT_OPCODES {
            let form_prefix = if set_flags_bits == BIT_SET {
                format!("{mnemonic}s")
            } else {
                (*mnemonic).to_string()
            };
            let extra_predicate = and([
                field_eq("rd_addr", REG_PC_BITS),
                dproc_operand_predicate(mnemonic),
            ]);
            instruction = instruction
                .form(dproc_register_shifted_register_form(
                    format!("{form_prefix}_register_shifted_register"),
                    opcode_bits,
                    set_flags(),
                    field_eq("set_flags", set_flags_bits),
                    extra_predicate.clone(),
                ))
                .form(dproc_register_immediate_shift_form(
                    format!("{form_prefix}_register_immediate_shift"),
                    opcode_bits,
                    set_flags(),
                    field_eq("set_flags", set_flags_bits),
                    extra_predicate.clone(),
                ))
                .form(dproc_immediate_form(
                    format!("{form_prefix}_immediate"),
                    opcode_bits,
                    set_flags(),
                    field_eq("set_flags", set_flags_bits),
                    extra_predicate,
                ));
        }
    }

    with_effects(instruction, dproc_effects(FlagMode::FromField))
}

pub fn mul() -> Instruction {
    with_effects(
        Instruction::new("mul", 32).form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c(ENC_MUL_FIXED_PREFIX),
                    do_mul_accum(),
                    set_flags(),
                    rd_addr(),
                    rn_addr(),
                    rs_addr(),
                    c(ENC_MUL_FIXED_SUFFIX),
                    rm_addr(),
                ])
                .derived_value(dv("result", mul_result()))
                .when(cond_valid_predicate()),
        ),
        mul_effects(),
    )
}

pub fn multiply_ops_mul() -> Instruction {
    let mut instruction = mul();
    instruction.name = "multiply_ops_mul".to_string();
    instruction
}

pub fn mull() -> Instruction {
    with_effects(
        Instruction::new("mull", 32).form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c(ENC_MULL_FIXED_PREFIX),
                    is_unsigned_mul(),
                    do_mul_accum(),
                    set_flags(),
                    rdhi_addr(),
                    rdlo_addr(),
                    rn_addr(),
                    c(ENC_MUL_FIXED_SUFFIX),
                    rm_addr(),
                ])
                .derived_value(dv("result", mull_result()))
                .when(cond_valid_predicate()),
        ),
        mull_effects(),
    )
}

pub fn multiply_ops_mull() -> Instruction {
    let mut instruction = mull();
    instruction.name = "multiply_ops_mull".to_string();
    instruction
}

pub fn swp() -> Instruction {
    with_effects(
        Instruction::new("swp", 32).form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c(ENC_SWP_FIXED_PREFIX),
                    is_byte_tfr(),
                    c(ENC_SWP_RESERVED),
                    rn_addr(),
                    rd_addr(),
                    c(ENC_SWP_FIXED_SUFFIX),
                    rm_addr(),
                ])
                .derived_value(dv("address", read_register_field("rn_addr", 32)))
                .derived_value(dv(
                    "load_value",
                    select(
                        if_field("is_byte_tfr", 1),
                        zero_extend(read_memory(derived("address"), 8), 32),
                        read_memory(derived("address"), 32),
                    ),
                ))
                .when(swp_valid_predicate()),
        ),
        swp_effects(),
    )
}

pub fn swap_ops() -> Instruction {
    let mut instruction = swp();
    instruction.name = "swap_ops".to_string();
    instruction
}

pub fn bx() -> Instruction {
    with_effects(
        Instruction::new("bx", 32)
            .branch_instruction(BranchOffset::Register)
            .form(
                InstructionForm::new("base")
                    .fields([cond(), c(ENC_BX_FIXED), rn_addr()])
                    .derived_value(dv("target", read_register_field("rn_addr", 32)))
                    .when(cond_valid_predicate()),
            ),
        bx_effects(),
    )
}

pub fn branch_ops_bx() -> Instruction {
    let mut instruction = bx();
    instruction.name = "branch_ops_bx".to_string();
    instruction
}

fn hwtfr_reg_offset_form(
    name: &str,
    is_load_bits: &'static str,
    extra_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields([
            cond(),
            c(ENC_HWTFR_FIXED_PREFIX),
            is_pre_idx(),
            is_up_offset(),
            c(ENC_BIT_LOW),
            do_writeback(),
            c(is_load_bits), // L bit: fixed by the load/store/branch bucket.
            rn_addr_read_write(),
            rd_addr_read_write(),
            c(ENC_HWTFR_REG_MARKER),
            sh_bits(),
            c(ENC_BIT_HIGH),
            rm_addr(),
        ])
        .derived_value(dv("offset", read_register_field("rm_addr", 32)))
        .derived_value(dv(
            "address",
            transfer_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_pre_idx",
                "is_up_offset",
            ),
        ))
        .derived_value(dv(
            "writeback_address",
            transfer_writeback_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_up_offset",
            ),
        ))
        .when(and([
            hwtfr_valid_predicate(),
            field_in("rm_addr", REG_NON_PC_PATTERNS),
            extra_predicate,
        ]))
}

fn hwtfr_imm_offset_form(
    name: &str,
    is_load_bits: &'static str,
    extra_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields([
            cond(),
            c(ENC_HWTFR_FIXED_PREFIX),
            is_pre_idx(),
            is_up_offset(),
            c(ENC_BIT_HIGH),
            do_writeback(),
            c(is_load_bits), // L bit: fixed by the load/store/branch bucket.
            rn_addr_read_write(),
            rd_addr_read_write(),
            imm8_high(),
            c(ENC_BIT_HIGH),
            sh_bits(),
            c(ENC_BIT_HIGH),
            imm8_low(),
        ])
        .derived_value(dv(
            "offset",
            zero_extend(
                concat([immediate_field("imm8_high"), immediate_field("imm8_low")]),
                32,
            ),
        ))
        .derived_value(dv(
            "address",
            transfer_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_pre_idx",
                "is_up_offset",
            ),
        ))
        .derived_value(dv(
            "writeback_address",
            transfer_writeback_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_up_offset",
            ),
        ))
        .when(and([hwtfr_valid_predicate(), extra_predicate]))
}

fn hwtfr_category(
    name: &str,
    is_load_bits: &'static str,
    extra_predicate: Predicate,
) -> Instruction {
    let mode = if is_load_bits == BIT_SET {
        TransferMode::Load
    } else {
        TransferMode::Store
    };
    with_effects(
        Instruction::new(name, 32)
            .form(hwtfr_reg_offset_form(
                "register_offset",
                is_load_bits,
                and([extra_predicate.clone(), data_tfr_normal_base_predicate()]),
            ))
            .form(hwtfr_reg_offset_form(
                "register_offset_pc_base",
                is_load_bits,
                and([extra_predicate.clone(), data_tfr_pc_base_predicate()]),
            ))
            .form(hwtfr_imm_offset_form(
                "immediate_offset",
                is_load_bits,
                and([extra_predicate.clone(), data_tfr_normal_base_predicate()]),
            ))
            .form(hwtfr_imm_offset_form(
                "immediate_offset_pc_base",
                is_load_bits,
                and([extra_predicate, data_tfr_pc_base_predicate()]),
            )),
        hwtfr_effects(mode),
    )
}

pub fn hwtfr_load_ops() -> Instruction {
    hwtfr_category(
        "hwtfr_load_ops",
        BIT_SET,
        and([
            field_in("rd_addr", REG_NON_PC_PATTERNS),
            field_in(
                "sh_bits",
                [
                    HWTFR_SH_UNSIGNED_HALFWORD_BITS,
                    HWTFR_SH_SIGNED_BYTE_BITS,
                    HWTFR_SH_SIGNED_HALFWORD_BITS,
                ],
            ),
        ]),
    )
}

pub fn hwtfr_store_ops() -> Instruction {
    hwtfr_category(
        "hwtfr_store_ops",
        BIT_CLEAR,
        and([field_eq("sh_bits", HWTFR_SH_UNSIGNED_HALFWORD_BITS)]),
    )
}

pub fn branch_ops_hwtfr() -> Instruction {
    hwtfr_category(
        "branch_ops_hwtfr",
        BIT_SET,
        and([
            field_eq("rd_addr", REG_PC_BITS),
            field_in(
                "sh_bits",
                [
                    HWTFR_SH_UNSIGNED_HALFWORD_BITS,
                    HWTFR_SH_SIGNED_BYTE_BITS,
                    HWTFR_SH_SIGNED_HALFWORD_BITS,
                ],
            ),
        ]),
    )
    .branch_instruction(BranchOffset::Register)
}

fn data_tfr_register_offset_form(
    name: &str,
    is_load_bits: &'static str,
    extra_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields(data_tfr_prefix(BIT_SET, is_load_bits))
        .fields([
            op2_imm_shift_amt(),
            op2_shift_type(),
            c(ENC_BIT_LOW),
            rm_addr(),
        ])
        .derived_value(dv(
            "offset",
            arm_shift(
                read_register_field("rm_addr", 32),
                immediate_field("op2_shift_type"),
                immediate_field("op2_imm_shift_amt"),
                false,
            ),
        ))
        .derived_value(dv(
            "address",
            transfer_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_pre_idx",
                "is_up_offset",
            ),
        ))
        .derived_value(dv(
            "writeback_address",
            transfer_writeback_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_up_offset",
            ),
        ))
        .when(and([
            data_tfr_valid_predicate(),
            field_in("rm_addr", REG_NON_PC_PATTERNS),
            extra_predicate,
        ]))
}

fn data_tfr_immediate_offset_form(
    name: &str,
    is_load_bits: &'static str,
    extra_predicate: Predicate,
) -> InstructionForm {
    InstructionForm::new(name)
        .fields(data_tfr_prefix(BIT_CLEAR, is_load_bits))
        .fields([imm12()])
        .derived_value(dv("offset", zero_extend(immediate_field("imm12"), 32)))
        .derived_value(dv(
            "address",
            transfer_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_pre_idx",
                "is_up_offset",
            ),
        ))
        .derived_value(dv(
            "writeback_address",
            transfer_writeback_address(
                read_register_field("rn_addr", 32),
                derived("offset"),
                "is_up_offset",
            ),
        ))
        .when(and([data_tfr_valid_predicate(), extra_predicate]))
}

fn data_tfr_category(
    name: &str,
    is_load_bits: &'static str,
    extra_predicate: Predicate,
) -> Instruction {
    let mode = if is_load_bits == BIT_SET {
        TransferMode::Load
    } else {
        TransferMode::Store
    };
    with_effects(
        Instruction::new(name, 32)
            .form(data_tfr_register_offset_form(
                "register_offset",
                is_load_bits,
                and([extra_predicate.clone(), data_tfr_normal_base_predicate()]),
            ))
            .form(data_tfr_register_offset_form(
                "register_offset_pc_base",
                is_load_bits,
                and([extra_predicate.clone(), data_tfr_pc_base_predicate()]),
            ))
            .form(data_tfr_immediate_offset_form(
                "immediate_offset",
                is_load_bits,
                and([extra_predicate.clone(), data_tfr_normal_base_predicate()]),
            ))
            .form(data_tfr_immediate_offset_form(
                "immediate_offset_pc_base",
                is_load_bits,
                and([extra_predicate, data_tfr_pc_base_predicate()]),
            )),
        data_transfer_effects(mode),
    )
}

pub fn load_ops() -> Instruction {
    data_tfr_category(
        "load_ops",
        BIT_SET,
        field_in("rd_addr", REG_NON_PC_PATTERNS),
    )
}

pub fn store_ops() -> Instruction {
    data_tfr_category("store_ops", BIT_CLEAR, Predicate::Always)
}

pub fn branch_ops_data_tfr() -> Instruction {
    data_tfr_category(
        "branch_ops_data_tfr",
        BIT_SET,
        field_eq("rd_addr", REG_PC_BITS),
    )
    .branch_instruction(BranchOffset::Register)
}

fn block_tfr_form(is_load_block_bits: &'static str, extra_predicate: Predicate) -> InstructionForm {
    InstructionForm::new("base")
        .fields([
            cond(),
            c(ENC_BLOCK_TRANSFER_CLASS),
            is_pre_idx_block(),
            is_up_offset_block(),
            c(BIT_CLEAR), // S bit: user-mode/PSR load form is not supported.
            do_writeback_block(),
            c(is_load_block_bits), // L bit: fixed by the block load/store/branch bucket.
            rn_addr_read_write(),
            block_reglist(),
        ])
        .derived_value(dv("transfer_count", block_transfer_count()))
        .derived_value(dv("start_address", block_start_address()))
        .derived_value(dv("writeback_address", block_writeback_address()))
        .when(and([block_tfr_valid_predicate(), extra_predicate]))
}

fn block_tfr_category(
    name: &str,
    is_load_block_bits: &'static str,
    extra_predicate: Predicate,
) -> Instruction {
    let mode = if is_load_block_bits == BIT_SET {
        TransferMode::Load
    } else {
        TransferMode::Store
    };
    with_effects(
        Instruction::new(name, 32).form(block_tfr_form(is_load_block_bits, extra_predicate)),
        block_tfr_effects(mode),
    )
}

pub fn block_load_ops() -> Instruction {
    block_tfr_category("block_load_ops", BIT_SET, bit_eq(16, Bit::Low))
}

pub fn block_store_ops() -> Instruction {
    block_tfr_category("block_store_ops", BIT_CLEAR, Predicate::Always)
}

pub fn branch_ops_block_tfr() -> Instruction {
    block_tfr_category("branch_ops_block_tfr", BIT_SET, bit_eq(16, Bit::High))
        .branch_instruction(BranchOffset::Register)
}

pub fn b() -> Instruction {
    with_effects(
        Instruction::new("b", 32)
            .branch_instruction(BranchOffset::PCRelative(branch_pc_relative_offset()))
            .form(
                InstructionForm::new("base")
                    .fields([cond(), c(ENC_BRANCH_CLASS), do_link(), branch_offset()])
                    .derived_value(dv("target", branch_target()))
                    .derived_value(dv("link_value", sub(true_pc(), constant(4, 32))))
                    .when(cond_valid_predicate()),
            ),
        branch_effects(),
    )
}

pub fn branch_ops_b() -> Instruction {
    let mut instruction = b();
    instruction.name = "branch_ops_b".to_string();
    instruction
}

pub fn pc_to_instruction_index(pc_value: u128, _program: Vec<DecodedInstruction>) -> u32 {
    ((pc_value - 8) / 4) as u32
}

pub fn instructions() -> Vec<Instruction> {
    vec![
        load_ops(),
        hwtfr_load_ops(),
        block_load_ops(),
        store_ops(),
        hwtfr_store_ops(),
        block_store_ops(),
        arithmetic_s0_reg_op2(),
        arithmetic_s0_imm_op2(),
        logical_s0_reg_op2(),
        logical_s0_imm_op2(),
        move_s0_reg_op2(),
        move_s0_imm_op2(),
        dproc_s1_reg_op2(),
        dproc_s1_imm_op2(),
        multiply_ops_mul(),
        multiply_ops_mull(),
        swap_ops(),
        branch_ops_b(),
        branch_ops_bx(),
        branch_ops_dproc(),
        branch_ops_data_tfr(),
        branch_ops_hwtfr(),
        branch_ops_block_tfr(),
    ]
}

pub fn gpr(identifier: u8) -> ArchitecturalRegister {
    ArchitecturalRegister {
        identifier,
        identifier_width: ARM_REGISTER_IDENTIFIER_WIDTH as u8,
        width: 32,
    }
}

pub fn flag(identifier: u8) -> ArchitecturalRegister {
    ArchitecturalRegister {
        identifier,
        identifier_width: VIRTUAL_REGISTER_IDENTIFIER_WIDTH as u8,
        width: 1,
    }
}

pub fn gprs() -> Vec<ArchitecturalRegister> {
    (0..=15).map(|i| gpr(i)).collect()
}

pub fn flags() -> Vec<ArchitecturalRegister> {
    vec![flag(REG_N.0), flag(REG_Z.0), flag(REG_C.0), flag(REG_V.0)]
}

pub fn registers() -> Vec<ArchitecturalRegister> {
    gprs().into_iter().chain(flags()).collect()
}

fn instance_name_on_line(line: &str) -> Option<&str> {
    let before_connections = line.split_once('(')?.0.trim_end();
    let mut tokens = before_connections.split_whitespace();
    tokens.next()?;
    tokens.last()
}

fn bit_to_verilog_const(bit: Bit) -> &'static str {
    match bit {
        Bit::Low => "1'b0",
        Bit::High => "1'b1",
        Bit::Var | Bit::Test => panic!("Cannot assign non-constant bit {:?}", bit),
    }
}

fn write_optimized_verilog(
    source_path: &str,
    output_path: &str,
    gates_to_comment: &HashSet<String>,
    assignments: &[GateOutputAssignment],
) -> std::io::Result<usize> {
    let verilog = fs::read_to_string(source_path)?;
    let mut commented_gate_count = 0;
    let mut comment_current_instance = false;
    let mut optimized_lines = Vec::new();

    for line in verilog.lines() {
        let starts_unused_instance = !comment_current_instance
            && instance_name_on_line(line).is_some_and(|name| gates_to_comment.contains(name));

        let should_comment = comment_current_instance || starts_unused_instance;
        if should_comment {
            optimized_lines.push(format!("//{line}"));

            if starts_unused_instance {
                commented_gate_count += 1;
            }

            comment_current_instance = !line.trim_end().ends_with(';');
        } else {
            optimized_lines.push(line.to_string());
        }
    }

    let assign_statements: Vec<String> = assignments
        .iter()
        .map(|assignment| {
            format!(
                "  assign {} = {};",
                assignment.wire_name,
                bit_to_verilog_const(assignment.value)
            )
        })
        .collect();

    if !assign_statements.is_empty() {
        let endmodule_idx = optimized_lines
            .iter()
            .rposition(|line| line.trim() == "endmodule")
            .expect("optimized verilog should contain endmodule");
        optimized_lines.splice(endmodule_idx..endmodule_idx, assign_statements);
    }

    let mut optimized_verilog = optimized_lines.join("\n");
    optimized_verilog.push('\n');

    if let Some(parent) = std::path::Path::new(output_path).parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(output_path, optimized_verilog)?;

    Ok(commented_gate_count)
}

fn main() {
    let mut args = std::env::args().skip(1);
    let program_binary_path = args.next().unwrap_or_else(|| {
        eprintln!("Usage: cargo run --example arm32 -- <program.bin> [--validate]");
        std::process::exit(2);
    });
    let validate_optimization = args.any(|arg| arg == "--validate");
    let arm32 = ISA {
        registers: registers(),
        instructions: instructions(),
        sp: StackPointer {
            register: gpr(12),
            stack_size: 32,
            direction: StackDirection::Downwards,
        },
        pc: gpr(15),
        pc_to_instruction_index,
    };

    let decoded_program: Vec<DecodedInstruction> =
        DecodedInstruction::decode_program(&program_binary_path, &arm32).unwrap();

    // Create hashmap of FieldUses
    let mut field_values: HashMap<FieldName, FieldUses> = std::collections::HashMap::new();

    for decoded in decoded_program.iter() {
        for DecodedField {
            name,
            value,
            merge_mode,
            ..
        } in &decoded.fields
        {
            let name = match name {
                Some(name) => name.clone(),
                None => {
                    // If there is no name, this is a constant field, so we can just ignore it
                    continue;
                }
            };
            let default_val = match merge_mode {
                MergeMode::Uses => FieldUses::Uses {
                    name: name.clone(),
                    patterns: [value.clone()].iter().cloned().collect(),
                    len: value.len(),
                },
                MergeMode::VariableBits => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: Some(value.clone()),
                    len: value.len(),
                },
            };
            match field_values.entry(name.clone()).or_insert(default_val) {
                FieldUses::Uses {
                    name: _,
                    patterns,
                    len,
                } => {
                    assert_eq!(*len, value.len());
                    let new_pattern = value.clone();
                    patterns.insert(new_pattern);
                }
                FieldUses::VariableBits {
                    name: _,
                    pattern,
                    len,
                } => {
                    assert_eq!(*len, value.len());
                    let pattern = pattern
                        .as_mut()
                        .expect("observed VariableBits field should be populated");
                    // Any bits which are different between the existing pattern and the new pattern should become variable bits
                    let new_pattern = value.clone();
                    if pattern.len() != new_pattern.len() {
                        panic!("Pattern length mismatch for field '{}'", name);
                    }
                    let mut indices_to_update = Vec::new();
                    for (i, (old_bit, new_bit)) in
                        pattern.bits.iter().zip(new_pattern.bits.iter()).enumerate()
                    {
                        if old_bit != new_bit {
                            indices_to_update.push(i);
                        }
                    }
                    for i in indices_to_update {
                        pattern.bits[i] = Bit::Var;
                    }
                }
            }
        }
    }

    // Merge patterns for fields with merge_mode_uses, to reduce the number of encodings we need to generate
    for (_, field_uses) in field_values.iter_mut() {
        if let FieldUses::Uses {
            name: _,
            patterns,
            len,
        } = field_uses
        {
            // Merge the patterns to reduce the number of encodings we need to generate
            let merged = FieldUses::Uses {
                name: "__".to_string(),
                patterns: patterns.clone(),
                len: *len,
            }
            .merge();
            *field_uses = merged;
        }
    }
    let mut valid_encodings = HashSet::new();

    // for each instruction, print all valid encodings
    for instr in &arm32.instructions {
        println!("Instruction: {}", instr.name);
        for form in &instr.forms {
            // We only want to get the encodings for the form if this form actually is used in the program
            if !decoded_program
                .iter()
                .any(|decoded| decoded.name == instr.name && decoded.form.name == form.name)
            {
                continue;
            }
            let encodings = form.fields_to_encodings(&field_values);
            println!("  Form: {}", form.name);
            for encoding in encodings {
                valid_encodings.insert(encoding.clone());

                // print as string, 0s and 1s for High and Low, and Xs for Var
                let encoding_str: String = encoding
                    .bits
                    .iter()
                    .map(|b| match b {
                        Bit::Low => '0',
                        Bit::High => '1',
                        Bit::Var => 'x',
                        Bit::Test => panic!("Test bits should not be present in final encodings"),
                    })
                    .collect();
                println!("    Encoding: {}", encoding_str);
            }
        }
    }

    println!(
        "Generated {} unique instruction encodings for optimization",
        valid_encodings.len()
    );

    // Print each field and its possible values
    println!("Fields and their possible values:");
    for (field_name, field_uses) in &field_values {
        println!("  Field: {}", field_name);
        match field_uses {
            FieldUses::Uses {
                name: _, patterns, ..
            } => {
                for pattern in patterns {
                    let pattern_str: String = pattern
                        .bits
                        .iter()
                        .map(|b| match b {
                            Bit::Low => '0',
                            Bit::High => '1',
                            Bit::Var => 'x',
                            Bit::Test => {
                                panic!("Test bits should not be present in final field patterns")
                            }
                        })
                        .collect();
                    println!("    Pattern: {}", pattern_str);
                }
            }
            FieldUses::VariableBits {
                name: _, pattern, ..
            } => {
                if let Some(pattern) = pattern {
                    let pattern_str: String = pattern
                        .bits
                        .iter()
                        .map(|b| match b {
                            Bit::Low => '0',
                            Bit::High => '1',
                            Bit::Var => 'x',
                            Bit::Test => {
                                panic!("Test bits should not be present in final field patterns")
                            }
                        })
                        .collect();
                    println!("    Pattern: {}", pattern_str);
                }
            }
        }
    }

    let simulator = Simulator::from_file(NETLIST_PATH, STDCELL_PATH);
    let sim_inputs: Vec<_> = valid_encodings
        .iter()
        .map(|encoding| simulator.pattern_to_sim_inputs(encoding, "inst"))
        .collect();

    println!(
        "Running gate usage optimization over {} simulation input patterns",
        sim_inputs.len()
    );

    let compiled_sim_inputs = simulator.compile_optimization_inputs(&sim_inputs);
    let mut optimization_workspace = simulator.optimization_workspace();
    let optimization_started = Instant::now();
    let optimization = simulator.optimize_compiled_gate_usage_details_with_workspace(
        &compiled_sim_inputs,
        &mut optimization_workspace,
    );
    let optimization_elapsed = optimization_started.elapsed();

    let gates_to_comment: HashSet<String> = optimization.gates_to_comment.iter().cloned().collect();

    let commented_gate_count = write_optimized_verilog(
        NETLIST_PATH,
        OPTIMIZED_NETLIST_PATH,
        &gates_to_comment,
        &optimization.assignments,
    )
    .unwrap();

    println!(
        "Kept {} combinational gates, commented out {} gates, added {} assigns, and wrote {}",
        simulator.combinational_gate_count() - optimization.gates_to_comment.len(),
        commented_gate_count,
        optimization.assignments.len(),
        OPTIMIZED_NETLIST_PATH
    );
    println!(
        "Optimization without validation took {:.3?}",
        optimization_elapsed
    );
    if validate_optimization {
        let validation = simulator.validate_compiled_gate_usage_optimization_with_workspace(
            &compiled_sim_inputs,
            &optimization,
            &mut optimization_workspace,
        );
        println!(
            "Validated {} input patterns with {} effective-output comparisons, {} replacement-output proofs, and {} gate evaluations in {:.3?}",
            validation.input_patterns_checked,
            validation.effective_outputs_checked,
            validation.replacement_outputs_checked,
            validation.gate_evaluations,
            validation.elapsed,
        );
    }
    // // Program: add r0, r0, r1; mov r1, r0
    // let program = DecodedInstruction::decode_program_str(
    //     "11100000100000000000000000000001\n11100001101000000001000000000000",
    //     &arm32,
    // )
    // Program: mov r5, #3; mul r4, r4, r5
    // let program = DecodedInstruction::decode_program_str(
    //     "11100011101000000101000000000011\n11100000000001000000010110010100",
    //     &arm32,
    // )
    // .unwrap();
    // let effects = instruction_seq_to_effects(&program, &arm32);
    // println!("\n\n\n\n\n\n\n");
    // for effect in &effects {
    //     println!("{:#?}", effect);
    // }

    // // program2: add r1, r0, r1
    // let program2 =
    //     DecodedInstruction::decode_program_str("11100000100000000001000000000001", &arm32).unwrap();
    // let effects2 = instruction_seq_to_effects(&program2, &arm32);
    // // effects[1] should be the write to r1 (mov r1, r0) and effects2[0] should be add r1, r0, r1. so these should be semantically equivalent in their contexts
    // assert_eq!(effects[1], effects2[0]);
}
