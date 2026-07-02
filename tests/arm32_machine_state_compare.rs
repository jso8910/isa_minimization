#[allow(dead_code)]
#[path = "../examples/arm32.rs"]
mod arm32;

use std::collections::HashMap;

use isa_minimization::{
    bit::Bit,
    instruction_semantics::FieldName,
    isa_specification::{
        DecodedField, DecodedInstruction, FieldUses, ISA, MergeMode, StackDirection, StackPointer,
    },
    semantic_matching::{BddEquality, BitWord, EquivalenceManager, MachineState},
    superoptimization::{Program, SuperoptimizationCtx},
};

fn arm32_isa() -> ISA {
    arm32_isa_with_stack_direction(StackDirection::Downwards)
}

fn arm32_isa_with_stack_direction(direction: StackDirection) -> ISA {
    ISA {
        registers: arm32::registers(),
        instructions: arm32::instructions(),
        sp: StackPointer {
            register: arm32::gpr(12),
            stack_size: 32,
            direction,
        },
        pc: arm32::gpr(15),
    }
}

fn field_uses_from(program: &[DecodedInstruction]) -> HashMap<FieldName, FieldUses> {
    let mut field_values = HashMap::new();

    for decoded in program {
        for DecodedField {
            name,
            value,
            merge_mode,
            ..
        } in &decoded.fields
        {
            let Some(name) = name else {
                continue;
            };
            let default_value = match merge_mode {
                MergeMode::Uses => FieldUses::Uses {
                    name: name.clone(),
                    patterns: [value.clone()].into_iter().collect(),
                },
                MergeMode::VariableBits => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: value.clone(),
                },
            };

            match field_values.entry(name.clone()).or_insert(default_value) {
                FieldUses::Uses { patterns, .. } => {
                    patterns.insert(value.clone());
                }
                FieldUses::VariableBits { pattern, .. } => {
                    assert_eq!(pattern.len(), value.len());
                    for (pattern_bit, value_bit) in pattern.bits.iter_mut().zip(&value.bits) {
                        if pattern_bit != value_bit {
                            *pattern_bit = Bit::Var;
                        }
                    }
                }
            }
        }
    }

    field_values
}

fn decode_one(bits: &str, isa: &ISA) -> DecodedInstruction {
    let decoded = DecodedInstruction::decode_program_str(bits, isa).expect("ARM32 decode failed");
    assert_eq!(decoded.len(), 1);
    decoded.into_iter().next().unwrap()
}

fn mov_imm(rd: u8, imm8: u8) -> String {
    format!("1110001110100000{rd:04b}0000{imm8:08b}")
}

fn str_imm(rd: u8, rn: u8, offset: i16, is_byte: bool) -> String {
    let is_up_offset = offset >= 0;
    let offset = offset.unsigned_abs();
    assert!(
        offset < (1 << 12),
        "ARM32 immediate transfer offset is 12 bits"
    );
    format!(
        "11100101{}{}00{rn:04b}{rd:04b}{offset:012b}",
        if is_up_offset { '1' } else { '0' },
        if is_byte { '1' } else { '0' },
    )
}

fn strb_imm(rd: u8, rn: u8, offset: i16) -> String {
    str_imm(rd, rn, offset, true)
}

fn str_word_imm(rd: u8, rn: u8, offset: i16) -> String {
    str_imm(rd, rn, offset, false)
}

fn decoded_sequence(isa: &ISA, bits: &[String]) -> Vec<DecodedInstruction> {
    bits.iter().map(|bits| decode_one(bits, isa)).collect()
}

fn program_from(instructions: Vec<DecodedInstruction>) -> Program {
    let length = instructions.len();
    Program::from_instructions(instructions, length)
}

fn ctx_for_execute<'a>(
    isa: &'a ISA,
    original: Vec<DecodedInstruction>,
    protected_registers: Vec<isa_minimization::isa_specification::ArchitecturalRegister>,
) -> SuperoptimizationCtx<'a> {
    let valid_field_uses = field_uses_from(&original);
    SuperoptimizationCtx::new_from_single_instruction(
        original
            .first()
            .expect("integration test should have an original instruction")
            .clone(),
        valid_field_uses,
        isa,
        protected_registers,
    )
}

fn unequal_counterexample(
    isa: &ISA,
    left: &[DecodedInstruction],
    right: &[DecodedInstruction],
) -> MachineState {
    let left = program_from(left.to_vec());
    let right = program_from(right.to_vec());
    let mut manager = EquivalenceManager::from_instructions(&left, &right, isa);
    let result = manager
        .compare_instructions()
        .expect("ARM32 BDD compare should allocate");
    let BddEquality::Unequal(state) = result else {
        panic!("predefined ARM32 sequences should be observably different");
    };
    state
}

fn execute_both(
    isa: &ISA,
    left: Vec<DecodedInstruction>,
    right: Vec<DecodedInstruction>,
    protected_registers: Vec<isa_minimization::isa_specification::ArchitecturalRegister>,
) -> (MachineState, MachineState, MachineState) {
    let counterexample = unequal_counterexample(isa, &left, &right);
    let ctx = ctx_for_execute(isa, left.clone(), protected_registers);
    let left = program_from(left);
    let right = program_from(right);

    (
        counterexample.clone(),
        ctx.execute_test(&left, &counterexample),
        ctx.execute_test(&right, &counterexample),
    )
}

fn execute_both_with_sp(
    isa: &ISA,
    left: Vec<DecodedInstruction>,
    right: Vec<DecodedInstruction>,
    sp: u128,
) -> (MachineState, MachineState, MachineState) {
    let mut counterexample = unequal_counterexample(isa, &left, &right);
    counterexample.registers.insert(12, BitWord::new(sp, 32));
    let ctx = ctx_for_execute(isa, left.clone(), vec![]);
    let left = program_from(left);
    let right = program_from(right);

    (
        counterexample.clone(),
        ctx.execute_test(&left, &counterexample),
        ctx.execute_test(&right, &counterexample),
    )
}

fn register_value(state: &MachineState, register: u8) -> BitWord {
    *state
        .registers
        .get(&(register as u128))
        .expect("expected register to be present")
}

fn memory_value(state: &MachineState, address: u128) -> BitWord {
    *state
        .memory
        .get(&(address, 8))
        .expect("expected byte memory write to be present")
}

fn low_byte(word: BitWord) -> BitWord {
    BitWord::new(word.value & 0xff, 8)
}

fn hamming_distance(left: BitWord, right: BitWord) -> u32 {
    assert_eq!(left.width, right.width);
    (left.value ^ right.value).count_ones()
}

fn shared_memory_cost(left_state: &MachineState, right_state: &MachineState, address: u128) -> u32 {
    hamming_distance(
        memory_value(left_state, address),
        memory_value(right_state, address),
    )
}

#[test]
fn bdd_counterexample_execute_test_and_compare_cover_scratch_and_protected_registers() {
    let isa = arm32_isa();
    let left = decoded_sequence(&isa, &[mov_imm(1, 1)]);
    let right = decoded_sequence(&isa, &[mov_imm(1, 2), mov_imm(8, 5)]);

    let mut counterexample = unequal_counterexample(&isa, &left, &right);
    counterexample.registers.remove(&8);
    let ctx = ctx_for_execute(&isa, left.clone(), vec![arm32::gpr(8)]);
    let left = program_from(left);
    let right = program_from(right);
    let left_state = ctx.execute_test(&left, &counterexample);
    let right_state = ctx.execute_test(&right, &counterexample);

    assert_eq!(register_value(&left_state, 1), BitWord::new(1, 32));
    assert_eq!(register_value(&right_state, 1), BitWord::new(2, 32));
    assert_eq!(register_value(&right_state, 8), BitWord::new(5, 32));

    let scratch_cost = left_state.compare(&right_state, &[], &isa.sp, 0);
    let protected_cost = left_state.compare(&right_state, &[arm32::gpr(8)], &isa.sp, 0);
    assert!(scratch_cost > 0);
    assert_eq!(
        protected_cost - scratch_cost,
        32 + isa_minimization::constants::WEIGHT_EXTRA_WRITE
    );
}

#[test]
fn bdd_counterexample_execute_test_and_compare_cover_arbitrary_memory_writes() {
    let isa = arm32_isa();
    let left = decoded_sequence(&isa, &[strb_imm(1, 0, 0)]);
    let right = decoded_sequence(&isa, &[strb_imm(2, 0, 0), strb_imm(2, 0, 4)]);

    let (counterexample, left_state, right_state) = execute_both(&isa, left, right, vec![]);
    let base = register_value(&counterexample, 0).value;
    let left_shared = memory_value(&left_state, base);
    let right_shared = memory_value(&right_state, base);

    assert_eq!(left_shared, low_byte(register_value(&counterexample, 1)));
    assert_eq!(right_shared, low_byte(register_value(&counterexample, 2)));
    assert_eq!(
        memory_value(&right_state, base + 4),
        low_byte(register_value(&counterexample, 2))
    );
    assert_ne!(left_shared, right_shared);

    let expected_shared_cost = hamming_distance(left_shared, right_shared);
    assert_eq!(
        left_state.compare(&right_state, &[], &isa.sp, 0),
        expected_shared_cost + 8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE
    );
}

#[test]
fn bdd_counterexample_execute_test_and_compare_ignore_stack_region_scratch_writes() {
    let isa = arm32_isa_with_stack_direction(StackDirection::Upwards);
    let left = decoded_sequence(&isa, &[strb_imm(1, 12, 33)]);
    let right = decoded_sequence(&isa, &[strb_imm(2, 12, 33), strb_imm(2, 12, 4)]);

    let (counterexample, left_state, right_state) = execute_both(&isa, left, right, vec![]);
    let sp = register_value(&counterexample, 12).value;
    let left_shared = memory_value(&left_state, sp + 33);
    let right_shared = memory_value(&right_state, sp + 33);

    assert_eq!(
        memory_value(&right_state, sp + 4),
        low_byte(register_value(&counterexample, 2))
    );
    assert_ne!(left_shared, right_shared);

    let expected_shared_cost = hamming_distance(left_shared, right_shared);
    assert_eq!(
        left_state.compare(&right_state, &[], &isa.sp, sp),
        expected_shared_cost
    );
    assert_eq!(
        right_state.compare(&left_state, &[], &isa.sp, sp),
        expected_shared_cost + 8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE
    );
}

#[test]
fn bdd_counterexample_execute_test_and_compare_count_writes_just_outside_stack_region() {
    let isa = arm32_isa_with_stack_direction(StackDirection::Upwards);
    let left = decoded_sequence(&isa, &[strb_imm(1, 12, 34)]);
    let right = decoded_sequence(&isa, &[strb_imm(2, 12, 34), strb_imm(2, 12, 33)]);

    let (counterexample, left_state, right_state) = execute_both(&isa, left, right, vec![]);
    let sp = register_value(&counterexample, 12).value;
    let left_shared = memory_value(&left_state, sp + 34);
    let right_shared = memory_value(&right_state, sp + 34);

    assert_eq!(
        memory_value(&right_state, sp + 33),
        low_byte(register_value(&counterexample, 2))
    );
    assert_ne!(left_shared, right_shared);

    let expected_shared_cost = hamming_distance(left_shared, right_shared);
    assert_eq!(
        left_state.compare(&right_state, &[], &isa.sp, sp),
        expected_shared_cost + 8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE
    );
}

#[test]
fn bdd_counterexample_execute_test_and_compare_cover_upward_stack_boundaries() {
    let isa = arm32_isa_with_stack_direction(StackDirection::Upwards);
    let sp = 0x100;

    for (extra_offset, expected_extra_bytes) in [(1, 0), (32, 0), (0, 1), (33, 1)] {
        let left = decoded_sequence(&isa, &[strb_imm(1, 12, 40)]);
        let right = decoded_sequence(&isa, &[strb_imm(2, 12, 40), strb_imm(2, 12, extra_offset)]);
        let (_counterexample, left_state, right_state) =
            execute_both_with_sp(&isa, left, right, sp);
        let expected_shared_cost = shared_memory_cost(&left_state, &right_state, sp + 40);

        assert_eq!(
            left_state.compare(&right_state, &[], &isa.sp, sp),
            expected_shared_cost
                + expected_extra_bytes * (8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE),
            "extra write at upward stack offset {extra_offset}"
        );
    }
}

#[test]
fn bdd_counterexample_execute_test_and_compare_cover_downward_stack_boundaries_and_above_sp() {
    let isa = arm32_isa_with_stack_direction(StackDirection::Downwards);
    let sp = 0x100;

    for (extra_offset, expected_extra_bytes) in [(-1, 0), (-32, 0), (0, 1), (-33, 1), (1, 1)] {
        let left = decoded_sequence(&isa, &[strb_imm(1, 12, 40)]);
        let right = decoded_sequence(&isa, &[strb_imm(2, 12, 40), strb_imm(2, 12, extra_offset)]);
        let (_counterexample, left_state, right_state) =
            execute_both_with_sp(&isa, left, right, sp);
        let expected_shared_cost = shared_memory_cost(&left_state, &right_state, sp + 40);

        assert_eq!(
            left_state.compare(&right_state, &[], &isa.sp, sp),
            expected_shared_cost
                + expected_extra_bytes * (8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE),
            "extra write at downward stack offset {extra_offset}"
        );
    }
}

#[test]
fn bdd_counterexample_execute_test_and_compare_counts_word_writes_crossing_upward_stack_boundary() {
    let isa = arm32_isa_with_stack_direction(StackDirection::Upwards);
    let sp = 0x100;
    let byte_cost = 8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE;

    for (extra_offset, expected_extra_bytes) in [(30, 1), (-2, 3)] {
        let left = decoded_sequence(&isa, &[strb_imm(1, 12, 40)]);
        let right = decoded_sequence(
            &isa,
            &[strb_imm(2, 12, 40), str_word_imm(2, 12, extra_offset)],
        );
        let (_counterexample, left_state, right_state) =
            execute_both_with_sp(&isa, left, right, sp);
        let expected_shared_cost = shared_memory_cost(&left_state, &right_state, sp + 40);

        assert_eq!(
            left_state.compare(&right_state, &[], &isa.sp, sp),
            expected_shared_cost + expected_extra_bytes * byte_cost,
            "word write crossing upward stack boundary from offset {extra_offset}"
        );
    }
}

#[test]
fn bdd_counterexample_execute_test_and_compare_counts_word_writes_crossing_downward_stack_boundary()
{
    let isa = arm32_isa_with_stack_direction(StackDirection::Downwards);
    let sp = 0x100;
    let byte_cost = 8 + isa_minimization::constants::WEIGHT_EXTRA_WRITE;

    for (extra_offset, expected_extra_bytes) in [(-34, 2), (-2, 2)] {
        let left = decoded_sequence(&isa, &[strb_imm(1, 12, 40)]);
        let right = decoded_sequence(
            &isa,
            &[strb_imm(2, 12, 40), str_word_imm(2, 12, extra_offset)],
        );
        let (_counterexample, left_state, right_state) =
            execute_both_with_sp(&isa, left, right, sp);
        let expected_shared_cost = shared_memory_cost(&left_state, &right_state, sp + 40);

        assert_eq!(
            left_state.compare(&right_state, &[], &isa.sp, sp),
            expected_shared_cost + expected_extra_bytes * byte_cost,
            "word write crossing downward stack boundary from offset {extra_offset}"
        );
    }
}
