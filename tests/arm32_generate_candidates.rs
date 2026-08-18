#[allow(dead_code, unused_imports)]
#[path = "../examples/arm32/isa.rs"]
mod arm32;

use std::{collections::HashMap, panic, time::Instant};

use isa_minimization::{
    bit::{Bit, BitPattern},
    instruction_semantics::{Expr, FieldName},
    isa_specification::{
        ArchitecturalRegister, BranchOffset, DecodedField, DecodedInstruction, FieldUses, ISA,
        MergeMode, StackDirection, StackPointer, instruction_valid_under_field_uses,
    },
    superoptimization::SuperoptimizationCtx,
};

fn arm32_isa() -> ISA {
    arm32_isa_with_instructions(arm32::instructions())
}

fn arm32_dproc_isa() -> ISA {
    arm32_isa_with_instructions(arm32_dproc_instructions())
}

fn arm32_dproc_data_tfr_isa() -> ISA {
    let mut instructions = arm32_dproc_instructions();
    instructions.extend([
        arm32::load_ops(),
        arm32::store_ops(),
        arm32::branch_ops_data_tfr(),
    ]);
    arm32_isa_with_instructions(instructions)
}

fn arm32_dproc_instructions() -> Vec<isa_minimization::isa_specification::Instruction> {
    vec![
        arm32::arithmetic_s0_reg_op2(),
        arm32::arithmetic_s0_imm_op2(),
        arm32::logical_s0_reg_op2(),
        arm32::logical_s0_imm_op2(),
        arm32::move_s0_reg_op2(),
        arm32::move_s0_imm_op2(),
        arm32::dproc_s1_reg_op2(),
        arm32::dproc_s1_imm_op2(),
        arm32::branch_ops_dproc(),
    ]
}

fn arm32_isa_with_instructions(
    instructions: Vec<isa_minimization::isa_specification::Instruction>,
) -> ISA {
    ISA {
        registers: arm32::registers(),
        instructions,
        sp: StackPointer {
            register: arm32::gpr(12),
            stack_size: 32,
            direction: StackDirection::Downwards,
        },
        pc: arm32::gpr(15),
    }
}

fn decode_one(bits: &str, isa: &ISA) -> DecodedInstruction {
    let decoded = DecodedInstruction::decode_program_str(bits, isa).expect("ARM32 decode failed");
    assert_eq!(decoded.len(), 1);
    decoded.into_iter().next().unwrap()
}

fn bits(parts: &[&str]) -> String {
    let instruction = parts.concat();
    assert_eq!(instruction.len(), 32);
    instruction
}

fn assert_decode_rejects(bits: &str, isa: &ISA) {
    let result = panic::catch_unwind(|| DecodedInstruction::decode_program_str(bits, isa));
    assert!(
        result.is_err() || result.unwrap().is_err(),
        "expected ARM32 decode to reject {bits}"
    );
}

fn assert_decodes_as(bits: &str, isa: &ISA, expected_instruction: &str) {
    let decoded = decode_one(bits, isa);
    assert_eq!(decoded.name, expected_instruction);
}

fn assert_matches_exactly_once(bits: &str, isa: &ISA) {
    let pattern = BitPattern::parse(bits);
    let matches = isa
        .instructions
        .iter()
        .filter_map(|instruction| instruction.find_match(&pattern.bits))
        .count();
    assert_eq!(matches, 1, "expected exactly one match for {bits}");
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
                    len: value.len(),
                },
                MergeMode::VariableBits => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: Some(value.clone()),
                    len: value.len(),
                },
            };

            match field_values.entry(name.clone()).or_insert(default_value) {
                FieldUses::Uses { patterns, .. } => {
                    patterns.insert(value.clone());
                }
                FieldUses::VariableBits { pattern, len, .. } => {
                    assert_eq!(*len, value.len());
                    let pattern = pattern
                        .as_mut()
                        .expect("observed VariableBits field should be populated");
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
        .into_iter()
        .map(|(name, field_uses)| (name, field_uses.merge()))
        .collect()
}

fn all_patterns(width: usize) -> Vec<BitPattern> {
    assert!(width <= 16, "test helper only expects small Uses fields");
    (0..(1usize << width))
        .map(|value| {
            BitPattern::new(
                (0..width)
                    .rev()
                    .map(|bit| {
                        if value & (1usize << bit) == 0 {
                            Bit::Low
                        } else {
                            Bit::High
                        }
                    })
                    .collect(),
            )
        })
        .collect()
}

fn open_field_uses(isa: &ISA) -> HashMap<FieldName, FieldUses> {
    let mut field_uses = HashMap::new();

    for instruction in &isa.instructions {
        for form in &instruction.forms {
            for field in &form.fields {
                let Some(name) = &field.name else {
                    continue;
                };

                field_uses
                    .entry(name.clone())
                    .or_insert_with(|| match field.merge_mode {
                        MergeMode::Uses => FieldUses::Uses {
                            name: name.clone(),
                            patterns: all_patterns(field.pattern.len()).into_iter().collect(),
                            len: field.pattern.len(),
                        },
                        MergeMode::VariableBits => FieldUses::VariableBits {
                            name: name.clone(),
                            pattern: Some(BitPattern::variable(field.pattern.len())),
                            len: field.pattern.len(),
                        },
                    });
            }
        }
    }

    merge_field_uses(&mut field_uses);
    field_uses
}

fn merge_field_uses(field_uses: &mut HashMap<FieldName, FieldUses>) {
    for uses in field_uses.values_mut() {
        *uses = uses.merge();
    }
}

fn restrict_variable_bits(
    field_uses: &mut HashMap<FieldName, FieldUses>,
    name: &str,
    pattern: &str,
) {
    field_uses.insert(
        name.to_string(),
        FieldUses::VariableBits {
            name: name.to_string(),
            pattern: Some(BitPattern::parse(pattern)),
            len: pattern.len(),
        },
    );
    merge_field_uses(field_uses);
}

fn restrict_uses(field_uses: &mut HashMap<FieldName, FieldUses>, name: &str, patterns: &[&str]) {
    let len = patterns
        .first()
        .map(|pattern| pattern.len())
        .expect("restrict_uses requires at least one pattern");
    assert!(
        patterns.iter().all(|pattern| pattern.len() == len),
        "restrict_uses patterns must have the same length"
    );
    field_uses.insert(
        name.to_string(),
        FieldUses::Uses {
            name: name.to_string(),
            patterns: patterns
                .iter()
                .map(|pattern| BitPattern::parse(pattern))
                .collect(),
            len,
        },
    );
    merge_field_uses(field_uses);
}

#[test]
fn arm32_generate_candidate_helpers_merge_field_uses() {
    let isa = arm32_dproc_isa();
    let valid_field_uses = open_field_uses(&isa);

    assert_eq!(
        valid_field_uses.get("cond"),
        Some(&FieldUses::Uses {
            name: "cond".to_string(),
            patterns: [BitPattern::parse("xxxx")].into_iter().collect(),
            len: 4,
        })
    );

    let mut restricted = HashMap::new();
    restrict_uses(&mut restricted, "two_bit_field", &["00", "01", "10", "11"]);

    assert_eq!(
        restricted.get("two_bit_field"),
        Some(&FieldUses::Uses {
            name: "two_bit_field".to_string(),
            patterns: [BitPattern::parse("xx")].into_iter().collect(),
            len: 2,
        })
    );
}

fn assert_arm32_generate_candidates_finds_two_instruction_replacement(
    original: DecodedInstruction,
    valid_field_uses: HashMap<FieldName, FieldUses>,
    isa: &ISA,
    live_out_registers: Vec<ArchitecturalRegister>,
    max_iters: u32,
) {
    let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
        original,
        valid_field_uses.clone(),
        isa,
        live_out_registers,
    );

    let timer = Instant::now();

    ctx.generate_candidates(3, max_iters);

    let time_elapsed = timer.elapsed().as_secs_f64();
    println!("============");
    println!("TIME ELAPSED");
    println!("{time_elapsed}");
    println!("============");
    println!("Instructions");

    let replacement = ctx
        .perfect_matches()
        .iter()
        .map(|(_, program)| program)
        .find(|program| program.iter_instructions().count() >= 2)
        .unwrap_or_else(|| {
            panic!(
                "generate_candidates did not find a two-instruction ARM32 replacement in {max_iters} accepted iterations"
            )
        });

    for replacement in ctx.perfect_matches().iter().map(|(_, program)| program) {
        println!("New Solution:");
        for instruction in replacement.iter_instructions() {
            println!("{:?}", instruction.name);
            println!("{:?}", instruction.bits);
            println!("{:?}", instruction.fields);
        }
    }

    assert!(replacement.iter_instructions().count() >= 2);
    assert!(
        replacement
            .iter_instructions()
            .all(|instruction| instruction_valid_under_field_uses(instruction, &valid_field_uses))
    );
}

#[test]
fn arm32_dproc_decode_rejects_nonzero_rn_for_mov_and_mvn() {
    let isa = arm32_dproc_isa();

    // E1A01BA1: MOV r1, r1, LSR #23.
    decode_one("11100001101000000001101110100001", &isa);
    // E1AC1BA1: same encoding except the ignored Rn field is r12, which is invalid.
    assert_decode_rejects("11100001101011000001101110100001", &isa);

    // E1E01001: MVN r1, r1.
    decode_one("11100001111000000001000000000001", &isa);
    // E1EC1001: same encoding except the ignored Rn field is r12, which is invalid.
    assert_decode_rejects("11100001111011000001000000000001", &isa);
}

#[test]
fn arm32_dproc_decode_rejects_nonzero_rd_for_test_and_compare_opcodes() {
    let isa = arm32_dproc_isa();

    for opcode in ["1000", "1001", "1010", "1011"] {
        decode_one(&format!("1110000{opcode}100010000000000000001"), &isa);
        assert_decode_rejects(&format!("1110000{opcode}100010001000000000001"), &isa);
    }
}

#[test]
fn arm32_decode_rejects_reserved_cond_for_all_instruction_families() {
    let isa = arm32_isa();
    let valid_encodings = [
        // MOV r1, #2
        bits(&[
            "1110", "00", "1", "1101", "0", "0000", "0001", "0000", "00000010",
        ]),
        // MUL r0, r1, r2
        bits(&[
            "1110", "000000", "0", "0", "0000", "0000", "0010", "1001", "0001",
        ]),
        // UMULL r1, r0, r3, r2
        bits(&[
            "1110", "00001", "1", "0", "0", "0001", "0000", "0010", "1001", "0011",
        ]),
        // SWP r1, r2, [r0]
        bits(&[
            "1110", "00010", "0", "00", "0000", "0001", "00001001", "0010",
        ]),
        // BX r0
        bits(&["1110", "000100101111111111110001", "0000"]),
        // STRH r1, [r0], +r2
        bits(&[
            "1110", "000", "1", "1", "0", "0", "1", "0000", "0001", "00001", "01", "1", "0010",
        ]),
        // STRH r1, [r0], #0
        bits(&[
            "1110", "000", "1", "1", "1", "0", "1", "0000", "0001", "0000", "1", "01", "1", "0000",
        ]),
        // STR r1, [r0]
        bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "0",
            "0",
            "0",
            "0000",
            "0001",
            "000000000000",
        ]),
        // STMIA r0, {r1}
        bits(&[
            "1110",
            "100",
            "0",
            "1",
            "0",
            "0",
            "0",
            "0000",
            "0000000000000010",
        ]),
        // B +0
        bits(&["1110", "101", "0", "000000000000000000000000"]),
    ];

    for encoding in valid_encodings {
        decode_one(&encoding, &isa);
        assert_decode_rejects(&format!("1111{}", &encoding[4..]), &isa);
    }
}

#[test]
fn arm32_categorized_dproc_decodes_to_expected_buckets() {
    let isa = arm32_isa();

    // ADD r1, r0, #1
    assert_decodes_as(
        &bits(&[
            "1110", "00", "1", "0100", "0", "0000", "0001", "0000", "00000001",
        ]),
        &isa,
        "arithmetic_s0_imm_op2",
    );
    // AND r1, r0, #1
    assert_decodes_as(
        &bits(&[
            "1110", "00", "1", "0000", "0", "0000", "0001", "0000", "00000001",
        ]),
        &isa,
        "logical_s0_imm_op2",
    );
    // MOV r1, #1
    assert_decodes_as(
        &bits(&[
            "1110", "00", "1", "1101", "0", "0000", "0001", "0000", "00000001",
        ]),
        &isa,
        "move_s0_imm_op2",
    );
    // ADDS r1, r0, #1
    assert_decodes_as(
        &bits(&[
            "1110", "00", "1", "0100", "1", "0000", "0001", "0000", "00000001",
        ]),
        &isa,
        "dproc_s1_imm_op2",
    );
    // CMP r0, #1
    assert_decodes_as(
        &bits(&[
            "1110", "00", "1", "1010", "1", "0000", "0000", "0000", "00000001",
        ]),
        &isa,
        "dproc_s1_imm_op2",
    );
}

#[test]
fn arm32_pc_writing_forms_decode_as_branch_ops_when_valid() {
    let isa = arm32_isa();

    // MOV PC, LR
    assert_decodes_as(
        &bits(&[
            "1110", "00", "0", "1101", "0", "0000", "1111", "00000", "00", "0", "1110",
        ]),
        &isa,
        "branch_ops_dproc",
    );
    // MOVS PC, LR: manual-valid PC/CPSR-restoring form.
    assert_decodes_as(
        &bits(&[
            "1110", "00", "0", "1101", "1", "0000", "1111", "00000", "00", "0", "1110",
        ]),
        &isa,
        "branch_ops_dproc",
    );
    // LDR PC, [r0]
    assert_decodes_as(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "0",
            "0",
            "1",
            "0000",
            "1111",
            "000000000000",
        ]),
        &isa,
        "branch_ops_data_tfr",
    );
    // LDMIA r0, {PC}
    assert_decodes_as(
        &bits(&[
            "1110",
            "100",
            "0",
            "1",
            "0",
            "0",
            "1",
            "0000",
            "1000000000000000",
        ]),
        &isa,
        "branch_ops_block_tfr",
    );
}

#[test]
fn arm32_branch_ops_carry_branch_metadata() {
    let isa = arm32_isa();

    let metadata = isa
        .instructions
        .iter()
        .map(|instruction| (instruction.name.as_str(), &instruction.branch_instruction))
        .collect::<HashMap<_, _>>();

    assert!(matches!(
        metadata["branch_ops_b"],
        Some(BranchOffset::PCRelative(_))
    ));
    for name in [
        "branch_ops_bx",
        "branch_ops_dproc",
        "branch_ops_data_tfr",
        "branch_ops_hwtfr",
        "branch_ops_block_tfr",
    ] {
        assert_eq!(metadata[name], &Some(BranchOffset::Register), "{name}");
    }
    assert_eq!(metadata["load_ops"], &None);
    assert_eq!(metadata["store_ops"], &None);

    let decoded_b = decode_one(
        &bits(&["1110", "101", "0", "000000000000000000000000"]),
        &isa,
    );
    assert!(matches!(
        decoded_b.branch_instruction,
        Some(BranchOffset::PCRelative(_))
    ));

    let decoded_bx = decode_one(&bits(&["1110", "000100101111111111110001", "0000"]), &isa);
    assert_eq!(decoded_bx.branch_instruction, Some(BranchOffset::Register));
}

#[test]
fn arm32_pc_values_map_to_instruction_addresses_and_prefetched_reads() {
    let isa = arm32_isa();
    let program = DecodedInstruction::decode_program_str(
        &[
            "11100011101000000000000000000001",
            "11100010100000000001000000000010",
            "11101010000000000000000000000001",
        ]
        .join("\n"),
        &isa,
    )
    .expect("ARM32 program should decode");

    assert_eq!(program[0].mem_addr, 0);
    assert_eq!(program[1].mem_addr, 4);
    assert_eq!(program[2].mem_addr, 8);

    let Some(BranchOffset::PCRelative(offset)) = &program[2].branch_instruction else {
        panic!("expected decoded B to carry PC-relative branch metadata");
    };
    let Expr::Const { value, .. } = offset.clone().collapse(&program[2]) else {
        panic!("ARM32 branch offset should collapse to a constant");
    };
    assert_eq!(program[2].mem_addr as u128 + value, 20);
}

#[test]
fn arm32_pc_looking_invalid_or_nonbranch_forms_stay_out_of_branch_ops() {
    let isa = arm32_isa();

    // CMP does not write Rd; encodings with nonzero Rd remain invalid.
    assert_decode_rejects(
        &bits(&[
            "1110", "00", "1", "1010", "1", "0000", "1111", "0000", "00000001",
        ]),
        &isa,
    );
    // STR PC, [r0] stores PC; it does not branch.
    assert_decodes_as(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "0",
            "0",
            "0",
            "0000",
            "1111",
            "000000000000",
        ]),
        &isa,
        "store_ops",
    );
    // STMIA r0, {PC} stores PC; it does not branch.
    assert_decodes_as(
        &bits(&[
            "1110",
            "100",
            "0",
            "1",
            "0",
            "0",
            "0",
            "0000",
            "1000000000000000",
        ]),
        &isa,
        "block_store_ops",
    );
}

#[test]
fn arm32_rejects_manual_invalid_r15_operands() {
    let isa = arm32_isa();

    // LDR r1, [r0, PC]
    assert_decode_rejects(
        &bits(&[
            "1110", "01", "1", "1", "1", "0", "0", "1", "0000", "0001", "00000", "00", "0", "1111",
        ]),
        &isa,
    );
    // LDR r1, [PC], #0 performs writeback to PC.
    assert_decode_rejects(
        &bits(&[
            "1110",
            "01",
            "0",
            "0",
            "1",
            "0",
            "0",
            "1",
            "1111",
            "0001",
            "000000000000",
        ]),
        &isa,
    );
    // SWP with Rd = PC.
    assert_decode_rejects(
        &bits(&[
            "1110", "00010", "0", "00", "0000", "1111", "00001001", "0001",
        ]),
        &isa,
    );
    // SWP with Rn = PC.
    assert_decode_rejects(
        &bits(&[
            "1110", "00010", "0", "00", "1111", "0001", "00001001", "0000",
        ]),
        &isa,
    );
    // SWP with Rm = PC.
    assert_decode_rejects(
        &bits(&[
            "1110", "00010", "0", "00", "0000", "0001", "00001001", "1111",
        ]),
        &isa,
    );
}

#[test]
fn arm32_categorized_representatives_match_exactly_once() {
    let isa = arm32_isa();
    let representatives = [
        // LDR r1, [r0]
        bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "0",
            "0",
            "1",
            "0000",
            "0001",
            "000000000000",
        ]),
        // STR r1, [r0]
        bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "0",
            "0",
            "0",
            "0000",
            "0001",
            "000000000000",
        ]),
        // ADD r1, r0, #1
        bits(&[
            "1110", "00", "1", "0100", "0", "0000", "0001", "0000", "00000001",
        ]),
        // ADDS r1, r0, #1
        bits(&[
            "1110", "00", "1", "0100", "1", "0000", "0001", "0000", "00000001",
        ]),
        // MUL r0, r1, r2
        bits(&[
            "1110", "000000", "0", "0", "0000", "0000", "0010", "1001", "0001",
        ]),
        // B +0
        bits(&["1110", "101", "0", "000000000000000000000000"]),
    ];

    for encoding in representatives {
        assert_matches_exactly_once(&encoding, &isa);
    }
}

#[test]
#[ignore = "stochastic ARM32 MCMC search; run explicitly to test word-store synthesis from byte stores"]
fn generate_candidates_finds_arm32_word_store_replacement_using_byte_stores() {
    let isa = arm32_dproc_data_tfr_isa();

    // STR r1, [r0]
    let word_store = decode_one(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "0",
            "0",
            "0",
            "0000",
            "0001",
            "000000000000",
        ]),
        &isa,
    );

    // STRB r1, [r0, #0]
    let store_byte_0 = decode_one(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "1",
            "0",
            "0",
            "0000",
            "0001",
            "000000000000",
        ]),
        &isa,
    );
    // MOV r2, r1, LSR #8
    let shift_byte_1 = decode_one(
        &bits(&[
            "1110", "00", "0", "1101", "0", "0000", "0010", "01000", "01", "0", "0001",
        ]),
        &isa,
    );
    // STRB r2, [r0, #1]
    let store_byte_1 = decode_one(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "1",
            "0",
            "0",
            "0000",
            "0010",
            "000000000001",
        ]),
        &isa,
    );
    // MOV r2, r1, LSR #16
    let shift_byte_2 = decode_one(
        &bits(&[
            "1110", "00", "0", "1101", "0", "0000", "0010", "10000", "01", "0", "0001",
        ]),
        &isa,
    );
    // STRB r2, [r0, #2]
    let store_byte_2 = decode_one(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "1",
            "0",
            "0",
            "0000",
            "0010",
            "000000000010",
        ]),
        &isa,
    );
    // MOV r2, r1, LSR #24
    let shift_byte_3 = decode_one(
        &bits(&[
            "1110", "00", "0", "1101", "0", "0000", "0010", "11000", "01", "0", "0001",
        ]),
        &isa,
    );
    // STRB r2, [r0, #3]
    let store_byte_3 = decode_one(
        &bits(&[
            "1110",
            "01",
            "0",
            "1",
            "1",
            "1",
            "0",
            "0",
            "0000",
            "0010",
            "000000000011",
        ]),
        &isa,
    );

    let valid_field_uses = field_uses_from(&[
        store_byte_0,
        shift_byte_1,
        store_byte_1,
        shift_byte_2,
        store_byte_2,
        shift_byte_3,
        store_byte_3,
    ]);

    assert!(
        !instruction_valid_under_field_uses(&word_store, &valid_field_uses),
        "word STR should be prohibited by the byte-store-only field uses"
    );

    let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
        word_store,
        valid_field_uses.clone(),
        &isa,
        vec![],
    );

    let timer = Instant::now();
    ctx.generate_candidates(1, 2_000_000);
    let time_elapsed = timer.elapsed().as_secs_f64();

    let replacement = ctx
        .perfect_matches()
        .iter()
        .map(|(_, program)| program)
        .find(|program| program.iter_instructions().count() >= 4)
        .unwrap_or_else(|| {
            panic!(
                "generate_candidates did not find a byte-store replacement for word STR in 2,000,000 iterations; elapsed {time_elapsed}s"
            )
        });

    println!("============");
    println!("TIME ELAPSED");
    println!("{time_elapsed}");
    println!("============");
    println!("Instructions");
    for instruction in replacement.iter_instructions() {
        println!("{:?}", instruction.name);
        println!("{:?}", instruction.bits);
        println!("{:?}", instruction.fields);
    }

    assert!(
        replacement
            .iter_instructions()
            .all(|instruction| instruction_valid_under_field_uses(instruction, &valid_field_uses)),
        "replacement should use only the allowed byte stores and scratch-register shifts"
    );
}

#[test]
#[ignore = "stochastic ARM32 MCMC harness; run explicitly when tuning generate_candidates"]
fn generate_candidates_finds_arm32_mov_immediate_replacement_with_restricted_subset() {
    let isa = arm32_isa();
    let original_mov_two = decode_one("11100011101000000001000000000010", &isa);
    let mov_one = decode_one("11100011101000000001000000000001", &isa);
    let add_one = decode_one("11100010100000010001000000000001", &isa);
    let valid_field_uses = field_uses_from(&[mov_one, add_one]);

    assert_arm32_generate_candidates_finds_two_instruction_replacement(
        original_mov_two,
        valid_field_uses,
        &isa,
        vec![arm32::gpr(1)],
        100_000,
    );
}

#[test]
#[ignore = "stochastic ARM32 search; bans MOV #2 via a targeted imm8 restriction"]
fn generate_candidates_finds_arm32_mov_immediate_replacement_with_open_subset() {
    let isa = arm32_dproc_isa();
    let original_mov_two = decode_one("11100011101000000001000000000010", &isa);
    let mut valid_field_uses = open_field_uses(&isa);

    // Keep the data-processing forms broadly open, while keeping the comparison focused on
    // unconditional candidates that write R1 without flags.
    restrict_uses(&mut valid_field_uses, "cond", &["1110"]);
    restrict_uses(
        &mut valid_field_uses,
        "data_proc_opcode",
        &[
            "0000", "0001", "0010", "0011", "0100", "0101", "0110", "0111", "1100", "1101", "1110",
            "1111",
        ],
    );
    restrict_uses(&mut valid_field_uses, "rd_addr", &["0001"]);
    restrict_variable_bits(&mut valid_field_uses, "set_flags", "0");

    // Remove the one-instruction MOV #2 solution.
    // MOV #1 followed by ADD #1 remains legal.
    restrict_variable_bits(&mut valid_field_uses, "imm8", "00000001");

    assert_arm32_generate_candidates_finds_two_instruction_replacement(
        original_mov_two,
        valid_field_uses,
        &isa,
        vec![arm32::gpr(1)],
        u32::MAX,
    );
}

#[test]
#[ignore = "stochastic ARM32 search; bans one bit of a nontrivial immediate"]
fn generate_candidates_finds_arm32_mov_complex_immediate_with_one_illegal_imm8_bit() {
    let isa = arm32_dproc_isa();
    // MOV r1, #0xa5
    let original_mov_a5 = decode_one(
        &bits(&[
            "1110", "00", "1", "1101", "0", "0000", "0001", "0000", "10100101",
        ]),
        &isa,
    );
    let mut valid_field_uses = open_field_uses(&isa);

    // Keep the data-processing forms broadly open, while keeping the comparison focused on
    // unconditional candidates that write R1 without flags.
    // restrict_uses(&mut valid_field_uses, "cond", &["1110"]);
    // restrict_uses(
    //     &mut valid_field_uses,
    //     "data_proc_opcode",
    //     &[
    //         "0000", "0001", "0010", "0011", "0100", "0101", "0110", "0111", "1100", "1101", "1110",
    //         "1111",
    //     ],
    // );
    // restrict_uses(&mut valid_field_uses, "rd_addr", &["0001"]);
    // restrict_variable_bits(&mut valid_field_uses, "set_flags", "0");

    // The original imm8 is 10100101. Forcing bit 6 to 1 bans that exact immediate
    // while leaving nearby decompositions legal.
    restrict_variable_bits(&mut valid_field_uses, "imm8", "x1xxxxxx");

    assert_arm32_generate_candidates_finds_two_instruction_replacement(
        original_mov_a5,
        valid_field_uses,
        &isa,
        vec![
            arm32::gpr(1),
            arm32::gpr(2),
            arm32::gpr(3),
            arm32::gpr(4),
            arm32::gpr(5),
            arm32::gpr(6),
        ],
        u32::MAX,
    );
}

#[test]
#[ignore = "stochastic ARM32 search; bans subtract-family opcodes and requires a subtraction-equivalent replacement"]
fn generate_candidates_replicates_arm32_sub_without_subtraction() {
    let isa = arm32_dproc_isa();
    // SUB r1, r0, #1
    let original_sub_r1_r0_one = decode_one(
        &bits(&[
            "1110", "00", "1", "0010", "0", "0000", "0001", "0000", "00000001",
        ]),
        &isa,
    );
    let mut valid_field_uses = open_field_uses(&isa);

    // Leave the data-processing subset open, except for removing subtract-family opcodes.
    restrict_uses(
        &mut valid_field_uses,
        "data_proc_opcode",
        &[
            "0000", "0001", "0100", "0101", "1000", "1001", "1011", "1100", "1101", "1110", "1111",
        ],
    );

    restrict_uses(
        &mut valid_field_uses,
        "rd_addr",
        &["0000", "0001", "0010", "0011"],
    );

    assert_arm32_generate_candidates_finds_two_instruction_replacement(
        original_sub_r1_r0_one,
        valid_field_uses,
        &isa,
        vec![arm32::gpr(1)],
        u32::MAX,
    );
}

#[test]
#[ignore = "stochastic ARM32 search; bans subtract-family opcodes and requires a register-subtraction replacement"]
fn generate_candidates_replicates_arm32_register_sub_without_subtraction() {
    let isa = arm32_dproc_isa();
    // SUB r1, r0, r2
    let original_sub_r1_r0_r2 = decode_one(
        &bits(&[
            "1110", "00", "0", "0010", "0", "0000", "0001", "00000", "00", "0", "0010",
        ]),
        &isa,
    );
    let mut valid_field_uses = open_field_uses(&isa);

    // Leave the data-processing subset open, except for removing subtract-family opcodes.
    restrict_uses(
        &mut valid_field_uses,
        "data_proc_opcode",
        &[
            "0000", "0001", "0100", "0101", "1000", "1001", "1011", "1100", "1101", "1110", "1111",
        ],
    );

    assert_arm32_generate_candidates_finds_two_instruction_replacement(
        original_sub_r1_r0_r2,
        valid_field_uses,
        &isa,
        vec![arm32::gpr(1)],
        u32::MAX,
    );
}
