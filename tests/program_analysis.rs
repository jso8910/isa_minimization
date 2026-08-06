#[allow(dead_code, unused_imports)]
#[path = "../examples/arm32.rs"]
mod arm32;

use isa_minimization::{
    isa_specification::{
        ArchitecturalRegister, DecodedInstruction, ISA, StackDirection, StackPointer,
    },
    program_analysis::ProgramAnalysis,
};
use std::collections::HashSet;

fn arm32_isa() -> ISA {
    ISA {
        registers: arm32::registers(),
        instructions: arm32::instructions(),
        sp: StackPointer {
            register: arm32::gpr(12),
            stack_size: 32,
            direction: StackDirection::Downwards,
        },
        pc: arm32::gpr(15),
        pc_to_instruction_index: arm32::pc_to_instruction_index,
        instruction_index_to_pc: arm32::instruction_index_to_pc,
    }
}

fn decode_program(words: &[&str], isa: &ISA) -> Vec<DecodedInstruction> {
    DecodedInstruction::decode_program_str(&words.join("\n"), isa)
        .expect("ARM32 test program should decode")
}

fn block_starts(analysis: &ProgramAnalysis<'_>) -> Vec<usize> {
    analysis
        .program
        .iter()
        .map(|block| block.start_instruction_idx)
        .collect()
}

fn block_successors(analysis: &ProgramAnalysis<'_>) -> Vec<Vec<usize>> {
    analysis
        .program
        .iter()
        .map(|block| block.next_blocks.clone())
        .collect()
}

fn arm_register_set(registers: &[u8]) -> HashSet<ArchitecturalRegister> {
    registers
        .iter()
        .map(|register| arm32::gpr(*register))
        .collect()
}

fn block_live_ins(analysis: &ProgramAnalysis<'_>) -> Vec<HashSet<ArchitecturalRegister>> {
    analysis
        .program
        .iter()
        .map(|block| block.live_in_regs.clone())
        .collect()
}

fn block_live_outs(analysis: &ProgramAnalysis<'_>) -> Vec<HashSet<ArchitecturalRegister>> {
    analysis
        .program
        .iter()
        .map(|block| block.live_out_regs.clone())
        .collect()
}

#[test]
fn arm32_program_analysis_splits_real_program_into_basic_blocks() {
    let isa = arm32_isa();

    //     mov r0, #1
    //     add r1, r0, #2
    //     b target
    // fallthrough:
    //     sub r0, r0, #1
    //     add r1, r1, #3
    // target:
    //     mov r2, r1
    // finished:
    //     b finished
    let program = decode_program(
        &[
            "11100011101000000000000000000001",
            "11100010100000000001000000000010",
            "11101010000000000000000000000001",
            "11100010010000000000000000000001",
            "11100010100000010001000000000011",
            "11100001101000000010000000000001",
            "11101010111111111111111111111110",
        ],
        &isa,
    );

    let analysis = ProgramAnalysis::from_program(program, &isa);

    assert_eq!(block_starts(&analysis), vec![0, 3, 5, 6]);
    assert_eq!(
        block_successors(&analysis),
        vec![vec![1, 2], vec![2], vec![3], vec![3]]
    );
}

#[test]
fn arm32_compute_liveliness_handles_straight_line_program() {
    let isa = arm32_isa();

    //     add r1, r0, #2
    //     add r2, r1, #3
    let program = decode_program(
        &[
            "11100010100000000001000000000010",
            "11100010100000010010000000000011",
        ],
        &isa,
    );

    let mut analysis = ProgramAnalysis::from_program(program, &isa);
    analysis.compute_liveliness();

    assert_eq!(block_starts(&analysis), vec![0]);
    assert_eq!(block_live_ins(&analysis), vec![arm_register_set(&[0])]);
    assert_eq!(block_live_outs(&analysis), vec![HashSet::new()]);
}

#[test]
fn arm32_compute_liveliness_handles_if_else_branching_program() {
    let isa = arm32_isa();

    //     cmp r0, #0
    //     beq else_block
    // then_block:
    //     mov r1, #1
    //     b join
    // else_block:
    //     mov r1, #2
    // join:
    //     add r2, r1, #3
    let program = decode_program(
        &[
            "11100011010100000000000000000000",
            "00001010000000000000000000000001",
            "11100011101000000001000000000001",
            "11101010000000000000000000000000",
            "11100011101000000001000000000010",
            "11100010100000010010000000000011",
        ],
        &isa,
    );

    let mut analysis = ProgramAnalysis::from_program(program, &isa);
    analysis.compute_liveliness();

    assert_eq!(block_starts(&analysis), vec![0, 2, 4, 5]);
    assert_eq!(
        block_successors(&analysis),
        vec![vec![1, 2], vec![2, 3], vec![3], vec![]]
    );
    assert_eq!(
        block_live_ins(&analysis),
        vec![
            arm_register_set(&[0, 15]),
            arm_register_set(&[15]),
            HashSet::new(),
            arm_register_set(&[1])
        ]
    );
    assert_eq!(
        block_live_outs(&analysis),
        vec![
            arm_register_set(&[15]),
            arm_register_set(&[1]),
            arm_register_set(&[1]),
            HashSet::new()
        ]
    );
}

#[test]
fn arm32_compute_liveliness_handles_loop_program() {
    let isa = arm32_isa();

    //     mov r0, #0
    // loop:
    //     add r0, r0, #1
    //     cmp r0, r1
    //     bne loop
    // done:
    //     add r2, r0, #3
    let program = decode_program(
        &[
            "11100011101000000000000000000000",
            "11100010100000000000000000000001",
            "11100001010100000000000000000001",
            "00011010111111111111111111111100",
            "11100010100000000010000000000011",
        ],
        &isa,
    );

    let mut analysis = ProgramAnalysis::from_program(program, &isa);
    analysis.compute_liveliness();

    assert_eq!(block_starts(&analysis), vec![0, 1, 4]);
    assert_eq!(
        block_successors(&analysis),
        vec![vec![1], vec![2, 1], vec![]]
    );
    assert_eq!(
        block_live_ins(&analysis),
        vec![
            arm_register_set(&[1, 15]),
            arm_register_set(&[0, 1, 15]),
            arm_register_set(&[0])
        ]
    );
    assert_eq!(
        block_live_outs(&analysis),
        vec![
            arm_register_set(&[0, 1, 15]),
            arm_register_set(&[0, 1, 15]),
            HashSet::new()
        ]
    );
}
