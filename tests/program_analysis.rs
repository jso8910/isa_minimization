#[allow(dead_code, unused_imports)]
#[path = "../examples/arm32.rs"]
mod arm32;

use isa_minimization::{
    isa_specification::{DecodedInstruction, ISA, StackDirection, StackPointer},
    program_analysis::ProgramAnalysis,
};

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
        vec![vec![1, 2], vec![2], vec![3], vec![]]
    );
}
