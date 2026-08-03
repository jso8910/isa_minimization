use std::collections::{HashMap, HashSet};

use itertools::Itertools;

use crate::{
    instruction_semantics::{Effect, Expr, OperandRef, RegisterRef},
    isa_specification::{ArchitecturalRegister, BranchOffset, DecodedInstruction, ISA},
    semantic_matching::{bit_mask, instruction_to_lowered_effects},
};

pub struct ProgramAnalysis<'a> {
    /// All instructions in the program
    pub program: Vec<BasicBlock>,
    isa: &'a ISA,
}

pub struct BasicBlock {
    /// The instruction index where this BasicBlock starts in the original program.
    pub start_instruction_idx: usize,
    /// HashSet of all registers which are read before being overwritten (ie their pre-block
    /// contents are used by this basic block in some calculation)
    pub live_in_regs: HashSet<ArchitecturalRegister>,
    /// HashSet of all registers which have their contents changed during the course of this basic block
    pub consumed_registers: HashSet<ArchitecturalRegister>,
    /// HashSet of all live-out registers (ie registers which may or may not be read after the
    /// basic block completes). Calculated assuming any branch could be taken. If live_out_regs is
    /// None, that means it hasn't yet been calculated
    pub live_out_regs: Option<HashSet<ArchitecturalRegister>>,
    /// A list of pointers to all other basic blocks which this basic block can lead to (excluding itself).
    /// Pointers are defined by BasicBlock indices which index ProgramAnalysis::program.
    pub next_blocks: Vec<usize>,
    /// The instructions in the basic block. This should include the branch statement which ends the
    /// basic block (if applicable).
    instructions: Vec<DecodedInstruction>,
}

// is there any way to do all this without using the semantics? i would really rather that not be
// necessary because that means that semantics have to be defined in TWO locations
// i really dont like the added complexity greenthumb has added
// maybe i can add a special "BranchDestination" field on InstructionForm? or smth
//

// and how do you handle branching to a register? should I just make certain assumptions in the ISA
// (ie calling conventions) that when you're branching to a non-constant location, certain registers
// are live-out, certain registers are live-in?
//      if branching to a register, assume all registers are live-out. i think that's the way

// NOTE: I think, for now, what I'm going to do is this: assume any instructions which modify the PC
// fall into two categories: branch by an immediate offset, and branch to register
// importantly, my current optimization method sort of assumes this. I can't do much optimization if
// I need to support *every* way the PC could potentially be modified.

// when rewriting the program, the relative branches need to change. I think the best way to solve
// this is to simply take the original assembly and put the new assembly in, then reassemble the program.

impl<'a> ProgramAnalysis<'a> {
    pub fn from_program(program: Vec<DecodedInstruction>, isa: &'a ISA) -> Self {
        // Indices of every instruction which starts a new basic block.
        // We need to also put a basic block boundary at the end of the program, so when we pair up
        // the basic block boundaries, the last basic block goes to the end of the program.
        let mut basic_block_boundaries = HashSet::from([0, program.len()]);

        // First, iterate through the branch instructions and add all known basic block boundaries.
        // There are some (unavoidable, to the best of my knowledge) limitations to this approach.
        // If there is a branch to a location defined by a word in memory (eg LDR pc, r10), then it
        // isn't possible to determine that there is a basic block gap there. However, I make the
        // assumption that any such locations will have a branch instruction immediately before that
        // memory address.
        // I don't know whether this is a universally valid assumption in normal compiler-generated
        // assembly, but it is necessary.
        for (idx, instruction) in program.iter().enumerate() {
            let Some(branch_type) = &instruction.branch_instruction else {
                continue;
            };
            let current_pc: u128 = (isa.instruction_index_to_pc)(
                idx.try_into()
                    .expect("Could not convert usize index of program to u32"),
                &program,
            );
            match branch_type {
                BranchOffset::PCRelative(offset_val) => {
                    let collapsed_offset = offset_val.clone().collapse(&instruction);

                    // Offset is a signed value. We will assume the current_pc is also the same
                    // width as the offset.
                    let Expr::Const { value, width } = collapsed_offset else {
                        panic!("PCRelative offset must evaluate to a Const!")
                    };

                    let new_pc = ((current_pc & bit_mask(width)) + (value & bit_mask(width)))
                        & bit_mask(width);
                    let new_program_idx = (isa.pc_to_instruction_index)(new_pc, &program);

                    // The next index will be the start of a basic block unless this branch is
                    // already at the end of the program.
                    if idx + 1 != program.len() {
                        basic_block_boundaries.insert(idx + 1);
                    }

                    // The branch target is also the start of a basic block
                    basic_block_boundaries.insert(
                        new_program_idx
                            .try_into()
                            .expect("Could not convert u32 to usize"),
                    );
                }
                BranchOffset::Register => {
                    // The next index will be the start of a basic block unless this branch is
                    // already at the end of the program.
                    if idx + 1 != program.len() {
                        basic_block_boundaries.insert(idx + 1);
                    }
                }
            }
        }
        // let mut current_basic_block_instructions = vec![];
        // let mut current_live_in_registers = HashSet::new();
        // let mut current_consumed_registers = HashSet::new();
        // let mut next_blocks = HashSet::new();

        let mut basic_blocks = vec![];

        // Get a list of all starts to a basic block in order
        let mut basic_block_starts = basic_block_boundaries.into_iter().collect_vec();
        basic_block_starts.sort();

        for (start_idx, end_idx) in basic_block_starts.windows(2).map(|w| (w[0], w[1])) {
            let mut instructions = vec![];
            // We want the program counter to always be live-in
            let mut live_in_registers = HashSet::from([isa.pc]);
            let mut consumed_registers = HashSet::new();

            // We know that the next instruction (at end_idx) is one potential next block if this
            // block isn't at the very end of the program
            let mut next_blocks = if end_idx == program.len() {
                vec![]
            } else {
                vec![end_idx]
            };
            let mut live_out_regs = None;

            for (idx, instruction) in program[start_idx..end_idx].iter().enumerate() {
                // We want to normalize the index to the start of the program
                let idx = idx + start_idx;
                if let Some(branch_type) = &instruction.branch_instruction {
                    // This idx should be at the END of the basic block
                    assert_eq!(idx + 1, end_idx);
                    match branch_type {
                        BranchOffset::PCRelative(offset_val) => {
                            let collapsed_offset = offset_val.clone().collapse(&instruction);

                            // Offset is a signed value. We will assume the current_pc is also the same
                            // width as the offset.
                            let Expr::Const { value, width } = collapsed_offset else {
                                panic!("PCRelative offset must evaluate to a Const!")
                            };

                            let current_pc: u128 = (isa.instruction_index_to_pc)(
                                idx.try_into()
                                    .expect("Could not convert usize index of program to u32"),
                                &program,
                            );

                            let new_pc = ((current_pc & bit_mask(width))
                                + (value & bit_mask(width)))
                                & bit_mask(width);
                            let new_program_idx = (isa.pc_to_instruction_index)(new_pc, &program)
                                .try_into()
                                .expect("Could not convert u32 to usize");

                            // We don't want to include loops in the potential next blocks for
                            // live-out analysis.
                            if new_program_idx != start_idx {
                                next_blocks.push(new_program_idx);
                            }
                        }
                        BranchOffset::Register => {
                            // Assume statically that all registers are live-out when a branch is to
                            // an unknown location. This will help to make sure calling conventions
                            // are respected, as well as preventing these branches from causing issues.
                            live_out_regs = Some(isa.registers.iter().cloned().collect());
                        }
                    }
                }
                instructions.push(instruction.clone());

                let effects = instruction_to_lowered_effects(&instruction, isa, &[]);
                let reads = instruction_register_reads(&effects);
                let writes = instruction_register_writes(&effects);

                // Any register which has been read but not consumed yet is one which this basic
                // block needs as a live-in register. We are assuming reads happen before writes.
                let new_live_in_regs = reads.difference(&consumed_registers);
                live_in_registers.extend(new_live_in_regs);

                // Now, we also want to add the registers which have been consumed
                consumed_registers.extend(writes);
            }

            basic_blocks.push(BasicBlock {
                start_instruction_idx: start_idx,
                live_in_regs: live_in_registers,
                consumed_registers,
                live_out_regs,
                // This is currently incorrect and invalid. The loop afterwards to convert from the
                // current "index of program instruction" to "index within BasicBlocks vector" is necessary!
                next_blocks: next_blocks,
                instructions,
            })
        }

        // Converts indices relative to instruction vector to indices relative to basic blocks
        // vector
        let block_index_by_start: HashMap<usize, usize> = basic_blocks
            .iter()
            .enumerate()
            .map(|(i, bb)| (bb.start_instruction_idx, i))
            .collect();
        for block in basic_blocks.iter_mut() {
            let indices = &block.next_blocks;

            let ptrs = indices
                .iter()
                .map(|i| {
                    *block_index_by_start
                        .get(i)
                        .expect("branch target did not match any basic block start")
                })
                .collect();

            block.next_blocks = ptrs;
        }

        Self {
            program: basic_blocks,
            isa,
        }
    }
}

/// Registers which are read by an instruction. Assumed to happen *before* writes.
fn instruction_register_reads(effects: &[Effect]) -> HashSet<ArchitecturalRegister> {
    let mut reads = HashSet::new();
    for effect in effects {
        match effect {
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                collect_expr_register_reads(guard, &mut reads);
                collect_expr_register_reads(register, &mut reads);
                collect_expr_register_reads(value, &mut reads);
            }
            Effect::WriteMemory {
                guard,
                address,
                value,
                ..
            } => {
                collect_expr_register_reads(guard, &mut reads);
                collect_expr_register_reads(address, &mut reads);
                collect_expr_register_reads(value, &mut reads);
            }
        }
    }
    reads
}

/// Registers which are written by an instruction.
fn instruction_register_writes(effects: &[Effect]) -> HashSet<ArchitecturalRegister> {
    effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::WriteRegister {
                register, value, ..
            } => register_expr_to_architectural_register(
                register,
                value
                    .expr_width()
                    .expect("Register write value should have an established width"),
            ),
            Effect::WriteMemory { .. } => None,
        })
        .collect()
}

fn collect_expr_register_reads(expr: &Expr, reads: &mut HashSet<ArchitecturalRegister>) {
    if let Expr::ReadRegister { register, width } = expr {
        collect_expr_register_reads(register, reads);
        if let Some(register) = register_expr_to_architectural_register(register, *width) {
            reads.insert(register);
        }
        return;
    }

    expr.visit_children(|child| collect_expr_register_reads(child, reads));
}

fn register_expr_to_architectural_register(
    expr: &Expr,
    data_width: u16,
) -> Option<ArchitecturalRegister> {
    let Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
        register,
        identifier_width,
    })) = expr
    else {
        return None;
    };

    Some(ArchitecturalRegister {
        identifier: register.0,
        identifier_width: (*identifier_width)
            .try_into()
            .expect("Register identifier width should fit in u8"),
        width: data_width
            .try_into()
            .expect("Register data width should fit in u8"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instruction_semantics::constant,
        isa_specification::{
            Instruction, InstructionField, InstructionForm, StackDirection, StackPointer,
            linear_instruction_index_to_pc, linear_pc_to_instruction_index,
        },
    };

    fn test_register(identifier: u8) -> ArchitecturalRegister {
        ArchitecturalRegister {
            identifier,
            identifier_width: 4,
            width: 32,
        }
    }

    fn test_isa() -> ISA {
        ISA {
            registers: vec![test_register(0), test_register(1)],
            instructions: vec![
                Instruction::new("nop", 2)
                    .form(InstructionForm::new("base").fields([InstructionField::constant("00")])),
                Instruction::new("branch_plus_two", 2)
                    .branch_instruction(BranchOffset::PCRelative(constant(2, 8)))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("10")])),
            ],
            sp: StackPointer {
                register: test_register(0),
                stack_size: 32,
                direction: StackDirection::Downwards,
            },
            pc: test_register(1),
            pc_to_instruction_index: linear_pc_to_instruction_index,
            instruction_index_to_pc: linear_instruction_index_to_pc,
        }
    }

    fn decode_program(words: &[&str], isa: &ISA) -> Vec<DecodedInstruction> {
        DecodedInstruction::decode_program_str(&words.join("\n"), isa)
            .expect("test program should decode")
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
    fn from_program_splits_fallthrough_and_pc_relative_branch_target_blocks() {
        let isa = test_isa();
        let program = decode_program(&["00", "10", "00", "00"], &isa);

        let analysis = ProgramAnalysis::from_program(program, &isa);

        assert_eq!(block_starts(&analysis), vec![0, 2, 3]);
        assert_eq!(
            block_successors(&analysis),
            vec![vec![1, 2], vec![2], vec![]]
        );
    }

    #[test]
    fn from_program_uses_absolute_instruction_index_for_later_branch_targets() {
        let isa = test_isa();
        let program = decode_program(&["10", "00", "00", "10", "00", "00"], &isa);

        let analysis = ProgramAnalysis::from_program(program, &isa);

        assert_eq!(block_starts(&analysis), vec![0, 1, 2, 4, 5]);
        assert_eq!(
            block_successors(&analysis),
            vec![vec![1, 2], vec![2], vec![3, 4], vec![4], vec![]]
        );
    }
}
