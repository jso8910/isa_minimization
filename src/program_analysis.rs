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
    /// HashSet of all registers which can be read before being overwritten in this program (ie its
    /// contents are still live)
    pub live_in_regs: HashSet<ArchitecturalRegister>,
    /// HashSet of all registers which are read by this basic block. Used as the
    /// live-in input to the Greenthumb superoptimizer (since, although more registers are live-in,
    /// they aren't useful for that block)
    pub read_regs: HashSet<ArchitecturalRegister>,
    /// HashSet of all registers which have their contents changed during the course of this basic block
    pub consumed_registers: HashSet<ArchitecturalRegister>,
    /// HashSet of all live-out registers (ie registers which may or may not be read after the
    /// basic block completes). Calculated assuming any branch could be taken.
    pub live_out_regs: HashSet<ArchitecturalRegister>,
    /// A list of pointers to all other basic blocks which this basic block can lead to.
    /// Pointers are defined by BasicBlock indices which index ProgramAnalysis::program.
    pub next_blocks: Vec<usize>,
    /// The instructions in the basic block. This should include the branch statement which ends the
    /// basic block (if applicable).
    pub instructions: Vec<DecodedInstruction>,
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

        let mut basic_blocks = vec![];

        // Get a list of all starts to a basic block in order
        let mut basic_block_starts = basic_block_boundaries.into_iter().collect_vec();
        basic_block_starts.sort();

        for (start_idx, end_idx) in basic_block_starts.windows(2).map(|w| (w[0], w[1])) {
            let mut instructions = vec![];
            let mut live_in_registers = HashSet::new();
            let mut consumed_registers = HashSet::new();

            // We know that the next instruction (at end_idx) is one potential next block if this
            // block isn't at the very end of the program
            let mut next_blocks = if end_idx == program.len() {
                vec![]
            } else {
                vec![end_idx]
            };
            let mut live_out_regs = HashSet::new();

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

                            next_blocks.push(new_program_idx);
                        }
                        BranchOffset::Register => {
                            // Assume statically that all registers are live-out when a branch is to
                            // an unknown location. This will help to make sure calling conventions
                            // are respected, as well as preventing these branches from causing issues.
                            live_out_regs = isa.registers.iter().cloned().collect();
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
                live_in_regs: live_in_registers.clone(),
                read_regs: live_in_registers,
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

    /// Completes the computing of live-out and live-in registers
    pub fn compute_liveliness(&mut self) {
        // Liveliness analysis is simple. If a register is live-out at a basic block node, and is
        // not overwritten, it is also live-in at that node. If a register is live-in at a successor
        // node, it is live-out at the node.
        // TODO: confirm this is all correct

        let mut changed = true;
        while changed {
            changed = false;
            for idx in 0..self.program.len() {
                let prev_live_in_len = self.program[idx].live_in_regs.len();
                let prev_live_out_len = self.program[idx].live_out_regs.len();

                let mut new_live_out = HashSet::new();
                for succ in self.program[idx].next_blocks.iter() {
                    new_live_out.extend(self.program[*succ].live_in_regs.clone());
                }

                // Now we do a mutable borrow to commit the changes
                let block: &mut BasicBlock = &mut self.program[idx];
                block
                    .live_in_regs
                    .extend(block.live_out_regs.difference(&block.consumed_registers));
                block.live_out_regs.extend(new_live_out);

                if (prev_live_in_len != block.live_in_regs.len())
                    || (prev_live_out_len != block.live_out_regs.len())
                {
                    changed = true;
                }
            }
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
                if guard_is_const_false(guard) {
                    continue;
                }
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
                if guard_is_const_false(guard) {
                    continue;
                }
                collect_expr_register_reads(guard, &mut reads);
                collect_expr_register_reads(address, &mut reads);
                collect_expr_register_reads(value, &mut reads);
            }
        }
    }
    reads
}

/// Registers which are written by an instruction. Only returned if the guard evaluates to 1
/// (always) for the purpose of being more conservative with live-out registers.
fn instruction_register_writes(effects: &[Effect]) -> HashSet<ArchitecturalRegister> {
    effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::WriteRegister {
                guard,
                register,
                value,
            } if guard_is_const_true(guard) => register_expr_to_architectural_register(
                register,
                value
                    .expr_width()
                    .expect("Register write value should have an established width"),
            ),
            Effect::WriteRegister { .. } | Effect::WriteMemory { .. } => None,
        })
        .collect()
}

fn guard_is_const_false(guard: &Expr) -> bool {
    matches!(
        guard,
        Expr::Const { value, width } if (value & bit_mask(*width)) == 0
    )
}

fn guard_is_const_true(guard: &Expr) -> bool {
    matches!(
        guard,
        Expr::Const { value, width } if *width == 1 && (value & bit_mask(*width)) == 1
    )
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
        instruction_semantics::{
            Register, bool_const, constant, fixed_register, read_fixed_register,
        },
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
            registers: vec![
                test_register(0),
                test_register(1),
                test_register(2),
                test_register(3),
            ],
            instructions: vec![
                Instruction::new("nop", 3)
                    .form(InstructionForm::new("base").fields([InstructionField::constant("000")])),
                Instruction::new("r0_from_r1", 3)
                    .effect(Effect::write_register(
                        fixed_register(Register(0), 4),
                        read_fixed_register(Register(1), 4, 32),
                    ))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("001")])),
                Instruction::new("r1_from_r0", 3)
                    .effect(Effect::write_register(
                        fixed_register(Register(1), 4),
                        read_fixed_register(Register(0), 4, 32),
                    ))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("010")])),
                Instruction::new("r2_from_r1", 3)
                    .effect(Effect::write_register(
                        fixed_register(Register(2), 4),
                        read_fixed_register(Register(1), 4, 32),
                    ))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("011")])),
                Instruction::new("branch_plus_two", 3)
                    .branch_instruction(BranchOffset::PCRelative(constant(2, 8)))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("100")])),
                Instruction::new("branch_minus_one", 3)
                    .branch_instruction(BranchOffset::PCRelative(constant(0xff, 8)))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("101")])),
                Instruction::new("r0_from_const", 3)
                    .effect(Effect::write_register(
                        fixed_register(Register(0), 4),
                        constant(0, 32),
                    ))
                    .form(InstructionForm::new("base").fields([InstructionField::constant("110")])),
            ],
            sp: StackPointer {
                register: test_register(0),
                stack_size: 32,
                direction: StackDirection::Downwards,
            },
            pc: test_register(3),
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

    fn register_set(registers: &[u8]) -> HashSet<ArchitecturalRegister> {
        registers
            .iter()
            .map(|register| test_register(*register))
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
    fn instruction_register_reads_ignores_false_guarded_effects() {
        let effects = vec![Effect::write_register_if(
            bool_const(false),
            fixed_register(Register(0), 4),
            read_fixed_register(Register(1), 4, 32),
        )];

        assert_eq!(instruction_register_reads(&effects), HashSet::new());
    }

    #[test]
    fn instruction_register_writes_only_counts_unconditional_register_writes() {
        let effects = vec![
            Effect::write_register_if(
                bool_const(false),
                fixed_register(Register(0), 4),
                constant(0, 32),
            ),
            Effect::write_register_if(
                read_fixed_register(Register(1), 4, 1),
                fixed_register(Register(2), 4),
                constant(0, 32),
            ),
            Effect::write_register(fixed_register(Register(3), 4), constant(0, 32)),
        ];

        assert_eq!(instruction_register_writes(&effects), register_set(&[3]));
    }

    #[test]
    fn from_program_splits_fallthrough_and_pc_relative_branch_target_blocks() {
        let isa = test_isa();
        let program = decode_program(&["000", "100", "000", "000"], &isa);

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
        let program = decode_program(&["100", "000", "000", "100", "000", "000"], &isa);

        let analysis = ProgramAnalysis::from_program(program, &isa);

        assert_eq!(block_starts(&analysis), vec![0, 1, 2, 4, 5]);
        assert_eq!(
            block_successors(&analysis),
            vec![vec![1, 2], vec![2], vec![3, 4], vec![4], vec![]]
        );
    }

    #[test]
    fn compute_liveliness_tracks_straight_line_register_uses() {
        let isa = test_isa();
        let program = decode_program(&["001", "011"], &isa);

        let mut analysis = ProgramAnalysis::from_program(program, &isa);
        analysis.compute_liveliness();

        assert_eq!(block_starts(&analysis), vec![0]);
        assert_eq!(block_live_ins(&analysis), vec![register_set(&[1])]);
        assert_eq!(block_live_outs(&analysis), vec![HashSet::new()]);
    }

    #[test]
    fn compute_liveliness_propagates_live_ins_across_branch_successors() {
        let isa = test_isa();
        let program = decode_program(&["001", "100", "010", "011"], &isa);

        let mut analysis = ProgramAnalysis::from_program(program, &isa);
        analysis.compute_liveliness();

        assert_eq!(block_starts(&analysis), vec![0, 2, 3]);
        assert_eq!(
            block_successors(&analysis),
            vec![vec![1, 2], vec![2], vec![]]
        );
        assert_eq!(
            block_live_ins(&analysis),
            vec![register_set(&[1]), register_set(&[0]), register_set(&[1])]
        );
        assert_eq!(
            block_live_outs(&analysis),
            vec![register_set(&[0, 1]), register_set(&[1]), HashSet::new()]
        );
    }

    #[test]
    fn compute_liveliness_reaches_fixed_point_for_loop_successors() {
        let isa = test_isa();
        let program = decode_program(&["110", "010", "101", "011"], &isa);

        let mut analysis = ProgramAnalysis::from_program(program, &isa);
        analysis.compute_liveliness();

        assert_eq!(block_starts(&analysis), vec![0, 1, 3]);
        assert_eq!(
            block_successors(&analysis),
            vec![vec![1], vec![2, 1], vec![]]
        );
        assert_eq!(
            block_live_ins(&analysis),
            vec![HashSet::new(), register_set(&[0]), register_set(&[1])]
        );
        assert_eq!(
            block_live_outs(&analysis),
            vec![register_set(&[0]), register_set(&[0, 1]), HashSet::new()]
        );
    }
}
