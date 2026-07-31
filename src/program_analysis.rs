use std::collections::HashSet;

use crate::isa_specification::{ArchitecturalRegister, DecodedInstruction, ISA};

pub struct ProgramAnalysis<'a> {
    /// All instructions in the program
    pub program: Vec<BasicBlock<'a>>,
    isa: &'a ISA,
}

pub struct BasicBlock<'a> {
    /// HashSet of all registers which are read before being overwritten (ie their pre-block
    /// contents are used by this basic block in some calculation)
    pub live_in_regs: HashSet<ArchitecturalRegister>,
    /// HashSet of all registers which have their contents changed during the course of this basic block
    consumed_registers: HashSet<ArchitecturalRegister>,
    /// HashSet of all live-out registers (ie registers which may or may not be read after the
    /// basic block completes). Calculated assuming any branch could be taken. If live_out_regs is
    /// None, that means it hasn't yet been calculated
    pub live_out_regs: Option<HashSet<ArchitecturalRegister>>,
    /// A list of pointers to all other basic blocks which this basic block can lead to (excluding itself)
    next_blocks: HashSet<&'a BasicBlock<'a>>,
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

impl<'a> ProgramAnalysis<'a> {
    // pub fn from_program(program: Vec<DecodedInstruction>, isa: &'a ISA) -> Self {

    // }
}
