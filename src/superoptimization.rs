// Given a certain instruction, a specification for the ISA,
// as well as a list of valid values for features, the goal
// of this file is to
//      1. Identify whether the instruction is valid under the new ISA
//      2. If it is not valid, generate some functionally equivalent replacement for the instruction

use std::collections::HashMap;

use crate::{
    instruction_semantics::FieldName,
    isa_specification::{FieldUses, Instruction},
};

pub struct SuperoptimizationCtx {
    pub field_values: HashMap<FieldName, FieldUses>,
    pub isa: Vec<Instruction>,
    // A list of already found equivalent instruction sequences (Instruction -> Multiple instructions)
    equivalent_instruction_sequences: Vec<(Instruction, Vec<Instruction>)>,
}
