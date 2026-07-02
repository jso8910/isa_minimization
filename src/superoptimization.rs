// Given a certain instruction, a specification for the ISA,
// as well as a list of valid values for features, the goal
// of this file is to
//      1. Identify whether the instruction is valid under the new ISA
//      2. If it is not valid, generate some functionally equivalent replacement for the instruction

use std::collections::HashMap;

use itertools::Itertools;
use rand::{RngExt, rngs::ThreadRng};

use crate::{
    bit::Bit,
    constants::{MCMC_TEMP, SUPEROPTIMIZATION_PROGRAM_LEN, WEIGHT_PROG_LEN},
    instruction_semantics::{Effect, Expr, FieldName, OperandRef, RegisterRef},
    isa_specification::{
        ArchitecturalRegister, DecodedField, DecodedInstruction, FieldUses, ISA, InstructionForm,
        MergeMode, StackDirection,
    },
    semantic_matching::{
        BddEquality, EquivalenceManager, MachineState, evaluate_expr, instruction_seq_to_effects,
    },
};

pub struct SuperoptimizationCtx<'a> {
    pub isa: &'a ISA,
    valid_field_uses: HashMap<FieldName, FieldUses>,
    counterexamples: Vec<MachineState>,
    original_program: Program,
    gen_program: Program,
    gen_program_cost: f64,
    original_program_effects: Vec<Effect>,
    protected_registers: Vec<ArchitecturalRegister>,

    instr_form_encoding_count: Vec<(usize, usize, u64)>,

    rng: ThreadRng,
}

impl<'a> SuperoptimizationCtx<'a> {
    pub fn new_from_single_instruction(
        original_instruction: DecodedInstruction,
        valid_field_uses: HashMap<FieldName, FieldUses>,
        isa: &'a ISA,
        protected_registers: Vec<ArchitecturalRegister>,
    ) -> Self {
        let original_program =
            Program::from_instructions(vec![original_instruction], SUPEROPTIMIZATION_PROGRAM_LEN);
        let rng = rand::rng();
        let gen_program = Program::from_instructions(vec![], SUPEROPTIMIZATION_PROGRAM_LEN);
        let original_program_effects = instruction_seq_to_effects(&original_program, isa);

        // Generate the legal count per instruction in the ISA
        let mut instr_form_encoding_count = Vec::new();
        for (instruction_idx, instruction) in isa.instructions.iter().enumerate() {
            for (form_idx, form) in instruction.forms.iter().enumerate() {
                let encodings = form.fields_to_encodings(&valid_field_uses);

                let mut legal_instruction_count: u64 = 0;
                for encoding in encodings.iter() {
                    // If there are n variable bits, this combined encoding counts for 2^n total encodings
                    legal_instruction_count += 1 << encoding.num_variable();
                }

                instr_form_encoding_count.push((
                    instruction_idx,
                    form_idx,
                    legal_instruction_count,
                ));
            }
        }
        Self {
            isa,
            valid_field_uses,
            counterexamples: vec![],
            original_program,
            gen_program,
            gen_program_cost: f64::INFINITY,
            original_program_effects,
            protected_registers,
            instr_form_encoding_count,
            rng,
        }
    }

    /// Returns whether an instruction is valid under the new ISA (valid_field_uses)
    fn instruction_valid(&self, instr: &DecodedInstruction) -> bool {
        for field in instr.fields.iter() {
            let Some(name) = &field.name else {
                // constant field
                continue;
            };
            let Some(valid_uses) = self.valid_field_uses.get(name) else {
                // The entire instruction form is illegal because it uses a field which we don't use
                return false;
            };

            match valid_uses {
                FieldUses::Uses { patterns, .. } => {
                    // At least one pattern must match
                    let matches = if field.value.bits.iter().any(|bit| *bit == Bit::Var) {
                        patterns
                            .iter()
                            .any(|pattern| field.value.matches_bits(&pattern.bits))
                    } else {
                        patterns
                            .iter()
                            .any(|pattern| pattern.matches_bits(&field.value.bits))
                    };
                    if !matches {
                        return false;
                    }
                }
                FieldUses::VariableBits { pattern, .. } => {
                    if !pattern.matches_bits(&field.value.bits) {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Selects a legal instruction (under valid_field_uses) randomly
    fn select_random_instruction(&mut self) -> DecodedInstruction {
        Self::select_random_instruction_with_rng(
            self.isa,
            &self.valid_field_uses,
            &self.instr_form_encoding_count,
            &mut self.rng,
        )
    }

    fn select_random_instruction_with_rng<R: RngExt>(
        isa: &ISA,
        valid_field_uses: &HashMap<FieldName, FieldUses>,
        instr_form_encoding_count: &[(usize, usize, u64)],
        rng: &mut R,
    ) -> DecodedInstruction {
        // First, we want to choose which instruction form the new instruction will be
        // This is done by sampling according to the counts in instr_form_encoding_count

        let total_weight: u64 = instr_form_encoding_count
            .iter()
            .map(|(_, _, count)| *count)
            .sum();
        let mut target = rng.random_range(0..total_weight);
        let mut selected_indices = None;
        for (instruction_idx, form_idx, count) in instr_form_encoding_count.iter() {
            if target < *count {
                selected_indices = Some((*instruction_idx, *form_idx));
                break;
            }
            target -= *count;
        }

        let (instruction_idx, form_idx) =
            selected_indices.expect("No instruction forms to select from");
        let selected_instruction = &isa.instructions[instruction_idx];
        let selected_form = &selected_instruction.forms[form_idx];

        loop {
            let mut bits = Vec::with_capacity(selected_form.width());
            let mut fields = Vec::with_capacity(selected_form.fields.len());
            let mut valid = true;

            for field in selected_form.fields.iter() {
                let pattern_idx = bits.len();
                let value = match &field.name {
                    Some(name) => {
                        let Some(field_use) = valid_field_uses.get(name) else {
                            valid = false;
                            break;
                        };
                        match (field.merge_mode, field_use) {
                            (MergeMode::VariableBits, FieldUses::VariableBits { pattern, .. }) => {
                                pattern.clone()
                            }
                            (MergeMode::Uses, FieldUses::Uses { patterns, .. }) => {
                                let selected = rng.random_range(0..patterns.len());
                                patterns
                                    .iter()
                                    .nth(selected)
                                    .expect("Field use must contain at least one pattern")
                                    .clone()
                            }
                            _ => {
                                valid = false;
                                break;
                            }
                        }
                    }
                    None => field.pattern.clone(),
                };

                let Some(mut value) = selected_form.constrain_variable_bits(
                    &value,
                    pattern_idx,
                    field.name.as_deref().unwrap_or("__const__"),
                ) else {
                    valid = false;
                    break;
                };

                // Randomly set Var bits to high or low
                for bit in value.bits.iter_mut() {
                    if *bit == Bit::Var {
                        *bit = if rng.random() { Bit::High } else { Bit::Low };
                    }
                }

                bits.extend(value.bits.iter().copied());
                fields.push(DecodedField {
                    name: field.name.clone(),
                    value,
                    merge_mode: field.merge_mode,
                    is_immediate: field.is_immediate,
                    is_register_read: field.is_register_read,
                    is_register_write: field.is_register_write,
                });
            }

            if !valid {
                continue;
            }

            let instruction = DecodedInstruction {
                name: Some(selected_instruction.name.clone()),
                form: Some(selected_form.clone()),
                bits,
                fields,
            };

            if selected_form.when.check(&instruction)
                && selected_instruction
                    .constraints
                    .iter()
                    .all(|constraint| constraint.check(&instruction))
            {
                return instruction;
            }
        }
    }

    /// Naive superoptimization which merely iterates through all valid instructions,
    /// checks whether they are valid (`instruction_valid`), checks whether they meet state constraints,
    /// then does the following to check whether the instruction sequences match, only moving to the next check if previous succeeds
    ///     1. Compare canonical forms of all effect exprs - if equal, they match
    ///             TODO not done yet
    ///     2. Check 5 random MachineState cases
    ///             TODO not done yet
    ///     3. Checks against all MachineStates in counterexamples
    ///     4. Checking using a BDD whether the sequences are equivalent, adding counterexamples if applicable
    pub fn naive_superoptimize(&mut self) -> Option<Program> {
        self.clear_counterexamples();
        let mut equivalence_manager =
            EquivalenceManager::from_left_instruction(&self.original_program, self.isa);
        // let candidates = self.all_legal_instructions();
        // println!("{}", candidates.len());
        // just iterate by length
        // this is quite naive
        for length in 0..10 {
            println!("{}", length);
            let mut i = 0;
            // for sequence in candidates.iter().cloned().permutations(length) {
            // i += 1;
            // if i % 10_000 == 0 {
            //     println!("{i}");
            // }
            // if !self.sequence_meets_state_constraints(&sequence) {
            //     continue;
            // }
            // if !self.sequence_matches_counterexamples(&sequence) {
            //     continue;
            // }
            // equivalence_manager.replace_right_instruction(&sequence);
            // let BddEquality::Unequal(counterexample) = equivalence_manager
            //     .compare_instructions()
            //     .unwrap_or_else(|e| panic!("Error: {e}"))
            // else {
            //     self.gen_program = sequence.clone();
            //     return Some(sequence);
            // };
            // self.add_counterexample(counterexample);
            // }
        }

        None
    }

    /// Returns the cost of a new instruction sequence, and selects it if applicable
    /// If false is returned, the proposal was not accepted.
    /// If true is returned, gen_instruction_seq is set to the `proposal` and
    /// `gen_instruction_seq_cost` is set to `cost(proposal)`
    fn decide_proposal_acceptance(&mut self, proposal: Program) -> bool {
        // Preliminary cost -- not yet complete calculating
        let mut cost: f64 = self
            .performance_cost(&proposal)
            .try_into()
            .expect("Could not convert u32 to f64");

        // Now, calculate random number which determines whether new sequence is selected
        let random: f64 = self.rng.random();

        // Currently, I am assuming that the "proposal distribution is symmetric" invariant is true
        // If it isn't, the calculations will be slightly worse.
        // FIXME make sure this is true givne my specific proposal distribution

        // We accept the new proposal iff:
        // cost' < cost - log(p) / beta, beta = 1/T (inverse temperature)
        let maximum_cost: f64 = self.gen_program_cost
            - random.ln() * f64::try_from(MCMC_TEMP).expect("Could not convert u32 to f64");

        for counterexample in self.counterexamples.iter() {
            cost += self.equality_cost(&proposal, counterexample);

            // At this point, we can exit early
            if cost > maximum_cost {
                return false;
            }
        }
        self.gen_program_cost = cost;
        self.gen_program = proposal;
        true
    }

    /// Evaluates performance cost of instruction sequence
    /// Currently, just the length of the sequence
    fn performance_cost(&self, sequence: &Program) -> u32 {
        u32::try_from(sequence.iter_instructions().count()).expect("Sequence doesn't fit into u32")
            * WEIGHT_PROG_LEN
    }

    /// Calculates equality cost for a sequence against a single counterexample
    fn equality_cost(&self, sequence: &Program, counterexample: &MachineState) -> f64 {
        let new_machinestate = self.execute_test(&sequence, &counterexample);
        let desired_machinestate = self.execute_test(&self.original_program, &counterexample);

        let sp_val = counterexample
            .registers
            .get(&(self.isa.sp.register.identifier as u128))
            .map(|value| value.value)
            .unwrap_or(0);

        let equality_cost: f64 = desired_machinestate
            .compare(
                &new_machinestate,
                &self.protected_registers,
                &self.isa.sp,
                sp_val,
            )
            .try_into()
            .expect("Could not convert u32 to f64");

        equality_cost
    }

    fn add_counterexample(&mut self, counterexample: MachineState) {
        // Add the extra cost to gen_instruction_seq_cost
        self.gen_program_cost += self.equality_cost(&self.gen_program, &counterexample);
        self.counterexamples.push(counterexample);
    }

    fn clear_counterexamples(&mut self) {
        self.counterexamples = vec![];
        self.gen_program_cost = self
            .performance_cost(&self.gen_program)
            .try_into()
            .expect("Could not convert u32 to f64");
    }

    /// Checks an instruction sequence against all counterexamples
    /// Returns true if it matches all, false if it doesnt
    fn sequence_matches_counterexamples(&self, sequence: &Program) -> bool {
        // todo!();
        self.counterexamples
            .iter()
            // .all(|state| self.check_sequence_machinestate(sequence, state))
            .all(|state| self.passes_test(sequence, state))
    }

    /// Whether an instruction sequence passes a test
    pub fn passes_test(&self, sequence: &Program, state: &MachineState) -> bool {
        let original_state = self.execute_test(&self.original_program, state);
        let generated_state = self.execute_test(sequence, state);
        let sp_val = state
            .registers
            .get(&(self.isa.sp.register.identifier as u128))
            .map(|value| value.value)
            .unwrap_or(0);

        original_state.compare(
            &generated_state,
            &self.protected_registers,
            &self.isa.sp,
            sp_val,
        ) == 0
    }

    /// Runs an instruction sequence against a MachineState, and returns the resulting MachineState
    pub fn execute_test(&self, sequence: &Program, state: &MachineState) -> MachineState {
        let mut next_state = state.clone();
        for effect in instruction_seq_to_effects(sequence, self.isa) {
            match effect {
                Effect::WriteRegister {
                    guard,
                    register,
                    value,
                } => {
                    if evaluate_expr(&guard, state).is_none_or(|guard| guard.value == 0) {
                        continue;
                    }

                    if let (Some(register), Some(value)) = (
                        evaluate_expr(&register, state),
                        evaluate_expr(&value, state),
                    ) {
                        next_state.registers.insert(register.value, value);
                    }
                }
                Effect::WriteMemory {
                    guard,
                    address,
                    value,
                    width,
                } => {
                    if evaluate_expr(&guard, state).is_none_or(|guard| guard.value == 0) {
                        continue;
                    }

                    if let (Some(address), Some(value)) =
                        (evaluate_expr(&address, state), evaluate_expr(&value, state))
                    {
                        next_state.memory.insert((address.value, width), value);
                    }
                }
            }
        }
        next_state
    }

    fn sequence_meets_state_constraints(&self, sequence: &Program) -> bool {
        let effects = instruction_seq_to_effects(sequence, self.isa);
        generated_effects_meet_state_constraints(
            &effects,
            &self.original_program_effects,
            &self.protected_registers,
            self.isa,
        )
    }

    fn form_field_uses_are_compatible(&self, form: &InstructionForm) -> bool {
        form.fields.iter().all(|field| {
            let Some(name) = &field.name else {
                return true;
            };
            let Some(field_use) = self.valid_field_uses.get(name) else {
                return true;
            };
            matches!(
                (field.merge_mode, field_use),
                (MergeMode::Uses, FieldUses::Uses { .. })
                    | (MergeMode::VariableBits, FieldUses::VariableBits { .. })
            )
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramInstr {
    UNUSED,
    Instruction(DecodedInstruction),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub instructions: Vec<ProgramInstr>,
}

impl Program {
    pub fn from_instructions(instructions: Vec<DecodedInstruction>, length: usize) -> Self {
        assert!(instructions.len() <= length);
        let mut program_seq = vec![ProgramInstr::UNUSED; length];

        for (i, instr) in instructions.into_iter().enumerate() {
            program_seq[i] = ProgramInstr::Instruction(instr);
        }

        Program {
            instructions: program_seq,
        }
    }

    pub fn iter_instructions(&self) -> impl Iterator<Item = &DecodedInstruction> {
        self.instructions.iter().filter_map(|instr| match instr {
            ProgramInstr::UNUSED => None,
            ProgramInstr::Instruction(i) => Some(i),
        })
    }
}

fn expand_variable_bits(bits: &[Bit]) -> Vec<Vec<Bit>> {
    fn helper(bits: &[Bit], current: &mut Vec<Bit>, expanded: &mut Vec<Vec<Bit>>) {
        let Some((bit, rest)) = bits.split_first() else {
            expanded.push(current.clone());
            return;
        };

        match bit {
            Bit::Low | Bit::High => {
                current.push(*bit);
                helper(rest, current, expanded);
                current.pop();
            }
            Bit::Var => {
                current.push(Bit::Low);
                helper(rest, current, expanded);
                current.pop();
                current.push(Bit::High);
                helper(rest, current, expanded);
                current.pop();
            }
            Bit::Test => panic!("Test bits should not appear in instruction encodings"),
        }
    }

    let mut expanded = Vec::new();
    helper(bits, &mut Vec::new(), &mut expanded);
    expanded
}

/// Cheaply rejects generated instruction sequences that use unsupported state destinations.
///
/// This is intended for the superoptimization hot path. It performs only syntactic checks after
/// lowering effects into the initial-state coordinate system:
/// - register write destinations must be constants/fixed registers,
///     - these constant registers are not protected by some form of read dependency or convention
/// - the stack pointer register may not be written,
/// - memory writes must either target an original memory write destination exactly or an approved
///   SP-relative scratch byte,
/// - every original write destination must have a corresponding generated write destination.
pub fn generated_sequence_meets_state_constraints(
    generated: &Program,
    original: &Program,
    protected_registers: &[ArchitecturalRegister],
    isa: &ISA,
) -> bool {
    let original_effects = instruction_seq_to_effects(original, isa);
    let generated_effects = instruction_seq_to_effects(generated, isa);

    generated_effects_meet_state_constraints(
        &generated_effects,
        &original_effects,
        protected_registers,
        isa,
    )
}

/// Checks already-lowered effects against the same destination constraints as
/// `generated_sequence_meets_state_constraints`.
///
/// Use this in hot paths when the original sequence's effects have already been computed.
pub fn generated_effects_meet_state_constraints(
    generated_effects: &[Effect],
    original_effects: &[Effect],
    protected_registers: &[ArchitecturalRegister],
    isa: &ISA,
) -> bool {
    let protected_register_identifiers: Vec<_> =
        protected_registers.iter().map(|r| r.identifier).collect();
    if !original_effects.iter().all(|original_effect| {
        generated_effects
            .iter()
            .any(|generated_effect| effect_destinations_match(original_effect, generated_effect))
    }) {
        return false;
    }

    let original_memory_destinations: Vec<_> = original_effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::WriteMemory { address, .. } => Some(address),
            Effect::WriteRegister { .. } => None,
        })
        .collect();

    let original_register_identifiers: Vec<_> = original_effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::WriteMemory { .. } => None,
            Effect::WriteRegister { register, .. } => Some(register_destination(register)),
        })
        .collect();

    generated_effects.iter().all(|effect| match effect {
        Effect::WriteRegister { register, .. } => {
            // Check whether write is to an illegal destination
            register_destination(register)
                .is_some_and(|destination| destination != isa.sp.register.identifier as u128 && !protected_register_identifiers.contains(&(destination as u8)))
            // but the destination is legal if it was an original register identifier
            || original_register_identifiers
                .iter()
                // Register must be Some, not None
                .any(|original_ident| register_destination(register)
                    .is_some_and(|r| Some(r) == *original_ident))
        }
        Effect::WriteMemory { address, .. } => {
            original_memory_destinations
                .iter()
                .any(|original_address| *original_address == address)
                || is_allowed_stack_scratch_address(address, isa)
        }
    })
}

fn effect_destinations_match(left: &Effect, right: &Effect) -> bool {
    match (left, right) {
        (
            Effect::WriteRegister {
                register: left_register,
                ..
            },
            Effect::WriteRegister {
                register: right_register,
                ..
            },
        ) => register_destination(left_register)
            .zip(register_destination(right_register))
            .is_some_and(|(left_destination, right_destination)| {
                left_destination == right_destination
            }),
        (
            Effect::WriteMemory {
                address: left_address,
                width: left_width,
                ..
            },
            Effect::WriteMemory {
                address: right_address,
                width: right_width,
                ..
            },
        ) => left_address == right_address && left_width == right_width,
        _ => false,
    }
}

fn register_destination(register: &Expr) -> Option<u128> {
    match register {
        Expr::Const { value, .. } => Some(*value),
        Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed { register, .. })) => {
            Some(register.0 as u128)
        }
        _ => None,
    }
}

fn is_allowed_stack_scratch_address(address: &Expr, isa: &ISA) -> bool {
    let Some((direction, offset)) = stack_pointer_relative_offset(address, isa.sp.register) else {
        return false;
    };

    let stack_size = isa.sp.stack_size as u128;
    if offset == 0 || offset > stack_size {
        return false;
    }

    direction == isa.sp.direction
}

fn stack_pointer_relative_offset(
    address: &Expr,
    sp: ArchitecturalRegister,
) -> Option<(StackDirection, u128)> {
    if is_stack_pointer_value(address, sp) {
        return Some((StackDirection::Upwards, 0));
    }

    match address {
        Expr::Add(lhs, rhs) => sp_relative_add_offset(lhs, rhs, sp),
        Expr::Sub(lhs, rhs) if is_stack_pointer_value(lhs, sp) => {
            constant_value(rhs).map(|(value, _)| (StackDirection::Downwards, value))
        }
        _ => None,
    }
}

fn sp_relative_add_offset(
    lhs: &Expr,
    rhs: &Expr,
    sp: ArchitecturalRegister,
) -> Option<(StackDirection, u128)> {
    if is_stack_pointer_value(lhs, sp) {
        constant_value(rhs).and_then(twos_complement_offset)
    } else if is_stack_pointer_value(rhs, sp) {
        constant_value(lhs).and_then(twos_complement_offset)
    } else {
        None
    }
}

fn twos_complement_offset((value, width): (u128, u16)) -> Option<(StackDirection, u128)> {
    let mask = bit_mask(width)?;
    let value = value & mask;
    if value == 0 {
        return Some((StackDirection::Upwards, 0));
    }

    let sign_bit = 1u128.checked_shl((width - 1) as u32)?;
    if value & sign_bit == 0 {
        Some((StackDirection::Upwards, value))
    } else {
        Some((StackDirection::Downwards, ((!value).wrapping_add(1)) & mask))
    }
}

fn is_stack_pointer_value(expr: &Expr, sp: ArchitecturalRegister) -> bool {
    match expr {
        Expr::ReadRegister { register, .. } => register_destination(register)
            .is_some_and(|destination| destination == sp.identifier as u128),
        _ => false,
    }
}

fn constant_value(expr: &Expr) -> Option<(u128, u16)> {
    match expr {
        Expr::Const { value, width } => Some((*value, *width)),
        _ => None,
    }
}

fn bit_mask(width: u16) -> Option<u128> {
    match width {
        0 => None,
        128 => Some(!0),
        width if width < 128 => Some((1u128 << width) - 1),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        bit::BitPattern,
        instruction_semantics::{Register, add, constant, fixed_register, read_register, sub},
        isa_specification::{
            Instruction, InstructionField, InstructionForm, StackPointer, field_eq,
        },
        semantic_matching::BitWord,
    };
    use rand::{SeedableRng, rngs::StdRng};

    const SP_ID: u8 = 31;
    const PC_ID: u8 = 30;

    fn arch_register(identifier: u8) -> ArchitecturalRegister {
        ArchitecturalRegister {
            identifier,
            identifier_width: 8,
            width: 32,
        }
    }

    fn test_isa(direction: StackDirection, instructions: Vec<Instruction>) -> ISA {
        let sp = arch_register(SP_ID);
        ISA {
            registers: vec![arch_register(0), arch_register(1), arch_register(2), sp],
            instructions,
            sp: StackPointer {
                register: sp,
                stack_size: 16,
                direction,
            },
            pc: arch_register(PC_ID),
        }
    }

    fn encoded_instruction(name: &str, bits: &str, effects: Vec<Effect>) -> Instruction {
        instruction_with_form(
            name,
            InstructionForm::new(format!("{name}_form")).field(InstructionField::constant(bits)),
            effects,
        )
    }

    fn instruction_with_form(
        name: &str,
        form: InstructionForm,
        effects: Vec<Effect>,
    ) -> Instruction {
        let mut instruction = Instruction::new(name, form.width()).form(form);
        for effect in effects {
            instruction = instruction.effect(effect);
        }
        instruction
    }

    fn decode_one(isa: &ISA, bits: &str, expected_name: &str) -> DecodedInstruction {
        let decoded =
            DecodedInstruction::decode_program_str(bits, isa).expect("test instruction decodes");
        assert_eq!(decoded.len(), 1);
        let decoded = decoded.into_iter().next().unwrap();
        assert_eq!(decoded.name.as_deref(), Some(expected_name));
        decoded
    }

    fn fixed_reg(identifier: u8) -> Expr {
        fixed_register(Register(identifier), 8)
    }

    fn read_reg(identifier: u8) -> Expr {
        read_register(fixed_reg(identifier), 32)
    }

    fn sp_value() -> Expr {
        read_reg(SP_ID)
    }

    fn sequence(isa: &ISA, bits: &str, expected_name: &str) -> Program {
        Program::from_instructions(vec![decode_one(isa, bits, expected_name)], 1)
    }

    fn variable_bits_use(name: &str, pattern: &str) -> (FieldName, FieldUses) {
        (
            name.to_owned(),
            FieldUses::VariableBits {
                name: name.to_owned(),
                pattern: BitPattern::parse(pattern),
            },
        )
    }

    fn uses_field(name: &str, patterns: &[&str]) -> (FieldName, FieldUses) {
        (
            name.to_owned(),
            FieldUses::Uses {
                name: name.to_owned(),
                patterns: patterns
                    .iter()
                    .map(|pattern| BitPattern::parse(pattern))
                    .collect(),
            },
        )
    }

    #[test]
    fn expand_variable_bits_enumerates_all_assignments_in_order() {
        let expanded = expand_variable_bits(&[Bit::High, Bit::Var, Bit::Low, Bit::Var]);

        assert_eq!(
            expanded,
            vec![
                vec![Bit::High, Bit::Low, Bit::Low, Bit::Low],
                vec![Bit::High, Bit::Low, Bit::Low, Bit::High],
                vec![Bit::High, Bit::High, Bit::Low, Bit::Low],
                vec![Bit::High, Bit::High, Bit::Low, Bit::High],
            ]
        );
    }

    #[test]
    fn program_from_instructions_pads_with_unused_and_iterates_instructions() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("FIRST", "00", vec![]),
                encoded_instruction("SECOND", "01", vec![]),
            ],
        );

        let program = Program::from_instructions(
            vec![
                decode_one(&isa, "00", "FIRST"),
                decode_one(&isa, "01", "SECOND"),
            ],
            4,
        );

        assert_eq!(program.instructions.len(), 4);
        assert!(matches!(program.instructions[2], ProgramInstr::UNUSED));
        assert!(matches!(program.instructions[3], ProgramInstr::UNUSED));
        assert_eq!(
            program
                .iter_instructions()
                .map(|instruction| instruction.name.as_deref())
                .collect::<Vec<_>>(),
            vec![Some("FIRST"), Some("SECOND")]
        );
    }

    #[test]
    fn superoptimization_ctx_initializes_from_single_instruction() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![encoded_instruction("ORIGINAL", "0000", vec![])],
        );
        let original = decode_one(&isa, "0000", "ORIGINAL");
        let mut valid_field_uses = HashMap::new();
        valid_field_uses.insert(
            variable_bits_use("imm", "1x").0,
            variable_bits_use("imm", "1x").1,
        );

        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            original.clone(),
            valid_field_uses,
            &isa,
            vec![],
        );

        assert!(std::ptr::eq(ctx.isa, &isa));
        assert_eq!(
            ctx.original_program,
            Program::from_instructions(vec![original], SUPEROPTIMIZATION_PROGRAM_LEN)
        );
        assert_eq!(ctx.gen_program.iter_instructions().count(), 0);
        assert!(ctx.counterexamples.is_empty());
        assert!(ctx.valid_field_uses.contains_key("imm"));
    }

    #[test]
    fn select_random_instruction_generates_valid_instructions_with_even_coverage() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "000", vec![]),
                instruction_with_form(
                    "CANDIDATE",
                    InstructionForm::new("candidate")
                        .field(InstructionField::variable("opcode", 1).merge_mode_uses())
                        .field(InstructionField::variable("imm", 2)),
                    vec![],
                ),
            ],
        );
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "000", "ORIGINAL"),
            HashMap::from([
                uses_field("opcode", &["0", "1"]),
                variable_bits_use("imm", "xx"),
            ]),
            &isa,
            vec![],
        );
        ctx.instr_form_encoding_count = vec![(1, 0, 8)];
        let mut rng = StdRng::seed_from_u64(0x5eed);
        let mut counts = [0usize; 8];

        for _ in 0..4096 {
            let instruction = SuperoptimizationCtx::select_random_instruction_with_rng(
                ctx.isa,
                &ctx.valid_field_uses,
                &ctx.instr_form_encoding_count,
                &mut rng,
            );

            assert_eq!(instruction.name.as_deref(), Some("CANDIDATE"));
            assert!(ctx.instruction_valid(&instruction));
            counts[instruction.bits.iter().fold(0, |acc, bit| {
                (acc << 1)
                    | match bit {
                        Bit::High => 1,
                        Bit::Low => 0,
                        _ => panic!("random instruction should not contain symbolic bits"),
                    }
            })] += 1;
        }

        for count in counts {
            assert!(
                (400..=625).contains(&count),
                "sample count {count} fell outside expected loose uniformity bounds"
            );
        }
    }

    #[test]
    fn select_random_instruction_retries_until_instruction_constraints_hold() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0", vec![]),
                Instruction::new("CONSTRAINED", 1)
                    .form(
                        InstructionForm::new("candidate")
                            .field(InstructionField::variable("imm", 1)),
                    )
                    .constraint(field_eq("imm", "1")),
            ],
        );
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0", "ORIGINAL"),
            HashMap::from([variable_bits_use("imm", "x")]),
            &isa,
            vec![],
        );
        ctx.instr_form_encoding_count = vec![(1, 0, 2)];
        let mut rng = StdRng::seed_from_u64(0xabad1dea);

        for _ in 0..64 {
            let instruction = SuperoptimizationCtx::select_random_instruction_with_rng(
                ctx.isa,
                &ctx.valid_field_uses,
                &ctx.instr_form_encoding_count,
                &mut rng,
            );

            assert_eq!(instruction.name.as_deref(), Some("CONSTRAINED"));
            assert_eq!(instruction.bits, vec![Bit::High]);
        }
    }

    #[test]
    fn select_random_instruction_wrapper_uses_context_rng_and_configuration() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0", vec![]),
                instruction_with_form(
                    "ONLY_CANDIDATE",
                    InstructionForm::new("candidate")
                        .field(InstructionField::variable("opcode", 1).merge_mode_uses()),
                    vec![],
                ),
            ],
        );
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0", "ORIGINAL"),
            HashMap::from([uses_field("opcode", &["1"])]),
            &isa,
            vec![],
        );
        ctx.instr_form_encoding_count = vec![(1, 0, 1)];

        let instruction = ctx.select_random_instruction();

        assert_eq!(instruction.name.as_deref(), Some("ONLY_CANDIDATE"));
        assert_eq!(instruction.bits, vec![Bit::High]);
    }

    #[test]
    fn cost_and_counterexample_helpers_update_context_state() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![encoded_instruction("ORIGINAL", "0", vec![])],
        );
        let original = decode_one(&isa, "0", "ORIGINAL");
        let proposal =
            Program::from_instructions(vec![original.clone()], SUPEROPTIMIZATION_PROGRAM_LEN);
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            original,
            HashMap::new(),
            &isa,
            vec![],
        );

        assert_eq!(ctx.performance_cost(&proposal), WEIGHT_PROG_LEN);
        assert!(ctx.decide_proposal_acceptance(proposal.clone()));
        assert_eq!(ctx.gen_program, proposal);
        assert_eq!(ctx.gen_program_cost, WEIGHT_PROG_LEN as f64);

        ctx.add_counterexample(MachineState::default());
        assert_eq!(ctx.counterexamples.len(), 1);
        assert_eq!(ctx.gen_program_cost, WEIGHT_PROG_LEN as f64);

        ctx.clear_counterexamples();
        assert!(ctx.counterexamples.is_empty());
        assert_eq!(ctx.gen_program_cost, WEIGHT_PROG_LEN as f64);
    }

    #[test]
    fn sequence_matches_counterexamples_requires_all_tests_to_pass() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "00",
                    vec![Effect::write_register(fixed_reg(1), constant(1, 32))],
                ),
                encoded_instruction(
                    "MATCHING",
                    "01",
                    vec![Effect::write_register(fixed_reg(1), constant(1, 32))],
                ),
                encoded_instruction(
                    "DIFFERENT",
                    "10",
                    vec![Effect::write_register(fixed_reg(1), constant(2, 32))],
                ),
            ],
        );
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "00", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );
        ctx.counterexamples.push(MachineState::default());

        assert!(ctx.sequence_matches_counterexamples(&sequence(&isa, "01", "MATCHING")));
        assert!(!ctx.sequence_matches_counterexamples(&sequence(&isa, "10", "DIFFERENT")));
    }

    #[test]
    fn sequence_meets_state_constraints_accepts_matching_destinations() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "00",
                    vec![Effect::write_register(fixed_reg(1), constant(1, 32))],
                ),
                encoded_instruction(
                    "GENERATED",
                    "01",
                    vec![Effect::write_register(fixed_reg(1), constant(2, 32))],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "00", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );

        assert!(ctx.sequence_meets_state_constraints(&sequence(&isa, "01", "GENERATED")));
    }

    #[test]
    fn form_field_uses_are_compatible_checks_merge_modes() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![encoded_instruction("ORIGINAL", "0", vec![])],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0", "ORIGINAL"),
            HashMap::from([uses_field("opcode", &["1"]), variable_bits_use("imm", "x")]),
            &isa,
            vec![],
        );

        assert!(
            ctx.form_field_uses_are_compatible(
                &InstructionForm::new("compatible")
                    .field(InstructionField::variable("opcode", 1).merge_mode_uses())
                    .field(InstructionField::variable("imm", 1))
            )
        );
        assert!(
            !ctx.form_field_uses_are_compatible(
                &InstructionForm::new("incompatible")
                    .field(InstructionField::variable("opcode", 1))
                    .field(InstructionField::variable("imm", 1).merge_mode_uses())
            )
        );
    }

    #[test]
    fn instruction_valid_accepts_uses_patterns_and_ignores_constant_fields() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0000", vec![]),
                instruction_with_form(
                    "CANDIDATE",
                    InstructionForm::new("candidate")
                        .field(InstructionField::constant("101"))
                        .field(
                            InstructionField::named("opcode", BitPattern::parse("xx"))
                                .merge_mode_uses(),
                        )
                        .field(InstructionField::named("imm", BitPattern::parse("xxxx"))),
                    vec![],
                ),
            ],
        );
        let valid_field_uses = HashMap::from([
            uses_field("opcode", &["00", "11"]),
            variable_bits_use("imm", "1xx0"),
        ]);
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            valid_field_uses,
            &isa,
            vec![],
        );
        let instr = decode_one(&isa, "101111010", "CANDIDATE");

        assert!(ctx.instruction_valid(&instr));
    }

    #[test]
    fn instruction_valid_rejects_missing_field_use_entry() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0", vec![]),
                instruction_with_form(
                    "CANDIDATE",
                    InstructionForm::new("candidate")
                        .field(InstructionField::variable("unknown", 1).merge_mode_uses()),
                    vec![],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0", "ORIGINAL"),
            HashMap::from([uses_field("known", &["1"])]),
            &isa,
            vec![],
        );
        let instr = decode_one(&isa, "1", "CANDIDATE");

        assert!(!ctx.instruction_valid(&instr));
    }

    #[test]
    fn instruction_valid_rejects_nonmatching_uses_pattern() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "00", vec![]),
                instruction_with_form(
                    "CANDIDATE",
                    InstructionForm::new("candidate")
                        .field(InstructionField::variable("opcode", 2).merge_mode_uses()),
                    vec![],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "00", "ORIGINAL"),
            HashMap::from([uses_field("opcode", &["00", "11"])]),
            &isa,
            vec![],
        );
        let instr = decode_one(&isa, "10", "CANDIDATE");

        assert!(!ctx.instruction_valid(&instr));
    }

    #[test]
    fn instruction_valid_rejects_nonmatching_variable_bits_pattern() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0000", vec![]),
                instruction_with_form(
                    "CANDIDATE",
                    InstructionForm::new("candidate").field(InstructionField::variable("imm", 4)),
                    vec![],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::from([variable_bits_use("imm", "10xx")]),
            &isa,
            vec![],
        );
        let instr = decode_one(&isa, "1101", "CANDIDATE");

        assert!(!ctx.instruction_valid(&instr));
    }

    #[test]
    fn instruction_valid_requires_every_named_field_to_be_valid() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "00000", vec![]),
                instruction_with_form(
                    "CANDIDATE",
                    InstructionForm::new("candidate")
                        .field(InstructionField::variable("opcode", 2).merge_mode_uses())
                        .field(InstructionField::variable("imm", 3)),
                    vec![],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "00000", "ORIGINAL"),
            HashMap::from([
                uses_field("opcode", &["01"]),
                variable_bits_use("imm", "xx1"),
            ]),
            &isa,
            vec![],
        );
        let instr = decode_one(&isa, "01000", "CANDIDATE");

        assert!(!ctx.instruction_valid(&instr));
    }

    #[test]
    #[ignore = "naive superoptimizer path is currently unfinished"]
    fn naive_superoptimize_finds_equivalent_single_instruction_in_minimal_isa() {
        let r0 = read_reg(0);
        let r1 = read_reg(1);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                instruction_with_form(
                    "ORIGINAL_ADD",
                    InstructionForm::new("original").field(
                        InstructionField::named("op", BitPattern::parse("0")).merge_mode_uses(),
                    ),
                    vec![Effect::write_register(
                        fixed_reg(2),
                        add(r0.clone(), r1.clone()),
                    )],
                ),
                instruction_with_form(
                    "CANDIDATE_ADD",
                    InstructionForm::new("candidate").field(
                        InstructionField::named("op", BitPattern::parse("1")).merge_mode_uses(),
                    ),
                    vec![Effect::write_register(fixed_reg(2), add(r1, r0))],
                ),
            ],
        );
        let original = decode_one(&isa, "0", "ORIGINAL_ADD");
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            original,
            HashMap::from([uses_field("op", &["1"])]),
            &isa,
            vec![],
        );

        let replacement = ctx
            .naive_superoptimize()
            .expect("naive superoptimizer should find the commuted add");

        let replacement_instructions = replacement.iter_instructions().collect::<Vec<_>>();
        assert_eq!(replacement_instructions.len(), 1);
        assert_eq!(
            replacement_instructions[0].name.as_deref(),
            Some("CANDIDATE_ADD")
        );
        assert_eq!(ctx.gen_program, replacement);
        assert!(ctx.counterexamples.is_empty());
    }

    #[test]
    #[ignore = "naive superoptimizer path is currently unfinished"]
    fn naive_superoptimize_finds_two_instruction_replacement_in_minimal_isa() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                instruction_with_form(
                    "ORIGINAL_SET_TWO_REGISTERS",
                    InstructionForm::new("original").field(
                        InstructionField::named("op", BitPattern::parse("00")).merge_mode_uses(),
                    ),
                    vec![
                        Effect::write_register(fixed_reg(0), constant(1, 2)),
                        Effect::write_register(fixed_reg(1), constant(2, 2)),
                    ],
                ),
                instruction_with_form(
                    "SET_R0_ONE",
                    InstructionForm::new("first").field(
                        InstructionField::named("op", BitPattern::parse("01")).merge_mode_uses(),
                    ),
                    vec![Effect::write_register(fixed_reg(0), constant(1, 2))],
                ),
                instruction_with_form(
                    "SET_R1_TWO",
                    InstructionForm::new("second").field(
                        InstructionField::named("op", BitPattern::parse("10")).merge_mode_uses(),
                    ),
                    vec![Effect::write_register(fixed_reg(1), constant(2, 2))],
                ),
            ],
        );
        let original = decode_one(&isa, "00", "ORIGINAL_SET_TWO_REGISTERS");
        let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
            original,
            HashMap::from([uses_field("op", &["01", "10"])]),
            &isa,
            vec![],
        );

        let replacement = ctx
            .naive_superoptimize()
            .expect("naive superoptimizer should build the value through r2");

        let names = replacement
            .iter_instructions()
            .map(|instruction| instruction.name.as_deref())
            .collect::<Vec<_>>();
        assert_eq!(names, vec![Some("SET_R0_ONE"), Some("SET_R1_TWO")]);
        assert_eq!(ctx.gen_program, replacement);
    }

    #[test]
    fn execute_test_applies_sequence_effects_to_machine_state() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0000", vec![]),
                encoded_instruction(
                    "GENERATED",
                    "0001",
                    vec![
                        Effect::write_register(fixed_reg(1), add(read_reg(0), constant(5, 32))),
                        Effect::write_memory(read_reg(2), constant(0xab, 8), 8),
                    ],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );
        let state = MachineState {
            registers: HashMap::from([
                (0, BitWord::new(7, 32)),
                (1, BitWord::new(99, 32)),
                (2, BitWord::new(0x100, 32)),
            ]),
            memory: HashMap::from([((0x100, 8), BitWord::new(0x11, 8))]),
        };

        let next_state = ctx.execute_test(&sequence(&isa, "0001", "GENERATED"), &state);

        assert_eq!(next_state.registers.get(&0), Some(&BitWord::new(7, 32)));
        assert_eq!(next_state.registers.get(&1), Some(&BitWord::new(12, 32)));
        assert_eq!(
            next_state.memory.get(&(0x100, 8)),
            Some(&BitWord::new(0xab, 8))
        );
        assert_eq!(state.registers.get(&1), Some(&BitWord::new(99, 32)));
    }

    #[test]
    fn execute_test_skips_effects_when_guard_is_false() {
        let guard = read_register(fixed_reg(3), 1);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "0000", vec![]),
                encoded_instruction(
                    "GUARDED",
                    "0001",
                    vec![
                        Effect::write_register_if(guard.clone(), fixed_reg(1), constant(0x55, 32)),
                        Effect::write_memory_if(guard, read_reg(2), constant(0xaa, 8), 8),
                    ],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );
        let state = MachineState {
            registers: HashMap::from([
                (1, BitWord::new(0x12, 32)),
                (2, BitWord::new(0x100, 32)),
                (3, BitWord::new(0, 1)),
            ]),
            memory: HashMap::from([((0x100, 8), BitWord::new(0x34, 8))]),
        };

        let next_state = ctx.execute_test(&sequence(&isa, "0001", "GUARDED"), &state);

        assert_eq!(next_state, state);
    }

    #[test]
    fn passes_test_accepts_equivalent_execution_results() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "0000",
                    vec![Effect::write_register(
                        fixed_reg(1),
                        add(read_reg(0), constant(5, 32)),
                    )],
                ),
                encoded_instruction(
                    "GENERATED",
                    "0001",
                    vec![Effect::write_register(
                        fixed_reg(1),
                        add(constant(5, 32), read_reg(0)),
                    )],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );
        let state = MachineState {
            registers: HashMap::from([(0, BitWord::new(7, 32))]),
            memory: HashMap::new(),
        };

        assert!(ctx.passes_test(&sequence(&isa, "0001", "GENERATED"), &state));
    }

    #[test]
    fn passes_test_rejects_different_required_register_result() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "0000",
                    vec![Effect::write_register(fixed_reg(1), constant(1, 32))],
                ),
                encoded_instruction(
                    "GENERATED",
                    "0001",
                    vec![Effect::write_register(fixed_reg(1), constant(2, 32))],
                ),
            ],
        );
        let ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );
        let state = MachineState::default();

        assert!(!ctx.passes_test(&sequence(&isa, "0001", "GENERATED"), &state));
    }

    #[test]
    fn passes_test_ignores_unprotected_scratch_register_but_rejects_protected_one() {
        let protected_register = arch_register(2);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "0000",
                    vec![Effect::write_register(fixed_reg(1), constant(1, 32))],
                ),
                encoded_instruction(
                    "GENERATED",
                    "0001",
                    vec![
                        Effect::write_register(fixed_reg(1), constant(1, 32)),
                        Effect::write_register(fixed_reg(2), constant(2, 32)),
                    ],
                ),
            ],
        );
        let unprotected_ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![],
        );
        let protected_ctx = SuperoptimizationCtx::new_from_single_instruction(
            decode_one(&isa, "0000", "ORIGINAL"),
            HashMap::new(),
            &isa,
            vec![protected_register],
        );
        let state = MachineState::default();
        let generated = sequence(&isa, "0001", "GENERATED");

        assert!(unprotected_ctx.passes_test(&generated, &state));
        assert!(!protected_ctx.passes_test(&generated, &state));
    }

    #[test]
    fn accepts_fixed_register_writes_and_original_memory_destinations() {
        let original_address = read_reg(0);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "00000000",
                    vec![Effect::write_memory(
                        original_address.clone(),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
                encoded_instruction(
                    "GENERATED",
                    "00000001",
                    vec![
                        Effect::write_register(fixed_reg(1), constant(0x12, 32)),
                        Effect::write_memory(original_address, constant(0xbb, 8), 8),
                    ],
                ),
            ],
        );

        assert!(generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "GENERATED"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
    }

    #[test]
    fn rejects_generated_sequences_missing_original_effect_destinations() {
        let original_address = read_reg(0);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "00000000",
                    vec![
                        Effect::write_register(fixed_reg(1), constant(0x12, 32)),
                        Effect::write_memory(original_address.clone(), constant(0xaa, 8), 8),
                    ],
                ),
                encoded_instruction(
                    "ONLY_REGISTER",
                    "00000001",
                    vec![Effect::write_register(fixed_reg(1), constant(0x34, 32))],
                ),
                encoded_instruction(
                    "ONLY_MEMORY",
                    "00000010",
                    vec![Effect::write_memory(
                        original_address.clone(),
                        constant(0xbb, 8),
                        8,
                    )],
                ),
                encoded_instruction(
                    "ONLY_STACK_SCRATCH",
                    "00000011",
                    vec![Effect::write_memory(
                        sub(sp_value(), constant(4, 32)),
                        constant(0xcc, 8),
                        8,
                    )],
                ),
            ],
        );

        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "ONLY_REGISTER"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000010", "ONLY_MEMORY"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000011", "ONLY_STACK_SCRATCH"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
    }

    #[test]
    fn rejects_nonconstant_register_destinations_and_stack_pointer_writes() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "00000000", vec![]),
                encoded_instruction(
                    "NONCONST_REG_DEST",
                    "00000001",
                    vec![Effect::write_register(read_reg(0), constant(0x12, 32))],
                ),
                encoded_instruction(
                    "SP_WRITE",
                    "00000010",
                    vec![Effect::write_register(fixed_reg(SP_ID), constant(0x12, 32))],
                ),
            ],
        );

        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "NONCONST_REG_DEST"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000010", "SP_WRITE"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
    }

    #[test]
    fn accepts_only_downward_sp_relative_stack_scratch_for_downward_stacks() {
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "00000000", vec![]),
                encoded_instruction(
                    "STACK_DOWN",
                    "00000001",
                    vec![Effect::write_memory(
                        sub(sp_value(), constant(4, 32)),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
                encoded_instruction(
                    "STACK_UP",
                    "00000010",
                    vec![Effect::write_memory(
                        add(sp_value(), constant(4, 32)),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
                encoded_instruction(
                    "STACK_TOO_FAR",
                    "00000011",
                    vec![Effect::write_memory(
                        sub(sp_value(), constant(17, 32)),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
                encoded_instruction(
                    "ARBITRARY_MEMORY",
                    "00000100",
                    vec![Effect::write_memory(read_reg(0), constant(0xaa, 8), 8)],
                ),
            ],
        );

        assert!(generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "STACK_DOWN"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000010", "STACK_UP"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000011", "STACK_TOO_FAR"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000100", "ARBITRARY_MEMORY"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
    }

    #[test]
    fn accepts_only_upward_sp_relative_stack_scratch_for_upward_stacks() {
        let isa = test_isa(
            StackDirection::Upwards,
            vec![
                encoded_instruction("ORIGINAL", "00000000", vec![]),
                encoded_instruction(
                    "STACK_UP",
                    "00000001",
                    vec![Effect::write_memory(
                        add(sp_value(), constant(4, 32)),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
                encoded_instruction(
                    "STACK_DOWN",
                    "00000010",
                    vec![Effect::write_memory(
                        sub(sp_value(), constant(4, 32)),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
            ],
        );

        assert!(generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "STACK_UP"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000010", "STACK_DOWN"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[],
            &isa
        ));
    }

    #[test]
    fn rejects_generated_writes_to_protected_registers() {
        let protected_register = arch_register(1);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "00000000", vec![]),
                encoded_instruction(
                    "WRITE_UNPROTECTED_R0",
                    "00000001",
                    vec![Effect::write_register(fixed_reg(0), constant(0x12, 32))],
                ),
                encoded_instruction(
                    "WRITE_PROTECTED_R1",
                    "00000010",
                    vec![Effect::write_register(fixed_reg(1), constant(0x34, 32))],
                ),
            ],
        );

        assert!(generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "WRITE_UNPROTECTED_R0"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[protected_register],
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000010", "WRITE_PROTECTED_R1"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[protected_register],
            &isa
        ));
    }

    #[test]
    fn allows_original_destination_even_when_register_is_protected() {
        let protected_register = arch_register(1);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction(
                    "ORIGINAL",
                    "00000000",
                    vec![Effect::write_register(fixed_reg(1), constant(0x12, 32))],
                ),
                encoded_instruction(
                    "GENERATED",
                    "00000001",
                    vec![Effect::write_register(fixed_reg(1), constant(0x34, 32))],
                ),
            ],
        );

        assert!(generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "GENERATED"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[protected_register],
            &isa
        ));
    }

    #[test]
    fn protected_registers_do_not_make_arbitrary_memory_writes_valid() {
        let protected_register = arch_register(1);
        let isa = test_isa(
            StackDirection::Downwards,
            vec![
                encoded_instruction("ORIGINAL", "00000000", vec![]),
                encoded_instruction(
                    "ARBITRARY_MEMORY",
                    "00000001",
                    vec![Effect::write_memory(read_reg(0), constant(0xaa, 8), 8)],
                ),
            ],
        );

        assert!(!generated_sequence_meets_state_constraints(
            &sequence(&isa, "00000001", "ARBITRARY_MEMORY"),
            &sequence(&isa, "00000000", "ORIGINAL"),
            &[protected_register],
            &isa
        ));
    }
}
