// Contains code to evaluate whether two Exprs are semantically equivalent
// Pipeline
//  1. Simple check to see if canonical form of Exprs are equal (if this succeeds great!)
//  2. Random testing to attempt to see if the Exprs are obviously different
//  3. Z3 (easier to program) or Bitwuzla (potentially faster) SMT solver to authoritatively check if the two Exprs are equivalent

// potential constraint for synthesis: never read from a register or memory address unless
//      1. the original instruction read from it (eg if ReadMemory(R4 + 4) is present, you can read from there)
//      2. the new program has already written to it

const LEFT_EXPR: bool = true;
const RIGHT_EXPR: bool = false;

use std::{
    collections::{HashMap, HashSet},
    ops::{BitAnd, BitOr, BitXor},
    time::{Duration, Instant},
};

use oxidd::{
    BooleanFunction, BooleanFunctionQuant, Manager, ManagerRef,
    bcdd::{BCDDFunction, BCDDManagerRef},
    util::{AllocResult, OptBool},
};
use z3::{
    Config as Z3Config, Model as Z3Model, SatResult, Solver, Sort,
    ast::{Array as Z3Array, BV, Bool},
    with_z3_config,
};

use crate::{
    constants::*,
    instruction_semantics::{
        Effect, Expr, OperandRef, RegisterRef, add, concat, constant, extract, or_expr,
        read_memory, read_register, select,
    },
    isa_specification::{
        ArchitecturalRegister, DecodedInstruction, ISA, StackDirection, StackPointer,
    },
    superoptimization::Program,
};

pub type InstructionIdx = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EffectExprRole {
    Guard,
    Destination,
    Value,
}

#[derive(Clone, Debug, Default)]
pub struct InstructionSeqToEffectsProfile {
    pub total: Duration,
    pub instruction_lookup: Duration,
    pub lowering_total: Duration,
    pub collapse: Duration,
    pub lower_memory_reads: Duration,
    pub substitute: Duration,
    pub canonicalize: Duration,
    pub combine_total: Duration,

    pub instructions: usize,
    pub source_effects: usize,
    pub source_register_effects: usize,
    pub source_memory_effects: usize,
    pub lowered_effects: usize,
    pub lowered_register_effects: usize,
    pub lowered_memory_effects: usize,
    pub combine_attempts: usize,
    pub combine_matches: usize,
    pub max_accumulated_effects: usize,
    pub final_effects: usize,
    pub source_expr_nodes: usize,
    pub lowered_expr_nodes: usize,
}

/// A table of all state uses
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateUseTable {
    /// Vector of tuples, saying which index the update is at and
    updates: Vec<(InstructionIdx, StateUse)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateUse {
    Write(StateDestination),
    Read(StateDestination),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateDestination {
    /// Register with identifier - `u8`
    Register(u8),
    /// Memory byte at address - `usize`
    MemoryByte(u32),
}

#[derive(Clone, PartialEq, Eq)]
pub struct MemoryRead {
    read_id: ReadId,
    /// If a memory read is used as the address or destination for another memory read,
    /// then it has a depth of 1. If it is a top level memory read it has a depth of 0. etc.
    depth: u8,
    address_expr: Expr,
    lowered_address: Option<BddWord>,
    width: u16,
    value: BddWord,
    value_variables: BddWord,
}

type ReadId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VariableDescription {
    Unallocated,
    RegisterBit {
        register: ArchitecturalRegister,
        bit: usize,
    },
    MemoryReadValueBit {
        read_id: ReadId,
        left: bool,
        bit: usize,
    },
}

/// Checks the equivalence between two instruction sequences
pub struct EquivalenceManager<'a> {
    left_effects: Vec<Effect>,
    right_effects: Vec<Effect>,

    /// BddManager for each `Effect` of `left` (parallel array)
    effect_managers: Vec<BddManager>,

    isa: &'a ISA,
}

impl<'a> EquivalenceManager<'a> {
    pub fn from_instructions(left: &Program, right: &Program, isa: &'a ISA) -> Self {
        let left_effects = Self::canonical_effects(instruction_seq_to_effects(left, isa));
        let right_effects = Self::canonical_effects(instruction_seq_to_effects(right, isa));

        let mut effect_managers = vec![];
        for effect in &left_effects {
            let (left_expr, left_ident, is_memory) = Self::effect_comparison_parts(effect);

            // Now, iterate to find the right value expr, which should be guaranteed to
            //  1. exist
            //  2. syntactically match the left expr
            // by generated_sequence_meets_state_constraints()/generated_effects_meet_state_constraints()
            if let Some(right_expr) =
                Self::matching_effect_value(&right_effects, &left_ident, is_memory)
            {
                effect_managers.push(BddManager::from_exprs(left_expr, right_expr, isa));
            } else {
                panic!(
                    "Right instruction sequence is missing effect writing to {:?} present in left instruction sequence",
                    left_ident
                );
            }
        }
        EquivalenceManager {
            left_effects,
            right_effects,
            effect_managers,
            isa,
        }
    }

    pub fn from_left_instruction(left: &Program, isa: &'a ISA) -> Self {
        Self::from_instructions(left, left, isa)
    }

    pub fn replace_right_instruction(&mut self, new_right: &Program) {
        let right_effects = instruction_seq_to_effects(new_right, self.isa);
        self.replace_right_effects(&right_effects);
    }

    pub fn replace_right_effects(&mut self, new_right_effects: &[Effect]) {
        self.right_effects = Self::canonical_effects(new_right_effects.to_vec());
        for (idx, effect) in self.left_effects.iter().enumerate() {
            let (left_ident, is_memory) = Self::effect_ident(effect);

            // Now iterate through the right effects to find the corresponding effect
            if let Some(right_expr) =
                Self::matching_effect_value(&self.right_effects, &left_ident, is_memory)
            {
                self.effect_managers[idx].replace_right_expr(right_expr);
            } else {
                panic!(
                    "Right instruction sequence is missing effect writing to {:?} present in left instruction sequence",
                    left_ident
                );
            }
        }
    }

    pub fn compare_instructions(&mut self) -> AllocResult<BddEquality> {
        for effect_manager in self.effect_managers.iter_mut() {
            let result = effect_manager.compare()?;
            match result {
                BddEquality::Equal => continue,
                // eagerly return on failure
                BddEquality::Unequal(..) => return Ok(result),
            }
        }
        Ok(BddEquality::Equal)
    }

    fn canonical_effects(effects: Vec<Effect>) -> Vec<Effect> {
        effects.into_iter().map(Effect::canonicalize).collect()
    }

    fn effect_comparison_parts(effect: &Effect) -> (Expr, Expr, bool) {
        match effect {
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                assert_eq!(*width, 8, "Memory writes should be lowered to 1 byte");
                (
                    Self::guarded_value_or_current_memory(
                        guard.clone(),
                        address.clone(),
                        value.clone(),
                        *width,
                    ),
                    address.clone(),
                    true,
                )
            }
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                let width = value.expr_width().expect("Effect value must have width!");
                (
                    Self::guarded_value_or_current_register(
                        guard.clone(),
                        register.clone(),
                        value.clone(),
                        width,
                    ),
                    register.clone(),
                    false,
                )
            }
        }
    }

    fn effect_ident(effect: &Effect) -> (Expr, bool) {
        match effect {
            Effect::WriteMemory { address, .. } => (address.clone(), true),
            Effect::WriteRegister { register, .. } => (register.clone(), false),
        }
    }

    fn matching_effect_value(effects: &[Effect], ident: &Expr, is_memory: bool) -> Option<Expr> {
        effects.iter().find_map(|effect| match effect {
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } if is_memory && address == ident => {
                assert_eq!(*width, 8, "Memory writes should be lowered to 1 byte");
                Some(Self::guarded_value_or_current_memory(
                    guard.clone(),
                    address.clone(),
                    value.clone(),
                    *width,
                ))
            }
            Effect::WriteRegister {
                guard,
                register,
                value,
            } if !is_memory && register == ident => {
                let width = value.expr_width().expect("Effect value must have width!");
                Some(Self::guarded_value_or_current_register(
                    guard.clone(),
                    register.clone(),
                    value.clone(),
                    width,
                ))
            }
            _ => None,
        })
    }

    fn guarded_value_or_current_memory(
        guard: Expr,
        address: Expr,
        value: Expr,
        width: u16,
    ) -> Expr {
        select(guard, value, read_memory(address, width)).canonicalize()
    }

    fn guarded_value_or_current_register(
        guard: Expr,
        register: Expr,
        value: Expr,
        width: u16,
    ) -> Expr {
        select(guard, value, read_register(register, width)).canonicalize()
    }
}

/// Z3-backed equivalence checker for decoded instruction sequences.
///
/// The BDD checker compares collapsed final effects. This checker symbolically
/// executes each instruction in order, keeping register files and memory as Z3
/// arrays, then asks whether any original/left write destination can differ in
/// the final state.
pub struct Z3EquivalenceManager<'a> {
    left: Program,
    right: Program,
    isa: &'a ISA,
    live_out_registers: Vec<ArchitecturalRegister>,
    timeout: Option<Duration>,
}

impl<'a> Z3EquivalenceManager<'a> {
    pub fn from_instructions(left: &Program, right: &Program, isa: &'a ISA) -> Self {
        Self::from_instructions_with_live_out_registers(
            left,
            right,
            isa,
            Self::left_register_destinations(left, isa),
        )
    }

    pub fn from_instructions_with_live_out_registers(
        left: &Program,
        right: &Program,
        isa: &'a ISA,
        live_out_registers: Vec<ArchitecturalRegister>,
    ) -> Self {
        Self {
            left: left.clone(),
            right: right.clone(),
            isa,
            live_out_registers,
            timeout: Some(Duration::from_millis(5_000)),
        }
    }

    pub fn from_left_instruction(left: &Program, isa: &'a ISA) -> Self {
        Self::from_instructions(left, left, isa)
    }

    pub fn from_left_instruction_with_live_out_registers(
        left: &Program,
        isa: &'a ISA,
        live_out_registers: Vec<ArchitecturalRegister>,
    ) -> Self {
        Self::from_instructions_with_live_out_registers(left, left, isa, live_out_registers)
    }

    pub fn replace_right_instruction(&mut self, new_right: &Program) {
        self.right = new_right.clone();
    }

    pub fn replace_right_effects(&mut self, new_right_effects: &[Effect]) {
        let _ = new_right_effects;
        panic!("Z3EquivalenceManager executes Programs directly; use replace_right_instruction")
    }

    pub fn compare_instructions(&mut self) -> BddEquality {
        let mut cfg = Z3Config::new();
        if let Some(timeout) = self.timeout {
            cfg.set_timeout_msec(timeout.as_millis().try_into().unwrap_or(u64::MAX));
        }

        with_z3_config(&cfg, || {
            let initial = Z3State::new();
            let (left_final, mut observations) =
                self.execute_program_observing(&initial, &self.left, Z3ObservationSide::Left);
            let (right_final, right_observations) =
                self.execute_program_observing(&initial, &self.right, Z3ObservationSide::Right);
            observations.extend(right_observations);
            observations.extend(self.live_out_register_observations());
            let solver = Solver::new();

            let differences =
                self.destination_differences(&observations, &left_final, &right_final);
            if differences.is_empty() {
                return BddEquality::Equal;
            }

            let difference_refs = differences.iter().collect::<Vec<_>>();
            solver.assert(&Bool::or(&difference_refs));

            match solver.check() {
                SatResult::Unsat => BddEquality::Equal,
                SatResult::Sat => {
                    let model = solver
                        .get_model()
                        .expect("SAT result should provide a Z3 model");
                    BddEquality::Unequal(self.model_to_machine_state(&model, &initial))
                }
                SatResult::Unknown => {
                    panic!("Z3 equivalence query returned unknown")
                }
            }
        })
    }

    fn destination_differences(
        &self,
        observations: &[Z3Observation],
        left_final: &Z3State,
        right_final: &Z3State,
    ) -> Vec<Bool> {
        observations
            .iter()
            .map(|observation| match observation {
                Z3Observation::Register { selector, width } => {
                    let left_value = left_final.read_register(selector, *width);
                    let right_value = right_final.read_register(selector, *width);
                    left_value.ne(&right_value)
                }
                Z3Observation::Memory { address, width } => {
                    let left_value = left_final.read_memory(address, *width);
                    let right_value = right_final.read_memory(address, *width);
                    left_value.ne(&right_value)
                }
            })
            .collect()
    }

    fn execute_program_observing(
        &self,
        initial: &Z3State,
        program: &Program,
        side: Z3ObservationSide,
    ) -> (Z3State, Vec<Z3Observation>) {
        let mut state = initial.clone();
        let mut observations = Vec::new();

        for instruction in program.iter_instructions() {
            let before = state.clone();
            let mut after = state.clone();

            for effect in instruction_effects(instruction, self.isa).iter().cloned() {
                let effect = collapse_effect(effect, instruction);
                if self.effect_destination_is_observable(&effect, side) {
                    observations.push(Z3State::observe_effect_destination(&effect, &before));
                }
                after.apply_collapsed_effect(&effect, &before);
            }

            state = after;
        }

        (state, observations)
    }

    fn effect_destination_is_observable(&self, effect: &Effect, side: Z3ObservationSide) -> bool {
        match effect {
            Effect::WriteRegister { .. } => false,
            Effect::WriteMemory { address, .. } => {
                side == Z3ObservationSide::Left
                    || !is_allowed_stack_scratch_address(address, self.isa)
            }
        }
    }

    fn live_out_register_observations(&self) -> Vec<Z3Observation> {
        self.live_out_registers
            .iter()
            .map(|register| Z3Observation::Register {
                selector: bv_const(
                    register.identifier as u128,
                    register.identifier_width.into(),
                ),
                width: register.width.into(),
            })
            .collect()
    }

    fn left_register_destinations(left: &Program, isa: &ISA) -> Vec<ArchitecturalRegister> {
        let mut live_out_registers = Vec::new();
        let mut seen = HashSet::new();
        for instruction in left.iter_instructions() {
            for effect in instruction_effects(instruction, isa).iter().cloned() {
                let Effect::WriteRegister {
                    register, value, ..
                } = collapse_effect(effect, instruction)
                else {
                    continue;
                };
                let Some(identifier) = register_destination(&register) else {
                    continue;
                };
                if !seen.insert(identifier) {
                    continue;
                }
                live_out_registers.push(ArchitecturalRegister {
                    identifier: identifier
                        .try_into()
                        .expect("architectural register identifiers should fit in u8"),
                    identifier_width: register
                        .expr_width()
                        .expect("register selector should have width")
                        .try_into()
                        .expect("register identifier width should fit in u8"),
                    width: value
                        .expr_width()
                        .expect("register write value should have width")
                        .try_into()
                        .expect("register value width should fit in u8"),
                });
            }
        }
        live_out_registers
    }

    fn model_to_machine_state(&self, model: &Z3Model, initial: &Z3State) -> MachineState {
        let mut state = MachineState::default();

        for register in &self.isa.registers {
            let selector = bv_const(
                register.identifier as u128,
                register.identifier_width.into(),
            );
            let value = initial.read_register(&selector, register.width.into());
            if let Some(value) = eval_model_bv(model, &value) {
                state.registers.insert(register.identifier as u128, value);
            }
        }

        self.add_program_state_points(&mut state, model, initial, &self.left);
        self.add_program_state_points(&mut state, model, initial, &self.right);

        state
    }

    fn add_program_state_points(
        &self,
        state: &mut MachineState,
        model: &Z3Model,
        initial: &Z3State,
        program: &Program,
    ) {
        let mut symbolic_state = initial.clone();
        for instruction in program.iter_instructions() {
            let before = symbolic_state.clone();
            let mut after = symbolic_state.clone();
            for effect in instruction_effects(instruction, self.isa).iter().cloned() {
                let effect = collapse_effect(effect, instruction);
                self.add_effect_state_points(state, model, initial, &before, &effect);
                after.apply_collapsed_effect(&effect, &before);
            }
            symbolic_state = after;
        }
    }

    fn add_effect_state_points(
        &self,
        state: &mut MachineState,
        model: &Z3Model,
        initial: &Z3State,
        context: &Z3State,
        effect: &Effect,
    ) {
        match effect {
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                self.add_expr_state_points(state, model, initial, context, guard);
                self.add_expr_state_points(state, model, initial, context, register);
                self.add_expr_state_points(state, model, initial, context, value);
                self.add_register_point(
                    state,
                    model,
                    initial,
                    context,
                    register,
                    value.expr_width(),
                );
            }
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                self.add_expr_state_points(state, model, initial, context, guard);
                self.add_expr_state_points(state, model, initial, context, address);
                self.add_expr_state_points(state, model, initial, context, value);
                self.add_memory_point(state, model, initial, context, address, *width);
            }
        }
    }

    fn add_expr_state_points(
        &self,
        state: &mut MachineState,
        model: &Z3Model,
        initial: &Z3State,
        context: &Z3State,
        expr: &Expr,
    ) {
        match expr {
            Expr::ReadRegister { register, width } => {
                self.add_expr_state_points(state, model, initial, context, register);
                self.add_register_point(state, model, initial, context, register, Some(*width));
            }
            Expr::ReadMemory { address, width } => {
                self.add_expr_state_points(state, model, initial, context, address);
                self.add_memory_point(state, model, initial, context, address, *width);
            }
            Expr::Const { .. } | Expr::Operand(_) | Expr::DerivedValue(_) => {}
            Expr::Add(lhs, rhs)
            | Expr::Sub(lhs, rhs)
            | Expr::Mul(lhs, rhs)
            | Expr::And(lhs, rhs)
            | Expr::Or(lhs, rhs)
            | Expr::Xor(lhs, rhs)
            | Expr::ShiftLeft(lhs, rhs)
            | Expr::LogicalShiftRight(lhs, rhs)
            | Expr::ArithmeticShiftRight(lhs, rhs)
            | Expr::RotateRight(lhs, rhs)
            | Expr::Equal(lhs, rhs)
            | Expr::UnsignedLessThan(lhs, rhs)
            | Expr::SignedLessThan(lhs, rhs) => {
                self.add_expr_state_points(state, model, initial, context, lhs);
                self.add_expr_state_points(state, model, initial, context, rhs);
            }
            Expr::Not(value)
            | Expr::CountOnes(value)
            | Expr::Extract { value, .. }
            | Expr::ZeroExtend { value, .. }
            | Expr::SignExtend { value, .. } => {
                self.add_expr_state_points(state, model, initial, context, value);
            }
            Expr::Concat(values) => {
                for value in values {
                    self.add_expr_state_points(state, model, initial, context, value);
                }
            }
            Expr::AddCarryOut {
                lhs, rhs, carry_in, ..
            }
            | Expr::AddOverflow {
                lhs, rhs, carry_in, ..
            }
            | Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in: carry_in,
                ..
            }
            | Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in: carry_in,
                ..
            } => {
                self.add_expr_state_points(state, model, initial, context, lhs);
                self.add_expr_state_points(state, model, initial, context, rhs);
                self.add_expr_state_points(state, model, initial, context, carry_in);
            }
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                self.add_expr_state_points(state, model, initial, context, condition);
                self.add_expr_state_points(state, model, initial, context, when_true);
                self.add_expr_state_points(state, model, initial, context, when_false);
            }
        }
    }

    fn add_register_point(
        &self,
        state: &mut MachineState,
        model: &Z3Model,
        initial: &Z3State,
        context: &Z3State,
        register: &Expr,
        value_width: Option<u16>,
    ) {
        let Some(width) = value_width else {
            return;
        };
        let selector = Z3State::lower_expr(register, context);
        let Some(selector_value) = eval_model_bv(model, &selector) else {
            return;
        };
        let value = initial.read_register(&selector, width);
        if let Some(value) = eval_model_bv(model, &value) {
            state.registers.insert(selector_value.value, value);
        }
    }

    fn add_memory_point(
        &self,
        state: &mut MachineState,
        model: &Z3Model,
        initial: &Z3State,
        context: &Z3State,
        address: &Expr,
        width: u16,
    ) {
        let address = Z3State::lower_expr(address, context);

        assert_eq!(width % 8, 0, "Memory width must be byte-aligned");
        for byte_index in 0..(width / 8) {
            let byte_address = bv_add_const(&address, byte_index as u128);
            let byte_value = initial.read_memory(&byte_address, 8);
            if let (Some(byte_address), Some(byte_value)) = (
                eval_model_bv(model, &byte_address),
                eval_model_bv(model, &byte_value),
            ) {
                state
                    .memory
                    .insert((byte_address.value, 8), BitWord::new(byte_value.value, 8));
            }
        }
    }
}

#[derive(Clone)]
struct Z3State {
    registers: HashMap<(u16, u16), Z3Array>,
    memory: HashMap<u16, Z3Array>,
}

enum Z3Observation {
    Register { selector: BV, width: u16 },
    Memory { address: BV, width: u16 },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Z3ObservationSide {
    Left,
    Right,
}

impl Z3State {
    fn new() -> Self {
        Self {
            registers: HashMap::new(),
            memory: HashMap::new(),
        }
    }

    fn observe_effect_destination(effect: &Effect, before: &Self) -> Z3Observation {
        match effect {
            Effect::WriteRegister {
                register, value, ..
            } => Z3Observation::Register {
                selector: Self::lower_expr(register, before),
                width: value
                    .expr_width()
                    .expect("Register write value needs width"),
            },
            Effect::WriteMemory { address, width, .. } => Z3Observation::Memory {
                address: Self::lower_expr(address, before),
                width: *width,
            },
        }
    }

    fn apply_collapsed_effect(&mut self, effect: &Effect, before: &Self) {
        match effect {
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                let guard = Self::lower_guard(guard, before);
                let register = Self::lower_expr(register, before);
                let value = Self::lower_expr(value, before);
                let key = (register.get_size() as u16, value.get_size() as u16);
                let old_file = self.register_file(key.0, key.1);
                let written_file = old_file.store(&register, &value);
                let next_file = guard.ite(&written_file, &old_file);
                self.registers.insert(key, next_file);
            }
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                let guard = Self::lower_guard(guard, before);
                let address = Self::lower_expr(address, before);
                let value = Self::lower_expr(value, before);
                let address_width = address.get_size() as u16;
                let old_memory = self.memory_array(address_width);
                let written_memory =
                    self.write_memory_unconditional(&old_memory, &address, &value, *width);
                let next_memory = guard.ite(&written_memory, &old_memory);
                self.memory.insert(address_width, next_memory);
            }
        }
    }

    fn lower_expr(expr: &Expr, state: &Self) -> BV {
        match expr {
            Expr::Const { value, width } => bv_const(*value, *width),
            Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
                register,
                identifier_width,
            })) => bv_const(register.0 as u128, *identifier_width),
            Expr::Operand(_) | Expr::DerivedValue(_) => {
                unreachable!("Z3 lowering expects collapsed effects, got {expr:?}")
            }
            Expr::ReadRegister { register, width } => {
                let register = Self::lower_expr(register, state);
                state.read_register(&register, *width)
            }
            Expr::ReadMemory { address, width } => {
                let address = Self::lower_expr(address, state);
                state.read_memory(&address, *width)
            }
            Expr::Add(lhs, rhs) => {
                Self::lower_expr(lhs, state).bvadd(&Self::lower_expr(rhs, state))
            }
            Expr::Sub(lhs, rhs) => {
                Self::lower_expr(lhs, state).bvsub(&Self::lower_expr(rhs, state))
            }
            Expr::Mul(lhs, rhs) => {
                Self::lower_expr(lhs, state).bvmul(&Self::lower_expr(rhs, state))
            }
            Expr::And(lhs, rhs) => {
                Self::lower_expr(lhs, state).bvand(&Self::lower_expr(rhs, state))
            }
            Expr::Or(lhs, rhs) => Self::lower_expr(lhs, state).bvor(&Self::lower_expr(rhs, state)),
            Expr::Xor(lhs, rhs) => {
                Self::lower_expr(lhs, state).bvxor(&Self::lower_expr(rhs, state))
            }
            Expr::Not(value) => Self::lower_expr(value, state).bvnot(),
            Expr::ShiftLeft(value, amount) => {
                Self::lower_expr(value, state).bvshl(&Self::lower_expr(amount, state))
            }
            Expr::LogicalShiftRight(value, amount) => {
                Self::lower_expr(value, state).bvlshr(&Self::lower_expr(amount, state))
            }
            Expr::ArithmeticShiftRight(value, amount) => {
                Self::lower_expr(value, state).bvashr(&Self::lower_expr(amount, state))
            }
            Expr::RotateRight(value, amount) => {
                Self::lower_expr(value, state).bvrotr(&Self::lower_expr(amount, state))
            }
            Expr::Equal(lhs, rhs) => {
                bool_to_bv(&Self::lower_expr(lhs, state).eq(&Self::lower_expr(rhs, state)))
            }
            Expr::UnsignedLessThan(lhs, rhs) => {
                bool_to_bv(&Self::lower_expr(lhs, state).bvult(&Self::lower_expr(rhs, state)))
            }
            Expr::SignedLessThan(lhs, rhs) => {
                bool_to_bv(&Self::lower_expr(lhs, state).bvslt(&Self::lower_expr(rhs, state)))
            }
            Expr::Extract { value, high, low } => {
                Self::lower_expr(value, state).extract((*high).into(), (*low).into())
            }
            Expr::Concat(values) => {
                let mut values = values.iter().map(|value| Self::lower_expr(value, state));
                let first = values
                    .next()
                    .expect("Concat must contain at least one value");
                values.fold(first, |acc, value| acc.concat(&value))
            }
            Expr::ZeroExtend { value, to_width } => {
                let value = Self::lower_expr(value, state);
                value.zero_ext(u32::from(*to_width) - value.get_size())
            }
            Expr::SignExtend { value, to_width } => {
                let value = Self::lower_expr(value, state);
                value.sign_ext(u32::from(*to_width) - value.get_size())
            }
            Expr::CountOnes(value) => {
                let value = Self::lower_expr(value, state);
                let width = value.get_size();
                (0..width).fold(BV::from_u64(0, width), |sum, bit| {
                    let bit_value = value.extract(bit, bit).zero_ext(width - 1);
                    sum.bvadd(&bit_value)
                })
            }
            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs = Self::lower_expr(lhs, state).zero_ext(1);
                let rhs = Self::lower_expr(rhs, state).zero_ext(1);
                let carry_in = Self::lower_expr(carry_in, state).zero_ext(u32::from(*width));
                let sum = lhs.bvadd(&rhs).bvadd(&carry_in);
                sum.extract(u32::from(*width), u32::from(*width))
            }
            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs = Self::lower_expr(lhs, state);
                let rhs = Self::lower_expr(rhs, state);
                let carry_in = Self::lower_expr(carry_in, state).zero_ext(u32::from(*width) - 1);
                let result = lhs.bvadd(&rhs).bvadd(&carry_in);
                signed_add_overflow(&lhs, &rhs, &result, *width)
            }
            Expr::SubCarryOut {
                lhs,
                rhs,
                borrow_in,
                width,
            } => {
                let lhs = Self::lower_expr(lhs, state).zero_ext(1);
                let rhs = Self::lower_expr(rhs, state).zero_ext(1);
                let borrow_in = Self::lower_expr(borrow_in, state).zero_ext(u32::from(*width));
                bool_to_bv(&rhs.bvadd(&borrow_in).bvule(&lhs))
            }
            Expr::SubOverflow {
                lhs,
                rhs,
                borrow_in,
                width,
            } => {
                let lhs = Self::lower_expr(lhs, state);
                let rhs = Self::lower_expr(rhs, state);
                let borrow_in = Self::lower_expr(borrow_in, state).zero_ext(u32::from(*width) - 1);
                let result = lhs.bvsub(&rhs).bvsub(&borrow_in);
                signed_sub_overflow(&lhs, &rhs, &result, *width)
            }
            Expr::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition = Self::lower_guard(condition, state);
                let when_true = Self::lower_expr(when_true, state);
                let when_false = Self::lower_expr(when_false, state);
                condition.ite(&when_true, &when_false)
            }
        }
    }

    fn lower_guard(expr: &Expr, state: &Self) -> Bool {
        let value = Self::lower_expr(expr, state);
        assert_eq!(value.get_size(), 1, "Guard expressions must be 1 bit");
        value.eq(BV::from_u64(1, 1))
    }

    fn read_register(&self, selector: &BV, width: u16) -> BV {
        self.register_file(selector.get_size() as u16, width)
            .select(selector)
            .as_bv()
            .expect("Register file select should produce a bit-vector")
    }

    fn read_memory(&self, address: &BV, width: u16) -> BV {
        assert_eq!(width % 8, 0, "Memory read width must be byte-aligned");
        if width == 8 {
            return self
                .memory_array(address.get_size() as u16)
                .select(address)
                .as_bv()
                .expect("Memory select should produce an 8-bit bit-vector");
        }

        let bytes = (0..(width / 8)).rev().map(|byte_index| {
            let byte_address = bv_add_const(address, byte_index as u128);
            self.memory_array(address.get_size() as u16)
                .select(&byte_address)
                .as_bv()
                .expect("Memory select should produce an 8-bit bit-vector")
        });
        concat_bvs(bytes)
    }

    fn write_memory_unconditional(
        &self,
        memory: &Z3Array,
        address: &BV,
        value: &BV,
        width: u16,
    ) -> Z3Array {
        assert_eq!(width % 8, 0, "Memory write width must be byte-aligned");
        let value = if value.get_size() < u32::from(width) {
            value.zero_ext(u32::from(width) - value.get_size())
        } else {
            value.clone()
        };
        let mut written = memory.clone();
        for byte_index in 0..(width / 8) {
            let low = u32::from(byte_index * 8);
            let byte = value.extract(low + 7, low);
            let byte_address = bv_add_const(address, byte_index as u128);
            written = written.store(&byte_address, &byte);
        }
        written
    }

    fn register_file(&self, identifier_width: u16, value_width: u16) -> Z3Array {
        self.registers
            .get(&(identifier_width, value_width))
            .cloned()
            .unwrap_or_else(|| {
                Z3Array::new_const(
                    format!("initial_reg_{identifier_width}_{value_width}"),
                    &Sort::bitvector(identifier_width.into()),
                    &Sort::bitvector(value_width.into()),
                )
            })
    }

    fn memory_array(&self, address_width: u16) -> Z3Array {
        self.memory.get(&address_width).cloned().unwrap_or_else(|| {
            Z3Array::new_const(
                format!("initial_mem_{address_width}"),
                &Sort::bitvector(address_width.into()),
                &Sort::bitvector(8),
            )
        })
    }
}

fn bool_to_bv(value: &Bool) -> BV {
    value.ite(&BV::from_u64(1, 1), &BV::from_u64(0, 1))
}

fn bv_const(value: u128, width: u16) -> BV {
    let value = value & bit_mask(width);
    if let Ok(value) = u64::try_from(value) {
        BV::from_u64(value, width.into())
    } else {
        BV::from_str(width.into(), &value.to_string())
            .expect("u128 decimal literal should construct a Z3 bit-vector")
    }
}

fn bv_add_const(value: &BV, rhs: u128) -> BV {
    value.bvadd(&bv_const(rhs, value.get_size() as u16))
}

fn concat_bvs(values: impl IntoIterator<Item = BV>) -> BV {
    let mut values = values.into_iter();
    let first = values.next().expect("At least one bit-vector is required");
    values.fold(first, |acc, value| acc.concat(&value))
}

fn signed_add_overflow(lhs: &BV, rhs: &BV, result: &BV, width: u16) -> BV {
    let sign_bit = u32::from(width - 1);
    let lhs_sign = lhs.extract(sign_bit, sign_bit);
    let rhs_sign = rhs.extract(sign_bit, sign_bit);
    let result_sign = result.extract(sign_bit, sign_bit);
    let signs_same = lhs_sign.bvxor(&rhs_sign).eq(BV::from_u64(0, 1));
    let result_changed = lhs_sign.bvxor(&result_sign).eq(BV::from_u64(1, 1));
    bool_to_bv(&Bool::and(&[&signs_same, &result_changed]))
}

fn signed_sub_overflow(lhs: &BV, rhs: &BV, result: &BV, width: u16) -> BV {
    let sign_bit = u32::from(width - 1);
    let lhs_sign = lhs.extract(sign_bit, sign_bit);
    let rhs_sign = rhs.extract(sign_bit, sign_bit);
    let result_sign = result.extract(sign_bit, sign_bit);
    let signs_differ = lhs_sign.bvxor(&rhs_sign).eq(BV::from_u64(1, 1));
    let result_changed = lhs_sign.bvxor(&result_sign).eq(BV::from_u64(1, 1));
    bool_to_bv(&Bool::and(&[&signs_differ, &result_changed]))
}

fn eval_model_bv(model: &Z3Model, value: &BV) -> Option<BitWord> {
    let evaluated = model.eval(value, true)?;
    z3_bv_to_u128(&evaluated).map(|value| BitWord::new(value, evaluated.get_size() as u16))
}

fn z3_bv_to_u128(value: &BV) -> Option<u128> {
    if let Some(value) = value.as_u64() {
        return Some(value.into());
    }

    let text = value.to_string();
    if let Some(hex) = text.strip_prefix("#x") {
        return u128::from_str_radix(hex, 16).ok();
    }
    if let Some(binary) = text.strip_prefix("#b") {
        return u128::from_str_radix(binary, 2).ok();
    }
    text.parse().ok()
}

fn collapse_effect(effect: Effect, instruction: &DecodedInstruction) -> Effect {
    match effect {
        Effect::WriteRegister {
            guard,
            register,
            value,
        } => Effect::WriteRegister {
            guard: guard.collapse(instruction).canonicalize(),
            register: register.collapse(instruction).canonicalize(),
            value: value.collapse(instruction).canonicalize(),
        },
        Effect::WriteMemory {
            guard,
            address,
            value,
            width,
        } => Effect::WriteMemory {
            guard: guard.collapse(instruction).canonicalize(),
            address: address.collapse(instruction).canonicalize(),
            value: value.collapse(instruction).canonicalize(),
            width,
        },
    }
}

//NOTE: should probably put this in some other file
// this file should be exclusively for expr matching imo
// should probably also move the instruction to expr function
// or maybe move the bddmanager?
// impl StateUseTable {
//     pub fn from_program(program: &Vec<DecodedInstruction>, isa: &Vec<Instruction>) -> Self {
//         for instruction in program.iter() {
//             let lowered_effects = instruction_to_lowered_effects(instruction, isa, &vec![]);
//         }
//         StateUseTable { updates: () }
//     }
// }

// wait how on earth am i meant to handle the state uses? i completely forgot that branching was possible
// do i need to follow every branch?
// maybe just assume any register not written before the next branch isnt usable?

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BddEquality {
    Equal,
    /// A concrete state witnessing inequality.
    Unequal(MachineState),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BitWord {
    pub value: u128,
    pub width: u16,
}

impl BitWord {
    pub fn new(value: u128, width: u16) -> Self {
        assert!(
            width > 0 && width <= 128,
            "BitWord width must be in 1..=128"
        );
        Self {
            value: value & bit_mask(width),
            width,
        }
    }

    fn bool(value: bool) -> Self {
        Self::new(value as u128, 1)
    }

    pub fn population(&self) -> u32 {
        (self.value & bit_mask(self.width)).count_ones()
    }
}

impl BitXor for BitWord {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.width, rhs.width);
        Self {
            value: self.value ^ rhs.value,
            width: self.width,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineState {
    /// Register values keyed by the evaluated register identifier.
    ///
    /// For fixed registers this is the numeric register id; for symbolic
    /// register expressions it is the concrete identifier produced by a
    /// counterexample assignment.
    pub registers: HashMap<u128, BitWord>,
    /// Memory values keyed by `(byte_address, width_in_bits)`.
    ///
    /// The `u128` is the concrete byte address produced by evaluating a memory
    /// address expression. The `u16` is the access width, in bits, from the
    /// corresponding memory read or write. Width is part of the key because the
    /// evaluator looks up exactly the value requested by `ReadMemory`; when
    /// callers need byte-level aliasing, they should lower wider accesses first.
    pub memory: HashMap<(u128, u16), BitWord>,
}

impl MachineState {
    /// Compares two MachineStates and returns a cost representing their difference. Lower is
    /// closer.
    /// (inspired by Equations 8, 10, and 15 of Stochastic Superoptimization by Schkufza et al.)
    /// mem(s, s1) = sum(POP(val(s, m) xor val(s1, m)))
    ///     This equation sums the Hamming distance between each memory location, m
    /// reg(s, s1) = sum(min R(r, r')), R = POP(val(s, r) xor val(s1, r')) + w_m * {r != r'}
    ///     Described in section 4.6, this equation acts the same as the memory cost equation, but it
    ///     chooses the two closest registers between the machine states to compare, rewarding an
    ///     implementation for producing correct values in incorrect locations, before applying a
    ///     penalty, w_m whenever the register with the lowest difference is not the same as the
    ///     normal register.
    ///
    /// One difference from the paper is the behavior when there is a write in one MachineState but not the other.
    /// In that case, all bits are considered to be different, as well as an additional penalty,
    /// w_{extra write} being added. This gives the following final equation:
    ///
    /// compare(s, s1) = mem(s, s1) + reg(s, s1)
    ///     where
    ///         reg(s, s1) = sum(min R(r, r')), R = POP(val(s, r) xor val(s1, r')) + w_m * {r != r'}
    ///                      + sum(width(r) + w_{extra write} for one-sided included register writes r)
    ///         mem(s, s1) = sum(POP(val(s, m) xor val(s1, m)))
    ///                      + sum(width(m) + w_{extra write} for one-sided included memory writes m)
    /// To illustrate, if self writes to R0, and other writes to R1, but they write the same value,
    /// the cost reg(self, other) = w_m + 2 * (width(R0) + w_{extra write}).
    ///
    /// In the calculation of the cost, not all registers and memory locations are included in the cost
    ///     - Registers: only registers in live_out_registers.
    ///       Other registers are scratch, and have arbitrary values
    ///     - Memory: all memory locations other than those within the stack indicated by the
    ///       StackPointer, as well as those in self.memory.
    ///
    /// sp_val should be the value that the stack pointer had in the counterexample.
    pub fn compare(
        &self,
        other: &MachineState,
        live_out_registers: &[ArchitecturalRegister],
        sp: &StackPointer,
        sp_val: u128,
    ) -> u32 {
        self.compute_memory_cost(other, sp, sp_val)
            + self.compute_register_cost(other, live_out_registers)
    }

    fn compute_memory_cost(&self, other: &MachineState, sp: &StackPointer, sp_val: u128) -> u32 {
        let mut cost = 0;
        for (memory_location, value) in self.memory.iter() {
            let Some(other_value) = other.memory.get(&memory_location) else {
                // We handle this case (missing memory write) later
                continue;
            };

            // pop(value XOR other_value) represents the Hamming distance
            cost += (*value ^ *other_value).population();
        }

        // Now we need to look for locations which are written to by one MachineState but not the
        // other, in both directions.
        let keys_only_in_self: Vec<_> = self
            .memory
            .keys()
            .filter(|key| !other.memory.contains_key(*key))
            .collect();

        let keys_only_in_other: Vec<_> = other
            .memory
            .keys()
            .filter(|key| {
                !self.memory.contains_key(*key)
                    && !memory_location_is_stack_scratch(**key, sp, sp_val)
            })
            .collect();

        for (_, width) in keys_only_in_self.iter() {
            cost += *width as u32;
            cost += WEIGHT_EXTRA_WRITE;
        }

        for (_, width) in keys_only_in_other.iter() {
            cost += *width as u32;
            cost += WEIGHT_EXTRA_WRITE;
        }

        cost
    }

    fn compute_register_cost(
        &self,
        other: &MachineState,
        live_out_registers: &[ArchitecturalRegister],
    ) -> u32 {
        let mut cost = 0;
        let involved_registers: HashSet<u128> = live_out_registers
            .iter()
            .map(|register| register.identifier as u128)
            .collect();

        for (reg, val) in self
            .registers
            .iter()
            .filter(|(reg, _)| involved_registers.contains(*reg))
        {
            let mut lowest_cost = u32::MAX;
            let mut lowest_cost_ident = 0;

            // whether there exists another register with the same bit-width
            let mut comparable_register_found = false;
            for (other_reg, other_val) in other
                .registers
                .iter()
                .filter(|(reg, _)| involved_registers.contains(*reg))
            {
                // Only compare registers with the same bit-width
                if other_val.width != val.width {
                    continue;
                }

                comparable_register_found = true;
                let local_cost = (*val ^ *other_val).population();
                if local_cost < lowest_cost {
                    lowest_cost = local_cost;
                    lowest_cost_ident = *other_reg;
                }

                // If the local cost equals the lowest cost, we have to make sure
                // that, if the identifiers are the same, this is reflected
                if local_cost == lowest_cost && other_reg == reg {
                    lowest_cost_ident = *reg;
                }
            }

            if !comparable_register_found {
                lowest_cost = 0;
                lowest_cost_ident = *reg;
            }

            cost += lowest_cost;

            if lowest_cost_ident != *reg {
                cost += WEIGHT_REGISTER_MISMATCH;
            }
        }

        // Now, check for registers which exist on one side but not the other
        let keys_only_in_self: Vec<_> = self
            .registers
            .iter()
            .filter(|(key, _)| {
                involved_registers.contains(*key) && !other.registers.contains_key(*key)
            })
            .collect();

        let keys_only_in_other: Vec<_> = other
            .registers
            .iter()
            .filter(|(key, _)| {
                involved_registers.contains(*key) && !self.registers.contains_key(*key)
            })
            .collect();

        for (_, value) in keys_only_in_self.iter() {
            cost += value.width as u32;
            cost += WEIGHT_EXTRA_WRITE;
        }

        for (_, value) in keys_only_in_other.iter() {
            cost += value.width as u32;
            cost += WEIGHT_EXTRA_WRITE;
        }

        cost
    }
}

/// Returns whether a memory location is on the stack
fn memory_location_is_stack_scratch(
    (address, width): (u128, u16),
    sp: &StackPointer,
    sp_val: u128,
) -> bool {
    let byte_width = u128::from(width).div_ceil(8);
    let Some(last_address) = address.checked_add(byte_width - 1) else {
        return false;
    };

    match sp.direction {
        StackDirection::Downwards => {
            let Some(stack_start) = sp_val.checked_sub(sp.stack_size as u128) else {
                return false;
            };
            address >= stack_start && last_address < sp_val
        }
        StackDirection::Upwards => {
            let Some(stack_start) = sp_val.checked_add(1) else {
                return false;
            };
            let Some(stack_end) = sp_val.checked_add(sp.stack_size as u128) else {
                return false;
            };
            address >= stack_start && last_address <= stack_end
        }
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
    let mask = checked_bit_mask(width)?;
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

fn register_destination(register: &Expr) -> Option<u128> {
    match register {
        Expr::Const { value, .. } => Some(*value),
        Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed { register, .. })) => {
            Some(register.0 as u128)
        }
        _ => None,
    }
}

fn constant_value(expr: &Expr) -> Option<(u128, u16)> {
    match expr {
        Expr::Const { value, width } => Some((*value, *width)),
        _ => None,
    }
}

fn checked_bit_mask(width: u16) -> Option<u128> {
    if width == 0 || width > 128 {
        return None;
    }
    Some(if width == 128 {
        !0
    } else {
        (1u128 << width) - 1
    })
}

pub fn bit_mask(width: u16) -> u128 {
    assert!(
        width > 0 && width <= 128,
        "Bit-vector width must be in 1..=128"
    );
    if width == 128 {
        !0
    } else {
        (1u128 << width) - 1
    }
}

fn sign_bit(width: u16) -> u128 {
    1u128 << (width - 1)
}

fn sign_extend_to_u128(value: u128, width: u16) -> u128 {
    let value = value & bit_mask(width);
    if value & sign_bit(width) == 0 {
        value
    } else {
        value | !bit_mask(width)
    }
}

fn signed_value(value: u128, width: u16) -> i128 {
    sign_extend_to_u128(value, width) as i128
}

fn same_width(lhs: BitWord, rhs: BitWord) -> Option<u16> {
    (lhs.width == rhs.width).then_some(lhs.width)
}

fn bool_word(value: bool) -> BitWord {
    BitWord::bool(value)
}

pub fn evaluate_expr(expr: &Expr, state: &MachineState) -> Option<BitWord> {
    match expr {
        Expr::Const { value, width } => Some(BitWord::new(*value, *width)),
        Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
            register,
            identifier_width,
        })) => Some(BitWord::new(register.0 as u128, *identifier_width)),
        Expr::Operand(_) | Expr::DerivedValue(_) => None,
        Expr::ReadRegister { register, width } => {
            let register = evaluate_expr(register, state)?;
            let value = state.registers.get(&register.value)?;
            (value.width == *width).then_some(*value)
        }
        Expr::ReadMemory { address, width } => {
            let address = evaluate_expr(address, state)?;
            read_concrete_memory(state, address, *width)
        }
        Expr::Add(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(BitWord::new(lhs.value.wrapping_add(rhs.value), width))
        }
        Expr::Sub(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(BitWord::new(lhs.value.wrapping_sub(rhs.value), width))
        }
        Expr::Mul(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(BitWord::new(lhs.value.wrapping_mul(rhs.value), width))
        }
        Expr::And(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(BitWord::new(lhs.value & rhs.value, width))
        }
        Expr::Or(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(BitWord::new(lhs.value | rhs.value, width))
        }
        Expr::Xor(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(BitWord::new(lhs.value ^ rhs.value, width))
        }
        Expr::Not(value) => {
            let value = evaluate_expr(value, state)?;
            Some(BitWord::new(!value.value, value.width))
        }
        Expr::ShiftLeft(value, amount) => {
            let value = evaluate_expr(value, state)?;
            let amount = evaluate_expr(amount, state)?;
            let width = same_width(value, amount)?;
            let shifted = if amount.value >= width as u128 {
                0
            } else {
                value.value << amount.value as u32
            };
            Some(BitWord::new(shifted, width))
        }
        Expr::LogicalShiftRight(value, amount) => {
            let value = evaluate_expr(value, state)?;
            let amount = evaluate_expr(amount, state)?;
            let width = same_width(value, amount)?;
            let shifted = if amount.value >= width as u128 {
                0
            } else {
                value.value >> amount.value as u32
            };
            Some(BitWord::new(shifted, width))
        }
        Expr::ArithmeticShiftRight(value, amount) => {
            let value = evaluate_expr(value, state)?;
            let amount = evaluate_expr(amount, state)?;
            let width = same_width(value, amount)?;
            let shifted = if amount.value >= width as u128 {
                if value.value & sign_bit(width) == 0 {
                    0
                } else {
                    bit_mask(width)
                }
            } else {
                (sign_extend_to_u128(value.value, width) as i128 >> amount.value as u32) as u128
            };
            Some(BitWord::new(shifted, width))
        }
        Expr::RotateRight(value, amount) => {
            let value = evaluate_expr(value, state)?;
            let amount = evaluate_expr(amount, state)?;
            let width = same_width(value, amount)?;
            let shift = (amount.value % width as u128) as u32;
            let rotated = if shift == 0 {
                value.value
            } else {
                (value.value >> shift) | (value.value << (width as u32 - shift))
            };
            Some(BitWord::new(rotated, width))
        }
        Expr::Equal(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            same_width(lhs, rhs)?;
            Some(bool_word(lhs.value == rhs.value))
        }
        Expr::UnsignedLessThan(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            same_width(lhs, rhs)?;
            Some(bool_word(lhs.value < rhs.value))
        }
        Expr::SignedLessThan(lhs, rhs) => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let width = same_width(lhs, rhs)?;
            Some(bool_word(
                signed_value(lhs.value, width) < signed_value(rhs.value, width),
            ))
        }
        Expr::Extract { value, high, low } => {
            let value = evaluate_expr(value, state)?;
            if high < low || *high >= value.width {
                return None;
            }
            let width = high - low + 1;
            Some(BitWord::new(value.value >> *low as u32, width))
        }
        Expr::Concat(values) => {
            let mut width = 0u16;
            let mut result = 0u128;
            for value in values {
                let value = evaluate_expr(value, state)?;
                width = width.checked_add(value.width)?;
                if width > 128 {
                    return None;
                }
                result = (result << value.width as u32) | value.value;
            }
            Some(BitWord::new(result, width))
        }
        Expr::ZeroExtend { value, to_width } => {
            let value = evaluate_expr(value, state)?;
            (value.width <= *to_width).then_some(BitWord::new(value.value, *to_width))
        }
        Expr::SignExtend { value, to_width } => {
            let value = evaluate_expr(value, state)?;
            if value.width > *to_width {
                return None;
            }
            Some(BitWord::new(
                sign_extend_to_u128(value.value, value.width),
                *to_width,
            ))
        }
        Expr::CountOnes(value) => {
            let value = evaluate_expr(value, state)?;
            Some(BitWord::new(
                (value.value & bit_mask(value.width)).count_ones() as u128,
                value.width,
            ))
        }
        Expr::AddCarryOut {
            lhs,
            rhs,
            carry_in,
            width,
        } => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let carry_in = evaluate_expr(carry_in, state)?;
            if lhs.width != *width || rhs.width != *width || carry_in.width != 1 {
                return None;
            }
            let carry = if *width == 128 {
                let (sum, carry1) = lhs.value.overflowing_add(rhs.value);
                let (_, carry2) = sum.overflowing_add(carry_in.value & 1);
                carry1 || carry2
            } else {
                (lhs.value & bit_mask(*width))
                    + (rhs.value & bit_mask(*width))
                    + (carry_in.value & 1)
                    > bit_mask(*width)
            };
            Some(bool_word(carry))
        }
        Expr::AddOverflow {
            lhs,
            rhs,
            carry_in,
            width,
        } => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let carry_in = evaluate_expr(carry_in, state)?;
            if lhs.width != *width || rhs.width != *width || carry_in.width != 1 {
                return None;
            }
            let result = lhs
                .value
                .wrapping_add(rhs.value)
                .wrapping_add(carry_in.value & 1)
                & bit_mask(*width);
            Some(bool_word(
                (!(lhs.value ^ rhs.value) & (lhs.value ^ result) & sign_bit(*width)) != 0,
            ))
        }
        Expr::SubCarryOut {
            lhs,
            rhs,
            borrow_in,
            width,
        } => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let borrow_in = evaluate_expr(borrow_in, state)?;
            if lhs.width != *width || rhs.width != *width || borrow_in.width != 1 {
                return None;
            }
            let lhs = lhs.value & bit_mask(*width);
            let rhs = rhs.value & bit_mask(*width);
            let (diff, borrow1) = lhs.overflowing_sub(rhs);
            let (_, borrow2) = diff.overflowing_sub(borrow_in.value & 1);
            Some(bool_word(!(borrow1 || borrow2)))
        }
        Expr::SubOverflow {
            lhs,
            rhs,
            borrow_in,
            width,
        } => {
            let lhs = evaluate_expr(lhs, state)?;
            let rhs = evaluate_expr(rhs, state)?;
            let borrow_in = evaluate_expr(borrow_in, state)?;
            if lhs.width != *width || rhs.width != *width || borrow_in.width != 1 {
                return None;
            }
            let result = lhs
                .value
                .wrapping_sub(rhs.value)
                .wrapping_sub(borrow_in.value & 1)
                & bit_mask(*width);
            Some(bool_word(
                ((lhs.value ^ rhs.value) & (lhs.value ^ result) & sign_bit(*width)) != 0,
            ))
        }
        Expr::Select {
            condition,
            when_true,
            when_false,
        } => {
            let condition = evaluate_expr(condition, state)?;
            let when_true = evaluate_expr(when_true, state)?;
            let when_false = evaluate_expr(when_false, state)?;
            if condition.width != 1 || when_true.width != when_false.width {
                return None;
            }
            Some(if condition.value & 1 != 0 {
                when_true
            } else {
                when_false
            })
        }
    }
}

fn read_concrete_memory(state: &MachineState, address: BitWord, width: u16) -> Option<BitWord> {
    if let Some(value) = state.memory.get(&(address.value, width)) {
        return Some(*value);
    }
    if width == 8 || width % 8 != 0 {
        return None;
    }

    let mut value = 0u128;
    for byte_index in 0..(width / 8) {
        let byte_address = (address.value + u128::from(byte_index)) & bit_mask(address.width);
        let byte = state.memory.get(&(byte_address, 8))?;
        if byte.width != 8 {
            return None;
        }
        value |= (byte.value & 0xff) << u32::from(byte_index * 8);
    }
    Some(BitWord::new(value, width))
}

pub fn write_concrete_memory_bytes(
    state: &mut MachineState,
    address: BitWord,
    value: BitWord,
    width: u16,
) {
    if width % 8 != 0 {
        state
            .memory
            .insert((address.value, width), BitWord::new(value.value, width));
        return;
    }

    let value = BitWord::new(value.value, width);
    for byte_index in 0..(width / 8) {
        let byte_address = (address.value + u128::from(byte_index)) & bit_mask(address.width);
        let byte_value = (value.value >> u32::from(byte_index * 8)) & 0xff;
        state
            .memory
            .insert((byte_address, 8), BitWord::new(byte_value, 8));
    }
}

// Cloning is not allowed to enforce exclusive ownership of the manager
// Similarly, manager_ref should never be accessed from outside the struct and
// all BCDDFunctions must be stored in BddManager.
#[derive(PartialEq, Eq)]
pub struct BddManager {
    manager_ref: BCDDManagerRef,

    left_memory_read_table: Vec<MemoryRead>,
    right_memory_read_table: Vec<MemoryRead>,
    variables: Vec<(VariableDescription, BCDDFunction)>,
    left: Option<BddWord>,
    right: Option<BddWord>,
    constraint: BCDDFunction,

    left_expr: Expr,
    right_expr: Expr,
    registers: Vec<ArchitecturalRegister>,

    true_fn: BCDDFunction,
    false_fn: BCDDFunction,
}

impl BddManager {
    fn new_variable(&mut self, description: VariableDescription) -> BCDDFunction {
        if let Some((existing_description, function)) = self
            .variables
            .iter_mut()
            .find(|(description, _)| *description == VariableDescription::Unallocated)
        {
            *existing_description = description;
            return function.clone();
        }

        let function = self.manager_ref.with_manager_exclusive(|manager| {
            let variable_number = manager
                .add_vars(1)
                .next()
                .expect("Expected one new BCDD variable");

            BCDDFunction::var(&*manager, variable_number).expect("Failed to create BCDD variable")
        });

        self.variables.push((description, function.clone()));
        function
    }

    fn function_uses_variable(
        function: &BCDDFunction,
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        function
            .unique(variable)
            .expect("Failed to check whether a BCDD function uses a variable")
            != *false_fn
    }

    fn optional_word_uses_variable(
        word: &Option<BddWord>,
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        let Some(word) = word else {
            // If the word isn't Some, it doesn't use the variable!
            return false;
        };
        word.bits
            .iter()
            .any(|function| Self::function_uses_variable(function, variable, false_fn))
    }

    fn word_uses_variable(
        word: &BddWord,
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        word.bits
            .iter()
            .any(|function| Self::function_uses_variable(function, variable, false_fn))
    }

    fn table_uses_variable(
        table: &[MemoryRead],
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        table.iter().any(|read| {
            Self::optional_word_uses_variable(&read.lowered_address, variable, false_fn)
                || Self::word_uses_variable(&read.value, variable, false_fn)
        })
    }

    fn release_variable(&mut self, variable_index: usize) {
        assert!(
            variable_index < self.variables.len(),
            "Variable index is outside the variable pool"
        );
        assert!(
            self.variables[variable_index].0 != VariableDescription::Unallocated,
            "Variable is already unallocated"
        );

        let variable = self.variables[variable_index].1.clone();
        let false_fn = &self.false_fn;

        let used = Self::optional_word_uses_variable(&self.left, &variable, false_fn)
            || Self::optional_word_uses_variable(&self.right, &variable, false_fn)
            || Self::function_uses_variable(&self.constraint, &variable, false_fn)
            || Self::table_uses_variable(&self.left_memory_read_table, &variable, false_fn)
            || Self::table_uses_variable(&self.right_memory_read_table, &variable, false_fn)
            || Self::function_uses_variable(&self.true_fn, &variable, false_fn)
            || Self::function_uses_variable(&self.false_fn, &variable, false_fn)
            || self
                .variables
                .iter()
                .enumerate()
                .any(|(index, (_, function))| {
                    index != variable_index
                        && Self::function_uses_variable(function, &variable, false_fn)
                });

        assert!(
            !used,
            "Cannot release a variable that is still used by a live BCDD function"
        );

        self.variables[variable_index].0 = VariableDescription::Unallocated;
    }

    pub fn from_exprs(left_expr: Expr, right_expr: Expr, isa: &ISA) -> Self {
        let manager_ref =
            oxidd::bcdd::new_manager(INNER_NODE_CAPACITY, APPLY_CACHE_CAPACITY, THREAD_COUNT);
        let (true_fn, false_fn) = manager_ref
            .with_manager_shared(|manager| (BCDDFunction::t(manager), BCDDFunction::f(manager)));

        let left_width = left_expr
            .expr_width()
            .expect("Width of instructions must be defined!");
        let right_width = right_expr
            .expr_width()
            .expect("Width of instructions must be defined!");

        assert_eq!(left_width, right_width, "Expression widths must match");
        // Initialize constraint as true_fn
        let constraint = true_fn.clone();

        // Iniitalize variables as vector with capacity equal to the length of the register file
        let registers = isa.registers.clone();
        // let mut variables = Vec::with_capacity(registers.iter().map(|r| r.width as usize).sum::<usize>() as usize);

        // We also want to initialize the register variables
        // This relatively trivial, because we just interleave them
        // First find the maximum register width
        let mut maximum_register_width = 0;
        for register in registers.iter() {
            if register.width > maximum_register_width {
                maximum_register_width = register.width;
            }
        }

        let variables = manager_ref.with_manager_exclusive(|manager| {
            let mut variables = Vec::new();

            for bit in 0..maximum_register_width {
                for register in &registers {
                    // In this case, we have already finished adding the variables for the register
                    // eg if width = 8, bit = 8, we have already added 8 bits (0..=7)
                    if register.width <= bit {
                        continue;
                    }

                    let variable_number =
                        manager.add_vars(1).next().expect("Expected one variable");

                    let function = BCDDFunction::var(&*manager, variable_number)
                        .expect("Failed to allocate BCDD variable");

                    variables.push((
                        VariableDescription::RegisterBit {
                            register: *register,
                            bit: bit.into(),
                        },
                        function,
                    ));
                }
            }

            variables
        });

        let left_memory_read_table = vec![];
        let right_memory_read_table = vec![];

        let mut inst = Self {
            manager_ref,
            left_memory_read_table,
            right_memory_read_table,
            variables,
            left: None,
            right: None,
            constraint,
            left_expr,
            right_expr,
            registers,
            true_fn,
            false_fn,
        };
        inst.assign_memory_read_variables(LEFT_EXPR);
        // Right memory read variables should be at the end of the
        // variable pool, because the left variables are static,
        // but the right variables will be periodically cleared and potentially
        // expanded
        inst.assign_memory_read_variables(RIGHT_EXPR);
        inst
    }

    pub fn from_left_expr(left_expr: Expr, isa: &ISA) -> Self {
        Self::from_exprs(left_expr.clone(), left_expr, isa)
    }

    /// Creates the memory read table and creates variables for one expression
    /// If left is true, it creates the memory read table for the left expression
    /// Otherwise, the right expression.
    /// Generally left = true should be run first, and then left = false should
    /// be run repeatedly as different RHS are tried.
    fn assign_memory_read_variables(&mut self, left: bool) {
        let existing_table = if left {
            &self.left_memory_read_table
        } else {
            &self.right_memory_read_table
        };

        assert_eq!(
            existing_table.len(),
            0,
            "Memory read table should be cleared before running assign_memory_read_variables. Use replace_right_expr to clear variables and the table."
        );

        // Traverse the expression to build one table entry per memory-read occurrence.
        // Read IDs and value variables are assigned afterward in depth order.

        /// Recursively collects memory reads into a skeleton memory-read table.
        fn traverse_expr(
            expr: &Expr,
            depth: u8,
            next_read_id: &mut u32,
            memory_read_table: &mut Vec<MemoryRead>,
        ) {
            match expr {
                Expr::ReadMemory { address, width } => {
                    traverse_expr(address, depth + 1, next_read_id, memory_read_table);
                    // Equivalent reads share one entry, kept at their greatest
                    // observed depth so address dependencies are ordered first.
                    if let Some(read) = memory_read_table
                        .iter_mut()
                        .find(|read| read.address_expr == **address && read.width == *width)
                    {
                        read.depth = read.depth.max(depth);
                    } else {
                        memory_read_table.push(MemoryRead {
                            read_id: *next_read_id,
                            depth,
                            address_expr: *address.clone(),
                            lowered_address: None,
                            width: *width,
                            value: BddWord { bits: vec![] },
                            value_variables: BddWord { bits: vec![] },
                        });
                        *next_read_id += 1;
                    }
                }
                any_expr => {
                    any_expr.visit_children(|child| {
                        traverse_expr(child, depth, next_read_id, memory_read_table)
                    });
                }
            }
        }

        let mut table = Vec::new();
        let mut next_read_id = 0;
        if left {
            traverse_expr(&self.left_expr, 0, &mut next_read_id, &mut table);
        } else {
            traverse_expr(&self.right_expr, 0, &mut next_read_id, &mut table);
        }

        // Assign lower read IDs to deeper reads so address dependencies are
        // processed before the reads that use them. Variables are ordered by
        // descending depth and then interleaved by bit within each depth.
        let Some(max_depth) = table.iter().map(|read| read.depth).max() else {
            return;
        };
        let mut next_read_id: ReadId = 0;
        for depth_level in (0..=max_depth).rev() {
            // Preserve table order within this depth.
            let read_indices: Vec<usize> = table
                .iter()
                .enumerate()
                .filter_map(|(index, read)| (read.depth == depth_level).then_some(index))
                .collect();

            // Assign read IDs before creating their bit variables.
            for &index in &read_indices {
                let read = &mut table[index];

                read.read_id = next_read_id;
                next_read_id += 1;

                read.value.bits.reserve(read.width as usize);
                read.value_variables.bits.reserve(read.width as usize);
            }

            // Get maximum read bit-width
            let maximum_read_width = read_indices
                .iter()
                .map(|&index| table[index].width)
                .max()
                .unwrap_or(0);
            // Now we want to iterate through each read at this depth, and update `value.bits`
            // We also want to go bit by bit just like constructing the registers
            // Bit-major ordering creates the desired interleaving:
            //
            // read A bit 0
            // read B bit 0
            // read A bit 1
            // read B bit 1
            // ...
            for bit in 0..maximum_read_width {
                for &index in &read_indices {
                    let read = &table[index];

                    if bit >= read.width {
                        continue;
                    }

                    let read_id = read.read_id;
                    let function = self.new_variable(VariableDescription::MemoryReadValueBit {
                        read_id,
                        left,
                        bit: bit as usize,
                    });

                    table[index].value.bits.push(function.clone());
                    table[index].value_variables.bits.push(function);
                }
            }
        }

        if left {
            self.left_memory_read_table = table;
        } else {
            self.right_memory_read_table = table;
        }
    }

    /// Removes the `right` expression along with variables,
    /// and replaces it with another expr
    /// Effectively, it should act like running from_exprs, but saves computation
    /// by only replacing the one which needs to be replaced
    /// After this, constraints are also gone and need to be rebuilt.
    /// The only thing that doesn't need to be rebuilt is the other Expr
    /// which was not replaced.
    pub fn replace_right_expr(&mut self, new_expr: Expr) {
        let expected_width = self
            .left_expr
            .expr_width()
            .expect("Width of existing expression should be defined");

        assert_eq!(
            new_expr
                .expr_width()
                .expect("Width of new_expr should be defined"),
            expected_width,
            "new_expr width should match existing expression widths"
        );

        self.right = None;
        self.right_memory_read_table.clear();
        self.constraint = self.true_fn.clone();
        self.right_expr = new_expr;

        let right_variable_indices: Vec<usize> = self
            .variables
            .iter()
            .enumerate()
            .filter_map(|(index, (description, _))| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit { left: false, .. }
                )
                .then_some(index)
            })
            .collect();

        for variable_index in right_variable_indices {
            self.release_variable(variable_index);
        }

        self.manager_ref.with_manager_shared(|manager| {
            manager.gc();
        });

        self.assign_memory_read_variables(RIGHT_EXPR);
    }

    /// Lowers memory addresses of the left or right expression
    fn lower_memory(&mut self, left: bool) {
        let len = if left {
            self.left_memory_read_table.len()
        } else {
            self.right_memory_read_table.len()
        };

        for i in 0..len {
            let address_lowered = {
                let table = if left {
                    &mut self.left_memory_read_table
                } else {
                    &mut self.right_memory_read_table
                };

                // Only lower the address if it isn't already lowered
                if table[i].lowered_address.is_some() {
                    continue;
                }

                let address_expr = table[i].address_expr.clone();
                self.lower_expression(&address_expr, left)
            };

            let table = if left {
                &mut self.left_memory_read_table
            } else {
                &mut self.right_memory_read_table
            };
            table[i].lowered_address = Some(address_lowered);
        }
    }

    /// Builds the memory constraint
    /// Which equals And_(i<j)(Ai == Aj => Vi == Vj)
    fn build_memory_constraint(&mut self) {
        let mut constraint = self.true_fn.clone();

        // Create a combined array of all memory reads
        let memory_reads: Vec<&MemoryRead> = self
            .left_memory_read_table
            .iter()
            .chain(&self.right_memory_read_table)
            .collect();

        for i in 0..memory_reads.len() {
            for j in 0..i {
                let left_addr = memory_reads[i]
                    .lowered_address
                    .clone()
                    .expect("Memory read address should be lowered before building constraints");
                let right_addr = memory_reads[j]
                    .lowered_address
                    .clone()
                    .expect("Memory read address should be lowered before building constraints");

                let addresses_equal = self
                    .lower_equal(left_addr, right_addr)
                    .expect("Failed to compare memory read addresses")
                    .bits
                    .pop()
                    .expect("Equality comparison should produce one bit");
                let values_equal = self
                    .all_true(
                        &memory_reads[i]
                            .value_variables
                            .bits
                            .iter()
                            .zip(&memory_reads[j].value_variables.bits)
                            .map(|(left_bit, right_bit)| {
                                left_bit
                                    .equiv(right_bit)
                                    .expect("Failed to compare memory read value bits")
                            })
                            .collect::<Vec<_>>(),
                    )
                    .expect("Failed to compare memory read values");
                let implication = addresses_equal
                    .not()
                    .expect("Failed to negate memory address equality")
                    .or(&values_equal)
                    .expect("Failed to build memory read implication");
                constraint = constraint
                    .and(&implication)
                    .expect("Failed to update memory constraint");
            }
        }

        self.constraint = constraint;
    }

    fn word_difference(
        lhs: &BddWord,
        rhs: &BddWord,
        bdd_false: &BCDDFunction,
    ) -> AllocResult<BCDDFunction> {
        assert_eq!(lhs.bits.len(), rhs.bits.len());

        let mut different = bdd_false.clone();

        for (lhs_bit, rhs_bit) in lhs.bits.iter().zip(&rhs.bits) {
            let bit_different = lhs_bit.xor(rhs_bit)?;
            different = different.or(&bit_different)?;
        }

        Ok(different)
    }

    fn lower_left_and_right(&mut self) -> (BddWord, BddWord) {
        if self.left.is_none() {
            self.left = Some(self.lower_expression(&self.left_expr, LEFT_EXPR));
        }
        if self.right.is_none() {
            self.right = Some(self.lower_expression(&self.right_expr, RIGHT_EXPR));
        }

        (
            self.left
                .clone()
                .expect("Left expression should be lowered"),
            self.right
                .clone()
                .expect("Right expression should be lowered"),
        )
    }

    fn cube_bit(cube: &[OptBool], variable_index: usize) -> bool {
        matches!(cube.get(variable_index), Some(OptBool::True))
    }

    fn cube_assignment(cube: &[OptBool]) -> Vec<(u32, bool)> {
        cube.iter()
            .enumerate()
            .map(|(index, value)| (index as u32, matches!(value, OptBool::True)))
            .collect()
    }

    fn evaluate_bdd_word_under_cube(word: &BddWord, assignment: &[(u32, bool)]) -> u128 {
        word.bits
            .iter()
            .enumerate()
            .map(|(bit, function)| {
                if function.eval(assignment.iter().copied()) {
                    1u128 << bit
                } else {
                    0
                }
            })
            .sum()
    }

    pub fn counterexample_state_from_cube(&self, cube: &[OptBool]) -> MachineState {
        let mut state = MachineState::default();

        for (index, (description, _)) in self.variables.iter().enumerate() {
            let VariableDescription::RegisterBit { register, bit } = description else {
                continue;
            };

            let entry = state
                .registers
                .entry(register.identifier as u128)
                .or_insert_with(|| BitWord::new(0, register.width as u16));
            assert_eq!(
                entry.width, register.width as u16,
                "Register variable descriptions should agree on register width"
            );
            if Self::cube_bit(cube, index) {
                entry.value |= 1u128 << *bit as u32;
            }
        }

        let assignment = Self::cube_assignment(cube);
        for read in self
            .left_memory_read_table
            .iter()
            .chain(&self.right_memory_read_table)
        {
            let Some(address) = &read.lowered_address else {
                continue;
            };
            let address = Self::evaluate_bdd_word_under_cube(address, &assignment);
            let value = Self::evaluate_bdd_word_under_cube(&read.value_variables, &assignment);
            write_concrete_memory_bytes(
                &mut state,
                BitWord::new(
                    address,
                    read.lowered_address.as_ref().unwrap().bits.len() as u16,
                ),
                BitWord::new(value, read.width),
                read.width,
            );
        }

        state
    }

    /// Compares the equality of the left and right expressions using a BDD
    /// Returns a counterexample if they are not equal
    pub fn compare(&mut self) -> AllocResult<BddEquality> {
        println!("{:?}", self.right_expr);
        let (left, right) = self.lower_left_and_right();

        // Lower the memory of both expressions
        // This function call is cheap if LEFT_EXPR has already been lowered
        self.lower_memory(LEFT_EXPR);
        self.lower_memory(RIGHT_EXPR);

        // Now, we need to build the memory constraint
        self.build_memory_constraint();

        // Returns whether there is a difference bitwise between the left and right word
        let difference = Self::word_difference(&left, &right, &self.false_fn)?;

        // Now, by anding this difference function with the constraint function,
        // we get a function which is high for any counter example inputs (ie machine states where the Expr doesn't match)
        let counterexamples = self.constraint.and(&difference)?;

        // If counterexamples is UNSAT, it is always 0 and so there is never
        // a difference between left and right for any valid input
        if !counterexamples.satisfiable() {
            Ok(BddEquality::Equal)
        } else {
            // Now we want to return a specific counterexample
            let cube = counterexamples
                .pick_cube(|_, _, _| false)
                .expect("Function is satisfiable, so a counterexample should exist");
            Ok(BddEquality::Unequal(
                self.counterexample_state_from_cube(&cube),
            ))
        }
    }

    /// Lowers an expression
    fn lower_expression(&self, expr: &Expr, left: bool) -> BddWord {
        self.try_lower_expression(expr, left)
            .expect("BCDD node allocation failed")
    }

    fn try_lower_expression(&self, expr: &Expr, left: bool) -> AllocResult<BddWord> {
        match expr {
            Expr::Const { value, width } => Ok(self.lower_constant(*value, *width)),

            Expr::ReadRegister { register, width } => {
                let selector = self.try_lower_expression(register, left)?;
                self.lower_register_read(selector, *width)
            }

            // This is the only valid Operand
            // Other Operands involve references to fields
            // This should collapse to the register identifier
            Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
                register,
                identifier_width,
            })) => Ok(self.lower_constant(register.0 as u128, *identifier_width)),

            Expr::ReadMemory { address, width } => {
                let table = if left {
                    &self.left_memory_read_table
                } else {
                    &self.right_memory_read_table
                };

                let read = table
                    .iter()
                    .find(|read| read.address_expr == **address && read.width == *width)
                    .unwrap_or_else(|| {
                        panic!("memory read missing from table: address={address:?}, width={width}")
                    });

                Ok(read.value.clone())
            }

            Expr::Add(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_add(op1_lowered, op2_lowered)
            }

            Expr::Mul(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_mul(op1_lowered, op2_lowered)
            }

            Expr::And(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_and(op1_lowered, op2_lowered)
            }

            Expr::Not(op) => {
                let op_lowered = self.try_lower_expression(op, left)?;
                self.lower_not(op_lowered)
            }

            Expr::ShiftLeft(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_shift_left(value_lowered, amount_lowered)
            }

            Expr::LogicalShiftRight(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_logical_shift_right(value_lowered, amount_lowered)
            }

            Expr::ArithmeticShiftRight(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_arithmetic_shift_right(value_lowered, amount_lowered)
            }

            Expr::RotateRight(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_rotate_right(value_lowered, amount_lowered)
            }

            Expr::Equal(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_equal(op1_lowered, op2_lowered)
            }

            Expr::UnsignedLessThan(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_unsigned_lt(op1_lowered, op2_lowered)
            }

            Expr::SignedLessThan(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_signed_lt(op1_lowered, op2_lowered)
            }

            Expr::Extract { value, high, low } => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_extract(value_lowered, *high, *low)
            }

            Expr::Concat(exprs) => {
                let exprs_lowered = exprs
                    .iter()
                    .map(|e| self.try_lower_expression(e, left))
                    .collect::<AllocResult<Vec<BddWord>>>()?;
                self.lower_concat(exprs_lowered)
            }

            Expr::ZeroExtend { value, to_width } => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_zero_extend(value_lowered, *to_width)
            }

            Expr::SignExtend { value, to_width } => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_sign_extend(value_lowered, *to_width)
            }

            Expr::CountOnes(value) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_count_ones(value_lowered)
            }

            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs_lowered = self.try_lower_expression(lhs, left)?;
                let rhs_lowered = self.try_lower_expression(rhs, left)?;
                let cin_lowered = self.try_lower_expression(carry_in, left)?;
                self.lower_add_cout(lhs_lowered, rhs_lowered, cin_lowered, *width)
            }

            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs_lowered = self.try_lower_expression(lhs, left)?;
                let rhs_lowered = self.try_lower_expression(rhs, left)?;
                let cin_lowered = self.try_lower_expression(carry_in, left)?;
                self.lower_add_overflow(lhs_lowered, rhs_lowered, cin_lowered, *width)
            }
            // Anything else should not show up in properly canonicalied expressions
            expr => {
                unreachable!("encountered Expr which should not appear in canonical form: {expr:?}")
            }
        }
    }

    fn lower_constant(&self, value: u128, width: u16) -> BddWord {
        assert!(width <= 128);

        let bits = (0..width)
            .map(|bit| {
                if ((value >> bit) & 1) != 0 {
                    self.true_fn.clone()
                } else {
                    self.false_fn.clone()
                }
            })
            .collect();

        BddWord { bits }
    }

    /// Simple 2-1 mux
    fn mux_word(
        &self,
        condition: &BCDDFunction,
        when_true: &BddWord,
        when_false: &BddWord,
    ) -> AllocResult<BddWord> {
        assert_eq!(when_true.bits.len(), when_false.bits.len());

        let bits = when_true
            .bits
            .iter()
            .zip(&when_false.bits)
            .map(|(true_bit, false_bit)| condition.ite(true_bit, false_bit))
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    /// Lowers a register read and builds a register mux to select the register contents
    /// Selects from all registers of width `width` and `identifier_width == selector.bits.len()`
    fn lower_register_read(&self, selector: BddWord, width: u16) -> AllocResult<BddWord> {
        assert!(
            selector.bits.len() <= 8,
            "register selector exceeds u8 identifier width"
        );
        let ident_width = selector.bits.len() as u8;
        // Temporarily initialize registers as all low
        // Technically it is not guaranteed that all bits are overriden.
        // As such, it is possible for these bits to "poison" the output
        // if the `selector` isn't selecting a valid register for the given `selector_width` and width
        let mut registers = vec![
            BddWord {
                bits: vec![self.false_fn.clone(); width as usize]
            };
            1usize << ident_width
        ];
        for (description, variable) in self.variables.iter() {
            let VariableDescription::RegisterBit { register, bit } = description else {
                // This isn't the right type of read!
                continue;
            };
            if register.width != width as u8 {
                continue;
            }
            if register.identifier_width != ident_width {
                continue;
            }

            if register.identifier as usize >= (1usize << register.identifier_width) {
                panic!("Register identifier too large for its identifier width!");
            }

            // This is safe because we have a guarantee on the length of the registers vec
            let reg_mut = &mut registers[register.identifier as usize];
            reg_mut.bits[*bit] = variable.clone();
        }

        // First layer: LSB selection bit (0 = even registers, 1 = odd)
        // Second layer: second LSB (0 = multiple of 4, 1 = multiple of 4 + 2)
        // and so on
        for selector_bit in &selector.bits {
            let mut next = Vec::with_capacity(registers.len() / 2);

            for pair in registers.chunks_exact(2) {
                let selected = self.mux_word(
                    selector_bit,
                    &pair[1], // selector bit = 1
                    &pair[0], // selector bit = 0
                )?;

                next.push(selected);
            }

            registers = next;
        }
        assert_eq!(registers.len(), 1);
        Ok(registers.pop().unwrap())
    }

    fn full_adder(
        a: &BCDDFunction,
        b: &BCDDFunction,
        carry_in: &BCDDFunction,
    ) -> AllocResult<(BCDDFunction, BCDDFunction)> {
        let a_xor_b = a.xor(b)?;

        let sum = a_xor_b.xor(carry_in)?;

        let generated = a.and(b)?;
        let propagated = a_xor_b.and(carry_in)?;
        let carry_out = generated.or(&propagated)?;

        Ok((sum, carry_out))
    }

    /// Helper function with an adder, which returns a result and the carry bit
    fn adder(
        &self,
        op1: &BddWord,
        op2: &BddWord,
        carry_in: BCDDFunction,
        width: usize,
    ) -> AllocResult<(BddWord, BCDDFunction)> {
        let mut result = Vec::with_capacity(width);
        let mut carry = carry_in;

        for bit in 0..width {
            let (sum, next_carry) = Self::full_adder(&op1.bits[bit], &op2.bits[bit], &carry)?;

            result.push(sum);
            carry = next_carry;
        }

        let result = BddWord { bits: result };

        Ok((result, carry))
    }

    /// Lowers an addition expression
    fn lower_add(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        assert_eq!(op1.bits.len(), op2.bits.len());
        let width = op1.bits.len();

        let (result, ..) = self.adder(&op1, &op2, self.false_fn.clone(), width)?;

        Ok(result)
    }

    /// Helper function to shift left by a constant
    fn shift_left_const(&self, value: &BddWord, amount: usize) -> BddWord {
        let width = value.bits.len();
        let mut result = vec![self.false_fn.clone(); width];
        for source in 0..value.bits.len() {
            let destination = source + amount;

            if destination < width {
                result[destination] = value.bits[source].clone();
            }
        }

        BddWord { bits: result }
    }

    /// Helper function to shift right (logical) by a constant
    fn shift_logical_right_const(&self, value: &BddWord, amount: usize) -> BddWord {
        let width = value.bits.len();
        let mut result = vec![self.false_fn.clone(); width];
        for source in 0..value.bits.len() {
            // This bit underflows and will be fully shifted out
            if source < amount {
                continue;
            }
            let destination = source - amount;
            result[destination] = value.bits[source].clone();
        }

        BddWord { bits: result }
    }

    /// Helper function to shift right (arithmetic) by a constant
    fn shift_arith_right_const(&self, value: &BddWord, amount: usize) -> BddWord {
        let width = value.bits.len();
        let sign_bit = value.bits.last().expect("Width should be greater than 0!");

        // Only change is we fill with the sign bit rather than 0
        let mut result = vec![sign_bit.clone(); width];
        for source in 0..value.bits.len() {
            // This bit underflowsm and will be shifted out
            if source < amount {
                continue;
            }
            let destination = source - amount;
            result[destination] = value.bits[source].clone();
        }

        BddWord { bits: result }
    }

    /// Helper function to rotate right by a constant
    fn rotate_right_const(&self, value: &BddWord, amount: usize) -> BddWord {
        let width = value.bits.len();

        // ROR is mod width
        // Eg ROR 0b101 by 3 is euqivalent to ROR by 0
        let amount = amount % width;

        // Take the bit at destination + amount and shift it by amount bits to destination
        let bits = (0..width)
            .map(|destination| {
                let source = (destination + amount) % width;
                value.bits[source].clone()
            })
            .collect();

        BddWord { bits }
    }

    /// Helper function to mask a word by a single bit (eg 0b101 & 0b0 = 0b000)
    fn mask_word(&self, condition: &BCDDFunction, value: &BddWord) -> AllocResult<BddWord> {
        let bits = value
            .bits
            .iter()
            .map(|bit| bit.and(condition))
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    /// Lowers a multiplication expression
    /// Takes two operands of some `width` and returns a BddWord of `width`
    fn lower_mul(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        assert_eq!(op1.bits.len(), op2.bits.len());
        let width = op1.bits.len();
        let mut result = BddWord {
            bits: vec![self.false_fn.clone(); width],
        };

        // Shift and add combinatorial multiplier
        // a*b = sum(bi * (a << i))
        for multiplier_bit in 0..width {
            let shifted = self.shift_left_const(&op1, multiplier_bit);

            let partial_product = self.mask_word(&op2.bits[multiplier_bit], &shifted)?;

            result = self.lower_add(result, partial_product)?;
        }

        Ok(result)
    }

    /// Lowers a bitwise and expression
    fn lower_and(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        op1 & op2
    }

    /// Lowers bitwise not
    fn lower_not(&self, op: BddWord) -> AllocResult<BddWord> {
        let bits = op
            .bits
            .iter()
            .map(|bit| bit.not())
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    fn barrel_shifter<F>(
        &self,
        mut value: BddWord,
        amount: BddWord,
        shift_const: F,
    ) -> AllocResult<BddWord>
    where
        F: Fn(&BddWord, usize) -> BddWord,
    {
        let width = value.bits.len();

        // Barrel shifter -- looks at each amount bit at position n, and creates a mux
        // shifting the result by 2^n if that bit is set
        for (bit_index, amount_bit) in amount.bits.iter().enumerate() {
            let shift = 1usize.checked_shl(bit_index as u32).unwrap_or(width);

            let shifted = shift_const(&value, shift);

            // Select: amount_bit ? shifted : result
            // if amount_bit is 1, shift by this amount, otherwise don't shift
            value = self.mux_word(amount_bit, &shifted, &value)?;
        }

        Ok(value)
    }

    fn rotate_right_shift_for_bit(width: usize, bit_index: usize) -> usize {
        assert!(width > 0);

        let mut shift = 1 % width;
        for _ in 0..bit_index {
            shift = (shift * 2) % width;
        }
        shift
    }

    /// Helper function to return if BddWord is all true
    fn all_true(&self, values: &[BCDDFunction]) -> AllocResult<BCDDFunction> {
        values
            .iter()
            .try_fold(self.true_fn.clone(), |result, value| result.and(value))
    }

    /// Lowers shift left
    fn lower_shift_left(&self, value: BddWord, amount: BddWord) -> AllocResult<BddWord> {
        self.barrel_shifter(value, amount, |v, a| self.shift_left_const(&v, a))
    }

    /// Lowers logical shift right
    fn lower_logical_shift_right(&self, value: BddWord, amount: BddWord) -> AllocResult<BddWord> {
        self.barrel_shifter(value, amount, |v, a| self.shift_logical_right_const(&v, a))
    }

    /// Lowers arithmetic shift right
    fn lower_arithmetic_shift_right(
        &self,
        value: BddWord,
        amount: BddWord,
    ) -> AllocResult<BddWord> {
        self.barrel_shifter(value, amount, |v, a| self.shift_arith_right_const(&v, a))
    }

    /// Lowers rotate right
    fn lower_rotate_right(&self, mut value: BddWord, amount: BddWord) -> AllocResult<BddWord> {
        let width = value.bits.len();

        for (bit_index, amount_bit) in amount.bits.iter().enumerate() {
            // The rotate amount can't be calculated easily as 2^n, because it can overflow
            // With shifts, when the value overflows, we simply clamp it to width, because
            // the bit is discarded anyways.
            // However, with shift, the bit is not discarded.
            // So instead, we take shift mod width at every step.
            let shift = Self::rotate_right_shift_for_bit(width, bit_index);
            if shift == 0 {
                continue;
            }

            let shifted = self.rotate_right_const(&value, shift);
            value = self.mux_word(amount_bit, &shifted, &value)?;
        }

        Ok(value)
    }

    /// Lowers equals operation - returns single bit in a Word
    fn lower_equal(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        let bits = vec![
            self.all_true(
                &op1.lower_bitwise_binary(op2, |op1_b, op2_b| op1_b.equiv(op2_b))?
                    .bits,
            )?,
        ];

        Ok(BddWord { bits })
    }

    /// Lowers unsigned less than. op1 < op2
    fn lower_unsigned_lt(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        assert_eq!(op1.bits.len(), op2.bits.len());
        let width = op1.bits.len();

        // Iterate from MSB to LSB
        // If op1[i] == op2[i], inconclusive
        // if op1[i] < op2[i], true
        // if op1[i] > op2[i], false
        // if everything has been inconclusive so far, and op1[0] == op2[0], false
        // true and false are both locking states
        // so we need 2 bits: one to represent whether we have determined that op1 != op2 yet
        // one to represent whether we have determined that op1 < op2 yet
        let mut equal_so_far = self.true_fn.clone();
        let mut less_so_far = self.false_fn.clone();
        for bit_idx in (0..width).rev() {
            let a = &op1.bits[bit_idx];
            let b = &op2.bits[bit_idx];

            // a < b iff a == 0 & b == 1 & equal_so_far
            let bit_less = a.not()?.and(b)?;
            less_so_far = less_so_far.or(&bit_less.and(&equal_so_far)?)?;

            let equal = a.equiv(b)?;
            equal_so_far = equal_so_far.and(&equal)?;
        }
        Ok(BddWord {
            bits: vec![less_so_far],
        })
    }

    /// Lowers signed less than
    fn lower_signed_lt(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        assert_eq!(op1.bits.len(), op2.bits.len());
        let width = op1.bits.len();

        assert!(width > 0);

        // Iterate from MSB to LSB, except treat the MSB different
        // If op1[i] == op2[i], inconclusive
        // if op1[i] < op2[i], true
        // if op1[i] > op2[i], false
        // if everything has been inconclusive so far, and op1[0] == op2[0], false
        // true and false are both locking states
        // so we need 2 bits: one to represent whether we have determined that op1 != op2 yet
        // one to represent whether we have determined that op1 < op2 yet

        let a_msb = &op1.bits[width - 1];
        let b_msb = &op2.bits[width - 1];
        let mut equal_so_far = a_msb.equiv(b_msb)?;

        // a < b if sign(a) == 1 and sign(b) == 0
        let mut less_so_far = a_msb.and(&b_msb.not()?)?;
        for bit_idx in (0..(width - 1)).rev() {
            let a = &op1.bits[bit_idx];
            let b = &op2.bits[bit_idx];

            // a < b iff a == 0 & b == 1 & equal_so_far
            let bit_less = a.not()?.and(b)?;
            less_so_far = less_so_far.or(&bit_less.and(&equal_so_far)?)?;

            let equal = a.equiv(b)?;
            equal_so_far = equal_so_far.and(&equal)?;
        }
        Ok(BddWord {
            bits: vec![less_so_far],
        })
    }

    /// Lowers bit extraction
    fn lower_extract(&self, value: BddWord, high: u16, low: u16) -> AllocResult<BddWord> {
        Ok(BddWord {
            bits: value.bits[low as usize..=high as usize].to_vec(),
        })
    }

    /// Lowers concatenation
    fn lower_concat(&self, values: Vec<BddWord>) -> AllocResult<BddWord> {
        let bits = values
            .into_iter()
            .rev() // eg if [[1, 1], [0, 0]], result should be [0, 0, 1, 1] with 1, 1 as MSB
            .flat_map(|e| e.bits)
            .collect();
        Ok(BddWord { bits })
    }

    /// Lowers zero extension
    fn lower_zero_extend(&self, mut value: BddWord, to_width: u16) -> AllocResult<BddWord> {
        let width = value.bits.len();
        if width > to_width as usize {
            panic!("width must be less than to_width!");
        }
        value.bits.resize(to_width as usize, self.false_fn.clone());
        Ok(value)
    }

    /// Lowers sign extension
    fn lower_sign_extend(&self, mut value: BddWord, to_width: u16) -> AllocResult<BddWord> {
        let width = value.bits.len();
        if width > to_width as usize {
            panic!("width must be less than to_width!");
        }

        let sign = &value.bits[width - 1];
        value.bits.resize(to_width as usize, sign.clone());
        Ok(value)
    }

    /// Lowers counting ones
    fn lower_count_ones(&self, value: BddWord) -> AllocResult<BddWord> {
        let width = value.bits.len();
        // Initialize the count as 0
        let mut count = BddWord {
            bits: vec![self.false_fn.clone(); width],
        };

        for idx in 0..width {
            let mut bit = BddWord {
                bits: vec![value.bits[idx].clone()],
            };
            bit.bits.resize(width, self.false_fn.clone());
            count = self.lower_add(count, bit)?;
        }
        Ok(count)
    }

    /// Lowers add carry out
    fn lower_add_cout(
        &self,
        lhs: BddWord,
        rhs: BddWord,
        carry_in: BddWord,
        width: u16,
    ) -> AllocResult<BddWord> {
        assert_eq!(carry_in.bits.len(), 1);

        let (.., cout) = self.adder(&lhs, &rhs, carry_in.bits[0].clone(), width as usize)?;

        Ok(BddWord { bits: vec![cout] })
    }

    /// Lowers add overflow flag bit
    fn lower_add_overflow(
        &self,
        lhs: BddWord,
        rhs: BddWord,
        carry_in: BddWord,
        width: u16,
    ) -> AllocResult<BddWord> {
        assert_eq!(carry_in.bits.len(), 1);

        let (res, ..) = self.adder(&lhs, &rhs, carry_in.bits[0].clone(), width as usize)?;

        // Overflow occurs when: lhs and rhs have same sign, but res has a different sign
        let lmsb = &lhs.bits[width as usize - 1];
        let rmsb = &rhs.bits[width as usize - 1];
        let res_msb = &res.bits[width as usize - 1];
        let overflow = lmsb.equiv(rmsb)?.and(&lmsb.equiv(res_msb)?.not()?)?;

        Ok(BddWord {
            bits: vec![overflow],
        })
    }
}

/// A word which is created by a vector of BCDDs
/// So, each bit is defined by some function.
#[derive(Clone, PartialEq, Eq)]
pub struct BddWord {
    /// bits[0] is the least-significant bit.
    pub bits: Vec<BCDDFunction>,
}

impl BddWord {
    pub fn lower_bitwise_binary<F>(self, rhs: BddWord, operation: F) -> AllocResult<BddWord>
    where
        F: Fn(&BCDDFunction, &BCDDFunction) -> AllocResult<BCDDFunction>,
    {
        assert_eq!(self.bits.len(), rhs.bits.len());

        let bits = self
            .bits
            .iter()
            .zip(&rhs.bits)
            .map(|(lhs, rhs)| operation(lhs, rhs))
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }
}

impl BitOr for BddWord {
    type Output = AllocResult<Self>;
    fn bitor(self, rhs: Self) -> Self::Output {
        self.lower_bitwise_binary(rhs, |lhs_bit, rhs_bit| lhs_bit.or(rhs_bit))
    }
}

impl BitAnd for BddWord {
    type Output = AllocResult<Self>;
    fn bitand(self, rhs: Self) -> Self::Output {
        self.lower_bitwise_binary(rhs, |lhs_bit, rhs_bit| lhs_bit.and(rhs_bit))
    }
}

/// Given some sequence of instructions, create a list of all Effects of the sequence in terms of the initial state
/// Includes lowering memory accesses to single-byte accesses
/// This effectively collapses instructions.len() = k instructions into a single state update u where s(t0+k) = u(s(t0))
pub fn instruction_seq_to_effects(instructions: &Program, isa: &ISA) -> Vec<Effect> {
    instruction_seq_to_effects_impl(instructions, isa, None)
}

pub fn instruction_seq_to_effects_profiled(
    instructions: &Program,
    isa: &ISA,
) -> (Vec<Effect>, InstructionSeqToEffectsProfile) {
    let mut profile = InstructionSeqToEffectsProfile::default();
    let start = Instant::now();
    let effects = instruction_seq_to_effects_impl(instructions, isa, Some(&mut profile));
    profile.total = start.elapsed();
    profile.final_effects = effects.len();
    (effects, profile)
}

fn instruction_seq_to_effects_impl(
    instructions: &Program,
    isa: &ISA,
    mut profile: Option<&mut InstructionSeqToEffectsProfile>,
) -> Vec<Effect> {
    let mut seq_effects = vec![];
    for instruction in instructions.iter_instructions() {
        if let Some(profile) = profile.as_mut() {
            profile.instructions += 1;
        }

        let lowered_effects = instruction_to_lowered_effects_impl(
            instruction,
            isa,
            &seq_effects,
            profile.as_deref_mut(),
        );
        if let Some(profile) = profile.as_mut() {
            profile.lowered_effects += lowered_effects.len();
            profile.max_accumulated_effects =
                profile.max_accumulated_effects.max(seq_effects.len());
        }

        // We want to combine the effects of this instruction with the existing effects in seq_effects
        // The variable name effect_2 refers to the fact that it takes place after the effect_1s that we are comparing it to
        for effect_2 in lowered_effects {
            // Whether we've found an effect in seq_effects which writes to the same place as effect_2
            let mut found_same_write = false;
            let combine_start = profile.as_ref().map(|_| Instant::now());
            for effect_1 in seq_effects.iter_mut() {
                if let Some(profile) = profile.as_mut() {
                    profile.combine_attempts += 1;
                }
                if let Some(new_effect) = combine_effects(effect_1, &effect_2) {
                    *effect_1 = new_effect;
                    found_same_write = true;
                    if let Some(profile) = profile.as_mut() {
                        profile.combine_matches += 1;
                    }
                    break;
                }
            }
            if let (Some(profile), Some(start)) = (profile.as_mut(), combine_start) {
                profile.combine_total += start.elapsed();
            }

            // If effect_2 didn't contribute itself to an existing effect in seq_effects, we want to add it
            if !found_same_write {
                // However, we don't want to add it if the effect_2.guard is a constant 0
                let guard = match effect_2 {
                    Effect::WriteMemory { ref guard, .. } => guard,
                    Effect::WriteRegister { ref guard, .. } => guard,
                };
                if *guard != constant(0, 1) {
                    seq_effects.push(effect_2);
                }
            }
            if let Some(profile) = profile.as_mut() {
                profile.max_accumulated_effects =
                    profile.max_accumulated_effects.max(seq_effects.len());
            }
        }
    }
    seq_effects
}

pub fn instruction_to_lowered_effects(
    instruction: &DecodedInstruction,
    isa: &ISA,
    previous_effects: &[Effect],
) -> Vec<Effect> {
    instruction_to_lowered_effects_impl(instruction, isa, previous_effects, None)
}

pub fn execute_program_concrete(
    instructions: &Program,
    isa: &ISA,
    state: &MachineState,
) -> MachineState {
    ConcreteProgram::from_program(instructions, isa).execute(state)
}

#[derive(Clone, Debug)]
pub struct ConcreteProgram {
    instructions: Vec<Vec<Effect>>,
}

impl ConcreteProgram {
    pub fn from_program(instructions: &Program, isa: &ISA) -> Self {
        Self {
            instructions: instructions
                .iter_instructions()
                .map(|instruction| {
                    instruction_effects(instruction, isa)
                        .iter()
                        .cloned()
                        .map(|effect| collapse_effect_for_concrete_execution(effect, instruction))
                        .collect()
                })
                .collect(),
        }
    }

    pub fn execute(&self, state: &MachineState) -> MachineState {
        let mut current_state = state.clone();

        for instruction_effects in &self.instructions {
            let mut register_writes = Vec::new();
            let mut memory_writes = Vec::new();

            for effect in instruction_effects.iter() {
                match effect {
                    Effect::WriteRegister {
                        guard,
                        register,
                        value,
                    } => {
                        if evaluate_expr(&guard, &current_state)
                            .is_none_or(|guard| guard.value == 0)
                        {
                            continue;
                        }

                        if let (Some(register), Some(value)) = (
                            evaluate_expr(&register, &current_state),
                            evaluate_expr(&value, &current_state),
                        ) {
                            register_writes.push((register.value, value));
                        }
                    }
                    Effect::WriteMemory {
                        guard,
                        address,
                        value,
                        width,
                    } => {
                        if evaluate_expr(&guard, &current_state)
                            .is_none_or(|guard| guard.value == 0)
                        {
                            continue;
                        }

                        if let (Some(address), Some(value)) = (
                            evaluate_expr(&address, &current_state),
                            evaluate_expr(&value, &current_state),
                        ) {
                            collect_concrete_memory_writes(
                                &mut memory_writes,
                                address,
                                value,
                                *width,
                            );
                        }
                    }
                }
            }

            for (register, value) in register_writes {
                current_state.registers.insert(register, value);
            }
            for (key, value) in memory_writes {
                current_state.memory.insert(key, value);
            }
        }

        current_state
    }
}

fn collapse_effect_for_concrete_execution(
    effect: Effect,
    instruction: &DecodedInstruction,
) -> Effect {
    match effect {
        Effect::WriteRegister {
            guard,
            register,
            value,
        } => Effect::WriteRegister {
            guard: guard.collapse(instruction),
            register: register.collapse(instruction),
            value: value.collapse(instruction),
        },
        Effect::WriteMemory {
            guard,
            address,
            value,
            width,
        } => Effect::WriteMemory {
            guard: guard.collapse(instruction),
            address: address.collapse(instruction),
            value: value.collapse(instruction),
            width,
        },
    }
}

fn instruction_effects<'a>(instruction: &DecodedInstruction, isa: &'a ISA) -> &'a [Effect] {
    let instruction_name = &instruction.name;
    &isa.instructions
        .iter()
        .find(|candidate| candidate.name == *instruction_name)
        .unwrap_or_else(|| {
            panic!(
                "Instruction in sequence should match with an instruction in the ISA, but {instruction_name} did not match!"
            )
        })
        .effects
}

fn collect_concrete_memory_writes(
    writes: &mut Vec<((u128, u16), BitWord)>,
    address: BitWord,
    value: BitWord,
    width: u16,
) {
    if width == 8 {
        writes.push(((address.value, 8), BitWord::new(value.value, 8)));
        return;
    }

    assert_eq!(width % 8, 0, "Memory write width must be byte-aligned");
    for byte_index in 0..(width / 8) {
        let byte_address = (address.value + u128::from(byte_index)) & bit_mask(address.width);
        let byte_value = (value.value >> u32::from(byte_index * 8)) & 0xff;
        writes.push(((byte_address, 8), BitWord::new(byte_value, 8)));
    }
}

fn instruction_to_lowered_effects_impl(
    instruction: &DecodedInstruction,
    isa: &ISA,
    previous_effects: &[Effect],
    mut profile: Option<&mut InstructionSeqToEffectsProfile>,
) -> Vec<Effect> {
    let lookup_start = profile.as_ref().map(|_| Instant::now());
    let instruction_effects = instruction_effects(instruction, isa);
    if let (Some(profile), Some(start)) = (profile.as_mut(), lookup_start) {
        profile.instruction_lookup += start.elapsed();
        profile.source_effects += instruction_effects.len();
    }
    let mut lowered_effects = Vec::with_capacity(instruction_effects.len());
    for effect in instruction_effects.iter().cloned() {
        if let Some(profile) = profile.as_mut() {
            match &effect {
                Effect::WriteMemory {
                    guard,
                    address,
                    value,
                    ..
                } => {
                    profile.source_memory_effects += 1;
                    profile.source_expr_nodes +=
                        expr_node_count(guard) + expr_node_count(address) + expr_node_count(value);
                }
                Effect::WriteRegister {
                    guard,
                    register,
                    value,
                } => {
                    profile.source_register_effects += 1;
                    profile.source_expr_nodes +=
                        expr_node_count(guard) + expr_node_count(register) + expr_node_count(value);
                }
            }
        }
        match effect {
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                let lowering_start = profile.as_ref().map(|_| Instant::now());
                let guard = collapse_lower_substitute_profiled(
                    guard,
                    instruction,
                    previous_effects,
                    EffectExprRole::Guard,
                    profile.as_deref_mut(),
                );
                let address = collapse_lower_substitute_profiled(
                    address,
                    instruction,
                    previous_effects,
                    EffectExprRole::Destination,
                    profile.as_deref_mut(),
                );
                let value = collapse_lower_substitute_profiled(
                    value,
                    instruction,
                    previous_effects,
                    EffectExprRole::Value,
                    profile.as_deref_mut(),
                );
                if let (Some(profile), Some(start)) = (profile.as_mut(), lowering_start) {
                    profile.lowering_total += start.elapsed();
                }
                if width == 8 {
                    if let Some(profile) = profile.as_mut() {
                        profile.lowered_memory_effects += 1;
                        profile.lowered_expr_nodes += expr_node_count(&guard)
                            + expr_node_count(&address)
                            + expr_node_count(&value);
                    }
                    lowered_effects.push(Effect::WriteMemory {
                        guard,
                        address,
                        value,
                        width,
                    });
                } else {
                    assert_eq!(width % 8, 0, "Memory write width must be byte-aligned");
                    let address_width = address
                        .expr_width()
                        .expect("Memory address should have established width");
                    for byte_index in 0..(width / 8) {
                        let low = byte_index * 8;
                        let byte_address = byte_address(&address, byte_index, address_width);
                        let byte_value = extract(value.clone(), low + 7, low);
                        if let Some(profile) = profile.as_mut() {
                            profile.lowered_memory_effects += 1;
                            profile.lowered_expr_nodes += expr_node_count(&guard)
                                + expr_node_count(&byte_address)
                                + expr_node_count(&byte_value);
                        }
                        lowered_effects.push(Effect::WriteMemory {
                            guard: guard.clone(),
                            address: byte_address,
                            value: byte_value,
                            width: 8,
                        });
                    }
                }
            }
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                let lowering_start = profile.as_ref().map(|_| Instant::now());
                let guard = collapse_lower_substitute_profiled(
                    guard,
                    instruction,
                    previous_effects,
                    EffectExprRole::Guard,
                    profile.as_deref_mut(),
                );
                let register = collapse_lower_substitute_profiled(
                    register,
                    instruction,
                    previous_effects,
                    EffectExprRole::Destination,
                    profile.as_deref_mut(),
                );
                let value = collapse_lower_substitute_profiled(
                    value,
                    instruction,
                    previous_effects,
                    EffectExprRole::Value,
                    profile.as_deref_mut(),
                );
                if let (Some(profile), Some(start)) = (profile.as_mut(), lowering_start) {
                    profile.lowering_total += start.elapsed();
                    profile.lowered_register_effects += 1;
                    profile.lowered_expr_nodes += expr_node_count(&guard)
                        + expr_node_count(&register)
                        + expr_node_count(&value);
                }
                lowered_effects.push(Effect::WriteRegister {
                    guard,
                    register,
                    value,
                });
            }
        }
    }

    lowered_effects
}

fn collapse_lower_substitute_profiled(
    expr: Expr,
    instruction: &DecodedInstruction,
    previous_effects: &[Effect],
    role: EffectExprRole,
    mut profile: Option<&mut InstructionSeqToEffectsProfile>,
) -> Expr {
    let start = profile.as_ref().map(|_| Instant::now());
    let expr = expr.collapse(instruction);
    if let (Some(profile), Some(start)) = (profile.as_mut(), start) {
        profile.collapse += start.elapsed();
    }

    let start = profile.as_ref().map(|_| Instant::now());
    let expr = lower_memory_reads(expr);
    if let (Some(profile), Some(start)) = (profile.as_mut(), start) {
        profile.lower_memory_reads += start.elapsed();
    }

    let start = profile.as_ref().map(|_| Instant::now());
    let expr = expr.substitute(previous_effects);
    if let (Some(profile), Some(start)) = (profile.as_mut(), start) {
        profile.substitute += start.elapsed();
    }

    let expr = match role {
        EffectExprRole::Guard | EffectExprRole::Destination => {
            let start = profile.as_ref().map(|_| Instant::now());
            let expr = expr.canonicalize();
            if let (Some(profile), Some(start)) = (profile.as_mut(), start) {
                profile.canonicalize += start.elapsed();
            }
            expr
        }
        EffectExprRole::Value => expr,
    };

    expr
}

fn expr_node_count(expr: &Expr) -> usize {
    1 + match expr {
        Expr::Const { .. } | Expr::Operand(_) | Expr::DerivedValue(_) => 0,
        Expr::ReadRegister { register, .. } => expr_node_count(register),
        Expr::ReadMemory { address, .. } => expr_node_count(address),
        Expr::Add(lhs, rhs)
        | Expr::Sub(lhs, rhs)
        | Expr::Mul(lhs, rhs)
        | Expr::And(lhs, rhs)
        | Expr::Or(lhs, rhs)
        | Expr::Xor(lhs, rhs)
        | Expr::ShiftLeft(lhs, rhs)
        | Expr::LogicalShiftRight(lhs, rhs)
        | Expr::ArithmeticShiftRight(lhs, rhs)
        | Expr::RotateRight(lhs, rhs)
        | Expr::Equal(lhs, rhs)
        | Expr::UnsignedLessThan(lhs, rhs)
        | Expr::SignedLessThan(lhs, rhs) => expr_node_count(lhs) + expr_node_count(rhs),
        Expr::Not(value) | Expr::CountOnes(value) => expr_node_count(value),
        Expr::Extract { value, .. }
        | Expr::ZeroExtend { value, .. }
        | Expr::SignExtend { value, .. } => expr_node_count(value),
        Expr::Concat(values) => values.iter().map(expr_node_count).sum(),
        Expr::AddCarryOut {
            lhs, rhs, carry_in, ..
        }
        | Expr::AddOverflow {
            lhs, rhs, carry_in, ..
        }
        | Expr::SubCarryOut {
            lhs,
            rhs,
            borrow_in: carry_in,
            ..
        }
        | Expr::SubOverflow {
            lhs,
            rhs,
            borrow_in: carry_in,
            ..
        } => expr_node_count(lhs) + expr_node_count(rhs) + expr_node_count(carry_in),
        Expr::Select {
            condition,
            when_true,
            when_false,
        } => expr_node_count(condition) + expr_node_count(when_true) + expr_node_count(when_false),
    }
}

fn lower_memory_reads(expr: Expr) -> Expr {
    match expr {
        Expr::ReadMemory { address, width } => {
            let address = lower_memory_reads(*address);
            if width == 8 {
                return read_memory(address, width);
            }

            assert_eq!(width % 8, 0, "Memory read width must be byte-aligned");
            let address_width = address
                .expr_width()
                .expect("Memory address should have established width");
            concat((0..(width / 8)).rev().map(|byte_index| {
                read_memory(byte_address(&address, byte_index, address_width), 8)
            }))
        }
        expr => expr.map_children(lower_memory_reads),
    }
}

fn byte_address(address: &Expr, byte_index: u16, address_width: u16) -> Expr {
    if byte_index == 0 {
        address.clone()
    } else {
        add(address.clone(), constant(byte_index as u128, address_width))
    }
}

/// Given two effects which either both write to the same register or memory, combine
/// their values and guards to create one effect
/// Returns Some(Effect) if the two effects are equivalent writes (ie same location), returns None otherwise
/// # Arguments
/// * `effect_1` - an Effect
/// * `effect_2` - an Effect which takes place sequentially after `effect_1``
fn combine_effects(effect_1: &Effect, effect_2: &Effect) -> Option<Effect> {
    // Let's call these effects a (effect_1) and b (effect_2). a comes before b
    // It is given that effect_1.guard is not always 0
    // The value of the combined effect is as follows:
    // if b.guard -> b.value
    // elif a.guard -> a.value
    // else old value
    // So we can do the following:
    //      1. The new Effect has a guard of a.guard || b.guard
    //      2. The new Effect has a value of b.guard ? b.value : a.value (equivalent to Expr::Select)
    //          - This is the case because (a.guard || b.guard) && !b.guard => a.guard
    // Importantly this process works multiple times (i.e. combine_effects(combine_effects(a, b), c) works)
    // So if now I have a new effect c, it still works to use the exact methodology.
    // We get a new Effect:
    //      guard = a.guard || b.guard || c.guard
    //      value = c.guard ? c.value : (b.guard ? b.value : a.value)
    //          Essentially: if c => c, elif b => b, elif a => a
    // So, the generalized new effect is:
    // Effect {
    //      guard = Or(old_effect.guard, new_effect.guard),
    //      value = Select(new_effect.guard, new_effect.value, old_effect.value)
    // }
    //
    // Importantly there are a few things which can be done in certain cases
    //  1. if effect_2.guard = 0, do nothing
    //  2. if effect_2.guard = 1, return effect_2 as the combined effect
    //  3. if effect_2.guard == effect_1.guard, return effect_2 as the combined effect
    // More generically, if effect_1.guard => effect_2.guard, then effect_2 is the combined effect
    // but that's complicated to check for.
    let memory_effect;
    let guard_1;
    let guard_2;
    let location;
    let value_1;
    let value_2;
    let val_width;
    match effect_1 {
        Effect::WriteMemory {
            guard,
            address,
            value,
            width,
        } => {
            memory_effect = true;
            guard_1 = guard;
            location = address;
            value_1 = value;
            val_width = *width;
        }
        Effect::WriteRegister {
            guard,
            register,
            value,
        } => {
            memory_effect = false;
            guard_1 = guard;
            location = register;
            value_1 = value;
            val_width = value
                .expr_width()
                .expect("Register writes should have established width!");
        }
    }

    // Now make sure effect_2 matches effect_1 and extract values
    match effect_2 {
        Effect::WriteMemory {
            guard,
            address,
            value,
            width,
        } => {
            if !memory_effect {
                return None;
            }
            if location != address {
                // Both must be at the same location to combine
                return None;
            }
            assert_eq!(
                val_width, *width,
                "effect_1 and effect_2 should have same memory write width"
            );

            guard_2 = guard;
            value_2 = value;
        }
        Effect::WriteRegister {
            guard,
            register,
            value,
        } => {
            if memory_effect {
                return None;
            }

            if location != register {
                return None;
            }
            assert_eq!(
                val_width,
                value
                    .expr_width()
                    .expect("Register writes should have established width!"),
                "effect_1 and effect_2 must have the same register write width"
            );

            guard_2 = guard;
            value_2 = value;
        }
    }

    // If effect_2.guard == 1
    if *guard_2 == constant(1, 1) {
        return Some(effect_2.clone());
    }

    // If effect_2.guard == 0
    if *guard_2 == constant(0, 1) {
        return Some(effect_1.clone());
    }

    // If effect_2.guard == effect_1.guard
    if guard_1 == guard_2 {
        return Some(effect_2.clone());
    }

    // Now, construct a new effect
    if memory_effect {
        Some(Effect::WriteMemory {
            guard: or_expr(guard_1.clone(), guard_2.clone()),
            address: location.clone(),
            value: select(guard_2.clone(), value_2.clone(), value_1.clone()),
            width: val_width,
        })
    } else {
        Some(Effect::WriteRegister {
            guard: or_expr(guard_1.clone(), guard_2.clone()),
            register: location.clone(),
            value: select(guard_2.clone(), value_2.clone(), value_1.clone()),
        })
    }
}

// Also this file may perhaps end up with the code to match all the `Effect`s of multiple instructions? or in superoptimization.rs have not decided

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instruction_semantics::{
            Register, add_carry_out, add_overflow, and_expr, arithmetic_shift_right, bool_const,
            count_ones, equal, fixed_register, logical_shift_right, mul, not_expr, read_memory,
            read_register, rotate_right, shift_left, sign_extend, signed_less_than, sub,
            sub_carry_out, sub_overflow, unsigned_less_than, xor_expr, zero_extend,
        },
        isa_specification::{Instruction, InstructionForm, StackDirection, StackPointer},
    };
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    fn decoded(name: &str) -> DecodedInstruction {
        DecodedInstruction {
            name: name.to_owned(),
            form: InstructionForm::new(format!("{name}_form")),
            bits: Vec::new(),
            fields: Vec::new(),
            branch_instruction: None,
            mem_addr: 0,
            static_instruction: false,
            assembly_line: 0,
        }
    }

    fn isa_instruction(name: &str, effects: Vec<Effect>) -> Instruction {
        let mut instruction = Instruction::new(name, 0);
        instruction.effects = effects;
        instruction
    }

    fn reg(register: u8) -> Expr {
        fixed_register(Register(register), 8)
    }

    fn read_reg(register: u8) -> Expr {
        read_register(reg(register), 32)
    }

    fn register_write_value(effects: &[Effect], register: u8) -> &Expr {
        effects
            .iter()
            .find_map(|effect| match effect {
                Effect::WriteRegister {
                    register: effect_register,
                    value,
                    ..
                } if *effect_register == reg(register) => Some(value),
                _ => None,
            })
            .expect("expected register write")
    }

    fn forwarding_condition(guard: Expr, read_identifier: Expr, write_identifier: Expr) -> Expr {
        and_expr(guard, equal(read_identifier, write_identifier))
    }

    fn test_arch_register(
        identifier: u8,
        identifier_width: u8,
        width: u8,
    ) -> ArchitecturalRegister {
        ArchitecturalRegister {
            identifier,
            identifier_width,
            width,
        }
    }

    fn test_isa(registers: Vec<ArchitecturalRegister>, instructions: Vec<Instruction>) -> ISA {
        let sp = test_arch_register(254, 8, 32);
        ISA {
            registers,
            instructions,
            sp: StackPointer {
                register: sp,
                stack_size: 16,
                direction: StackDirection::Downwards,
            },
            pc: test_arch_register(253, 8, 32),
        }
    }

    fn bdd_test_isa() -> ISA {
        test_isa(vec![test_arch_register(0, 1, 1)], vec![])
    }

    fn machine_state(
        registers: &[(u128, BitWord)],
        memory: &[((u128, u16), BitWord)],
    ) -> MachineState {
        MachineState {
            registers: registers.iter().copied().collect(),
            memory: memory.iter().copied().collect(),
        }
    }

    fn machine_state_with_optional_register_and_memory(
        include_register: bool,
        include_memory: bool,
    ) -> MachineState {
        machine_state(
            include_register
                .then_some((0, BitWord::new(0xab, 8)))
                .as_slice(),
            include_memory
                .then_some(((0x20, 8), BitWord::new(0xcd, 8)))
                .as_slice(),
        )
    }

    fn compare_test_sp(direction: StackDirection) -> StackPointer {
        StackPointer {
            register: test_arch_register(254, 8, 32),
            stack_size: 16,
            direction,
        }
    }

    fn compare_test_sp_val() -> u128 {
        0x100
    }

    fn manager_variable_count(manager: &BddManager) -> u32 {
        manager
            .manager_ref
            .with_manager_shared(|manager| manager.num_vars())
    }

    fn bdd_manager_for_width(width: u16) -> BddManager {
        BddManager::from_exprs(
            constant(0, width),
            constant(0, width),
            &test_isa(vec![], vec![]),
        )
    }

    fn bit_mask(width: u16) -> u128 {
        if width == 128 {
            !0
        } else {
            (1u128 << width) - 1
        }
    }

    fn signed_value(value: u128, width: u16) -> i128 {
        let value = value & bit_mask(width);
        if width == 128 {
            value as i128
        } else {
            let sign = 1u128 << (width - 1);
            if value & sign == 0 {
                value as i128
            } else {
                (value as i128) - (1i128 << width as u32)
            }
        }
    }

    fn const_expr_oracle(expr: Expr) -> (u128, u16) {
        match expr
            .clone()
            .collapse_and_canonicalize(&decoded("CONST_ORACLE"))
        {
            Expr::Const { value, width } => (value & bit_mask(width), width),
            lowered => panic!("constant-only expression did not collapse to const: {lowered:?}"),
        }
    }

    fn assert_const_expr_lowering_with_manager(
        manager: &BddManager,
        expr: Expr,
        expected_value: u128,
        expected_width: u16,
    ) {
        let (oracle_value, oracle_width) = const_expr_oracle(expr.clone());
        assert_eq!(oracle_width, expected_width, "oracle width for {expr:?}");
        assert_eq!(
            oracle_value,
            expected_value & bit_mask(expected_width),
            "manual expectation disagrees with const oracle for {expr:?}"
        );

        let lowered = manager.lower_expression(&expr, LEFT_EXPR);

        assert_eq!(lowered.bits.len(), oracle_width as usize);
        assert_eq!(
            constant_bdd_word_value(&manager, &lowered),
            oracle_value,
            "BDD lowering disagrees with const oracle for {expr:?}"
        );
    }

    fn assert_const_expr_lowering(expr: Expr, expected_value: u128, expected_width: u16) {
        let manager = bdd_manager_for_width(expected_width);
        assert_const_expr_lowering_with_manager(&manager, expr, expected_value, expected_width);
    }

    fn constant_bdd_word_value(manager: &BddManager, word: &BddWord) -> u128 {
        word.bits
            .iter()
            .enumerate()
            .map(|(bit, function)| {
                if *function == manager.true_fn {
                    1u128 << bit
                } else {
                    assert!(
                        *function == manager.false_fn,
                        "expected a constant BCDD bit"
                    );
                    0
                }
            })
            .sum()
    }

    fn eval_bdd_word(word: &BddWord, assignment: &[(u32, bool)]) -> u128 {
        word.bits
            .iter()
            .enumerate()
            .map(|(bit, function)| {
                if function.eval(assignment.iter().copied()) {
                    1u128 << bit
                } else {
                    0
                }
            })
            .sum()
    }

    fn bdd_compare_test_isa(width: u8) -> ISA {
        test_isa(
            vec![
                test_arch_register(0, 8, width),
                test_arch_register(1, 8, width),
                test_arch_register(2, 8, width),
            ],
            vec![],
        )
    }

    fn equivalence_test_isa(width: u8, instructions: Vec<Instruction>) -> ISA {
        test_isa(
            (0u8..8)
                .map(|identifier| test_arch_register(identifier, 8, width))
                .collect(),
            instructions,
        )
    }

    fn decoded_sequence(names: &[&str]) -> Program {
        Program::from_instructions(
            names.iter().map(|name| decoded(name)).collect(),
            names.len(),
        )
    }

    fn assert_bdd_compare_equal(left: Expr, right: Expr, isa: &ISA) {
        let mut manager = BddManager::from_exprs(left.canonicalize(), right.canonicalize(), isa);

        assert_eq!(
            manager.compare().expect("compare should allocate"),
            BddEquality::Equal
        );
    }

    fn assert_bdd_compare_unequal_counterexample(left: Expr, right: Expr, isa: &ISA) {
        let left = left.canonicalize();
        let right = right.canonicalize();
        let mut manager = BddManager::from_exprs(left.clone(), right.clone(), isa);

        let result = manager.compare().expect("compare should allocate");
        let BddEquality::Unequal(state) = result else {
            panic!("expected expressions to be unequal");
        };

        let left_value =
            evaluate_expr(&left, &state).expect("counterexample should evaluate left expr");
        let right_value =
            evaluate_expr(&right, &state).expect("counterexample should evaluate right expr");
        assert_eq!(
            left_value.width, right_value.width,
            "counterexample sides should have matching widths"
        );
        assert_ne!(
            left_value.value, right_value.value,
            "returned state should be an actual counterexample"
        );
    }

    #[test]
    fn machine_state_memory_cost_counts_hamming_distance_for_shared_writes() {
        let left = machine_state(
            &[],
            &[
                ((0x20, 8), BitWord::new(0b1010_1010, 8)),
                ((0x40, 4), BitWord::new(0b1100, 4)),
            ],
        );
        let right = machine_state(
            &[],
            &[
                ((0x20, 8), BitWord::new(0b1111_0000, 8)),
                ((0x40, 4), BitWord::new(0b0101, 4)),
            ],
        );

        assert_eq!(
            left.compute_memory_cost(
                &right,
                &compare_test_sp(StackDirection::Downwards),
                compare_test_sp_val()
            ),
            6
        );
    }

    #[test]
    fn machine_state_memory_cost_counts_missing_write_as_all_bits_plus_penalty() {
        let left = machine_state(&[], &[((0x20, 8), BitWord::new(0xab, 8))]);
        let right = MachineState::default();

        assert_eq!(
            left.compute_memory_cost(
                &right,
                &compare_test_sp(StackDirection::Downwards),
                compare_test_sp_val()
            ),
            8 + WEIGHT_EXTRA_WRITE
        );
        assert_eq!(
            right.compute_memory_cost(
                &left,
                &compare_test_sp(StackDirection::Downwards),
                compare_test_sp_val()
            ),
            8 + WEIGHT_EXTRA_WRITE
        );
    }

    #[test]
    fn machine_state_register_cost_counts_hamming_distance_for_same_register() {
        let left = machine_state(&[(0, BitWord::new(0b1010_1010, 8))], &[]);
        let right = machine_state(&[(0, BitWord::new(0b1111_0000, 8))], &[]);
        let live_out = [test_arch_register(0, 8, 8)];

        assert_eq!(left.compute_register_cost(&right, &live_out), 4);
    }

    #[test]
    fn machine_state_register_cost_rewards_matching_value_in_different_register_with_penalties() {
        let left = machine_state(&[(0, BitWord::new(0xab, 8))], &[]);
        let right = machine_state(&[(1, BitWord::new(0xab, 8))], &[]);
        let live_out = [test_arch_register(0, 8, 8), test_arch_register(1, 8, 8)];

        assert_eq!(
            left.compute_register_cost(&right, &live_out),
            WEIGHT_REGISTER_MISMATCH + (2 * (8 + WEIGHT_EXTRA_WRITE))
        );
    }

    #[test]
    fn machine_state_register_cost_counts_missing_write_as_all_bits_plus_penalty() {
        let left = machine_state(&[(0, BitWord::new(0xab, 8))], &[]);
        let right = MachineState::default();
        let live_out = [test_arch_register(0, 8, 8)];

        assert_eq!(
            left.compute_register_cost(&right, &live_out),
            8 + WEIGHT_EXTRA_WRITE
        );
        assert_eq!(
            right.compute_register_cost(&left, &live_out),
            8 + WEIGHT_EXTRA_WRITE
        );
    }

    #[test]
    fn machine_state_register_cost_ignores_non_live_out_other_scratch_registers() {
        let left = MachineState::default();
        let right = machine_state(&[(1, BitWord::new(0xab, 8))], &[]);

        assert_eq!(left.compute_register_cost(&right, &[]), 0);
    }

    #[test]
    fn machine_state_register_cost_ignores_non_live_out_self_registers() {
        let left = machine_state(&[(1, BitWord::new(0xab, 8))], &[]);
        let right = MachineState::default();

        assert_eq!(left.compute_register_cost(&right, &[]), 0);
    }

    #[test]
    fn machine_state_register_cost_includes_live_out_other_registers() {
        let left = MachineState::default();
        let right = machine_state(&[(1, BitWord::new(0xab, 8))], &[]);
        let live_out = [test_arch_register(1, 8, 8)];

        assert_eq!(
            left.compute_register_cost(&right, &live_out),
            8 + WEIGHT_EXTRA_WRITE
        );
    }

    #[test]
    fn machine_state_register_cost_only_counts_live_out_registers_present_in_both_states() {
        let left = machine_state(
            &[
                (0, BitWord::new(0b1010_1010, 8)),
                (1, BitWord::new(0b1100_1100, 8)),
            ],
            &[],
        );
        let right = machine_state(
            &[
                (0, BitWord::new(0b0101_0101, 8)),
                (1, BitWord::new(0b1111_0000, 8)),
            ],
            &[],
        );
        let live_out = [test_arch_register(1, 8, 8)];

        assert_eq!(left.compute_register_cost(&right, &live_out), 4);
    }

    #[test]
    fn machine_state_memory_cost_ignores_other_stack_scratch_unless_live_in_self() {
        let stack_memory = [((0xf8, 8), BitWord::new(0xab, 8))];
        let left = MachineState::default();
        let right = machine_state(&[], &stack_memory);
        let sp = compare_test_sp(StackDirection::Downwards);

        assert_eq!(
            left.compute_memory_cost(&right, &sp, compare_test_sp_val()),
            0
        );

        let left = machine_state(&[], &stack_memory);
        let right = MachineState::default();
        assert_eq!(
            left.compute_memory_cost(&right, &sp, compare_test_sp_val()),
            8 + WEIGHT_EXTRA_WRITE
        );
    }

    #[test]
    fn machine_state_costs_handle_all_empty_register_and_memory_combinations() {
        for self_has_register in [false, true] {
            for other_has_register in [false, true] {
                for self_has_memory in [false, true] {
                    for other_has_memory in [false, true] {
                        let left = machine_state_with_optional_register_and_memory(
                            self_has_register,
                            self_has_memory,
                        );
                        let right = machine_state_with_optional_register_and_memory(
                            other_has_register,
                            other_has_memory,
                        );

                        let expected_register_cost = 0;
                        let expected_memory_cost = match (self_has_memory, other_has_memory) {
                            (false, false) | (true, true) => 0,
                            (true, false) | (false, true) => 8 + WEIGHT_EXTRA_WRITE,
                        };

                        assert_eq!(
                            left.compute_register_cost(&right, &[]),
                            expected_register_cost,
                            "register cost for self_has_register={self_has_register}, other_has_register={other_has_register}, self_has_memory={self_has_memory}, other_has_memory={other_has_memory}",
                        );
                        assert_eq!(
                            left.compute_memory_cost(
                                &right,
                                &compare_test_sp(StackDirection::Downwards),
                                compare_test_sp_val()
                            ),
                            expected_memory_cost,
                            "memory cost for self_has_register={self_has_register}, other_has_register={other_has_register}, self_has_memory={self_has_memory}, other_has_memory={other_has_memory}",
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn machine_state_compare_adds_memory_and_register_costs() {
        let left = machine_state(
            &[(0, BitWord::new(0b1010, 4))],
            &[((0x20, 4), BitWord::new(0b1100, 4))],
        );
        let right = machine_state(
            &[(0, BitWord::new(0b0011, 4))],
            &[((0x20, 4), BitWord::new(0b0101, 4))],
        );

        assert_eq!(
            left.compare(
                &right,
                &[test_arch_register(0, 8, 4)],
                &compare_test_sp(StackDirection::Downwards),
                compare_test_sp_val()
            ),
            4
        );
    }

    #[test]
    fn effect_canonicalize_normalizes_destinations_guards_and_values() {
        let guard = or_expr(read_register(reg(1), 1), bool_const(false));
        let address = add(constant(1, 8), reg(0));
        let value = xor_expr(read_register(reg(2), 8), constant(0, 8));

        assert_eq!(
            Effect::write_memory_if(guard.clone(), address.clone(), value.clone(), 8)
                .canonicalize(),
            Effect::write_memory_if(
                guard.canonicalize(),
                address.canonicalize(),
                value.canonicalize(),
                8,
            )
        );

        let register = add(reg(3), constant(0, 8));
        let register_value = add(read_register(reg(4), 8), constant(0, 8));
        assert_eq!(
            Effect::write_register(register.clone(), register_value.clone()).canonicalize(),
            Effect::write_register(register.canonicalize(), register_value.canonicalize())
        );
    }

    #[test]
    fn compare_reports_equal_for_equivalent_expression_identities() {
        let isa = bdd_compare_test_isa(4);
        let x = read_register(reg(0), 4);
        let y = read_register(reg(1), 4);

        assert_bdd_compare_equal(add(x.clone(), constant(0, 4)), x.clone(), &isa);
        assert_bdd_compare_equal(mul(x.clone(), constant(1, 4)), x.clone(), &isa);
        assert_bdd_compare_equal(add(x.clone(), y.clone()), add(y.clone(), x.clone()), &isa);
        assert_bdd_compare_equal(
            zero_extend(extract(x.clone(), 2, 0), 4),
            and_expr(x, constant(0b0111, 4)),
            &isa,
        );
    }

    #[test]
    fn compare_reports_unequal_and_returns_real_counterexamples() {
        let isa = bdd_compare_test_isa(4);
        let x = read_register(reg(0), 4);
        let y = read_register(reg(1), 4);

        assert_bdd_compare_unequal_counterexample(
            and_expr(x.clone(), constant(0b1110, 4)),
            x.clone(),
            &isa,
        );
        assert_bdd_compare_unequal_counterexample(
            logical_shift_right(shift_left(x.clone(), constant(1, 4)), constant(1, 4)),
            x.clone(),
            &isa,
        );
        assert_bdd_compare_unequal_counterexample(
            unsigned_less_than(x.clone(), y.clone()),
            signed_less_than(x.clone(), y.clone()),
            &isa,
        );
    }

    #[test]
    fn compare_counterexamples_work_for_expressions_equal_on_many_values() {
        let isa = bdd_compare_test_isa(8);
        let x = read_register(reg(0), 8);
        let memory = read_memory(x.clone(), 8);

        assert_bdd_compare_unequal_counterexample(
            and_expr(memory.clone(), constant(0xfe, 8)),
            memory,
            &isa,
        );
        assert_bdd_compare_unequal_counterexample(
            zero_extend(extract(x.clone(), 6, 0), 8),
            x,
            &isa,
        );
    }

    #[test]
    fn compare_covers_canonicalized_expr_forms() {
        let isa = bdd_compare_test_isa(4);
        let x = read_register(reg(0), 4);
        let y = read_register(reg(1), 4);
        let z = read_register(reg(2), 4);
        let memory_at_x = read_memory(x.clone(), 4);

        let cases = vec![
            ("const", constant(0b1010, 4), constant(0b1010, 4)),
            ("fixed-register operand", reg(2), constant(2, 8)),
            ("read-register", x.clone(), add(x.clone(), constant(0, 4))),
            (
                "read-memory",
                memory_at_x.clone(),
                add(memory_at_x.clone(), constant(0, 4)),
            ),
            ("add", add(x.clone(), y.clone()), add(y.clone(), x.clone())),
            ("sub", sub(x.clone(), constant(0, 4)), x.clone()),
            ("mul", mul(x.clone(), constant(1, 4)), x.clone()),
            ("and", and_expr(x.clone(), constant(0b1111, 4)), x.clone()),
            ("or", or_expr(x.clone(), constant(0, 4)), x.clone()),
            ("xor", xor_expr(x.clone(), constant(0, 4)), x.clone()),
            ("not", not_expr(not_expr(x.clone())), x.clone()),
            (
                "shift-left",
                shift_left(x.clone(), constant(0, 4)),
                x.clone(),
            ),
            (
                "logical-shift-right",
                logical_shift_right(x.clone(), constant(0, 4)),
                x.clone(),
            ),
            (
                "arithmetic-shift-right",
                arithmetic_shift_right(x.clone(), constant(0, 4)),
                x.clone(),
            ),
            (
                "rotate-right",
                rotate_right(x.clone(), constant(0, 4)),
                x.clone(),
            ),
            ("equal", equal(x.clone(), x.clone()), bool_const(true)),
            (
                "unsigned-less-than",
                unsigned_less_than(x.clone(), x.clone()),
                bool_const(false),
            ),
            (
                "signed-less-than",
                signed_less_than(x.clone(), x.clone()),
                bool_const(false),
            ),
            ("extract", extract(x.clone(), 3, 0), x.clone()),
            (
                "concat",
                concat([extract(x.clone(), 3, 2), extract(x.clone(), 1, 0)]),
                x.clone(),
            ),
            (
                "zero-extend",
                zero_extend(x.clone(), 8),
                concat([constant(0, 4), x.clone()]),
            ),
            (
                "sign-extend",
                sign_extend(x.clone(), 8),
                sign_extend(x.clone(), 8),
            ),
            ("count-ones", count_ones(x.clone()), count_ones(x.clone())),
            (
                "add-carry-out",
                add_carry_out(x.clone(), y.clone(), bool_const(false), 4),
                add_carry_out(y.clone(), x.clone(), bool_const(false), 4),
            ),
            (
                "add-overflow",
                add_overflow(x.clone(), y.clone(), bool_const(false), 4),
                add_overflow(y.clone(), x.clone(), bool_const(false), 4),
            ),
            (
                "sub-carry-out",
                sub_carry_out(x.clone(), y.clone(), bool_const(false), 4),
                sub_carry_out(x.clone(), y.clone(), bool_const(false), 4),
            ),
            (
                "sub-overflow",
                sub_overflow(x.clone(), y.clone(), bool_const(false), 4),
                sub_overflow(x.clone(), y.clone(), bool_const(false), 4),
            ),
            (
                "select",
                select(bool_const(true), x.clone(), y.clone()),
                x.clone(),
            ),
            (
                "nested primitive mix",
                add(
                    and_expr(
                        read_memory(add(x.clone(), y.clone()), 4),
                        not_expr(z.clone()),
                    ),
                    count_ones(or_expr(x.clone(), y.clone())),
                ),
                add(
                    count_ones(or_expr(y.clone(), x.clone())),
                    and_expr(
                        read_memory(add(y.clone(), x.clone()), 4),
                        not_expr(z.clone()),
                    ),
                ),
            ),
        ];

        for (name, left, right) in cases {
            let mut manager =
                BddManager::from_exprs(left.canonicalize(), right.canonicalize(), &isa);

            assert_eq!(
                manager.compare().expect("compare should allocate"),
                BddEquality::Equal,
                "{name}"
            );
        }
    }

    #[test]
    fn compare_covers_multiply_and_manual_bit_level_arithmetic() {
        let isa_4 = bdd_compare_test_isa(4);
        let x = read_register(reg(0), 4);
        let y = read_register(reg(1), 4);

        assert_bdd_compare_equal(
            mul(add(x.clone(), constant(1, 4)), y.clone()),
            mul(y.clone(), add(x.clone(), constant(1, 4))),
            &isa_4,
        );
        assert_bdd_compare_equal(
            mul(x.clone(), constant(2, 4)),
            shift_left(x.clone(), constant(1, 4)),
            &isa_4,
        );
        assert_bdd_compare_equal(
            mul(x.clone(), constant(3, 4)),
            add(shift_left(x.clone(), constant(1, 4)), x.clone()),
            &isa_4,
        );
        assert_bdd_compare_equal(
            mul(x.clone(), constant(5, 4)),
            add(shift_left(x.clone(), constant(2, 4)), x.clone()),
            &isa_4,
        );
        assert_bdd_compare_equal(
            mul(add(x.clone(), y.clone()), constant(2, 4)),
            shift_left(add(y.clone(), x.clone()), constant(1, 4)),
            &isa_4,
        );
        assert_bdd_compare_unequal_counterexample(
            mul(x.clone(), constant(3, 4)),
            shift_left(x.clone(), constant(1, 4)),
            &isa_4,
        );

        let isa_2 = bdd_compare_test_isa(2);
        let a = read_register(reg(0), 2);
        let b = read_register(reg(1), 2);
        let a0 = extract(a.clone(), 0, 0);
        let a1 = extract(a.clone(), 1, 1);
        let b0 = extract(b.clone(), 0, 0);
        let b1 = extract(b.clone(), 1, 1);
        let low_sum = xor_expr(a0.clone(), b0.clone());
        let carry = and_expr(a0, b0);
        let high_sum = xor_expr(xor_expr(a1, b1), carry);
        let manual_adder = concat([high_sum, low_sum]);

        assert_bdd_compare_equal(add(a.clone(), b.clone()), manual_adder, &isa_2);
    }

    #[test]
    fn compare_complex_nested_expressions_return_real_counterexamples() {
        let isa = bdd_compare_test_isa(4);
        let x = read_register(reg(0), 4);
        let y = read_register(reg(1), 4);
        let memory_at_sum = read_memory(add(x.clone(), y.clone()), 4);

        assert_bdd_compare_unequal_counterexample(
            count_ones(and_expr(memory_at_sum.clone(), not_expr(x.clone()))),
            count_ones(and_expr(memory_at_sum.clone(), x.clone())),
            &isa,
        );
        assert_bdd_compare_unequal_counterexample(
            rotate_right(
                add(shift_left(x.clone(), constant(1, 4)), y.clone()),
                constant(1, 4),
            ),
            logical_shift_right(
                add(shift_left(x.clone(), constant(1, 4)), y.clone()),
                constant(1, 4),
            ),
            &isa,
        );
        assert_bdd_compare_unequal_counterexample(
            select(
                equal(extract(x.clone(), 0, 0), constant(0, 1)),
                y.clone(),
                x.clone(),
            ),
            y,
            &isa,
        );
    }

    #[test]
    #[ignore = "stress test: intentionally builds an unrealistically large BDD"]
    fn stress_constructs_unrealistically_large_symbolic_bdd() {
        let width = 96;
        let isa = bdd_compare_test_isa(width as u8);
        let x = read_register(reg(0), width);
        let y = read_register(reg(1), width);
        let z = read_register(reg(2), width);
        let mut expr = mul(
            add(x.clone(), rotate_right(y.clone(), constant(13, width))),
            add(z.clone(), constant(0x9e37, width)),
        );

        for round in 0..6 {
            let round_constant = constant(0x1001 + round, width);
            let mixed_xy = mul(expr, add(y.clone(), round_constant));
            let mixed_xz = rotate_right(
                mul(add(x.clone(), constant(round + 1, width)), z.clone()),
                constant((round * 7 + 3) % width as u128, width),
            );
            expr = add(mixed_xy, mixed_xz);
        }

        let mut manager = BddManager::from_exprs(expr, constant(0, width), &isa);
        let comparison =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| manager.compare()));

        match comparison {
            Ok(Ok(_)) => {}
            Ok(Err(_)) => panic!("BDD allocation failed during stress construction"),
            Err(_) => panic!("BDD stress construction panicked"),
        }
    }

    #[test]
    fn compare_replacement_of_right_expr_updates_equality_result() {
        let isa = bdd_compare_test_isa(4);
        let x = read_register(reg(0), 4);
        let equivalent = add(x.clone(), constant(0, 4)).canonicalize();
        let unequal = and_expr(x.clone(), constant(0b1110, 4)).canonicalize();

        let mut manager = BddManager::from_exprs(x.clone().canonicalize(), equivalent, &isa);
        assert_eq!(
            manager.compare().expect("initial compare should allocate"),
            BddEquality::Equal
        );

        manager.replace_right_expr(unequal.clone());
        let BddEquality::Unequal(state) = manager
            .compare()
            .expect("replacement compare should allocate")
        else {
            panic!("replacement should make expressions unequal");
        };
        let left_value = evaluate_expr(&x.clone().canonicalize(), &state)
            .expect("counterexample should evaluate left");
        let right_value =
            evaluate_expr(&unequal, &state).expect("counterexample should evaluate right");
        assert_ne!(left_value.value, right_value.value);

        manager.replace_right_expr(x.clone().canonicalize());
        assert_eq!(
            manager.compare().expect("final compare should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn equivalence_manager_compares_equivalent_register_sequences() {
        let r0 = read_register(reg(0), 4);
        let r1 = read_register(reg(1), 4);
        let r2 = read_register(reg(2), 4);
        let isa = equivalence_test_isa(
            4,
            vec![
                isa_instruction(
                    "SUM_R0_R1_R2",
                    vec![Effect::write_register(reg(0), add(r1.clone(), r2.clone()))],
                ),
                isa_instruction(
                    "SUM_R0_R2_R1",
                    vec![Effect::write_register(reg(0), add(r2.clone(), r1.clone()))],
                ),
                isa_instruction(
                    "TRIPLE_R3_R0_WITH_MUL",
                    vec![Effect::write_register(
                        reg(3),
                        mul(r0.clone(), constant(3, 4)),
                    )],
                ),
                isa_instruction(
                    "TRIPLE_R3_R0_WITH_SHIFT_ADD",
                    vec![Effect::write_register(
                        reg(3),
                        add(shift_left(r0.clone(), constant(1, 4)), r0),
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["SUM_R0_R1_R2", "TRIPLE_R3_R0_WITH_MUL"]);
        let right = decoded_sequence(&["SUM_R0_R2_R1", "TRIPLE_R3_R0_WITH_SHIFT_ADD"]);

        let mut manager = EquivalenceManager::from_instructions(&left, &right, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("instruction comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn equivalence_manager_returns_counterexample_for_different_register_sequence() {
        let r0 = read_register(reg(0), 4);
        let r1 = read_register(reg(1), 4);
        let r2 = read_register(reg(2), 4);
        let isa = equivalence_test_isa(
            4,
            vec![
                isa_instruction(
                    "SUM_R0_R1_R2",
                    vec![Effect::write_register(reg(0), add(r1.clone(), r2.clone()))],
                ),
                isa_instruction(
                    "TRIPLE_R3_R0_WITH_MUL",
                    vec![Effect::write_register(
                        reg(3),
                        mul(r0.clone(), constant(3, 4)),
                    )],
                ),
                isa_instruction(
                    "DOUBLE_R3_R0_WITH_SHIFT",
                    vec![Effect::write_register(
                        reg(3),
                        shift_left(r0, constant(1, 4)),
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["SUM_R0_R1_R2", "TRIPLE_R3_R0_WITH_MUL"]);
        let right = decoded_sequence(&["SUM_R0_R1_R2", "DOUBLE_R3_R0_WITH_SHIFT"]);

        let mut manager = EquivalenceManager::from_instructions(&left, &right, &isa);

        let result = manager
            .compare_instructions()
            .expect("instruction comparison should allocate");
        let BddEquality::Unequal(state) = result else {
            panic!("different instruction sequence should produce a counterexample");
        };
        assert!(
            !state.registers.is_empty(),
            "counterexample should include the register state that separates the sequences"
        );
    }

    #[test]
    fn equivalence_manager_compares_guarded_write_to_explicit_select() {
        let r0 = read_register(reg(0), 4);
        let r1 = read_register(reg(1), 4);
        let r2 = read_register(reg(2), 4);
        let guard = unsigned_less_than(r1, r2);
        let isa = equivalence_test_isa(
            4,
            vec![
                isa_instruction(
                    "GUARDED_WRITE_R0",
                    vec![Effect::write_register_if(
                        guard.clone(),
                        reg(0),
                        constant(0b1010, 4),
                    )],
                ),
                isa_instruction(
                    "EXPLICIT_SELECT_WRITE_R0",
                    vec![Effect::write_register(
                        reg(0),
                        select(guard, constant(0b1010, 4), r0),
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["GUARDED_WRITE_R0"]);
        let right = decoded_sequence(&["EXPLICIT_SELECT_WRITE_R0"]);

        let mut manager = EquivalenceManager::from_instructions(&left, &right, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("instruction comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn equivalence_manager_matches_canonicalized_effect_destinations() {
        let r1 = read_register(reg(1), 8);
        let base = constant(0x20, 8);
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "LEFT_CANONICAL_DESTINATIONS",
                    vec![
                        Effect::write_register(add(reg(0), constant(0, 8)), r1.clone()),
                        Effect::write_memory(
                            add(constant(1, 8), base.clone()),
                            xor_expr(r1.clone(), constant(0, 8)),
                            8,
                        ),
                    ],
                ),
                isa_instruction(
                    "RIGHT_CANONICAL_DESTINATIONS",
                    vec![
                        Effect::write_register(reg(0), add(r1.clone(), constant(0, 8))),
                        Effect::write_memory(add(base, constant(1, 8)), r1, 8),
                    ],
                ),
            ],
        );
        let left = decoded_sequence(&["LEFT_CANONICAL_DESTINATIONS"]);
        let right = decoded_sequence(&["RIGHT_CANONICAL_DESTINATIONS"]);

        let mut manager = EquivalenceManager::from_instructions(&left, &right, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("canonicalized destination comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn equivalence_manager_canonicalizes_values_before_bdd_lowering() {
        let r0 = read_register(reg(0), 4);
        let isa = equivalence_test_isa(
            4,
            vec![
                isa_instruction(
                    "WRITE_R0_DIRECT",
                    vec![Effect::write_register(reg(0), r0.clone())],
                ),
                isa_instruction(
                    "WRITE_R0_UNCANONICAL",
                    vec![Effect::write_register(
                        reg(0),
                        Expr::Sub(
                            Box::new(or_expr(r0, constant(0, 4))),
                            Box::new(constant(0, 4)),
                        ),
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["WRITE_R0_DIRECT"]);
        let right = decoded_sequence(&["WRITE_R0_UNCANONICAL"]);

        let mut manager = EquivalenceManager::from_instructions(&left, &right, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("canonicalized value comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn equivalence_manager_from_left_then_replace_right_register_sequences() {
        let r0 = read_register(reg(0), 4);
        let r1 = read_register(reg(1), 4);
        let r2 = read_register(reg(2), 4);
        let isa = equivalence_test_isa(
            4,
            vec![
                isa_instruction(
                    "SUM_R0_R1_R2",
                    vec![Effect::write_register(reg(0), add(r1.clone(), r2.clone()))],
                ),
                isa_instruction(
                    "SUM_R0_R2_R1",
                    vec![Effect::write_register(reg(0), add(r2, r1))],
                ),
                isa_instruction(
                    "TRIPLE_R3_R0_WITH_MUL",
                    vec![Effect::write_register(
                        reg(3),
                        mul(r0.clone(), constant(3, 4)),
                    )],
                ),
                isa_instruction(
                    "TRIPLE_R3_R0_WITH_SHIFT_ADD",
                    vec![Effect::write_register(
                        reg(3),
                        add(shift_left(r0.clone(), constant(1, 4)), r0.clone()),
                    )],
                ),
                isa_instruction(
                    "DOUBLE_R3_R0_WITH_SHIFT",
                    vec![Effect::write_register(
                        reg(3),
                        shift_left(r0, constant(1, 4)),
                    )],
                ),
            ],
        );
        let original = decoded_sequence(&["SUM_R0_R1_R2", "TRIPLE_R3_R0_WITH_MUL"]);
        let equivalent = decoded_sequence(&["SUM_R0_R2_R1", "TRIPLE_R3_R0_WITH_SHIFT_ADD"]);
        let different = decoded_sequence(&["SUM_R0_R1_R2", "DOUBLE_R3_R0_WITH_SHIFT"]);
        let mut manager = EquivalenceManager::from_left_instruction(&original, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("initial instruction comparison should allocate"),
            BddEquality::Equal
        );

        manager.replace_right_instruction(&equivalent);
        assert_eq!(
            manager
                .compare_instructions()
                .expect("equivalent replacement should allocate"),
            BddEquality::Equal
        );

        manager.replace_right_instruction(&different);
        assert!(
            matches!(
                manager
                    .compare_instructions()
                    .expect("different replacement should allocate"),
                BddEquality::Unequal(_)
            ),
            "different replacement should make the instruction sequences unequal"
        );

        manager.replace_right_instruction(&original);
        assert_eq!(
            manager
                .compare_instructions()
                .expect("restored replacement should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    #[should_panic(expected = "Right instruction sequence is missing effect writing")]
    fn equivalence_manager_from_instructions_rejects_missing_right_effect() {
        let isa = equivalence_test_isa(
            4,
            vec![
                isa_instruction(
                    "WRITE_R0_AND_R3",
                    vec![
                        Effect::write_register(reg(0), constant(1, 4)),
                        Effect::write_register(reg(3), constant(2, 4)),
                    ],
                ),
                isa_instruction(
                    "WRITE_ONLY_R0",
                    vec![Effect::write_register(reg(0), constant(1, 4))],
                ),
            ],
        );
        let left = decoded_sequence(&["WRITE_R0_AND_R3"]);
        let right = decoded_sequence(&["WRITE_ONLY_R0"]);

        let _ = EquivalenceManager::from_instructions(&left, &right, &isa);
    }

    #[test]
    #[should_panic(expected = "Right instruction sequence is missing effect writing")]
    fn equivalence_manager_replace_right_instruction_rejects_missing_left_effect() {
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "STORE_A",
                    vec![Effect::write_memory(
                        constant(0x20, 8),
                        constant(0xa5, 8),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE_B",
                    vec![Effect::write_memory(
                        constant(0x30, 8),
                        constant(0x5a, 8),
                        8,
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["STORE_A"]);
        let missing_left_effect = decoded_sequence(&["STORE_B"]);
        let mut manager = EquivalenceManager::from_left_instruction(&left, &isa);

        manager.replace_right_instruction(&missing_left_effect);
    }

    #[test]
    fn equivalence_manager_compares_lowered_memory_write_sequences() {
        let address = constant(0x20, 8);
        let value = constant(0xbeef, 16);
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "STORE16",
                    vec![Effect::write_memory(address.clone(), value.clone(), 16)],
                ),
                isa_instruction(
                    "STORE16_LOW_BYTE",
                    vec![Effect::write_memory(
                        address.clone(),
                        extract(value.clone(), 7, 0),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE16_HIGH_BYTE",
                    vec![Effect::write_memory(
                        add(address.clone(), constant(1, 8)),
                        extract(value, 15, 8),
                        8,
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["STORE16"]);
        let right = decoded_sequence(&["STORE16_LOW_BYTE", "STORE16_HIGH_BYTE"]);

        let mut manager = EquivalenceManager::from_instructions(&left, &right, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("memory instruction comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn z3_equivalence_manager_compares_register_effects() {
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "WRITE_R0_ONE",
                    vec![Effect::write_register(reg(0), constant(1, 8))],
                ),
                isa_instruction(
                    "WRITE_R0_ONE_AGAIN",
                    vec![Effect::write_register(reg(0), constant(1, 8))],
                ),
                isa_instruction(
                    "WRITE_R0_TWO",
                    vec![Effect::write_register(reg(0), constant(2, 8))],
                ),
            ],
        );
        let left = decoded_sequence(&["WRITE_R0_ONE"]);
        let equal_right = decoded_sequence(&["WRITE_R0_ONE_AGAIN"]);
        let unequal_right = decoded_sequence(&["WRITE_R0_TWO"]);
        let mut manager = Z3EquivalenceManager::from_instructions(&left, &equal_right, &isa);

        assert_eq!(manager.compare_instructions(), BddEquality::Equal);

        manager.replace_right_instruction(&unequal_right);
        let BddEquality::Unequal(counterexample) = manager.compare_instructions() else {
            panic!("expected Z3 to find a register counterexample");
        };
        assert_eq!(
            execute_program_concrete(&left, &isa, &counterexample).registers[&0].value,
            1
        );
        assert_eq!(
            execute_program_concrete(&unequal_right, &isa, &counterexample).registers[&0].value,
            2
        );
    }

    #[test]
    fn z3_equivalence_manager_observes_only_live_out_registers() {
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "WRITE_R1_ONE",
                    vec![Effect::write_register(reg(1), constant(1, 8))],
                ),
                isa_instruction(
                    "WRITE_R1_TWO",
                    vec![Effect::write_register(reg(1), constant(2, 8))],
                ),
            ],
        );
        let left = decoded_sequence(&["WRITE_R1_ONE"]);
        let right = decoded_sequence(&["WRITE_R1_TWO"]);

        let mut scratch_manager = Z3EquivalenceManager::from_instructions_with_live_out_registers(
            &left,
            &right,
            &isa,
            vec![],
        );
        assert_eq!(scratch_manager.compare_instructions(), BddEquality::Equal);

        let mut live_out_manager = Z3EquivalenceManager::from_instructions_with_live_out_registers(
            &left,
            &right,
            &isa,
            vec![test_arch_register(1, 8, 8)],
        );
        assert!(matches!(
            live_out_manager.compare_instructions(),
            BddEquality::Unequal(_)
        ));
    }

    #[test]
    fn z3_equivalence_manager_uses_stack_scratch_memory_policy() {
        let sp = Expr::ReadRegister {
            register: Box::new(fixed_register(Register(254), 8)),
            width: 32,
        };
        let stack_scratch_address = sub(sp, constant(4, 32));
        let arbitrary_address = read_reg(0);
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction("NOP", vec![]),
                isa_instruction(
                    "STACK_SCRATCH",
                    vec![Effect::write_memory(
                        stack_scratch_address.clone(),
                        constant(0xaa, 8),
                        8,
                    )],
                ),
                isa_instruction(
                    "ARBITRARY_MEMORY",
                    vec![Effect::write_memory(
                        arbitrary_address,
                        constant(0xaa, 8),
                        8,
                    )],
                ),
            ],
        );
        let empty = decoded_sequence(&["NOP"]);
        let stack_scratch = decoded_sequence(&["STACK_SCRATCH"]);
        let arbitrary_memory = decoded_sequence(&["ARBITRARY_MEMORY"]);

        let mut right_scratch_manager =
            Z3EquivalenceManager::from_instructions_with_live_out_registers(
                &empty,
                &stack_scratch,
                &isa,
                vec![],
            );
        assert_eq!(
            right_scratch_manager.compare_instructions(),
            BddEquality::Equal
        );

        let mut right_arbitrary_manager =
            Z3EquivalenceManager::from_instructions_with_live_out_registers(
                &empty,
                &arbitrary_memory,
                &isa,
                vec![],
            );
        assert!(matches!(
            right_arbitrary_manager.compare_instructions(),
            BddEquality::Unequal(_)
        ));

        let mut left_scratch_manager =
            Z3EquivalenceManager::from_instructions_with_live_out_registers(
                &stack_scratch,
                &empty,
                &isa,
                vec![],
            );
        assert!(matches!(
            left_scratch_manager.compare_instructions(),
            BddEquality::Unequal(_)
        ));
    }

    #[test]
    fn z3_equivalence_manager_handles_wide_memory_write_aliasing() {
        let address = constant(0x20, 8);
        let value = constant(0x4433_2211, 32);
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "STORE32",
                    vec![Effect::write_memory(address.clone(), value.clone(), 32)],
                ),
                isa_instruction(
                    "STORE32_BYTES",
                    vec![
                        Effect::write_memory(address.clone(), extract(value.clone(), 7, 0), 8),
                        Effect::write_memory(
                            add(address.clone(), constant(1, 8)),
                            extract(value.clone(), 15, 8),
                            8,
                        ),
                        Effect::write_memory(
                            add(address.clone(), constant(2, 8)),
                            extract(value.clone(), 23, 16),
                            8,
                        ),
                        Effect::write_memory(
                            add(address.clone(), constant(3, 8)),
                            extract(value.clone(), 31, 24),
                            8,
                        ),
                    ],
                ),
                isa_instruction(
                    "STORE32_BAD_BYTE_1",
                    vec![
                        Effect::write_memory(address.clone(), extract(value.clone(), 7, 0), 8),
                        Effect::write_memory(
                            add(address.clone(), constant(1, 8)),
                            constant(0, 8),
                            8,
                        ),
                        Effect::write_memory(
                            add(address.clone(), constant(2, 8)),
                            extract(value.clone(), 23, 16),
                            8,
                        ),
                        Effect::write_memory(
                            add(address.clone(), constant(3, 8)),
                            extract(value, 31, 24),
                            8,
                        ),
                    ],
                ),
            ],
        );
        let left = decoded_sequence(&["STORE32"]);
        let equal_right = decoded_sequence(&["STORE32_BYTES"]);
        let unequal_right = decoded_sequence(&["STORE32_BAD_BYTE_1"]);
        let mut manager = Z3EquivalenceManager::from_instructions(&left, &equal_right, &isa);

        assert_eq!(manager.compare_instructions(), BddEquality::Equal);

        manager.replace_right_instruction(&unequal_right);
        let BddEquality::Unequal(counterexample) = manager.compare_instructions() else {
            panic!("expected Z3 to find a memory counterexample");
        };
        let left_output = execute_program_concrete(&left, &isa, &counterexample);
        let right_output = execute_program_concrete(&unequal_right, &isa, &counterexample);

        assert_eq!(left_output.memory[&(0x21, 8)].value, 0x22);
        assert_eq!(right_output.memory[&(0x21, 8)].value, 0);
    }

    #[test]
    fn z3_equivalence_manager_random_counterexamples_match_concrete_execution() {
        let r0 = read_register(reg(0), 8);
        let r1 = read_register(reg(1), 8);
        let r2 = read_register(reg(2), 8);
        let mem20 = read_memory(constant(0x20, 8), 8);
        let mem21 = read_memory(constant(0x21, 8), 8);
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "MOV_R0_R1",
                    vec![Effect::write_register(reg(0), r1.clone())],
                ),
                isa_instruction(
                    "MOV_R0_R2",
                    vec![Effect::write_register(reg(0), r2.clone())],
                ),
                isa_instruction(
                    "ADD_R0_R1_R2",
                    vec![Effect::write_register(reg(0), add(r1.clone(), r2.clone()))],
                ),
                isa_instruction(
                    "SUB_R0_R1_R2",
                    vec![Effect::write_register(reg(0), sub(r1.clone(), r2.clone()))],
                ),
                isa_instruction(
                    "XOR_R0_R1_R2",
                    vec![Effect::write_register(
                        reg(0),
                        xor_expr(r1.clone(), r2.clone()),
                    )],
                ),
                isa_instruction(
                    "LOW_R0",
                    vec![Effect::write_register(reg(0), constant(0x3c, 8))],
                ),
                isa_instruction(
                    "HIGH_R0",
                    vec![Effect::write_register(reg(0), constant(0xc3, 8))],
                ),
                isa_instruction(
                    "GUARDED_R0",
                    vec![Effect::write_register_if(
                        unsigned_less_than(r1.clone(), r2.clone()),
                        reg(0),
                        constant(0x5a, 8),
                    )],
                ),
                isa_instruction(
                    "STORE20_R0",
                    vec![Effect::write_memory(constant(0x20, 8), r0.clone(), 8)],
                ),
                isa_instruction(
                    "STORE21_R1",
                    vec![Effect::write_memory(constant(0x21, 8), r1.clone(), 8)],
                ),
                isa_instruction(
                    "LOAD20_R0",
                    vec![Effect::write_register(reg(0), mem20.clone())],
                ),
                isa_instruction(
                    "LOAD21_R0",
                    vec![Effect::write_register(reg(0), mem21.clone())],
                ),
            ],
        );
        let instruction_names = [
            "MOV_R0_R1",
            "MOV_R0_R2",
            "ADD_R0_R1_R2",
            "SUB_R0_R1_R2",
            "XOR_R0_R1_R2",
            "LOW_R0",
            "HIGH_R0",
            "GUARDED_R0",
            "STORE20_R0",
            "STORE21_R1",
            "LOAD20_R0",
            "LOAD21_R0",
        ];
        let mut rng = StdRng::seed_from_u64(0x5a3c_2026);
        let mut checked_counterexamples = 0;

        for _ in 0..96 {
            let left = random_decoded_sequence(&instruction_names, &mut rng);
            let right = random_decoded_sequence(&instruction_names, &mut rng);
            let mut manager = Z3EquivalenceManager::from_instructions(&left, &right, &isa);

            if let BddEquality::Unequal(counterexample) = manager.compare_instructions() {
                let left_output = execute_program_concrete(&left, &isa, &counterexample);
                let right_output = execute_program_concrete(&right, &isa, &counterexample);
                assert_ne!(
                    left_output, right_output,
                    "Z3 counterexample did not separate left={left:?} right={right:?} state={counterexample:?}"
                );
                checked_counterexamples += 1;
            }
        }

        assert!(
            checked_counterexamples > 0,
            "randomized Z3/concrete test should exercise at least one counterexample"
        );
    }

    fn random_decoded_sequence(instruction_names: &[&str], rng: &mut StdRng) -> Program {
        let len = rng.random_range(1..=4);
        let instructions = (0..len)
            .map(|_| {
                let idx = rng.random_range(0..instruction_names.len());
                decoded(instruction_names[idx])
            })
            .collect();
        Program::from_instructions(instructions, len)
    }

    #[test]
    fn equivalence_manager_replace_right_instruction_allows_extra_memory_effect_changes() {
        let address_a = constant(0x20, 8);
        let address_b = constant(0x30, 8);
        let address_c = constant(0x40, 8);
        let isa = equivalence_test_isa(
            8,
            vec![
                isa_instruction(
                    "STORE_A",
                    vec![Effect::write_memory(
                        address_a.clone(),
                        constant(0xa5, 8),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE_B",
                    vec![Effect::write_memory(
                        address_b.clone(),
                        constant(0x5a, 8),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE_C",
                    vec![Effect::write_memory(
                        address_c.clone(),
                        constant(0xc3, 8),
                        8,
                    )],
                ),
            ],
        );
        let left = decoded_sequence(&["STORE_A"]);
        let right_with_b = decoded_sequence(&["STORE_A", "STORE_B"]);
        let right_with_c = decoded_sequence(&["STORE_A", "STORE_C"]);
        let mut manager = EquivalenceManager::from_instructions(&left, &right_with_b, &isa);

        assert_eq!(
            manager
                .compare_instructions()
                .expect("initial memory comparison should allocate"),
            BddEquality::Equal
        );

        manager.replace_right_instruction(&right_with_c);
        assert!(
            manager.right_effects.iter().any(|effect| {
                matches!(effect, Effect::WriteMemory { address, .. } if *address == address_c)
            }),
            "replacement should install the new extra right-side memory effect"
        );
        assert!(
            !manager.right_effects.iter().any(|effect| {
                matches!(effect, Effect::WriteMemory { address, .. } if *address == address_b)
            }),
            "replacement should remove the old extra right-side memory effect"
        );
        assert_eq!(
            manager
                .compare_instructions()
                .expect("memory replacement comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn evaluate_expr_uses_registers_memory_and_bitvector_operations() {
        let mut state = MachineState::default();
        state.registers.insert(1, BitWord::new(0x0f, 8));
        state.memory.insert((0x20, 8), BitWord::new(0xf0, 8));

        let expr = Expr::Xor(
            Box::new(read_register(reg(1), 8)),
            Box::new(read_memory(constant(0x20, 8), 8)),
        );

        assert_eq!(evaluate_expr(&expr, &state), Some(BitWord::new(0xff, 8)));

        let selected = select(
            equal(read_register(reg(1), 8), constant(0x0f, 8)),
            constant(0x12, 8),
            constant(0x34, 8),
        );
        assert_eq!(
            evaluate_expr(&selected, &state),
            Some(BitWord::new(0x12, 8))
        );
    }

    #[test]
    fn evaluate_expr_reads_wide_memory_from_bytes() {
        let state = machine_state(
            &[],
            &[
                ((0x20, 8), BitWord::new(0x11, 8)),
                ((0x21, 8), BitWord::new(0x22, 8)),
                ((0x22, 8), BitWord::new(0x33, 8)),
                ((0x23, 8), BitWord::new(0x44, 8)),
            ],
        );

        assert_eq!(
            evaluate_expr(&read_memory(constant(0x20, 8), 32), &state),
            Some(BitWord::new(0x4433_2211, 32))
        );
    }

    #[test]
    fn evaluate_expr_returns_none_for_missing_state() {
        let state = MachineState::default();

        assert_eq!(evaluate_expr(&read_register(reg(1), 8), &state), None);
        assert_eq!(
            evaluate_expr(&read_memory(constant(0x20, 8), 8), &state),
            None
        );
    }

    #[test]
    fn compare_returns_counterexample_state_that_evaluates_expressions() {
        let mut manager = BddManager::from_exprs(
            read_register(reg(0), 1),
            constant(0, 1),
            &test_isa(vec![test_arch_register(0, 8, 1)], vec![]),
        );

        let result = manager.compare().expect("compare should allocate");
        let BddEquality::Unequal(state) = result else {
            panic!("expected a counterexample");
        };

        assert_eq!(
            evaluate_expr(&read_register(reg(0), 1), &state),
            Some(BitWord::new(1, 1))
        );
        assert_eq!(
            evaluate_expr(&constant(0, 1), &state),
            Some(BitWord::new(0, 1))
        );
    }

    #[test]
    fn compare_counterexample_state_includes_memory_reads() {
        let memory_read = read_memory(constant(0x40, 8), 8);
        let mut manager =
            BddManager::from_exprs(memory_read.clone(), constant(0, 8), &bdd_test_isa());

        let result = manager.compare().expect("compare should allocate");
        let BddEquality::Unequal(state) = result else {
            panic!("expected a counterexample");
        };

        let read_value = evaluate_expr(&memory_read, &state)
            .expect("counterexample should include the memory read value");
        assert_ne!(read_value.value, 0);
        assert_eq!(read_value.width, 8);
    }

    #[test]
    fn compare_counterexample_handles_register_addressed_memory_and_shared_register_read() {
        let address = add(read_register(reg(0), 8), read_register(reg(1), 8));
        let expr = Expr::Xor(
            Box::new(read_memory(address.clone(), 8)),
            Box::new(read_register(reg(0), 8)),
        )
        .canonicalize();
        let mut manager = BddManager::from_exprs(
            expr.clone(),
            constant(0, 8),
            &test_isa(
                vec![test_arch_register(0, 8, 8), test_arch_register(1, 8, 8)],
                vec![],
            ),
        );

        let result = manager.compare().expect("compare should allocate");
        let BddEquality::Unequal(state) = result else {
            panic!("expected a counterexample");
        };

        let address_value = evaluate_expr(&address, &state)
            .expect("counterexample should include address registers");
        assert!(
            state.memory.contains_key(&(address_value.value, 8)),
            "counterexample should include memory at the register-computed address"
        );
        let expr_value = evaluate_expr(&expr, &state)
            .expect("counterexample should evaluate the register-addressed memory expression");
        assert_ne!(expr_value.value, 0);
        assert_eq!(expr_value.width, 8);
    }

    #[test]
    fn compare_counterexample_handles_memory_indexed_register_and_shared_memory_read() {
        let selector = read_memory(constant(0x20, 8), 1);
        let indexed_register = read_register(selector.clone(), 8);
        let expr = Expr::Xor(
            Box::new(indexed_register.clone()),
            Box::new(zero_extend(selector.clone(), 8)),
        )
        .canonicalize();
        let mut manager = BddManager::from_exprs(
            expr.clone(),
            constant(0, 8),
            &test_isa(
                vec![test_arch_register(0, 1, 8), test_arch_register(1, 1, 8)],
                vec![],
            ),
        );

        let result = manager.compare().expect("compare should allocate");
        let BddEquality::Unequal(state) = result else {
            panic!("expected a counterexample");
        };

        let selector_value = evaluate_expr(&selector, &state)
            .expect("counterexample should include the memory-backed register selector");
        assert!(selector_value.value <= 1);
        assert!(
            state.memory.contains_key(&(0x20, 1)),
            "counterexample should include the shared memory selector read"
        );
        evaluate_expr(&indexed_register, &state)
            .expect("counterexample should include the selected register");
        let expr_value = evaluate_expr(&expr, &state)
            .expect("counterexample should evaluate the memory-indexed register expression");
        assert_ne!(expr_value.value, 0);
        assert_eq!(expr_value.width, 8);
    }

    #[test]
    fn compare_returns_equal_for_identical_memory_reads() {
        let expr = read_memory(constant(0x40, 8), 8);
        let mut manager = BddManager::from_exprs(expr.clone(), expr, &bdd_test_isa());

        assert_eq!(
            manager.compare().expect("compare should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    fn new_variable_reuses_released_slots() {
        let mut manager = bdd_manager_for_width(1);
        let first = manager.new_variable(VariableDescription::RegisterBit {
            register: ArchitecturalRegister {
                identifier: 0,
                identifier_width: 1,
                width: 1,
            },
            bit: 0,
        });

        manager.release_variable(0);
        let second = manager.new_variable(VariableDescription::MemoryReadValueBit {
            read_id: 0,
            left: true,
            bit: 0,
        });

        assert_eq!(manager.variables.len(), 1);
        assert!(first == second);
        assert!(matches!(
            manager.variables[0].0,
            VariableDescription::MemoryReadValueBit {
                read_id: 0,
                left: true,
                bit: 0
            }
        ));
    }

    #[test]
    #[should_panic(expected = "Variable index is outside the variable pool")]
    fn release_variable_rejects_out_of_range_indices() {
        let mut manager = bdd_manager_for_width(1);

        manager.release_variable(0);
    }

    #[test]
    #[should_panic(expected = "Variable is already unallocated")]
    fn release_variable_rejects_already_released_slots() {
        let mut manager = bdd_manager_for_width(1);
        manager.new_variable(VariableDescription::RegisterBit {
            register: ArchitecturalRegister {
                identifier: 0,
                identifier_width: 1,
                width: 1,
            },
            bit: 0,
        });

        manager.release_variable(0);
        manager.release_variable(0);
    }

    #[test]
    fn variable_usage_helpers_find_variables_in_functions_words_and_tables() {
        let mut manager = bdd_manager_for_width(1);
        let variable = manager.new_variable(VariableDescription::RegisterBit {
            register: ArchitecturalRegister {
                identifier: 0,
                identifier_width: 1,
                width: 1,
            },
            bit: 0,
        });
        let word = BddWord {
            bits: vec![variable.clone()],
        };
        let table = vec![MemoryRead {
            read_id: 0,
            depth: 0,
            address_expr: constant(0x100, 32),
            lowered_address: Some(word.clone()),
            width: 1,
            value: BddWord {
                bits: vec![manager.false_fn.clone()],
            },
            value_variables: BddWord { bits: vec![] },
        }];

        assert!(BddManager::function_uses_variable(
            &variable,
            &variable,
            &manager.false_fn
        ));
        assert!(!BddManager::function_uses_variable(
            &manager.true_fn,
            &variable,
            &manager.false_fn
        ));
        assert!(BddManager::word_uses_variable(
            &word,
            &variable,
            &manager.false_fn
        ));
        assert!(BddManager::table_uses_variable(
            &table,
            &variable,
            &manager.false_fn
        ));
    }

    #[test]
    #[should_panic(expected = "Expression widths must match")]
    fn from_exprs_rejects_mismatched_expression_widths() {
        BddManager::from_exprs(constant(0, 1), constant(0, 2), &test_isa(vec![], vec![]));
    }

    #[test]
    fn from_left_expr_uses_same_expression_on_both_sides() {
        let expr = and_expr(read_register(reg(0), 1), bool_const(true));
        let mut manager = BddManager::from_left_expr(expr.clone(), &bdd_test_isa());

        assert_eq!(manager.left_expr, expr);
        assert_eq!(manager.right_expr, expr);
        assert_eq!(
            manager.compare().expect("comparison should allocate"),
            BddEquality::Equal
        );
    }

    #[test]
    #[should_panic(expected = "new_expr width should match existing expression widths")]
    fn replace_right_expr_rejects_mismatched_widths() {
        let mut manager = bdd_manager_for_width(8);

        manager.replace_right_expr(constant(0, 16));
    }

    #[test]
    fn lower_constant_handles_128_bit_edges() {
        assert_const_expr_lowering(constant(u128::MAX, 128), u128::MAX, 128);
        assert_const_expr_lowering(constant(1u128 << 127, 128), 1u128 << 127, 128);
    }

    #[test]
    fn mux_word_uses_symbolic_condition() {
        let condition_expr = read_memory(constant(0x100, 32), 1);
        let manager = BddManager::from_exprs(condition_expr, constant(0, 1), &bdd_test_isa());
        let condition = manager.left_memory_read_table[0].value.bits[0].clone();
        let result = manager
            .mux_word(
                &condition,
                &manager.lower_constant(0b1010, 4),
                &manager.lower_constant(0b0101, 4),
            )
            .unwrap();
        let condition_variable = manager
            .variables
            .iter()
            .position(|(description, _)| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit {
                        left: true,
                        bit: 0,
                        ..
                    }
                )
            })
            .expect("expected condition memory variable") as u32;

        assert_eq!(
            eval_bdd_word(&result, &[(condition_variable, false)]),
            0b0101
        );
        assert_eq!(
            eval_bdd_word(&result, &[(condition_variable, true)]),
            0b1010
        );
    }

    #[test]
    fn lower_expression_lowers_fixed_register_operands_to_identifiers() {
        let manager = bdd_manager_for_width(3);
        let lowered = manager.lower_expression(&fixed_register(Register(5), 3), LEFT_EXPR);

        assert_eq!(constant_bdd_word_value(&manager, &lowered), 5);
        assert_eq!(lowered.bits.len(), 3);
    }

    #[test]
    fn lower_expression_lowers_read_register_through_fixed_selector() {
        let registers = (0..4)
            .map(|identifier| ArchitecturalRegister {
                identifier,
                identifier_width: 2,
                width: 4,
            })
            .collect();
        let read = read_register(fixed_register(Register(2), 2), 4);
        let manager =
            BddManager::from_exprs(read.clone(), constant(0, 4), &test_isa(registers, vec![]));
        let result = manager.lower_expression(&read, LEFT_EXPR);
        let register_values = [0b0001u128, 0b0010, 0b0100, 0b1000];
        let assignment: Vec<_> = manager
            .variables
            .iter()
            .enumerate()
            .map(|(variable, (description, _))| {
                let value = match description {
                    VariableDescription::RegisterBit { register, bit } => {
                        (register_values[register.identifier as usize] >> bit) & 1 != 0
                    }
                    _ => false,
                };
                (variable as u32, value)
            })
            .collect();

        assert_eq!(eval_bdd_word(&result, &assignment), register_values[2]);
    }

    #[test]
    fn lower_expression_uses_the_requested_side_memory_read_table() {
        let left_read = read_memory(constant(0x100, 32), 8);
        let right_read = read_memory(constant(0x200, 32), 8);
        let manager =
            BddManager::from_exprs(left_read.clone(), right_read.clone(), &bdd_test_isa());

        assert!(
            manager.lower_expression(&left_read, LEFT_EXPR)
                == manager.left_memory_read_table[0].value
        );
        assert!(
            manager.lower_expression(&right_read, RIGHT_EXPR)
                == manager.right_memory_read_table[0].value
        );
        assert!(
            manager.lower_expression(&right_read, RIGHT_EXPR)
                != manager.left_memory_read_table[0].value
        );
    }

    #[test]
    fn lower_register_read_defaults_missing_register_ids_to_zero() {
        let registers = [0, 2]
            .into_iter()
            .map(|identifier| ArchitecturalRegister {
                identifier,
                identifier_width: 2,
                width: 3,
            })
            .collect();
        let selector_expr = read_memory(constant(0x100, 32), 2);
        let manager =
            BddManager::from_exprs(selector_expr, constant(0, 2), &test_isa(registers, vec![]));
        let selector = manager.left_memory_read_table[0].value.clone();
        let result = manager.lower_register_read(selector, 3).unwrap();
        let register_values = [0b101u128, 0, 0b011, 0];

        for selected_register in 0..4 {
            let assignment: Vec<_> = manager
                .variables
                .iter()
                .enumerate()
                .map(|(variable, (description, _))| {
                    let value = match description {
                        VariableDescription::RegisterBit { register, bit } => {
                            (register_values[register.identifier as usize] >> bit) & 1 != 0
                        }
                        VariableDescription::MemoryReadValueBit {
                            left: true, bit, ..
                        } => (selected_register >> bit) & 1 != 0,
                        _ => false,
                    };
                    (variable as u32, value)
                })
                .collect();

            assert_eq!(
                eval_bdd_word(&result, &assignment),
                register_values[selected_register],
                "selected_register={selected_register}"
            );
        }
    }

    #[test]
    #[should_panic(expected = "Register identifier too large for its identifier width")]
    fn lower_register_read_rejects_register_ids_outside_selector_space() {
        let manager = BddManager::from_exprs(
            constant(0, 2),
            constant(0, 2),
            &test_isa(
                vec![ArchitecturalRegister {
                    identifier: 4,
                    identifier_width: 2,
                    width: 1,
                }],
                vec![],
            ),
        );

        manager
            .lower_register_read(manager.lower_constant(0, 2), 1)
            .unwrap();
    }

    #[test]
    #[should_panic(expected = "register selector exceeds u8 identifier width")]
    fn lower_register_read_rejects_too_wide_selectors() {
        let manager = bdd_manager_for_width(1);

        manager
            .lower_register_read(manager.lower_constant(0, 9), 1)
            .unwrap();
    }

    #[test]
    fn direct_shift_helpers_handle_zero_width_and_oversized_amount_edges() {
        let manager = bdd_manager_for_width(4);
        let value = manager.lower_constant(0b1001, 4);
        let negative = manager.lower_constant(0b1000, 4);
        let empty = BddWord { bits: vec![] };

        assert_eq!(
            constant_bdd_word_value(&manager, &manager.shift_left_const(&value, 0)),
            0b1001
        );
        assert_eq!(
            constant_bdd_word_value(&manager, &manager.shift_left_const(&value, 5)),
            0
        );
        assert_eq!(
            constant_bdd_word_value(&manager, &manager.shift_logical_right_const(&value, 5)),
            0
        );
        assert_eq!(
            constant_bdd_word_value(&manager, &manager.shift_arith_right_const(&negative, 5)),
            0b1111
        );
        assert_eq!(manager.shift_left_const(&empty, 3).bits.len(), 0);
        assert_eq!(manager.shift_logical_right_const(&empty, 3).bits.len(), 0);
    }

    #[test]
    fn rotate_right_const_and_shift_steps_reduce_amounts_modulo_width() {
        let manager = bdd_manager_for_width(5);
        let value = manager.lower_constant(0b10011, 5);

        assert_eq!(BddManager::rotate_right_shift_for_bit(65, 64), 16);
        assert_eq!(BddManager::rotate_right_shift_for_bit(64, 64), 0);
        assert_eq!(BddManager::rotate_right_shift_for_bit(1, 127), 0);
        assert_eq!(
            constant_bdd_word_value(&manager, &manager.rotate_right_const(&value, 7)),
            0b11100
        );
    }

    #[test]
    fn all_true_handles_empty_all_true_and_mixed_inputs() {
        let manager = bdd_manager_for_width(1);

        assert!(manager.all_true(&[]).unwrap() == manager.true_fn);
        assert!(
            manager
                .all_true(&[manager.true_fn.clone(), manager.true_fn.clone()])
                .unwrap()
                == manager.true_fn
        );
        assert!(
            manager
                .all_true(&[manager.true_fn.clone(), manager.false_fn.clone()])
                .unwrap()
                == manager.false_fn
        );
    }

    #[test]
    #[should_panic]
    fn lower_bitwise_binary_rejects_mismatched_widths() {
        let manager = bdd_manager_for_width(2);

        manager
            .lower_constant(0, 1)
            .lower_bitwise_binary(manager.lower_constant(0, 2), |lhs, rhs| lhs.and(rhs))
            .unwrap();
    }

    #[test]
    fn lower_concat_handles_empty_inputs() {
        let manager = bdd_manager_for_width(1);
        let result = manager.lower_concat(Vec::new()).unwrap();

        assert!(result.bits.is_empty());
    }

    #[test]
    #[should_panic(expected = "width must be less than to_width")]
    fn lower_zero_extend_rejects_shrinking() {
        let manager = bdd_manager_for_width(2);

        manager
            .lower_zero_extend(manager.lower_constant(0, 2), 1)
            .unwrap();
    }

    #[test]
    #[should_panic(expected = "width must be less than to_width")]
    fn lower_sign_extend_rejects_shrinking() {
        let manager = bdd_manager_for_width(2);

        manager
            .lower_sign_extend(manager.lower_constant(0, 2), 1)
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn lower_sign_extend_rejects_empty_words() {
        let manager = bdd_manager_for_width(1);

        manager
            .lower_sign_extend(BddWord { bits: vec![] }, 1)
            .unwrap();
    }

    #[test]
    fn high_amount_bits_saturate_non_rotate_shifts() {
        let width = 128;
        let manager = bdd_manager_for_width(width);
        let huge_amount = constant(1u128 << 127, width);

        assert_const_expr_lowering_with_manager(
            &manager,
            shift_left(constant(1, width), huge_amount.clone()),
            0,
            width,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            logical_shift_right(constant(1u128 << 127, width), huge_amount.clone()),
            0,
            width,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            arithmetic_shift_right(constant(1u128 << 127, width), huge_amount),
            u128::MAX,
            width,
        );
    }

    #[test]
    fn lower_comparisons_handle_128_bit_signed_and_unsigned_edges() {
        let manager = bdd_manager_for_width(1);

        assert_const_expr_lowering_with_manager(
            &manager,
            equal(constant(u128::MAX, 128), constant(u128::MAX, 128)),
            1,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            equal(constant(u128::MAX, 128), constant(0, 128)),
            0,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            unsigned_less_than(constant(0, 128), constant(u128::MAX, 128)),
            1,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            signed_less_than(constant(u128::MAX, 128), constant(0, 128)),
            1,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            signed_less_than(constant(1u128 << 127, 128), constant(u128::MAX, 128)),
            1,
            1,
        );
    }

    #[test]
    fn lower_extract_handles_128_bit_boundaries() {
        assert_const_expr_lowering(extract(constant(1u128 << 127, 128), 127, 127), 1, 1);
        assert_const_expr_lowering(
            extract(constant(1u128 << 127, 128), 127, 120),
            0b1000_0000,
            8,
        );
        assert_const_expr_lowering(
            extract(constant(0xfeed_beef_dead_cafe, 128), 15, 0),
            0xcafe,
            16,
        );
    }

    #[test]
    fn lower_count_ones_handles_128_bit_edges() {
        assert_const_expr_lowering(count_ones(constant(u128::MAX, 128)), 128, 128);
        assert_const_expr_lowering(count_ones(constant(1u128 << 127, 128)), 1, 128);
    }

    #[test]
    fn lower_add_flags_handle_more_128_bit_boundaries() {
        let manager = bdd_manager_for_width(1);

        assert_const_expr_lowering_with_manager(
            &manager,
            add_carry_out(constant(0, 128), constant(0, 128), bool_const(false), 128),
            0,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            add_carry_out(
                constant(u128::MAX, 128),
                constant(u128::MAX, 128),
                bool_const(true),
                128,
            ),
            1,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            add_overflow(
                constant((1u128 << 127) - 1, 128),
                constant(1, 128),
                bool_const(false),
                128,
            ),
            1,
            1,
        );
    }

    #[test]
    #[should_panic]
    fn lower_add_carry_out_rejects_multi_bit_carry_inputs() {
        let manager = bdd_manager_for_width(2);

        manager
            .lower_add_cout(
                manager.lower_constant(0, 2),
                manager.lower_constant(0, 2),
                manager.lower_constant(0, 2),
                2,
            )
            .unwrap();
    }

    #[test]
    #[should_panic]
    fn lower_add_overflow_rejects_multi_bit_carry_inputs() {
        let manager = bdd_manager_for_width(2);

        manager
            .lower_add_overflow(
                manager.lower_constant(0, 2),
                manager.lower_constant(0, 2),
                manager.lower_constant(0, 2),
                2,
            )
            .unwrap();
    }

    #[test]
    fn lower_constant_uses_little_endian_bits_and_truncates_to_width() {
        assert_const_expr_lowering(constant(0b1_1010_0101, 8), 0b1010_0101, 8);
    }

    #[test]
    fn mux_word_selects_the_requested_word() {
        let manager = bdd_manager_for_width(4);
        let when_true = manager.lower_constant(0b1010, 4);
        let when_false = manager.lower_constant(0b0101, 4);

        let selected_true = manager
            .mux_word(&manager.true_fn, &when_true, &when_false)
            .unwrap();
        let selected_false = manager
            .mux_word(&manager.false_fn, &when_true, &when_false)
            .unwrap();

        assert_eq!(constant_bdd_word_value(&manager, &selected_true), 0b1010);
        assert_eq!(constant_bdd_word_value(&manager, &selected_false), 0b0101);
    }

    #[test]
    fn full_adder_matches_all_truth_table_rows() {
        let manager = bdd_manager_for_width(1);

        for a in [false, true] {
            for b in [false, true] {
                for carry_in in [false, true] {
                    let a_fn = if a {
                        &manager.true_fn
                    } else {
                        &manager.false_fn
                    };
                    let b_fn = if b {
                        &manager.true_fn
                    } else {
                        &manager.false_fn
                    };
                    let carry_fn = if carry_in {
                        &manager.true_fn
                    } else {
                        &manager.false_fn
                    };

                    let (sum, carry_out) = BddManager::full_adder(a_fn, b_fn, carry_fn).unwrap();
                    let total = a as u8 + b as u8 + carry_in as u8;

                    assert_eq!(sum == manager.true_fn, total & 1 != 0);
                    assert_eq!(carry_out == manager.true_fn, total >= 2);
                }
            }
        }
    }

    #[test]
    fn lower_add_matches_wrapping_addition_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(width);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        add(constant(lhs, width), constant(rhs, width)),
                        (lhs + rhs) & (limit - 1),
                        width,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_shift_left_matches_const_oracle_exhaustively() {
        let width = 6;
        let manager = bdd_manager_for_width(width);
        let mask = (1u128 << width) - 1;

        for value in 0..=mask {
            for amount in 0..=mask {
                assert_const_expr_lowering_with_manager(
                    &manager,
                    shift_left(constant(value, width), constant(amount, width)),
                    (value << amount as u32) & mask,
                    width,
                );
            }
        }
    }

    #[test]
    fn mask_word_selects_value_or_zero() {
        let manager = bdd_manager_for_width(5);

        for value in 0..32 {
            let value_word = manager.lower_constant(value, 5);
            let included = manager.mask_word(&manager.true_fn, &value_word).unwrap();
            let excluded = manager.mask_word(&manager.false_fn, &value_word).unwrap();

            assert_eq!(constant_bdd_word_value(&manager, &included), value);
            assert_eq!(constant_bdd_word_value(&manager, &excluded), 0);
        }
    }

    #[test]
    fn lower_mul_matches_wrapping_multiplication_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(width);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        mul(constant(lhs, width), constant(rhs, width)),
                        (lhs * rhs) & (limit - 1),
                        width,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_mul_matches_64_bit_wrapping_multiplication() {
        let manager = bdd_manager_for_width(64);
        let cases = [
            (0, u64::MAX),
            (1, u64::MAX),
            (u64::MAX, u64::MAX),
            (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
            (1u64 << 63, 2),
        ];

        for (lhs, rhs) in cases {
            assert_const_expr_lowering_with_manager(
                &manager,
                mul(constant(lhs as u128, 64), constant(rhs as u128, 64)),
                lhs.wrapping_mul(rhs) as u128,
                64,
            );
        }
    }

    #[test]
    fn lower_and_and_not_match_bitwise_semantics_exhaustively() {
        let width = 5;
        let manager = bdd_manager_for_width(width);
        let mask = (1u128 << width) - 1;

        for lhs in 0..=mask {
            assert_const_expr_lowering_with_manager(
                &manager,
                not_expr(constant(lhs, width)),
                (!lhs) & mask,
                width,
            );

            for rhs in 0..=mask {
                assert_const_expr_lowering_with_manager(
                    &manager,
                    and_expr(constant(lhs, width), constant(rhs, width)),
                    lhs & rhs,
                    width,
                );
            }
        }
    }

    #[test]
    fn bdd_word_bitor_matches_bitwise_or_exhaustively() {
        let width = 5;
        let manager = bdd_manager_for_width(width);
        let mask = bit_mask(width);

        for lhs in 0..=mask {
            for rhs in 0..=mask {
                let result = (manager.lower_constant(lhs, width)
                    | manager.lower_constant(rhs, width))
                .unwrap();

                assert_eq!(constant_bdd_word_value(&manager, &result), lhs | rhs);
            }
        }
    }

    #[test]
    fn lower_logical_shift_right_matches_const_oracle_exhaustively() {
        let width = 6;
        let manager = bdd_manager_for_width(width);
        let mask = bit_mask(width);

        for value in 0..=mask {
            for amount in 0..=mask {
                let expected = if amount >= width as u128 {
                    0
                } else {
                    value >> amount as u32
                };

                assert_const_expr_lowering_with_manager(
                    &manager,
                    logical_shift_right(constant(value, width), constant(amount, width)),
                    expected,
                    width,
                );
            }
        }
    }

    #[test]
    fn lower_arithmetic_shift_right_matches_const_oracle_exhaustively() {
        let width = 6;
        let manager = bdd_manager_for_width(width);
        let mask = bit_mask(width);
        let sign = 1u128 << (width - 1);

        for value in 0..=mask {
            for amount in 0..=mask {
                let expected = if amount >= width as u128 {
                    if value & sign == 0 { 0 } else { mask }
                } else {
                    (signed_value(value, width) >> amount as u32) as u128
                };

                assert_const_expr_lowering_with_manager(
                    &manager,
                    arithmetic_shift_right(constant(value, width), constant(amount, width)),
                    expected,
                    width,
                );
            }
        }
    }

    #[test]
    fn lower_rotate_right_matches_const_oracle_exhaustively() {
        let width = 5;
        let manager = bdd_manager_for_width(width);
        let mask = bit_mask(width);

        for value in 0..=mask {
            for amount in 0..=mask {
                let shift = (amount % width as u128) as u32;
                let expected = if shift == 0 {
                    value
                } else {
                    (value >> shift) | ((value << (width as u32 - shift)) & mask)
                };

                assert_const_expr_lowering_with_manager(
                    &manager,
                    rotate_right(constant(value, width), constant(amount, width)),
                    expected,
                    width,
                );
            }
        }
    }

    #[test]
    fn lower_rotate_right_handles_wide_non_power_of_two_amount_bits() {
        let manager = bdd_manager_for_width(65);
        let width = 65;
        let value = 0x1_2345_6789_abcd_ef01u128;
        let amount = 1u128 << 64;
        let shift = (amount % width as u128) as u32;
        let expected = (value >> shift) | ((value << (width as u32 - shift)) & bit_mask(width));

        assert_const_expr_lowering_with_manager(
            &manager,
            rotate_right(constant(value, width), constant(amount, width)),
            expected,
            width,
        );
    }

    #[test]
    fn lower_equal_matches_const_oracle_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(1);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        equal(constant(lhs, width), constant(rhs, width)),
                        (lhs == rhs) as u128,
                        1,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_unsigned_less_than_matches_const_oracle_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(1);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        unsigned_less_than(constant(lhs, width), constant(rhs, width)),
                        (lhs < rhs) as u128,
                        1,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_signed_less_than_matches_const_oracle_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(1);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        signed_less_than(constant(lhs, width), constant(rhs, width)),
                        (signed_value(lhs, width) < signed_value(rhs, width)) as u128,
                        1,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_extract_matches_const_oracle_for_all_ranges() {
        let width = 8;
        let manager = bdd_manager_for_width(width);
        let values = [0, 1, 0b1000_0000, 0b1011_0101, 0xff];

        for value in values {
            for low in 0..width {
                for high in low..width {
                    let out_width = high - low + 1;
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        extract(constant(value, width), high, low),
                        (value >> low) & bit_mask(out_width),
                        out_width,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_concat_matches_const_oracle_for_mixed_width_chunks() {
        let manager = bdd_manager_for_width(1);
        let cases = [
            vec![(0b1010, 4), (0b0101, 4)],
            vec![(0b1, 1), (0b10, 2), (0b011, 3)],
            vec![(0xab, 8), (0xc, 4), (0x123, 12)],
        ];

        for chunks in cases {
            let mut expected = 0;
            let mut total_width = 0;
            let exprs = chunks.iter().map(|&(value, width)| {
                expected = (expected << width as u32) | (value & bit_mask(width));
                total_width += width;
                constant(value, width)
            });

            assert_const_expr_lowering_with_manager(&manager, concat(exprs), expected, total_width);
        }
    }

    #[test]
    fn lower_zero_extend_matches_const_oracle_for_equal_and_wider_widths() {
        let manager = bdd_manager_for_width(1);
        for from_width in 1..=6 {
            let input_mask = bit_mask(from_width);
            for value in 0..=input_mask {
                for to_width in from_width..=8 {
                    assert_const_expr_lowering_with_manager(
                        &manager,
                        zero_extend(constant(value, from_width), to_width),
                        value,
                        to_width,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_sign_extend_matches_const_oracle_for_equal_and_wider_widths() {
        let manager = bdd_manager_for_width(1);
        for from_width in 1..=6 {
            let input_mask = bit_mask(from_width);
            let sign = 1u128 << (from_width - 1);

            for value in 0..=input_mask {
                for to_width in from_width..=8 {
                    let expected = if value & sign == 0 {
                        value
                    } else {
                        value | (bit_mask(to_width) ^ bit_mask(from_width))
                    };

                    assert_const_expr_lowering_with_manager(
                        &manager,
                        sign_extend(constant(value, from_width), to_width),
                        expected,
                        to_width,
                    );
                }
            }
        }
    }

    #[test]
    fn lower_count_ones_matches_const_oracle_exhaustively() {
        for width in 1..=8 {
            let manager = bdd_manager_for_width(width);
            let limit = 1u128 << width;

            for value in 0..limit {
                assert_const_expr_lowering_with_manager(
                    &manager,
                    count_ones(constant(value, width)),
                    value.count_ones() as u128,
                    width,
                );
            }
        }
    }

    #[test]
    fn lower_add_carry_out_matches_const_oracle_exhaustively() {
        let manager = bdd_manager_for_width(1);
        for width in 1..=6 {
            let limit = 1u128 << width;
            let mask = bit_mask(width);

            for lhs in 0..limit {
                for rhs in 0..limit {
                    for carry_in in 0..=1 {
                        assert_const_expr_lowering_with_manager(
                            &manager,
                            add_carry_out(
                                constant(lhs, width),
                                constant(rhs, width),
                                constant(carry_in, 1),
                                width,
                            ),
                            (lhs + rhs + carry_in > mask) as u128,
                            1,
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn lower_add_overflow_matches_const_oracle_exhaustively() {
        let manager = bdd_manager_for_width(1);
        for width in 1..=6 {
            let limit = 1u128 << width;
            let sign = 1u128 << (width - 1);
            let mask = bit_mask(width);

            for lhs in 0..limit {
                for rhs in 0..limit {
                    for carry_in in 0..=1 {
                        let result = (lhs + rhs + carry_in) & mask;
                        let expected =
                            ((lhs ^ rhs) & sign == 0 && (lhs ^ result) & sign != 0) as u128;

                        assert_const_expr_lowering_with_manager(
                            &manager,
                            add_overflow(
                                constant(lhs, width),
                                constant(rhs, width),
                                constant(carry_in, 1),
                                width,
                            ),
                            expected,
                            1,
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn lower_add_flags_match_const_oracle_for_wide_edges() {
        let manager = bdd_manager_for_width(1);

        assert_const_expr_lowering_with_manager(
            &manager,
            add_carry_out(
                constant(u128::MAX, 128),
                constant(0, 128),
                bool_const(true),
                128,
            ),
            1,
            1,
        );
        assert_const_expr_lowering_with_manager(
            &manager,
            add_overflow(
                constant(1u128 << 127, 128),
                constant(u128::MAX, 128),
                bool_const(false),
                128,
            ),
            1,
            1,
        );
    }

    #[test]
    fn lower_register_read_muxes_symbolic_selectors() {
        let registers = (0..4)
            .map(|identifier| ArchitecturalRegister {
                identifier,
                identifier_width: 2,
                width: 3,
            })
            .collect();
        let selector_expr = read_memory(constant(0x100, 32), 2);
        let manager =
            BddManager::from_exprs(selector_expr, constant(0, 2), &test_isa(registers, vec![]));
        let selector = manager.left_memory_read_table[0].value.clone();
        let result = manager.lower_register_read(selector, 3).unwrap();
        let register_values = [0b001u128, 0b010, 0b100, 0b111];

        for selected_register in 0..4 {
            let assignment: Vec<_> = manager
                .variables
                .iter()
                .enumerate()
                .map(|(variable, (description, _))| {
                    let value = match description {
                        VariableDescription::RegisterBit { register, bit } => {
                            (register_values[register.identifier as usize] >> bit) & 1 != 0
                        }
                        VariableDescription::MemoryReadValueBit {
                            left: true, bit, ..
                        } => (selected_register >> bit) & 1 != 0,
                        _ => false,
                    };
                    (variable as u32, value)
                })
                .collect();

            assert_eq!(
                eval_bdd_word(&result, &assignment),
                register_values[selected_register],
                "selected_register={selected_register}"
            );
        }
    }

    #[test]
    fn bdd_manager_interleaves_memory_read_variables_by_bit() {
        let left_expr = concat([
            read_memory(constant(0x100, 32), 8),
            read_memory(constant(0x200, 32), 16),
        ]);
        let manager = BddManager::from_exprs(left_expr, constant(0, 24), &bdd_test_isa());

        let descriptions: Vec<_> = manager
            .variables
            .iter()
            .filter_map(|(description, _)| match description {
                VariableDescription::MemoryReadValueBit {
                    read_id,
                    left: true,
                    bit,
                } => Some((*read_id, *bit)),
                _ => None,
            })
            .collect();

        let mut expected = Vec::new();
        for bit in 0..8 {
            expected.push((0, bit));
            expected.push((1, bit));
        }
        for bit in 8..16 {
            expected.push((1, bit));
        }

        assert_eq!(descriptions, expected);

        for read in &manager.left_memory_read_table {
            assert_eq!(read.value.bits.len(), read.value_variables.bits.len());
            for (bit, variable) in read.value_variables.bits.iter().enumerate() {
                assert!(
                    read.value.bits[bit] == *variable,
                    "memory read bit should match its value variable"
                );
                assert!(
                    manager
                        .variables
                        .iter()
                        .any(|(_, manager_variable)| manager_variable == variable),
                    "memory read bit should come from BddManager.variables"
                );
            }
        }
    }

    #[test]
    fn bdd_manager_assigns_nested_memory_reads_deepest_first() {
        let nested_address = read_memory(constant(0x100, 32), 32);
        let manager = BddManager::from_exprs(
            read_memory(nested_address, 8),
            constant(0, 8),
            &bdd_test_isa(),
        );

        let reads: Vec<_> = manager
            .left_memory_read_table
            .iter()
            .map(|read| (read.read_id, read.depth, read.width))
            .collect();

        assert_eq!(reads, vec![(0, 1, 32), (1, 0, 8)]);
    }

    #[test]
    fn duplicate_memory_read_keeps_greatest_observed_depth() {
        let shared_read = read_memory(constant(0x100, 32), 32);
        let manager = BddManager::from_exprs(
            concat([shared_read.clone(), read_memory(shared_read.clone(), 8)]),
            constant(0, 40),
            &bdd_test_isa(),
        );

        let shared_entry = manager
            .left_memory_read_table
            .iter()
            .find(|read| read.address_expr == constant(0x100, 32) && read.width == 32)
            .expect("expected deduplicated shared memory read");

        assert_eq!(shared_entry.depth, 1);
        assert_eq!(
            manager
                .left_memory_read_table
                .iter()
                .filter(|read| { read.address_expr == constant(0x100, 32) && read.width == 32 })
                .count(),
            1
        );
    }

    #[test]
    fn lower_memory_read_returns_the_assigned_value_word() {
        let memory_read = read_memory(constant(0x100, 32), 8);
        let manager = BddManager::from_exprs(memory_read.clone(), constant(0, 8), &bdd_test_isa());

        assert!(
            manager.lower_expression(&memory_read, LEFT_EXPR)
                == manager.left_memory_read_table[0].value
        );
    }

    #[test]
    fn replace_right_expr_reuses_variables_and_preserves_left_state() {
        let mut manager = BddManager::from_exprs(
            constant(0, 16),
            concat([
                read_memory(constant(0x100, 32), 8),
                read_memory(constant(0x200, 32), 8),
            ]),
            &bdd_test_isa(),
        );

        let register_variable = manager
            .variables
            .iter()
            .find_map(|(description, function)| {
                matches!(description, VariableDescription::RegisterBit { .. })
                    .then(|| function.clone())
            })
            .expect("expected register variable");
        manager.left = Some(BddWord {
            bits: vec![register_variable.clone()],
        });
        manager.constraint = manager
            .variables
            .iter()
            .find_map(|(description, function)| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit { left: false, .. }
                )
                .then(|| function.clone())
            })
            .expect("expected right memory variable");

        let initial_variable_count = manager_variable_count(&manager);

        for address in 0x300..0x310 {
            manager.replace_right_expr(read_memory(constant(address, 32), 16));

            assert_eq!(manager_variable_count(&manager), initial_variable_count);
            assert!(
                manager
                    .left
                    .as_ref()
                    .expect("expected preserved left word")
                    .bits
                    == vec![register_variable.clone()]
            );
            assert!(manager.constraint == manager.true_fn);
            assert_eq!(manager.right_expr, read_memory(constant(address, 32), 16));
            assert_eq!(manager.right_memory_read_table.len(), 1);
            let read = &manager.right_memory_read_table[0];
            for (bit, variable) in read.value_variables.bits.iter().enumerate() {
                assert!(
                    read.value.bits[bit] == *variable,
                    "reused right memory read bit should match its value variable"
                );
                assert!(
                    manager
                        .variables
                        .iter()
                        .any(|(_, manager_variable)| manager_variable == variable),
                    "reused right memory read bit should come from BddManager.variables"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "still used by a live BCDD function")]
    fn release_variable_rejects_a_variable_used_by_any_owned_root() {
        let mut manager = BddManager::from_exprs(
            constant(0, 8),
            read_memory(constant(0x100, 32), 8),
            &bdd_test_isa(),
        );
        let variable_index = manager
            .variables
            .iter()
            .position(|(description, _)| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit { left: false, .. }
                )
            })
            .expect("expected right memory variable");

        manager.left = Some(BddWord {
            bits: vec![manager.variables[variable_index].1.clone()],
        });
        manager.release_variable(variable_index);
    }

    #[test]
    fn instruction_seq_to_effects_does_not_double_substitute_register_reads() {
        let r0 = read_reg(0);
        let single_add = add(r0.clone(), r0).canonicalize();
        let double_substituted = add(single_add.clone(), single_add.clone()).canonicalize();
        let isa = test_isa(
            vec![],
            vec![
                isa_instruction(
                    "ADD_R0_R0_R0",
                    vec![Effect::write_register(
                        reg(0),
                        add(read_reg(0), read_reg(0)),
                    )],
                ),
                isa_instruction(
                    "MOV_R1_R0",
                    vec![Effect::write_register(reg(1), read_reg(0))],
                ),
            ],
        );
        let sequence =
            Program::from_instructions(vec![decoded("ADD_R0_R0_R0"), decoded("MOV_R1_R0")], 2);

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            register_write_value(&effects, 0).clone().canonicalize(),
            single_add
        );
        assert_eq!(
            register_write_value(&effects, 1).clone().canonicalize(),
            single_add
        );
        assert_ne!(
            register_write_value(&effects, 1).clone().canonicalize(),
            double_substituted
        );
    }

    #[test]
    fn instruction_seq_to_effects_lowers_memory_writes_to_bytes() {
        let address = constant(0x100, 32);
        let value = constant(0xaabb_ccdd, 32);
        let isa = test_isa(
            vec![],
            vec![isa_instruction(
                "STORE32",
                vec![Effect::write_memory(address.clone(), value.clone(), 32)],
            )],
        );
        let sequence = Program::from_instructions(vec![decoded("STORE32")], 1);

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            effects,
            vec![
                Effect::write_memory(address.clone(), extract(value.clone(), 7, 0), 8),
                Effect::write_memory(
                    add(address.clone(), constant(1, 32)),
                    extract(value.clone(), 15, 8),
                    8,
                ),
                Effect::write_memory(
                    add(address.clone(), constant(2, 32)),
                    extract(value.clone(), 23, 16),
                    8,
                ),
                Effect::write_memory(
                    add(address.clone(), constant(3, 32)),
                    extract(value.clone(), 31, 24),
                    8,
                ),
            ]
        );
    }

    #[test]
    fn instruction_seq_to_effects_lowers_memory_reads_before_substitution() {
        let address = constant(0x100, 32);
        let value = constant(0xaabb_ccdd, 32);
        let isa = test_isa(
            vec![],
            vec![
                isa_instruction(
                    "STORE32",
                    vec![Effect::write_memory(address.clone(), value.clone(), 32)],
                ),
                isa_instruction(
                    "LOAD32_R0",
                    vec![Effect::write_register(
                        reg(0),
                        read_memory(address.clone(), 32),
                    )],
                ),
            ],
        );
        let sequence =
            Program::from_instructions(vec![decoded("STORE32"), decoded("LOAD32_R0")], 2);

        let effects = instruction_seq_to_effects(&sequence, &isa);

        let byte_addresses = [
            address.clone(),
            add(address.clone(), constant(1, 32)),
            add(address.clone(), constant(2, 32)),
            add(address.clone(), constant(3, 32)),
        ];
        let byte_values = [
            extract(value.clone(), 7, 0),
            extract(value.clone(), 15, 8),
            extract(value.clone(), 23, 16),
            extract(value.clone(), 31, 24),
        ];
        let forwarded_byte = |read_address: Expr| {
            byte_addresses
                .iter()
                .cloned()
                .zip(byte_values.iter().cloned())
                .fold(
                    read_memory(read_address.clone(), 8),
                    |fallback, (address, value)| {
                        select(
                            forwarding_condition(bool_const(true), read_address.clone(), address),
                            value,
                            fallback,
                        )
                    },
                )
        };

        assert_eq!(
            register_write_value(&effects, 0).clone().canonicalize(),
            concat([
                forwarded_byte(add(address.clone(), constant(3, 32))),
                forwarded_byte(add(address.clone(), constant(2, 32))),
                forwarded_byte(add(address.clone(), constant(1, 32))),
                forwarded_byte(address),
            ])
            .canonicalize()
        );
    }

    #[test]
    fn instruction_seq_to_effects_forwards_symbolic_memory_aliases() {
        let write_address = read_reg(0);
        let read_address = read_reg(1);
        let write_value = constant(0x5a, 8);
        let isa = test_isa(
            vec![],
            vec![
                isa_instruction(
                    "STORE_R0",
                    vec![Effect::write_memory(
                        write_address.clone(),
                        write_value.clone(),
                        8,
                    )],
                ),
                isa_instruction(
                    "LOAD_R2_FROM_R1",
                    vec![Effect::write_register(
                        reg(2),
                        read_memory(read_address.clone(), 8),
                    )],
                ),
            ],
        );
        let sequence =
            Program::from_instructions(vec![decoded("STORE_R0"), decoded("LOAD_R2_FROM_R1")], 2);

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            register_write_value(&effects, 2).clone().canonicalize(),
            select(
                forwarding_condition(bool_const(true), read_address.clone(), write_address),
                write_value,
                read_memory(read_address, 8),
            )
            .canonicalize()
        );
    }

    #[test]
    fn instruction_seq_to_effects_applies_many_memory_forwards_in_latest_write_order() {
        let write_addresses = [read_reg(0), read_reg(1), read_reg(2), read_reg(3)];
        let read_address = read_reg(4);
        let write_values = [
            constant(0x10, 8),
            constant(0x20, 8),
            constant(0x30, 8),
            constant(0x40, 8),
        ];
        let isa = test_isa(
            vec![],
            vec![
                isa_instruction(
                    "STORE_R0",
                    vec![Effect::write_memory(
                        write_addresses[0].clone(),
                        write_values[0].clone(),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE_R1",
                    vec![Effect::write_memory(
                        write_addresses[1].clone(),
                        write_values[1].clone(),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE_R2",
                    vec![Effect::write_memory(
                        write_addresses[2].clone(),
                        write_values[2].clone(),
                        8,
                    )],
                ),
                isa_instruction(
                    "STORE_R3",
                    vec![Effect::write_memory(
                        write_addresses[3].clone(),
                        write_values[3].clone(),
                        8,
                    )],
                ),
                isa_instruction(
                    "LOAD_R5_FROM_R4",
                    vec![Effect::write_register(
                        reg(5),
                        read_memory(read_address.clone(), 8),
                    )],
                ),
            ],
        );
        let sequence = Program::from_instructions(
            vec![
                decoded("STORE_R0"),
                decoded("STORE_R1"),
                decoded("STORE_R2"),
                decoded("STORE_R3"),
                decoded("LOAD_R5_FROM_R4"),
            ],
            5,
        );
        let expected = write_addresses
            .iter()
            .cloned()
            .zip(write_values.iter().cloned())
            .fold(
                read_memory(read_address.clone(), 8),
                |fallback, (address, value)| {
                    select(
                        forwarding_condition(bool_const(true), read_address.clone(), address),
                        value,
                        fallback,
                    )
                },
            )
            .canonicalize();

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            register_write_value(&effects, 5).clone().canonicalize(),
            expected
        );
    }

    #[test]
    fn instruction_seq_to_effects_preserves_guards_in_symbolic_memory_forwarding() {
        let guard = read_register(reg(7), 1);
        let write_address = read_reg(0);
        let read_address = read_reg(1);
        let write_value = constant(0xa5, 8);
        let isa = test_isa(
            vec![],
            vec![
                isa_instruction(
                    "GUARDED_STORE_R0",
                    vec![Effect::write_memory_if(
                        guard.clone(),
                        write_address.clone(),
                        write_value.clone(),
                        8,
                    )],
                ),
                isa_instruction(
                    "LOAD_R2_FROM_R1",
                    vec![Effect::write_register(
                        reg(2),
                        read_memory(read_address.clone(), 8),
                    )],
                ),
            ],
        );
        let sequence = Program::from_instructions(
            vec![decoded("GUARDED_STORE_R0"), decoded("LOAD_R2_FROM_R1")],
            2,
        );

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            register_write_value(&effects, 2).clone().canonicalize(),
            select(
                forwarding_condition(guard, read_address.clone(), write_address),
                write_value,
                read_memory(read_address, 8),
            )
            .canonicalize()
        );
    }

    #[test]
    fn lower_memory_reads_uses_little_endian_byte_order() {
        let address = constant(0x100, 32);

        assert_eq!(
            lower_memory_reads(read_memory(address.clone(), 32)),
            concat([
                read_memory(add(address.clone(), constant(3, 32)), 8),
                read_memory(add(address.clone(), constant(2, 32)), 8),
                read_memory(add(address.clone(), constant(1, 32)), 8),
                read_memory(address, 8),
            ])
        );
    }

    #[test]
    fn lower_memory_reads_leaves_single_byte_reads_unchanged() {
        let address = constant(0x100, 32);

        assert_eq!(
            lower_memory_reads(read_memory(address.clone(), 8)),
            read_memory(address, 8)
        );
    }

    #[test]
    fn lower_memory_reads_recurses_through_other_expressions() {
        let address = constant(0x100, 32);

        assert_eq!(
            lower_memory_reads(add(read_memory(address.clone(), 16), constant(1, 16))),
            add(
                concat([
                    read_memory(add(address.clone(), constant(1, 32)), 8),
                    read_memory(address, 8),
                ]),
                constant(1, 16),
            )
        );
    }

    #[test]
    fn byte_address_preserves_base_for_zero_and_adds_byte_offsets() {
        let address = constant(0x100, 32);

        assert_eq!(byte_address(&address, 0, 32), address);
        assert_eq!(
            byte_address(&constant(0x100, 32), 7, 32),
            add(constant(0x100, 32), constant(7, 32))
        );
    }

    #[test]
    fn combine_effects_unconditional_second_register_write_wins() {
        let first = Effect::write_register(reg(0), constant(1, 32));
        let second = Effect::write_register(reg(0), constant(2, 32));

        assert_eq!(combine_effects(&first, &second), Some(second));
    }

    #[test]
    fn combine_effects_returns_none_for_different_locations() {
        let first = Effect::write_register(reg(0), constant(1, 32));
        let second = Effect::write_register(reg(1), constant(2, 32));

        assert_eq!(combine_effects(&first, &second), None);
    }

    #[test]
    fn combine_effects_returns_none_for_different_effect_kinds() {
        let register_write = Effect::write_register(reg(0), constant(1, 32));
        let memory_write = Effect::write_memory(constant(0x100, 32), constant(2, 32), 32);

        assert_eq!(combine_effects(&register_write, &memory_write), None);
        assert_eq!(combine_effects(&memory_write, &register_write), None);
    }

    #[test]
    fn combine_effects_merges_guarded_writes_to_same_location() {
        let guard_1 = read_register(reg(10), 1);
        let guard_2 = read_register(reg(11), 1);
        let value_1 = constant(1, 32);
        let value_2 = constant(2, 32);
        let first = Effect::write_register_if(guard_1.clone(), reg(0), value_1.clone());
        let second = Effect::write_register_if(guard_2.clone(), reg(0), value_2.clone());

        assert_eq!(
            combine_effects(&first, &second),
            Some(Effect::WriteRegister {
                guard: or_expr(guard_1, guard_2.clone()),
                register: reg(0),
                value: select(guard_2, value_2, value_1),
            })
        );
    }

    #[test]
    fn combine_effects_ignores_false_guarded_second_write() {
        let first = Effect::write_register_if(read_register(reg(10), 1), reg(0), constant(1, 32));
        let second = Effect::write_register_if(bool_const(false), reg(0), constant(2, 32));

        assert_eq!(combine_effects(&first, &second), Some(first));
    }

    #[test]
    fn combine_effects_handles_memory_write_edges() {
        let address = constant(0x100, 32);
        let guard = read_register(reg(10), 1);
        let first = Effect::write_memory_if(guard.clone(), address.clone(), constant(1, 32), 32);
        let same_guard_second =
            Effect::write_memory_if(guard.clone(), address.clone(), constant(2, 32), 32);
        let true_second = Effect::write_memory(address.clone(), constant(3, 32), 32);
        let false_second =
            Effect::write_memory_if(bool_const(false), address.clone(), constant(4, 32), 32);
        let different_address =
            Effect::write_memory_if(guard.clone(), constant(0x200, 32), constant(5, 32), 32);

        assert_eq!(
            combine_effects(&first, &same_guard_second),
            Some(same_guard_second)
        );
        assert_eq!(combine_effects(&first, &true_second), Some(true_second));
        assert_eq!(combine_effects(&first, &false_second), Some(first.clone()));
        assert_eq!(combine_effects(&first, &different_address), None);
    }
    #[test]
    #[ignore = "64 bit multiplication is too much for the BDD"]
    fn compare_64_bit_symbolic_multiply_commutes() {
        let isa = bdd_compare_test_isa(64);
        let x = read_register(reg(0), 64);
        let y = read_register(reg(1), 64);

        assert_bdd_compare_equal(mul(x.clone(), y.clone()), mul(y, x), &isa);
    }
}
