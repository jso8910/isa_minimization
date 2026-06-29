// Given a certain instruction, a specification for the ISA,
// as well as a list of valid values for features, the goal
// of this file is to
//      1. Identify whether the instruction is valid under the new ISA
//      2. If it is not valid, generate some functionally equivalent replacement for the instruction

use std::collections::HashMap;

use crate::{
    instruction_semantics::{Effect, Expr, FieldName, OperandRef, RegisterRef},
    isa_specification::{
        ArchitecturalRegister, DecodedInstruction, FieldUses, Instruction, StackDirection, ISA,
    },
    semantic_matching::instruction_seq_to_effects,
};

pub struct SuperoptimizationCtx {
    pub field_values: HashMap<FieldName, FieldUses>,
    pub isa: Vec<Instruction>,
    // A list of already found equivalent instruction sequences (Instruction -> Multiple instructions)
    equivalent_instruction_sequences: Vec<(Instruction, Vec<Instruction>)>,
}

/// Cheaply rejects generated instruction sequences that use unsupported state destinations.
///
/// This is intended for the superoptimization hot path. It performs only syntactic checks after
/// lowering effects into the initial-state coordinate system:
/// - register write destinations must be constants/fixed registers,
/// - the stack pointer register may not be written,
/// - memory writes must either target an original memory write destination exactly or an approved
///   SP-relative scratch byte,
/// - every original write destination must have a corresponding generated write destination.
pub fn generated_sequence_meets_state_constraints(
    generated: &[DecodedInstruction],
    original: &[DecodedInstruction],
    isa: &ISA,
) -> bool {
    let original_effects = instruction_seq_to_effects(original, isa);
    let generated_effects = instruction_seq_to_effects(generated, isa);

    generated_effects_meet_state_constraints(&generated_effects, &original_effects, isa)
}

/// Checks already-lowered effects against the same destination constraints as
/// `generated_sequence_meets_state_constraints`.
///
/// Use this in hot paths when the original sequence's effects have already been computed.
pub fn generated_effects_meet_state_constraints(
    generated_effects: &[Effect],
    original_effects: &[Effect],
    isa: &ISA,
) -> bool {
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

    generated_effects.iter().all(|effect| match effect {
        Effect::WriteRegister { register, .. } => register_destination(register)
            .is_some_and(|destination| destination != isa.sp.register.identifier as u128),
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
        instruction_semantics::{add, constant, fixed_register, read_register, sub, Register},
        isa_specification::{InstructionForm, StackPointer},
    };

    const SP_ID: u8 = 31;
    const PC_ID: u8 = 30;

    fn arch_register(identifier: u8) -> ArchitecturalRegister {
        ArchitecturalRegister {
            identifier,
            identifier_width: 8,
            width: 32,
        }
    }

    fn test_isa(direction: StackDirection) -> ISA {
        let sp = arch_register(SP_ID);
        ISA {
            registers: vec![arch_register(0), arch_register(1), arch_register(2), sp],
            instructions: vec![],
            sp: StackPointer {
                register: sp,
                stack_size: 16,
                direction,
            },
            pc: arch_register(PC_ID),
        }
    }

    fn decoded(name: &str) -> DecodedInstruction {
        DecodedInstruction {
            name: Some(name.to_owned()),
            form: Some(InstructionForm::new(format!("{name}_form"))),
            bits: Vec::new(),
            fields: Vec::new(),
        }
    }

    fn instruction(name: &str, effects: Vec<Effect>) -> Instruction {
        let mut instruction = Instruction::new(name, 0);
        instruction.effects = effects;
        instruction
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

    fn sequence(name: &str) -> Vec<DecodedInstruction> {
        vec![decoded(name)]
    }

    #[test]
    fn accepts_fixed_register_writes_and_original_memory_destinations() {
        let original_address = read_reg(0);
        let mut isa = test_isa(StackDirection::Downwards);
        isa.instructions = vec![
            instruction(
                "ORIGINAL",
                vec![Effect::write_memory(
                    original_address.clone(),
                    constant(0xaa, 8),
                    8,
                )],
            ),
            instruction(
                "GENERATED",
                vec![
                    Effect::write_register(fixed_reg(1), constant(0x12, 32)),
                    Effect::write_memory(original_address, constant(0xbb, 8), 8),
                ],
            ),
        ];

        assert!(generated_sequence_meets_state_constraints(
            &sequence("GENERATED"),
            &sequence("ORIGINAL"),
            &isa
        ));
    }

    #[test]
    fn rejects_generated_sequences_missing_original_effect_destinations() {
        let original_address = read_reg(0);
        let mut isa = test_isa(StackDirection::Downwards);
        isa.instructions = vec![
            instruction(
                "ORIGINAL",
                vec![
                    Effect::write_register(fixed_reg(1), constant(0x12, 32)),
                    Effect::write_memory(original_address.clone(), constant(0xaa, 8), 8),
                ],
            ),
            instruction(
                "ONLY_REGISTER",
                vec![Effect::write_register(fixed_reg(1), constant(0x34, 32))],
            ),
            instruction(
                "ONLY_MEMORY",
                vec![Effect::write_memory(
                    original_address.clone(),
                    constant(0xbb, 8),
                    8,
                )],
            ),
            instruction(
                "ONLY_STACK_SCRATCH",
                vec![Effect::write_memory(
                    sub(sp_value(), constant(4, 32)),
                    constant(0xcc, 8),
                    8,
                )],
            ),
        ];

        assert!(!generated_sequence_meets_state_constraints(
            &sequence("ONLY_REGISTER"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("ONLY_MEMORY"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("ONLY_STACK_SCRATCH"),
            &sequence("ORIGINAL"),
            &isa
        ));
    }

    #[test]
    fn rejects_nonconstant_register_destinations_and_stack_pointer_writes() {
        let mut isa = test_isa(StackDirection::Downwards);
        isa.instructions = vec![
            instruction("ORIGINAL", vec![]),
            instruction(
                "NONCONST_REG_DEST",
                vec![Effect::write_register(read_reg(0), constant(0x12, 32))],
            ),
            instruction(
                "SP_WRITE",
                vec![Effect::write_register(fixed_reg(SP_ID), constant(0x12, 32))],
            ),
        ];

        assert!(!generated_sequence_meets_state_constraints(
            &sequence("NONCONST_REG_DEST"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("SP_WRITE"),
            &sequence("ORIGINAL"),
            &isa
        ));
    }

    #[test]
    fn accepts_only_downward_sp_relative_stack_scratch_for_downward_stacks() {
        let mut isa = test_isa(StackDirection::Downwards);
        isa.instructions = vec![
            instruction("ORIGINAL", vec![]),
            instruction(
                "STACK_DOWN",
                vec![Effect::write_memory(
                    sub(sp_value(), constant(4, 32)),
                    constant(0xaa, 8),
                    8,
                )],
            ),
            instruction(
                "STACK_UP",
                vec![Effect::write_memory(
                    add(sp_value(), constant(4, 32)),
                    constant(0xaa, 8),
                    8,
                )],
            ),
            instruction(
                "STACK_TOO_FAR",
                vec![Effect::write_memory(
                    sub(sp_value(), constant(17, 32)),
                    constant(0xaa, 8),
                    8,
                )],
            ),
            instruction(
                "ARBITRARY_MEMORY",
                vec![Effect::write_memory(read_reg(0), constant(0xaa, 8), 8)],
            ),
        ];

        assert!(generated_sequence_meets_state_constraints(
            &sequence("STACK_DOWN"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("STACK_UP"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("STACK_TOO_FAR"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("ARBITRARY_MEMORY"),
            &sequence("ORIGINAL"),
            &isa
        ));
    }

    #[test]
    fn accepts_only_upward_sp_relative_stack_scratch_for_upward_stacks() {
        let mut isa = test_isa(StackDirection::Upwards);
        isa.instructions = vec![
            instruction("ORIGINAL", vec![]),
            instruction(
                "STACK_UP",
                vec![Effect::write_memory(
                    add(sp_value(), constant(4, 32)),
                    constant(0xaa, 8),
                    8,
                )],
            ),
            instruction(
                "STACK_DOWN",
                vec![Effect::write_memory(
                    sub(sp_value(), constant(4, 32)),
                    constant(0xaa, 8),
                    8,
                )],
            ),
        ];

        assert!(generated_sequence_meets_state_constraints(
            &sequence("STACK_UP"),
            &sequence("ORIGINAL"),
            &isa
        ));
        assert!(!generated_sequence_meets_state_constraints(
            &sequence("STACK_DOWN"),
            &sequence("ORIGINAL"),
            &isa
        ));
    }
}
