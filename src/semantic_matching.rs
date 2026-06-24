// Contains code to evaluate whether two Exprs are semantically equivalent
// Pipeline
//  1. Simple check to see if canonical form of Exprs are equal (if this succeeds great!)
//  2. Random testing to attempt to see if the Exprs are obviously different
//  3. Z3 (easier to program) or Bitwuzla (potentially faster) SMT solver to authoritatively check if the two Exprs are equivalent

use crate::{
    instruction_semantics::{
        Effect, Expr, add, concat, constant, extract, or_expr, read_memory, select,
    },
    isa_specification::{DecodedInstruction, Instruction},
};

pub type InstructionIdx = u32;

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

// impl StateUseTable {
//     pub fn from_program(program: &Vec<DecodedInstruction>, isa: &Vec<Instruction>) -> Self {
//         for instruction in program.iter() {
//             let lowered_effects = instruction_to_lowered_effects(instruction, isa, &vec![]);
//         }
//         StateUseTable { updates: () }
//     }
// }

/// Given some sequence of instructions, create a list of all Effects of the sequence in terms of the initial state
/// Includes lowering memory accesses to single-byte accesses
/// This effectively collapses instructions.len() = k instructions into a single state update u where s(t0+k) = u(s(t0))
pub fn instruction_seq_to_effects(
    instructions: &[DecodedInstruction],
    isa: &[Instruction],
) -> Vec<Effect> {
    let mut seq_effects = vec![];
    for instruction in instructions.iter() {
        let lowered_effects = instruction_to_lowered_effects(instruction, isa, &seq_effects);

        // We want to combine the effects of this instruction with the existing effects in seq_effects
        // The variable name effect_2 refers to the fact that it takes place after the effect_1s that we are comparing it to
        for effect_2 in lowered_effects {
            // Whether we've found an effect in seq_effects which writes to the same place as effect_2
            let mut found_same_write = false;
            for effect_1 in seq_effects.iter_mut() {
                if let Some(new_effect) = combine_effects(effect_1, &effect_2) {
                    *effect_1 = new_effect;
                    found_same_write = true;
                }
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
        }
    }
    seq_effects
}

pub fn instruction_to_lowered_effects(
    instruction: &DecodedInstruction,
    isa: &[Instruction],
    previous_effects: &[Effect],
) -> Vec<Effect> {
    let instruction_name = instruction
        .name
        .as_ref()
        .expect("Instruction should have a name");
    let instruction_effects = &isa
        .iter()
        .find(|candidate| candidate.name == *instruction_name)
        .unwrap_or_else(|| {
            panic!(
                "Instruction in sequence should match with an instruction in the ISA, but {instruction_name} did not match!"
            )
        })
        .effects;
    let mut lowered_effects = Vec::with_capacity(instruction_effects.len());
    for effect in instruction_effects.iter().cloned() {
        match effect {
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                let guard = collapse_lower_substitute(guard, instruction, previous_effects);
                let address = collapse_lower_substitute(address, instruction, previous_effects);
                let value = collapse_lower_substitute(value, instruction, previous_effects);
                if width == 8 {
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
                        lowered_effects.push(Effect::WriteMemory {
                            guard: guard.clone(),
                            address: byte_address(&address, byte_index, address_width),
                            value: extract(value.clone(), low + 7, low),
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
                let guard = collapse_lower_substitute(guard, instruction, previous_effects);
                let register = collapse_lower_substitute(register, instruction, previous_effects);
                let value = collapse_lower_substitute(value, instruction, previous_effects);
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

fn collapse_lower_substitute(
    expr: Expr,
    instruction: &DecodedInstruction,
    previous_effects: &[Effect],
) -> Expr {
    lower_memory_reads(expr.collapse(instruction))
        .substitute(previous_effects)
        .canonicalize()
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
        instruction_semantics::{Register, bool_const, fixed_register, read_memory, read_register},
        isa_specification::InstructionForm,
    };

    fn decoded(name: &str) -> DecodedInstruction {
        DecodedInstruction {
            name: Some(name.to_owned()),
            form: Some(InstructionForm::new(format!("{name}_form"))),
            bits: Vec::new(),
            fields: Vec::new(),
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

    #[test]
    fn instruction_seq_to_effects_does_not_double_substitute_register_reads() {
        let r0 = read_reg(0);
        let single_add = add(r0.clone(), r0).canonicalize();
        let double_substituted = add(single_add.clone(), single_add.clone()).canonicalize();
        let isa = vec![
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
        ];
        let sequence = vec![decoded("ADD_R0_R0_R0"), decoded("MOV_R1_R0")];

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(register_write_value(&effects, 0), &single_add);
        assert_eq!(register_write_value(&effects, 1), &single_add);
        assert_ne!(register_write_value(&effects, 1), &double_substituted);
    }

    #[test]
    fn instruction_seq_to_effects_lowers_memory_writes_to_bytes() {
        let address = constant(0x100, 32);
        let value = constant(0xaabb_ccdd, 32);
        let isa = vec![isa_instruction(
            "STORE32",
            vec![Effect::write_memory(address.clone(), value.clone(), 32)],
        )];
        let sequence = vec![decoded("STORE32")];

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
        let isa = vec![
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
        ];
        let sequence = vec![decoded("STORE32"), decoded("LOAD32_R0")];

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            register_write_value(&effects, 0),
            &concat([
                extract(value.clone(), 31, 24),
                extract(value.clone(), 23, 16),
                extract(value.clone(), 15, 8),
                extract(value, 7, 0),
            ])
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
}
