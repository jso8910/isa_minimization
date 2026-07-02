#[allow(dead_code)]
#[path = "../examples/arm32.rs"]
mod arm32;

use std::collections::HashMap;

use isa_minimization::{
    bit::{Bit, BitPattern},
    instruction_semantics::FieldName,
    isa_specification::{
        DecodedField, DecodedInstruction, FieldUses, ISA, MergeMode, StackDirection, StackPointer,
    },
    superoptimization::SuperoptimizationCtx,
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
    }
}

fn field_uses_from(program: &[DecodedInstruction]) -> HashMap<FieldName, FieldUses> {
    let mut field_values = HashMap::new();

    for decoded in program {
        for DecodedField {
            name,
            value,
            merge_mode,
            ..
        } in &decoded.fields
        {
            let Some(name) = name else {
                continue;
            };
            let default_value = match merge_mode {
                MergeMode::Uses => FieldUses::Uses {
                    name: name.clone(),
                    patterns: [value.clone()].into_iter().collect(),
                },
                MergeMode::VariableBits => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: value.clone(),
                },
            };

            match field_values.entry(name.clone()).or_insert(default_value) {
                FieldUses::Uses { patterns, .. } => {
                    patterns.insert(value.clone());
                }
                FieldUses::VariableBits { pattern, .. } => {
                    assert_eq!(pattern.len(), value.len());
                    for (pattern_bit, value_bit) in pattern.bits.iter_mut().zip(&value.bits) {
                        if pattern_bit != value_bit {
                            *pattern_bit = Bit::Var;
                        }
                    }
                }
            }
        }
    }

    field_values
}

fn decode_one(bits: &str, isa: &ISA) -> DecodedInstruction {
    let decoded = DecodedInstruction::decode_program_str(bits, isa).expect("ARM32 decode failed");
    assert_eq!(decoded.len(), 1);
    decoded.into_iter().next().unwrap()
}

fn bit_string(decoded: &DecodedInstruction) -> String {
    decoded
        .bits
        .iter()
        .map(|bit| match bit {
            Bit::Low => '0',
            Bit::High => '1',
            Bit::Var => 'x',
            Bit::Test => 't',
        })
        .collect()
}

fn all_patterns(width: usize) -> Vec<BitPattern> {
    assert!(width <= 16, "test helper only expects small Uses fields");
    (0..(1usize << width))
        .map(|value| {
            BitPattern::new(
                (0..width)
                    .rev()
                    .map(|bit| {
                        if value & (1usize << bit) == 0 {
                            Bit::Low
                        } else {
                            Bit::High
                        }
                    })
                    .collect(),
            )
        })
        .collect()
}

fn broad_field_uses_except_sub(isa: &ISA) -> HashMap<FieldName, FieldUses> {
    let mut field_uses = HashMap::new();

    for instruction in &isa.instructions {
        for form in &instruction.forms {
            for field in &form.fields {
                let Some(name) = &field.name else {
                    continue;
                };

                field_uses
                    .entry(name.clone())
                    .or_insert_with(|| match field.merge_mode {
                        MergeMode::Uses => {
                            let mut patterns = all_patterns(field.pattern.len());
                            if name == "data_proc_opcode" {
                                patterns.retain(|pattern| pattern != &BitPattern::parse("0010"));
                            } else {
                                patterns = vec![BitPattern::parse(&"x".repeat(field.pattern.len()))]
                            }
                            FieldUses::Uses {
                                name: name.clone(),
                                patterns: patterns.into_iter().collect(),
                            }
                        }
                        MergeMode::VariableBits => FieldUses::VariableBits {
                            name: name.clone(),
                            pattern: BitPattern::variable(field.pattern.len()),
                        },
                    });
            }
        }
    }

    field_uses
}

#[test]
#[ignore = "naive superoptimizer path is currently unfinished/slow"]
fn naive_superoptimize_finds_commuted_arm32_add_with_removed_operand_features() {
    let isa = arm32_isa();
    let original = decode_one("11100000100000000001000000000001", &isa);
    let candidate = decode_one("11100000100000010001000000000000", &isa);
    let valid_field_uses = field_uses_from(std::slice::from_ref(&candidate));
    let mut ctx =
        SuperoptimizationCtx::new_from_single_instruction(original, valid_field_uses, &isa, vec![]);

    let replacement = ctx
        .naive_superoptimize()
        .expect("ARM32 commuted ADD should be found");
    let replacement = replacement.iter_instructions().collect::<Vec<_>>();

    assert_eq!(replacement.len(), 1);
    assert_eq!(bit_string(replacement[0]), bit_string(&candidate));
}

#[test]
#[ignore = "naive superoptimizer path is currently unfinished/slow"]
fn naive_superoptimize_finds_two_instruction_arm32_immediate_replacement() {
    let isa = arm32_isa();
    let original_mov_two = decode_one("11100011101000000001000000000010", &isa);
    let mov_one = decode_one("11100011101000000001000000000001", &isa);
    let add_one = decode_one("11100010100000010001000000000001", &isa);
    let valid_field_uses = field_uses_from(&[mov_one.clone(), add_one.clone()]);
    let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
        original_mov_two,
        valid_field_uses,
        &isa,
        vec![],
    );

    let replacement = ctx
        .naive_superoptimize()
        .expect("ARM32 MOV #2 should be synthesized from MOV #1; ADD #1");
    let replacement = replacement.iter_instructions().collect::<Vec<_>>();

    assert_eq!(replacement.len(), 2);

    let first = bit_string(replacement[0]);
    let valid_mov_one_encodings = [
        "11100011101000000001000000000001",
        "11100011101000010001000000000001",
    ];
    assert!(valid_mov_one_encodings.contains(&first.as_str()));
    assert_eq!(bit_string(replacement[1]), bit_string(&add_one));
}

#[test]
#[ignore = "broad ARM32 search stress test: bans only SUB and may enumerate many candidates"]
fn naive_superoptimize_replaces_arm32_sub_when_only_sub_opcode_is_banned() {
    let isa = arm32_isa();
    let original_sub = decode_one("11100000010000000001000000000010", &isa);
    let expected_replacement = [
        decode_one("11100001111000000001000000000010", &isa),
        decode_one("11100010100000010001000000000001", &isa),
        decode_one("11100000100000000001000000000001", &isa),
    ];
    let valid_field_uses = broad_field_uses_except_sub(&isa);
    let mut ctx = SuperoptimizationCtx::new_from_single_instruction(
        original_sub,
        valid_field_uses,
        &isa,
        vec![],
    );

    let replacement = ctx
        .naive_superoptimize()
        .expect("SUB should be replaceable as MVN; ADD #1; ADD");
    let replacement = replacement.iter_instructions().collect::<Vec<_>>();

    eprintln!(
        "broad ARM32 SUB replacement bits = {:?}",
        replacement
            .iter()
            .copied()
            .map(bit_string)
            .collect::<Vec<_>>()
    );

    assert_eq!(
        replacement
            .iter()
            .copied()
            .map(bit_string)
            .collect::<Vec<_>>(),
        expected_replacement
            .iter()
            .map(bit_string)
            .collect::<Vec<_>>()
    );
}
