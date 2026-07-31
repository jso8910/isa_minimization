#[allow(dead_code, unused_imports)]
#[path = "../examples/arm32.rs"]
mod arm32;

use std::{collections::HashMap, sync::LazyLock, time::Duration};

use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main,
};

use isa_minimization::{
    bit::Bit,
    instruction_semantics::FieldName,
    isa_specification::{
        DecodedField, DecodedInstruction, FieldUses, ISA, MergeMode, StackDirection, StackPointer,
    },
    superoptimization::SuperoptimizationCtx,
};

const CANDIDATE_LOOP_ITERS: u32 = 25;

static ARM32_ISA: LazyLock<ISA> = LazyLock::new(arm32_isa);

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
    }
}

fn decode_one(bits: &str, isa: &ISA) -> DecodedInstruction {
    let decoded = DecodedInstruction::decode_program_str(bits, isa).expect("ARM32 decode failed");
    assert_eq!(decoded.len(), 1);
    decoded.into_iter().next().expect("decoded one instruction")
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
                    len: value.len(),
                },
                MergeMode::VariableBits => FieldUses::VariableBits {
                    name: name.clone(),
                    pattern: Some(value.clone()),
                    len: value.len(),
                },
            };

            match field_values.entry(name.clone()).or_insert(default_value) {
                FieldUses::Uses { patterns, .. } => {
                    patterns.insert(value.clone());
                }
                FieldUses::VariableBits { pattern, len, .. } => {
                    assert_eq!(*len, value.len());
                    let pattern = pattern
                        .as_mut()
                        .expect("observed VariableBits field should be populated");
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

fn benchmark_context() -> SuperoptimizationCtx<'static> {
    let isa = &ARM32_ISA;
    let original_mov_two = decode_one("11100011101000000001000000000010", isa);
    let mov_one = decode_one("11100011101000000001000000000001", isa);
    let add_one = decode_one("11100010100000010001000000000001", isa);
    let valid_field_uses = field_uses_from(&[mov_one, add_one]);

    SuperoptimizationCtx::new_from_single_instruction(
        original_mov_two,
        valid_field_uses,
        isa,
        vec![],
    )
}

fn bench_generate_candidates(c: &mut Criterion) {
    let mut group = c.benchmark_group("generate_accept_candidates");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));
    group.throughput(Throughput::Elements(u64::from(CANDIDATE_LOOP_ITERS)));

    group.bench_with_input(
        BenchmarkId::from_parameter(CANDIDATE_LOOP_ITERS),
        &CANDIDATE_LOOP_ITERS,
        |b, &iters| {
            b.iter_batched(
                benchmark_context,
                |mut ctx| {
                    ctx.generate_candidates(usize::MAX, black_box(iters - 1));
                    black_box(ctx.perfect_matches().len())
                },
                BatchSize::SmallInput,
            );
        },
    );

    group.finish();
}

criterion_group!(benches, bench_generate_candidates);
criterion_main!(benches);
