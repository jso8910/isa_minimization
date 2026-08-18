mod isa;
mod rewrite_util;

use std::collections::HashSet;
use std::time::Instant;

use isa::*;
use isa_minimization::bit::Bit;
use isa_minimization::isa_optimization::{ISACandidate, write_commented_gatelist};
use isa_minimization::isa_specification::{
    DecodedInstruction, FieldUses, ISA, StackDirection, StackPointer,
};
use isa_minimization::simulator::Simulator;

const NETLIST_PATH: &str = "examples/arm32_core_syn.v";
const STDCELL_PATH: &str = "examples/NangateOpenCellLibrary_typical.lib";
const OPTIMIZED_NETLIST_PATH: &str = "outputs/optimized.v";

fn main() {
    let mut args = std::env::args().skip(1);
    let program_binary_path = args.next().unwrap_or_else(|| {
        eprintln!("Usage: cargo run --example arm32 -- <program.bin> [--validate]");
        std::process::exit(2);
    });
    let validate_optimization = args.any(|arg| arg == "--validate");
    let arm32 = ISA {
        registers: registers(),
        instructions: instructions(),
        sp: StackPointer {
            register: gpr(12),
            stack_size: 32,
            direction: StackDirection::Downwards,
        },
        pc: gpr(15),
    };

    let decoded_program: Vec<DecodedInstruction> =
        DecodedInstruction::decode_program(&program_binary_path, &arm32).unwrap();
    let candidate = ISACandidate::from_program(&arm32, &decoded_program);
    let field_values = &candidate.valid_field_uses;
    let mut valid_encodings = HashSet::new();

    // for each instruction, print all valid encodings
    for instr in &arm32.instructions {
        println!("Instruction: {}", instr.name);
        for form in &instr.forms {
            // We only want to get the encodings for the form if this form actually is used in the program
            if !candidate
                .active_forms
                .get(&instr.name)
                .is_some_and(|forms| forms.contains(&form.name))
            {
                continue;
            }
            let encodings = form.fields_to_encodings(&field_values);
            println!("  Form: {}", form.name);
            for encoding in encodings {
                valid_encodings.insert(encoding.clone());

                // print as string, 0s and 1s for High and Low, and Xs for Var
                let encoding_str: String = encoding
                    .bits
                    .iter()
                    .map(|b| match b {
                        Bit::Low => '0',
                        Bit::High => '1',
                        Bit::Var => 'x',
                        Bit::Test => panic!("Test bits should not be present in final encodings"),
                    })
                    .collect();
                println!("    Encoding: {}", encoding_str);
            }
        }
    }

    println!(
        "Generated {} unique instruction encodings for optimization",
        valid_encodings.len()
    );

    // Print each field and its possible values
    println!("Fields and their possible values:");
    for (field_name, field_uses) in field_values {
        match field_uses {
            FieldUses::Uses {
                name: _, patterns, ..
            } => {
                if patterns.is_empty() {
                    continue;
                }
                println!("  Field: {}", field_name);
                for pattern in patterns {
                    let pattern_str: String = pattern
                        .bits
                        .iter()
                        .map(|b| match b {
                            Bit::Low => '0',
                            Bit::High => '1',
                            Bit::Var => 'x',
                            Bit::Test => {
                                panic!("Test bits should not be present in final field patterns")
                            }
                        })
                        .collect();
                    println!("    Pattern: {}", pattern_str);
                }
            }
            FieldUses::VariableBits {
                name: _, pattern, ..
            } => {
                if let Some(pattern) = pattern {
                    println!("  Field: {}", field_name);
                    let pattern_str: String = pattern
                        .bits
                        .iter()
                        .map(|b| match b {
                            Bit::Low => '0',
                            Bit::High => '1',
                            Bit::Var => 'x',
                            Bit::Test => {
                                panic!("Test bits should not be present in final field patterns")
                            }
                        })
                        .collect();
                    println!("    Pattern: {}", pattern_str);
                }
            }
        }
    }

    let simulator = Simulator::from_file(NETLIST_PATH, STDCELL_PATH);
    let sim_inputs: Vec<_> = valid_encodings
        .iter()
        .map(|encoding| simulator.pattern_to_sim_inputs(encoding, "inst"))
        .collect();

    println!(
        "Running gate usage optimization over {} simulation input patterns",
        sim_inputs.len()
    );

    let compiled_sim_inputs = simulator.compile_optimization_inputs(&sim_inputs);
    let mut optimization_workspace = simulator.optimization_workspace();
    let optimization_started = Instant::now();
    let optimization = simulator.optimize_compiled_gate_usage_details_with_workspace(
        &compiled_sim_inputs,
        &mut optimization_workspace,
    );
    let optimization_elapsed = optimization_started.elapsed();

    let gates_to_comment: HashSet<String> = optimization.gates_to_comment.iter().cloned().collect();

    let commented_gate_count = write_commented_gatelist(
        NETLIST_PATH,
        OPTIMIZED_NETLIST_PATH,
        &gates_to_comment,
        &optimization.assignments,
    )
    .unwrap();

    println!(
        "Kept {} combinational gates, commented out {} gates, added {} assigns, and wrote {}",
        simulator.combinational_gate_count() - optimization.gates_to_comment.len(),
        commented_gate_count,
        optimization.assignments.len(),
        OPTIMIZED_NETLIST_PATH
    );
    println!(
        "Optimization without validation took {:.3?}",
        optimization_elapsed
    );
    if validate_optimization {
        let validation = simulator.validate_compiled_gate_usage_optimization_with_workspace(
            &compiled_sim_inputs,
            &optimization,
            &mut optimization_workspace,
        );
        println!(
            "Validated {} input patterns with {} effective-output comparisons, {} replacement-output proofs, and {} gate evaluations in {:.3?}",
            validation.input_patterns_checked,
            validation.effective_outputs_checked,
            validation.replacement_outputs_checked,
            validation.gate_evaluations,
            validation.elapsed,
        );
    }
    // // Program: add r0, r0, r1; mov r1, r0
    // let program = DecodedInstruction::decode_program_str(
    //     "11100000100000000000000000000001\n11100001101000000001000000000000",
    //     &arm32,
    // )
    // Program: mov r5, #3; mul r4, r4, r5
    // let program = DecodedInstruction::decode_program_str(
    //     "11100011101000000101000000000011\n11100000000001000000010110010100",
    //     &arm32,
    // )
    // .unwrap();
    // let effects = instruction_seq_to_effects(&program, &arm32);
    // println!("\n\n\n\n\n\n\n");
    // for effect in &effects {
    //     println!("{:#?}", effect);
    // }

    // // program2: add r1, r0, r1
    // let program2 =
    //     DecodedInstruction::decode_program_str("11100000100000000001000000000001", &arm32).unwrap();
    // let effects2 = instruction_seq_to_effects(&program2, &arm32);
    // // effects[1] should be the write to r1 (mov r1, r0) and effects2[0] should be add r1, r0, r1. so these should be semantically equivalent in their contexts
    // assert_eq!(effects[1], effects2[0]);
}
