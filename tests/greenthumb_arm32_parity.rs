#[allow(dead_code)]
#[path = "../examples/arm32.rs"]
mod arm32;

use std::process::Command;

use isa_minimization::{
    instruction_semantics::Effect,
    isa_specification::{DecodedInstruction, ISA, StackDirection, StackPointer},
    semantic_matching::{
        BitWord, MachineState, evaluate_expr, instruction_seq_to_effects,
        write_concrete_memory_bytes,
    },
    superoptimization::Program,
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
        pc_to_instruction_index: arm32::pc_to_instruction_index,
        instruction_index_to_pc: arm32::instruction_index_to_pc,
    }
}

fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

fn run_green_thumb(args: &[&str]) -> String {
    let quoted_args = args
        .iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ");
    let command = format!(
        "source greenthumb/source.sh && racket greenthumb/arm/tests/arm32-parity-cli.rkt {quoted_args}"
    );
    let output = Command::new("zsh")
        .arg("-lc")
        .arg(command)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("failed to run GreenThumb parity CLI");

    assert!(
        output.status.success(),
        "GreenThumb parity CLI failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8(output.stdout).expect("GreenThumb parity CLI output should be UTF-8")
}

fn decode_word(isa: &ISA, word: u32) -> DecodedInstruction {
    let bits = format!("{word:032b}");
    let decoded = DecodedInstruction::decode_program_str(&bits, isa).expect("word should decode");
    assert_eq!(decoded.len(), 1);
    decoded.into_iter().next().unwrap()
}

fn execute_words(isa: &ISA, words: &[u32], state: &MachineState) -> MachineState {
    let decoded = words
        .iter()
        .map(|word| decode_word(isa, *word))
        .collect::<Vec<_>>();
    let program = Program::from_instructions(decoded, words.len());
    let effects = instruction_seq_to_effects(&program, isa);
    execute_effects(&effects, state)
}

fn execute_effects(effects: &[Effect], state: &MachineState) -> MachineState {
    let mut next_state = state.clone();
    for effect in effects {
        match effect {
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                if evaluate_expr(guard, state).is_none_or(|guard| guard.value == 0) {
                    continue;
                }
                if let (Some(register), Some(value)) =
                    (evaluate_expr(register, state), evaluate_expr(value, state))
                {
                    next_state.registers.insert(register.value, value);
                }
            }
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                if evaluate_expr(guard, state).is_none_or(|guard| guard.value == 0) {
                    continue;
                }
                if let (Some(address), Some(value)) =
                    (evaluate_expr(address, state), evaluate_expr(value, state))
                {
                    write_concrete_memory_bytes(&mut next_state, address, value, *width);
                }
            }
        }
    }
    next_state
}

fn state_with_regs(regs: [u32; 16]) -> MachineState {
    let mut state = MachineState::default();
    for (index, value) in regs.into_iter().enumerate() {
        state
            .registers
            .insert(index as u128, BitWord::new(value as u128, 32));
    }
    state
}

fn write_word_bytes(state: &mut MachineState, address: u128, value: u32) {
    for byte_index in 0..4 {
        let byte = (value >> (byte_index * 8)) & 0xff;
        state.memory.insert(
            (address + byte_index as u128, 8),
            BitWord::new(byte as u128, 8),
        );
    }
}

fn parse_hex_word(value: &str) -> u32 {
    u32::from_str_radix(
        value
            .strip_prefix("0x")
            .expect("GreenThumb word should be hex"),
        16,
    )
    .expect("GreenThumb word should parse")
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Observation {
    Register(u128),
    Memory(u128),
}

fn parse_observations(output: &str) -> Vec<(Observation, u128)> {
    output
        .lines()
        .map(|line| {
            let parts = line.split_whitespace().collect::<Vec<_>>();
            assert_eq!(
                parts.len(),
                3,
                "observation line should have three columns: {line}"
            );
            let index = parts[1].parse::<u128>().expect("observation index parses");
            let value = parts[2].parse::<i128>().expect("observation value parses");
            let value = value as u128;
            match parts[0] {
                "reg" => (Observation::Register(index), value & 0xffff_ffff),
                "mem" => (Observation::Memory(index), value & 0xff),
                other => panic!("unknown observation kind: {other}"),
            }
        })
        .collect()
}

#[test]
fn rust_fixtures_encode_to_expected_greenthumb_words() {
    let fixtures: &[(&str, &[&str], &str)] = &[
        (
            "raw-load-writeback-down",
            &[
                "encode",
                "ldr-full#",
                "||",
                "||",
                "0",
                "1",
                "12",
                "1",
                "0",
                "1",
            ],
            "0xe531000c",
        ),
        (
            "raw-store-byte-shifted-register",
            &[
                "encode",
                "strb-full",
                "||",
                "lsl#",
                "2",
                "3",
                "4",
                "1",
                "1",
                "0",
                "2",
            ],
            "0xe7c32104",
        ),
        (
            "raw-halfword-load",
            &[
                "encode",
                "ldrh-full#",
                "||",
                "||",
                "0",
                "1",
                "2",
                "1",
                "1",
                "0",
            ],
            "0xe1d100b2",
        ),
        (
            "raw-block-store-db-writeback",
            &["encode", "stm-full#", "||", "||", "3", "5", "1", "0", "1"],
            "0xe9230005",
        ),
        (
            "raw-block-load-ia-writeback",
            &["encode", "ldm-full#", "||", "||", "3", "5", "0", "1", "1"],
            "0xe8b30005",
        ),
    ];

    for (name, args, expected) in fixtures {
        let actual = run_green_thumb(args);
        assert_eq!(actual.trim(), *expected, "{name}");
    }
}

#[test]
fn greenthumb_generated_samples_decode_as_expected_rust_forms() {
    let isa = arm32_isa();
    let output = run_green_thumb(&["samples"]);

    for line in output.lines() {
        let parts = line.split_whitespace().collect::<Vec<_>>();
        assert_eq!(
            parts.len(),
            4,
            "sample line should have four columns: {line}"
        );
        let sample = parts[0];
        let expected_name = parts[1];
        let expected_form = parts[2];
        let word = parse_hex_word(parts[3]);
        let decoded = decode_word(&isa, word);

        assert_eq!(decoded.name, expected_name, "{sample} instruction name");
        assert_eq!(decoded.form.name, expected_form, "{sample} form name");
    }
}

#[test]
fn greenthumb_rejects_rust_invalid_representatives() {
    let invalid: &[(&str, &[&str])] = &[
        (
            "post-index-pc-base",
            &[
                "encode",
                "ldr-full#",
                "||",
                "||",
                "0",
                "15",
                "4",
                "0",
                "1",
                "0",
            ],
        ),
        (
            "empty-block-reglist",
            &["encode", "stm-full#", "||", "||", "3", "0", "0", "1", "0"],
        ),
        (
            "block-pc-base",
            &["encode", "ldm-full#", "||", "||", "15", "5", "0", "1", "0"],
        ),
        ("swap-pc-rd", &["encode", "swp", "||", "||", "15", "1", "2"]),
    ];

    for (name, args) in invalid {
        let actual = run_green_thumb(args);
        assert_eq!(actual.trim(), "#f", "{name}");
    }
}

#[test]
fn concrete_semantic_samples_match_between_rust_and_greenthumb() {
    let isa = arm32_isa();
    let mut ldm_state = state_with_regs([0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000]);
    write_word_bytes(&mut ldm_state, 100, 0x1122_3344);

    let samples: &[(&str, &[u32], MachineState)] = &[
        (
            "store_byte_layout_writeback",
            &[0xe481_2004],
            state_with_regs([
                0,
                100,
                0x1234_5678,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                1000,
            ]),
        ),
        ("ldm_writeback_overridden", &[0xe8b3_0008], ldm_state),
        (
            "stm_store_old_base",
            &[0xe923_0005],
            state_with_regs([11, 22, 33, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1000]),
        ),
    ];

    for (sample, words, state) in samples {
        let rust_output = execute_words(&isa, words, state);
        let greenthumb_output = run_green_thumb(&["run-sample", sample]);
        for (observation, greenthumb_value) in parse_observations(&greenthumb_output) {
            let rust_value = match observation {
                Observation::Register(register) => {
                    rust_output
                        .registers
                        .get(&register)
                        .unwrap_or_else(|| panic!("{sample}: missing Rust register r{register}"))
                        .value
                        & 0xffff_ffff
                }
                Observation::Memory(address) => {
                    rust_output
                        .memory
                        .get(&(address, 8))
                        .unwrap_or_else(|| panic!("{sample}: missing Rust memory byte {address}"))
                        .value
                        & 0xff
                }
            };
            assert_eq!(rust_value, greenthumb_value, "{sample}: {observation:?}");
        }
    }
}
