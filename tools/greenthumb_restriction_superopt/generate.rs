#[path = "../../examples/arm32/isa.rs"]
mod arm32;

use std::{
    env, fs,
    io::ErrorKind,
    path::{Path, PathBuf},
};

use isa_minimization::{
    greenthumb_restrictions::{GreenthumbRestrictionOptions, GreenthumbRestrictionSet},
    isa_optimization::ISACandidate,
    isa_specification::{ISA, StackDirection, StackPointer},
};

const DEFAULT_OUTPUT_DIR: &str = "greenthumb/arm/restriction-superopt/generated";

struct Case {
    name: &'static str,
    input: &'static str,
    live_out: &'static str,
    denies: Vec<&'static str>,
    forbidden_opcodes: Vec<&'static str>,
    expected_shape: &'static str,
    size: u32,
    timeout: u32,
    hard: bool,
    require_discovered: bool,
    mode: &'static str,
    stack_scratch: Option<StackScratch>,
}

#[derive(Clone, Copy)]
struct StackScratch {
    register: u8,
    size: u32,
    direction: &'static str,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let out_dir = env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_OUTPUT_DIR));
    generate_cases(&out_dir)
}

fn generate_cases(out_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    fs::create_dir_all(out_dir)?;

    let isa = arm32_isa();
    let base_candidate = ISACandidate::max_isa(&isa);
    let options = GreenthumbRestrictionOptions {
        exclude_branches: true,
        exclude_multiplies: true,
        exclude_extension_ops: true,
    };
    let base_restrictions =
        GreenthumbRestrictionSet::from_candidate(&isa, &base_candidate, &options);

    for case in cases() {
        let case_dir = out_dir.join(case.name);
        fs::create_dir_all(&case_dir)?;

        fs::write(case_dir.join("input.s"), ensure_newline(case.input))?;
        fs::write(case_dir.join("input.s.info"), ensure_newline(case.live_out))?;
        match fs::remove_file(case_dir.join("inputs")) {
            Ok(()) => {}
            Err(err) if err.kind() == ErrorKind::NotFound => {}
            Err(err) => return Err(Box::new(err)),
        }

        let restrictions = base_restrictions
            .clone()
            .with_deny_patterns(case.denies.iter().map(|pattern| (*pattern).to_string()));
        fs::write(
            case_dir.join("restrict.rkt"),
            restrictions.to_racket_default_deny(),
        )?;
        fs::write(case_dir.join("expected.rkt"), expected_metadata(&case))?;
    }

    Ok(())
}

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

fn ensure_newline(text: &str) -> String {
    if text.ends_with('\n') {
        text.to_string()
    } else {
        format!("{text}\n")
    }
}

fn expected_metadata(case: &Case) -> String {
    let stack_scratch = match case.stack_scratch {
        Some(config) => format!(
            "(stack-scratch ({} {} {}))",
            config.register, config.size, config.direction
        ),
        None => "(stack-scratch #f)".to_string(),
    };

    format!(
        "((name \"{}\")\n (hard {})\n (timeout {})\n (size {})\n (workers 4)\n {}\n (require-discovered {})\n (mode \"{}\")\n (expected-shape \"{}\")\n (forbidden-opcodes {}))\n",
        case.name,
        racket_bool(case.hard),
        case.timeout,
        case.size,
        stack_scratch,
        racket_bool(case.require_discovered),
        escape(case.mode),
        escape(case.expected_shape),
        racket_string_list(&case.forbidden_opcodes),
    )
}

fn racket_bool(value: bool) -> &'static str {
    if value { "#t" } else { "#f" }
}

fn racket_string_list(values: &[&str]) -> String {
    format!(
        "({})",
        values
            .iter()
            .map(|value| format!("\"{}\"", escape(value)))
            .collect::<Vec<_>>()
            .join(" ")
    )
}

fn escape(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
}

fn cases() -> Vec<Case> {
    let branch_forbidden = &["b", "bl", "bx"];
    vec![
        Case {
            name: "01_sub_without_subtract_family",
            input: "sub r0, r1, r2",
            live_out: "0",
            denies: vec![
                dp_opcode("0010"),
                dp_opcode("0011"),
                dp_opcode("0110"),
                dp_opcode("0111"),
                dp_opcode("1010"),
            ],
            forbidden_opcodes: vec!["sub", "rsb", "sbc", "rsc", "cmp"],
            expected_shape: "mvn tmp, r2; add r0, r1, tmp; add r0, r0, #1",
            size: 3,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "02_rsb_without_subtract_family",
            input: "rsb r0, r1, r2",
            live_out: "0",
            denies: vec![
                dp_opcode("0010"),
                dp_opcode("0011"),
                dp_opcode("0110"),
                dp_opcode("0111"),
                dp_opcode("1010"),
            ],
            forbidden_opcodes: vec!["sub", "rsb", "sbc", "rsc", "cmp"],
            expected_shape: "mvn tmp, r1; add r0, r2, tmp; add r0, r0, #1",
            size: 3,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "03_cmp_without_cmp",
            input: "cmp r1, r2",
            live_out: "z",
            denies: vec![dp_opcode("1010")],
            forbidden_opcodes: vec!["cmp"],
            expected_shape: "subs tmp, r1, r2",
            size: 1,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "04_cmn_without_cmn",
            input: "cmn r1, r2",
            live_out: "z",
            denies: vec![dp_opcode("1011")],
            forbidden_opcodes: vec!["cmn"],
            expected_shape: "adds tmp, r1, r2",
            size: 1,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "05_tst_without_tst",
            input: "tst r1, r2",
            live_out: "z",
            denies: vec![dp_opcode("1000")],
            forbidden_opcodes: vec!["tst"],
            expected_shape: "ands tmp, r1, r2",
            size: 1,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "06_teq_without_teq",
            input: "teq r1, r2",
            live_out: "z",
            denies: vec![dp_opcode("1001")],
            forbidden_opcodes: vec!["teq"],
            expected_shape: "eors tmp, r1, r2",
            size: 1,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "07_mov_register_without_mov_register",
            input: "mov r0, r1",
            live_out: "0",
            denies: vec![dp_register_opcode("1101")],
            forbidden_opcodes: vec!["mov"],
            expected_shape: "orr r0, r1, r1 or add r0, r1, #0",
            size: 2,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "08_mvn_without_mvn",
            input: "mvn r0, r1",
            live_out: "0",
            denies: vec![dp_opcode("1111")],
            forbidden_opcodes: vec!["mvn"],
            expected_shape: "eor r0, r1, #-1 or equivalent",
            size: 2,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "09_orr_without_orr",
            input: "orr r0, r1, r2",
            live_out: "0",
            denies: vec![dp_opcode("1100")],
            forbidden_opcodes: vec!["orr"],
            expected_shape: "De Morgan sequence using mvn and bic",
            size: 3,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "10_bic_without_bic",
            input: "bic r0, r1, r2",
            live_out: "0",
            denies: vec![dp_opcode("1110")],
            forbidden_opcodes: vec!["bic"],
            expected_shape: "mvn tmp, r2; and r0, r1, tmp",
            size: 2,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "11_add_imm4_without_exact_imm4",
            input: "add r0, r1, #4",
            live_out: "0",
            denies: vec![dp_immediate_opcode_imm12("0100", "000000000100")],
            forbidden_opcodes: vec![],
            expected_shape: "split immediate sequence such as #1 plus #3",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "12_mov_imm255_without_exact_imm255",
            input: "mov r0, #255",
            live_out: "0",
            denies: vec![mov_immediate_imm12("000011111111")],
            forbidden_opcodes: vec![],
            expected_shape: "nearby constant construction such as #256 minus #1",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "13_lsl1_without_mov_shift",
            input: "lsl r0, r1, #1",
            live_out: "0",
            denies: vec![mov_lsl_immediate("00001")],
            forbidden_opcodes: vec!["lsl"],
            expected_shape: "add r0, r1, r1",
            size: 1,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "14_lsl2_without_mov_shift",
            input: "lsl r0, r1, #2",
            live_out: "0",
            denies: vec![mov_lsl_immediate("00010")],
            forbidden_opcodes: vec!["lsl"],
            expected_shape: "add tmp, r1, r1; add r0, tmp, tmp",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "15_add_with_lsl2_operand2_field",
            input: "add r0, r1, r2, lsl #2",
            live_out: "0",
            denies: vec![dp_register_unshifted_operand2()],
            forbidden_opcodes: vec![],
            expected_shape: "same immediate-shifted operand2 form or equivalent",
            size: 2,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "16_add_with_lsr_register_shift",
            input: "add r0, r1, r2, lsr r3",
            live_out: "0",
            denies: vec![dp_register_immediate_shift_operand2()],
            forbidden_opcodes: vec![],
            expected_shape: "register-shifted-register operand2 form or shifted temporary",
            size: 2,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "17_addeq_without_al_condition",
            input: "addeq r0, r1, r2",
            live_out: "0",
            denies: vec![condition("1110")],
            forbidden_opcodes: branch_forbidden.to_vec(),
            expected_shape: "addeq r0, r1, r2 or predicated equivalent",
            size: 2,
            timeout: 60,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "18_subpl_without_subtract_family",
            input: "subpl r0, r1, r2",
            live_out: "0",
            denies: vec![
                dp_opcode("0010"),
                dp_opcode("0011"),
                dp_opcode("0110"),
                dp_opcode("0111"),
                dp_opcode("1010"),
            ],
            forbidden_opcodes: vec!["sub", "rsb", "sbc", "rsc", "cmp"],
            expected_shape: "mvnpl tmp, r2; addpl r0, r1, tmp; addpl r0, r0, #1",
            size: 3,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "19_ldr_imm_without_imm_offset",
            input: "ldr r0, [r1, #4]",
            live_out: "0",
            denies: vec![word_transfer_immediate(false, true)],
            forbidden_opcodes: vec![],
            expected_shape: "mov tmp, #4; ldr r0, [r1, tmp]",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "20_str_imm_without_imm_offset",
            input: "str r0, [r1, #4]",
            live_out: "",
            denies: vec![word_transfer_immediate(false, false)],
            forbidden_opcodes: vec![],
            expected_shape: "mov tmp, #4; str r0, [r1, tmp]",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "21_ldrh_imm_without_imm_offset",
            input: "ldrh r0, [r1, #2]",
            live_out: "0",
            denies: vec![halfword_transfer_immediate(true)],
            forbidden_opcodes: vec![],
            expected_shape: "mov tmp, #2; ldrh r0, [r1, tmp]",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "22_strh_imm_without_imm_offset",
            input: "strh r0, [r1, #2]",
            live_out: "",
            denies: vec![halfword_transfer_immediate(false)],
            forbidden_opcodes: vec![],
            expected_shape: "mov tmp, #2; strh r0, [r1, tmp]",
            size: 2,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "23_word_load_from_bytes",
            input: "ldr r0, [r1, #0]",
            live_out: "0",
            denies: vec![direct_word_transfer(true)],
            forbidden_opcodes: vec!["ldr"],
            expected_shape: "four ldrb operations plus shifts and orr to rebuild r0",
            size: 8,
            timeout: 300,
            hard: true,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "24_word_store_from_bytes",
            input: "str r0, [r1, #0]",
            live_out: "",
            denies: vec![direct_word_transfer(false)],
            forbidden_opcodes: vec!["str"],
            expected_shape: "four strb operations with shifts to write each byte",
            size: 8,
            timeout: 300,
            hard: true,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "25_swp_without_swap",
            input: "swp r0, r2, [r1]",
            live_out: "0",
            denies: vec![swap()],
            forbidden_opcodes: vec!["swp", "swpb"],
            expected_shape: "ldr tmp, [r1]; str r2, [r1]; mov r0, tmp",
            size: 3,
            timeout: 120,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "26_swpb_without_swap",
            input: "swpb r0, r2, [r1]",
            live_out: "0",
            denies: vec![swap()],
            forbidden_opcodes: vec!["swp", "swpb"],
            expected_shape: "ldrb tmp, [r1]; strb r2, [r1]; mov r0, tmp",
            size: 3,
            timeout: 120,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "27_stm_without_block_transfer",
            input: "stm r1, #5",
            live_out: "",
            denies: vec![block_transfer()],
            forbidden_opcodes: vec!["stm", "ldm"],
            expected_shape: "str r0, [r1,#0]; str r2, [r1,#4]",
            size: 2,
            timeout: 180,
            hard: true,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "28_ldm_without_block_transfer",
            input: "ldm r1, #5",
            live_out: "0,2",
            denies: vec![block_transfer()],
            forbidden_opcodes: vec!["stm", "ldm"],
            expected_shape: "ldr r0, [r1,#0]; ldr r2, [r1,#4]",
            size: 2,
            timeout: 180,
            hard: true,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "29_stack_scratch_store",
            input: "str r0, [r12, #-4]",
            live_out: "",
            denies: vec![],
            forbidden_opcodes: branch_forbidden.to_vec(),
            expected_shape: "original store, with any extra memory writes confined to r12 downward scratch",
            size: 3,
            timeout: 90,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: Some(StackScratch {
                register: 12,
                size: 32,
                direction: "downwards",
            }),
        },
        Case {
            name: "30_add_without_plain_register_operand2",
            input: "add r0, r1, r2",
            live_out: "0",
            denies: vec![dp_register_unshifted_operand2()],
            forbidden_opcodes: vec![],
            expected_shape: "shifted-register or materialized-register workaround if one exists",
            size: 3,
            timeout: 180,
            hard: true,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "31_pc_read_middle_of_independent_sequence",
            input: "add r1, r1, r0
eor r4, r4, r5
add r2, r2, r15
add r3, r3, r0
eor r6, r6, r7",
            live_out: "2",
            denies: vec![],
            forbidden_opcodes: vec![],
            expected_shape: "two-instruction replacement must preserve the original index-2 PC read, e.g. by compensating if the PC read moves",
            size: 2,
            timeout: 180,
            hard: false,
            require_discovered: false,
            mode: "syn",
            stack_scratch: None,
        },
        Case {
            name: "32_pop_pc_without_pop",
            input: "pop {r0, r1, r2, pc}",
            live_out: "0,1,2",
            denies: vec![block_load_transfer()],
            forbidden_opcodes: vec!["pop", "ldm"],
            expected_shape: "ldr r0, [sp], #4; ldr r1, [sp], #4; ldr r2, [sp], #4",
            size: 4,
            timeout: 180,
            hard: true,
            require_discovered: true,
            mode: "syn",
            stack_scratch: None,
        },
    ]
}

fn dp_opcode(bits: &'static str) -> &'static str {
    Box::leak(format!("xxxx00x{bits}xxxxxxxxxxxxxxxxxxxxx").into_boxed_str())
}

fn dp_register_opcode(bits: &'static str) -> &'static str {
    Box::leak(format!("xxxx000{bits}xxxxxxxxxxxxxxxxxxxxx").into_boxed_str())
}

fn dp_immediate_opcode_imm12(opcode: &'static str, imm12: &'static str) -> &'static str {
    Box::leak(format!("xxxx001{opcode}xxxxxxxxx{imm12}").into_boxed_str())
}

fn mov_immediate_imm12(imm12: &'static str) -> &'static str {
    Box::leak(format!("xxxx0011101x0000xxxx{imm12}").into_boxed_str())
}

fn mov_lsl_immediate(imm5: &'static str) -> &'static str {
    Box::leak(format!("xxxx0001101x0000xxxx{imm5}000xxxx").into_boxed_str())
}

fn dp_register_unshifted_operand2() -> &'static str {
    "xxxx000xxxxxxxxxxxxx00000000xxxx"
}

fn dp_register_immediate_shift_operand2() -> &'static str {
    "xxxx000xxxxxxxxxxxxxxxxxxxx0xxxx"
}

fn condition(bits: &'static str) -> &'static str {
    Box::leak(format!("{bits}xxxxxxxxxxxxxxxxxxxxxxxxxxxx").into_boxed_str())
}

fn word_transfer_immediate(byte: bool, load: bool) -> &'static str {
    Box::leak(format!("xxxx010xx{}x{}{}", bit(byte), bit(load), "x".repeat(20)).into_boxed_str())
}

fn direct_word_transfer(load: bool) -> &'static str {
    Box::leak(format!("xxxx01xxx0x{}{}", bit(load), "x".repeat(20)).into_boxed_str())
}

fn halfword_transfer_immediate(load: bool) -> &'static str {
    Box::leak(format!("xxxx000xx1x{}xxxxxxxxxxxx1xx1xxxx", bit(load)).into_boxed_str())
}

fn swap() -> &'static str {
    "xxxx00010x00xxxxxxxx00001001xxxx"
}

fn block_transfer() -> &'static str {
    "xxxx100xxxxxxxxxxxxxxxxxxxxxxxxx"
}

fn block_load_transfer() -> &'static str {
    "xxxx100xxxx1xxxxxxxxxxxxxxxxxxxx"
}

fn bit(value: bool) -> char {
    if value { '1' } else { '0' }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn generated_patterns_are_valid_arm_words() {
        let mut patterns = HashSet::new();
        for case in cases() {
            for pattern in case.denies {
                assert_eq!(pattern.len(), 32, "{}: {}", case.name, pattern);
                assert!(
                    pattern.chars().all(|ch| matches!(ch, '0' | '1' | 'x')),
                    "{}: {}",
                    case.name,
                    pattern
                );
                patterns.insert(pattern);
            }
        }
        assert!(patterns.len() >= 10);
    }
}
