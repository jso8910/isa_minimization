#[allow(dead_code)]
#[path = "../examples/arm32/isa.rs"]
mod arm32;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    env, fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    thread,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use isa_minimization::{
    bit::{Bit, BitPattern},
    isa_specification::{
        DecodedField, DecodedInstruction, FieldUses, ISA, Instruction, InstructionField,
        InstructionForm, MergeMode, StackDirection, StackPointer,
    },
};
use rand::{RngExt, SeedableRng, rngs::StdRng};

const DEFAULT_RANDOM_PER_FORM: usize = 256;
const DEFAULT_SEED: u64 = 0;
const MAX_EXAMPLES_PER_GROUP: usize = 5;

#[derive(Clone, Debug)]
struct CorpusCase {
    word: u32,
    instruction: String,
    form: String,
}

#[derive(Clone, Debug)]
struct GtInst {
    op: String,
    cond: String,
    shf: String,
    args: Vec<String>,
}

#[derive(Clone, Debug)]
struct FailureExample {
    word: u32,
    instruction: String,
    form: String,
    asm: String,
    detail: String,
}

#[derive(Default)]
struct FailureReport {
    total_words: usize,
    form_counts: BTreeMap<String, usize>,
    unsupported_input: BTreeMap<String, Vec<FailureExample>>,
    parse_mismatch: BTreeMap<String, Vec<FailureExample>>,
    printer_asm_failure: BTreeMap<String, Vec<FailureExample>>,
    printer_mismatch: BTreeMap<String, Vec<FailureExample>>,
    generation_failures: Vec<String>,
    skipped_printer: BTreeMap<String, usize>,
}

impl FailureReport {
    fn is_empty(&self) -> bool {
        self.unsupported_input.is_empty()
            && self.parse_mismatch.is_empty()
            && self.printer_asm_failure.is_empty()
            && self.printer_mismatch.is_empty()
            && self.generation_failures.is_empty()
    }

    fn push(
        bucket: &mut BTreeMap<String, Vec<FailureExample>>,
        case: &CorpusCase,
        asm: impl Into<String>,
        reason: impl Into<String>,
    ) {
        let key = format!("{}::{}", case.instruction, case.form);
        bucket.entry(key).or_default().push(FailureExample {
            word: case.word,
            instruction: case.instruction.clone(),
            form: case.form.clone(),
            asm: asm.into(),
            detail: reason.into(),
        });
    }

    fn render(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "GreenThumb ARM32 assembly surface report\n  total words tested: {}\n  forms covered: {}\n",
            self.total_words,
            self.form_counts.len()
        ));

        if !self.generation_failures.is_empty() {
            out.push_str("\nGeneration failures:\n");
            for failure in &self.generation_failures {
                out.push_str(&format!("  - {failure}\n"));
            }
        }

        if !self.skipped_printer.is_empty() {
            out.push_str("\nPrinter cases skipped because no GreenThumb mapping exists:\n");
            for (key, count) in &self.skipped_printer {
                out.push_str(&format!("  - {key}: {count}\n"));
            }
        }

        Self::render_bucket(
            &mut out,
            "Unsupported GreenThumb input syntax",
            &self.unsupported_input,
        );
        Self::render_bucket(
            &mut out,
            "GreenThumb parse mismatches",
            &self.parse_mismatch,
        );
        Self::render_bucket(
            &mut out,
            "Printer assembly failures",
            &self.printer_asm_failure,
        );
        Self::render_bucket(
            &mut out,
            "Printer re-encoding mismatches",
            &self.printer_mismatch,
        );
        out
    }

    fn render_bucket(
        out: &mut String,
        title: &str,
        bucket: &BTreeMap<String, Vec<FailureExample>>,
    ) {
        if bucket.is_empty() {
            return;
        }
        let total: usize = bucket.values().map(Vec::len).sum();
        out.push_str(&format!(
            "\n{title}: {total} failures in {} groups\n",
            bucket.len()
        ));
        for (key, examples) in bucket {
            out.push_str(&format!("  - {key}: {}\n", examples.len()));
            for example in examples.iter().take(MAX_EXAMPLES_PER_GROUP) {
                out.push_str(&format!(
                    "      {:#010x} {}::{} asm=`{}` detail=`{}`\n",
                    example.word, example.instruction, example.form, example.asm, example.detail
                ));
            }
        }
    }
}

#[test]
fn greenthumb_arm32_assembly_surface_matches_rust_encodings() {
    let trace_timing = env_flag("GT_ARM32_ASM_TRACE_TIMING");
    let test_start = Instant::now();
    let random_per_form = env_usize("GT_ARM32_ASM_RANDOM_PER_FORM", DEFAULT_RANDOM_PER_FORM);
    let seed = env_u64("GT_ARM32_ASM_SEED", DEFAULT_SEED);
    let max_cases = env::var("GT_ARM32_ASM_MAX_CASES")
        .ok()
        .and_then(|value| value.parse::<usize>().ok());
    let tools = ArmTools::discover();
    let isa = arm32_isa();
    let mut rng = StdRng::seed_from_u64(seed);

    let mut report = FailureReport::default();
    let generation_start = Instant::now();
    let corpus = generate_corpus(&isa, random_per_form, max_cases, &mut rng, &mut report);
    trace_phase(
        trace_timing,
        "generate_corpus",
        generation_start,
        format!("{} cases", corpus.len()),
    );
    report.total_words = corpus.len();
    for case in &corpus {
        *report
            .form_counts
            .entry(format!("{}::{}", case.instruction, case.form))
            .or_insert(0) += 1;
    }

    let disassemble_start = Instant::now();
    let disassembled = tools.disassemble_words(corpus.iter().map(|case| case.word));
    trace_phase(trace_timing, "disassemble_words", disassemble_start, "");
    let mut asm_by_case = Vec::with_capacity(corpus.len());
    for (case, result) in corpus.iter().zip(disassembled) {
        match result {
            Ok(asm) => {
                let decoded = decode_case(&isa, case);
                asm_by_case.push(Some(exact_parse_asm(&decoded).unwrap_or(asm)));
            }
            Err(err) => {
                FailureReport::push(
                    &mut report.unsupported_input,
                    case,
                    "<disassemble failed>",
                    err,
                );
                asm_by_case.push(None);
            }
        }
    }

    let mut parse_input = String::new();
    let mut parse_case_indices = Vec::new();
    let mut print_input = String::new();
    let mut print_case_indices = Vec::new();
    let request_build_start = Instant::now();
    for (index, asm) in asm_by_case.iter().enumerate() {
        let Some(asm) = asm else {
            continue;
        };
        if matches!(
            corpus[index].instruction.as_str(),
            "branch_ops_b" | "branch_ops_bx"
        ) {
            continue;
        }
        parse_input.push_str(asm);
        parse_input.push('\n');
        parse_case_indices.push(index);
    }

    for (index, case) in corpus.iter().enumerate() {
        if case.instruction.starts_with("branch_ops_") {
            *report
                .skipped_printer
                .entry(format!("{}::{}", case.instruction, case.form))
                .or_insert(0) += 1;
            continue;
        }
        let Some(gt_inst) = gt_inst_from_decoded(&decode_case(&isa, case)) else {
            *report
                .skipped_printer
                .entry(format!("{}::{}", case.instruction, case.form))
                .or_insert(0) += 1;
            continue;
        };
        print_input.push_str(&gt_inst.batch_line());
        print_input.push('\n');
        print_case_indices.push(index);
    }
    trace_phase(
        trace_timing,
        "build_surface_requests",
        request_build_start,
        format!(
            "{} parse requests, {} print requests",
            parse_case_indices.len(),
            print_case_indices.len()
        ),
    );

    let parse_start = Instant::now();
    let parse_output = if parse_input.is_empty() {
        Ok(String::new())
    } else {
        run_green_thumb_stdin(&["parse-asm-batch"], &parse_input)
    };
    trace_phase(trace_timing, "greenthumb_parse_batch", parse_start, "");
    match &parse_output {
        Ok(output) => {
            for (case_index, line) in parse_case_indices.iter().zip(output.lines()) {
                let case = &corpus[*case_index];
                let asm = asm_by_case[*case_index]
                    .as_deref()
                    .unwrap_or("<disassemble failed>");
                match parse_gt_parse_output(line) {
                    Ok(parsed_word) if parsed_word == case.word => {}
                    Ok(parsed_word) => FailureReport::push(
                        &mut report.parse_mismatch,
                        case,
                        asm,
                        format!("GreenThumb encoded {parsed_word:#010x}"),
                    ),
                    Err(err) => {
                        FailureReport::push(&mut report.unsupported_input, case, asm, err);
                    }
                }
            }
            if output.lines().count() < parse_case_indices.len() {
                for case_index in &parse_case_indices[output.lines().count()..] {
                    let case = &corpus[*case_index];
                    FailureReport::push(
                        &mut report.unsupported_input,
                        case,
                        asm_by_case[*case_index]
                            .as_deref()
                            .unwrap_or("<disassemble failed>"),
                        "GreenThumb batch output ended early",
                    );
                }
            }
        }
        Err(err) => {
            for case_index in &parse_case_indices {
                let case = &corpus[*case_index];
                let asm = asm_by_case[*case_index]
                    .as_deref()
                    .unwrap_or("<disassemble failed>");
                FailureReport::push(&mut report.unsupported_input, case, asm, err.clone());
            }
        }
    }

    let print_start = Instant::now();
    let print_output = if print_input.is_empty() {
        Ok(String::new())
    } else {
        run_green_thumb_stdin(&["print-encoded-batch"], &print_input)
    };
    trace_phase(trace_timing, "greenthumb_print_batch", print_start, "");

    let mut printed_for_assembler = Vec::new();
    match &print_output {
        Ok(output) => {
            for (case_index, line) in print_case_indices.iter().zip(output.lines()) {
                let case = &corpus[*case_index];
                let asm = asm_by_case[*case_index]
                    .as_deref()
                    .unwrap_or("<disassemble failed>");
                let Some(printed) = line.trim().strip_prefix("ok ") else {
                    FailureReport::push(
                        &mut report.printer_asm_failure,
                        case,
                        asm,
                        format!("GreenThumb print failed: {line}"),
                    );
                    continue;
                };
                printed_for_assembler.push((*case_index, printed.to_string()));
            }
            if output.lines().count() < print_case_indices.len() {
                for case_index in &print_case_indices[output.lines().count()..] {
                    let case = &corpus[*case_index];
                    FailureReport::push(
                        &mut report.printer_asm_failure,
                        case,
                        asm_by_case[*case_index]
                            .as_deref()
                            .unwrap_or("<disassemble failed>"),
                        "GreenThumb print batch output ended early",
                    );
                }
            }
        }
        Err(err) => {
            for case_index in &print_case_indices {
                let case = &corpus[*case_index];
                FailureReport::push(
                    &mut report.printer_asm_failure,
                    case,
                    asm_by_case[*case_index]
                        .as_deref()
                        .unwrap_or("<disassemble failed>"),
                    err.clone(),
                );
            }
        }
    }

    let printed_lines = printed_for_assembler
        .iter()
        .map(|(_, printed)| printed.as_str())
        .collect::<Vec<_>>();
    let assembler_start = Instant::now();
    for ((case_index, printed), assembled) in printed_for_assembler
        .iter()
        .zip(tools.assemble_lines(&printed_lines))
    {
        let case = &corpus[*case_index];
        match assembled {
            Ok(assembled_word) if assembled_word == case.word => {}
            Ok(assembled_word) => FailureReport::push(
                &mut report.printer_mismatch,
                case,
                printed,
                format!(
                    "assembler encoded {assembled_word:#010x}, expected {:#010x}",
                    case.word
                ),
            ),
            Err(err) => FailureReport::push(&mut report.printer_asm_failure, case, printed, err),
        }
    }
    trace_phase(
        trace_timing,
        "assemble_printed_lines",
        assembler_start,
        format!("{} lines", printed_lines.len()),
    );
    trace_phase(trace_timing, "total", test_start, "");

    if !report.is_empty() {
        panic!("{}", report.render());
    }
}

#[test]
#[ignore = "optimizer smoke syntax check invokes stochastic GreenThumb search"]
fn greenthumb_arm32_optimizer_output_assembles_smoke() {
    let tools = ArmTools::discover();
    let dir = temp_dir("gt-arm32-optimizer-smoke");
    let program = dir.join("input.s");
    let info = dir.join("input.s.info");
    fs::write(&program, "add r0, r1, #1\n").expect("write smoke program");
    fs::write(&info, "0\n").expect("write smoke live-out");

    let output_dir = dir.join("out");
    let command = format!(
        "source greenthumb/source.sh && racket greenthumb/arm/optimize.rkt --stoch -s -c 1 -t 5 -d {} {}",
        shell_quote(output_dir.to_str().expect("output dir should be utf8")),
        shell_quote(program.to_str().expect("program path should be utf8"))
    );
    let output = Command::new("zsh")
        .arg("-lc")
        .arg(command)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("failed to run GreenThumb optimizer smoke");

    assert!(
        output.status.success(),
        "optimizer smoke failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let best = fs::read_to_string(output_dir.join("best.s")).expect("read best.s");
    for line in best.lines().map(str::trim).filter(|line| !line.is_empty()) {
        tools.assemble_line(line).unwrap_or_else(|err| {
            panic!("optimizer emitted assembler-invalid line `{line}`: {err}")
        });
    }
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

fn generate_corpus(
    isa: &ISA,
    random_per_form: usize,
    max_cases: Option<usize>,
    rng: &mut StdRng,
    report: &mut FailureReport,
) -> Vec<CorpusCase> {
    let mut seen = HashSet::new();
    let mut corpus = Vec::new();

    for instruction in &isa.instructions {
        for form in &instruction.forms {
            let mut accepted = 0usize;
            let mut target = random_per_form.max(1);
            if let Some(max_unique) = max_unique_samples_for_form(instruction, form) {
                target = target.min(max_unique);
            }
            let constrained_patterns = constrained_form_patterns(form);

            for bits in constructive_form_bits(form, &constrained_patterns) {
                if accepted >= target {
                    break;
                }
                if let Some(case) = accepted_case(instruction, form, bits) {
                    if seen.insert((case.word, case.instruction.clone(), case.form.clone())) {
                        accepted += 1;
                        corpus.push(case);
                        if max_cases.is_some_and(|max_cases| corpus.len() >= max_cases) {
                            return corpus;
                        }
                    }
                }
            }

            if accepted < target {
                let attempts = ((target - accepted) * 512).max(4096);
                for _ in 0..attempts {
                    if accepted >= target || constrained_patterns.is_empty() {
                        break;
                    }
                    let pattern =
                        &constrained_patterns[rng.random_range(0..constrained_patterns.len())];
                    let bits = concretize_pattern_randomly(pattern, rng);
                    if let Some(case) = accepted_case(instruction, form, bits) {
                        if seen.insert((case.word, case.instruction.clone(), case.form.clone())) {
                            accepted += 1;
                            corpus.push(case);
                            if max_cases.is_some_and(|max_cases| corpus.len() >= max_cases) {
                                return corpus;
                            }
                        }
                    }
                }
            }

            if accepted < target {
                report.generation_failures.push(format!(
                    "{}::{} produced {accepted}/{target} unique accepted samples",
                    instruction.name, form.name
                ));
            }
        }
    }

    corpus
}

fn max_unique_samples_for_form(instruction: &Instruction, form: &InstructionForm) -> Option<usize> {
    match (instruction.name.as_str(), form.name.as_str()) {
        ("branch_ops_bx", "base") => Some(15 * 16),
        _ => None,
    }
}

fn accepted_case(
    instruction: &Instruction,
    form: &InstructionForm,
    bits: Vec<Bit>,
) -> Option<CorpusCase> {
    let decoded = instruction.find_match(&bits)?;
    if decoded.form.name == form.name {
        if !assembler_surface_representable(&decoded) {
            return None;
        }
        Some(CorpusCase {
            word: bits_to_word(&bits),
            instruction: instruction.name.clone(),
            form: decoded.form.name,
        })
    } else {
        None
    }
}

fn assembler_surface_representable(decoded: &DecodedInstruction) -> bool {
    match decoded.name.as_str() {
        "multiply_ops_mul" => {
            let Some(rd) = field(decoded, "rd_addr") else {
                return false;
            };
            let Some(rn) = field(decoded, "rn_addr") else {
                return false;
            };
            let Some(rs) = field(decoded, "rs_addr") else {
                return false;
            };
            let Some(rm) = field(decoded, "rm_addr") else {
                return false;
            };
            if [rd, rn, rs, rm].contains(&15) {
                return false;
            }
            field(decoded, "do_mul_accum") != Some(0) || rn == 0
        }
        "multiply_ops_mull" => {
            let Some(rdhi) = field(decoded, "rdhi_addr") else {
                return false;
            };
            let Some(rdlo) = field(decoded, "rdlo_addr") else {
                return false;
            };
            let Some(rn) = field(decoded, "rn_addr") else {
                return false;
            };
            let Some(rm) = field(decoded, "rm_addr") else {
                return false;
            };
            ![rdhi, rdlo, rn, rm].contains(&15) && rdhi != rdlo
        }
        _ => true,
    }
}

fn constructive_form_bits(
    form: &InstructionForm,
    constrained_patterns: &[BitPattern],
) -> Vec<Vec<Bit>> {
    let mut out = Vec::new();

    for pattern in constrained_patterns {
        out.push(concretize_pattern_with_counter(pattern, 0));
        out.push(concretize_pattern_with_counter(pattern, u128::MAX));
        out.push(concretize_pattern_with_counter(
            pattern,
            0xaaaa_aaaa_aaaa_aaaa,
        ));
        out.push(concretize_pattern_with_counter(
            pattern,
            0x5555_5555_5555_5555,
        ));
    }

    for values in targeted_form_values(form) {
        out.push(form_bits_with_values(form, &values));
    }

    for field in &form.fields {
        let Some(name) = &field.name else {
            continue;
        };
        let width = field.pattern.len();
        for value in edge_values(name, width) {
            let mut values = BTreeMap::new();
            values.insert(name.clone(), value);
            out.push(form_bits_with_values(form, &values));
        }
    }

    out
}

fn targeted_form_values(form: &InstructionForm) -> Vec<BTreeMap<String, u128>> {
    let mut out = Vec::new();
    if let Some(opcode) = dproc_opcode_for_form(&form.name) {
        let mut values = BTreeMap::new();
        values.insert("cond".to_string(), 14);
        values.insert("data_proc_opcode".to_string(), opcode);
        values.insert("rd_addr".to_string(), 15);
        values.insert("rn_addr".to_string(), 0);
        values.insert(
            "set_flags".to_string(),
            if form.name.split('_').next().unwrap_or("").ends_with('s') {
                1
            } else {
                0
            },
        );
        values.insert("rm_addr".to_string(), 0);
        values.insert("rs_addr".to_string(), 0);
        values.insert("op2_imm_shift_amt".to_string(), 0);
        values.insert("op2_shift_type".to_string(), 0);
        values.insert("imm_ror_amt".to_string(), 0);
        values.insert("imm8".to_string(), 0);
        out.push(values);
    }
    out
}

fn dproc_opcode_for_form(form_name: &str) -> Option<u128> {
    let mnemonic = form_name.split('_').next()?.trim_end_matches('s');
    Some(match mnemonic {
        "and" => 0,
        "eor" => 1,
        "sub" => 2,
        "rsb" => 3,
        "add" => 4,
        "adc" => 5,
        "sbc" => 6,
        "rsc" => 7,
        "orr" => 12,
        "mov" => 13,
        "bic" => 14,
        "mvn" => 15,
        _ => return None,
    })
}

fn constrained_form_patterns(form: &InstructionForm) -> Vec<BitPattern> {
    constrained_form_patterns_with_values(form, &BTreeMap::new())
}

fn constrained_form_patterns_with_values(
    form: &InstructionForm,
    values: &BTreeMap<String, u128>,
) -> Vec<BitPattern> {
    let mut field_values = HashMap::new();
    for field in &form.fields {
        let Some(name) = &field.name else {
            continue;
        };
        let pattern = field_pattern_with_value(field, values.get(name).copied());
        let field_use = match field.merge_mode {
            MergeMode::VariableBits => FieldUses::VariableBits {
                name: name.clone(),
                pattern: Some(pattern),
                len: field.pattern.len(),
            },
            MergeMode::Uses => FieldUses::Uses {
                name: name.clone(),
                patterns: HashSet::from([pattern]),
                len: field.pattern.len(),
            },
        };
        field_values.insert(name.clone(), field_use);
    }
    form.fields_to_encodings(&field_values)
}

fn form_bits_with_values(form: &InstructionForm, values: &BTreeMap<String, u128>) -> Vec<Bit> {
    let mut bits = Vec::new();
    for field in &form.fields {
        let width = field.pattern.len();
        let value = field
            .name
            .as_ref()
            .and_then(|name| values.get(name))
            .copied()
            .unwrap_or_else(|| default_value_for_field(field.name.as_deref(), width));
        bits.extend(field_pattern_with_value(field, Some(value)).bits);
    }
    bits
}

fn default_value_for_field(name: Option<&str>, width: usize) -> u128 {
    edge_values(name.unwrap_or(""), width)
        .into_iter()
        .next()
        .unwrap_or(0)
}

fn field_pattern_with_value(field: &InstructionField, value: Option<u128>) -> BitPattern {
    let Some(value) = value else {
        return field.pattern.clone();
    };
    let mut bits = Vec::new();
    let width = field.pattern.len();
    for (index, pattern_bit) in field.pattern.bits.iter().enumerate() {
        match pattern_bit {
            Bit::Low | Bit::High => bits.push(*pattern_bit),
            Bit::Var | Bit::Test => {
                let shift = width - index - 1;
                bits.push(if ((value >> shift) & 1) == 1 {
                    Bit::High
                } else {
                    Bit::Low
                });
            }
        }
    }
    BitPattern::new(bits)
}

fn concretize_pattern_with_counter(pattern: &BitPattern, mut counter: u128) -> Vec<Bit> {
    pattern
        .bits
        .iter()
        .map(|bit| match bit {
            Bit::Low | Bit::High => *bit,
            Bit::Var | Bit::Test => {
                let out = if (counter & 1) == 1 {
                    Bit::High
                } else {
                    Bit::Low
                };
                counter = counter.rotate_right(1);
                out
            }
        })
        .collect()
}

fn concretize_pattern_randomly(pattern: &BitPattern, rng: &mut StdRng) -> Vec<Bit> {
    pattern
        .bits
        .iter()
        .map(|bit| match bit {
            Bit::Low | Bit::High => *bit,
            Bit::Var | Bit::Test => {
                if rng.random() {
                    Bit::High
                } else {
                    Bit::Low
                }
            }
        })
        .collect()
}

fn edge_values(name: &str, width: usize) -> Vec<u128> {
    let max = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let mut values = BTreeSet::from([0, 1.min(max), max]);
    if max >= 2 {
        values.insert(2);
    }
    if max >= 3 {
        values.insert(3);
    }
    if max >= 7 {
        values.insert(7);
    }
    if max >= 8 {
        values.insert(8);
    }
    if max >= 15 {
        values.insert(15);
    }
    if max >= 31 {
        values.insert(31);
    }
    if max >= 255 {
        values.insert(255);
    }
    if max >= 4095 {
        values.insert(4095);
    }

    match name {
        "cond" => values.extend(0..=14),
        "rn_addr" | "rd_addr" | "rm_addr" | "rs_addr" | "rdhi_addr" | "rdlo_addr" => {
            values.extend([0, 1, 2, 3, 12, 13, 14, 15]);
        }
        "op2_shift_type" | "sh_bits" => values.extend(0..=3),
        "op2_imm_shift_amt" => values.extend([0, 1, 2, 3, 8, 16, 31]),
        "block_reglist" => values.extend([1, 2, 3, 5, 0x80, 0x100, 0x4000, 0x8000, 0xffff]),
        _ => {}
    }

    values.into_iter().filter(|value| *value <= max).collect()
}

fn decode_case(isa: &ISA, case: &CorpusCase) -> DecodedInstruction {
    let bits = (0..32)
        .rev()
        .map(|shift| {
            if ((case.word >> shift) & 1) == 1 {
                Bit::High
            } else {
                Bit::Low
            }
        })
        .collect::<Vec<_>>();
    isa.instructions
        .iter()
        .find(|instruction| instruction.name == case.instruction)
        .and_then(|instruction| {
            instruction
                .find_match(&bits)
                .filter(|decoded| decoded.form.name == case.form)
        })
        .expect("generated case should decode through intended Rust form")
}

fn bits_to_word(bits: &[Bit]) -> u32 {
    bits.iter().fold(0u32, |acc, bit| {
        (acc << 1)
            | match bit {
                Bit::High => 1,
                Bit::Low => 0,
                Bit::Var | Bit::Test => panic!("generated bits must be concrete"),
            }
    })
}

fn gt_inst_from_decoded(decoded: &DecodedInstruction) -> Option<GtInst> {
    let cond = cond_arg(field(decoded, "cond")?);
    match decoded.name.as_str() {
        "arithmetic_s0_reg_op2"
        | "logical_s0_reg_op2"
        | "move_s0_reg_op2"
        | "dproc_s1_reg_op2"
        | "branch_ops_dproc" => gt_dproc_reg(decoded, cond),
        "arithmetic_s0_imm_op2" | "logical_s0_imm_op2" | "move_s0_imm_op2" | "dproc_s1_imm_op2" => {
            gt_dproc_imm(decoded, cond)
        }
        "multiply_ops_mul" => gt_mul(decoded, cond),
        "multiply_ops_mull" => gt_mull(decoded, cond),
        "swap_ops" => {
            let rd = field(decoded, "rd_addr")?;
            let rm = field(decoded, "rm_addr")?;
            let rn = field(decoded, "rn_addr")?;
            if rn == rd || rn == rm {
                None
            } else {
                Some(GtInst {
                    op: if field(decoded, "is_byte_tfr")? == 1 {
                        "swpb".to_string()
                    } else {
                        "swp".to_string()
                    },
                    cond,
                    shf: "||".to_string(),
                    args: vec![rd.to_string(), rm.to_string(), rn.to_string()],
                })
            }
        }
        "load_ops" | "store_ops" | "branch_ops_data_tfr" => {
            if decoded.name == "store_ops" && field(decoded, "rd_addr")? == 15 {
                None
            } else {
                gt_data_tfr(decoded, cond)
            }
        }
        "hwtfr_load_ops" | "hwtfr_store_ops" | "branch_ops_hwtfr" => {
            if decoded.name == "hwtfr_store_ops" && field(decoded, "rd_addr")? == 15 {
                None
            } else {
                gt_hwtfr(decoded, cond)
            }
        }
        "block_load_ops" | "block_store_ops" | "branch_ops_block_tfr" => {
            gt_block_tfr(decoded, cond)
        }
        _ => None,
    }
}

fn gt_dproc_reg(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    let mut base_op = dproc_mnemonic(decoded)?;
    if dproc_sets_flags(decoded)
        && !base_op.ends_with('s')
        && !matches!(base_op.as_str(), "tst" | "teq" | "cmp" | "cmn")
    {
        base_op.push('s');
    }
    let op = base_op.clone();
    let rd = field(decoded, "rd_addr")?;
    let rn = field(decoded, "rn_addr")?;
    let rm = field(decoded, "rm_addr")?;
    let mut args = dproc_base_args(&op, rd, rn, rm);
    let (shf, shift_arg) = shift_arg(decoded)?;
    if let Some(shift_arg) = shift_arg {
        args.push(shift_arg);
    }
    Some(GtInst {
        op,
        cond,
        shf,
        args,
    })
}

fn gt_dproc_imm(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    let mut base_op = dproc_mnemonic(decoded)?;
    if dproc_sets_flags(decoded)
        && !base_op.ends_with('s')
        && !matches!(base_op.as_str(), "tst" | "teq" | "cmp" | "cmn")
    {
        base_op.push('s');
    }
    let mut op = base_op.clone();
    op.push('#');
    let rd = field(decoded, "rd_addr")?;
    let rn = field(decoded, "rn_addr")?;
    let imm8 = field(decoded, "imm8")?;
    let imm_ror = field(decoded, "imm_ror_amt")?;
    let imm = raw_modified_immediate_operand(imm8, imm_ror);
    let args = if matches!(op.as_str(), "mov#" | "mvn#" | "movs#" | "mvns#") {
        vec![rd.to_string(), imm]
    } else if matches!(op.as_str(), "tst#" | "teq#" | "cmp#" | "cmn#") {
        vec![rn.to_string(), imm]
    } else {
        vec![rd.to_string(), rn.to_string(), imm]
    };
    Some(GtInst {
        op,
        cond,
        shf: "||".to_string(),
        args,
    })
}

fn exact_parse_asm(decoded: &DecodedInstruction) -> Option<String> {
    if !matches!(
        decoded.name.as_str(),
        "arithmetic_s0_reg_op2"
            | "arithmetic_s0_imm_op2"
            | "logical_s0_reg_op2"
            | "logical_s0_imm_op2"
            | "move_s0_reg_op2"
            | "move_s0_imm_op2"
            | "branch_ops_dproc"
            | "dproc_s1_reg_op2"
            | "dproc_s1_imm_op2"
    ) {
        return None;
    }

    let mut base_op = dproc_mnemonic(decoded)?;
    if dproc_sets_flags(decoded)
        && !base_op.ends_with('s')
        && !matches!(base_op.as_str(), "tst" | "teq" | "cmp" | "cmn")
    {
        base_op.push('s');
    }
    let mut op = base_op.clone();
    let cond = cond_arg(field(decoded, "cond")?);
    if cond != "||" {
        op.push_str(&cond);
    }

    let rd = field(decoded, "rd_addr")?;
    let rn = field(decoded, "rn_addr")?;
    let args = if decoded.form.name.ends_with("_immediate") {
        let imm = format!(
            "#{}",
            raw_modified_immediate_operand(field(decoded, "imm8")?, field(decoded, "imm_ror_amt")?)
        );
        if matches!(base_op.as_str(), "mov" | "mvn" | "movs" | "mvns") {
            vec![reg(rd), imm]
        } else if matches!(base_op.as_str(), "tst" | "teq" | "cmp" | "cmn") {
            vec![reg(rn), imm]
        } else {
            vec![reg(rd), reg(rn), imm]
        }
    } else {
        let rm = field(decoded, "rm_addr")?;
        let mut args = if matches!(base_op.as_str(), "mov" | "mvn" | "movs" | "mvns") {
            vec![reg(rd), reg(rm)]
        } else if matches!(base_op.as_str(), "tst" | "teq" | "cmp" | "cmn") {
            vec![reg(rn), reg(rm)]
        } else {
            vec![reg(rd), reg(rn), reg(rm)]
        };
        if decoded.form.name.ends_with("register_shifted_register") {
            let shift_type = field(decoded, "op2_shift_type")?;
            args.push(format!(
                "{} {}",
                shift_name(shift_type)?,
                reg(field(decoded, "rs_addr")?)
            ));
        } else {
            let shift_type = field(decoded, "op2_shift_type")?;
            let shift = assembler_shift_amount(shift_type, field(decoded, "op2_imm_shift_amt")?);
            if shift_type == 3 && shift == 0 {
                args.push("rrx".to_string());
            } else if !(shift_type == 0 && shift == 0) {
                args.push(format!("{} #{shift}", shift_name(shift_type)?));
            }
        }
        args
    };
    Some(format!("{op}\t{}", args.join(", ")))
}

fn shift_name(shift_type: u128) -> Option<&'static str> {
    match shift_type {
        0 => Some("lsl"),
        1 => Some("lsr"),
        2 => Some("asr"),
        3 => Some("ror"),
        _ => None,
    }
}

fn raw_modified_immediate_operand(imm8: u128, imm_ror: u128) -> String {
    if imm_ror == 0 {
        imm8.to_string()
    } else {
        format!("{imm8}, {}", imm_ror * 2)
    }
}

fn reg(id: u128) -> String {
    format!("r{id}")
}

fn dproc_base_args(op: &str, rd: u128, rn: u128, rm: u128) -> Vec<String> {
    if matches!(op, "mov" | "mvn" | "movs" | "mvns") {
        vec![rd.to_string(), rm.to_string()]
    } else if matches!(op, "tst" | "teq" | "cmp" | "cmn") {
        vec![rn.to_string(), rm.to_string()]
    } else {
        vec![rd.to_string(), rn.to_string(), rm.to_string()]
    }
}

fn dproc_mnemonic(decoded: &DecodedInstruction) -> Option<String> {
    decoded.form.name.split('_').next().map(ToOwned::to_owned)
}

fn dproc_sets_flags(decoded: &DecodedInstruction) -> bool {
    decoded.name == "dproc_s1_reg_op2"
        || decoded.name == "dproc_s1_imm_op2"
        || decoded.form.name.starts_with("adds_")
        || decoded.form.name.starts_with("adcs_")
        || decoded.form.name.starts_with("subs_")
        || decoded.form.name.starts_with("rsbs_")
        || decoded.form.name.starts_with("sbcs_")
        || decoded.form.name.starts_with("rscs_")
        || decoded.form.name.starts_with("ands_")
        || decoded.form.name.starts_with("orrs_")
        || decoded.form.name.starts_with("eors_")
        || decoded.form.name.starts_with("bics_")
        || decoded.form.name.starts_with("movs_")
        || decoded.form.name.starts_with("mvns_")
}

fn shift_arg(decoded: &DecodedInstruction) -> Option<(String, Option<String>)> {
    let shift_type = field(decoded, "op2_shift_type")?;
    let shift_name = match shift_type {
        0 => "lsl",
        1 => "lsr",
        2 => "asr",
        3 => "ror",
        _ => return None,
    };
    if decoded.form.name.ends_with("register_shifted_register") {
        Some((
            shift_name.to_string(),
            Some(field(decoded, "rs_addr")?.to_string()),
        ))
    } else {
        let shift = assembler_shift_amount(shift_type, field(decoded, "op2_imm_shift_amt")?);
        if shift == 0 && shift_type == 0 {
            Some(("||".to_string(), None))
        } else {
            Some((format!("{shift_name}#"), Some(shift.to_string())))
        }
    }
}

fn gt_mul(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    let accumulate = field(decoded, "do_mul_accum")? == 1;
    let set_flags = field(decoded, "set_flags")? == 1;
    let op = match (accumulate, set_flags) {
        (false, false) => "mul",
        (false, true) => "muls",
        (true, false) => "mla",
        (true, true) => "mlas",
    };
    let mut args = vec![
        field(decoded, "rd_addr")?.to_string(),
        field(decoded, "rm_addr")?.to_string(),
        field(decoded, "rs_addr")?.to_string(),
    ];
    if accumulate {
        args.push(field(decoded, "rn_addr")?.to_string());
    }
    Some(GtInst {
        op: op.to_string(),
        cond,
        shf: "||".to_string(),
        args,
    })
}

fn gt_mull(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    let unsigned = field(decoded, "is_unsigned_mul")? == 1;
    let accumulate = field(decoded, "do_mul_accum")? == 1;
    let set_flags = field(decoded, "set_flags")? == 1;
    let op = match (unsigned, accumulate, set_flags) {
        (false, false, false) => "umull",
        (true, false, false) => "smull",
        (false, false, true) => "umulls",
        (true, false, true) => "smulls",
        (false, true, false) => "umlal",
        (true, true, false) => "smlal",
        (false, true, true) => "umlals",
        (true, true, true) => "smlals",
    };
    Some(GtInst {
        op: op.to_string(),
        cond,
        shf: "||".to_string(),
        args: vec![
            field(decoded, "rdlo_addr")?.to_string(),
            field(decoded, "rdhi_addr")?.to_string(),
            field(decoded, "rm_addr")?.to_string(),
            field(decoded, "rn_addr")?.to_string(),
        ],
    })
}

fn gt_data_tfr(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    let load = decoded.name != "store_ops";
    let byte = field(decoded, "is_byte_tfr")? == 1;
    let base = match (load, byte) {
        (true, false) => "ldr-full",
        (true, true) => "ldrb-full",
        (false, false) => "str-full",
        (false, true) => "strb-full",
    };
    let rd = field(decoded, "rd_addr")?;
    let rn = field(decoded, "rn_addr")?;
    let p = field(decoded, "is_pre_idx")?;
    let u = field(decoded, "is_up_offset")?;
    let w = field(decoded, "do_writeback")?;
    if decoded.form.name.starts_with("immediate_offset") {
        Some(GtInst {
            op: format!("{base}#"),
            cond,
            shf: "||".to_string(),
            args: vec![
                rd.to_string(),
                rn.to_string(),
                field(decoded, "imm12")?.to_string(),
                p.to_string(),
                u.to_string(),
                w.to_string(),
            ],
        })
    } else {
        let shift_type = field(decoded, "op2_shift_type")?;
        let shift = assembler_shift_amount(shift_type, field(decoded, "op2_imm_shift_amt")?);
        let shift_name = match shift_type {
            0 => "lsl#",
            1 => "lsr#",
            2 => "asr#",
            3 => "ror#",
            _ => return None,
        };
        Some(GtInst {
            op: base.to_string(),
            cond,
            shf: shift_name.to_string(),
            args: vec![
                rd.to_string(),
                rn.to_string(),
                field(decoded, "rm_addr")?.to_string(),
                p.to_string(),
                u.to_string(),
                w.to_string(),
                shift.to_string(),
            ],
        })
    }
}

fn assembler_shift_amount(shift_type: u128, encoded_amount: u128) -> u128 {
    if encoded_amount == 0 && matches!(shift_type, 1 | 2) {
        32
    } else {
        encoded_amount
    }
}

fn gt_hwtfr(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    let load = decoded.name != "hwtfr_store_ops";
    let sh_bits = field(decoded, "sh_bits")?;
    let base = match (load, sh_bits) {
        (true, 1) => "ldrh-full",
        (true, 2) => "ldrsb-full",
        (true, 3) => "ldrsh-full",
        (false, 1) => "strh-full",
        _ => return None,
    };
    let rd = field(decoded, "rd_addr")?;
    let rn = field(decoded, "rn_addr")?;
    let p = field(decoded, "is_pre_idx")?;
    let u = field(decoded, "is_up_offset")?;
    let w = field(decoded, "do_writeback")?;
    if decoded.form.name.starts_with("immediate_offset") {
        let imm = (field(decoded, "imm8_high")? << 4) | field(decoded, "imm8_low")?;
        Some(GtInst {
            op: format!("{base}#"),
            cond,
            shf: "||".to_string(),
            args: vec![
                rd.to_string(),
                rn.to_string(),
                imm.to_string(),
                p.to_string(),
                u.to_string(),
                w.to_string(),
            ],
        })
    } else {
        Some(GtInst {
            op: base.to_string(),
            cond,
            shf: "||".to_string(),
            args: vec![
                rd.to_string(),
                rn.to_string(),
                field(decoded, "rm_addr")?.to_string(),
                p.to_string(),
                u.to_string(),
                w.to_string(),
            ],
        })
    }
}

fn gt_block_tfr(decoded: &DecodedInstruction, cond: String) -> Option<GtInst> {
    Some(GtInst {
        op: if decoded.name == "block_store_ops" {
            "stm-full#".to_string()
        } else {
            "ldm-full#".to_string()
        },
        cond,
        shf: "||".to_string(),
        args: vec![
            field(decoded, "rn_addr")?.to_string(),
            field(decoded, "block_reglist")?.to_string(),
            field(decoded, "is_pre_idx_block")?.to_string(),
            field(decoded, "is_up_offset_block")?.to_string(),
            field(decoded, "do_writeback_block")?.to_string(),
        ],
    })
}

impl GtInst {
    fn batch_line(&self) -> String {
        let mut parts = vec![self.op.clone(), self.cond.clone(), self.shf.clone()];
        parts.extend(self.args.clone());
        parts.join("\t")
    }
}

fn field(decoded: &DecodedInstruction, name: &str) -> Option<u128> {
    decoded
        .fields
        .iter()
        .find(|field| field.name.as_deref() == Some(name))
        .map(field_to_u128)
}

fn field_to_u128(field: &DecodedField) -> u128 {
    field.value.bits.iter().fold(0, |acc, bit| {
        (acc << 1)
            | match bit {
                Bit::High => 1,
                Bit::Low => 0,
                Bit::Var | Bit::Test => panic!("decoded field should be concrete"),
            }
    })
}

fn cond_arg(value: u128) -> String {
    match value {
        0 => "eq",
        1 => "ne",
        2 => "cs",
        3 => "cc",
        4 => "mi",
        5 => "pl",
        6 => "vs",
        7 => "vc",
        8 => "hi",
        9 => "ls",
        10 => "ge",
        11 => "lt",
        12 => "gt",
        13 => "le",
        14 => "||",
        _ => "al",
    }
    .to_string()
}

struct ArmTools {
    assembler: PathBuf,
    objcopy: PathBuf,
    objdump: PathBuf,
    arch: String,
}

impl ArmTools {
    fn discover() -> Self {
        Self {
            assembler: env_path("GT_ARM32_AS")
                .or_else(|| {
                    find_tool(&[
                        "arm-none-eabi-as",
                        "arm-linux-gnueabi-as",
                        "arm-linux-gnueabihf-as",
                    ])
                })
                .expect("could not find ARM assembler; set GT_ARM32_AS"),
            objcopy: env_path("GT_ARM32_OBJCOPY")
                .or_else(|| {
                    find_tool(&[
                        "arm-none-eabi-objcopy",
                        "arm-linux-gnueabi-objcopy",
                        "arm-linux-gnueabihf-objcopy",
                        "llvm-objcopy",
                        "objcopy",
                    ])
                })
                .expect("could not find objcopy; set GT_ARM32_OBJCOPY"),
            objdump: env_path("GT_ARM32_OBJDUMP")
                .or_else(|| {
                    find_tool(&[
                        "arm-none-eabi-objdump",
                        "arm-linux-gnueabi-objdump",
                        "arm-linux-gnueabihf-objdump",
                        "llvm-objdump",
                        "objdump",
                    ])
                })
                .expect("could not find ARM objdump; set GT_ARM32_OBJDUMP"),
            arch: env::var("GT_ARM32_ARCH").unwrap_or_else(|_| "armv7ve".to_string()),
        }
    }

    fn assemble_line(&self, asm: &str) -> Result<u32, String> {
        let dir = temp_dir("gt-arm32-asm");
        let asm_file = dir.join("one.s");
        let obj_file = dir.join("one.o");
        let bin_file = dir.join("one.bin");
        let source = format!(
            ".syntax unified\n.arm\n.arch {}\n.text\n.global _start\n_start:\n{}\n",
            self.arch, asm
        );
        fs::write(&asm_file, source).map_err(|err| err.to_string())?;

        let output = Command::new(&self.assembler)
            .arg(format!("-march={}", self.arch))
            .arg("-o")
            .arg(&obj_file)
            .arg(&asm_file)
            .output()
            .map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "assembler failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }

        let output = Command::new(&self.objcopy)
            .arg("-O")
            .arg("binary")
            .arg("-j")
            .arg(".text")
            .arg(&obj_file)
            .arg(&bin_file)
            .output()
            .map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "objcopy failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }

        let bytes = fs::read(&bin_file).map_err(|err| err.to_string())?;
        if bytes.len() != 4 {
            return Err(format!("expected 4 output bytes, got {}", bytes.len()));
        }
        Ok(u32::from_le_bytes(
            bytes.try_into().expect("length checked above"),
        ))
    }

    fn assemble_lines(&self, lines: &[&str]) -> Vec<Result<u32, String>> {
        if lines.is_empty() {
            return Vec::new();
        }

        match self.try_assemble_lines_batch(lines) {
            Ok(words) => words.into_iter().map(Ok).collect(),
            Err(_) if lines.len() <= 1 => {
                lines.iter().map(|line| self.assemble_line(line)).collect()
            }
            Err(_) => {
                let mid = lines.len() / 2;
                let mut out = self.assemble_lines(&lines[..mid]);
                out.extend(self.assemble_lines(&lines[mid..]));
                out
            }
        }
    }

    fn try_assemble_lines_batch(&self, lines: &[&str]) -> Result<Vec<u32>, String> {
        let dir = temp_dir("gt-arm32-asm-batch");
        let asm_file = dir.join("batch.s");
        let obj_file = dir.join("batch.o");
        let bin_file = dir.join("batch.bin");
        let mut source = format!(
            ".syntax unified\n.arm\n.arch {}\n.text\n.global _start\n_start:\n",
            self.arch
        );
        for line in lines {
            source.push_str(line);
            source.push('\n');
        }
        fs::write(&asm_file, source).map_err(|err| err.to_string())?;

        let output = Command::new(&self.assembler)
            .arg(format!("-march={}", self.arch))
            .arg("-o")
            .arg(&obj_file)
            .arg(&asm_file)
            .output()
            .map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "assembler failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }

        let output = Command::new(&self.objcopy)
            .arg("-O")
            .arg("binary")
            .arg("-j")
            .arg(".text")
            .arg(&obj_file)
            .arg(&bin_file)
            .output()
            .map_err(|err| err.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "objcopy failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }

        let bytes = fs::read(&bin_file).map_err(|err| err.to_string())?;
        if bytes.len() != lines.len() * 4 {
            return Err(format!(
                "expected {} output bytes, got {}",
                lines.len() * 4,
                bytes.len()
            ));
        }

        Ok(bytes
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes(chunk.try_into().expect("chunk size checked above")))
            .collect())
    }

    fn disassemble_words(
        &self,
        words: impl IntoIterator<Item = u32>,
    ) -> Vec<Result<String, String>> {
        let words = words.into_iter().collect::<Vec<_>>();
        if words.is_empty() {
            return Vec::new();
        }
        let dir = temp_dir("gt-arm32-disasm");
        let bin_file = dir.join("one.bin");
        let bytes = words
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect::<Vec<_>>();
        if let Err(err) = fs::write(&bin_file, bytes) {
            return vec![Err(err.to_string()); words.len()];
        }
        let output = Command::new(&self.objdump)
            .arg("-D")
            .arg("-b")
            .arg("binary")
            .arg("-m")
            .arg("arm")
            .arg("-M")
            .arg("reg-names-raw")
            .arg(&bin_file)
            .output();
        let output = match output {
            Ok(output) => output,
            Err(err) => return vec![Err(err.to_string()); words.len()],
        };
        if !output.status.success() {
            return vec![
                Err(format!(
                    "objdump failed: {}",
                    String::from_utf8_lossy(&output.stderr).trim()
                ));
                words.len()
            ];
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let mut out = vec![Err("could not parse objdump output".to_string()); words.len()];
        for line in stdout.lines() {
            let columns = line.split('\t').collect::<Vec<_>>();
            if columns.len() < 3 || !columns[0].contains(':') {
                continue;
            }
            let Some(offset_text) = columns[0].split(':').next() else {
                continue;
            };
            let Ok(offset) = usize::from_str_radix(offset_text.trim(), 16) else {
                continue;
            };
            if offset % 4 != 0 {
                continue;
            }
            let index = offset / 4;
            if index >= out.len() {
                continue;
            }
            let asm = columns[2..].join("\t");
            let asm = asm
                .split(" ;")
                .next()
                .unwrap_or(&asm)
                .split('@')
                .next()
                .unwrap_or(&asm)
                .trim();
            if !asm.is_empty() {
                out[index] = Ok(asm.to_string());
            }
        }
        out
    }
}

fn parse_gt_parse_output(output: &str) -> Result<u32, String> {
    let trimmed = output.trim();
    if let Some(rest) = trimmed.strip_prefix("ok ") {
        return parse_hex(rest).map_err(|err| format!("bad ok word `{rest}`: {err}"));
    }
    if let Some(rest) = trimmed.strip_prefix("err ") {
        return Err(rest.to_string());
    }
    Err(format!("unexpected GreenThumb output `{trimmed}`"))
}

fn parse_hex(value: &str) -> Result<u32, std::num::ParseIntError> {
    u32::from_str_radix(value.trim().trim_start_matches("0x"), 16)
}

fn run_green_thumb_stdin(args: &[&str], stdin: &str) -> Result<String, String> {
    match run_green_thumb_stdin_with_compiled_mode(args, stdin, true) {
        Ok(output) => Ok(output),
        Err(err) if err.contains("wrong version for compiled code") => {
            run_green_thumb_stdin_with_compiled_mode(args, stdin, false)
        }
        Err(err) => Err(err),
    }
}

fn run_green_thumb_stdin_with_compiled_mode(
    args: &[&str],
    stdin: &str,
    use_compiled: bool,
) -> Result<String, String> {
    let quoted_args = args
        .iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ");
    let racket = if use_compiled { "racket" } else { "racket -c" };
    let command = format!(
        "source greenthumb/source.sh && {racket} greenthumb/arm/tests/arm32-parity-cli.rkt {quoted_args}"
    );
    let mut child = Command::new("zsh")
        .arg("-lc")
        .arg(command)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|err| err.to_string())?;

    let stdin_bytes = stdin.as_bytes().to_vec();
    let mut child_stdin = child.stdin.take().expect("stdin should be piped");
    let stdin_writer = thread::spawn(move || {
        child_stdin
            .write_all(&stdin_bytes)
            .map_err(|err| err.to_string())
    });

    let output = child.wait_with_output().map_err(|err| err.to_string())?;
    let stdin_result = stdin_writer
        .join()
        .map_err(|_| "GreenThumb CLI stdin writer panicked".to_string())?;
    if !output.status.success() {
        return Err(format!(
            "GreenThumb CLI failed: stdout=`{}` stderr=`{}`",
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    stdin_result?;
    String::from_utf8(output.stdout).map_err(|err| err.to_string())
}

fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

fn find_tool(names: &[&str]) -> Option<PathBuf> {
    let path = env::var_os("PATH")?;
    for dir in env::split_paths(&path) {
        for name in names {
            let candidate = dir.join(name);
            if is_executable(&candidate) {
                return Some(candidate);
            }
        }
    }
    None
}

fn env_path(name: &str) -> Option<PathBuf> {
    env::var_os(name).map(PathBuf::from)
}

fn is_executable(path: &Path) -> bool {
    path.is_file()
}

fn env_usize(name: &str, default: usize) -> usize {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn env_u64(name: &str, default: u64) -> u64 {
    env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

fn env_flag(name: &str) -> bool {
    env::var(name).is_ok_and(|value| !matches!(value.as_str(), "" | "0" | "false" | "False"))
}

fn trace_phase(trace: bool, name: &str, start: Instant, detail: impl AsRef<str>) {
    if trace {
        let detail = detail.as_ref();
        if detail.is_empty() {
            eprintln!("GT_ARM32_ASM_TRACE {name}: {:.3?}", start.elapsed());
        } else {
            eprintln!(
                "GT_ARM32_ASM_TRACE {name}: {:.3?} ({detail})",
                start.elapsed()
            );
        }
    }
}

fn temp_dir(prefix: &str) -> PathBuf {
    let mut path = env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    path.push(format!("{prefix}-{}-{nanos}", std::process::id()));
    fs::create_dir_all(&path).expect("create temp dir");
    path
}
