// Contains arm32 specification
// Simply an example of what you can do with isa_specification

use std::collections::HashMap;
use std::time::Instant;

use isa_minimization::stdcell_library::StandardCellLibrary;
use isa_minimization::isa_specification::{DecodedField, DecodedInstruction, FieldUses, Instruction, InstructionField, InstructionForm, MergeMode, and, bit_eq, c, field_eq, field_in, not, or};
use isa_minimization::bit::{Bit, BitPattern};

// Instruction field definitions

pub fn cond() -> InstructionField {
    InstructionField::variable("cond", 4)
        .merge_mode_uses()
}

pub fn set_flags() -> InstructionField {
    InstructionField::variable("set_flags", 1)
}

pub fn rn_addr() -> InstructionField {
    InstructionField::variable("rn_addr", 4)
            .merge_mode_uses()
}

pub fn rd_addr() -> InstructionField {
    InstructionField::variable("rd_addr", 4)
            .merge_mode_uses()
}

pub fn rm_addr() -> InstructionField {
    InstructionField::variable("rm_addr", 4)
            .merge_mode_uses()
}

pub fn rs_addr() -> InstructionField {
    InstructionField::variable("rs_addr", 4)
            .merge_mode_uses()
}

pub fn data_proc_opcode() -> InstructionField {
    InstructionField::variable("data_proc_opcode", 4)
            .merge_mode_uses()
}

pub fn has_imm() -> InstructionField {
    InstructionField::variable("has_imm", 1)
}

pub fn op2_imm_shift_amt() -> InstructionField {
    InstructionField::variable("op2_imm_shift_amt", 5)
}

pub fn op2_shift_type() -> InstructionField {
    InstructionField::variable("op2_shift_type", 2)
            .merge_mode_uses()
}

pub fn imm_ror_amt() -> InstructionField {
    InstructionField::variable("imm_ror_amt", 4)
}

pub fn imm8() -> InstructionField {
    InstructionField::variable("imm8", 8)
}

pub fn do_mul_accum() -> InstructionField {
    InstructionField::variable("do_mul_accum", 1)
}

pub fn is_unsigned_mul() -> InstructionField {
    InstructionField::variable("is_unsigned_mul", 1)
}

pub fn rdhi_addr() -> InstructionField {
    InstructionField::variable("rdhi_addr", 4)
            .merge_mode_uses()
}

pub fn rdlo_addr() -> InstructionField {
    InstructionField::variable("rdlo_addr", 4)
            .merge_mode_uses()
}

pub fn is_pre_idx() -> InstructionField {
    InstructionField::variable("is_pre_idx", 1)
}

pub fn is_up_offset() -> InstructionField {
    InstructionField::variable("is_up_offset", 1)
}

pub fn do_writeback() -> InstructionField {
    InstructionField::variable("do_writeback", 1)
}

pub fn is_load() -> InstructionField {
    InstructionField::variable("is_load", 1)
}

pub fn has_imm_offset() -> InstructionField {
    InstructionField::variable("has_imm_offset", 1)
}

pub fn sh_bits() -> InstructionField {
    // Cannot have value 00
    InstructionField::variable("sh_bits", 2)
            .merge_mode_uses()
}

pub fn imm8_high() -> InstructionField {
    InstructionField::variable("imm8_high", 4)
}

pub fn imm8_low() -> InstructionField {
    InstructionField::variable("imm8_low", 4)
}

pub fn is_byte_tfr() -> InstructionField {
    InstructionField::variable("is_byte_tfr", 1)
}

pub fn imm12() -> InstructionField {
    InstructionField::variable("imm12", 12)
}

pub fn is_pre_idx_block() -> InstructionField {
    InstructionField::variable("is_pre_idx_block", 1)
}

pub fn is_up_offset_block() -> InstructionField {
    InstructionField::variable("is_up_offset_block", 1)
}

pub fn do_load_psr() -> InstructionField {
    InstructionField::variable("do_load_psr", 1)
}

pub fn do_writeback_block() -> InstructionField {
    InstructionField::variable("do_writeback_block", 1)
}

pub fn is_load_block() -> InstructionField {
    InstructionField::variable("is_load_block", 1)
}

pub fn block_reglist() -> InstructionField {
    InstructionField::variable("block_reglist", 16)
}

pub fn do_link() -> InstructionField {
    InstructionField::variable("do_link", 1)
}

pub fn branch_offset() -> InstructionField {
    InstructionField::variable("branch_offset", 24)
}


// Instruction definitions
pub fn dproc_prefix() -> Vec<InstructionField> {
    vec![
        cond(),
        c("00"),
        has_imm(),
        data_proc_opcode(),
        set_flags(),
        rn_addr(),
        rd_addr(),
    ]
}

pub fn data_tfr_prefix() -> Vec<InstructionField> {
    vec![
        cond(),
        c("01"),
        has_imm_offset(),
        is_pre_idx(),
        is_up_offset(),
        is_byte_tfr(),
        do_writeback(),
        is_load(),
        rn_addr(),
        rd_addr(),
    ]
}

pub fn dproc() -> Instruction {
    Instruction::new("dproc", 32)
        .form(
            InstructionForm::new("register_shifted_register")
                .fields(dproc_prefix())
                .fields([
                    rs_addr(),
                    c("0"),
                    op2_shift_type(),
                    c("1"),
                    rm_addr(),
                ])
                .when(bit_eq(6, Bit::Low)),
        )
        .form(
            InstructionForm::new("register_immediate_shift")
                .fields(dproc_prefix())
                .fields([
                    op2_imm_shift_amt(),
                    op2_shift_type(),
                    c("0"),
                    rm_addr(),
                ])
                .when(bit_eq(6, Bit::Low)),
        )
        .form(
            InstructionForm::new("immediate")
                .fields(dproc_prefix())
                .fields([
                    imm_ror_amt(),
                    imm8(),
                ])
                .when(bit_eq(6, Bit::High)),
        )
        // TST, TEQ, CMP, CMN must set flags.
        //
        // Invalid:
        // data_proc_opcode in {1000, 1001, 1010, 1011}
        // AND set_flags == 0
        .constraint(not(and([
            field_in(
                "data_proc_opcode",
                [
                    "1000", // TST
                    "1001", // TEQ
                    "1010", // CMP
                    "1011", // CMN
                ],
            ),
            field_eq("set_flags", "0"),
        ])))
}

pub fn mul() -> Instruction {
    Instruction::new("mul", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("000000"),
                    do_mul_accum(),
                    set_flags(),
                    rd_addr(),
                    rn_addr(),
                    rs_addr(),
                    c("1001"),
                    rm_addr(),
                ]),
        )
}

pub fn mull() -> Instruction {
    Instruction::new("mull", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("00001"),
                    is_unsigned_mul(),
                    do_mul_accum(),
                    set_flags(),
                    rdhi_addr(),
                    rdlo_addr(),
                    rn_addr(),
                    c("1001"),
                    rm_addr(),
                ]),
        )
}

pub fn swp() -> Instruction {
    Instruction::new("swp", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("00010"),
                    is_byte_tfr(),
                    c("00"),
                    rn_addr(),
                    rd_addr(),
                    c("00001001"),
                    rm_addr(),
                ]),
        )
}

pub fn bx() -> Instruction {
    Instruction::new("bx", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("000100101111111111110001"),
                    rn_addr(),
                ]),
        )
}

pub fn hwtfr_reg_offset() -> Instruction {
    Instruction::new("hwtfr_reg_offset", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("000"),
                    is_pre_idx(),
                    is_up_offset(),
                    c("0"),
                    do_writeback(),
                    is_load(),
                    rn_addr(),
                    rd_addr(),
                    c("00001"),
                    sh_bits(),
                    c("1"),
                    rm_addr(),
                ]),
        )
        // sh_bits must not be 00.
        .constraint(not(field_eq("sh_bits", "00")))
}

pub fn hwtfr_imm_offset() -> Instruction {
    Instruction::new("hwtfr_imm_offset", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("000"),
                    is_pre_idx(),
                    is_up_offset(),
                    c("1"),
                    do_writeback(),
                    is_load(),
                    rn_addr(),
                    rd_addr(),
                    imm8_high(),
                    c("1"),
                    sh_bits(),
                    c("1"),
                    imm8_low(),
                ]),
        )
        // sh_bits must not be 00.
        .constraint(not(field_eq("sh_bits", "00")))
}

pub fn data_tfr() -> Instruction {
    Instruction::new("data_tfr", 32)
        .form(
            InstructionForm::new("register_offset")
                .fields(data_tfr_prefix())
                .fields([
                    op2_imm_shift_amt(),
                    op2_shift_type(),
                    c("0"),
                    rm_addr(),
                ])
                .when(bit_eq(6, Bit::High)),
        )
        .form(
            InstructionForm::new("immediate_offset")
                .fields(data_tfr_prefix())
                .fields([
                    imm12(),
                ])
                .when(bit_eq(6, Bit::Low)),
        )
}

pub fn block_tfr() -> Instruction {
    Instruction::new("block_tfr", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("100"),
                    is_pre_idx_block(),
                    is_up_offset_block(),
                    do_load_psr(),
                    do_writeback_block(),
                    is_load_block(),
                    rn_addr(),
                    block_reglist(),
                ]),
        )
}

pub fn b() -> Instruction {
    Instruction::new("b", 32)
        .form(
            InstructionForm::new("base")
                .fields([
                    cond(),
                    c("101"),
                    do_link(),
                    branch_offset(),
                ]),
        )
}

pub fn instructions() -> Vec<Instruction> {
    vec![
        dproc(),
        mul(),
        mull(),
        swp(),
        bx(),
        hwtfr_reg_offset(),
        hwtfr_imm_offset(),
        data_tfr(),
        block_tfr(),
        b(),
    ]
}

fn main() {
    let arm32 = instructions();

    // Get all the instructions from the binsearch.bin program
    let program_binary_path = "examples/binsearch.bin".to_string();
    let program_binary = std::fs::read_to_string(program_binary_path).expect("Failed to read program binary");

    let mut decoded_program: Vec<DecodedInstruction> = vec![];

    // Create hashmap of FieldUses
    let mut field_values: HashMap<String, FieldUses> = std::collections::HashMap::new();

    for (i, line) in program_binary.lines().enumerate() {
        let bits: Vec<Bit> = line.chars().map(|c| {
            match c {
                '0' => Bit::Low,
                '1' => Bit::High,
                _ => panic!("Invalid character in program binary: {}", c),
            }
        }).collect();

        // Try to decode the instruction
        let mut decoded = None;
        for instr in &arm32 {
            if let Some(decoded_instr) = instr.find_match(&bits) {
                decoded = Some(decoded_instr);
                break;
            }
        }

        if let Some(_) = &decoded {} else {
            panic!("Instruction {}: Failed to decode", i);
        }

        decoded_program.push(decoded.clone().unwrap());
        
        for DecodedField { name, value, merge_mode} in &decoded.unwrap().fields {
            let name = match name {
                Some(name) => name.clone(),
                None => {
                    // If there is no name, this is a constant field, so we can just ignore it
                    continue;
                }
            };
            let default_val = match merge_mode {
                MergeMode::Uses => FieldUses::Uses { name: name.clone(), patterns: [value.clone()].iter().cloned().collect() },
                MergeMode::VariableBits => FieldUses::VariableBits { name: name.clone(), pattern: value.clone() },
            };
            match field_values.entry(name.clone()).or_insert(default_val) {
                FieldUses::Uses { name: _, patterns } => {
                    let new_pattern = value.clone();
                    patterns.insert(new_pattern);

                }
                FieldUses::VariableBits { name: _, pattern } => {
                    // Any bits which are different between the existing pattern and the new pattern should become variable bits
                    let new_pattern = value.clone();
                    if pattern.len() != new_pattern.len() {
                        panic!("Pattern length mismatch for field '{}'", name);
                    }
                    let mut indices_to_update = Vec::new();
                    for (i, (old_bit, new_bit)) in pattern.bits.iter().zip(new_pattern.bits.iter()).enumerate() {
                        if old_bit != new_bit {
                            indices_to_update.push(i);
                        }
                    }
                    for i in indices_to_update {
                        pattern.bits[i] = Bit::Var;
                    }
                }
            }
        }
    }

    // Merge patterns for fields with merge_mode_uses, to reduce the number of encodings we need to generate
    for (_, field_uses) in field_values.iter_mut() {
        if let FieldUses::Uses { name: _, patterns } = field_uses {
            // Merge the patterns to reduce the number of encodings we need to generate
            let merged = FieldUses::Uses { name: "__".to_string(), patterns: patterns.clone() }.merge();
            *field_uses = merged;
        }
    }
    // for each instruction, print all valid encodings
    for instr in &arm32 {
        println!("Instruction: {}", instr.name);
        for form in &instr.forms {
            // We only want to get the encodings for the form if this form actually is used in the program
            if !decoded_program.iter().any(|decoded| decoded.form_name.as_ref().unwrap() == &form.name) {
                continue;
            }
            let encodings = form.fields_to_encodings(&field_values);
            println!("  Form: {}", form.name);
            for encoding in encodings {
                // print as string, 0s and 1s for High and Low, and Xs for Var
                let encoding_str: String = encoding.bits.iter().map(|b| {
                    match b {
                        Bit::Low => '0',
                        Bit::High => '1',
                        Bit::Var => 'x',
                        Bit::Test => panic!("Test bits should not be present in final encodings"),
                    }
                }).collect();
                println!("    Encoding: {}", encoding_str);
            }
        }
    }

    // Print each field and its possible values
    println!("Fields and their possible values:");
    for (field_name, field_uses) in &field_values {
        println!("  Field: {}", field_name);
        match field_uses {
            FieldUses::Uses { name: _, patterns } => {
                for pattern in patterns {
                    let pattern_str: String = pattern.bits.iter().map(|b| {
                        match b {
                            Bit::Low => '0',
                            Bit::High => '1',
                            Bit::Var => 'x',
                            Bit::Test => panic!("Test bits should not be present in final field patterns"),
                        }
                    }).collect();
                    println!("    Pattern: {}", pattern_str);
                }
            },
            FieldUses::VariableBits { name: _, pattern } => {
                let pattern_str: String = pattern.bits.iter().map(|b| {
                    match b {
                        Bit::Low => '0',
                        Bit::High => '1',
                        Bit::Var => 'x',
                        Bit::Test => panic!("Test bits should not be present in final field patterns"),
                    }
                }).collect();
                println!("    Pattern: {}", pattern_str);
            }
        }
    }

    StandardCellLibrary::new("examples/NangateOpenCellLibrary_typical.lib");
}