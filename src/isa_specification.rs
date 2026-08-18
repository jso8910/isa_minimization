use std::{
    collections::{HashMap, HashSet},
    io,
};

use crate::instruction_semantics::{Effect, Expr, FieldName, ValueName};

use super::bit::{Bit, BitPattern};

#[derive(Debug, Clone)]
pub struct ISA {
    pub registers: Vec<ArchitecturalRegister>,
    pub instructions: Vec<Instruction>,
    /// Register used as stack pointer
    pub sp: StackPointer,
    /// Register used as program counter (even if the ISA
    /// does not literally use a GPR as the PC, it should be
    /// defined as an ArchitecturalRegister)
    pub pc: ArchitecturalRegister,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StackPointer {
    /// Which register is used as the stack pointer
    /// This is assumed to point to the most recent item pushed to the stack
    /// Even if it points to the next item on the stack for some reason, this assumption does not
    /// lead to any errors but is merely slightly conservative.
    pub register: ArchitecturalRegister,
    /// How many bytes the symbolic solver can assume will be free above/below the current stack pointer
    /// Set to a conservative value to avoid accidental overwrites of real data.
    /// Either way, writing to the stack will be avoided, so it is unlikely a large value is needed.
    pub stack_size: u32,
    /// Direction the stack grows
    pub direction: StackDirection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackDirection {
    Upwards,
    Downwards,
}

/// Definition of a register in the architecture.
/// You can set the identifier, the identifier width,
/// and the width of the register.
/// Identifiers should never overlap regardless of width.
///
/// Thus, for some architectures (eg those with floating point registers)
/// you may need to have identifiers differ slightly (eg adding an extra bit to denote
/// the type of register).
///
/// Importantly, however, you need to make sure that if a certain `width` and
/// `identifier_width` does not have 2^identifier_width registers (ie the identifiers are sparse)
/// with that identifier width, it is not possible for any instruction to
/// ever request any register which is undefined using a given selector width.
///     Notice the nuance that the register `width` also matters.
///     If R0-R14 are all 32 bits but R15 is 16 bits, and you create something
///     which indexes from a field to get a 16 bit register, and that field takes any
///     value other than 15, there will be issues which will manifest
///     in the form of bugs, rather than the form of a program panic.
///
/// Eg if you define R18 as the only 5 bit identifier_width,
/// you should only select other registers (eg R0-R15) using
/// a 4 bit identifier_width.
///
/// As such, you likely shouldn't mess with identifier width and sparsely
/// defining register identifiers unless you're using fixed register identifiers.
/// Register identifiers should never be sparse at an accessible level from the ISA.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArchitecturalRegister {
    pub identifier: u8,
    pub identifier_width: u8,
    pub width: u8,
}

/// Enum which describes the two supported methods of PC modifications. If your program uses any
/// other methods, the superoptimization of the program won't work very well, as live-out registers
/// won't be properly identified.
/// Importantly, in the genetic algorithm, the instructions which support these must be unrestricted
/// - ie able to take any values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BranchOffset {
    /// Adds the value in the Expr to the decoded instruction's memory address (the add(mem_addr,
    /// ...) need not be included, it is implied). It is assumed that the address should be the same
    /// width as the Expr. As such, if there is a negative offset, Expr merely needs to be correctly
    /// sign extended.
    /// The Expr must evaluate to a Const when collapsed with a decoded instruction
    PCRelative(Expr),
    /// Indicates a register branch. It is assumed that all registers are live-out if there is a
    /// register branch. It is also assumed that a Register branch is to a location which is either
    /// itself immediately after a branch instruction and thus already inferred to be the start of a
    /// basic block (eg bx lr always branches to the instruction right after a `bl` instruction), or is
    /// branched to by some other piece of code. If this isn't the case, basic block analysis will not
    /// work properly, and there may be bugs in the final program.
    Register,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    pub name: String,
    pub width: usize,

    /// An instruction can have multiple forms (eg immediate-shifted-registers vs register-shifted-register)
    pub forms: Vec<InstructionForm>,

    /// Each instruction has a set of effects which occur. An instruction should never
    /// have two effects which could possibly write to the same location.
    pub effects: Vec<Effect>,

    /// Branch instruction. Some if this instruction modifies the PC
    /// Note that this means branch instructions and any PC-modifying instructions necessarily must
    /// be fully separate from other instructions.
    /// This is used for basic block analysis.
    pub branch_instruction: Option<BranchOffset>,
}

impl Instruction {
    pub fn new(name: impl Into<String>, width: usize) -> Self {
        Self {
            name: name.into(),
            width,
            forms: Vec::new(),
            effects: Vec::new(),
            branch_instruction: None,
        }
    }

    pub fn branch_instruction(mut self, branch_instruction: BranchOffset) -> Self {
        self.branch_instruction = Some(branch_instruction);
        self
    }

    pub fn form(mut self, form: InstructionForm) -> Self {
        if form.width() != self.width {
            panic!(
                "form '{}' has width {}, expected {}",
                form.name,
                form.width(),
                self.width,
            );
        }

        self.forms.push(form);
        self
    }

    pub fn effect(mut self, effect: Effect) -> Self {
        self.effects.push(effect);
        self
    }

    /// Attempt to match the given bits to this instruction, returning a DecodedInstruction if successful
    /// This works by checking that all static bits (non-variable) match, and then extracting the variable bits into fields
    /// If there are multiple forms that match, this will fail (return None) to avoid ambiguity.
    /// Each form must also match its when Predicate.
    /// As a result, if, for example, you have a field which must be equal to 0 for a form to be valid, if that field
    /// is left as variable, this function will fail to match that form.
    pub fn find_match(&self, bits: &[Bit]) -> Option<DecodedInstruction> {
        let mut matched_form = None;

        for form in &self.forms {
            if form.width() != bits.len() {
                continue; // Skip forms that don't match the width
            }

            let mut decoded_fields = DecodedInstruction {
                name: self.name.clone(),
                form: form.clone(),
                bits: bits.to_vec(),
                fields: Vec::new(),
                branch_instruction: self.branch_instruction.clone(),
                mem_addr: 0,
                static_instruction: self.branch_instruction.is_some(),
                assembly_line: 0,
            };
            let mut matches = true;

            let mut current_bit_index = 0;

            for field in form.fields.iter() {
                let pattern_matches = &field.pattern.matches_bits(
                    &bits[current_bit_index..current_bit_index + field.pattern.len()],
                );
                if !pattern_matches {
                    matches = false;
                    break;
                }

                decoded_fields.fields.push(DecodedField {
                    name: field.name.clone(),
                    value: BitPattern::new(
                        bits[current_bit_index..current_bit_index + field.pattern.len()].to_vec(),
                    ),
                    merge_mode: field.merge_mode,
                    is_immediate: field.is_immediate,
                    is_register_read: field.is_register_read,
                    is_register_write: field.is_register_write,
                });

                current_bit_index += field.pattern.len();
            }

            if matches && form.when.check(&decoded_fields) {
                if matched_form.is_some() {
                    // Multiple forms match, this is ambiguous
                    return None;
                }
                matched_form = Some(decoded_fields);
            }
        }
        matched_form
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInstruction {
    pub name: String,
    pub form: InstructionForm,
    pub bits: Vec<Bit>,
    pub fields: Vec<DecodedField>,
    pub branch_instruction: Option<BranchOffset>,
    pub mem_addr: usize,
    /// Instruction must not be included in any rewrites. Usually because it includes some symbolic
    /// element (eg b label, eg ldr r0, label). We also consider a basic block boundary to occur at
    /// these instructions.
    pub static_instruction: bool,
    /// The line number in the assembly file which corresponds with this instruction. If the
    /// instruction is not set as `static_instruction`, this should be a valid input to greenthumb
    /// (ie without references to labels, etc)
    pub assembly_line: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedField {
    pub name: Option<String>,
    pub value: BitPattern,
    pub merge_mode: MergeMode,
    pub is_immediate: bool,
    pub is_register_read: bool,
    pub is_register_write: bool,
}

/// Returns whether a decoded instruction is valid under the supplied field-use constraints.
pub fn instruction_valid_under_field_uses(
    instr: &DecodedInstruction,
    valid_field_uses: &HashMap<FieldName, FieldUses>,
) -> bool {
    if !instr.form.when.check(instr) {
        return false;
    }

    for field in &instr.fields {
        let Some(name) = &field.name else {
            continue;
        };
        let Some(valid_uses) = valid_field_uses.get(name) else {
            return false;
        };

        match valid_uses {
            FieldUses::Uses { patterns, .. } => {
                let matches = if field.value.bits.iter().any(|bit| *bit == Bit::Var) {
                    patterns
                        .iter()
                        .any(|pattern| field.value.matches_bits(&pattern.bits))
                } else {
                    patterns
                        .iter()
                        .any(|pattern| pattern.matches_bits(&field.value.bits))
                };
                if !matches {
                    return false;
                }
            }
            FieldUses::VariableBits { pattern, .. } => {
                let Some(pattern) = pattern else {
                    return false;
                };
                if !pattern.matches_bits(&field.value.bits) {
                    return false;
                }
            }
        }
    }

    true
}

impl DecodedInstruction {
    pub fn field_value(&self, name: &str) -> Option<&BitPattern> {
        self.fields
            .iter()
            .find(|field| field.name == Some(name.to_string()))
            .map(|field| &field.value)
    }

    pub fn decode_program(filename: &str, isa: &ISA) -> Result<Vec<Self>, io::Error> {
        let program_binary = std::fs::read_to_string(filename)?;

        DecodedInstruction::decode_program_str(&program_binary, isa)
    }

    pub fn decode_program_str(program: &str, isa: &ISA) -> Result<Vec<Self>, io::Error> {
        let mut decoded_program: Vec<DecodedInstruction> = vec![];

        for (i, line) in program.lines().enumerate() {
            let bits: Vec<Bit> = line
                .chars()
                .map(|c| match c {
                    '0' => Bit::Low,
                    '1' => Bit::High,
                    _ => panic!("Invalid character in program binary: {}", c),
                })
                .collect();

            // Try to decode the instruction
            let mut decoded = None;
            for instr in isa.instructions.iter() {
                if let Some(decoded_instr) = instr.find_match(&bits) {
                    decoded = Some(decoded_instr);
                    break;
                }
            }

            let Some(mut decoded) = decoded else {
                panic!("Instruction {}: Failed to decode", i);
            };

            decoded.mem_addr = decoded_program
                .last()
                .map(|prev| prev.mem_addr + instruction_addr_stride(prev.bits.len()))
                .unwrap_or(0);
            decoded.assembly_line = i;
            decoded_program.push(decoded);
        }
        Ok(decoded_program)
    }
}

fn instruction_addr_stride(bit_width: usize) -> usize {
    bit_width.div_ceil(8).max(1)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DerivedValue {
    pub name: ValueName,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionForm {
    pub name: String,
    pub fields: Vec<InstructionField>,

    /// Condition (on the instruction) for when the field is applicable (eg requiring a certain bit to be set to 1)
    /// For these predicates, use conjunctions of positive constraints. `fields_to_encodings`
    /// supports `And`, `FieldEq`, `FieldIn`, and `BitEq`.
    pub when: Predicate,

    /// Derived values for this instruction form for semantics (eg defining a certain "operand2 = Rm << Rs")
    pub derived_values: Vec<DerivedValue>,
}

impl InstructionForm {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            fields: Vec::new(),
            when: Predicate::Always,
            derived_values: Vec::new(),
        }
    }

    pub fn field(mut self, field: InstructionField) -> Self {
        self.fields.push(field);
        self
    }

    pub fn fields(mut self, fields: impl IntoIterator<Item = InstructionField>) -> Self {
        self.fields.extend(fields);
        self
    }

    pub fn when(mut self, predicate: Predicate) -> Self {
        self.when = predicate;
        self
    }

    pub fn derived_value(mut self, derived_value: DerivedValue) -> Self {
        self.derived_values.push(derived_value);
        self
    }

    pub fn width(&self) -> usize {
        self.fields.iter().map(InstructionField::width).sum()
    }

    /// Given a vector of field uses, produce all the possible encodings of this instruction form that would match those field uses.
    /// Things like variable bits are NOT expanded.
    /// This is the raw output, so certain inefficiencies may exist (eg this may output [0, 1] when [x] is more efficient)
    pub fn fields_to_encodings(
        &self,
        field_values: &HashMap<String, FieldUses>,
    ) -> Vec<BitPattern> {
        let mut encodings = Vec::new();
        // We approach this problem by walking through each field in in the instruction form
        // If a field is MergeMode::VariableBits, we don't need to expand anything
        // If it is MergeMode::Uses, and there are n uses, we need to generate n new instructions
        // So for an instruction with only MergeMode::VariableBits fields, we generate 1 encoding, and for an instruction with n MergeMode::Uses fields with m1, m2, ..., mn uses respectively, we generate m1 * m2 * ... * mn encodings
        // We can do this with a recursive helper function that takes the current index of the field we are processing, and the current encoding we have generated so far
        fn helper(
            form: &InstructionForm,
            field_values: &HashMap<String, FieldUses>,
            current_encoding: &mut Vec<Bit>,
            encodings: &mut Vec<BitPattern>,
            field_index: usize,
        ) {
            if field_index == form.fields.len() {
                encodings.push(BitPattern {
                    bits: current_encoding.clone(),
                });
                return;
            }
            let field = &form.fields[field_index];
            let Some(field_use) = (match &field.name {
                Some(name) => field_values.get(name),
                None => {
                    if field.pattern.bits.iter().any(|b| *b == Bit::Var) {
                        panic!("Unnamed fields cannot have variable bits");
                    }
                    // If there is no name, this is a constant field, so we can just use the pattern directly
                    Some(&FieldUses::VariableBits {
                        name: "__const__".to_string(),
                        pattern: Some(field.pattern.clone()),
                        len: field.pattern.len(),
                    })
                }
            }) else {
                // Since the field doesn't exist, we should abandon this specific encoding
                // This is because this instructionform isn't used
                return;
            };
            match (field.merge_mode, field_use) {
                (
                    MergeMode::VariableBits,
                    FieldUses::VariableBits {
                        name: _,
                        pattern,
                        len,
                    },
                ) => {
                    assert_eq!(
                        *len,
                        field.pattern.len(),
                        "FieldUses::VariableBits length must match instruction field width"
                    );
                    let Some(pattern) = pattern else {
                        return;
                    };
                    // If the field or a bit in the field necessarily must have a certain value for a predicate in the form
                    // and it is currently unknown, we must fix that bit to the required value, since otherwise we would generate an encoding that doesn't satisfy the form's predicate
                    let pattern_idx = current_encoding.len();
                    let constrained_patterns = form.constrain_variable_bits(
                        pattern,
                        pattern_idx,
                        field
                            .name
                            .as_ref()
                            .unwrap_or(&"__const__".to_string())
                            .as_str(),
                    );
                    for constrained_pattern in constrained_patterns {
                        current_encoding.extend(constrained_pattern.bits);
                        helper(
                            form,
                            field_values,
                            current_encoding,
                            encodings,
                            field_index + 1,
                        );
                        current_encoding.truncate(pattern_idx);
                    }
                }
                (
                    MergeMode::Uses,
                    FieldUses::Uses {
                        name: _,
                        patterns,
                        len,
                    },
                ) => {
                    assert_eq!(
                        *len,
                        field.pattern.len(),
                        "FieldUses::Uses length must match instruction field width"
                    );

                    // For each pattern, append it to the current encoding and recurse
                    for pattern in patterns {
                        let pattern_idx = current_encoding.len();
                        let constrained_patterns = form.constrain_variable_bits(
                            pattern,
                            pattern_idx,
                            field
                                .name
                                .as_ref()
                                .unwrap_or(&"__const__".to_string())
                                .as_str(),
                        );
                        for constrained_pattern in constrained_patterns {
                            current_encoding.extend(constrained_pattern.bits);
                            helper(
                                form,
                                field_values,
                                current_encoding,
                                encodings,
                                field_index + 1,
                            );
                            current_encoding.truncate(pattern_idx);
                        }
                    }
                }
                _ => panic!("Field use does not match field merge mode"),
            }
        }

        helper(self, field_values, &mut Vec::new(), &mut encodings, 0);

        // Remove any direct duplicates (created by constrain_variable_bits)
        let mut seen = HashSet::new();
        encodings.retain(|encoding| seen.insert(encoding.clone()));
        encodings
    }

    /// Elaborates variable bits in a BitPattern to satisfy the predicate of InstructionForm::when.
    /// `FieldIn` can split one broad pattern into multiple constrained patterns.
    /// Arguments:
    /// * `pattern` - the BitPattern to elaborate.
    /// * `pattern_idx` - the starting index of the pattern in the overall instruction encoding (used for checking BitEq predicates)
    /// * `field_name` - the name of the field corresponding to this pattern (used for checking FieldEq and FieldIn predicates)
    pub fn constrain_variable_bits(
        &self,
        pattern: &BitPattern,
        pattern_idx: usize,
        field_name: &str,
    ) -> Vec<BitPattern> {
        let pattern = pattern.clone();

        fn constrain_pattern(pattern: &BitPattern, value: &BitPattern) -> Option<BitPattern> {
            if pattern.bits.len() != value.bits.len() {
                return None;
            }

            let mut constrained = pattern.clone();
            for (pattern_bit, value_bit) in constrained.bits.iter_mut().zip(&value.bits) {
                match (*pattern_bit, *value_bit) {
                    (_, Bit::Var) => {}
                    (Bit::Var, bit) => *pattern_bit = bit,
                    (lhs, rhs) if lhs == rhs => {}
                    _ => return None,
                }
            }

            Some(constrained)
        }

        fn merge_patterns(patterns: Vec<BitPattern>) -> Vec<BitPattern> {
            let Some(len) = patterns.first().map(BitPattern::len) else {
                return Vec::new();
            };
            let patterns = patterns.into_iter().collect::<HashSet<_>>();
            let merged = FieldUses::Uses {
                name: "__predicate__".to_string(),
                patterns,
                len,
            }
            .merge();

            let FieldUses::Uses { patterns, .. } = merged else {
                unreachable!("FieldUses::Uses::merge must return FieldUses::Uses");
            };
            patterns.into_iter().collect()
        }

        fn apply_constraints(
            form: &InstructionForm,
            predicate: &Predicate,
            patterns: Vec<BitPattern>,
            pattern_idx: usize,
            field_name: &str,
        ) -> Vec<BitPattern> {
            match predicate {
                Predicate::Always => patterns,
                Predicate::Never => Vec::new(),
                Predicate::And(predicates) => {
                    let mut constrained = patterns;
                    for p in predicates {
                        constrained =
                            apply_constraints(form, p, constrained, pattern_idx, field_name);
                        if constrained.is_empty() {
                            break;
                        }
                    }
                    constrained
                }
                Predicate::FieldEq {
                    field_name: pred_field_name,
                    value,
                } => {
                    if pred_field_name == field_name {
                        patterns
                            .iter()
                            .filter_map(|pattern| constrain_pattern(pattern, value))
                            .collect()
                    } else {
                        patterns
                    }
                }
                Predicate::BitEq { index, value } => {
                    let pattern_len = patterns.first().map_or(0, BitPattern::len);
                    if *index < pattern_idx || *index >= pattern_idx + pattern_len {
                        return patterns;
                    }
                    let local_index = *index - pattern_idx;
                    patterns
                        .into_iter()
                        .filter_map(|mut pattern| {
                            let bit = pattern.bits.get_mut(local_index)?;
                            match (*bit, *value) {
                                (Bit::Var, value) => {
                                    *bit = value;
                                    Some(pattern)
                                }
                                (lhs, rhs) if lhs == rhs => Some(pattern),
                                _ => None,
                            }
                        })
                        .collect()
                }
                Predicate::FieldIn {
                    field_name: pred_field_name,
                    values,
                } => {
                    if pred_field_name == field_name {
                        merge_patterns(
                            patterns
                                .iter()
                                .flat_map(|pattern| {
                                    values
                                        .iter()
                                        .filter_map(|value| constrain_pattern(pattern, value))
                                })
                                .collect(),
                        )
                    } else {
                        patterns
                    }
                }
            }
        }

        apply_constraints(self, &self.when, vec![pattern], pattern_idx, field_name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldUses {
    /// The used values of the field is represented by a single bit pattern (eg 01 and 11 can be represented by x1)
    VariableBits {
        name: String,
        pattern: Option<BitPattern>,
        len: usize,
    },

    /// The used values of the field is represented by a set of distinct bit patterns (eg 00, 01, and 11 can be represented by {00, 01, 11}, but not by a single pattern)
    Uses {
        name: String,
        patterns: HashSet<BitPattern>,
        len: usize,
    },
}

impl FieldUses {
    /// Uses Quine-McCluskey style merging to attempt to merge the patterns in this FieldUses, returning a new FieldUses with the merged patterns. Only applicable for FieldUses::Uses.
    pub fn merge(&self) -> Self {
        match self {
            FieldUses::VariableBits { name, pattern, len } => FieldUses::VariableBits {
                name: name.clone(),
                pattern: pattern.clone(),
                len: *len,
            },
            FieldUses::Uses {
                name,
                patterns,
                len,
            } => {
                let mut patterns = patterns.clone();
                assert!(
                    patterns.iter().all(|pattern| pattern.len() == *len),
                    "All FieldUses::Uses patterns must match len"
                );
                fn remove_subsumed(patterns: HashSet<BitPattern>) -> HashSet<BitPattern> {
                    patterns
                        .iter()
                        .filter(|pattern| {
                            !patterns
                                .iter()
                                .any(|other| *other != **pattern && other.covers(pattern))
                        })
                        .cloned()
                        .collect()
                }

                patterns = remove_subsumed(patterns);
                loop {
                    let mut used = HashSet::new();
                    let mut new_strings = HashSet::new();

                    let bit_list: Vec<BitPattern> = patterns.iter().cloned().collect();

                    for i in 0..bit_list.len() {
                        for j in i + 1..bit_list.len() {
                            let b1 = &bit_list[i];
                            let b2 = &bit_list[j];

                            if b1.can_merge_with(b2) {
                                let merged = b1.merge_with(b2);
                                used.insert(b1.clone());
                                used.insert(b2.clone());
                                new_strings.insert(merged);
                            }
                        }
                    }

                    let next_strings = remove_subsumed(
                        patterns
                            .difference(&used)
                            .cloned()
                            .chain(new_strings.into_iter())
                            .collect(),
                    );

                    if next_strings == patterns {
                        break;
                    }

                    patterns = next_strings;
                }
                FieldUses::Uses {
                    name: name.clone(),
                    patterns: patterns,
                    len: *len,
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MergeMode {
    /// Merge by bit positions. If observed values differ in a bit, that bit becomes variable.
    ///
    /// Good for immediates, offsets, literal bitfields, etc.
    VariableBits,

    /// Merge by distinct used values.
    ///
    /// Good for register addresses, small selectors, opcodes, condition codes, etc.
    Uses,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionField {
    pub name: Option<FieldName>,
    pub pattern: BitPattern,
    pub merge_mode: MergeMode,
    pub is_immediate: bool,
    pub is_register_read: bool,
    pub is_register_write: bool,
}

impl InstructionField {
    pub fn named(name: impl Into<String>, pattern: BitPattern) -> Self {
        Self {
            name: Some(name.into()),
            pattern,
            merge_mode: MergeMode::VariableBits,
            is_immediate: false,
            is_register_read: false,
            is_register_write: false,
        }
    }

    pub fn constant(bits: &str) -> Self {
        Self {
            name: None,
            pattern: BitPattern::parse(bits),
            merge_mode: MergeMode::VariableBits,
            is_immediate: false,
            is_register_read: false,
            is_register_write: false,
        }
    }

    pub fn variable(name: impl Into<String>, width: usize) -> Self {
        Self {
            name: Some(name.into()),
            pattern: BitPattern::variable(width),
            merge_mode: MergeMode::VariableBits,
            is_immediate: false,
            is_register_read: false,
            is_register_write: false,
        }
    }

    pub fn merge_mode_uses(mut self) -> Self {
        self.merge_mode = MergeMode::Uses;
        self
    }

    pub fn merge_mode_variable_bits(mut self) -> Self {
        self.merge_mode = MergeMode::VariableBits;
        self
    }

    pub fn immediate(mut self) -> Self {
        self.is_immediate = true;
        self
    }

    pub fn register_read(mut self) -> Self {
        self.is_register_read = true;
        self
    }

    pub fn register_write(mut self) -> Self {
        self.is_register_write = true;
        self
    }

    pub fn register_read_write(mut self) -> Self {
        self.is_register_read = true;
        self.is_register_write = true;
        self
    }

    pub fn width(&self) -> usize {
        self.pattern.len()
    }
}

/// Helper function to create a constant instruction field
pub fn c(bits: &'static str) -> InstructionField {
    InstructionField::constant(bits)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Predicate {
    Always,
    Never,

    And(Vec<Predicate>),

    BitEq {
        index: usize,
        value: Bit,
    },

    FieldEq {
        field_name: String,
        value: BitPattern,
    },

    FieldIn {
        field_name: String,
        values: Vec<BitPattern>,
    },
}

impl Predicate {
    pub fn check(&self, inst: &DecodedInstruction) -> bool {
        match self {
            Predicate::Always => true,
            Predicate::Never => false,
            Predicate::And(inner) => inner.iter().all(|i| i.check(inst)),
            Predicate::BitEq { index, value } => inst.bits[*index] == *value,
            Predicate::FieldEq { field_name, value } => inst.field_value(field_name) == Some(value),
            Predicate::FieldIn { field_name, values } => values.iter().any(|v| {
                inst.field_value(field_name)
                    .is_some_and(|field| v.matches_bits(&field.bits))
            }),
        }
    }
}

// Predicate constructor functions (outside of impl to reduce verbosity)
pub fn bit_eq(index: usize, value: Bit) -> Predicate {
    assert!(
        value != Bit::Var,
        "BitEq must compare against Low or High, not Variable"
    );

    Predicate::BitEq { index, value }
}

pub fn field_eq(name: impl Into<String>, value: &str) -> Predicate {
    Predicate::FieldEq {
        field_name: name.into(),
        value: BitPattern::parse(value),
    }
}

pub fn field_in(
    name: impl Into<String>,
    values: impl IntoIterator<Item = impl Into<String>>,
) -> Predicate {
    Predicate::FieldIn {
        field_name: name.into(),
        values: values
            .into_iter()
            .map(|value| BitPattern::parse(&value.into()))
            .collect(),
    }
}

pub fn and(predicates: impl IntoIterator<Item = Predicate>) -> Predicate {
    Predicate::And(predicates.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static TEST_FILE_COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn write_temp_program(contents: &str) -> String {
        let id = TEST_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut path: PathBuf = std::env::temp_dir();
        path.push(format!(
            "isa_minimization_decode_program_{}_{}.bin",
            std::process::id(),
            id
        ));
        fs::write(&path, contents).unwrap();
        path.to_string_lossy().into_owned()
    }

    fn minimal_isa(instruction: Instruction) -> ISA {
        let reg = ArchitecturalRegister {
            identifier: 0,
            identifier_width: 1,
            width: 32,
        };
        ISA {
            registers: vec![reg],
            instructions: vec![instruction],
            sp: StackPointer {
                register: reg,
                stack_size: 16,
                direction: StackDirection::Downwards,
            },
            pc: reg,
        }
    }

    #[test]
    fn decode_program_reads_binary_file() {
        let instruction = Instruction::new("NOP", 2)
            .form(InstructionForm::new("nop_form").field(InstructionField::constant("01")));
        let isa = minimal_isa(instruction);
        let path = write_temp_program("01\n01\n");

        let decoded = DecodedInstruction::decode_program(&path, &isa).unwrap();

        assert_eq!(decoded.len(), 2);
        assert!(decoded.iter().all(|instr| instr.name == "NOP"));
        assert_eq!(decoded[0].assembly_line, 0);
        assert_eq!(decoded[1].assembly_line, 1);
    }

    #[test]
    fn field_and_predicate_builders_cover_variable_bits_and_field_in() {
        let field = InstructionField::variable("mode", 2)
            .merge_mode_uses()
            .merge_mode_variable_bits();
        assert_eq!(field.merge_mode, MergeMode::VariableBits);

        let instruction = Instruction::new("TEST", 2).form(
            InstructionForm::new("form")
                .field(field)
                .when(field_in("mode", ["01", "10"])),
        );

        assert!(
            instruction
                .find_match(&BitPattern::parse("01").bits)
                .is_some()
        );
        assert!(
            instruction
                .find_match(&BitPattern::parse("10").bits)
                .is_some()
        );
        assert!(
            instruction
                .find_match(&BitPattern::parse("11").bits)
                .is_none()
        );
    }

    #[test]
    fn find_match_marks_branch_instructions_static() {
        let instruction = Instruction::new("BRANCH", 2)
            .branch_instruction(BranchOffset::PCRelative(Expr::Const { value: 0, width: 8 }))
            .form(InstructionForm::new("branch_form").field(InstructionField::constant("11")));

        let decoded = instruction
            .find_match(&BitPattern::parse("11").bits)
            .expect("branch instruction should decode");

        assert!(decoded.branch_instruction.is_some());
        assert!(decoded.static_instruction);
    }

    fn decoded_with_form(form: InstructionForm, fields: Vec<DecodedField>) -> DecodedInstruction {
        DecodedInstruction {
            name: "TEST".to_string(),
            form,
            bits: BitPattern::parse("101011").bits,
            fields,
            branch_instruction: None,
            mem_addr: 0,
            static_instruction: false,
            assembly_line: 0,
        }
    }

    fn decoded_field(name: Option<&str>, value: &str, merge_mode: MergeMode) -> DecodedField {
        DecodedField {
            name: name.map(str::to_string),
            value: BitPattern::parse(value),
            merge_mode,
            is_immediate: false,
            is_register_read: false,
            is_register_write: false,
        }
    }

    fn uses(name: &str, patterns: &[&str]) -> (FieldName, FieldUses) {
        let len = patterns.first().expect("uses requires patterns").len();
        (
            name.to_string(),
            FieldUses::Uses {
                name: name.to_string(),
                patterns: patterns
                    .iter()
                    .map(|pattern| BitPattern::parse(pattern))
                    .collect(),
                len,
            },
        )
    }

    fn variable_bits(name: &str, pattern: &str) -> (FieldName, FieldUses) {
        (
            name.to_string(),
            FieldUses::VariableBits {
                name: name.to_string(),
                pattern: Some(BitPattern::parse(pattern)),
                len: pattern.len(),
            },
        )
    }

    #[test]
    fn instruction_valid_under_field_uses_accepts_matching_named_fields() {
        let instr = decoded_with_form(
            InstructionForm::new("form"),
            vec![
                decoded_field(None, "101", MergeMode::VariableBits),
                decoded_field(Some("opcode"), "10", MergeMode::Uses),
                decoded_field(Some("imm"), "0110", MergeMode::VariableBits),
            ],
        );
        let valid_field_uses =
            HashMap::from([uses("opcode", &["00", "10"]), variable_bits("imm", "0xx0")]);

        assert!(instruction_valid_under_field_uses(
            &instr,
            &valid_field_uses
        ));
    }

    #[test]
    fn instruction_valid_under_field_uses_rejects_empty_variable_bits_use() {
        let instr = decoded_with_form(
            InstructionForm::new("form"),
            vec![decoded_field(Some("imm"), "01", MergeMode::VariableBits)],
        );
        let valid_field_uses = HashMap::from([(
            "imm".to_string(),
            FieldUses::VariableBits {
                name: "imm".to_string(),
                pattern: None,
                len: 2,
            },
        )]);

        assert!(!instruction_valid_under_field_uses(
            &instr,
            &valid_field_uses
        ));
    }

    #[test]
    fn instruction_valid_under_field_uses_accepts_variable_decoded_uses_field() {
        let instr = decoded_with_form(
            InstructionForm::new("form"),
            vec![decoded_field(Some("opcode"), "1x", MergeMode::Uses)],
        );
        let valid_field_uses = HashMap::from([uses("opcode", &["10"])]);

        assert!(instruction_valid_under_field_uses(
            &instr,
            &valid_field_uses
        ));
    }

    #[test]
    fn instruction_valid_under_field_uses_rejects_missing_field_use() {
        let instr = decoded_with_form(
            InstructionForm::new("form"),
            vec![decoded_field(Some("opcode"), "10", MergeMode::Uses)],
        );

        assert!(!instruction_valid_under_field_uses(&instr, &HashMap::new()));
    }

    #[test]
    fn instruction_valid_under_field_uses_rejects_nonmatching_uses_pattern() {
        let instr = decoded_with_form(
            InstructionForm::new("form"),
            vec![decoded_field(Some("opcode"), "10", MergeMode::Uses)],
        );
        let valid_field_uses = HashMap::from([uses("opcode", &["00", "01"])]);

        assert!(!instruction_valid_under_field_uses(
            &instr,
            &valid_field_uses
        ));
    }

    #[test]
    fn instruction_valid_under_field_uses_rejects_nonmatching_variable_bits_pattern() {
        let instr = decoded_with_form(
            InstructionForm::new("form"),
            vec![decoded_field(Some("imm"), "0110", MergeMode::VariableBits)],
        );
        let valid_field_uses = HashMap::from([variable_bits("imm", "1xx0")]);

        assert!(!instruction_valid_under_field_uses(
            &instr,
            &valid_field_uses
        ));
    }

    #[test]
    fn instruction_valid_under_field_uses_rejects_failed_form_predicate() {
        let instr = decoded_with_form(
            InstructionForm::new("form")
                .field(InstructionField::variable("mode", 2))
                .when(field_eq("mode", "11")),
            vec![decoded_field(Some("mode"), "10", MergeMode::VariableBits)],
        );
        let valid_field_uses = HashMap::from([variable_bits("mode", "xx")]);

        assert!(!instruction_valid_under_field_uses(
            &instr,
            &valid_field_uses
        ));
    }

    mod inst_recognition {
        use super::*;

        #[test]
        fn test_simple_match() {
            let test = Instruction::new("TEST", 2).form(
                InstructionForm::new("form1")
                    .fields(vec![
                        InstructionField::variable("field1", 1), // bit 0 must be 0
                        InstructionField::variable("field2", 1), // bit 1 must be 0
                    ])
                    .when(and(vec![field_eq("field1", "0"), field_eq("field2", "0")])),
            );
            let test_bits = vec![Bit::Low, Bit::Low];
            let test_decoded = test.find_match(&test_bits);
            assert!(test_decoded.is_some());
            let test_decoded = test_decoded.unwrap();
            assert_eq!(test_decoded.bits, test_bits);
            assert_eq!(test_decoded.fields.len(), 2);
            assert_eq!(test_decoded.fields[0].name, Some("field1".to_string()));
            assert_eq!(test_decoded.fields[0].value, BitPattern::parse("0"));
            assert_eq!(test_decoded.fields[1].name, Some("field2".to_string()));
            assert_eq!(test_decoded.fields[1].value, BitPattern::parse("0"));
        }

        #[test]
        fn decoded_fields_preserve_immediate_marker() {
            let test =
                Instruction::new("TEST", 6).form(InstructionForm::new("form1").fields(vec![
                    InstructionField::constant("10"),
                    InstructionField::variable("rd", 2).merge_mode_uses(),
                    InstructionField::variable("imm", 2).immediate(),
                ]));

            let decoded = test
                .find_match(&[
                    Bit::High,
                    Bit::Low,
                    Bit::High,
                    Bit::Low,
                    Bit::Low,
                    Bit::High,
                ])
                .expect("instruction should decode");

            assert!(!decoded.fields[0].is_immediate);
            assert!(!decoded.fields[1].is_immediate);
            assert!(decoded.fields[2].is_immediate);
        }

        #[test]
        fn test_no_match() {
            let test = Instruction::new("TEST", 2).form(
                InstructionForm::new("form1")
                    .fields(vec![
                        InstructionField::variable("field1", 1), // bit 0 must be 0
                        InstructionField::variable("field2", 1), // bit 1 must be 0
                    ])
                    .when(and(vec![field_eq("field1", "0"), field_eq("field2", "0")])),
            );
            let test_bits = vec![Bit::High, Bit::Low];
            let test_decoded = test.find_match(&test_bits);
            assert!(test_decoded.is_none());
        }

        #[test]
        fn test_ambiguous_match() {
            let test = Instruction::new("TEST", 2)
                .form(
                    InstructionForm::new("form1")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                        ])
                        .when(and(vec![field_eq("field1", "0"), field_eq("field2", "0")])),
                )
                .form(
                    InstructionForm::new("form2")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                        ])
                        .when(and(vec![field_eq("field1", "0"), field_eq("field2", "0")])),
                );
            let test_bits = vec![Bit::Low, Bit::Low];
            let test_decoded = test.find_match(&test_bits);
            assert!(test_decoded.is_none());
        }

        #[test]
        fn test_disambiguation() {
            let test = Instruction::new("TEST", 3)
                .form(
                    InstructionForm::new("form1")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                            InstructionField::variable("field3", 1), // bit 2 must be 0
                        ])
                        .when(and(vec![field_eq("field1", "0"), field_eq("field2", "0")])),
                )
                .form(
                    InstructionForm::new("form2")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                            InstructionField::variable("field4", 1), // bit 2 must be 0
                        ])
                        .when(and(vec![field_eq("field1", "0"), field_eq("field2", "1")])),
                );
            let test_bits = vec![Bit::Low, Bit::High, Bit::Var];
            let test_decoded = test.find_match(&test_bits);
            assert!(test_decoded.is_some());
            let test_decoded = test_decoded.unwrap();
            assert_eq!(test_decoded.bits, test_bits);
            assert_eq!(test_decoded.fields.len(), 3);
            assert_eq!(test_decoded.fields[0].name, Some("field1".to_string()));
            assert_eq!(test_decoded.fields[0].value, BitPattern::parse("0"));
            assert_eq!(test_decoded.fields[1].name, Some("field2".to_string()));
            assert_eq!(test_decoded.fields[1].value, BitPattern::parse("1"));
            assert_eq!(test_decoded.fields[2].name, Some("field4".to_string()));
            assert_eq!(test_decoded.fields[2].value, BitPattern::parse("x"));
        }
    }

    mod fields_to_encodings {
        use super::*;

        #[test]
        fn constrain_variable_bits_applies_field_and_bit_eq_predicates() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 3))
                .when(and(vec![field_eq("field1", "1x0"), bit_eq(1, Bit::High)]));

            assert_eq!(
                form.constrain_variable_bits(&BitPattern::parse("xxx"), 0, "field1"),
                vec![BitPattern::parse("110")]
            );
        }

        #[test]
        fn constrain_variable_bits_rejects_unsatisfiable_predicates() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2))
                .when(and(vec![field_eq("field1", "10"), bit_eq(1, Bit::High)]));

            assert_eq!(
                form.constrain_variable_bits(&BitPattern::parse("1x"), 0, "field1"),
                Vec::<BitPattern>::new()
            );
        }

        #[test]
        fn constrain_variable_bits_expands_field_in_predicates() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2))
                .when(field_in("field1", ["0x", "x1"]));
            let expected = HashSet::from([BitPattern::parse("0x"), BitPattern::parse("x1")]);

            assert_eq!(
                form.constrain_variable_bits(&BitPattern::parse("xx"), 0, "field1")
                    .into_iter()
                    .collect::<HashSet<_>>(),
                expected
            );
        }

        #[test]
        fn constrain_variable_bits_merges_field_in_results() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2))
                .when(field_in("field1", ["00", "10"]));

            assert_eq!(
                form.constrain_variable_bits(&BitPattern::parse("xx"), 0, "field1"),
                vec![BitPattern::parse("x0")]
            );
        }

        #[test]
        fn test_variable_bits() {
            let form = InstructionForm::new("form1").field(InstructionField::variable("field1", 2));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::VariableBits {
                    name: "field1".to_string(),
                    pattern: Some(BitPattern::parse("x1")),
                    len: 2,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 1);
            assert_eq!(encodings[0], BitPattern::parse("x1"));
        }

        #[test]
        fn test_variable_bits_none_generates_no_encodings() {
            let form = InstructionForm::new("form1").field(InstructionField::variable("field1", 2));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::VariableBits {
                    name: "field1".to_string(),
                    pattern: None,
                    len: 2,
                },
            );

            let encodings = form.fields_to_encodings(&field_values);

            assert!(encodings.is_empty());
        }

        #[test]
        fn test_uses() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses());
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [
                        BitPattern::parse("00"),
                        BitPattern::parse("01"),
                        BitPattern::parse("11"),
                    ]
                    .iter()
                    .cloned()
                    .collect(),
                    len: 2,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 3);
            assert!(encodings.contains(&BitPattern::parse("00")));
            assert!(encodings.contains(&BitPattern::parse("01")));
            assert!(encodings.contains(&BitPattern::parse("11")));
        }

        #[test]
        fn fields_to_encodings_splits_wildcard_uses_with_field_in_predicate() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses())
                .when(field_in("field1", ["00", "10"]));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: HashSet::from([BitPattern::parse("xx")]),
                    len: 2,
                },
            );

            let encodings = form.fields_to_encodings(&field_values);

            assert_eq!(encodings, vec![BitPattern::parse("x0")]);
        }

        #[test]
        fn test_mixed() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses())
                .field(InstructionField::variable("field2", 1));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [BitPattern::parse("00"), BitPattern::parse("01")]
                        .iter()
                        .cloned()
                        .collect(),
                    len: 2,
                },
            );
            field_values.insert(
                "field2".to_string(),
                FieldUses::VariableBits {
                    name: "field2".to_string(),
                    pattern: Some(BitPattern::parse("x")),
                    len: 1,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 2);
            assert!(encodings.contains(&BitPattern::parse("00x")));
            assert!(encodings.contains(&BitPattern::parse("01x")));
        }

        #[test]
        fn test_complex() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses())
                .field(InstructionField::variable("field2", 2))
                .field(InstructionField::variable("field3", 3).merge_mode_uses());
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [BitPattern::parse("00"), BitPattern::parse("01")]
                        .iter()
                        .cloned()
                        .collect(),
                    len: 2,
                },
            );
            field_values.insert(
                "field2".to_string(),
                FieldUses::VariableBits {
                    name: "field2".to_string(),
                    pattern: Some(BitPattern::parse("xx")),
                    len: 2,
                },
            );
            field_values.insert(
                "field3".to_string(),
                FieldUses::Uses {
                    name: "field3".to_string(),
                    patterns: [BitPattern::parse("000"), BitPattern::parse("111")]
                        .iter()
                        .cloned()
                        .collect(),
                    len: 3,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 4);
            assert!(encodings.contains(&BitPattern::parse("00xx000")));
            assert!(encodings.contains(&BitPattern::parse("00xx111")));
            assert!(encodings.contains(&BitPattern::parse("01xx000")));
            assert!(encodings.contains(&BitPattern::parse("01xx111")));
        }

        #[test]
        fn test_consts() {
            let form = InstructionForm::new("form1")
                .field(c("10"))
                .field(InstructionField::variable("field1", 2).merge_mode_uses());
            let mut field_values = HashMap::new();
            field_values.insert(
                "field1".to_string(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [BitPattern::parse("00"), BitPattern::parse("01")]
                        .iter()
                        .cloned()
                        .collect(),
                    len: 2,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 2);
            assert!(encodings.contains(&BitPattern::parse("1000")));
            assert!(encodings.contains(&BitPattern::parse("1001")));
        }

        #[test]
        fn test_field_predicate_constraint_variable() {
            let form = InstructionForm::new("form1")
                .field(c("100101"))
                .field(InstructionField::variable("field2", 2))
                .field(c("10010"))
                .when(field_eq("field2", "00"));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field2".to_string(),
                FieldUses::VariableBits {
                    name: "field2".to_string(),
                    pattern: Some(BitPattern::parse("xx")),
                    len: 2,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 1);
            assert!(encodings.contains(&BitPattern::parse("1001010010010")));
        }

        #[test]
        fn test_field_predicate_constraint_uses() {
            let form = InstructionForm::new("form1")
                .field(c("100101"))
                .field(InstructionField::variable("field2", 2).merge_mode_uses())
                .field(c("10010"))
                .when(field_eq("field2", "00"));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field2".to_string(),
                FieldUses::Uses {
                    name: "field2".to_string(),
                    patterns: [
                        BitPattern::parse("00"),
                        BitPattern::parse("0x"),
                        BitPattern::parse("01"),
                    ]
                    .iter()
                    .cloned()
                    .collect(),
                    len: 2,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 1);
            assert!(encodings.contains(&BitPattern::parse("1001010010010")));
        }

        #[test]
        fn test_field_predicate_constraint_unsatisfiable() {
            let form = InstructionForm::new("form1")
                .field(c("100101"))
                .field(InstructionField::variable("field2", 2).merge_mode_uses())
                .field(c("10010"))
                .when(field_eq("field2", "00"));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field2".to_string(),
                FieldUses::Uses {
                    name: "field2".to_string(),
                    patterns: [BitPattern::parse("01"), BitPattern::parse("10")]
                        .iter()
                        .cloned()
                        .collect(),
                    len: 2,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 0);
        }

        #[test]
        fn test_field_predicate_constraint_multiple() {
            let form = InstructionForm::new("form1")
                .field(c("100101"))
                .field(InstructionField::variable("field2", 2).merge_mode_uses())
                .field(c("10010"))
                .field(InstructionField::variable("field3", 1))
                .when(and([field_eq("field2", "00"), bit_eq(13, Bit::High)]));
            let mut field_values = HashMap::new();
            field_values.insert(
                "field2".to_string(),
                FieldUses::Uses {
                    name: "field2".to_string(),
                    patterns: [
                        BitPattern::parse("00"),
                        BitPattern::parse("0x"),
                        BitPattern::parse("01"),
                    ]
                    .iter()
                    .cloned()
                    .collect(),
                    len: 2,
                },
            );
            field_values.insert(
                "field3".to_string(),
                FieldUses::VariableBits {
                    name: "field3".to_string(),
                    pattern: Some(BitPattern::parse("x")),
                    len: 1,
                },
            );
            let encodings = form.fields_to_encodings(&field_values);
            assert_eq!(encodings.len(), 1);
            assert!(encodings.contains(&BitPattern::parse("10010100100101")));
        }
    }

    mod merge_uses {
        use super::*;

        #[test]
        fn test_merge() {
            let field_uses = FieldUses::Uses {
                name: "field1".to_string(),
                patterns: [
                    BitPattern::parse("00"),
                    BitPattern::parse("01"),
                    BitPattern::parse("11"),
                ]
                .iter()
                .cloned()
                .collect(),
                len: 2,
            };
            let merged = field_uses.merge();
            // 00, 01, and 11 can be merged into 0x and x1, but it will still be FieldUses::Uses
            let FieldUses::Uses {
                name,
                patterns,
                len,
            } = merged
            else {
                panic!("Merged FieldUses should be MergeMode::Uses");
            };
            assert_eq!(name, "field1".to_string());
            assert_eq!(len, 2);
            assert_eq!(patterns.len(), 2);
            assert!(patterns.contains(&BitPattern::parse("0x")));
            assert!(patterns.contains(&BitPattern::parse("x1")));
        }

        #[test]
        fn test_no_merge() {
            let field_uses = FieldUses::Uses {
                name: "field1".to_string(),
                patterns: [BitPattern::parse("00"), BitPattern::parse("11")]
                    .iter()
                    .cloned()
                    .collect(),
                len: 2,
            };
            let merged = field_uses.merge();
            assert_eq!(
                merged,
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [BitPattern::parse("00"), BitPattern::parse("11")]
                        .iter()
                        .cloned()
                        .collect(),
                    len: 2,
                }
            );
        }

        #[test]
        fn test_merge_3bit() {
            let field_uses = FieldUses::Uses {
                name: "field1".to_string(),
                patterns: [
                    BitPattern::parse("000"),
                    BitPattern::parse("001"),
                    BitPattern::parse("111"),
                ]
                .iter()
                .cloned()
                .collect(),
                len: 3,
            };
            let merged = field_uses.merge();
            let FieldUses::Uses {
                name,
                patterns,
                len,
            } = merged
            else {
                panic!("Merged FieldUses should be MergeMode::Uses");
            };
            assert_eq!(name, "field1".to_string());
            assert_eq!(len, 3);
            assert_eq!(patterns.len(), 2);
            assert!(patterns.contains(&BitPattern::parse("00x")));
            assert!(patterns.contains(&BitPattern::parse("111")));
        }

        #[test]
        fn test_merge_complex() {
            let field_uses = FieldUses::Uses {
                name: "field1".to_string(),
                patterns: [
                    BitPattern::parse("000"),
                    BitPattern::parse("001"),
                    BitPattern::parse("010"),
                    BitPattern::parse("011"),
                    BitPattern::parse("100"),
                    BitPattern::parse("101"),
                    BitPattern::parse("110"),
                    BitPattern::parse("111"),
                ]
                .iter()
                .cloned()
                .collect(),
                len: 3,
            };
            let merged = field_uses.merge();
            let FieldUses::Uses {
                name,
                patterns,
                len,
            } = merged
            else {
                panic!("Merged FieldUses should be MergeMode::Uses");
            };
            assert_eq!(name, "field1".to_string());
            assert_eq!(len, 3);
            assert_eq!(patterns.len(), 1);
            assert!(patterns.contains(&BitPattern::parse("xxx")));
        }

        #[test]
        fn test_merge_removes_subsumed_pattern() {
            let field_uses = FieldUses::Uses {
                name: "field1".to_string(),
                patterns: [BitPattern::parse("0x"), BitPattern::parse("00")]
                    .iter()
                    .cloned()
                    .collect(),
                len: 2,
            };

            assert_eq!(
                field_uses.merge(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [BitPattern::parse("0x")].iter().cloned().collect(),
                    len: 2,
                }
            );
        }

        #[test]
        fn test_merge_removes_subsumed_pattern_after_merge_round() {
            let field_uses = FieldUses::Uses {
                name: "field1".to_string(),
                patterns: [
                    BitPattern::parse("00"),
                    BitPattern::parse("01"),
                    BitPattern::parse("0x"),
                ]
                .iter()
                .cloned()
                .collect(),
                len: 2,
            };

            assert_eq!(
                field_uses.merge(),
                FieldUses::Uses {
                    name: "field1".to_string(),
                    patterns: [BitPattern::parse("0x")].iter().cloned().collect(),
                    len: 2,
                }
            );
        }

        #[test]
        fn test_merge_preserves_empty_variable_bits() {
            let field_uses = FieldUses::VariableBits {
                name: "field1".to_string(),
                pattern: None,
                len: 3,
            };

            assert_eq!(
                field_uses.merge(),
                FieldUses::VariableBits {
                    name: "field1".to_string(),
                    pattern: None,
                    len: 3,
                }
            );
        }
    }
}
