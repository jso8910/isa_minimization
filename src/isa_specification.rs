use std::collections::{HashMap, HashSet};

use super::bit::{BitPattern, Bit};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    pub name: String,
    pub width: usize,

    /// An instruction can have multiple forms (eg immediate-shifted-registers vs register-shifted-register)
    pub forms: Vec<InstructionForm>,
    pub constraints: Vec<Predicate>
}

impl Instruction {
    pub fn new(name: impl Into<String>, width: usize) -> Self {
        Self {
            name: name.into(),
            width,
            forms: Vec::new(),
            constraints: Vec::new(),
        }
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

    pub fn constraint(mut self, predicate: Predicate) -> Self {
        self.constraints.push(predicate);
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
                name: Some(self.name.clone()),
                bits: bits.to_vec(),
                fields: Vec::new(),
            };
            let mut matches = true;

            let mut current_bit_index = 0;

            for field in form.fields.iter() {
                let pattern_matches = &field.pattern.matches_bits(&bits[current_bit_index..current_bit_index + field.pattern.len()]);
                if !pattern_matches {
                    matches = false;
                    break;
                }

                decoded_fields.fields.push(DecodedField {
                    name: field.name.clone(),
                    value: BitPattern::new(bits[current_bit_index..current_bit_index + field.pattern.len()].to_vec()),
                });

                current_bit_index += field.pattern.len();
            }

            if matches && form.when.check(&decoded_fields) && self.constraints.iter().all(|c| c.check(&decoded_fields)) {
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
    pub name: Option<String>,
    pub bits: Vec<Bit>,
    pub fields: Vec<DecodedField>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedField {
    pub name: Option<String>,
    pub value: BitPattern,
}

impl DecodedInstruction {
    pub fn field_value(&self, name: &str) -> Option<&BitPattern> {
        self.fields
            .iter()
            .find(|field| field.name == Some(name.to_string()))
            .map(|field| &field.value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionForm {
    pub name: String,
    pub fields: Vec<InstructionField>,

    /// Condition (on the instruction) for when the field is applicable (eg requiring a certain bit to be set to 1)
    pub when: Predicate
}

impl InstructionForm {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            fields: Vec::new(),
            when: Predicate::Always
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

    pub fn width(&self) -> usize {
        self.fields.iter().map(InstructionField::width).sum()
    }

    /// Given a vector of field uses, produce all the possible encodings of this instruction form that would match those field uses.
    /// Things like variable bits are NOT expanded.
    /// This is the raw output, so certain inefficiencies may exist (eg this may output [0, 1] when [x] is more efficient)
    fn fields_to_encodings_raw(&self, field_values: &HashMap<String, FieldUses>) -> Vec<BitPattern> {
        let mut encodings = Vec::new();

        // We approach this problem by walking through each field in in the instruction form
        // If a field is MergeMode::VariableBits, we don't need to expand anything
        // If it is MergeMode::Uses, and there are n uses, we need to generate n new instructions
        // So for an instruction with only MergeMode::VariableBits fields, we generate 1 encoding, and for an instruction with n MergeMode::Uses fields with m1, m2, ..., mn uses respectively, we generate m1 * m2 * ... * mn encodings
        // We can do this with a recursive helper function that takes the current index of the field we are processing, and the current encoding we have generated so far
        fn helper(
            form: &InstructionForm,
            field_values: &HashMap<String, FieldUses>,
            current_encoding: BitPattern,
            encodings: &mut Vec<BitPattern>,
            field_index: usize,
        ) {
            if field_index == form.fields.len() {
                encodings.push(current_encoding);
                return;
            }
            let field = &form.fields[field_index];
            let field_use = match &field.name {
                Some(name) => field_values.get(name).unwrap_or_else(|| panic!("Field value for '{}' not found", name)),
                None => {
                    if field.pattern.bits.iter().any(|b| *b == Bit::Var) {
                        panic!("Unnamed fields cannot have variable bits");
                    }
                    // If there is no name, this is a constant field, so we can just use the pattern directly
                    &FieldUses::VariableBits { name: "__const__".to_string(), pattern: field.pattern.clone() }
                }
            };
            match (field.merge_mode, field_use) {
                (MergeMode::VariableBits, FieldUses::VariableBits { name: _, pattern }) => {
                    // Just append the pattern to the current encoding and move on
                    let new_encoding = BitPattern {
                        bits: [current_encoding.bits.clone(), pattern.bits.clone()].concat(),
                    };
                    helper(form, field_values, new_encoding, encodings, field_index + 1);
                }
                (MergeMode::Uses, FieldUses::Uses { name: _, patterns }) => {
                    // For each pattern, append it to the current encoding and recurse
                    for pattern in patterns {
                        let new_encoding = BitPattern {
                            bits: [current_encoding.bits.clone(), pattern.bits.clone()].concat(),
                        };
                        helper(form, field_values, new_encoding, encodings, field_index + 1);
                    }
                }
                _ => panic!("Field use does not match field merge mode"),
            }
        }

        helper(self, field_values, BitPattern { bits: Vec::new() }, &mut encodings, 0);
        encodings
    }

    /// Given a vector of field uses, produce all the possible encodings of this instruction form that would match those field uses.
    /// Things like variable bits are NOT expanded.
    /// This function returns merged encodings where encodings that differ by only 1 bit flip are merged to an x (eg [00, 01] -> [0x])
    pub fn fields_to_encodings(&self, field_values: &HashMap<String, FieldUses>) -> Vec<BitPattern> {
        let encodings_raw = self.fields_to_encodings_raw(field_values);

        let mut encodings = encodings_raw.clone();

        // Once no merges occur in one cycle, we stop
        let mut merges_happened = true;

        'outer: while merges_happened {
            merges_happened = false;
            let encodings_copy = encodings.clone();
            for encoding in encodings_copy.iter() {
                let num_ones = encoding.num_high();

                // The only comparisons we want to make are to encodings which have exactly one more one than the current encoding
                for enc_cmp in encodings_copy.iter().filter(|enc| enc.num_high() == num_ones + 1) {
                    // Now check whether the single extra 1 is in a place where the current `encoding` has a 0
                    println!("Comparing {:?} and {:?}", encoding, enc_cmp);
                    if encoding.can_merge_with(enc_cmp) {
                        // If so, merge them and add the merged encoding to the list of encodings (if it doesn't already exist)
                        let merged = encoding.merge_with(enc_cmp);
                        if !encodings_raw.contains(&merged) {
                            encodings.push(merged);
                            merges_happened = true;
                            // Remove the two original encodings from the list of encodings (if they exist)
                            encodings.retain(|e| e != encoding && e != enc_cmp);
                            continue 'outer;
                        }
                    }
                }
            }
        }
        encodings
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldUses {
    /// The used values of the field is represented by a single bit pattern (eg 01 and 11 can be represented by x1)
    VariableBits { name: String, pattern: BitPattern },

    /// The used values of the field is represented by a set of distinct bit patterns (eg 00, 01, and 11 can be represented by {00, 01, 11}, but not by a single pattern)
    Uses { name: String, patterns: HashSet<BitPattern> },
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
    pub name: Option<String>,
    pub pattern: BitPattern,
    pub merge_mode: MergeMode,
}

impl InstructionField {
    pub fn named(name: impl Into<String>, pattern: BitPattern) -> Self {
        Self {
            name: Some(name.into()),
            pattern,
            merge_mode: MergeMode::VariableBits,
        }
    }

    pub fn constant(bits: &str) -> Self {
        Self {
            name: None,
            pattern: BitPattern::parse(bits),
            merge_mode: MergeMode::VariableBits,
        }
    }

    pub fn variable(name: impl Into<String>, width: usize) -> Self {
        Self {
            name: Some(name.into()),
            pattern: BitPattern::variable(width),
            merge_mode: MergeMode::VariableBits,
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

    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),

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
            Predicate::Not(inner) => !inner.check(inst),
            Predicate::And(inner) => inner.iter().all(|i| i.check(inst)),
            Predicate::Or(inner) => inner.iter().any(|i| i.check(inst)),
            Predicate::BitEq { index, value } => inst.bits[*index] == *value,
            Predicate::FieldEq { field_name, value} => inst.field_value(field_name) == Some(value),
            Predicate::FieldIn { field_name, values } => values.iter().any(|v| inst.field_value(field_name) == Some(v))
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

pub fn field_in(name: impl Into<String>, values: impl IntoIterator<Item = &'static str>) -> Predicate {
    Predicate::FieldIn {
        field_name: name.into(),
        values: values.into_iter().map(BitPattern::parse).collect(),
    }
}

pub fn not(predicate: Predicate) -> Predicate {
    Predicate::Not(Box::new(predicate))
}

pub fn and(predicates: impl IntoIterator<Item = Predicate>) -> Predicate {
    Predicate::And(predicates.into_iter().collect())
}

pub fn or(predicates: impl IntoIterator<Item = Predicate>) -> Predicate {
    Predicate::Or(predicates.into_iter().collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    mod inst_recognition {
        use super::*;

        #[test]
        fn test_simple_match() {
            let test = Instruction::new("TEST", 2)
                .form(
                    InstructionForm::new("form1")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                        ]).when(and(vec![
                            field_eq("field1", "0"),
                            field_eq("field2", "0"),
                        ])),
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
         fn test_no_match() {
            let test = Instruction::new("TEST", 2)
                .form(
                    InstructionForm::new("form1")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                        ]).when(and(vec![
                            field_eq("field1", "0"),
                            field_eq("field2", "0"),
                        ])),
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
                        ]).when(and(vec![
                            field_eq("field1", "0"),
                            field_eq("field2", "0"),
                        ])),
                )
                .form(
                    InstructionForm::new("form2")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                        ]).when(and(vec![
                            field_eq("field1", "0"),
                            field_eq("field2", "0"),
                        ])),
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
                        ]).when(and(vec![
                            field_eq("field1", "0"),
                            field_eq("field2", "0"),
                        ])),
                )
                .form(
                    InstructionForm::new("form2")
                        .fields(vec![
                            InstructionField::variable("field1", 1), // bit 0 must be 0
                            InstructionField::variable("field2", 1), // bit 1 must be 0
                            InstructionField::variable("field4", 1), // bit 2 must be 0
                        ]).when(and(vec![
                            field_eq("field1", "0"),
                            field_eq("field2", "1"),
                        ])),
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

    mod fields_to_encodings_raw {
        use super::*;

        #[test]
        fn test_variable_bits() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2));
            let mut field_values = HashMap::new();
            field_values.insert("field1".to_string(), FieldUses::VariableBits { name: "field1".to_string(), pattern: BitPattern::parse("x1") });
            let encodings = form.fields_to_encodings_raw(&field_values);
            assert_eq!(encodings.len(), 1);
            assert_eq!(encodings[0], BitPattern::parse("x1"));
        }

        #[test]
        fn test_uses() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses());
            let mut field_values = HashMap::new();
            field_values.insert("field1".to_string(), FieldUses::Uses { name: "field1".to_string(), patterns: [BitPattern::parse("00"), BitPattern::parse("01"), BitPattern::parse("11")].iter().cloned().collect() });
            let encodings = form.fields_to_encodings_raw(&field_values);
            assert_eq!(encodings.len(), 3);
            assert!(encodings.contains(&BitPattern::parse("00")));
            assert!(encodings.contains(&BitPattern::parse("01")));
            assert!(encodings.contains(&BitPattern::parse("11")));
        }

        #[test]
        fn test_mixed() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses())
                .field(InstructionField::variable("field2", 1));
            let mut field_values = HashMap::new();
            field_values.insert("field1".to_string(), FieldUses::Uses { name: "field1".to_string(), patterns: [BitPattern::parse("00"), BitPattern::parse("01")].iter().cloned().collect() });
            field_values.insert("field2".to_string(), FieldUses::VariableBits { name: "field2".to_string(), pattern: BitPattern::parse("x") });
            let encodings = form.fields_to_encodings_raw(&field_values);
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
            field_values.insert("field1".to_string(), FieldUses::Uses { name: "field1".to_string(), patterns: [BitPattern::parse("00"), BitPattern::parse("01")].iter().cloned().collect() });
            field_values.insert("field2".to_string(), FieldUses::VariableBits { name: "field2".to_string(), pattern: BitPattern::parse("xx") });
            field_values.insert("field3".to_string(), FieldUses::Uses { name: "field3".to_string(), patterns: [BitPattern::parse("000"), BitPattern::parse("111")].iter().cloned().collect() });
            let encodings = form.fields_to_encodings_raw(&field_values);
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
            field_values.insert("field1".to_string(), FieldUses::Uses { name: "field1".to_string(), patterns: [BitPattern::parse("00"), BitPattern::parse("01")].iter().cloned().collect() });
            let encodings = form.fields_to_encodings_raw(&field_values);
            assert_eq!(encodings.len(), 2);
            assert!(encodings.contains(&BitPattern::parse("1000")));
            assert!(encodings.contains(&BitPattern::parse("1001")));
        }
    }

    mod fields_to_encodings {
        use super::*;

        fn expand(bp: &BitPattern) -> HashSet<String> {
            fn helper(bits: &[Bit], idx: usize, cur: &mut String, out: &mut HashSet<String>) {
                if idx == bits.len() { out.insert(cur.clone()); return; }
                match bits[idx] {
                    Bit::Low => { cur.push('0'); helper(bits, idx+1, cur, out); cur.pop(); }
                    Bit::High => { cur.push('1'); helper(bits, idx+1, cur, out); cur.pop(); }
                    Bit::Var => {
                        cur.push('0'); helper(bits, idx+1, cur, out); cur.pop();
                        cur.push('1'); helper(bits, idx+1, cur, out); cur.pop();
                    }
                    Bit::Test => panic!("Test bits should not be present in encodings"),
                }
            }
            let mut out = HashSet::new();
            let mut s = String::new();
            helper(&bp.bits, 0, &mut s, &mut out);
            out
        }

        #[test]
        fn merge_property_test() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses())
                .field(InstructionField::variable("field2", 2))
                .field(InstructionField::variable("field3", 3).merge_mode_uses());
            let mut field_values = HashMap::new();
            field_values.insert("field1".to_string(), FieldUses::Uses { name: "field1".to_string(), patterns: [BitPattern::parse("00"), BitPattern::parse("01")].iter().cloned().collect() });
            field_values.insert("field2".to_string(), FieldUses::VariableBits { name: "field2".to_string(), pattern: BitPattern::parse("xx") });
            field_values.insert("field3".to_string(), FieldUses::Uses { name: "field3".to_string(), patterns: [BitPattern::parse("000"), BitPattern::parse("111")].iter().cloned().collect() });
            let raw = form.fields_to_encodings_raw(&field_values);
            let merged = form.fields_to_encodings(&field_values);

            let raw_expanded: HashSet<String> = raw.iter().flat_map(|p| expand(p)).collect();
            let merged_expanded: HashSet<String> = merged.iter().flat_map(|p| expand(p)).collect();

            assert_eq!(raw_expanded, merged_expanded);        // coverage / no-new-concretes
            assert!(merged.len() <= raw.len());               // reduction
            assert_eq!(merged, form.fields_to_encodings(&field_values)); // deterministic
        }

                #[test]
        fn merge_property_test2() {
            let form = InstructionForm::new("form1")
                .field(InstructionField::variable("field1", 2).merge_mode_uses())
                .field(InstructionField::variable("field2", 2))
                .field(InstructionField::variable("field3", 3).merge_mode_uses());
            let mut field_values = HashMap::new();
            field_values.insert("field1".to_string(), FieldUses::Uses { name: "field1".to_string(), patterns: [BitPattern::parse("00"), BitPattern::parse("01")].iter().cloned().collect() });
            field_values.insert("field2".to_string(), FieldUses::VariableBits { name: "field2".to_string(), pattern: BitPattern::parse("x1") });
            field_values.insert("field3".to_string(), FieldUses::Uses { name: "field3".to_string(), patterns: [BitPattern::parse("000"), BitPattern::parse("111"), BitPattern::parse("101")].iter().cloned().collect() });
            let raw = form.fields_to_encodings_raw(&field_values);
            let merged = form.fields_to_encodings(&field_values);

            let raw_expanded: HashSet<String> = raw.iter().flat_map(|p| expand(p)).collect();
            let merged_expanded: HashSet<String> = merged.iter().flat_map(|p| expand(p)).collect();

            assert_eq!(raw_expanded, merged_expanded);        // coverage / no-new-concretes
            assert!(merged.len() <= raw.len());               // reduction
            assert_eq!(merged, form.fields_to_encodings(&field_values)); // deterministic
        }
    }
}