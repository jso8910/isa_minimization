use std::thread::current;

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
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionField {
    name: Option<String>,
    pattern: BitPattern
}

impl InstructionField {
    pub fn named(name: impl Into<String>, pattern: BitPattern) -> Self {
        Self {
            name: Some(name.into()),
            pattern
        }
    }

    pub fn constant(bits: &str) -> Self {
        Self {
            name: None,
            pattern: BitPattern::parse(bits)
        }
    }

    pub fn variable(name: impl Into<String>, width: usize) -> Self {
        Self {
            name: Some(name.into()),
            pattern: BitPattern::variable(width),
        }
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
}