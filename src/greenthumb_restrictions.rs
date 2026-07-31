use std::collections::BTreeSet;

use crate::{
    bit::{Bit, BitPattern},
    isa_optimization::ISACandidate,
    isa_specification::ISA,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GreenthumbRestrictionOptions {
    pub exclude_branches: bool,
    pub exclude_multiplies: bool,
    pub exclude_extension_ops: bool,
}

impl Default for GreenthumbRestrictionOptions {
    fn default() -> Self {
        Self {
            exclude_branches: false,
            exclude_multiplies: false,
            exclude_extension_ops: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GreenthumbRestrictionSet {
    pub allow_patterns: BTreeSet<String>,
    pub deny_patterns: BTreeSet<String>,
}

impl GreenthumbRestrictionSet {
    pub fn from_candidate(
        isa: &ISA,
        candidate: &ISACandidate,
        options: &GreenthumbRestrictionOptions,
    ) -> Self {
        let mut allow_patterns = BTreeSet::new();

        for instruction in &isa.instructions {
            if should_exclude_instruction(&instruction.name, options) {
                continue;
            }

            let Some(active_forms) = candidate.active_forms.get(&instruction.name) else {
                continue;
            };

            for form in &instruction.forms {
                if !active_forms.contains(&form.name) {
                    continue;
                }

                for encoding in form.fields_to_encodings(&candidate.valid_field_uses) {
                    if encoding.len() == instruction.width {
                        allow_patterns.insert(bit_pattern_string(&encoding));
                    }
                }
            }
        }

        Self {
            allow_patterns,
            deny_patterns: BTreeSet::new(),
        }
    }

    pub fn with_deny_pattern(mut self, pattern: impl Into<String>) -> Self {
        self.deny_patterns.insert(validate_pattern(pattern.into()));
        self
    }

    pub fn with_deny_patterns(mut self, patterns: impl IntoIterator<Item = String>) -> Self {
        for pattern in patterns {
            self.deny_patterns.insert(validate_pattern(pattern));
        }
        self
    }

    pub fn to_racket_default_deny(&self) -> String {
        let mut out = String::from("((default deny)\n");
        for pattern in &self.allow_patterns {
            out.push_str(&format!(" (allow \"{pattern}\")\n"));
        }
        for pattern in &self.deny_patterns {
            out.push_str(&format!(" (deny \"{pattern}\")\n"));
        }
        out.push_str(")\n");
        out
    }
}

fn should_exclude_instruction(name: &str, options: &GreenthumbRestrictionOptions) -> bool {
    (options.exclude_branches && name.starts_with("branch_ops"))
        || (options.exclude_multiplies && name.starts_with("multiply_ops"))
        || (options.exclude_extension_ops && is_extension_instruction(name))
}

fn is_extension_instruction(name: &str) -> bool {
    matches!(
        name,
        "division_ops" | "bitfield_ops" | "reverse_ops" | "extension_ops"
    )
}

fn bit_pattern_string(pattern: &BitPattern) -> String {
    pattern
        .bits
        .iter()
        .map(|bit| match bit {
            Bit::Low => '0',
            Bit::High => '1',
            Bit::Var | Bit::Test => 'x',
        })
        .collect()
}

fn validate_pattern(pattern: String) -> String {
    assert_eq!(
        pattern.len(),
        32,
        "GreenThumb ARM restriction patterns must be 32 bits"
    );
    assert!(
        pattern
            .chars()
            .all(|ch| matches!(ch, '0' | '1' | 'x' | 'X')),
        "GreenThumb ARM restriction patterns may only contain 0, 1, or x"
    );
    pattern.to_ascii_lowercase()
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap, HashSet};

    use crate::{
        bit::BitPattern,
        greenthumb_restrictions::{GreenthumbRestrictionOptions, GreenthumbRestrictionSet},
        isa_optimization::ISACandidate,
        isa_specification::{
            ArchitecturalRegister, FieldUses, ISA, Instruction, InstructionField, InstructionForm,
            StackDirection, StackPointer, linear_pc_to_instruction_index,
        },
    };

    fn toy_isa() -> ISA {
        ISA {
            registers: vec![
                ArchitecturalRegister {
                    identifier: 0,
                    identifier_width: 1,
                    width: 32,
                },
                ArchitecturalRegister {
                    identifier: 1,
                    identifier_width: 1,
                    width: 32,
                },
            ],
            instructions: vec![
                Instruction::new("alu", 4).form(
                    InstructionForm::new("base")
                        .field(InstructionField::constant("10"))
                        .field(InstructionField::variable("opcode", 2).merge_mode_uses()),
                ),
                Instruction::new("branch_ops_b", 4).form(
                    InstructionForm::new("base")
                        .field(InstructionField::constant("11"))
                        .field(InstructionField::variable("target", 2)),
                ),
            ],
            sp: StackPointer {
                register: ArchitecturalRegister {
                    identifier: 1,
                    identifier_width: 1,
                    width: 32,
                },
                stack_size: 4,
                direction: StackDirection::Downwards,
            },
            pc: ArchitecturalRegister {
                identifier: 1,
                identifier_width: 1,
                width: 32,
            },
            pc_to_instruction_index: linear_pc_to_instruction_index,
        }
    }

    #[test]
    fn candidate_emits_default_deny_allow_patterns() {
        let isa = toy_isa();
        let candidate = ISACandidate {
            valid_field_uses: HashMap::from([(
                "opcode".to_string(),
                FieldUses::Uses {
                    name: "opcode".to_string(),
                    patterns: HashSet::from([BitPattern::parse("0x")]),
                    len: 2,
                },
            )]),
            active_forms: HashMap::from([("alu".to_string(), HashSet::from(["base".to_string()]))]),
        };

        let restrictions = GreenthumbRestrictionSet::from_candidate(
            &isa,
            &candidate,
            &GreenthumbRestrictionOptions::default(),
        );

        assert_eq!(
            restrictions.to_racket_default_deny(),
            "((default deny)\n (allow \"100x\")\n)\n"
        );
    }

    #[test]
    fn branch_forms_can_be_excluded() {
        let isa = toy_isa();
        let candidate = ISACandidate::max_isa(&isa);
        let restrictions = GreenthumbRestrictionSet::from_candidate(
            &isa,
            &candidate,
            &GreenthumbRestrictionOptions {
                exclude_branches: true,
                exclude_multiplies: false,
                exclude_extension_ops: false,
            },
        );

        assert!(restrictions.allow_patterns.contains("10xx"));
        assert!(!restrictions.allow_patterns.contains("11xx"));
    }

    #[test]
    fn deny_patterns_are_emitted_after_allows() {
        let restrictions = GreenthumbRestrictionSet {
            allow_patterns: BTreeSet::from(["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx".to_string()]),
            deny_patterns: BTreeSet::new(),
        }
        .with_deny_pattern("11110000111100001111000011110000");

        assert_eq!(
            restrictions.to_racket_default_deny(),
            "((default deny)\n (allow \"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\")\n (deny \"11110000111100001111000011110000\")\n)\n"
        );
    }

    #[test]
    fn inactive_forms_emit_no_allow_patterns() {
        let isa = toy_isa();
        let candidate = ISACandidate {
            valid_field_uses: HashMap::from([(
                "opcode".to_string(),
                FieldUses::Uses {
                    name: "opcode".to_string(),
                    patterns: HashSet::from([BitPattern::parse("xx")]),
                    len: 2,
                },
            )]),
            active_forms: HashMap::from([("alu".to_string(), HashSet::new())]),
        };

        let restrictions = GreenthumbRestrictionSet::from_candidate(
            &isa,
            &candidate,
            &GreenthumbRestrictionOptions::default(),
        );

        assert!(restrictions.allow_patterns.is_empty());
    }
}
