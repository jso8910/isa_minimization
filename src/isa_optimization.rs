use std::collections::{HashMap, HashSet};

use rand::{
    Rng, RngExt,
    distr::{Distribution, weighted::WeightedIndex},
    seq::{IndexedRandom, IteratorRandom},
};

use crate::{
    bit::{Bit, BitPattern},
    instruction_semantics::FieldName,
    isa_specification::{FieldUses, ISA, MergeMode},
};

pub struct IsaOptimizationManager<'a, R: Rng> {
    isa: &'a ISA,
    candidates: Vec<ISACandidate>,
    rng: R,
}

impl<'a, R: Rng> IsaOptimizationManager<'a, R> {
    /// Evaluates the gate count which will be able to be removed by a candidate
    fn gate_removal_count(&mut self, candidate: ISACandidate) -> u32 {
        todo!()
    }

    /// Mutates an ISA candidate
    fn mutate(&mut self, candidate: ISACandidate) -> ISACandidate {
        // First, select a random field
        // Each field is almost equivalent to a gene
        let mut candidate = candidate;
        let (field, uses) = candidate
            .valid_field_uses
            .iter()
            .choose(&mut self.rng)
            .expect("valid_field_uses should not be empty");
        let field = field.clone();
        let field_width = match uses {
            FieldUses::VariableBits { pattern, .. } => pattern.len(),
            FieldUses::Uses { len, .. } => *len,
        };
        let new_field = self.mutate_field(uses.clone(), field_width);
        candidate.valid_field_uses.insert(field, new_field);
        candidate
    }

    /// Mutates the provided field
    fn mutate_field(&mut self, mut field: FieldUses, field_width: usize) -> FieldUses {
        match field {
            FieldUses::VariableBits { name, mut pattern } => {
                // Choose a random bit to flip
                let bit_idx = self.rng.random_range(0..pattern.bits.len());
                let new_bit = match pattern.bits[bit_idx] {
                    Bit::Low => Bit::High,
                    Bit::High => Bit::Low,
                    // If variable, we choose a random bit
                    _ => choose_random_bit(&mut self.rng),
                };
                pattern.bits[bit_idx] = new_bit;
                FieldUses::VariableBits { name, pattern }
            }

            FieldUses::Uses {
                name,
                mut patterns,
                len,
            } => {
                assert_eq!(
                    len, field_width,
                    "FieldUses::Uses len must match field_width"
                );
                assert!(
                    patterns.iter().all(|pattern| pattern.len() == len),
                    "All FieldUses::Uses patterns must match len"
                );
                // For `Uses`, what is done is constructing a weighted average.
                // Each pattern has a frequncy of 2^k where k = number of variable bits, and there
                // is finally a frequency for non-included patterns, equal to the number of patterns
                // that are uncovered
                //
                // One of these patterns is selected according to this weighting. If a pattern is
                // selected, a random variable bit is chosen to switch to a non-variable bit. Or, if
                // there are no variable bits in a pattern, that pattern is removed.
                // If the non-included patterns are selected, a random sequence of high and low bits
                // which isn't covered by the current set of Bifield_length: usizetPatterns is
                // selected.

                let mut patterns_ordered = patterns.clone().into_iter().collect();
                let mut freqs = Self::construct_bitpatterns_frequencies(&patterns_ordered);

                let uncovered = Self::uncovered_patterns(&patterns, field_width);

                // Now we give a frequency in the distribution for the number of uncovered bit patterns
                freqs.push(
                    uncovered
                        .iter()
                        .map(|p| 1 << p.num_variable())
                        .sum::<u128>(),
                );
                let dist = WeightedIndex::new(&freqs).expect("WeightedIndex not created");
                let mut pattern_idx = dist.sample(&mut self.rng);

                // This doesn't correspond with a real pattern, it means we want to add a random
                // uncovered pattern
                if pattern_idx == patterns_ordered.len() {
                    patterns.insert(self.random_pattern(&uncovered, field_width));
                } else {
                    // Now, take the pattern out of `patterns`, flip a variable bit to a
                    // non-variable, and add it back
                    let mut pattern = patterns_ordered.remove(pattern_idx);
                    patterns.remove(&pattern);
                    if pattern.num_variable() != 0 {
                        let variable_idxs: Vec<_> = pattern
                            .bits
                            .iter()
                            .enumerate()
                            .filter(|(idx, b)| **b == Bit::Var)
                            .map(|e| e.0)
                            .collect();
                        let idx_to_mutate = variable_idxs
                            .choose(&mut self.rng)
                            .expect("There is at least one varaible bit");
                        let choice = [Bit::Low, Bit::High]
                            .choose(&mut self.rng)
                            .expect("Array has 2 elements");
                        pattern.bits[*idx_to_mutate] = *choice;
                        patterns.insert(pattern);
                    }
                }
                FieldUses::Uses {
                    name,
                    patterns,
                    len,
                }
                .merge()
            }
        }
    }

    fn uncovered_patterns(
        patterns: &HashSet<BitPattern>,
        field_width: usize,
    ) -> HashSet<BitPattern> {
        assert!(
            patterns.iter().all(|pattern| pattern.len() == field_width),
            "All patterns must match field_width"
        );
        let universal = BitPattern::variable(field_width);
        let mut uncovered_patterns = HashSet::from([universal]);

        for pattern in patterns {
            let mut new_uncovered = HashSet::new();
            for uncovered in uncovered_patterns.iter() {
                new_uncovered.extend(uncovered.cube_subtract(pattern));
            }
            uncovered_patterns = new_uncovered;
        }
        uncovered_patterns
    }

    fn random_pattern(&mut self, patterns: &HashSet<BitPattern>, field_width: usize) -> BitPattern {
        assert!(
            patterns.iter().all(|pattern| pattern.len() == field_width),
            "All patterns must match field_width"
        );

        let mut patterns_ordered = patterns.into_iter().cloned().collect();
        let weights = Self::construct_bitpatterns_frequencies(&patterns_ordered);

        let dist = WeightedIndex::new(&weights).expect("WeightedIndex not created");
        let mut pattern = patterns_ordered.remove(dist.sample(&mut self.rng));

        for bit in &mut pattern.bits {
            if *bit == Bit::Var {
                *bit = if self.rng.random() {
                    Bit::High
                } else {
                    Bit::Low
                };
            }
        }

        pattern
    }

    fn construct_bitpatterns_frequencies(patterns: &Vec<BitPattern>) -> Vec<u128> {
        let mut freqs = vec![0; patterns.len()];
        for (idx, pattern) in patterns.iter().enumerate() {
            freqs[idx] = 1 << pattern.num_variable();
        }
        freqs
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ISACandidate {
    valid_field_uses: HashMap<FieldName, FieldUses>,
}

impl ISACandidate {
    /// Generates an ISACandidate which supports all functions of an ISA
    pub fn max_isa(isa: &ISA) -> Self {
        let mut valid_field_uses = HashMap::new();
        for instruction in isa.instructions.iter() {
            for form in instruction.forms.iter() {
                for field in form.fields.iter() {
                    let Some(name) = field.name.clone() else {
                        continue;
                    };
                    if valid_field_uses.contains_key(&name) {
                        continue;
                    }
                    match field.merge_mode {
                        MergeMode::Uses => {
                            valid_field_uses.insert(
                                name.clone(),
                                FieldUses::Uses {
                                    name,
                                    patterns: HashSet::from([field.pattern.clone()]),
                                    len: field.pattern.len(),
                                },
                            );
                        }
                        MergeMode::VariableBits => {
                            valid_field_uses.insert(
                                name.clone(),
                                FieldUses::VariableBits {
                                    name,
                                    pattern: field.pattern.clone(),
                                },
                            );
                        }
                    }
                }
            }
        }
        Self { valid_field_uses }
    }
}

fn choose_random_bit<R: Rng>(rng: &mut R) -> Bit {
    let bit = rng.random_range(0..=1);
    if bit == 0 { Bit::Low } else { Bit::High }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa_specification::{ArchitecturalRegister, StackDirection, StackPointer};
    use rand::{SeedableRng, rngs::StdRng};

    fn test_isa() -> ISA {
        let register = ArchitecturalRegister {
            identifier: 0,
            identifier_width: 1,
            width: 1,
        };

        ISA {
            registers: vec![register],
            instructions: vec![],
            sp: StackPointer {
                register,
                stack_size: 0,
                direction: StackDirection::Downwards,
            },
            pc: register,
        }
    }

    fn manager(rng: StdRng) -> IsaOptimizationManager<'static, StdRng> {
        let isa = Box::leak(Box::new(test_isa()));
        IsaOptimizationManager {
            isa,
            candidates: vec![],
            rng,
        }
    }

    fn patterns(patterns: &[&str]) -> HashSet<BitPattern> {
        patterns
            .iter()
            .map(|pattern| BitPattern::parse(pattern))
            .collect()
    }

    fn pattern_string(pattern: &BitPattern) -> String {
        pattern
            .bits
            .iter()
            .map(|bit| match bit {
                Bit::Low => '0',
                Bit::High => '1',
                Bit::Var => 'x',
                Bit::Test => 't',
            })
            .collect()
    }

    fn assert_concrete(pattern: &BitPattern) {
        assert!(
            pattern
                .bits
                .iter()
                .all(|bit| matches!(bit, Bit::Low | Bit::High)),
            "expected a concrete pattern, got {}",
            pattern_string(pattern)
        );
    }

    fn assert_uncovered(pattern: &BitPattern, covered: &HashSet<BitPattern>) {
        assert!(
            !covered
                .iter()
                .any(|covered_pattern| covered_pattern.matches_bits(&pattern.bits)),
            "expected {} to be uncovered",
            pattern_string(pattern)
        );
    }

    fn variable_bits_field(pattern: &str) -> FieldUses {
        FieldUses::VariableBits {
            name: "field".to_string(),
            pattern: BitPattern::parse(pattern),
        }
    }

    fn uses_field(patterns: &[&str]) -> FieldUses {
        let len = patterns
            .first()
            .map(|pattern| pattern.len())
            .expect("Uses test helper requires at least one pattern");
        assert!(
            patterns.iter().all(|pattern| pattern.len() == len),
            "Uses test helper patterns must have the same length"
        );
        FieldUses::Uses {
            name: "field".to_string(),
            patterns: self::patterns(patterns),
            len,
        }
    }

    fn unwrap_variable_bits(field: FieldUses) -> BitPattern {
        let FieldUses::VariableBits { pattern, .. } = field else {
            panic!("expected VariableBits field");
        };
        pattern
    }

    fn unwrap_uses(field: FieldUses) -> HashSet<BitPattern> {
        let FieldUses::Uses { patterns, .. } = field else {
            panic!("expected Uses field");
        };
        patterns
    }

    fn candidate(fields: &[(&str, FieldUses)]) -> ISACandidate {
        ISACandidate {
            valid_field_uses: fields
                .iter()
                .map(|(name, field)| (name.to_string(), field.clone()))
                .collect(),
        }
    }

    #[test]
    fn mutate_updates_the_only_variable_bits_field() {
        let mut manager = manager(StdRng::seed_from_u64(0x6001));
        let original = candidate(&[("imm", variable_bits_field("0"))]);
        let mutated = manager.mutate(original);
        let field = mutated
            .valid_field_uses
            .get("imm")
            .expect("mutated candidate should keep imm field");

        assert_eq!(
            field,
            &FieldUses::VariableBits {
                name: "field".to_string(),
                pattern: BitPattern::parse("1")
            }
        );
    }

    #[test]
    fn mutate_updates_the_only_uses_field_and_preserves_len() {
        let mut manager = manager(StdRng::seed_from_u64(0x6002));
        let original = candidate(&[("opcode", uses_field(&["00"]))]);
        let mutated = manager.mutate(original);
        let field = mutated
            .valid_field_uses
            .get("opcode")
            .expect("mutated candidate should keep opcode field");
        let FieldUses::Uses { patterns, len, .. } = field else {
            panic!("expected Uses field");
        };

        assert_eq!(*len, 2);
        assert!(patterns.iter().all(|pattern| pattern.len() == *len));
        assert_ne!(patterns, &self::patterns(&["00"]));
    }

    #[test]
    fn mutate_preserves_unselected_fields() {
        let original = candidate(&[
            ("a", variable_bits_field("0")),
            ("b", variable_bits_field("1")),
        ]);

        for seed in 0..256 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let mutated = manager.mutate(original.clone());
            let changed: Vec<_> = original
                .valid_field_uses
                .iter()
                .filter(|(name, field)| mutated.valid_field_uses.get(*name) != Some(*field))
                .map(|(name, _)| name.as_str())
                .collect();

            assert_eq!(changed.len(), 1, "mutate should change exactly one field");
            for (name, field) in &original.valid_field_uses {
                if !changed.contains(&name.as_str()) {
                    assert_eq!(mutated.valid_field_uses.get(name), Some(field));
                }
            }
        }
    }

    #[test]
    fn mutate_keeps_all_candidate_field_names() {
        let original = candidate(&[
            ("imm", variable_bits_field("x")),
            ("opcode", uses_field(&["00", "11"])),
        ]);
        let mut manager = manager(StdRng::seed_from_u64(0x6003));
        let mutated = manager.mutate(original);

        assert!(mutated.valid_field_uses.contains_key("imm"));
        assert!(mutated.valid_field_uses.contains_key("opcode"));
        assert_eq!(mutated.valid_field_uses.len(), 2);
    }

    #[test]
    fn mutate_preserves_uses_length_metadata_when_that_field_is_selected() {
        let original = candidate(&[
            ("imm", variable_bits_field("1")),
            ("opcode", uses_field(&["00x"])),
        ]);
        let mut saw_opcode_mutation = false;

        for seed in 0..512 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let mutated = manager.mutate(original.clone());
            if mutated.valid_field_uses.get("opcode") != original.valid_field_uses.get("opcode") {
                let FieldUses::Uses { patterns, len, .. } = mutated
                    .valid_field_uses
                    .get("opcode")
                    .expect("opcode field should remain present")
                else {
                    panic!("expected Uses field");
                };

                assert_eq!(*len, 3);
                assert!(patterns.iter().all(|pattern| pattern.len() == *len));
                saw_opcode_mutation = true;
                break;
            }
        }

        assert!(saw_opcode_mutation, "expected some seed to mutate opcode");
    }

    #[test]
    #[should_panic(expected = "valid_field_uses should not be empty")]
    fn mutate_panics_for_empty_candidate() {
        let mut manager = manager(StdRng::seed_from_u64(0x6004));
        manager.mutate(ISACandidate {
            valid_field_uses: HashMap::new(),
        });
    }

    #[test]
    fn mutate_field_variable_bits_flips_low_to_high() {
        let mut manager = manager(StdRng::seed_from_u64(0x10));
        let mutated = unwrap_variable_bits(manager.mutate_field(variable_bits_field("0"), 1));

        assert_eq!(mutated, BitPattern::parse("1"));
    }

    #[test]
    fn mutate_field_variable_bits_flips_high_to_low() {
        let mut manager = manager(StdRng::seed_from_u64(0x11));
        let mutated = unwrap_variable_bits(manager.mutate_field(variable_bits_field("1"), 1));

        assert_eq!(mutated, BitPattern::parse("0"));
    }

    #[test]
    fn mutate_field_variable_bits_materializes_var_to_concrete_bit() {
        let mut manager = manager(StdRng::seed_from_u64(0x12));
        let mutated = unwrap_variable_bits(manager.mutate_field(variable_bits_field("x"), 1));

        assert_concrete(&mutated);
    }

    #[test]
    fn mutate_field_variable_bits_preserves_name_and_width() {
        let mut manager = manager(StdRng::seed_from_u64(0x13));
        let mutated = manager.mutate_field(variable_bits_field("101"), 3);
        let FieldUses::VariableBits { name, pattern } = mutated else {
            panic!("expected VariableBits field");
        };

        assert_eq!(name, "field");
        assert_eq!(pattern.len(), 3);
    }

    #[test]
    fn mutate_field_variable_bits_selects_bit_positions_roughly_uniformly() {
        let mut manager = manager(StdRng::seed_from_u64(0x14));
        let field = variable_bits_field("000");
        let sample_count = 6_000usize;
        let expected_count = sample_count / 3;
        let tolerance = expected_count / 5;
        let mut counts = [0usize; 3];

        for _ in 0..sample_count {
            let mutated = unwrap_variable_bits(manager.mutate_field(field.clone(), 3));
            let high_idx = mutated
                .bits
                .iter()
                .position(|bit| *bit == Bit::High)
                .expect("one Low bit should flip to High");
            counts[high_idx] += 1;
        }

        for count in counts {
            assert!(
                expected_count.abs_diff(count) <= tolerance,
                "expected count {count} to be within {tolerance} of {expected_count}"
            );
        }
    }

    #[test]
    fn mutate_field_variable_bits_materializes_var_values_roughly_uniformly() {
        let mut manager = manager(StdRng::seed_from_u64(0x15));
        let field = variable_bits_field("x");
        let sample_count = 4_000usize;
        let expected_count = sample_count / 2;
        let tolerance = expected_count / 5;
        let mut low_count = 0usize;
        let mut high_count = 0usize;

        for _ in 0..sample_count {
            let mutated = unwrap_variable_bits(manager.mutate_field(field.clone(), 1));
            match mutated.bits[0] {
                Bit::Low => low_count += 1,
                Bit::High => high_count += 1,
                other => panic!("expected concrete bit, got {other:?}"),
            }
        }

        assert!(expected_count.abs_diff(low_count) <= tolerance);
        assert!(expected_count.abs_diff(high_count) <= tolerance);
    }

    #[test]
    fn mutate_field_uses_specializes_selected_variable_pattern() {
        let mut manager = manager(StdRng::seed_from_u64(0x16));
        let mutated = unwrap_uses(manager.mutate_field(uses_field(&["x"]), 1));

        assert_eq!(mutated.len(), 1);
        assert!(
            mutated.contains(&BitPattern::parse("0")) || mutated.contains(&BitPattern::parse("1")),
            "expected x to specialize to either 0 or 1, got {mutated:?}"
        );
        assert!(!mutated.contains(&BitPattern::parse("x")));
    }

    #[test]
    fn mutate_field_uses_can_add_random_uncovered_pattern() {
        let mut added = false;

        for seed in 0..256 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let original = patterns(&["00x"]);
            let mutated = unwrap_uses(manager.mutate_field(
                FieldUses::Uses {
                    name: "field".to_string(),
                    patterns: original.clone(),
                    len: 3,
                },
                3,
            ));

            if mutated.len() > original.len() {
                let added_patterns: Vec<_> = mutated.difference(&original).collect();
                assert_eq!(added_patterns.len(), 1);
                assert_concrete(added_patterns[0]);
                assert_uncovered(added_patterns[0], &original);
                added = true;
                break;
            }
        }

        assert!(
            added,
            "expected some seeded mutation to add an uncovered pattern"
        );
    }

    #[test]
    fn mutate_field_uses_can_remove_selected_concrete_pattern() {
        let mut removed = false;

        for seed in 0..256 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["0", "1"]), 1));

            if mutated.len() == 1 {
                assert!(
                    mutated.contains(&BitPattern::parse("0"))
                        || mutated.contains(&BitPattern::parse("1"))
                );
                removed = true;
                break;
            }
        }

        assert!(
            removed,
            "expected some seeded mutation to remove a concrete pattern"
        );
    }

    #[test]
    fn mutate_field_uses_samples_existing_and_uncovered_buckets_by_frequency() {
        let mut manager = manager(StdRng::seed_from_u64(0x17));
        let field = uses_field(&["00x"]);
        let sample_count = 4_000usize;
        let expected_add_count = sample_count * 6 / 8;
        let expected_specialize_count = sample_count * 2 / 8;
        let tolerance = sample_count / 10;
        let mut add_count = 0usize;
        let mut specialize_count = 0usize;

        for _ in 0..sample_count {
            let mutated = unwrap_uses(manager.mutate_field(field.clone(), 3));
            if mutated.len() == 2 && mutated.contains(&BitPattern::parse("00x")) {
                add_count += 1;
            } else if mutated.len() == 1 && !mutated.contains(&BitPattern::parse("00x")) {
                specialize_count += 1;
            } else {
                panic!("unexpected Uses mutation outcome: {mutated:?}");
            }
        }

        assert!(
            expected_add_count.abs_diff(add_count) <= tolerance,
            "expected add count {add_count} to be within {tolerance} of {expected_add_count}"
        );
        assert!(
            expected_specialize_count.abs_diff(specialize_count) <= tolerance,
            "expected specialize count {specialize_count} to be within {tolerance} of {expected_specialize_count}"
        );
    }

    #[test]
    fn mutate_field_uses_merges_added_uncovered_pattern_with_existing_pattern() {
        let mut merged = false;

        for seed in 0..512 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["00"]), 2));

            if mutated.contains(&BitPattern::parse("0x")) {
                assert_eq!(
                    mutated,
                    patterns(&["0x"]),
                    "expected newly added adjacent pattern to merge with 00"
                );
                merged = true;
                break;
            }
        }

        assert!(
            merged,
            "expected some seeded mutation to add 01 and merge to 0x"
        );
    }

    #[test]
    fn mutate_field_uses_merges_specialized_pattern_with_neighbor() {
        let mut merged = false;

        for seed in 0..512 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["0x", "10"]), 2));

            if mutated == patterns(&["x0"]) {
                merged = true;
                break;
            }
        }

        assert!(
            merged,
            "expected some seeded mutation to specialize 0x to 00 and merge with 10 into x0"
        );
    }

    #[test]
    fn mutate_field_uses_applies_merge_until_fixed_point() {
        let mut merged_to_universal = false;

        for seed in 0..1024 {
            let mut manager = manager(StdRng::seed_from_u64(seed));
            let mutated = unwrap_uses(manager.mutate_field(uses_field(&["0x", "10"]), 2));

            if mutated == patterns(&["xx"]) {
                merged_to_universal = true;
                break;
            }
        }

        assert!(
            merged_to_universal,
            "expected some seeded mutation to add 11 and merge 0x, 10, 11 into xx"
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_returns_empty_for_empty_patterns() {
        let patterns = vec![];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_counts_concrete_patterns_as_one() {
        let patterns = vec![
            BitPattern::parse("00"),
            BitPattern::parse("01"),
            BitPattern::parse("10"),
            BitPattern::parse("11"),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![1, 1, 1, 1]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_uses_power_of_variable_bit_count() {
        let patterns = vec![
            BitPattern::parse("x"),
            BitPattern::parse("xx"),
            BitPattern::parse("x0x"),
            BitPattern::parse("xxxx"),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![2, 4, 4, 16]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_preserves_input_order() {
        let patterns = vec![
            BitPattern::parse("xxx"),
            BitPattern::parse("0"),
            BitPattern::parse("x0"),
            BitPattern::parse("xx00x"),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![8, 1, 2, 8]
        );
    }

    #[test]
    fn construct_bitpatterns_frequencies_counts_only_var_bits() {
        let patterns = vec![
            BitPattern::new(vec![Bit::Test, Bit::Low, Bit::High]),
            BitPattern::new(vec![Bit::Var, Bit::Test, Bit::Var]),
        ];

        assert_eq!(
            IsaOptimizationManager::<StdRng>::construct_bitpatterns_frequencies(&patterns),
            vec![1, 4]
        );
    }

    #[test]
    fn random_uncovered_pattern_only_returns_concrete_uncovered_patterns() {
        let covered = patterns(&["00x", "101", "11x"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x51a0));

        for _ in 0..256 {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_uncovered(&pattern, &covered);
        }
    }

    #[test]
    fn random_uncovered_pattern_samples_uncovered_patterns_uniformly() {
        let covered = patterns(&["00x"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x5150));
        let sample_count = 6_000usize;
        let expected_count = sample_count / 6;
        let tolerance = expected_count / 5;
        let mut counts = HashMap::new();

        for _ in 0..sample_count {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_uncovered(&pattern, &covered);
            *counts.entry(pattern_string(&pattern)).or_insert(0usize) += 1;
        }

        assert_eq!(counts.len(), 6, "expected to sample all uncovered patterns");
        for pattern in ["010", "011", "100", "101", "110", "111"] {
            let count = *counts.get(pattern).unwrap_or(&0);
            assert!(
                expected_count.abs_diff(count) <= tolerance,
                "expected {pattern} count {count} to be within {tolerance} of {expected_count}"
            );
        }
    }

    #[test]
    fn random_uncovered_pattern_samples_all_patterns_when_none_are_covered() {
        let covered = patterns(&[]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 2);
        let mut manager = manager(StdRng::seed_from_u64(0x0fee));
        let sample_count = 4_000usize;
        let expected_count = sample_count / 4;
        let tolerance = expected_count / 5;
        let mut counts = HashMap::new();

        for _ in 0..sample_count {
            let pattern = manager.random_pattern(&uncovered, 2);

            assert_concrete(&pattern);
            *counts.entry(pattern_string(&pattern)).or_insert(0usize) += 1;
        }

        assert_eq!(counts.len(), 4, "expected to sample all concrete patterns");
        for pattern in ["00", "01", "10", "11"] {
            let count = *counts.get(pattern).unwrap_or(&0);
            assert!(
                expected_count.abs_diff(count) <= tolerance,
                "expected {pattern} count {count} to be within {tolerance} of {expected_count}"
            );
        }
    }

    #[test]
    fn random_uncovered_pattern_handles_overlapping_covered_patterns() {
        let covered = patterns(&["0xx", "x0x", "110"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x0b1a));
        let mut sampled = HashSet::new();

        for _ in 0..256 {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_uncovered(&pattern, &covered);
            sampled.insert(pattern_string(&pattern));
        }

        assert_eq!(
            sampled,
            ["111".to_string()].into_iter().collect(),
            "expected only the sole uncovered pattern to be sampled"
        );
    }

    #[test]
    fn random_uncovered_pattern_repeatedly_returns_only_remaining_assignment() {
        let covered = patterns(&["0xx", "10x", "110"]);
        let uncovered = IsaOptimizationManager::<StdRng>::uncovered_patterns(&covered, 3);
        let mut manager = manager(StdRng::seed_from_u64(0x501e));

        for _ in 0..64 {
            let pattern = manager.random_pattern(&uncovered, 3);

            assert_concrete(&pattern);
            assert_eq!(pattern_string(&pattern), "111");
        }
    }
}
