#[path = "../examples/arm32/isa.rs"]
mod arm32;

use std::{collections::HashSet, fs, path::Path};

use isa_minimization::{
    greenthumb_restrictions::{GreenthumbRestrictionOptions, GreenthumbRestrictionSet},
    isa_optimization::ISACandidate,
    isa_specification::{ISA, StackDirection, StackPointer},
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
    }
}

#[test]
fn arm32_broad_candidate_emits_default_deny_without_branch_or_multiply_classes() {
    let isa = arm32_isa();
    let candidate = ISACandidate::max_isa(&isa);
    let restrictions = GreenthumbRestrictionSet::from_candidate(
        &isa,
        &candidate,
        &GreenthumbRestrictionOptions {
            exclude_branches: true,
            exclude_multiplies: true,
            exclude_extension_ops: true,
        },
    );

    assert!(!restrictions.allow_patterns.is_empty());
    for pattern in &restrictions.allow_patterns {
        assert_eq!(pattern.len(), 32);
        assert!(pattern.chars().all(|ch| matches!(ch, '0' | '1' | 'x')));
        assert!(
            !pattern[4..].starts_with("101"),
            "branch encoding leaked into allow pattern: {pattern}"
        );
    }

    let racket = restrictions.to_racket_default_deny();
    assert!(racket.starts_with("((default deny)\n"));
    assert!(racket.contains("(allow "));
}

#[test]
fn generated_restriction_superopt_fixtures_are_well_formed() {
    let root = Path::new("greenthumb/arm/restriction-superopt/generated");
    let mut cases = HashSet::new();

    for entry in fs::read_dir(root).expect("generated restriction-superopt fixtures should exist") {
        let path = entry.expect("fixture dir entry should be readable").path();
        if !path.is_dir() {
            continue;
        }

        cases.insert(
            path.file_name()
                .expect("case dir has a name")
                .to_string_lossy()
                .to_string(),
        );

        for file_name in ["input.s", "input.s.info", "restrict.rkt", "expected.rkt"] {
            assert!(
                path.join(file_name).is_file(),
                "missing {} in {}",
                file_name,
                path.display()
            );
        }

        let restrict = fs::read_to_string(path.join("restrict.rkt"))
            .expect("restriction file should be readable");
        assert!(restrict.starts_with("((default deny)\n"));
        for line in restrict.lines() {
            if !(line.contains("(allow ") || line.contains("(deny ")) {
                continue;
            }
            let pattern = line
                .split('"')
                .nth(1)
                .expect("restriction line should contain a quoted pattern");
            assert_eq!(pattern.len(), 32, "{}: {pattern}", path.display());
            assert!(
                pattern.chars().all(|ch| matches!(ch, '0' | '1' | 'x')),
                "{}: {pattern}",
                path.display()
            );
        }

        let expected =
            fs::read_to_string(path.join("expected.rkt")).expect("metadata should be readable");
        assert!(expected.contains("(workers 4)"));
    }

    assert_eq!(cases.len(), 32);
    assert!(cases.contains("23_word_load_from_bytes"));
    assert!(cases.contains("24_word_store_from_bytes"));
    assert!(cases.contains("29_stack_scratch_store"));
    assert!(cases.contains("31_pc_read_middle_of_independent_sequence"));
    assert!(cases.contains("32_pop_pc_without_pop"));
}
