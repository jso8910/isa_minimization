#[path = "../examples/arm32/isa.rs"]
mod arm32;

use std::collections::{HashMap, HashSet};

use isa_minimization::bit::BitPattern;
use isa_minimization::isa_optimization::IsaOptimizationManager;
use isa_minimization::isa_specification::{DecodedInstruction, FieldUses, ISA, StackDirection, StackPointer};
use rand::{SeedableRng, rngs::StdRng};

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
#[ignore = "runs the genetic ISA optimizer and prints progress"]
fn arm32_optimize_arraysum_smoke() {
    let isa = arm32_isa();
    let program = DecodedInstruction::decode_program("examples/matdet_stdlib.bin", &isa)
        .expect("arraysum ARM binary should decode");
    let mandatory_forms = HashMap::from([
        ("load_ops".to_string(), HashSet::new()),
        ("store_ops".to_string(), HashSet::new()),
        ("arithmetic_s0_reg_op2".to_string(), HashSet::new()),
        ("arithmetic_s0_imm_op2".to_string(), HashSet::new()),
        ("logical_s0_reg_op2".to_string(), HashSet::new()),
        ("logical_s0_imm_op2".to_string(), HashSet::new()),
        ("move_s0_imm_op2".to_string(), HashSet::new()),
        ("move_s0_reg_op2".to_string(), HashSet::new()),
        ("dproc_s1_reg_op2".to_string(), HashSet::new()),
        ("dproc_s1_imm_op2".to_string(), HashSet::new()),
    ]);
    // let unrestricted_forms = isa
    //     .instructions
    //     .iter()
    //     .filter(|instruction| instruction.name.starts_with("branch_ops"))
    //     .map(|instruction| {
    //         (
    //             instruction.name.clone(),
    //             instruction
    //                 .forms
    //                 .iter()
    //                 .map(|form| form.name.clone())
    //                 .collect::<HashSet<_>>(),
    //         )
    //     })
    //     .collect::<HashMap<_, _>>();

    let unrestricted_forms = HashMap::from([
        (
            "branch_ops_b".to_string(),
            HashSet::from(["base".to_string()]),
        ),
        (
            "branch_ops_bx".to_string(),
            HashSet::from(["base".to_string()]),
        ),
        (
            "branch_ops_block_tfr".to_string(),
            HashSet::from(["base".to_string()]),
        ),
        (
            "branch_ops_data_tfr".to_string(),
            HashSet::from([
                "register_offset".to_string(),
                "register_offset_pc_base".to_string(),
                "immediate_offset".to_string(),
                "immediate_offset_pc_base".to_string(),
            ]),
        ),
        (
            // Instructions of the form ldr rn, [pc, #imm12] must be unrestricted, because they are
            // used to access values from literal pools.
            "load_ops".to_string(),
            HashSet::from(["immediate_offset_pc_base".to_string()]),
        ),
    ]);

    let mut manager = IsaOptimizationManager::new(
        &isa,
        StdRng::seed_from_u64(0xA32),
        mandatory_forms,
        unrestricted_forms,
        "examples/arm32_core_syn.v",
        "examples/NangateOpenCellLibrary_typical.lib",
        program,
        50,
        4,
        0.5,
        0.5,
        0.05,
        0.01,
    )
        .with_fixed_field_uses(HashMap::from([(
            "op2_shift_type".to_string(),
            FieldUses::Uses {
                name: "op2_shift_type".to_string(),
                patterns: HashSet::from([BitPattern::parse("xx")]),
                len: 2,
            },
        )]));

    manager.optimize();
}
