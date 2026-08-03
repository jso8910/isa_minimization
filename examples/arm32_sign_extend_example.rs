#[allow(dead_code)]
#[path = "arm32.rs"]
mod arm32;

use std::time::{Duration, Instant};

use isa_minimization::instruction_semantics::{
    Effect, Expr, Register, extract, fixed_register, read_fixed_register, sign_extend,
};
use isa_minimization::isa_specification::{DecodedInstruction, ISA, StackDirection, StackPointer};
use isa_minimization::semantic_matching::{
    BddEquality, BddManager, evaluate_expr, instruction_seq_to_effects,
};
use isa_minimization::superoptimization::Program;

const ASR_R1_R0_31: &str = "11100001101000000001111111000000";
const ARM_REGISTER_IDENTIFIER_WIDTH: u16 = 4;
const DEFAULT_BENCH_ITERATIONS: usize = 10;

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
        pc_to_instruction_index: arm32::pc_to_instruction_index,
        instruction_index_to_pc: arm32::instruction_index_to_pc,
    }
}

fn fixed_gpr(register: u8) -> Expr {
    fixed_register(Register(register), ARM_REGISTER_IDENTIFIER_WIDTH)
}

fn read_gpr(register: u8) -> Expr {
    read_fixed_register(Register(register), ARM_REGISTER_IDENTIFIER_WIDTH, 32)
}

fn bench_iterations() -> usize {
    std::env::args()
        .nth(1)
        .map(|arg| {
            let iterations = arg
                .parse()
                .expect("optional benchmark iteration count must be a positive integer");
            assert!(
                iterations > 0,
                "optional benchmark iteration count must be greater than zero"
            );
            iterations
        })
        .unwrap_or(DEFAULT_BENCH_ITERATIONS)
}

fn bench_bdd_solver(isa: &ISA, left: &Expr, right: &Expr, iterations: usize) -> Duration {
    let start = Instant::now();

    for _ in 0..iterations {
        let mut bdd_manager = BddManager::from_exprs(left.clone(), right.clone(), isa);
        let result = bdd_manager
            .compare()
            .expect("BDD benchmark comparison should allocate");
        assert_eq!(result, BddEquality::Equal);
    }

    start.elapsed()
}

fn main() {
    let iterations = bench_iterations();
    let isa = arm32_isa();
    let program =
        DecodedInstruction::decode_program_str(ASR_R1_R0_31, &isa).expect("decode ASR program");
    let program = Program::from_instructions(program, 1);
    let effects = instruction_seq_to_effects(&program, &isa);
    let r1 = fixed_gpr(1);

    let r1_value = effects
        .iter()
        .find_map(|effect| match effect {
            Effect::WriteRegister {
                register, value, ..
            } if *register == r1 => Some(value.clone().canonicalize()),
            _ => None,
        })
        .expect("program should write r1");

    let r0 = read_gpr(0);
    let high_half_of_r0_sign_extend = extract(sign_extend(r0, 64), 63, 32).canonicalize();
    let mut bdd_manager =
        BddManager::from_exprs(r1_value.clone(), high_half_of_r0_sign_extend.clone(), &isa);
    let bdd_result = bdd_manager
        .compare()
        .expect("BDD comparison should allocate");
    let bench_elapsed = bench_bdd_solver(&isa, &r1_value, &high_half_of_r0_sign_extend, iterations);
    let seconds_per_iteration = bench_elapsed.as_secs_f64() / iterations as f64;

    println!("Program:");
    println!("  ASR R1, R0, #31");
    println!();
    println!("Canonical expression for value written to r1:");
    println!("{:#?}", r1_value);
    println!();
    println!("Canonical expression for extract(sign_extend(r0, 64), 63, 32):");
    println!("{:#?}", high_half_of_r0_sign_extend);
    println!();
    println!("BDD equivalence result:");
    match bdd_result {
        BddEquality::Equal => {
            println!("  Equal");
        }
        BddEquality::Unequal(state) => {
            println!("  Unequal");
            println!("  Counterexample state: {state:#?}");
            println!(
                "  r1 expression evaluates to: {:#?}",
                evaluate_expr(&r1_value, &state)
            );
            println!(
                "  high-half sign-extension expression evaluates to: {:#?}",
                evaluate_expr(&high_half_of_r0_sign_extend, &state)
            );
        }
    }
    println!();
    println!("BDD solver benchmark:");
    println!("  iterations: {iterations}");
    println!("  total: {:.6}s", bench_elapsed.as_secs_f64());
    println!(
        "  time per iteration: {:.6}ms",
        seconds_per_iteration * 1_000.0
    );
}
