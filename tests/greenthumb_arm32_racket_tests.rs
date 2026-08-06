use std::process::Command;

fn run_racket_test(path: &str, args: &[&str]) {
    let command = format!(
        "source greenthumb/source.sh && racket {} {}",
        shell_quote(path),
        args.iter()
            .map(|arg| shell_quote(arg))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let output = Command::new("zsh")
        .arg("-lc")
        .arg(command)
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .unwrap_or_else(|err| panic!("failed to run {path}: {err}"));

    assert!(
        output.status.success(),
        "{} failed\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        path,
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

#[test]
fn greenthumb_arm32_layer1_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-arm32-layer1.rkt", &[]);
}

#[test]
fn greenthumb_arm32_layer2_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-arm32-layer2.rkt", &[]);
}

#[test]
fn greenthumb_arm32_layer3_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-arm32-layer3.rkt", &[]);
}

#[test]
fn greenthumb_arm32_rust_parity_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-arm32-rust-parity.rkt", &[]);
}

#[test]
fn greenthumb_arm32_block_lowering_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-block-lowering.rkt", &[]);
}

#[test]
fn greenthumb_arm32_random_encoding_racket_tests_pass() {
    run_racket_test(
        "greenthumb/arm/tests/test-random-encodings.rkt",
        &["--seed", "0", "--progress", "0"],
    );
}

#[test]
#[ignore = "symbolic/enumerative synthesis regression test; not part of default stochastic coverage"]
fn greenthumb_arm32_regression_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-regression.rkt", &[]);
}

#[test]
fn greenthumb_arm32_restriction_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-restrictions.rkt", &[]);
}

#[test]
fn greenthumb_arm32_simulator_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-simulator.rkt", &[]);
}

#[test]
#[ignore = "solver-heavy counterexample test; not part of default stochastic coverage"]
fn greenthumb_arm32_solver_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-solver.rkt", &[]);
}

#[test]
fn greenthumb_arm32_stack_scratch_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-stack-scratch.rkt", &[]);
}

#[test]
fn greenthumb_arm32_stochastic_flags_racket_tests_pass() {
    run_racket_test("greenthumb/arm/tests/test-stochastic-flags.rkt", &[]);
}
