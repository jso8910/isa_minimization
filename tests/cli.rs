use std::process::Command;

#[test]
fn binary_entrypoint_runs() {
    let output = Command::new(env!("CARGO_BIN_EXE_isa_minimization"))
        .output()
        .expect("binary should run");

    assert!(output.status.success());
    assert_eq!(output.stdout, b"Hello, world!\n");
    assert!(output.stderr.is_empty());
}
