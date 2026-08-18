#[allow(dead_code, unused_variables)]
#[path = "../examples/arm32/rewrite_util.rs"]
mod rewrite_util;

use std::{
    collections::{BTreeSet, HashSet},
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use isa_minimization::{
    isa_specification::ArchitecturalRegister, program_rewrite::ProgramRewriteUtil,
};
use rewrite_util::Arm32Rewrite;

#[test]
fn compile_program_to_asm_runs_build_script_and_returns_main_assembly() {
    if !command_available("clang") || !command_available("arm-none-eabi-readelf") {
        eprintln!("skipping test: clang and arm-none-eabi-readelf are required");
        return;
    }

    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let temp_root = temp_dir("arm32-compile-program");
    let source_dir = temp_root.join("source");
    let workdir = temp_root.join("workdir");
    fs::create_dir_all(&source_dir).expect("create source dir");
    fs::create_dir_all(&workdir).expect("create workdir");

    let source_file = source_dir.join("input.c");
    fs::write(&source_file, "int main(void) { return 7; }\n").expect("write source file");

    let rewrite = Arm32Rewrite::new(repo_root.join("examples/arm32/newlib"), &workdir);
    let mut build_script = Command::new(repo_root.join("examples/arm32/compile-program.sh"));
    build_script.arg(&source_file);

    let assembly_path = rewrite.compile_program_to_asm(build_script);
    let object_path = workdir.join("out/main.o");

    assert_eq!(assembly_path, workdir.join("out/main.s"));
    assert!(
        assembly_path.is_file(),
        "expected assembly at {assembly_path:?}"
    );
    assert!(
        object_path.is_file(),
        "expected object file at {object_path:?}"
    );

    let assembly = fs::read_to_string(&assembly_path).expect("read generated assembly");
    assert!(assembly.contains(".cpu\tarm7tdmi"));
    assert!(assembly.contains("main:"));

    let readelf = Command::new("arm-none-eabi-readelf")
        .arg("-h")
        .arg(&object_path)
        .output()
        .expect("run readelf on generated object");
    assert!(
        readelf.status.success(),
        "readelf failed with status {}\nstderr:\n{}",
        readelf.status,
        String::from_utf8_lossy(&readelf.stderr)
    );

    let readelf_stdout = String::from_utf8_lossy(&readelf.stdout);
    assert!(readelf_stdout.contains("Type:                              REL"));
    assert!(readelf_stdout.contains("Machine:                           ARM"));
}

#[test]
fn write_live_out_info_writes_sorted_greenthumb_register_list_with_flag_token() {
    let temp_root = temp_dir("arm32-live-out-info");
    let info_file = temp_root.join("nested/input.s.info");
    let rewrite = Arm32Rewrite::new(temp_root.join("newlib"), &temp_root);
    let live_out_regs = HashSet::from([
        arch_register(10),
        arch_register(0),
        arch_register(3),
        arch_register(1),
        flag_register(18),
        flag_register(16),
    ]);

    rewrite.write_live_out_info(&live_out_regs, &info_file);

    let info = fs::read_to_string(&info_file).expect("read live-out info");
    assert_eq!(info, "0,1,3,10,flag\n");
}

#[test]
#[ignore = "patches and builds newlib; requires the arm-none-eabi toolchain"]
fn library_files_returns_all_newlib_build_assembly_outputs() {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let rewrite = Arm32Rewrite::new(
        repo_root.join("examples/arm32/newlib"),
        repo_root.join("examples/arm32"),
    );

    let library_files = rewrite.library_files();
    let expected_files = find_assembly_files(&repo_root.join("examples/arm32/build-newlib"));

    assert!(
        library_files.len() > 10,
        "expected more than 10 generated assembly files, got {}",
        library_files.len()
    );

    assert_eq!(
        paths_as_relative_set(&repo_root, &library_files),
        paths_as_relative_set(&repo_root, &expected_files)
    );
}

fn find_assembly_files(build_dir: &Path) -> Vec<PathBuf> {
    let output = Command::new("find")
        .arg(build_dir)
        .arg("-type")
        .arg("f")
        .arg("-name")
        .arg("*.s")
        .arg("-print0")
        .output()
        .expect("failed to list generated assembly files with find");

    assert!(
        output.status.success(),
        "find failed with status {}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    output
        .stdout
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
        .map(|path| PathBuf::from(String::from_utf8_lossy(path).into_owned()))
        .collect()
}

fn paths_as_relative_set(repo_root: &Path, paths: &[PathBuf]) -> BTreeSet<PathBuf> {
    paths
        .iter()
        .map(|path| path.strip_prefix(repo_root).unwrap_or(path).to_path_buf())
        .collect()
}

fn command_available(command: &str) -> bool {
    Command::new(command)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}

fn temp_dir(prefix: &str) -> PathBuf {
    let mut path = env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    path.push(format!("{prefix}-{}-{nanos}", std::process::id()));
    fs::create_dir_all(&path).expect("create temp dir");
    path
}

fn arch_register(identifier: u8) -> ArchitecturalRegister {
    ArchitecturalRegister {
        identifier,
        identifier_width: 4,
        width: 32,
    }
}

fn flag_register(identifier: u8) -> ArchitecturalRegister {
    ArchitecturalRegister {
        identifier,
        identifier_width: 5,
        width: 1,
    }
}
