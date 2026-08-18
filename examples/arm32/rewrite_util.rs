use std::{
    collections::{HashMap, HashSet}, fs::{self, File}, path::PathBuf, process::{Command, Stdio},
};

use colored::*;
use glob::{glob_with, MatchOptions};
use isa_minimization::{isa_specification::ArchitecturalRegister, program_rewrite::{LabelAllocator, ProgramRewriteUtil}};

struct FileLocation {
    pub file: PathBuf,
    pub line_num: usize,
}

pub struct Arm32Rewrite {
    label_allocator: LabelAllocator,
    stdlib_source: PathBuf,
    labels: HashMap<String, FileLocation>,
    workdir: PathBuf,
}

impl Arm32Rewrite {
    pub fn new(stdlib_source: impl Into<PathBuf>, workdir: impl Into<PathBuf>) -> Self {
        Self {
            label_allocator: LabelAllocator::new("tailor"),
            stdlib_source: stdlib_source.into(),
            labels: HashMap::new(),
            workdir: workdir.into(),
        }
    }
}

impl ProgramRewriteUtil for Arm32Rewrite {
    fn workdir(&self) -> &PathBuf {
        &self.workdir
    }

    fn label_allocator(&mut self) -> &mut LabelAllocator {
        &mut self.label_allocator
    }

    fn library_files(&self) -> Vec<PathBuf> {
        println!("{}", "Building newlib".green());
        // First, we need to apply the patch to newlib
        let patch_path = self.workdir.join("newlib-no-mode-stack-init.patch");
        let newlib_dir = self.workdir.join("newlib");

        let patch_file = match File::open(&patch_path) {
            Ok(file) => file,
            Err(e) => {
                panic!(
                    "Failed to open patch file at {}: {}",
                    patch_path.to_string_lossy(),
                    e
                );
            }
        };

        let status = Command::new("patch")
            .arg("--forward")
            .arg("--silent")
            .arg("-d")
            .arg(newlib_dir)
            .arg("-p1")
            .stdin(Stdio::from(patch_file))
            .stdout(Stdio::null())
            .status()
            .expect("Failed to execute the patch process");

        // Status == 1 means a patch was skipped. Status > 1 means an error
        if status.code().unwrap() > 1 {
            panic!("Patch command failed with exit code: {}", status);
        }

        // Now, we want to build newlib
        let newlib_build_script = self.workdir.join("newlib-build.sh");
        let newlib_dir = self.workdir.join("newlib");
        let newlib_build_dir = self.workdir.join("build-newlib");
        let status = Command::new(newlib_build_script)
            .arg(&newlib_dir)
            .arg(&newlib_build_dir)
            .stdout(Stdio::null())
            .status()
            .expect("Failed to execute newlib build script!");

        if !status.success() {
            panic!("Newlib build command failed with exit code: {}", status);
        }

        // Finally, we want to collect all assembly files in the newlib build directory
        // We can do this with a glob *.s search
        let options = MatchOptions {
            case_sensitive: true,
            require_literal_separator: true,
            // Hidden files will be matched
            require_literal_leading_dot: false,
        };

        let mut library_files = vec![];
        for entry in glob_with(
            format!(
                "{}/**/*.s",
                newlib_build_dir
                    .into_os_string()
                    .into_string()
                    .expect("Could not convert path to string!")
            )
            .as_str(),
            options,
        )
        .expect("Glob pattern for *.s failed!")
        {
            if let Ok(path) = entry {
                library_files.push(path);
            }
        }

        println!("{}", "Newlib successfully built!".green());

        library_files
    }

    /// Compiles a program to workdir/out/main.s using build_script
    fn compile_program_to_asm(&self, mut build_script: Command) -> PathBuf {
        // Run compile-program.sh script
        let status = build_script
            .arg(&self.workdir)
            .stdout(Stdio::null())
            .status()
            .expect("Failed to execute C program build script!");

        if !status.success() {
            panic!(
                "Program compilation script failed with exit code: {}",
                status
            );
        }

        self.workdir.join("out").join("main.s")
    }

    fn asm_preproc(&mut self, assembly_path: &PathBuf, library_files: &Vec<PathBuf>) {
        todo!()
    }

    fn write_live_out_info(
        &self,
        live_out_regs: &std::collections::HashSet<
            isa_minimization::isa_specification::ArchitecturalRegister,
        >,
        info_file: &PathBuf,
    ) {
        let flags_are_live = live_out_regs
            .iter()
            .any(|register| (16..=19).contains(&register.identifier));

        let mut live_out_regs = live_out_regs
            .iter()
            .filter_map(|register| {
                if register.identifier <= 15 {
                    Some(register.identifier)
                } else if (16..=19).contains(&register.identifier) {
                    None
                } else {
                    panic!(
                        "Unsupported ARM live-out register identifier: {}",
                        register.identifier
                    );
                }
            })
            .collect::<Vec<_>>();
        live_out_regs.sort_unstable();
        live_out_regs.dedup();

        let mut live_out_tokens = live_out_regs
            .iter()
            .map(|register| register.to_string())
            .collect::<Vec<_>>();
        if flags_are_live {
            live_out_tokens.push("flag".to_string());
        }

        let live_out_info = live_out_tokens.join(",");

        if let Some(parent) = info_file.parent() {
            fs::create_dir_all(parent).unwrap_or_else(|e| {
                panic!(
                    "Failed to create info file parent directory {}: {}",
                    parent.to_string_lossy(),
                    e
                )
            });
        }

        fs::write(info_file, format!("{live_out_info}\n")).unwrap_or_else(|e| {
            panic!(
                "Failed to write live-out info to {}: {}",
                info_file.to_string_lossy(),
                e
            )
        });
    }

    fn scratch_replacement(
        &mut self,
        instruction: &isa_minimization::isa_specification::DecodedInstruction,
        candidate: &isa_minimization::isa_optimization::ISACandidate,
        scratchable_regs: &HashSet<ArchitecturalRegister>
    ) -> Option<String> {
        match (instruction.name.as_str(), instruction.form.name.as_str()) {
            ("multiply_ops_mul", "base") => {},
            ("multiply_ops_mull", "base") => {},
            _ => return None
        }
        return None
    }

    fn replace_assembly(
        &self,
        basic_block: &isa_minimization::program_analysis::BasicBlock,
        rewrite: String,
        assembly_path: &PathBuf,
    ) {
        todo!()
    }

    fn replace_assembly_line(&self, line_num: usize, rewrite: String, assembly_path: &PathBuf) {
        todo!()
    }

    fn assembly_postprocess(&self, assembly_path: &PathBuf) {
        todo!()
    }

    fn assemble_and_link(&self, program_asm: &PathBuf, library_files: &Vec<PathBuf>) -> PathBuf {
        todo!()
    }

    fn read_elf(
        &self,
        elf_file: &PathBuf,
    ) -> Vec<isa_minimization::isa_specification::DecodedInstruction> {
        todo!()
    }
}
