use std::{collections::HashSet, env, ffi::OsString, fs, path::PathBuf, process::Command};

use crate::{
    constants::{
        GREENTHUMB_CANDIDATE_SIZE, GREENTHUMB_CORES, GREENTHUMB_REWRITE_MODE_FLAG,
        GREENTHUMB_SEARCH_MODE_FLAG, GREENTHUMB_TIMEOUT_SECONDS,
    },
    greenthumb_restrictions::{GreenthumbRestrictionOptions, GreenthumbRestrictionSet},
    isa_optimization::ISACandidate,
    isa_specification::{ArchitecturalRegister, DecodedInstruction, ISA, StackDirection},
    program_analysis::{BasicBlock, ProgramAnalysis},
};

pub trait ProgramRewriteUtil {
    fn workdir(&self) -> &PathBuf;

    /// Traits cannot require concrete fields, so implementers expose their allocator here.
    fn label_allocator(&mut self) -> &mut LabelAllocator;

    /// Returns paths to all library (eg C standard library, startup code, etc.) assembly .s files
    fn library_files(&self) -> Vec<PathBuf>;

    /// Compiles a program to an assembly file using a build script. The assembly file should be
    /// outputted at workdir()/out/main.s, and the obj/elf file should be at workdir()/out/main.o.
    /// The command will be called by adding a final argument at the end of the command, workdir(),
    /// so there should be room for that command line argument to decide where the files end up.
    fn compile_program_to_asm(&self, build_script: Command) -> PathBuf;

    /// Pre-processing to modify the assembly file for analysis. For example, you may
    /// want to add labels before every line so you can more easily identify what line and file an
    /// instruction came from.
    /// This function can be run multiple times, so this should be taken into account. If you add
    /// labels before each line, for example, you will likely want to have an easy way to remove all
    /// of these labels at the start of this function.
    fn asm_preproc(&mut self, assembly_path: &PathBuf, library_files: &Vec<PathBuf>);

    /// Write live-out register info in the format which Greenthumb is expecting (ISA specific)
    fn write_live_out_info(
        &self,
        live_out_regs: &HashSet<ArchitecturalRegister>,
        info_file: &PathBuf,
    );

    /// Some instructions cannot be fixed by straight-line replacements. For example, MUL, MULL,
    /// MLA, etc. So, this function takes, as input, any instruction, and outputs an assembly string
    /// which contains whatever loops or control flow is necessary to replicate an instruction.
    fn scratch_replacement(
        &mut self,
        instruction: &DecodedInstruction,
        candidate: &ISACandidate,
        scratchable_regs: &HashSet<ArchitecturalRegister>
    ) -> Option<String>;

    /// Replaces a basic block with its rewrite. The rewrite should
    /// contain valid assembly syntax outputted by Greenthumb.
    fn replace_assembly(&self, basic_block: &BasicBlock, rewrite: String, assembly_path: &PathBuf);

    /// Replaces a single line of assembly with a valid rewrite
    fn replace_assembly_line(&self, line_num: usize, rewrite: String, assembly_path: &PathBuf);

    /// Post-processing run on assembly file before final compilation. For example, in ARM,
    /// if your pre-processing in `compile_program` involves changing all ldr, rd, =value
    /// pseudo-instructions to static literal pool instructions, you might want to check in the
    /// post-processing step if there is a legal immediate move you can replace the memory access
    /// with.
    fn assembly_postprocess(&self, assembly_path: &PathBuf);

    /// Assembles and links the main program and library files, returning the resulting final ELF file.
    fn assemble_and_link(
        &self,
        program_asm: &PathBuf,
        library_files: &Vec<PathBuf>,
    ) -> PathBuf;

    /// Reads ELF file to Vec<DecodedInstruction>
    fn read_elf(&self, elf_file: &PathBuf) -> Vec<DecodedInstruction>;
}

/// Compiles and rewrites a program for a given ISA modification, outputting the final ELF file.
/// 
/// # Arguments
/// * `build_script` - A partially formed Command for a build script which takes one additional
///   argument (the workdir where the files will be outputted). This script should place an assembly
///   file in the location expected by your implementation of `compile_program_to_asm`, or otherwise
///   communicate where its file is to that function.
/// * `candidate` - the ISA candidate which the program is to be rewritten under.
/// * `isa` - the base ISA
/// * `rewrite_util` - Your implementation of the ISA-specific functions needed to compile, rewrite,
///   etc.
pub fn rewrite_program<'a, T: ProgramRewriteUtil>(
    build_script: Command,
    candidate: ISACandidate,
    isa: &'a ISA,
    mut rewrite_util: T,
) -> PathBuf {
    let library_files = rewrite_util.library_files();
    let assembly_path = rewrite_util.compile_program_to_asm(build_script);

    rewrite_util.asm_preproc(&assembly_path, &library_files);

    let mut elf_file_prerewrite =
        rewrite_util.assemble_and_link(&assembly_path, &library_files);
    let mut program = rewrite_util.read_elf(&elf_file_prerewrite);

    // Scratch replacements can be recursive, potentially, so we want to keep running until there
    // are no longer any relevant scratch replacements.
    loop {
        // Scratch replacements can expand to assembly which itself needs a scratch replacement, so
        // keep assembling and decoding until the current program has no scratchable instructions.
        let mut scratch_analysis =
            ProgramAnalysis::from_program_split_every_instruction(program.clone(), isa);
        scratch_analysis.compute_liveliness();

        let mut replacements = Vec::new();
        for block in scratch_analysis.program.iter() {
            let instruction = block
                .instructions
                .first()
                .expect("instruction-split analysis should produce non-empty blocks");

            if candidate.supports_instruction(instruction) {
                continue;
            }

            let scratchable_regs = isa
                .registers
                .iter()
                .filter(|register| !block.live_out_regs.contains(register))
                .cloned()
                .collect();
            if let Some(rewrite) =
                rewrite_util.scratch_replacement(instruction, &candidate, &scratchable_regs)
            {
                replacements.push((instruction.assembly_line, rewrite));
            }
        }

        if replacements.is_empty() {
            break;
        }

        // Apply from the end of the file upward so multi-line replacements do not invalidate the
        // assembly_line values decoded for instructions earlier in this pass.
        replacements.sort_unstable_by(|(left_line, _), (right_line, _)| right_line.cmp(left_line));

        for (line_num, rewrite) in replacements {
            rewrite_util.replace_assembly_line(line_num, rewrite, &assembly_path);
        }

        // Re-run preprocessing so newly inserted scratch assembly receives line labels before the
        // next decode pass.
        rewrite_util.asm_preproc(&assembly_path, &library_files);
        elf_file_prerewrite =
            rewrite_util.assemble_and_link(&assembly_path, &library_files);
        program = rewrite_util.read_elf(&elf_file_prerewrite);
    }

    let mut program_analysis = ProgramAnalysis::from_program(program, isa);
    program_analysis.compute_liveliness();

    let assembly_lines = fs::read_to_string(&assembly_path)
        .unwrap_or_else(|e| panic!("{e}"))
        .lines()
        .map(str::to_string)
        .collect::<Vec<_>>();

    for block in program_analysis.program {
        // Static instructions may not be rewritten so we skip them
        if block
            .instructions
            .iter()
            .any(|instr| instr.static_instruction)
        {
            // If all is correct, this block should be of length 1
            assert_eq!(block.instructions.len(), 1);

            // The block should also not need a rewrite
            assert!(block
                .instructions
                .iter()
                .all(|instr| candidate.supports_instruction(instr)));

            continue;
        }

        let needs_rewrite = block
            .instructions
            .iter()
            .any(|instr| !candidate.supports_instruction(instr));

        if !needs_rewrite {
            continue;
        }

        let case_dir = rewrite_util.workdir().join(format!("block_{}", block.start_instruction_idx));
        let input_s = case_dir.join("input.s");
        let info = case_dir.join("input.s.info");
        let restrict = case_dir.join("restrict.rkt");
        let output_dir = case_dir.join("out");

        fs::create_dir_all(&case_dir)
            .unwrap_or_else(|err| panic!("failed to create rewrite case dir {case_dir:?}: {err}"));

        let block_asm = block
            .instructions
            .iter()
            .map(|instr| assembly_lines[instr.assembly_line].as_str())
            .collect::<Vec<_>>()
            .join("\n");

        fs::write(&input_s, format!("{block_asm}\n")).unwrap_or_else(|e| panic!("{e}"));

        rewrite_util.write_live_out_info(&block.live_out_regs, &info);

        let restrictions = GreenthumbRestrictionSet::from_candidate(
            isa,
            &candidate,
            &GreenthumbRestrictionOptions {
                exclude_branches: true,
                ..Default::default()
            },
        );
        fs::write(&restrict, restrictions.to_racket_default_deny())
            .unwrap_or_else(|err| panic!("failed to write restriction file {restrict:?}: {err}"));

        let rewrite_path = run_greenthumb(isa, &input_s, &restrict, &output_dir);
        let rewrite = fs::read_to_string(&rewrite_path)
            .unwrap_or_else(|err| panic!("failed to read rewrite {rewrite_path:?}: {err}"));

        rewrite_util.replace_assembly(&block, rewrite, &assembly_path);
    }

    rewrite_util.assembly_postprocess(&assembly_path);

    rewrite_util.assemble_and_link(&assembly_path, &library_files)
}

pub fn run_greenthumb(
    isa: &ISA,
    input_s: &PathBuf,
    restrict: &PathBuf,
    output_dir: &PathBuf,
) -> PathBuf {
    fs::create_dir_all(output_dir).unwrap_or_else(|err| {
        panic!("failed to create GreenThumb output dir {output_dir:?}: {err}")
    });

    let input_s = input_s
        .canonicalize()
        .unwrap_or_else(|err| panic!("failed to resolve GreenThumb input {input_s:?}: {err}"));
    let restrict = restrict.canonicalize().unwrap_or_else(|err| {
        panic!("failed to resolve GreenThumb restriction file {restrict:?}: {err}")
    });
    let output_dir = output_dir.canonicalize().unwrap_or_else(|err| {
        panic!("failed to resolve GreenThumb output dir {output_dir:?}: {err}")
    });

    let stack_direction = match isa.sp.direction {
        StackDirection::Upwards => "upwards",
        StackDirection::Downwards => "downwards",
    };

    let output = Command::new("racket")
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .env("PATH", greenthumb_path())
        .arg("greenthumb/arm/optimize.rkt")
        .arg(GREENTHUMB_SEARCH_MODE_FLAG)
        .arg(GREENTHUMB_REWRITE_MODE_FLAG)
        .arg("--solver")
        .arg("z3")
        .arg("-c")
        .arg(GREENTHUMB_CORES.to_string())
        .arg("-t")
        .arg(GREENTHUMB_TIMEOUT_SECONDS.to_string())
        .arg("-n")
        .arg(GREENTHUMB_CANDIDATE_SIZE.to_string())
        .arg("-d")
        .arg(&output_dir)
        .arg("--restrict")
        .arg(&restrict)
        .arg("--stack-pointer-reg")
        .arg(isa.sp.register.identifier.to_string())
        .arg("--stack-scratch-size")
        .arg(isa.sp.stack_size.to_string())
        .arg("--stack-direction")
        .arg(stack_direction)
        .arg(&input_s)
        .output()
        .unwrap_or_else(|err| panic!("failed to run GreenThumb optimizer: {err}"));

    if !output.status.success() {
        panic!(
            "GreenThumb optimizer failed with status {}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let best_s = output_dir.join("best.s");
    if !best_s.exists() {
        panic!(
            "GreenThumb optimizer completed but did not produce {best_s:?}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    // `optimize.rkt` writes `best.s` after optimization returns, so the file alone only proves that
    // GreenThumb produced some printable program. `stat.rkt` writes `best.info` from
    // `update-best-correct`, which is the point where the search has identified a correct candidate.
    // For program rewriting we require that stronger signal; replacing assembly with fallback output
    // would silently leave an invalid block in place under the restricted ISA.
    let best_info = output_dir.join("best.info");
    let best_info_contents = fs::read_to_string(&best_info).unwrap_or_else(|err| {
        panic!(
            "GreenThumb optimizer produced {best_s:?}, but no rewrite was identified at {best_info:?}: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });

    let mut lines = best_info_contents.lines();
    let cost = lines.next().and_then(|line| line.parse::<u64>().ok());
    let len = lines.next().and_then(|line| line.parse::<u64>().ok());
    if cost.is_none() || len.is_none() {
        panic!(
            "GreenThumb rewrite metadata in {best_info:?} was malformed: {best_info_contents:?}"
        );
    }

    best_s
}

fn greenthumb_path() -> OsString {
    let mut paths = Vec::new();
    if let Some(home) = env::var_os("HOME") {
        paths.push(PathBuf::from(home).join("racket/bin"));
    }
    if let Some(existing) = env::var_os("PATH") {
        paths.extend(env::split_paths(&existing));
    }
    env::join_paths(paths).expect("failed to construct PATH for GreenThumb")
}

pub struct LabelAllocator {
    prefix: String,
    next: usize,
}

impl LabelAllocator {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
            next: 0,
        }
    }

    pub fn fresh(&mut self, hint: &str) -> String {
        let label = format!(".L{}_{}_{}", self.prefix, hint, self.next);
        self.next += 1;
        label
    }
}
