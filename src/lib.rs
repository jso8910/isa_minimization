use std::error::Error;
use std::path::PathBuf;

pub mod bit;
pub mod constants;
pub mod instruction_semantics;
pub mod isa_specification;
pub mod parser;
pub mod semantic_matching;
pub mod simulator;
pub mod stdcell_library;
pub mod superoptimization;

/// Configuration for the whole program
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    /// Path of the synthesized CPU HDL file
    pub hdl_path: PathBuf,

    /// Path of the "binary" (strings of 1s and 0s with each instruction on a new line)
    pub program_binary_path: PathBuf,

    /// Gate library liberty file path
    pub gate_library_path: PathBuf,
}

impl Config {
    pub fn new(
        hdl_path_str: String,
        program_binary_path_str: String,
        gate_library_path_str: String,
    ) -> Result<Self, Box<dyn Error>> {
        let hdl_path = PathBuf::from(hdl_path_str);
        let program_binary_path = PathBuf::from(program_binary_path_str);
        let gate_library_path = PathBuf::from(gate_library_path_str);

        // Make sure all paths exist (return the error if it doesn't)
        hdl_path.try_exists()?;
        program_binary_path.try_exists()?;
        gate_library_path.try_exists()?;

        // Create Config object
        Ok(Self {
            hdl_path,
            program_binary_path,
            gate_library_path,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicUsize, Ordering},
    };

    static TEST_FILE_COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn write_temp_file(prefix: &str) -> String {
        let id = TEST_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let mut path: PathBuf = std::env::temp_dir();
        path.push(format!(
            "isa_minimization_config_{}_{}_{}",
            prefix,
            std::process::id(),
            id
        ));
        fs::write(&path, "").unwrap();
        path.to_string_lossy().into_owned()
    }

    #[test]
    fn config_new_accepts_existing_paths() {
        let hdl_path = write_temp_file("hdl");
        let program_binary_path = write_temp_file("program");
        let gate_library_path = write_temp_file("liberty");

        let config = Config::new(
            hdl_path.clone(),
            program_binary_path.clone(),
            gate_library_path.clone(),
        )
        .unwrap();

        assert_eq!(config.hdl_path, PathBuf::from(hdl_path));
        assert_eq!(
            config.program_binary_path,
            PathBuf::from(program_binary_path)
        );
        assert_eq!(config.gate_library_path, PathBuf::from(gate_library_path));
    }
}
