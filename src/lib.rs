use std::path::PathBuf;
use std::error::Error;

mod bit;

/// Configuration for the whole program
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    /// Path of the synthesized CPU HDL file
    pub hdl_path: PathBuf,

    /// Path of the "binary" (strings of 1s and 0s with each instruction on a new line)
    pub program_binary_path: PathBuf,

    /// Gate library liberty file path
    pub gate_library_path: PathBuf
}

impl Config {
    pub fn new(hdl_path_str: String, program_binary_path_str: String, gate_library_path_str: String) -> Result<Self, Box<dyn Error>> {
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
            gate_library_path
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config() {

    }
}