// BDD constants
// TODO multiple threads perchance? command line option
pub const THREAD_COUNT: u32 = 1;
// Anecdotally, these seem like good, performant values
// When running arm32_sign_extend_example, the execution time per iteration
// jumps after these numbers
pub const INNER_NODE_CAPACITY: usize = 1 << 18;
pub const APPLY_CACHE_CAPACITY: usize = 1 << 18;

// Constant which defines the penalty in MachineState::compare when one side writes to an included
// register or memory location and the other doesn't. The symmetric nature of this constant applies
// both to penalizing a new candidate program for writing to extra protected registers and to
// forgetting to write required destination registers.
pub const WEIGHT_EXTRA_WRITE: u32 = 3;

// Constants from the STOKE paper
// Currently based on the original ones they used in table 10

// Constant for the extra cost when the least Hamming-distance register in the other state is not
// the same register (ie if R0 and R1' have the same value, but R0 and R0' don't have the same
// value).
// omega_m
pub const WEIGHT_REGISTER_MISMATCH: u32 = 3;
