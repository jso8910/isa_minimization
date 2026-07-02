// BDD constants
// TODO multiple threads perchance? command line option
pub const THREAD_COUNT: u32 = 1;
// Anecdotally, these seem like good, performant values
// When running arm32_sign_extend_example, the execution time per iteration
// jumps after these numbers
pub const INNER_NODE_CAPACITY: usize = 1 << 18;
pub const APPLY_CACHE_CAPACITY: usize = 1 << 18;

// Markov chain Monte Carlo temperature (1/T = Beta)
// Currently same value from STOKE
// TODO: at some point, may want to use simulated annealing
pub const MCMC_TEMP: u32 = 10;

// Weight for how heavily the number of instructions in the program should be weighted relative to
// correctness in MCMC stochastic instruction generation (impacts which search space the optimizer
// enters)
pub const WEIGHT_PROG_LEN: u32 = 3;

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

// Probabilities of stochastic program modifications
pub const P_FIELD_CHANGE: f64 = 0.65;
pub const P_INSTR_CHANGE: f64 = 0.125;
pub const P_INSERT_UNUSED: f64 = 0.125;
pub const P_SWAP_LINES: f64 = 0.1;

// Superoptimization maximum program length
pub const SUPEROPTIMIZATION_PROGRAM_LEN: usize = 16;
