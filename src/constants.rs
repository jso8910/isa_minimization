// BDD constants
// TODO multiple threads perchance? command line option
pub const THREAD_COUNT: u32 = 1;
// Anecdotally, these seem like good, performant values
// When running arm32_sign_extend_example, the execution time per iteration
// jumps after these numbers
pub const INNER_NODE_CAPACITY: usize = 1 << 20;
pub const APPLY_CACHE_CAPACITY: usize = 1 << 20;

// Markov chain Monte Carlo temperature (1/T = Beta)
// Higher => more likely to accept a higher cost proposal
pub const MCMC_TEMP: f64 = 5.0;

// Weight for how heavily the number of instructions in the program should be weighted relative to
// correctness in MCMC stochastic instruction generation (impacts which search space the optimizer
// enters)
pub const WEIGHT_PROG_LEN: u32 = 0;

// Constant which defines the penalty in MachineState::compare when one side writes to an included
// register or memory location and the other doesn't. The symmetric nature of this constant applies
// both to penalizing a new candidate program for writing to extra protected registers and to
// forgetting to write required destination registers.
pub const WEIGHT_EXTRA_WRITE: u32 = 5;

// If an instruction sequence reads from an unintended register/memory location (ie a location not
// read by the original sequence, or not written by the new program so far), a certain penalty is
// added
pub const WEIGHT_ILLEGAL_READ: f64 = 8.0;

// If we revisit the same program twice, we want a penalty
// It is of the form WEIGHT_REVISIT_PENALTY * ln(1 + num_visits)
pub const WEIGHT_REVISIT_PENALTY: f64 = 25.0;

// Constants from the STOKE paper
// Currently based on the original ones they used in table 10

// Constant for the extra cost when the least Hamming-distance register in the other state is not
// the same register (ie if R0 and R1' have the same value, but R0 and R0' don't have the same
// value).
// omega_m
pub const WEIGHT_REGISTER_MISMATCH: u32 = 3;

// Probabilities of stochastic program modifications
pub const P_FIELD_CHANGE: f64 = 0.6;
pub const P_INSTR_CHANGE: f64 = 0.30;
// Since the cost of an instruction change is high (likely to insert an illegal read or write), it's
// important to make the UNUSED probability much lower
pub const P_INSERT_UNUSED: f64 = 0.05;
pub const P_SWAP_LINES: f64 = 0.05;

// Superoptimization maximum program length
pub const SUPEROPTIMIZATION_PROGRAM_LEN: usize = 16;
