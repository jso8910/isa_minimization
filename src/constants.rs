// Weights for genetic algorithm hardware optimization
pub const WEIGHT_UNMODIFIED_PROGRAM: f64 = 0.5;
pub const WEIGHT_CORE_SIZE: f64 = 4.0;
pub const MUTATE_FIELD_RATE: f64 = 0.01;
pub const MUTATE_FORM_RATE: f64 = 0.001;
pub const P_MUT_CONST_TO_VAR: f64 = 0.5;
pub const P_MUT_VAR_TO_NONE: f64 = 0.05;
// probability of crossover for each individual gene (each value of valid_field_uses is considered
// to be one gene, or the valid forms of an instruction is considered to be a gene)
pub const P_CROSSOVER_GENE: f64 = 0.5;

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

// TODO: figure out relationship between temperature and number of counterexamples
// TODO: parameterize number of random counterexamples generated?
// TODO: figure out whether I actually want to weight program length by number of counterexamples?
// TODO: potentially try to figure out symmetry? the calculation couldn't be *that* hard
pub const MCMC_TEMP: f64 = 3.5;

// Weight for how heavily the number of instructions in the program should be weighted relative to
// correctness in MCMC stochastic instruction generation (impacts which search space the optimizer
// enters)
// no longer // Multiplied by the current number of counterexamples/test cases to be scaled.
pub const WEIGHT_PROG_LEN: f64 = 1.0;

// Constant which defines the penalty in MachineState::compare when one side writes to an included
// register or memory location and the other doesn't. The symmetric nature of this constant applies
// both to penalizing a new candidate program for writing to extra live-out registers and to
// forgetting to write required destination registers.
pub const WEIGHT_EXTRA_WRITE: u32 = 7;

// If an instruction sequence reads from an unintended register/memory location (ie a location not
// read by the original sequence, or not written by the new program so far), a certain penalty is
// added
pub const WEIGHT_ILLEGAL_READ: f64 = 8.0;

// To avoid local minima, we don't want to continue selecting proposals which have the same cost.
// So, we impose a penalty if a proposal has the same cost as the current proposal. Quick and dirty
// way to identify generating the same program.
pub const SAME_COST_PENALTY: f64 = 0.0;

// Constants from the STOKE paper
// Currently based on the original ones they used in table 10

// Constant for the extra cost when the least Hamming-distance register in the other state is not
// the same register (ie if R0 and R1' have the same value, but R0 and R0' don't have the same
// value).
// omega_m
pub const WEIGHT_REGISTER_MISMATCH: u32 = 5;

// Probabilities of stochastic program modifications
pub const P_FIELD_CHANGE: f64 = 0.44;
pub const P_INSTR_CHANGE: f64 = 0.35;
// Since the cost of an instruction change is high (likely to insert an illegal read or write), it's
// important to make the UNUSED probability much lower
pub const P_INSERT_UNUSED: f64 = 0.05;
pub const P_SWAP_LINES: f64 = 0.15;

// Superoptimization maximum program length
pub const SUPEROPTIMIZATION_PROGRAM_LEN: usize = 12;
