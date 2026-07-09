use regex::Regex;
use rhai::{CustomType, Engine, Scope, TypeBuilder};
use std::collections::{HashMap, HashSet};
use std::ops::{BitAnd, BitOr, BitXor, Not};

/// Enum for the Bit type used in symbolic simulation
#[derive(PartialEq, Eq, Debug, Copy, Clone, Hash)]
pub enum Bit {
    /// Logical 1
    High,
    /// Logical 0
    Low,
    /// Variable value (could be either 0 or 1)
    Var,
    /// Test value to test whether an operand affects the output of an expression
    /// Behaves the same as Variable but with higher precedence
    Test,
}

impl Bit {
    pub fn is_concrete(&self) -> bool {
        match self {
            Bit::High | Bit::Low => true,
            Bit::Var | Bit::Test => false,
        }
    }
}

// rhai custom type implementation
impl CustomType for Bit {
    fn build(mut builder: TypeBuilder<Self>) {
        builder
            .with_name("Bit")
            // Register variant constructors (Simulating Bit::High)
            .with_fn("High", || Bit::High)
            .with_fn("Low", || Bit::Low)
            .with_fn("Variable", || Bit::Var)
            .with_fn("Test", || Bit::Test)
            // Operator overloads
            .with_fn("!", |a: &mut Bit| !*a)
            .with_fn("&", |a: &mut Bit, b: Bit| *a & b)
            .with_fn("|", |a: &mut Bit, b: Bit| *a | b)
            .with_fn("^", |a: &mut Bit, b: Bit| *a ^ b)
            // Optional: Register a printer for debugging/printing inside scripts
            .on_print(|b| format!("{b:?}"))
            .on_debug(|b| format!("{b:?}"));
    }
}

impl Not for Bit {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Bit::Low => Bit::High,
            Bit::High => Bit::Low,
            Bit::Test => Bit::Test,
            Bit::Var => Bit::Var,
        }
    }
}

impl BitAnd for Bit {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Bit::Low, _) | (_, Bit::Low) => Bit::Low,
            (Bit::Test, _) | (_, Bit::Test) => Bit::Test,
            (Bit::Var, _) | (_, Bit::Var) => Bit::Var,
            (Bit::High, Bit::High) => Bit::High,
        }
    }
}

impl BitOr for Bit {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Bit::High, _) | (_, Bit::High) => Bit::High,
            (Bit::Test, _) | (_, Bit::Test) => Bit::Test,
            (Bit::Var, _) | (_, Bit::Var) => Bit::Var,
            (Bit::Low, Bit::Low) => Bit::Low,
        }
    }
}

impl BitXor for Bit {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Bit::Test, _) | (_, Bit::Test) => Bit::Test,
            (Bit::Var, _) | (_, Bit::Var) => Bit::Var,
            (Bit::High, Bit::Low) | (Bit::Low, Bit::High) => Bit::High,
            (Bit::High, Bit::High) | (Bit::Low, Bit::Low) => Bit::Low,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitPattern {
    pub bits: Vec<Bit>,
}

impl BitPattern {
    pub fn new(bits: Vec<Bit>) -> Self {
        Self { bits }
    }

    pub fn len(&self) -> usize {
        self.bits.len()
    }

    pub fn parse(s: &str) -> Self {
        let bits = s
            .chars()
            .map(|c| match c {
                '0' => Bit::Low,
                '1' => Bit::High,
                'x' => Bit::Var,
                _ => panic!("Invalid bit pattern character: {c}"),
            })
            .collect();
        Self { bits }
    }

    pub fn variable(width: usize) -> Self {
        Self {
            bits: vec![Bit::Var; width],
        }
    }

    pub fn matches_prefix(&self, prefix: &[Bit]) -> bool {
        // Checks whether a k bit prefix matches the first k bits of an n bit BitPattern, k<n
        let prefix_len = prefix.len();
        if prefix_len > self.len() {
            return false;
        }

        // By default, zip takes the shorter length, which should be `prefix`
        for (pattern_bit, bit) in self.bits.iter().zip(prefix) {
            match pattern_bit {
                Bit::Low => {
                    if *bit != Bit::Low {
                        return false;
                    }
                }
                Bit::High => {
                    if *bit != Bit::High {
                        return false;
                    }
                }
                Bit::Var => {}
                Bit::Test => {}
            }
        }
        true
    }

    pub fn matches_bits(&self, bits: &[Bit]) -> bool {
        if self.bits.len() != bits.len() {
            return false;
        }

        self.matches_prefix(bits)
    }

    pub fn num_high(&self) -> usize {
        return self.bits.iter().filter(|b| **b == Bit::High).count();
    }

    pub fn num_variable(&self) -> usize {
        return self.bits.iter().filter(|b| **b == Bit::Var).count();
    }

    pub fn can_merge_with(&self, other: &BitPattern) -> bool {
        if self.bits.len() != other.bits.len() {
            return false;
        }

        let mut diff_count = 0;
        for (b1, b2) in self.bits.iter().zip(&other.bits) {
            if b1 != b2 {
                // If the bits are different, they can only be merged if one of them is high and the other is low
                if (b1 == &Bit::High && b2 == &Bit::Low) || (b1 == &Bit::Low && b2 == &Bit::High) {
                    // This is fine, we can merge these two bits into a variable bit
                } else {
                    // If the bits are different but cannot be merged, then these two patterns cannot be merged
                    return false;
                }
                diff_count += 1;
            }
        }
        diff_count == 1
    }

    pub fn merge_with(&self, other: &BitPattern) -> Self {
        assert!(
            self.can_merge_with(other),
            "Cannot merge these two BitPatterns"
        );

        let merged_bits = self.bits.iter().zip(&other.bits).map(|(b1, b2)| {
            if b1 == b2 {
                *b1
            } else {
                // If the bits are different, they can only be merged if one of them is high and the other is low, in which case we merge them into a variable bit
                if b1 == &Bit::High && b2 == &Bit::Low || b1 == &Bit::Low && b2 == &Bit::High {
                    Bit::Var
                } else {
                    panic!("This should never happen since we check can_merge_with before calling this function");
                }
            }
        }).collect();

        Self { bits: merged_bits }
    }

    pub fn to_int(&self) -> u128 {
        self.bits
            .iter()
            .rev()
            .enumerate()
            .map(|(idx, b)| match b {
                Bit::High => 1 << idx,
                Bit::Low => 0,
                _ => panic!("BitPattern must have no Var or Test"),
            })
            .sum()
    }

    /// Cube subtraction/sharp operation. For A # B, the result is the part of cube A not covered by
    /// cube B.
    /// The sharp product is described in
    /// Roth, J. Paul. “Algebraic Topological Methods for the Synthesis of Switching Systems. I.”
    /// Transactions of the American Mathematical Society 88, no. 2 (1958): 301–26.
    /// https://doi.org/10.2307/1993216.
    pub fn cube_subtract(&self, other: &BitPattern) -> HashSet<BitPattern> {
        if self.len() != other.len() {
            panic!("Cube subtract must have same length!");
        }
        if self.cube_disjoint(other) {
            return HashSet::from([self.clone()]);
        }

        if other.cube_covers(self) {
            return HashSet::new();
        }

        for (idx, (bit, other_bit)) in self.bits.iter().zip(&other.bits).enumerate() {
            if !bit.is_concrete() && other_bit.is_concrete() {
                // Now we have two cases: where `self` is outside `other` (bit == !other_bit)
                // and where `self` is inside `other`
                // When `self` is outside `other`, it is a part of A not covered by B
                // When `self is inside `other`, we can recursively call subtract
                let mut outside = self.clone();
                outside.bits[idx] = !*other_bit;
                let mut res = HashSet::from([outside]);

                let mut inside = self.clone();
                inside.bits[idx] = *other_bit;

                res.extend(inside.cube_subtract(other));
                return res;
            }
        }

        panic!(
            "If `self` is not either covered by or disjoint with `other`, there should be at least one index where `self` has a variable bit and `other` has a concrete bit"
        );
    }

    /// Returns whether two cubes are disjoint
    fn cube_disjoint(&self, other: &BitPattern) -> bool {
        self.bits
            .iter()
            .zip(&other.bits)
            .any(|(x, y)| matches!((x, y), (Bit::Low, Bit::High) | (Bit::High, Bit::Low)))
    }

    /// Returns whether `self` covers `other`
    fn cube_covers(&self, other: &BitPattern) -> bool {
        self.bits
            .iter()
            .zip(&other.bits)
            .all(|(x, y)| *x == Bit::Var || x == y)
    }
}

/// Lookup table implementation for boolean functions involving the Bit enum
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct LookupTable {
    /// Number of inputs in the boolean function
    input_count: usize,
    /// Truth table with 4^n values for each input
    /// Indexes are encoded as following:
    ///     1. 00 = low
    ///     2. 01 = high
    ///     3. 10 = variable
    ///     4. 11 = test
    /// For a 3 input function where the inputs are aa, bb, cc, the index in this vector is 0bccbbaa (c goes in MSB, etc)
    truth_table: Vec<Bit>,
    /// Function inputs
    input_names: Vec<String>,
    /// Optional: original function value
    function: Option<String>,
}

impl LookupTable {
    pub fn new(
        input_count: usize,
        truth_table: Vec<Bit>,
        input_names: Vec<String>,
        function: Option<String>,
    ) -> Self {
        // Truth table length should be equal to 4**input_count
        assert_eq!(
            truth_table.len(),
            1 << 2 * input_count,
            "Invalid truth table size"
        );

        Self {
            input_count,
            truth_table,
            input_names,
            function,
        }
    }

    /// Defines a new LookupTable from a boolean function string.
    /// The syntax used is the same as that defined in the Liberty file format
    /// For the specification, see page 156 in the following document
    /// https://people.eecs.berkeley.edu/~alanmi/publications/other/liberty07_03.pdf
    ///
    /// Does not support certain constructs (e.g. postfix invert, space for and)
    ///
    /// # Arguments
    /// * `expr` - the boolean function expression as a string
    /// * `inputs` - a vector of the names of all inputs in the expression, in the order they will be included in the LUT
    pub fn new_from_string(expr: &str, input_names: Vec<&str>) -> Self {
        // In order to evaluate this function, we don't want to have to manually parse it
        // What we do is we construct a LUT by using the eval_string_expr function

        // First, some preprocessing on the expr string

        // The liberty file expressions support * and + for the bitwise operators
        let expr = expr.replace("*", "&");
        let expr = expr.replace("+", "|");

        // They also support 1 and 0 for hardcoded bits
        let re_low = Regex::new(r"\b0\b").unwrap();
        let re_high = Regex::new(r"\b1\b").unwrap();
        let expr = re_high.replace_all(&expr, "High()").into_owned();
        let expr = re_low.replace_all(&expr, "Low()").into_owned();

        let mut truth_table: Vec<Bit> = Vec::with_capacity(2 << input_names.len());

        // Create rhai engine
        let mut engine = Engine::new();

        // Needed for overloaded operators on Bit
        engine.set_fast_operators(false);

        // Register Bit
        engine.build_type::<Bit>();

        // Compile/parse the expression
        let ast = engine.compile_expression(&expr).unwrap();

        // Create scope once
        let mut scope = Scope::new();
        for name in input_names.iter() {
            scope.push(*name, Bit::Low);
        }

        // We need to permute every bit
        // let mut input_vals: HashMap<String, Bit> = HashMap::new();
        for i in 0..(1 << 2 * input_names.len()) {
            for (idx, input) in input_names.iter().enumerate() {
                let val = match (i >> (2 * idx)) & 0b11 {
                    0 => Bit::Low,
                    1 => Bit::High,
                    2 => Bit::Var,
                    3 => Bit::Test,
                    _ => panic!("This can't happen. Value cannot be greater than 3"),
                };
                scope.set_value(*input, val);
            }

            let result = engine.eval_ast_with_scope::<Bit>(&mut scope, &ast).unwrap();
            truth_table.push(result);
            // truth_table.push(LookupTable::eval_string_expr(&expr, &input_vals));
        }
        LookupTable {
            input_count: input_names.len(),
            truth_table,
            input_names: input_names.into_iter().map(|v| v.to_string()).collect(),
            function: Some(expr.to_string()),
        }
    }

    /// Evaluates the expression in the LUT
    /// # Arguments
    /// * `operands` - a HashMap which contains key-value pairs of the inputs and outputs in the expression
    pub fn evaluate_named(&self, operands: &HashMap<String, Bit>) -> Bit {
        let mut operands_unnamed: Vec<Bit> = Vec::with_capacity(self.input_count);
        for key in &self.input_names {
            operands_unnamed.push(
                *operands
                    .get(key)
                    .expect("Must include all inputs in `operands`"),
            );
        }
        self.evaluate(&operands_unnamed)
    }

    /// Takes a list of operands, in the same order as `self.input_names`, and returns the result in the LUT
    pub fn evaluate(&self, operands: &[Bit]) -> Bit {
        assert_eq!(
            operands.len(),
            self.input_count,
            "Invalid number of operands"
        );

        // Find the correct index in the LUT
        let index = self.get_index(operands);

        self.truth_table[index]
    }

    /// Used to get the index in the lookup table corresponding with certain operands
    fn get_index(&self, operands: &[Bit]) -> usize {
        let mut index = 0;
        for (i, val) in operands.iter().enumerate() {
            let enc = match val {
                Bit::Low => 0,
                Bit::High => 1,
                Bit::Var => 2,
                Bit::Test => 3,
            };
            index |= enc << (2 * i);
        }
        index
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn bit_pattern_to_int() {
        assert_eq!(BitPattern::parse("1001").to_int(), 9);
        assert_eq!(BitPattern::parse("101000010010001111").to_int(), 165007);
        assert_eq!(
            BitPattern::parse("1000001001011111111110011010110").to_int(),
            1093663958
        );
    }

    #[test]
    #[should_panic]
    fn fail_if_variable_bit() {
        BitPattern::parse("100x0").to_int();
    }

    #[test]
    fn matches_prefix_accepts_matching_concrete_prefix() {
        let pattern = BitPattern::parse("1010");

        assert!(pattern.matches_prefix(&[Bit::High, Bit::Low]));
        assert!(pattern.matches_prefix(&[Bit::High, Bit::Low, Bit::High, Bit::Low]));
    }

    #[test]
    fn matches_prefix_rejects_mismatched_or_too_long_prefix() {
        let pattern = BitPattern::parse("1010");

        assert!(!pattern.matches_prefix(&[Bit::High, Bit::High]));
        assert!(!pattern.matches_prefix(&[Bit::High, Bit::Low, Bit::High, Bit::Low, Bit::Low,]));
    }

    #[test]
    fn matches_prefix_treats_pattern_var_and_test_bits_as_wildcards() {
        let pattern = BitPattern::new(vec![Bit::High, Bit::Var, Bit::Test, Bit::Low]);

        assert!(pattern.matches_prefix(&[Bit::High, Bit::Low, Bit::High, Bit::Low]));
        assert!(pattern.matches_prefix(&[Bit::High, Bit::High, Bit::Low, Bit::Low]));
        assert!(!pattern.matches_prefix(&[Bit::Low]));
    }

    #[test]
    fn matches_bits_requires_equal_length() {
        let pattern = BitPattern::parse("10xx");

        assert!(pattern.matches_bits(&[Bit::High, Bit::Low, Bit::Low, Bit::High]));
        assert!(!pattern.matches_bits(&[Bit::High, Bit::Low]));
        assert!(!pattern.matches_bits(&[Bit::High, Bit::Low, Bit::Low, Bit::High, Bit::Low,]));
    }

    #[test]
    fn matches_bits_rejects_concrete_mismatches() {
        let pattern = BitPattern::parse("10x1");

        assert!(!pattern.matches_bits(&[Bit::High, Bit::High, Bit::Low, Bit::High]));
        assert!(!pattern.matches_bits(&[Bit::High, Bit::Low, Bit::High, Bit::Low]));
    }

    fn bit_pattern_string(pattern: &BitPattern) -> String {
        pattern
            .bits
            .iter()
            .map(|bit| match bit {
                Bit::Low => '0',
                Bit::High => '1',
                Bit::Var => 'x',
                Bit::Test => 't',
            })
            .collect()
    }

    fn cube_subtract_patterns(lhs: &str, rhs: &str) -> HashSet<String> {
        let lhs = BitPattern::parse(lhs);
        let rhs = BitPattern::parse(rhs);

        lhs.cube_subtract(&rhs)
            .into_iter()
            .map(|pattern| bit_pattern_string(&pattern))
            .collect()
    }

    fn pattern_set(patterns: &[&str]) -> HashSet<String> {
        patterns.iter().map(|pattern| pattern.to_string()).collect()
    }

    #[test]
    fn cube_subtract_returns_original_cube_when_disjoint() {
        assert_eq!(cube_subtract_patterns("0x", "1x"), pattern_set(&["0x"]));
    }

    #[test]
    fn cube_subtract_returns_empty_when_cubes_are_identical() {
        assert!(cube_subtract_patterns("10x", "10x").is_empty());
    }

    #[test]
    fn cube_subtract_returns_empty_when_rhs_covers_lhs() {
        assert!(cube_subtract_patterns("100", "1xx").is_empty());
    }

    #[test]
    fn cube_subtract_splits_single_variable_against_concrete_bit() {
        assert_eq!(cube_subtract_patterns("xx", "0x"), pattern_set(&["1x"]));
    }

    #[test]
    fn cube_subtract_splits_on_later_variable_when_prefix_matches() {
        assert_eq!(cube_subtract_patterns("1xx", "10x"), pattern_set(&["11x"]));
    }

    #[test]
    fn cube_subtract_fragments_two_constrained_bits() {
        assert_eq!(
            cube_subtract_patterns("xxx", "010"),
            pattern_set(&["1xx", "00x", "011"])
        );
    }

    #[test]
    fn cube_subtract_handles_rhs_with_variable_suffix() {
        assert_eq!(
            cube_subtract_patterns("xxxx", "10xx"),
            pattern_set(&["0xxx", "11xx"])
        );
    }

    #[test]
    fn cube_subtract_preserves_unrelated_concrete_bits_in_fragments() {
        assert_eq!(
            cube_subtract_patterns("x1x0", "1100"),
            pattern_set(&["01x0", "1110"])
        );
    }

    #[test]
    fn cube_subtract_removes_one_point_from_two_bit_cube() {
        assert_eq!(
            cube_subtract_patterns("xx", "00"),
            pattern_set(&["1x", "01"])
        );
    }

    #[test]
    #[should_panic(expected = "Cube subtract must have same length!")]
    fn cube_subtract_panics_for_mismatched_lengths() {
        BitPattern::parse("xx").cube_subtract(&BitPattern::parse("xxx"));
    }

    mod bit {
        use super::*;

        // Tests for and function
        mod and {
            use super::*;

            #[test]
            fn and_high_returns_high() {
                assert_eq!(Bit::High & Bit::High, Bit::High);
            }

            #[test]
            fn and_low_returns_low() {
                assert_eq!(Bit::High & Bit::Low, Bit::Low);
                assert_eq!(Bit::Low & Bit::High, Bit::Low);
                assert_eq!(Bit::Low & Bit::Low, Bit::Low);
                assert_eq!(Bit::Low & Bit::Var, Bit::Low);
                assert_eq!(Bit::Test & Bit::Low, Bit::Low);
            }

            #[test]
            fn and_variable_returns_variable() {
                assert_eq!(Bit::High & Bit::Var, Bit::Var);
                assert_eq!(Bit::Var & Bit::Var, Bit::Var);
                assert_eq!(Bit::Var & Bit::High, Bit::Var);
            }

            #[test]
            fn and_test_returns_test() {
                assert_eq!(Bit::High & Bit::Test, Bit::Test);
                assert_eq!(Bit::Test & Bit::High, Bit::Test);
                assert_eq!(Bit::Test & Bit::Var, Bit::Test);
            }

            #[test]
            fn and_is_commutative() {
                let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
                for v1 in bits {
                    for v2 in bits {
                        assert_eq!(v1 & v2, v2 & v1)
                    }
                }
            }
        }

        // Tests for invert
        mod not {
            use super::*;

            #[test]
            fn not_high_returns_low() {
                assert_eq!(!Bit::High, Bit::Low);
            }

            #[test]
            fn not_low_returns_high() {
                assert_eq!(!Bit::Low, Bit::High);
            }

            #[test]
            fn not_variable_returns_variable() {
                assert_eq!(!Bit::Var, Bit::Var);
            }

            #[test]
            fn not_test_returns_test() {
                assert_eq!(!Bit::Test, Bit::Test);
            }
        }

        // Or function tests
        mod or {
            use super::*;

            #[test]
            fn or_high_returns_high() {
                assert_eq!(Bit::High | Bit::Low, Bit::High);
                assert_eq!(Bit::High | Bit::Test, Bit::High);
                assert_eq!(Bit::High | Bit::Var, Bit::High);
            }

            #[test]
            fn or_low_returns_low() {
                assert_eq!(Bit::Low | Bit::Low, Bit::Low);
            }

            #[test]
            fn or_variable_returns_variable() {
                assert_eq!(Bit::Var | Bit::Low, Bit::Var);
                assert_eq!(Bit::Var | Bit::Var, Bit::Var);
            }

            #[test]
            fn or_test_returns_test() {
                assert_eq!(Bit::Test | Bit::Low, Bit::Test);
                assert_eq!(Bit::Test | Bit::Var, Bit::Test);
                assert_eq!(Bit::Test | Bit::Test, Bit::Test);
            }

            #[test]
            fn or_is_commutative() {
                let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
                for v1 in bits {
                    for v2 in bits {
                        assert_eq!(v1 | v2, v2 | v1)
                    }
                }
            }
        }

        // Tests for xor function
        mod xor {
            use super::*;

            #[test]
            fn xor_one_high_returns_high() {
                assert_eq!(Bit::High ^ Bit::Low, Bit::High);
            }

            #[test]
            fn xor_match_returns_low() {
                assert_eq!(Bit::High ^ Bit::High, Bit::Low);
                assert_eq!(Bit::Low ^ Bit::Low, Bit::Low);
            }

            #[test]
            fn xor_variable_returns_variable() {
                assert_eq!(Bit::Var ^ Bit::High, Bit::Var);
                assert_eq!(Bit::Var ^ Bit::Low, Bit::Var);
            }

            #[test]
            fn xor_test_returns_test() {
                assert_eq!(Bit::Test ^ Bit::High, Bit::Test);
                assert_eq!(Bit::Test ^ Bit::Low, Bit::Test);
            }

            #[test]
            fn xor_is_commutative() {
                let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
                for v1 in bits {
                    for v2 in bits {
                        assert_eq!(v1 ^ v2, v2 ^ v1)
                    }
                }
            }
        }

        #[test]
        fn bit_pattern_num_high() {
            let bp = BitPattern::parse("1011xxx1000x");
            assert_eq!(bp.num_high(), 4);
        }

        #[test]
        fn bit_pattern_num_variable_counts_only_variable_bits() {
            let bp = BitPattern::new(vec![
                Bit::Var,
                Bit::High,
                Bit::Low,
                Bit::Test,
                Bit::Var,
                Bit::Var,
            ]);

            assert_eq!(bp.num_variable(), 3);
        }
    }

    mod lookup_table {
        use super::*;

        #[test]
        fn lookup_table_and_function() {
            // Simple test of a truth table for an and function
            let table = vec![
                // b = 0
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = 1
                Bit::Low,
                Bit::High,
                Bit::Var,
                Bit::Test,
                // b = variable
                Bit::Low,
                Bit::Var,
                Bit::Var,
                Bit::Test,
                // b = test
                Bit::Low,
                Bit::Test,
                Bit::Test,
                Bit::Test,
            ];
            let lookup_table =
                LookupTable::new(2, table, vec![String::from("A"), String::from("B")], None);

            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = HashMap::from([(String::from("A"), a), (String::from("B"), b)]);
                    assert_eq!(lookup_table.evaluate_named(&operands), a & b);
                }
            }
        }

        #[test]
        fn lookup_table_noncommutative_function() {
            // Test of a noncommutative function. In this case, the implication function (X = !A | B)
            let table = vec![
                // b = 0
                Bit::High,
                Bit::Low,
                Bit::Var,
                Bit::Test,
                // b = 1
                Bit::High,
                Bit::High,
                Bit::High,
                Bit::High,
                // b = variable
                Bit::High,
                Bit::Var,
                Bit::Var,
                Bit::Test,
                // b = test
                Bit::High,
                Bit::Test,
                Bit::Test,
                Bit::Test,
            ];
            let lookup_table =
                LookupTable::new(2, table, vec![String::from("A"), String::from("B")], None);

            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = HashMap::from([(String::from("A"), a), (String::from("B"), b)]);
                    assert_eq!(lookup_table.evaluate_named(&operands), !a | b);
                }
            }
        }

        #[test]
        fn lookup_table_three_input_function() {
            // Table for 3 input and
            let table = vec![
                // b = 0, c = 0
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = 1, c = 0
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = x, c = 0
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = t, c = 0
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = 0, c = 1
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = 1, c = 1
                Bit::Low,
                Bit::High,
                Bit::Var,
                Bit::Test,
                // b = x, c = 1
                Bit::Low,
                Bit::Var,
                Bit::Var,
                Bit::Test,
                // b = t, c = 1
                Bit::Low,
                Bit::Test,
                Bit::Test,
                Bit::Test,
                // b = 0, c = x
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = 1, c = x
                Bit::Low,
                Bit::Var,
                Bit::Var,
                Bit::Test,
                // b = x, c = x
                Bit::Low,
                Bit::Var,
                Bit::Var,
                Bit::Test,
                // b = t, c = x
                Bit::Low,
                Bit::Test,
                Bit::Test,
                Bit::Test,
                // b = 0, c = t
                Bit::Low,
                Bit::Low,
                Bit::Low,
                Bit::Low,
                // b = 1, c = t
                Bit::Low,
                Bit::Test,
                Bit::Test,
                Bit::Test,
                // b = x, c = t
                Bit::Low,
                Bit::Test,
                Bit::Test,
                Bit::Test,
                // b = t, c = t
                Bit::Low,
                Bit::Test,
                Bit::Test,
                Bit::Test,
            ];
            let lookup_table = LookupTable::new(
                3,
                table,
                vec![String::from("A"), String::from("B"), String::from("C")],
                None,
            );

            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    for c in bits {
                        let operands = HashMap::from([
                            (String::from("A"), a),
                            (String::from("B"), b),
                            (String::from("C"), c),
                        ]);
                        assert_eq!(lookup_table.evaluate_named(&operands), a & b & c);
                    }
                }
            }
        }

        #[test]
        fn lookup_table_str_and() {
            let input_names = vec!["A", "B"];
            let lookup_table = LookupTable::new_from_string("A & B", input_names);
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = vec![a, b];
                    assert_eq!(lookup_table.evaluate(&operands), a & b);
                }
            }
        }

        #[test]
        fn lookup_table_str_and3() {
            let input_names = vec!["A", "B", "C"];
            let lookup_table = LookupTable::new_from_string("A & B & C", input_names);
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    for c in bits {
                        let operands = vec![a, b, c];
                        assert_eq!(lookup_table.evaluate(&operands), a & b & c);
                    }
                }
            }
        }

        #[test]
        fn lookup_table_str_3_inp_noncommutative() {
            let input_names = vec!["A", "B", "C"];
            let lookup_table = LookupTable::new_from_string("!A | (B & C)", input_names);
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    for c in bits {
                        let operands = vec![a, b, c];
                        assert_eq!(lookup_table.evaluate(&operands), !a | (b & c));
                    }
                }
            }
        }

        #[test]
        fn lookup_table_str_hardcoded_high() {
            let input_names = vec!["A", "B"];
            let lookup_table = LookupTable::new_from_string("!A | (B & 1)", input_names);
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = vec![a, b];
                    assert_eq!(lookup_table.evaluate(&operands), !a | (b & Bit::High));
                }
            }
        }

        #[test]
        fn lookup_table_str_hardcoded_low() {
            let input_names = vec!["A", "B"];
            let lookup_table = LookupTable::new_from_string("!A | (B & 1) & 0", input_names);
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = vec![a, b];
                    assert_eq!(
                        lookup_table.evaluate(&operands),
                        !a | (b & Bit::High) & Bit::Low
                    );
                }
            }
        }
    }
}
