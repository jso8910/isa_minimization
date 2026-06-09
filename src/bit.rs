use std::collections::HashMap;
use std::ops::{BitAnd, BitOr, Not, BitXor};
use regex::Regex;
use rhai::{CustomType, Engine, Scope, TypeBuilder};

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
    Test
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
            .with_fn("&",|a: &mut Bit, b: Bit| *a & b)
            .with_fn("|",|a: &mut Bit, b: Bit| *a | b)
            .with_fn("^",|a: &mut Bit, b: Bit| *a ^ b)

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
            Bit::Var => Bit::Var
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
            (Bit::Low, Bit::Low) => Bit::Low
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
            (Bit::High, Bit::High) | (Bit::Low, Bit::Low) => Bit::Low
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BitPattern {
    pub bits: Vec<Bit>
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
                _ => panic!("Invalid bit pattern character: {c}")
            })
            .collect();
        Self { bits }
    }

    pub fn variable(width: usize) -> Self {
        Self {
            bits: vec![Bit::Var; width],
        }
    }

    pub fn matches_bits(&self, bits: &[Bit]) -> bool {
        if self.bits.len() != bits.len() {
            return false;
        }

        for (pattern_bit, bit) in self.bits.iter().zip(bits) {
            match pattern_bit {
                Bit::Low => if *bit != Bit::Low { return false; },
                Bit::High => if *bit != Bit::High { return false; },
                Bit::Var => {},
                Bit::Test => {}
            }
        }
        true
    }

    pub fn num_high(&self) -> usize {
        return self.bits.iter().filter(|b| **b == Bit::High).count()
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
        assert!(self.can_merge_with(other), "Cannot merge these two BitPatterns");

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
}

/// Lookup table implementation for boolean functions involving the Bit enum
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
    input_names: Vec<String>
}

impl LookupTable {
    pub fn new(input_count: usize, truth_table: Vec<Bit>, input_names: Vec<String>) -> Self {
        // Truth table length should be equal to 4**input_count
        assert_eq!(truth_table.len(), 1 << 2*input_count, "Invalid truth table size");

        Self { input_count, truth_table, input_names }
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
    pub fn new_from_string(expr: &str, input_names: Vec<String>) -> Self {
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

        // We need to permute every bit
        let mut input_vals: HashMap<String, Bit> = HashMap::new();
        for i in 0..(1 << 2*input_names.len()) {
            for (idx, input) in input_names.iter().enumerate() {
                input_vals.insert(
                    input.to_string(),
                    match (i >> (2*idx)) & 0b11 {
                        0 => Bit::Low,
                        1 => Bit::High,
                        2 => Bit::Var,
                        3 => Bit::Test,
                        _ => panic!("This can't happen. Value cannot be greater than 3")
                    }
                );
            }

            truth_table.push(LookupTable::eval_string_expr(&expr, &input_vals));
        }
        LookupTable { input_count: input_names.len(), truth_table, input_names: input_names }
    }

    /// Evaluates the expression in the LUT
    /// # Arguments
    /// * `operands` - a HashMap which contains key-value pairs of the inputs and outputs in the expression
    pub fn evaluate_named(&self, operands: &HashMap<String, Bit>) -> Bit {
        let mut operands_unnamed: Vec<Bit> = Vec::with_capacity(self.input_count);
        for key in &self.input_names {
            operands_unnamed.push(*operands.get(key).expect("Must include all inputs in `operands`"));
        }
        self.evaluate(&operands_unnamed)
    }

    /// Function which takes, as input, a string expression and the inputs to it (as BitTypes) and returns the result
    /// Uses the rhai module
    fn eval_string_expr(expr: &str, inputs: &HashMap<String, Bit>) -> Bit {
        let mut engine = Engine::new();

        // In order for operator overloading to work, "fast operators" must be set to false
        engine.set_fast_operators(false);

        // Register Bit with the rhai engine
        engine.build_type::<Bit>();


        let mut scope = Scope::new();
        for (name, val) in inputs {
            scope.push(name.to_string(), *val);
        }

        engine.eval_with_scope(&mut scope, expr).unwrap()
    }

    /// Takes a list of operands, in the same order as `self.input_names`, and returns the result in the LUT
    fn evaluate(&self, operands: &[Bit]) -> Bit {
        assert_eq!(operands.len(), self.input_count, "Invalid number of operands");

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
                Bit::Test => 3
            };
            index |= enc << (2 * i);
        }
        index
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    }

    mod lookup_table {
        use super::*;

        #[test]
        fn lookup_table_and_function() {
            // Simple test of a truth table for an and function
            let table = vec![
                // b = 0
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = 1
                Bit::Low, Bit::High, Bit::Var, Bit::Test,
                // b = variable
                Bit::Low, Bit::Var, Bit::Var, Bit::Test,
                // b = test
                Bit::Low, Bit::Test, Bit::Test, Bit::Test
            ];
            let lookup_table = LookupTable::new(2, table, vec![String::from("A"), String::from("B")]);

            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = HashMap::from([
                        (String::from("A"), a),
                        (String::from("B"), b)
                    ]);
                    assert_eq!(lookup_table.evaluate_named(&operands), a & b);
                }
            }
        }

        #[test]
        fn lookup_table_noncommutative_function() {
            // Test of a noncommutative function. In this case, the implication function (X = !A | B)
            let table = vec![
                // b = 0
                Bit::High, Bit::Low, Bit::Var, Bit::Test,
                // b = 1
                Bit::High, Bit::High, Bit::High, Bit::High,
                // b = variable
                Bit::High, Bit::Var, Bit::Var, Bit::Test,
                // b = test
                Bit::High, Bit::Test, Bit::Test, Bit::Test
            ];
            let lookup_table = LookupTable::new(2, table, vec![String::from("A"), String::from("B")]);

            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = HashMap::from([
                        (String::from("A"), a),
                        (String::from("B"), b)
                    ]);
                    assert_eq!(lookup_table.evaluate_named(&operands), !a | b);
                }
            }
        }

        #[test]
        fn lookup_table_three_input_function() {
            // Table for 3 input and
            let table = vec![
                // b = 0, c = 0
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = 1, c = 0
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = x, c = 0
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = t, c = 0
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = 0, c = 1
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = 1, c = 1
                Bit::Low, Bit::High, Bit::Var, Bit::Test,
                // b = x, c = 1
                Bit::Low, Bit::Var, Bit::Var, Bit::Test,
                // b = t, c = 1
                Bit::Low, Bit::Test, Bit::Test, Bit::Test,
                // b = 0, c = x
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = 1, c = x
                Bit::Low, Bit::Var, Bit::Var, Bit::Test,
                // b = x, c = x
                Bit::Low, Bit::Var, Bit::Var, Bit::Test,
                // b = t, c = x
                Bit::Low, Bit::Test, Bit::Test, Bit::Test,
                // b = 0, c = t
                Bit::Low, Bit::Low, Bit::Low, Bit::Low,
                // b = 1, c = t
                Bit::Low, Bit::Test, Bit::Test, Bit::Test,
                // b = x, c = t
                Bit::Low, Bit::Test, Bit::Test, Bit::Test,
                // b = t, c = t
                Bit::Low, Bit::Test, Bit::Test, Bit::Test,
            ];
            let lookup_table = LookupTable::new(3, table, vec![String::from("A"), String::from("B"), String::from("C")]);

            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    for c in bits {
                        let operands = HashMap::from([
                            (String::from("A"), a),
                            (String::from("B"), b),
                            (String::from("C"), c)
                        ]);
                        assert_eq!(lookup_table.evaluate_named(&operands), a & b & c);
                    }
                }
            }
        }

        #[test]
        fn lookup_table_str_and() {
            let input_names = vec![
                String::from("A"),
                String::from("B")
            ];
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
            let input_names = vec![
                String::from("A"),
                String::from("B"),
                String::from("C")
            ];
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
            let input_names = vec![
                String::from("A"),
                String::from("B"),
                String::from("C")
            ];
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
            let input_names = vec![
                String::from("A"),
                String::from("B")
            ];
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
            let input_names = vec![
                String::from("A"),
                String::from("B")
            ];
            let lookup_table = LookupTable::new_from_string("!A | (B & 1) & 0", input_names);
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Var];
            for a in bits {
                for b in bits {
                    let operands = vec![a, b];
                    assert_eq!(lookup_table.evaluate(&operands), !a | (b & Bit::High) & Bit::Low);
                }
            }
        }
    }
}