/// Enum for the Bit type used in symbolic simulation
#[derive(PartialEq, Eq, Debug)]
pub enum Bit {
    /// Logical 1
    High,
    /// Logical 0
    Low,
    /// Variable value (could be either 0 or 1)
    Variable,
    /// Test value to test whether an operand affects the output of an expression
    /// Behaves the same as Variable but with higher precedence
    Test
}

impl Bit {
    fn and(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (Bit::Low, _) | (_, Bit::Low) => Bit::Low,
            (Bit::Test, _) | (_, Bit::Test) => Bit::Test,
            (Bit::Variable, _) | (_, Bit::Variable) => Bit::Variable,
            (Bit::High, Bit::High) => Bit::High,
        }
    }

    fn not(&self) -> Self {
        match self {
            Bit::Low => Bit::High,
            Bit::High => Bit::Low,
            Bit::Test => Bit::Test,
            Bit::Variable => Bit::Variable
        }
    }

    fn or(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (Bit::High, _) | (_, Bit::High) => Bit::High,
            (Bit::Test, _) | (_, Bit::Test) => Bit::Test,
            (Bit::Variable, _) | (_, Bit::Variable) => Bit::Variable,
            (Bit::Low, Bit::Low) => Bit::Low
        }
    }

    fn xor(&self, rhs: &Self) -> Self {
        match (self, rhs) {
            (Bit::Test, _) | (_, Bit::Test) => Bit::Test,
            (Bit::Variable, _) | (_, Bit::Variable) => Bit::Variable,
            (Bit::High, Bit::Low) | (Bit::Low, Bit::High) => Bit::High,
            (Bit::High, Bit::High) | (Bit::Low, Bit::Low) => Bit::Low
        }
    }
    // fn build_expr() -> Self {}
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests for and function
    mod and {
        use super::*;

        #[test]
        fn and_high_returns_high() {
            assert_eq!(Bit::High.and(&Bit::High), Bit::High);
        }

        #[test]
        fn and_low_returns_low() {
            assert_eq!(Bit::High.and(&Bit::Low), Bit::Low);
            assert_eq!(Bit::Low.and(&Bit::High), Bit::Low);
            assert_eq!(Bit::Low.and(&Bit::Low), Bit::Low);
            assert_eq!(Bit::Low.and(&Bit::Variable), Bit::Low);
            assert_eq!(Bit::Test.and(&Bit::Low), Bit::Low);
        }

        #[test]
        fn and_variable_returns_variable() {
            assert_eq!(Bit::High.and(&Bit::Variable), Bit::Variable);
            assert_eq!(Bit::Variable.and(&Bit::Variable), Bit::Variable);
            assert_eq!(Bit::Variable.and(&Bit::High), Bit::Variable);
        }

        #[test]
        fn and_test_returns_test() {
            assert_eq!(Bit::High.and(&Bit::Test), Bit::Test);
            assert_eq!(Bit::Test.and(&Bit::High), Bit::Test);
            assert_eq!(Bit::Test.and(&Bit::Variable), Bit::Test);
        }

        #[test]
        fn and_is_commutative() {
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Variable];
            for v1 in &bits {
                for v2 in &bits {
                    assert_eq!(v1.and(v2), v2.and(v1))
                }
            }
        }
    }

    // Tests for invert
    mod not {
        use super::*;

        #[test]
        fn not_high_returns_low() {
            assert_eq!(Bit::High.not(), Bit::Low);
        }

        #[test]
        fn not_low_returns_high() {
            assert_eq!(Bit::Low.not(), Bit::High);
        }

        #[test]
        fn not_variable_returns_variable() {
            assert_eq!(Bit::Variable.not(), Bit::Variable);
        }

        #[test]
        fn not_test_returns_test() {
            assert_eq!(Bit::Test.not(), Bit::Test);
        }
    }

    // Or function tests
    mod or {
        use super::*;

        #[test]
        fn or_high_returns_high() {
            assert_eq!(Bit::High.or(&Bit::Low), Bit::High);
            assert_eq!(Bit::High.or(&Bit::Test), Bit::High);
            assert_eq!(Bit::High.or(&Bit::Variable), Bit::High);
        }

        #[test]
        fn or_low_returns_low() {
            assert_eq!(Bit::Low.or(&Bit::Low), Bit::Low);
        }

        #[test]
        fn or_variable_returns_variable() {
            assert_eq!(Bit::Variable.or(&Bit::Low), Bit::Variable);
            assert_eq!(Bit::Variable.or(&Bit::Variable), Bit::Variable);
        }

        #[test]
        fn or_test_returns_test() {
            assert_eq!(Bit::Test.or(&Bit::Low), Bit::Test);
            assert_eq!(Bit::Test.or(&Bit::Variable), Bit::Test);
            assert_eq!(Bit::Test.or(&Bit::Test), Bit::Test);
        }

        #[test]
        fn or_is_commutative() {
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Variable];
            for v1 in &bits {
                for v2 in &bits {
                    assert_eq!(v1.or(v2), v2.or(v1))
                }
            }
        }
    }

    // Tests for xor function
    mod xor {
        use super::*;

        #[test]
        fn xor_one_high_returns_high() {
            assert_eq!(Bit::High.xor(&Bit::Low), Bit::High);
        }

        #[test]
        fn xor_match_returns_low() {
            assert_eq!(Bit::High.xor(&Bit::High), Bit::Low);
            assert_eq!(Bit::Low.xor(&Bit::Low), Bit::Low);
        }

        #[test]
        fn xor_variable_returns_variable() {
            assert_eq!(Bit::Variable.xor(&Bit::High), Bit::Variable);
            assert_eq!(Bit::Variable.xor(&Bit::Low), Bit::Variable);
        }

        #[test]
        fn xor_test_returns_test() {
            assert_eq!(Bit::Test.xor(&Bit::High), Bit::Test);
            assert_eq!(Bit::Test.xor(&Bit::Low), Bit::Test);
        }

        #[test]
        fn xor_is_commutative() {
            let bits = [Bit::Low, Bit::High, Bit::Test, Bit::Variable];
            for v1 in &bits {
                for v2 in &bits {
                    assert_eq!(v1.xor(v2), v2.xor(v1))
                }
            }
        }
    }
}