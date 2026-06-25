// Contains code to evaluate whether two Exprs are semantically equivalent
// Pipeline
//  1. Simple check to see if canonical form of Exprs are equal (if this succeeds great!)
//  2. Random testing to attempt to see if the Exprs are obviously different
//  3. Z3 (easier to program) or Bitwuzla (potentially faster) SMT solver to authoritatively check if the two Exprs are equivalent

// potential constraint for synthesis: never read from a register or memory address unless
//      1. the original instruction read from it (eg if ReadMemory(R4 + 4) is present, you can read from there)
//      2. the new program has already written to it

// TODO multiple threads perchance? command line option
const THREAD_COUNT: u32 = 1;
const INNER_NODE_CAPACITY: usize = 4096;
const APPLY_CACHE_CAPACITY: usize = 2048;

const LEFT_EXPR: bool = true;
const RIGHT_EXPR: bool = false;

use std::{cmp::Reverse, collections::BTreeMap};

use oxidd::{
    BooleanFunction, BooleanFunctionQuant, Manager, ManagerRef,
    bcdd::{BCDDFunction, BCDDManagerRef},
    util::AllocResult,
};

use crate::{
    instruction_semantics::{
        Effect, Expr, OperandRef, RegisterRef, add, concat, constant, extract, or_expr,
        read_memory, select,
    },
    isa_specification::{ArchitecturalRegister, DecodedInstruction, ISA, Instruction},
};

pub type InstructionIdx = u32;

/// A table of all state uses
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateUseTable {
    /// Vector of tuples, saying which index the update is at and
    updates: Vec<(InstructionIdx, StateUse)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateUse {
    Write(StateDestination),
    Read(StateDestination),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateDestination {
    /// Register with identifier - `u8`
    Register(u8),
    /// Memory byte at address - `usize`
    MemoryByte(u32),
}

#[derive(Clone, PartialEq, Eq)]
pub struct MemoryRead {
    read_id: ReadId,
    /// If a memory read is used as the address or destination for another memory read,
    /// then it has a depth of 1. If it is a top level memory read it has a depth of 0. etc.
    depth: u8,
    address_expr: Expr,
    lowered_address: Option<BddWord>,
    width: u16,
    value: BddWord,
}

type VariableId = u32;
type ReadId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VariableDescription {
    Unallocated,
    RegisterBit {
        register: ArchitecturalRegister,
        bit: usize,
    },
    MemoryReadValueBit {
        read_id: ReadId,
        left: bool,
        bit: usize,
    },
}

//NOTE: should probably put this in some other file
// this file should be exclusively for expr matching imo
// should probably also move the instruction to expr function
// or maybe move the bddmanager?
// impl StateUseTable {
//     pub fn from_program(program: &Vec<DecodedInstruction>, isa: &Vec<Instruction>) -> Self {
//         for instruction in program.iter() {
//             let lowered_effects = instruction_to_lowered_effects(instruction, isa, &vec![]);
//         }
//         StateUseTable { updates: () }
//     }
// }

// Cloning is not allowed to enforce exclusive ownership of the manager
// Similarly, manager_ref should never be accessed from outside the struct and
// all BCDDFunctions must be stored in BddManager.
#[derive(PartialEq, Eq)]
pub struct BddManager {
    manager_ref: BCDDManagerRef,

    left_memory_read_table: Vec<MemoryRead>,
    right_memory_read_table: Vec<MemoryRead>,
    variables: Vec<(VariableDescription, BCDDFunction)>,
    left: BddWord,
    right: BddWord,
    constraint: BCDDFunction,

    left_expr: Expr,
    right_expr: Expr,
    registers: Vec<ArchitecturalRegister>,

    true_fn: BCDDFunction,
    false_fn: BCDDFunction,
}

impl BddManager {
    fn new_variable(&mut self, description: VariableDescription) -> BCDDFunction {
        if let Some((existing_description, function)) = self
            .variables
            .iter_mut()
            .find(|(description, _)| *description == VariableDescription::Unallocated)
        {
            *existing_description = description;
            return function.clone();
        }

        let function = self.manager_ref.with_manager_exclusive(|manager| {
            let variable_number = manager
                .add_vars(1)
                .next()
                .expect("Expected one new BCDD variable");

            BCDDFunction::var(&*manager, variable_number).expect("Failed to create BCDD variable")
        });

        self.variables.push((description, function.clone()));
        function
    }

    fn function_uses_variable(
        function: &BCDDFunction,
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        function
            .unique(variable)
            .expect("Failed to check whether a BCDD function uses a variable")
            != *false_fn
    }

    fn word_uses_variable(
        word: &BddWord,
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        word.bits
            .iter()
            .any(|function| Self::function_uses_variable(function, variable, false_fn))
    }

    fn table_uses_variable(
        table: &[MemoryRead],
        variable: &BCDDFunction,
        false_fn: &BCDDFunction,
    ) -> bool {
        table.iter().any(|read| {
            read.lowered_address
                .as_ref()
                .is_some_and(|address| Self::word_uses_variable(address, variable, false_fn))
                || Self::word_uses_variable(&read.value, variable, false_fn)
        })
    }

    fn release_variable(&mut self, variable_index: usize) {
        assert!(
            variable_index < self.variables.len(),
            "Variable index is outside the variable pool"
        );
        assert!(
            self.variables[variable_index].0 != VariableDescription::Unallocated,
            "Variable is already unallocated"
        );

        let variable = self.variables[variable_index].1.clone();
        let false_fn = &self.false_fn;

        let used = Self::word_uses_variable(&self.left, &variable, false_fn)
            || Self::word_uses_variable(&self.right, &variable, false_fn)
            || Self::function_uses_variable(&self.constraint, &variable, false_fn)
            || Self::table_uses_variable(&self.left_memory_read_table, &variable, false_fn)
            || Self::table_uses_variable(&self.right_memory_read_table, &variable, false_fn)
            || Self::function_uses_variable(&self.true_fn, &variable, false_fn)
            || Self::function_uses_variable(&self.false_fn, &variable, false_fn)
            || self
                .variables
                .iter()
                .enumerate()
                .any(|(index, (_, function))| {
                    index != variable_index
                        && Self::function_uses_variable(function, &variable, false_fn)
                });

        assert!(
            !used,
            "Cannot release a variable that is still used by a live BCDD function"
        );

        self.variables[variable_index].0 = VariableDescription::Unallocated;
    }

    pub fn from_exprs(left_expr: Expr, right_expr: Expr, isa: &ISA) -> Self {
        let manager_ref =
            oxidd::bcdd::new_manager(INNER_NODE_CAPACITY, APPLY_CACHE_CAPACITY, THREAD_COUNT);
        let (true_fn, false_fn) = manager_ref
            .with_manager_shared(|manager| (BCDDFunction::t(manager), BCDDFunction::f(manager)));

        let left_width = left_expr.expr_width();
        let right_width = right_expr.expr_width();

        assert_eq!(left_width, right_width, "Expression widths must match");

        let width = left_width.expect("Width of expressions must be defined!");

        // Initialize left and right words
        let left = BddWord {
            bits: Vec::with_capacity(width as usize),
        };
        let right = BddWord {
            bits: Vec::with_capacity(width as usize),
        };

        // Initialize constraint as true_fn
        let constraint = true_fn.clone();

        // Iniitalize variables as vector with capacity equal to the length of the register file
        let registers = isa.registers.clone();
        // let mut variables = Vec::with_capacity(registers.iter().map(|r| r.width as usize).sum::<usize>() as usize);

        // We also want to initialize the register variables
        // This relatively trivial, because we just interleave them
        // First find the maximum register width
        let mut maximum_register_width = 0;
        for register in registers.iter() {
            if register.width > maximum_register_width {
                maximum_register_width = register.width;
            }
        }

        let variables = manager_ref.with_manager_exclusive(|manager| {
            let mut variables = Vec::new();

            for bit in 0..maximum_register_width {
                for register in &registers {
                    // In this case, we have already finished adding the variables for the register
                    // eg if width = 8, bit = 8, we have already added 8 bits (0..=7)
                    if register.width <= bit {
                        continue;
                    }

                    let variable_number =
                        manager.add_vars(1).next().expect("Expected one variable");

                    let function = BCDDFunction::var(&*manager, variable_number)
                        .expect("Failed to allocate BCDD variable");

                    variables.push((
                        VariableDescription::RegisterBit {
                            register: *register,
                            bit: bit.into(),
                        },
                        function,
                    ));
                }
            }

            variables
        });

        let left_memory_read_table = vec![];
        let right_memory_read_table = vec![];

        let mut inst = Self {
            manager_ref,
            left_memory_read_table,
            right_memory_read_table,
            variables,
            left,
            right,
            constraint,
            left_expr,
            right_expr,
            registers,
            true_fn,
            false_fn,
        };
        inst.assign_memory_read_variables(LEFT_EXPR);
        // Right memory read variables should be at the end of the
        // variable pool, because the left variables are static,
        // but the right variables will be periodically cleared and potentially
        // expanded
        inst.assign_memory_read_variables(RIGHT_EXPR);
        inst
    }

    /// Creates the memory read table and creates variables for one expression
    /// If left is true, it creates the memory read table for the left expression
    /// Otherwise, the right expression.
    /// Generally left = true should be run first, and then left = false should
    /// be run repeatedly as different RHS are tried.
    fn assign_memory_read_variables(&mut self, left: bool) {
        let existing_table = if left {
            &self.left_memory_read_table
        } else {
            &self.right_memory_read_table
        };

        assert_eq!(
            existing_table.len(),
            0,
            "Memory read table should be cleared before running assign_memory_read_variables. Use replace_right_expr to clear variables and the table."
        );

        // Traverse the expression to build one table entry per memory-read occurrence.
        // Read IDs and value variables are assigned afterward in depth order.

        /// Recursively collects memory reads into a skeleton memory-read table.
        fn traverse_expr(
            expr: &Expr,
            depth: u8,
            next_read_id: &mut u32,
            memory_read_table: &mut Vec<MemoryRead>,
        ) {
            match expr {
                Expr::ReadMemory { address, width } => {
                    traverse_expr(address, depth + 1, next_read_id, memory_read_table);
                    // Equivalent reads share one entry, kept at their greatest
                    // observed depth so address dependencies are ordered first.
                    if let Some(read) = memory_read_table
                        .iter_mut()
                        .find(|read| read.address_expr == **address && read.width == *width)
                    {
                        read.depth = read.depth.max(depth);
                    } else {
                        memory_read_table.push(MemoryRead {
                            read_id: *next_read_id,
                            depth,
                            address_expr: *address.clone(),
                            lowered_address: None,
                            width: *width,
                            value: BddWord { bits: vec![] },
                        });
                        *next_read_id += 1;
                    }
                }
                any_expr => {
                    any_expr.visit_children(|child| {
                        traverse_expr(child, depth, next_read_id, memory_read_table)
                    });
                }
            }
        }

        let mut table = Vec::new();
        let mut next_read_id = 0;
        if left {
            traverse_expr(&self.left_expr, 0, &mut next_read_id, &mut table);
        } else {
            traverse_expr(&self.right_expr, 0, &mut next_read_id, &mut table);
        }

        // Assign lower read IDs to deeper reads so address dependencies are
        // processed before the reads that use them. Variables are ordered by
        // descending depth and then interleaved by bit within each depth.
        let Some(max_depth) = table.iter().map(|read| read.depth).max() else {
            return;
        };
        let mut next_read_id: ReadId = 0;
        for depth_level in (0..=max_depth).rev() {
            // Preserve table order within this depth.
            let read_indices: Vec<usize> = table
                .iter()
                .enumerate()
                .filter_map(|(index, read)| (read.depth == depth_level).then_some(index))
                .collect();

            // Assign read IDs before creating their bit variables.
            for &index in &read_indices {
                let read = &mut table[index];

                read.read_id = next_read_id;
                next_read_id += 1;

                read.value.bits.reserve(read.width as usize);
            }

            // Get maximum read bit-width
            let maximum_read_width = read_indices
                .iter()
                .map(|&index| table[index].width)
                .max()
                .unwrap_or(0);
            // Now we want to iterate through each read at this depth, and update `value.bits`
            // We also want to go bit by bit just like constructing the registers
            // Bit-major ordering creates the desired interleaving:
            //
            // read A bit 0
            // read B bit 0
            // read A bit 1
            // read B bit 1
            // ...
            for bit in 0..maximum_read_width {
                for &index in &read_indices {
                    let read = &table[index];

                    if bit >= read.width {
                        continue;
                    }

                    let read_id = read.read_id;
                    let function = self.new_variable(VariableDescription::MemoryReadValueBit {
                        read_id,
                        left,
                        bit: bit as usize,
                    });

                    table[index].value.bits.push(function);
                }
            }
        }

        if left {
            self.left_memory_read_table = table;
        } else {
            self.right_memory_read_table = table;
        }
    }

    /// Removes the `right` expression along with variables,
    /// and replaces it with another expr
    /// Effectively, it should act like running from_exprs, but saves computation
    /// by only replacing the one which needs to be replaced
    /// After this, constraints are also gone and need to be rebuilt.
    /// The only thing that doesn't need to be rebuilt is the other Expr
    /// which was not replaced.
    pub fn replace_right_expr(&mut self, new_expr: Expr) {
        let expected_width = self
            .left_expr
            .expr_width()
            .expect("Width of existing expression should be defined");

        assert_eq!(
            new_expr
                .expr_width()
                .expect("Width of new_expr should be defined"),
            expected_width,
            "new_expr width should match existing expression widths"
        );

        self.right.bits.clear();
        self.right_memory_read_table.clear();
        self.constraint = self.true_fn.clone();
        self.right_expr = new_expr;

        let right_variable_indices: Vec<usize> = self
            .variables
            .iter()
            .enumerate()
            .filter_map(|(index, (description, _))| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit { left: false, .. }
                )
                .then_some(index)
            })
            .collect();

        for variable_index in right_variable_indices {
            self.release_variable(variable_index);
        }

        self.manager_ref.with_manager_shared(|manager| {
            manager.gc();
        });

        self.assign_memory_read_variables(RIGHT_EXPR);
    }

    /// Lowers an expression
    pub fn lower_expression(&self, expr: &Expr, left: bool) -> BddWord {
        self.try_lower_expression(expr, left)
            .expect("BCDD node allocation failed")
    }

    fn try_lower_expression(&self, expr: &Expr, left: bool) -> AllocResult<BddWord> {
        match expr {
            Expr::Const { value, width } => Ok(self.lower_constant(*value, *width)),

            Expr::ReadRegister { register, width } => {
                let selector = self.try_lower_expression(register, left)?;
                self.lower_register_read(selector, *width)
            }

            // This is the only valid Operand
            // Other Operands involve references to fields
            // This should collapse to the register identifier
            Expr::Operand(OperandRef::RegisterField(RegisterRef::Fixed {
                register,
                identifier_width,
            })) => Ok(self.lower_constant(register.0 as u128, *identifier_width)),

            Expr::ReadMemory { address, width } => {
                let table = if left {
                    &self.left_memory_read_table
                } else {
                    &self.right_memory_read_table
                };

                let read = table
                    .iter()
                    .find(|read| read.address_expr == **address && read.width == *width)
                    .unwrap_or_else(|| {
                        panic!("memory read missing from table: address={address:?}, width={width}")
                    });

                Ok(read.value.clone())
            }

            Expr::Add(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_add(op1_lowered, op2_lowered)
            }

            Expr::Mul(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_mul(op1_lowered, op2_lowered)
            }

            Expr::And(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_and(op1_lowered, op2_lowered)
            }

            Expr::Not(op) => {
                let op_lowered = self.try_lower_expression(op, left)?;
                self.lower_not(op_lowered)
            }

            Expr::ShiftLeft(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_shift_left(value_lowered, amount_lowered)
            }

            Expr::LogicalShiftRight(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_logical_shift_right(value_lowered, amount_lowered)
            }

            Expr::ArithmeticShiftRight(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_arithmetic_shift_right(value_lowered, amount_lowered)
            }

            Expr::RotateRight(value, amount) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                let amount_lowered = self.try_lower_expression(amount, left)?;
                self.lower_rotate_right(value_lowered, amount_lowered)
            }

            Expr::Equal(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_equal(op1_lowered, op2_lowered)
            }

            Expr::UnsignedLessThan(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_unsigned_lt(op1_lowered, op2_lowered)
            }

            Expr::SignedLessThan(op1, op2) => {
                let op1_lowered = self.try_lower_expression(op1, left)?;
                let op2_lowered = self.try_lower_expression(op2, left)?;
                self.lower_signed_lt(op1_lowered, op2_lowered)
            }

            Expr::Extract { value, high, low } => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_extract(value_lowered, *high, *low)
            }

            Expr::Concat(exprs) => {
                let exprs_lowered = exprs
                    .iter()
                    .map(|e| self.try_lower_expression(e, left))
                    .collect::<AllocResult<Vec<BddWord>>>()?;
                self.lower_concat(exprs_lowered)
            }

            Expr::ZeroExtend { value, to_width } => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_zero_extend(value_lowered, *to_width)
            }

            Expr::SignExtend { value, to_width } => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_sign_extend(value_lowered, *to_width)
            }

            Expr::CountOnes(value) => {
                let value_lowered = self.try_lower_expression(value, left)?;
                self.lower_count_ones(value_lowered)
            }

            Expr::AddCarryOut {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs_lowered = self.try_lower_expression(lhs, left)?;
                let rhs_lowered = self.try_lower_expression(rhs, left)?;
                let cin_lowered = self.try_lower_expression(carry_in, left)?;
                self.lower_add_cout(lhs_lowered, rhs_lowered, cin_lowered, *width)
            }

            Expr::AddOverflow {
                lhs,
                rhs,
                carry_in,
                width,
            } => {
                let lhs_lowered = self.try_lower_expression(lhs, left)?;
                let rhs_lowered = self.try_lower_expression(rhs, left)?;
                let cin_lowered = self.try_lower_expression(carry_in, left)?;
                self.lower_add_overflow(lhs_lowered, rhs_lowered, cin_lowered, *width)
            }
            // Anything else should not show up in properly canonicalied expressions
            expr => {
                unreachable!("encountered Expr which should not appear in canonical form: {expr:?}")
            }
        }
    }

    fn lower_constant(&self, value: u128, width: u16) -> BddWord {
        assert!(width <= 128);

        let bits = (0..width)
            .map(|bit| {
                if ((value >> bit) & 1) != 0 {
                    self.true_fn.clone()
                } else {
                    self.false_fn.clone()
                }
            })
            .collect();

        BddWord { bits }
    }

    fn lower_bitwise_binary<F>(
        &self,
        lhs: BddWord,
        rhs: BddWord,
        operation: F,
    ) -> AllocResult<BddWord>
    where
        F: Fn(&BCDDFunction, &BCDDFunction) -> AllocResult<BCDDFunction>,
    {
        assert_eq!(lhs.bits.len(), rhs.bits.len());

        let bits = lhs
            .bits
            .iter()
            .zip(&rhs.bits)
            .map(|(lhs, rhs)| operation(lhs, rhs))
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    /// Simple 2-1 mux
    fn mux_word(
        &self,
        condition: &BCDDFunction,
        when_true: &BddWord,
        when_false: &BddWord,
    ) -> AllocResult<BddWord> {
        assert_eq!(when_true.bits.len(), when_false.bits.len());

        let bits = when_true
            .bits
            .iter()
            .zip(&when_false.bits)
            .map(|(true_bit, false_bit)| condition.ite(true_bit, false_bit))
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    /// Lowers a register read and builds a register mux to select the register contents
    /// Selects from all registers of width `width` and `identifier_width == selector.bits.len()`
    fn lower_register_read(&self, selector: BddWord, width: u16) -> AllocResult<BddWord> {
        assert!(
            selector.bits.len() <= 8,
            "register selector exceeds u8 identifier width"
        );
        let ident_width = selector.bits.len() as u8;
        // Temporarily initialize registers as all low
        // Technically it is not guaranteed that all bits are overriden.
        // As such, it is possible for these bits to "poison" the output
        // if the `selector` isn't selecting a valid register for the given `selector_width` and width
        let mut registers = vec![
            BddWord {
                bits: vec![self.false_fn.clone(); width as usize]
            };
            1usize << ident_width
        ];
        for (description, variable) in self.variables.iter() {
            let VariableDescription::RegisterBit { register, bit } = description else {
                // This isn't the right type of read!
                continue;
            };
            if register.width != width as u8 {
                continue;
            }
            if register.identifier_width != ident_width {
                continue;
            }

            if register.identifier as usize >= (1usize << register.identifier_width) {
                panic!("Register identifier too large for its identifier width!");
            }

            // This is safe because we have a guarantee on the length of the registers vec
            let reg_mut = &mut registers[register.identifier as usize];
            reg_mut.bits[*bit] = variable.clone();
        }

        // First layer: LSB selection bit (0 = even registers, 1 = odd)
        // Second layer: second LSB (0 = multiple of 4, 1 = multiple of 4 + 2)
        // and so on
        for selector_bit in &selector.bits {
            let mut next = Vec::with_capacity(registers.len() / 2);

            for pair in registers.chunks_exact(2) {
                let selected = self.mux_word(
                    selector_bit,
                    &pair[1], // selector bit = 1
                    &pair[0], // selector bit = 0
                )?;

                next.push(selected);
            }

            registers = next;
        }
        assert_eq!(registers.len(), 1);
        Ok(registers.pop().unwrap())
    }

    fn full_adder(
        a: &BCDDFunction,
        b: &BCDDFunction,
        carry_in: &BCDDFunction,
    ) -> AllocResult<(BCDDFunction, BCDDFunction)> {
        let a_xor_b = a.xor(b)?;

        let sum = a_xor_b.xor(carry_in)?;

        let generated = a.and(b)?;
        let propagated = a_xor_b.and(carry_in)?;
        let carry_out = generated.or(&propagated)?;

        Ok((sum, carry_out))
    }

    /// Lowers an addition expression
    fn lower_add(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        assert_eq!(op1.bits.len(), op2.bits.len());
        let width = op1.bits.len();

        let mut result = Vec::with_capacity(width);
        let mut carry = self.false_fn.clone();

        for bit in 0..width {
            let (sum, next_carry) = Self::full_adder(&op1.bits[bit], &op2.bits[bit], &carry)?;

            result.push(sum);
            carry = next_carry;
        }

        Ok(BddWord { bits: result })
    }

    /// Helper function to shift left by a constant
    fn shift_left_const(&self, value: &BddWord, amount: usize) -> BddWord {
        let width = value.bits.len();
        let mut result = vec![self.false_fn.clone(); width];
        for source in 0..value.bits.len() {
            let destination = source + amount;

            if destination < width {
                result[destination] = value.bits[source].clone();
            }
        }

        BddWord { bits: result }
    }

    /// Helper function to mask a word by a single bit (eg 0b101 & 0b0 = 0b000)
    fn mask_word(&self, condition: &BCDDFunction, value: &BddWord) -> AllocResult<BddWord> {
        let bits = value
            .bits
            .iter()
            .map(|bit| bit.and(condition))
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    /// Lowers a multiplication expression
    /// Takes two operands of some `width` and returns a BddWord of `width`
    fn lower_mul(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        assert_eq!(op1.bits.len(), op2.bits.len());
        let width = op1.bits.len();
        let mut result = BddWord {
            bits: vec![self.false_fn.clone(); width],
        };

        // Shift and add combinatorial multiplier
        // a*b = sum(bi * (a << i))
        for multiplier_bit in 0..width {
            let shifted = self.shift_left_const(&op1, multiplier_bit);

            let partial_product = self.mask_word(&op2.bits[multiplier_bit], &shifted)?;

            result = self.lower_add(result, partial_product)?;
        }

        Ok(result)
    }

    /// Lowers a bitwise and expression
    fn lower_and(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        self.lower_bitwise_binary(op1, op2, |lhs_bit, rhs_bit| lhs_bit.and(rhs_bit))
    }

    /// Lowers bitwise not
    fn lower_not(&self, op: BddWord) -> AllocResult<BddWord> {
        let bits = op
            .bits
            .iter()
            .map(|bit| bit.not())
            .collect::<AllocResult<Vec<_>>>()?;

        Ok(BddWord { bits })
    }

    /// Lowers shift left
    fn lower_shift_left(&self, value: BddWord, amount: BddWord) -> AllocResult<BddWord> {
        todo!("not implementated")
    }

    /// Lowers logical shift right
    fn lower_logical_shift_right(&self, value: BddWord, amount: BddWord) -> AllocResult<BddWord> {
        todo!("not implementated")
    }

    /// Lowers arithmetic shift right
    fn lower_arithmetic_shift_right(
        &self,
        value: BddWord,
        amount: BddWord,
    ) -> AllocResult<BddWord> {
        todo!("not implementated")
    }

    /// Lowers rotate right
    fn lower_rotate_right(&self, value: BddWord, amount: BddWord) -> AllocResult<BddWord> {
        todo!("not implementated")
    }

    /// Lowers bitwise equals operation
    fn lower_equal(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers unsigned less than
    fn lower_unsigned_lt(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers signed less than
    fn lower_signed_lt(&self, op1: BddWord, op2: BddWord) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers bit extraction
    fn lower_extract(&self, value: BddWord, high: u16, low: u16) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers concatenation
    fn lower_concat(&self, values: Vec<BddWord>) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers zero extension
    fn lower_zero_extend(&self, value: BddWord, to_width: u16) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers sign extension
    fn lower_sign_extend(&self, value: BddWord, to_width: u16) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers counting ones
    fn lower_count_ones(&self, value: BddWord) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers add carry out
    fn lower_add_cout(
        &self,
        lhs: BddWord,
        rhs: BddWord,
        carry_in: BddWord,
        width: u16,
    ) -> AllocResult<BddWord> {
        todo!("not implemented")
    }

    /// Lowers add overflow flag bit
    fn lower_add_overflow(
        &self,
        lhs: BddWord,
        rhs: BddWord,
        carry_in: BddWord,
        width: u16,
    ) -> AllocResult<BddWord> {
        todo!("not implemented")
    }
}

/// A word which is created by a vector of BCDDs
/// So, each bit is defined by some function.
#[derive(Clone, PartialEq, Eq)]
pub struct BddWord {
    /// bits[0] is the least-significant bit.
    pub bits: Vec<BCDDFunction>,
}

/// Given some sequence of instructions, create a list of all Effects of the sequence in terms of the initial state
/// Includes lowering memory accesses to single-byte accesses
/// This effectively collapses instructions.len() = k instructions into a single state update u where s(t0+k) = u(s(t0))
pub fn instruction_seq_to_effects(instructions: &[DecodedInstruction], isa: &ISA) -> Vec<Effect> {
    let mut seq_effects = vec![];
    for instruction in instructions.iter() {
        let lowered_effects = instruction_to_lowered_effects(instruction, isa, &seq_effects);

        // We want to combine the effects of this instruction with the existing effects in seq_effects
        // The variable name effect_2 refers to the fact that it takes place after the effect_1s that we are comparing it to
        for effect_2 in lowered_effects {
            // Whether we've found an effect in seq_effects which writes to the same place as effect_2
            let mut found_same_write = false;
            for effect_1 in seq_effects.iter_mut() {
                if let Some(new_effect) = combine_effects(effect_1, &effect_2) {
                    *effect_1 = new_effect;
                    found_same_write = true;
                }
            }

            // If effect_2 didn't contribute itself to an existing effect in seq_effects, we want to add it
            if !found_same_write {
                // However, we don't want to add it if the effect_2.guard is a constant 0
                let guard = match effect_2 {
                    Effect::WriteMemory { ref guard, .. } => guard,
                    Effect::WriteRegister { ref guard, .. } => guard,
                };
                if *guard != constant(0, 1) {
                    seq_effects.push(effect_2);
                }
            }
        }
    }
    seq_effects
}

pub fn instruction_to_lowered_effects(
    instruction: &DecodedInstruction,
    isa: &ISA,
    previous_effects: &[Effect],
) -> Vec<Effect> {
    let instruction_name = instruction
        .name
        .as_ref()
        .expect("Instruction should have a name");
    let instruction_effects = &isa.instructions
        .iter()
        .find(|candidate| candidate.name == *instruction_name)
        .unwrap_or_else(|| {
            panic!(
                "Instruction in sequence should match with an instruction in the ISA, but {instruction_name} did not match!"
            )
        })
        .effects;
    let mut lowered_effects = Vec::with_capacity(instruction_effects.len());
    for effect in instruction_effects.iter().cloned() {
        match effect {
            Effect::WriteMemory {
                guard,
                address,
                value,
                width,
            } => {
                let guard = collapse_lower_substitute(guard, instruction, previous_effects);
                let address = collapse_lower_substitute(address, instruction, previous_effects);
                let value = collapse_lower_substitute(value, instruction, previous_effects);
                if width == 8 {
                    lowered_effects.push(Effect::WriteMemory {
                        guard,
                        address,
                        value,
                        width,
                    });
                } else {
                    assert_eq!(width % 8, 0, "Memory write width must be byte-aligned");
                    let address_width = address
                        .expr_width()
                        .expect("Memory address should have established width");
                    for byte_index in 0..(width / 8) {
                        let low = byte_index * 8;
                        lowered_effects.push(Effect::WriteMemory {
                            guard: guard.clone(),
                            address: byte_address(&address, byte_index, address_width),
                            value: extract(value.clone(), low + 7, low),
                            width: 8,
                        });
                    }
                }
            }
            Effect::WriteRegister {
                guard,
                register,
                value,
            } => {
                let guard = collapse_lower_substitute(guard, instruction, previous_effects);
                let register = collapse_lower_substitute(register, instruction, previous_effects);
                let value = collapse_lower_substitute(value, instruction, previous_effects);
                lowered_effects.push(Effect::WriteRegister {
                    guard,
                    register,
                    value,
                });
            }
        }
    }

    lowered_effects
}

fn collapse_lower_substitute(
    expr: Expr,
    instruction: &DecodedInstruction,
    previous_effects: &[Effect],
) -> Expr {
    lower_memory_reads(expr.collapse(instruction))
        .substitute(previous_effects)
        .canonicalize()
}

fn lower_memory_reads(expr: Expr) -> Expr {
    match expr {
        Expr::ReadMemory { address, width } => {
            let address = lower_memory_reads(*address);
            if width == 8 {
                return read_memory(address, width);
            }

            assert_eq!(width % 8, 0, "Memory read width must be byte-aligned");
            let address_width = address
                .expr_width()
                .expect("Memory address should have established width");
            concat((0..(width / 8)).rev().map(|byte_index| {
                read_memory(byte_address(&address, byte_index, address_width), 8)
            }))
        }
        expr => expr.map_children(lower_memory_reads),
    }
}

fn byte_address(address: &Expr, byte_index: u16, address_width: u16) -> Expr {
    if byte_index == 0 {
        address.clone()
    } else {
        add(address.clone(), constant(byte_index as u128, address_width))
    }
}

/// Given two effects which either both write to the same register or memory, combine
/// their values and guards to create one effect
/// Returns Some(Effect) if the two effects are equivalent writes (ie same location), returns None otherwise
/// # Arguments
/// * `effect_1` - an Effect
/// * `effect_2` - an Effect which takes place sequentially after `effect_1``
fn combine_effects(effect_1: &Effect, effect_2: &Effect) -> Option<Effect> {
    // Let's call these effects a (effect_1) and b (effect_2). a comes before b
    // It is given that effect_1.guard is not always 0
    // The value of the combined effect is as follows:
    // if b.guard -> b.value
    // elif a.guard -> a.value
    // else old value
    // So we can do the following:
    //      1. The new Effect has a guard of a.guard || b.guard
    //      2. The new Effect has a value of b.guard ? b.value : a.value (equivalent to Expr::Select)
    //          - This is the case because (a.guard || b.guard) && !b.guard => a.guard
    // Importantly this process works multiple times (i.e. combine_effects(combine_effects(a, b), c) works)
    // So if now I have a new effect c, it still works to use the exact methodology.
    // We get a new Effect:
    //      guard = a.guard || b.guard || c.guard
    //      value = c.guard ? c.value : (b.guard ? b.value : a.value)
    //          Essentially: if c => c, elif b => b, elif a => a
    // So, the generalized new effect is:
    // Effect {
    //      guard = Or(old_effect.guard, new_effect.guard),
    //      value = Select(new_effect.guard, new_effect.value, old_effect.value)
    // }
    //
    // Importantly there are a few things which can be done in certain cases
    //  1. if effect_2.guard = 0, do nothing
    //  2. if effect_2.guard = 1, return effect_2 as the combined effect
    //  3. if effect_2.guard == effect_1.guard, return effect_2 as the combined effect
    // More generically, if effect_1.guard => effect_2.guard, then effect_2 is the combined effect
    // but that's complicated to check for.
    let memory_effect;
    let guard_1;
    let guard_2;
    let location;
    let value_1;
    let value_2;
    let val_width;
    match effect_1 {
        Effect::WriteMemory {
            guard,
            address,
            value,
            width,
        } => {
            memory_effect = true;
            guard_1 = guard;
            location = address;
            value_1 = value;
            val_width = *width;
        }
        Effect::WriteRegister {
            guard,
            register,
            value,
        } => {
            memory_effect = false;
            guard_1 = guard;
            location = register;
            value_1 = value;
            val_width = value
                .expr_width()
                .expect("Register writes should have established width!");
        }
    }

    // Now make sure effect_2 matches effect_1 and extract values
    match effect_2 {
        Effect::WriteMemory {
            guard,
            address,
            value,
            width,
        } => {
            if !memory_effect {
                return None;
            }
            if location != address {
                // Both must be at the same location to combine
                return None;
            }
            assert_eq!(
                val_width, *width,
                "effect_1 and effect_2 should have same memory write width"
            );

            guard_2 = guard;
            value_2 = value;
        }
        Effect::WriteRegister {
            guard,
            register,
            value,
        } => {
            if memory_effect {
                return None;
            }

            if location != register {
                return None;
            }
            assert_eq!(
                val_width,
                value
                    .expr_width()
                    .expect("Register writes should have established width!"),
                "effect_1 and effect_2 must have the same register write width"
            );

            guard_2 = guard;
            value_2 = value;
        }
    }

    // If effect_2.guard == 1
    if *guard_2 == constant(1, 1) {
        return Some(effect_2.clone());
    }

    // If effect_2.guard == 0
    if *guard_2 == constant(0, 1) {
        return Some(effect_1.clone());
    }

    // If effect_2.guard == effect_1.guard
    if guard_1 == guard_2 {
        return Some(effect_2.clone());
    }

    // Now, construct a new effect
    if memory_effect {
        Some(Effect::WriteMemory {
            guard: or_expr(guard_1.clone(), guard_2.clone()),
            address: location.clone(),
            value: select(guard_2.clone(), value_2.clone(), value_1.clone()),
            width: val_width,
        })
    } else {
        Some(Effect::WriteRegister {
            guard: or_expr(guard_1.clone(), guard_2.clone()),
            register: location.clone(),
            value: select(guard_2.clone(), value_2.clone(), value_1.clone()),
        })
    }
}

// Also this file may perhaps end up with the code to match all the `Effect`s of multiple instructions? or in superoptimization.rs have not decided

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instruction_semantics::{Register, bool_const, fixed_register, read_memory, read_register},
        isa_specification::InstructionForm,
    };

    fn decoded(name: &str) -> DecodedInstruction {
        DecodedInstruction {
            name: Some(name.to_owned()),
            form: Some(InstructionForm::new(format!("{name}_form"))),
            bits: Vec::new(),
            fields: Vec::new(),
        }
    }

    fn isa_instruction(name: &str, effects: Vec<Effect>) -> Instruction {
        let mut instruction = Instruction::new(name, 0);
        instruction.effects = effects;
        instruction
    }

    fn reg(register: u8) -> Expr {
        fixed_register(Register(register), 8)
    }

    fn read_reg(register: u8) -> Expr {
        read_register(reg(register), 32)
    }

    fn register_write_value(effects: &[Effect], register: u8) -> &Expr {
        effects
            .iter()
            .find_map(|effect| match effect {
                Effect::WriteRegister {
                    register: effect_register,
                    value,
                    ..
                } if *effect_register == reg(register) => Some(value),
                _ => None,
            })
            .expect("expected register write")
    }

    fn bdd_test_isa() -> ISA {
        ISA {
            registers: vec![ArchitecturalRegister {
                identifier: 0,
                identifier_width: 1,
                width: 1,
            }],
            instructions: vec![],
        }
    }

    fn manager_variable_count(manager: &BddManager) -> u32 {
        manager
            .manager_ref
            .with_manager_shared(|manager| manager.num_vars())
    }

    fn bdd_manager_for_width(width: u16) -> BddManager {
        BddManager::from_exprs(
            constant(0, width),
            constant(0, width),
            &ISA {
                registers: vec![],
                instructions: vec![],
            },
        )
    }

    fn constant_bdd_word_value(manager: &BddManager, word: &BddWord) -> u128 {
        word.bits
            .iter()
            .enumerate()
            .map(|(bit, function)| {
                if *function == manager.true_fn {
                    1u128 << bit
                } else {
                    assert!(
                        *function == manager.false_fn,
                        "expected a constant BCDD bit"
                    );
                    0
                }
            })
            .sum()
    }

    fn eval_bdd_word(word: &BddWord, assignment: &[(u32, bool)]) -> u128 {
        word.bits
            .iter()
            .enumerate()
            .map(|(bit, function)| {
                if function.eval(assignment.iter().copied()) {
                    1u128 << bit
                } else {
                    0
                }
            })
            .sum()
    }

    #[test]
    fn lower_constant_uses_little_endian_bits_and_truncates_to_width() {
        let manager = bdd_manager_for_width(8);

        let word = manager.lower_constant(0b1_1010_0101, 8);

        assert_eq!(constant_bdd_word_value(&manager, &word), 0b1010_0101);
        assert_eq!(word.bits.len(), 8);
    }

    #[test]
    fn mux_word_selects_the_requested_word() {
        let manager = bdd_manager_for_width(4);
        let when_true = manager.lower_constant(0b1010, 4);
        let when_false = manager.lower_constant(0b0101, 4);

        let selected_true = manager
            .mux_word(&manager.true_fn, &when_true, &when_false)
            .unwrap();
        let selected_false = manager
            .mux_word(&manager.false_fn, &when_true, &when_false)
            .unwrap();

        assert_eq!(constant_bdd_word_value(&manager, &selected_true), 0b1010);
        assert_eq!(constant_bdd_word_value(&manager, &selected_false), 0b0101);
    }

    #[test]
    fn full_adder_matches_all_truth_table_rows() {
        let manager = bdd_manager_for_width(1);

        for a in [false, true] {
            for b in [false, true] {
                for carry_in in [false, true] {
                    let a_fn = if a {
                        &manager.true_fn
                    } else {
                        &manager.false_fn
                    };
                    let b_fn = if b {
                        &manager.true_fn
                    } else {
                        &manager.false_fn
                    };
                    let carry_fn = if carry_in {
                        &manager.true_fn
                    } else {
                        &manager.false_fn
                    };

                    let (sum, carry_out) = BddManager::full_adder(a_fn, b_fn, carry_fn).unwrap();
                    let total = a as u8 + b as u8 + carry_in as u8;

                    assert_eq!(sum == manager.true_fn, total & 1 != 0);
                    assert_eq!(carry_out == manager.true_fn, total >= 2);
                }
            }
        }
    }

    #[test]
    fn lower_add_matches_wrapping_addition_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(width);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    let result = manager
                        .lower_add(
                            manager.lower_constant(lhs, width),
                            manager.lower_constant(rhs, width),
                        )
                        .unwrap();

                    assert_eq!(
                        constant_bdd_word_value(&manager, &result),
                        (lhs + rhs) & (limit - 1),
                        "width={width}, lhs={lhs}, rhs={rhs}"
                    );
                }
            }
        }
    }

    #[test]
    fn shift_left_const_matches_wrapping_bitvector_shift() {
        let width = 6;
        let manager = bdd_manager_for_width(width);
        let mask = (1u128 << width) - 1;

        for value in 0..=mask {
            for amount in 0..=(width as usize + 1) {
                let shifted =
                    manager.shift_left_const(&manager.lower_constant(value, width), amount);

                assert_eq!(
                    constant_bdd_word_value(&manager, &shifted),
                    (value << amount) & mask,
                    "value={value}, amount={amount}"
                );
            }
        }
    }

    #[test]
    fn mask_word_selects_value_or_zero() {
        let manager = bdd_manager_for_width(5);

        for value in 0..32 {
            let value_word = manager.lower_constant(value, 5);
            let included = manager.mask_word(&manager.true_fn, &value_word).unwrap();
            let excluded = manager.mask_word(&manager.false_fn, &value_word).unwrap();

            assert_eq!(constant_bdd_word_value(&manager, &included), value);
            assert_eq!(constant_bdd_word_value(&manager, &excluded), 0);
        }
    }

    #[test]
    fn lower_mul_matches_wrapping_multiplication_exhaustively() {
        for width in 1..=6 {
            let manager = bdd_manager_for_width(width);
            let limit = 1u128 << width;

            for lhs in 0..limit {
                for rhs in 0..limit {
                    let result = manager
                        .lower_mul(
                            manager.lower_constant(lhs, width),
                            manager.lower_constant(rhs, width),
                        )
                        .unwrap();

                    assert_eq!(
                        constant_bdd_word_value(&manager, &result),
                        (lhs * rhs) & (limit - 1),
                        "width={width}, lhs={lhs}, rhs={rhs}"
                    );
                }
            }
        }
    }

    #[test]
    fn lower_mul_matches_64_bit_wrapping_multiplication() {
        let manager = bdd_manager_for_width(64);
        let cases = [
            (0, u64::MAX),
            (1, u64::MAX),
            (u64::MAX, u64::MAX),
            (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
            (1u64 << 63, 2),
        ];

        for (lhs, rhs) in cases {
            let result = manager
                .lower_mul(
                    manager.lower_constant(lhs as u128, 64),
                    manager.lower_constant(rhs as u128, 64),
                )
                .unwrap();
            let result_value = constant_bdd_word_value(&manager, &result);

            assert_eq!(
                result_value,
                lhs.wrapping_mul(rhs) as u128,
                "lhs={lhs:#018x}, rhs={rhs:#018x}"
            );
            println!("opa={lhs:#018x}, opb={rhs:#018x}, result={result_value:#018x}");
        }
    }

    #[test]
    fn lower_and_and_not_match_bitwise_semantics_exhaustively() {
        let width = 5;
        let manager = bdd_manager_for_width(width);
        let mask = (1u128 << width) - 1;

        for lhs in 0..=mask {
            let not_result = manager
                .lower_not(manager.lower_constant(lhs, width))
                .unwrap();
            assert_eq!(
                constant_bdd_word_value(&manager, &not_result),
                (!lhs) & mask
            );

            for rhs in 0..=mask {
                let and_result = manager
                    .lower_and(
                        manager.lower_constant(lhs, width),
                        manager.lower_constant(rhs, width),
                    )
                    .unwrap();
                assert_eq!(constant_bdd_word_value(&manager, &and_result), lhs & rhs);
            }
        }
    }

    #[test]
    fn lower_register_read_muxes_symbolic_selectors() {
        let registers = (0..4)
            .map(|identifier| ArchitecturalRegister {
                identifier,
                identifier_width: 2,
                width: 3,
            })
            .collect();
        let selector_expr = read_memory(constant(0x100, 32), 2);
        let manager = BddManager::from_exprs(
            selector_expr,
            constant(0, 2),
            &ISA {
                registers,
                instructions: vec![],
            },
        );
        let selector = manager.left_memory_read_table[0].value.clone();
        let result = manager.lower_register_read(selector, 3).unwrap();
        let register_values = [0b001u128, 0b010, 0b100, 0b111];

        for selected_register in 0..4 {
            let assignment: Vec<_> = manager
                .variables
                .iter()
                .enumerate()
                .map(|(variable, (description, _))| {
                    let value = match description {
                        VariableDescription::RegisterBit { register, bit } => {
                            (register_values[register.identifier as usize] >> bit) & 1 != 0
                        }
                        VariableDescription::MemoryReadValueBit {
                            left: true, bit, ..
                        } => (selected_register >> bit) & 1 != 0,
                        _ => false,
                    };
                    (variable as u32, value)
                })
                .collect();

            assert_eq!(
                eval_bdd_word(&result, &assignment),
                register_values[selected_register],
                "selected_register={selected_register}"
            );
        }
    }

    #[test]
    fn bdd_manager_interleaves_memory_read_variables_by_bit() {
        let left_expr = concat([
            read_memory(constant(0x100, 32), 8),
            read_memory(constant(0x200, 32), 16),
        ]);
        let manager = BddManager::from_exprs(left_expr, constant(0, 24), &bdd_test_isa());

        let descriptions: Vec<_> = manager
            .variables
            .iter()
            .filter_map(|(description, _)| match description {
                VariableDescription::MemoryReadValueBit {
                    read_id,
                    left: true,
                    bit,
                } => Some((*read_id, *bit)),
                _ => None,
            })
            .collect();

        let mut expected = Vec::new();
        for bit in 0..8 {
            expected.push((0, bit));
            expected.push((1, bit));
        }
        for bit in 8..16 {
            expected.push((1, bit));
        }

        assert_eq!(descriptions, expected);
    }

    #[test]
    fn bdd_manager_assigns_nested_memory_reads_deepest_first() {
        let nested_address = read_memory(constant(0x100, 32), 32);
        let manager = BddManager::from_exprs(
            read_memory(nested_address, 8),
            constant(0, 8),
            &bdd_test_isa(),
        );

        let reads: Vec<_> = manager
            .left_memory_read_table
            .iter()
            .map(|read| (read.read_id, read.depth, read.width))
            .collect();

        assert_eq!(reads, vec![(0, 1, 32), (1, 0, 8)]);
    }

    #[test]
    fn duplicate_memory_read_keeps_greatest_observed_depth() {
        let shared_read = read_memory(constant(0x100, 32), 32);
        let manager = BddManager::from_exprs(
            concat([shared_read.clone(), read_memory(shared_read.clone(), 8)]),
            constant(0, 40),
            &bdd_test_isa(),
        );

        let shared_entry = manager
            .left_memory_read_table
            .iter()
            .find(|read| read.address_expr == constant(0x100, 32) && read.width == 32)
            .expect("expected deduplicated shared memory read");

        assert_eq!(shared_entry.depth, 1);
        assert_eq!(
            manager
                .left_memory_read_table
                .iter()
                .filter(|read| { read.address_expr == constant(0x100, 32) && read.width == 32 })
                .count(),
            1
        );
    }

    #[test]
    fn lower_memory_read_returns_the_assigned_value_word() {
        let memory_read = read_memory(constant(0x100, 32), 8);
        let manager = BddManager::from_exprs(memory_read.clone(), constant(0, 8), &bdd_test_isa());

        assert!(
            manager.lower_expression(&memory_read, LEFT_EXPR)
                == manager.left_memory_read_table[0].value
        );
    }

    #[test]
    fn replace_right_expr_reuses_variables_and_preserves_left_state() {
        let mut manager = BddManager::from_exprs(
            constant(0, 16),
            concat([
                read_memory(constant(0x100, 32), 8),
                read_memory(constant(0x200, 32), 8),
            ]),
            &bdd_test_isa(),
        );

        let register_variable = manager
            .variables
            .iter()
            .find_map(|(description, function)| {
                matches!(description, VariableDescription::RegisterBit { .. })
                    .then(|| function.clone())
            })
            .expect("expected register variable");
        manager.left.bits.push(register_variable.clone());
        manager.constraint = manager
            .variables
            .iter()
            .find_map(|(description, function)| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit { left: false, .. }
                )
                .then(|| function.clone())
            })
            .expect("expected right memory variable");

        let initial_variable_count = manager_variable_count(&manager);

        for address in 0x300..0x310 {
            manager.replace_right_expr(read_memory(constant(address, 32), 16));

            assert_eq!(manager_variable_count(&manager), initial_variable_count);
            assert!(manager.left.bits == vec![register_variable.clone()]);
            assert!(manager.constraint == manager.true_fn);
            assert_eq!(manager.right_expr, read_memory(constant(address, 32), 16));
            assert_eq!(manager.right_memory_read_table.len(), 1);
        }
    }

    #[test]
    #[should_panic(expected = "still used by a live BCDD function")]
    fn release_variable_rejects_a_variable_used_by_any_owned_root() {
        let mut manager = BddManager::from_exprs(
            constant(0, 8),
            read_memory(constant(0x100, 32), 8),
            &bdd_test_isa(),
        );
        let variable_index = manager
            .variables
            .iter()
            .position(|(description, _)| {
                matches!(
                    description,
                    VariableDescription::MemoryReadValueBit { left: false, .. }
                )
            })
            .expect("expected right memory variable");

        manager
            .left
            .bits
            .push(manager.variables[variable_index].1.clone());
        manager.release_variable(variable_index);
    }

    #[test]
    fn instruction_seq_to_effects_does_not_double_substitute_register_reads() {
        let r0 = read_reg(0);
        let single_add = add(r0.clone(), r0).canonicalize();
        let double_substituted = add(single_add.clone(), single_add.clone()).canonicalize();
        let isa = ISA {
            instructions: vec![
                isa_instruction(
                    "ADD_R0_R0_R0",
                    vec![Effect::write_register(
                        reg(0),
                        add(read_reg(0), read_reg(0)),
                    )],
                ),
                isa_instruction(
                    "MOV_R1_R0",
                    vec![Effect::write_register(reg(1), read_reg(0))],
                ),
            ],
            registers: vec![],
        };
        let sequence = vec![decoded("ADD_R0_R0_R0"), decoded("MOV_R1_R0")];

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(register_write_value(&effects, 0), &single_add);
        assert_eq!(register_write_value(&effects, 1), &single_add);
        assert_ne!(register_write_value(&effects, 1), &double_substituted);
    }

    #[test]
    fn instruction_seq_to_effects_lowers_memory_writes_to_bytes() {
        let address = constant(0x100, 32);
        let value = constant(0xaabb_ccdd, 32);
        let isa = ISA {
            instructions: vec![isa_instruction(
                "STORE32",
                vec![Effect::write_memory(address.clone(), value.clone(), 32)],
            )],
            registers: vec![],
        };
        let sequence = vec![decoded("STORE32")];

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            effects,
            vec![
                Effect::write_memory(address.clone(), extract(value.clone(), 7, 0), 8),
                Effect::write_memory(
                    add(address.clone(), constant(1, 32)),
                    extract(value.clone(), 15, 8),
                    8,
                ),
                Effect::write_memory(
                    add(address.clone(), constant(2, 32)),
                    extract(value.clone(), 23, 16),
                    8,
                ),
                Effect::write_memory(
                    add(address.clone(), constant(3, 32)),
                    extract(value.clone(), 31, 24),
                    8,
                ),
            ]
        );
    }

    #[test]
    fn instruction_seq_to_effects_lowers_memory_reads_before_substitution() {
        let address = constant(0x100, 32);
        let value = constant(0xaabb_ccdd, 32);
        let isa = ISA {
            instructions: vec![
                isa_instruction(
                    "STORE32",
                    vec![Effect::write_memory(address.clone(), value.clone(), 32)],
                ),
                isa_instruction(
                    "LOAD32_R0",
                    vec![Effect::write_register(
                        reg(0),
                        read_memory(address.clone(), 32),
                    )],
                ),
            ],
            registers: vec![],
        };
        let sequence = vec![decoded("STORE32"), decoded("LOAD32_R0")];

        let effects = instruction_seq_to_effects(&sequence, &isa);

        assert_eq!(
            register_write_value(&effects, 0),
            &concat([
                extract(value.clone(), 31, 24),
                extract(value.clone(), 23, 16),
                extract(value.clone(), 15, 8),
                extract(value, 7, 0),
            ])
            .canonicalize()
        );
    }

    #[test]
    fn lower_memory_reads_uses_little_endian_byte_order() {
        let address = constant(0x100, 32);

        assert_eq!(
            lower_memory_reads(read_memory(address.clone(), 32)),
            concat([
                read_memory(add(address.clone(), constant(3, 32)), 8),
                read_memory(add(address.clone(), constant(2, 32)), 8),
                read_memory(add(address.clone(), constant(1, 32)), 8),
                read_memory(address, 8),
            ])
        );
    }

    #[test]
    fn lower_memory_reads_recurses_through_other_expressions() {
        let address = constant(0x100, 32);

        assert_eq!(
            lower_memory_reads(add(read_memory(address.clone(), 16), constant(1, 16))),
            add(
                concat([
                    read_memory(add(address.clone(), constant(1, 32)), 8),
                    read_memory(address, 8),
                ]),
                constant(1, 16),
            )
        );
    }

    #[test]
    fn combine_effects_unconditional_second_register_write_wins() {
        let first = Effect::write_register(reg(0), constant(1, 32));
        let second = Effect::write_register(reg(0), constant(2, 32));

        assert_eq!(combine_effects(&first, &second), Some(second));
    }

    #[test]
    fn combine_effects_returns_none_for_different_locations() {
        let first = Effect::write_register(reg(0), constant(1, 32));
        let second = Effect::write_register(reg(1), constant(2, 32));

        assert_eq!(combine_effects(&first, &second), None);
    }

    #[test]
    fn combine_effects_merges_guarded_writes_to_same_location() {
        let guard_1 = read_register(reg(10), 1);
        let guard_2 = read_register(reg(11), 1);
        let value_1 = constant(1, 32);
        let value_2 = constant(2, 32);
        let first = Effect::write_register_if(guard_1.clone(), reg(0), value_1.clone());
        let second = Effect::write_register_if(guard_2.clone(), reg(0), value_2.clone());

        assert_eq!(
            combine_effects(&first, &second),
            Some(Effect::WriteRegister {
                guard: or_expr(guard_1, guard_2.clone()),
                register: reg(0),
                value: select(guard_2, value_2, value_1),
            })
        );
    }

    #[test]
    fn combine_effects_ignores_false_guarded_second_write() {
        let first = Effect::write_register_if(read_register(reg(10), 1), reg(0), constant(1, 32));
        let second = Effect::write_register_if(bool_const(false), reg(0), constant(2, 32));

        assert_eq!(combine_effects(&first, &second), Some(first));
    }
}
