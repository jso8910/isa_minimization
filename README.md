# ISA Minimization

## Genetic ISA Field Restrictions

The genetic ISA optimizer mutates and crosses over entries in
`ISACandidate.valid_field_uses`. During those GA reproduction steps, fields
marked with `InstructionField::register_read()`,
`InstructionField::register_write()`, or
`InstructionField::register_read_write()` are not selectable genes. Examples
include ARM register operand selectors such as `Rn`, `Rm`, `Rd`, and `Rs`.