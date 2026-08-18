# ARM32 Scratch Replacement Templates

Scratch replacements are stored as `.s.tmpl` files. They are assembly-like templates,
not standalone assembler input. Rust is expected to select a template, allocate
temporary registers, substitute placeholders, optionally wrap the body for predication,
and then assemble/decode the result to verify that every emitted instruction is valid
for the current ISA candidate.

## Metadata

Each template starts with ARM comment metadata:

```asm
@ scratch-template: v1
@ family: mul
@ op: mul
@ algorithm: unrolled32
@ flags: preserve_nzcv
@ kind: whole
@ temps: t0,t1,t2
```

Required keys are `scratch-template`, `family`, `op`, `algorithm`, `flags`, `kind`,
and `temps`. The `kind` value is `whole`, `wrapper`, or `fragment`.

Useful optional keys are:

- `inputs`: source placeholders read by the template.
- `outputs`: destination placeholders written by the template.
- `requires`: lower-level template or instruction capability required by this file.
- `repeats`: how Rust should repeat a fragment.
- `predication`: normally `wrap guards/predicated_branch_guard.s.tmpl`.
- `reject-if`: conditions Rust must reject before choosing the template.

## Placeholders

Register, immediate, label, and mnemonic placeholders are raw `%ident` tokens:

```asm
mov %t0, %rm
%op %rd, %rn, %t0
%Ldone:
```

Common operand placeholders:

- `%rd`, `%rn`, `%rm`, `%rs`
- `%rdlo`, `%rdhi`
- `%base`, `%reg`, `%offset`, `%byte_count`
- `%t0`, `%t1`, ... for temporary registers allocated by Rust
- `%Lname` for fresh local labels

Mnemonic placeholders such as `%op`, `%op_s`, `%xfer_op`, `%mul`, `%umull`, and
`%smull` expand to complete mnemonics, including any condition suffix when the
template is using per-instruction predication.

Line placeholders are allowed only when named in metadata. They splice a complete
already-substituted line or block. Current line/block placeholders:

- `%body` in the predication wrapper
- `%mul_unrolled32_steps`
- `%variable_shift_steps`
- `%shift_overflow_fixup`
- `%dproc_result_line`
- `%logical_s_line`
- `%block_transfer_steps`
- `%block_writeback`

## Predication

The preferred predicated form is the guard wrapper:

```asm
%skip_if_not_cond %Ldone
%body
%Ldone:
```

Rust expands `%skip_if_not_cond` to a complete inverse-condition branch mnemonic,
for example `bne`, `beq`, or removes the guard entirely for `al`.

Use the branch guard for any template that may clobber flags. Per-instruction
condition suffixes are only safe when all flag-clobbering work happens after the
last instruction whose predicate depends on the original NZCV value.

## Flag Policy

- `preserve_nzcv`: no instruction in the body may write flags.
- `clobber_nzcv`: the body may write flags; Rust may select it only when flags are
  dead or when a following flag suffix template overwrites the required flags.
- flag suffix templates intentionally live in `flags/` and can be appended by Rust.

For multiply flags, the templates match the current Rust ARM semantics: N/Z are
computed from the result, and C/V are preserved even though the ARM7TDMI manual
describes some multiply C/V results as meaningless.

## Repetition

The template language has no loop or repetition directive. Files marked
`kind: fragment` are repeated by Rust. For example, Rust builds a 32-step unrolled
multiply by substituting `mul/mul_unrolled32_step_preserve_nzcv.s.tmpl` thirty-two
times into `%mul_unrolled32_steps`.

## Selection Requirements

Rust must reject a selected replacement when:

- there are not enough scratch registers for all `%tN` placeholders;
- an emitted instruction is not supported by the candidate after substitution;
- a branch guard is needed but branches are unavailable or unsafe;
- a template's `reject-if` metadata applies;
- replacing the instruction would shift a later PC read in a way the implementation
  cannot compensate for.
