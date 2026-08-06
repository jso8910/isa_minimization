# ISA Minimization

## Genetic ISA Field Restrictions

The genetic ISA optimizer mutates and crosses over entries in
`ISACandidate.valid_field_uses`. During those GA reproduction steps, fields
marked with `InstructionField::register_read()`,
`InstructionField::register_write()`, or
`InstructionField::register_read_write()` are not selectable genes. Examples
include ARM register operand selectors such as `Rn`, `Rm`, `Rd`, and `Rs`.

## Program input restrictions

TAILOR makes two key assumptions about the input assembly:

1. For ARM32 specifically, no data processing operations (eg ADD, MVN, etc.) which impact the
   program counter are generated. If these operations were generated, they would make it incredibly
   difficult to optimize the ISA.
2. In general, all branch destinations should either be distinguishable as the start of a basic
   block by being either an immediate offset branch or by being immediately after another branch
   operation.

If these two assumptions are not met, TAILOR will not be able to guarantee the creation of a
functionally equivalent program.

## Compiling programs for ARM7TDMI

This guide is for Arch Linux, for now. Debian-based systems will be added later.

```
sudo pacman -S arm-none-eabi-newlib arm-none-eabi-gcc
```

To compile a progam, `main.c` to a destination binary `main.o`. You will also want to link your
startup files and include a linker script for your actual hardware, as well as an actual standard library.

```

patch -d newlib -p1 < newlib-no-mode-stack-init.patch

arm-none-eabi-gcc \
  -mcpu=arm7tdmi \
  -marm \
  -mfloat-abi=soft \
  -DNO_MODE_STACK_INIT \
  -I"$PWD/newlib/libgloss/arm" \
  -I"$PWD/newlib/include" \
  -I/usr/arm-none-eabi/include \
  -x assembler-with-cpp \
  -c "$PWD/newlib/libgloss/arm/crt0.S" \
  -o "$PWD/startup-override/crt0.o"

clang -target arm-none-eabi \
  -mcpu=arm7tdmi \
  -mfloat-abi=soft \
  -marm \
  --sysroot=/usr/arm-none-eabi \
  -save-temps=obj \
  -O3 \
  -c main.c -o out/main.o

arm-none-eabi-gcc \
  -mcpu=arm7tdmi \
  -marm \
  -mfloat-abi=soft \
  -B"$PWD/startup-override/" \
  out/main.o \
  -T main.ld \
  -Wl,-e,_start \
  -specs=nosys.specs \
  -Wl,--gc-sections \
  -Wl,-Map=out/main.map \
  -o out/main.elf
```


## Greenthumb

ISA notes: superoptimization must reject instructions which modify the PC (ie branch operations or
other similar operations). It must, however, also not be affected by the program counter being a
live-out register (the only concern is, if the semantic effect of the modification to the PC is
encoded by each)