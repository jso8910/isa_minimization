#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
    echo "Usage: $0 /path/to/program.c /path/to/workdir"
    exit 2
fi

PROGRAM="$(realpath -m "$1")"
WORKDIR="$(realpath -m "$2")"
OUTDIR="$WORKDIR/out"

if [[ ! -f "$PROGRAM" ]]; then
    echo "ERROR: input C file not found: $PROGRAM"
    exit 1
fi

case "$PROGRAM" in
    *.c) ;;
    *)
        echo "ERROR: expected a .c input file: $PROGRAM"
        exit 1
        ;;
esac

for tool in \
    clang \
    arm-none-eabi-readelf
do
    command -v "$tool" >/dev/null || {
        echo "ERROR: $tool not found"
        exit 1
    }
done

mkdir -p "$OUTDIR"

ASM="$OUTDIR/main.s"
OBJ="$OUTDIR/main.o"
SYSROOT="${ARM_NONE_EABI_SYSROOT:-/usr/arm-none-eabi}"

COMMON_CFLAGS=(
    -target arm-none-eabi
    -mcpu=arm7tdmi
    -mfloat-abi=soft
    -marm
    -ffunction-sections
    -fdata-sections
    -fno-jump-tables
    -fno-exceptions
    -fno-unwind-tables
    -fno-asynchronous-unwind-tables
    -fno-pic
    --sysroot="$SYSROOT"
    -O3
)

clang "${COMMON_CFLAGS[@]}" \
    -S "$PROGRAM" \
    -o "$ASM"

clang "${COMMON_CFLAGS[@]}" \
    -c "$PROGRAM" \
    -o "$OBJ"

if ! arm-none-eabi-readelf -h "$OBJ" >/dev/null; then
    echo "ERROR: failed to verify object file as ELF: $OBJ"
    exit 1
fi

echo "Assembly: $ASM"
echo "Object:   $OBJ"
