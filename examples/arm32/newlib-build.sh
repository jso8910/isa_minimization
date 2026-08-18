#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 /path/to/cygwin-repo [build-dir] [install-dir]"
    exit 2
fi

SRC="$(realpath "$1")"
PARENT="$(dirname "$SRC")"

BUILD="$(realpath -m "${2:-$PARENT/build-newlib}")"
INSTALL="$(realpath -m "${3:-$PARENT/newlib-install}")"

if [[ ! -f "$SRC/configure" ]]; then
    echo "ERROR: $SRC is not the top-level newlib/cygwin source directory."
    echo "Expected: $SRC/configure"
    echo
    echo "configure files found nearby:"
    find "$SRC" -maxdepth 2 -name configure -print 2>/dev/null || true
    exit 1
fi

if [[ ! -d "$SRC/newlib" ]]; then
    echo "ERROR: expected $SRC/newlib"
    exit 1
fi

for tool in \
    arm-none-eabi-gcc \
    arm-none-eabi-ar \
    arm-none-eabi-as \
    arm-none-eabi-ld \
    arm-none-eabi-nm \
    arm-none-eabi-objcopy \
    arm-none-eabi-objdump \
    arm-none-eabi-ranlib \
    arm-none-eabi-readelf
do
    command -v "$tool" >/dev/null || {
        echo "ERROR: $tool not found"
        exit 1
    }
done

TARGET_CFLAGS="\
-mcpu=arm7tdmi \
-marm \
-mfloat-abi=soft \
-O3 \
-ffunction-sections \
-fdata-sections \
-fno-jump-tables \
-fno-exceptions \
-fno-unwind-tables \
-fno-asynchronous-unwind-tables \
-fno-pic \
-save-temps=obj"

# Start with a clean configuration, since changing target flags in an
# existing configured tree can give misleading results.
rm -rf "$BUILD"
mkdir -p "$BUILD" "$INSTALL"

cd "$BUILD"

CC_FOR_TARGET=arm-none-eabi-gcc \
AR_FOR_TARGET=arm-none-eabi-ar \
AS_FOR_TARGET=arm-none-eabi-as \
LD_FOR_TARGET=arm-none-eabi-ld \
NM_FOR_TARGET=arm-none-eabi-nm \
OBJCOPY_FOR_TARGET=arm-none-eabi-objcopy \
OBJDUMP_FOR_TARGET=arm-none-eabi-objdump \
RANLIB_FOR_TARGET=arm-none-eabi-ranlib \
READELF_FOR_TARGET=arm-none-eabi-readelf \
CFLAGS_FOR_TARGET="$TARGET_CFLAGS" \
"$SRC/configure" \
    --target=arm-none-eabi \
    --prefix="$INSTALL" \
    --with-newlib \
    --disable-multilib \
    --disable-nls

make -j"$(nproc)" \
    CFLAGS_FOR_TARGET="$TARGET_CFLAGS" \
    all-target-newlib \
    all-target-libgloss
