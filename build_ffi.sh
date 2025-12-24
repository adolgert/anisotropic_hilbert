#!/bin/bash
#
# Build script for Lean FFI integration testing
#
# This script:
# 1. Builds the Lean project (if needed)
# 2. Compiles the FFI wrapper
# 3. Compiles the test harness
# 4. Links everything together
# 5. Runs the tests

set -e  # Exit on error

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$SCRIPT_DIR/lean"
SRC_DIR="$SCRIPT_DIR/src"
BUILD_DIR="$SCRIPT_DIR/build"

# Find Lean toolchain
LEAN_HOME="${LEAN_HOME:-$HOME/.elan/toolchains/leanprover--lean4---v4.26.0}"

if [ ! -d "$LEAN_HOME" ]; then
    echo "Error: Lean toolchain not found at $LEAN_HOME"
    echo "Please set LEAN_HOME environment variable or ensure Lean 4.26.0 is installed"
    exit 1
fi

echo "Using Lean toolchain: $LEAN_HOME"

# Create build directory
mkdir -p "$BUILD_DIR"

# Step 1: Build Lean project (just our module, not all of Mathlib)
echo ""
echo "=== Building Lean project ==="
cd "$LEAN_DIR"
# Build just our module and its dependencies (not Mathlib:shared which can fail)
lake build AnisoHilbert
echo "Lean build complete."

# Step 2: Gather library paths
LEAN_LIB="$LEAN_HOME/lib/lean"
PROJECT_LIB="$LEAN_DIR/.lake/build/lib/lean"

# Find all our module dylibs
ANISO_DYLIBS=$(find "$PROJECT_LIB" -name "AnisoHilbert*.dylib" | tr '\n' ' ')

echo ""
echo "=== Found module libraries ==="
echo "$ANISO_DYLIBS" | tr ' ' '\n'

# Step 3: Compile FFI wrapper
echo ""
echo "=== Compiling FFI wrapper ==="
clang -c \
    -I"$LEAN_HOME/include" \
    -I"$LEAN_DIR/ffi" \
    -fPIC \
    -O2 \
    "$LEAN_DIR/ffi/hilbert_ffi.c" \
    -o "$BUILD_DIR/hilbert_ffi.o"
echo "FFI wrapper compiled."

# Step 4: Compile the handwritten C implementation
echo ""
echo "=== Compiling handwritten C implementation ==="
clang -c \
    -fPIC \
    -O2 \
    "$SRC_DIR/anisotropic_hilbert.c" \
    -o "$BUILD_DIR/anisotropic_hilbert.o"
echo "C implementation compiled."

# Step 5: Compile test harness
echo ""
echo "=== Compiling test harness ==="
clang -c \
    -I"$LEAN_DIR/ffi" \
    -I"$SRC_DIR" \
    -O2 \
    "$SRC_DIR/test_against_lean.c" \
    -o "$BUILD_DIR/test_against_lean.o"
echo "Test harness compiled."

# Step 6: Link everything
echo ""
echo "=== Linking test executable ==="

# On macOS, we need to set rpath for finding dylibs at runtime
RPATH_FLAGS="-Wl,-rpath,$LEAN_LIB -Wl,-rpath,$PROJECT_LIB"

# Link the test executable
clang \
    "$BUILD_DIR/test_against_lean.o" \
    "$BUILD_DIR/hilbert_ffi.o" \
    "$BUILD_DIR/anisotropic_hilbert.o" \
    -L"$LEAN_LIB" \
    -L"$PROJECT_LIB" \
    -lleanshared \
    $ANISO_DYLIBS \
    $RPATH_FLAGS \
    -o "$BUILD_DIR/test_against_lean"

echo "Linking complete."

# Step 7: Run tests
echo ""
echo "=== Running tests ==="
"$BUILD_DIR/test_against_lean"

echo ""
echo "=== Build complete ==="
