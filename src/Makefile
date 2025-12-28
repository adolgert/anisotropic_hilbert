# Makefile for anisotropic_hilbert C library

CC = gcc
CXX = g++
CFLAGS = -O3 -march=native -fPIC -Wall -Wextra -std=c11
CFLAGS += -fstrict-aliasing -Wstrict-aliasing=2
CXXFLAGS = -std=c++17 -O2 -Wall -Wextra
LDFLAGS = -shared

# Platform-specific shared library extension
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    LIBEXT = .dylib
    LDFLAGS += -dynamiclib
else
    LIBEXT = .so
endif

# Lean toolchain paths (for Lean-enabled builds)
LEAN_HOME ?= $(HOME)/.elan/toolchains/leanprover--lean4---v4.26.0
LEAN_DIR = ../lean
LEAN_LIB = $(LEAN_HOME)/lib/lean
PROJECT_LIB = $(LEAN_DIR)/.lake/build/lib/lean

TARGET = libanisotropic_hilbert$(LIBEXT)
SRC = anisotropic_hilbert.c
OBJ = $(SRC:.c=.o)

.PHONY: all clean test refine_pi_test test_affine test_affine_verbose test_affine_lean test_compare test_gray

all: $(TARGET)

$(TARGET): $(SRC)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

# Debug build
debug: CFLAGS = -g -O0 -fPIC -Wall -Wextra -std=c11 -fsanitize=address,undefined
debug: LDFLAGS += -fsanitize=address,undefined
debug: $(TARGET)

# Run Python tests
test: $(TARGET)
	python3 -m unittest -v test_anisotropic_hilbert

# Quick sanity test
quicktest: $(TARGET)
	python3 -c "from anisotropic_hilbert_c import encode, decode; print('C library loaded'); p = decode(0, (2,2)); print(f'decode(0, (2,2)) = {p}')"

clean:
	rm -f $(TARGET) $(OBJ) hilbert_affine.o hilbert_ffi.o test_hilbert_affine test_hilbert_affine_lean refine_pi_test generate_gray.o generate_gray_test

# Build and run the refine_pi self-test harness.
refine_pi_test: refine_pi.c
	$(CC) $(CFLAGS) -DREFINE_PI_TEST -o refine_pi_test refine_pi.c

# Build and run the hilbert_affine C++ test harness.
# Compile C file separately to preserve C linkage, then link with C++.
hilbert_affine.o: hilbert_affine.c
	$(CC) $(CFLAGS) -c -o $@ $<

test_hilbert_affine: test_hilbert_affine.cpp hilbert_affine.o
	$(CXX) $(CXXFLAGS) -o $@ $^

test_affine: test_hilbert_affine
	./test_hilbert_affine

test_affine_verbose: test_hilbert_affine
	./test_hilbert_affine -v

# Build and run the Gray code generator tests
generate_gray.o: generate_gray.cpp generate_gray.h
	$(CXX) $(CXXFLAGS) -c -o $@ generate_gray.cpp

generate_gray_test: generate_gray_test.cpp generate_gray.o
	$(CXX) $(CXXFLAGS) -o $@ $^

test_gray: generate_gray_test
	./generate_gray_test

test_gray_verbose: generate_gray_test
	./generate_gray_test -v

# Show compiler info
info:
	@echo "CC: $(CC)"
	@echo "CXX: $(CXX)"
	@echo "CFLAGS: $(CFLAGS)"
	@echo "CXXFLAGS: $(CXXFLAGS)"
	@echo "Target: $(TARGET)"
	@$(CC) --version | head -1

# ---------------------------------------------------------------------------
# Lean-enabled builds
# ---------------------------------------------------------------------------

# Find AnisoHilbert dylibs (macOS) or .so files (Linux)
ifeq ($(UNAME_S),Darwin)
    ANISO_DYLIBS = $(wildcard $(PROJECT_LIB)/AnisoHilbert*.dylib)
    RPATH_FLAGS = -Wl,-rpath,$(LEAN_LIB) -Wl,-rpath,$(PROJECT_LIB)
else
    ANISO_DYLIBS = $(wildcard $(PROJECT_LIB)/AnisoHilbert*.so)
    RPATH_FLAGS = -Wl,-rpath,$(LEAN_LIB) -Wl,-rpath,$(PROJECT_LIB)
endif

# Compile FFI wrapper
hilbert_ffi.o: $(LEAN_DIR)/ffi/hilbert_ffi.c
	$(CC) -c -I$(LEAN_HOME)/include -I$(LEAN_DIR)/ffi -fPIC -O2 -o $@ $<

# Build test harness with Lean support
test_hilbert_affine_lean: test_hilbert_affine.cpp hilbert_affine.o hilbert_ffi.o
	$(CXX) $(CXXFLAGS) -DWITH_LEAN -I$(LEAN_DIR)/ffi \
	    -o $@ $^ \
	    -L$(LEAN_LIB) -L$(PROJECT_LIB) \
	    -lleanshared $(ANISO_DYLIBS) \
	    $(RPATH_FLAGS)

# Run Lean implementation tests
test_affine_lean: test_hilbert_affine_lean
	./test_hilbert_affine_lean --lean

# Run comparison between C and Lean implementations
test_compare: test_hilbert_affine_lean
	./test_hilbert_affine_lean --compare

# Verbose comparison
test_compare_verbose: test_hilbert_affine_lean
	./test_hilbert_affine_lean -v --compare
