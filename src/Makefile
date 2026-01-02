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

.PHONY: all clean test refine_pi_test test_affine test_affine_verbose test_affine_lean test_compare test_gray test_general test_general_verbose test_hdf5 generate_fast_tables test_fast_tables test_hamilton test_affine_alt test_affine_alt_verbose test_affine_alt_hamilton test_affine_alt_hamilton_verbose

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
	rm -f $(TARGET) $(OBJ) hilbert_affine.o hilbert_ffi.o test_hilbert_affine test_hilbert_affine_lean test_hilbert_general refine_pi_test generate_gray.o generate_gray_test tables_hdf5.o test_tables_hdf5 test_hilbert_tables.h5 generate_fast_tables test_fast_tables_verify test_fast.h5 test_random.h5 setup_hilbert.o hilbert_tables.h5 hamilton.o hilbert_general.o test_hamilton hamilton_metrics haverkort_metrics bounding_box_stats range_query_clustering hilbert_affine_alt.o hilbert_affine_alt_hamilton.o test_hilbert_affine_alt test_hilbert_affine_alt_hamilton

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

# ---------------------------------------------------------------------------
# Alternative mismatch-based Hilbert curve (hilbert_affine_alt.c)
# ---------------------------------------------------------------------------
# This file contains both Hamilton's original and the "look-both-ways"
# alternative. Default is alternative; use -DHILBERT_AFFINE_USE_HAMILTON=1
# to switch back to Hamilton.

# Compile alt implementation (default = alternative mismatch sequence)
hilbert_affine_alt.o: hilbert_affine_alt.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Compile alt implementation with Hamilton's formulas
hilbert_affine_alt_hamilton.o: hilbert_affine_alt.c
	$(CC) $(CFLAGS) -DHILBERT_AFFINE_VARIANT=2 -c -o $@ $<

# Test executable using alternative mismatch sequence
test_hilbert_affine_alt: test_hilbert_affine_alt.cpp hilbert_affine_alt.o
	$(CXX) $(CXXFLAGS) -o $@ $^

# Test executable using Hamilton via alt file (for comparison)
test_hilbert_affine_alt_hamilton: test_hilbert_affine_alt.cpp hilbert_affine_alt_hamilton.o
	$(CXX) $(CXXFLAGS) -o $@ test_hilbert_affine_alt.cpp hilbert_affine_alt_hamilton.o

# Run tests
test_affine_alt: test_hilbert_affine_alt
	./test_hilbert_affine_alt

test_affine_alt_verbose: test_hilbert_affine_alt
	./test_hilbert_affine_alt -v

test_affine_alt_hamilton: test_hilbert_affine_alt_hamilton
	./test_hilbert_affine_alt_hamilton

test_affine_alt_hamilton_verbose: test_hilbert_affine_alt_hamilton
	./test_hilbert_affine_alt_hamilton -v

# Build and run the hilbert_general test harness.
# This tests the table-based implementation using HDF5 tables.
setup_hilbert.o: setup_hilbert.c setup_hilbert.h tables_hdf5.h
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -c -o $@ $<

test_hilbert_general: test_hilbert_general.c hilbert_general.c setup_hilbert.h setup_hilbert.o tables_hdf5.o
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -o $@ test_hilbert_general.c setup_hilbert.o tables_hdf5.o $(HDF5_LIBS)

# Generate HDF5 tables file (1 set per curve type for testing)
hilbert_tables.h5: generate_fast_tables generate_hilbert_curves.sh
	./generate_hilbert_curves.sh hilbert_tables.h5 1

test_general: test_hilbert_general hilbert_tables.h5
	./test_hilbert_general

test_general_verbose: test_hilbert_general hilbert_tables.h5
	./test_hilbert_general -v

# Build and run the Gray code generator tests
generate_gray.o: generate_gray.cpp generate_gray.h
	$(CXX) $(CXXFLAGS) -c -o $@ generate_gray.cpp

generate_gray_test: generate_gray_test.cpp generate_gray.o
	$(CXX) $(CXXFLAGS) -o $@ $^

test_gray: generate_gray_test
	./generate_gray_test

test_gray_verbose: generate_gray_test
	./generate_gray_test -v

# ---------------------------------------------------------------------------
# HDF5 table storage
# ---------------------------------------------------------------------------

# HDF5 flags - try pkg-config first, fall back to common paths
HDF5_CFLAGS := $(shell pkg-config --cflags hdf5 2>/dev/null || echo "-I/usr/include/hdf5/serial")
HDF5_LIBS := $(shell pkg-config --libs hdf5 2>/dev/null || echo "-lhdf5")

tables_hdf5.o: tables_hdf5.c tables_hdf5.h
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -c -o $@ $<

test_tables_hdf5: test_tables_hdf5.c tables_hdf5.o
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -o $@ $^ $(HDF5_LIBS)

test_hdf5: test_tables_hdf5
	./test_tables_hdf5

# Fast table generator (GF(2)^k DP algorithm, HDF5 output)
generate_fast_tables: generate_fast_tables.cpp generate_gray.o tables_hdf5.o
	$(CXX) $(CXXFLAGS) $(HDF5_CFLAGS) -o $@ $^ $(HDF5_LIBS)

# Test target for generate_fast_tables
test_fast_tables: generate_fast_tables test_fast_tables_verify
	./generate_fast_tables --output test_fast.h5 --gray brgc
	./test_fast_tables_verify test_fast.h5 brgc 0
	./generate_fast_tables --output test_random.h5 --gray random --seed 42
	./test_fast_tables_verify test_random.h5 random 0
	rm -f test_fast.h5 test_random.h5
	@echo "All generate_fast_tables tests passed."

test_fast_tables_verify: test_fast_tables_verify.c tables_hdf5.o
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -o $@ $^ $(HDF5_LIBS)

# ---------------------------------------------------------------------------
# Hamilton's Compact Hilbert Index (with bug) - for metrics comparison
# ---------------------------------------------------------------------------

hamilton.o: hamilton.c hamilton.h
	$(CC) $(CFLAGS) -c -o $@ $<

test_hamilton: test_hamilton.cpp hamilton.c hamilton.h
	$(CXX) $(CXXFLAGS) -o $@ test_hamilton.cpp

hamilton_metrics: hamilton_metrics.c hamilton.c hamilton.h
	$(CC) $(CFLAGS) -o $@ hamilton_metrics.c -lm

hilbert_general.o: hilbert_general.c setup_hilbert.h
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -c -o $@ $<

haverkort_metrics: haverkort_metrics.c haverkort_metrics.h hamilton.o hilbert_general.o setup_hilbert.o tables_hdf5.o
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -o $@ haverkort_metrics.c hamilton.o hilbert_general.o setup_hilbert.o tables_hdf5.o $(HDF5_LIBS) -lm

bounding_box_stats: bounding_box_stats.c hamilton.o hilbert_general.o setup_hilbert.o tables_hdf5.o
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -o $@ bounding_box_stats.c hamilton.o hilbert_general.o setup_hilbert.o tables_hdf5.o $(HDF5_LIBS) -lm

range_query_clustering: range_query_clustering.c hamilton.o hilbert_general.o setup_hilbert.o tables_hdf5.o
	$(CC) $(CFLAGS) $(HDF5_CFLAGS) -o $@ range_query_clustering.c hamilton.o hilbert_general.o setup_hilbert.o tables_hdf5.o $(HDF5_LIBS) -lm

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
