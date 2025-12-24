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

TARGET = libanisotropic_hilbert$(LIBEXT)
SRC = anisotropic_hilbert.c
OBJ = $(SRC:.c=.o)

.PHONY: all clean test refine_pi_test test_affine test_affine_verbose

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
	rm -f $(TARGET) $(OBJ) hilbert_affine.o test_hilbert_affine refine_pi_test

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

# Show compiler info
info:
	@echo "CC: $(CC)"
	@echo "CXX: $(CXX)"
	@echo "CFLAGS: $(CFLAGS)"
	@echo "CXXFLAGS: $(CXXFLAGS)"
	@echo "Target: $(TARGET)"
	@$(CC) --version | head -1
