# Makefile for anisotropic_hilbert C library

CC = gcc
CFLAGS = -O3 -march=native -fPIC -Wall -Wextra -std=c11
CFLAGS += -fstrict-aliasing -Wstrict-aliasing=2
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

.PHONY: all clean test

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
	rm -f $(TARGET) $(OBJ)

# Show compiler info
info:
	@echo "CC: $(CC)"
	@echo "CFLAGS: $(CFLAGS)"
	@echo "Target: $(TARGET)"
	@$(CC) --version | head -1
