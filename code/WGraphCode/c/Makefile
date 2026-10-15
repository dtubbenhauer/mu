CC ?= cc
CFLAGS ?= -O3
CFLAGS += -std=c11 -Wall -Wextra -Wpedantic

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
LIBOMP_PREFIX ?= $(shell brew --prefix libomp 2>/dev/null)
OPENMP_CFLAGS ?= -Xpreprocessor -fopenmp
CPPFLAGS += -isystem $(LIBOMP_PREFIX)/include
LDFLAGS += -L$(LIBOMP_PREFIX)/lib -Wl,-rpath,$(LIBOMP_PREFIX)/lib
LDLIBS += -lomp -lm
else
OPENMP_CFLAGS ?= -fopenmp
LDLIBS += -fopenmp -lm
endif

.PHONY: all clean help test check-openmp
all: wgraphgen

check-openmp:
ifeq ($(UNAME_S),Darwin)
	@test -f "$(LIBOMP_PREFIX)/include/omp.h" || { printf '%s\n' 'libomp not found; set LIBOMP_PREFIX to an installed libomp prefix.'; exit 1; }
endif

wgraphgen: wgraphgen.c Makefile | check-openmp
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OPENMP_CFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

test_wide_weight: test_wide_weight.c wgraphgen.c Makefile | check-openmp
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OPENMP_CFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

test: test_wide_weight
	@set -eu; path="$$(mktemp "$${TMPDIR:-/tmp}/wgraphgen-wide.XXXXXX")"; \
	  trap 'rm -f "$$path" "$$path.tmp"' 0 1 2 3 15; \
	  ./test_wide_weight "$$path"

help:
	@printf '%s\n' 'Targets: all (wgraphgen), test, test_wide_weight, clean, help' \
	  'Overrides: CC, CPPFLAGS, CFLAGS, LDFLAGS, LDLIBS, OPENMP_CFLAGS' \
	  'macOS: LIBOMP_PREFIX (default: brew --prefix libomp)' \
	  'Linux: make CC=gcc; macOS: make CC=clang' \
	  'No dependencies are installed by this Makefile.'

clean:
	rm -f wgraphgen test_wide_weight
