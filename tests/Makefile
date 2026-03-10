# Makefile for compiling test fixtures and generating golden files.
# Must be run from the project root, e.g.:
#   make -f tests/Makefile compile
#   make -f tests/Makefile golden
#
# Each fixture may declare which compilers to use with:
#   //%  <compiler>...   (space-separated; defaults to DEFAULT_COMPILERS)

ALL_COMPILERS    := gcc-13-x86_64   clang-16-x86_64 clang-17-x86_64 clang-18-x86_64 \
                    gcc-13-aarch64  clang-18-aarch64  \
                    gcc-13-aarch32  clang-18-aarch32  \
                    gcc-13-ppc32    clang-18-ppc32    \
                    gcc-13-ppc64    clang-18-ppc64
DEFAULT_COMPILERS := gcc-13-x86_64 clang-18-x86_64
FIXTURES  := $(patsubst tests/test-data/%.c,%,$(wildcard tests/test-data/*.c))
# Link without standard libraries: avoids needing cross-libc packages while
# still producing a fully linked ELF (so DWARF relocations are resolved).
CFLAGS    := -nostdlib -nostartfiles -g -O0

# Shell case statement mapping compiler identifiers to their binaries/flags.
# Expanded inline in compile and golden targets.
RESOLVE_COMPILER = \
	case $$compiler in \
	  gcc-13-x86_64)    cmd="gcc-13" ;; \
	  clang-16-x86_64)  cmd="clang-16" ;; \
	  clang-17-x86_64)  cmd="clang-17" ;; \
	  clang-18-x86_64)  cmd="clang-18" ;; \
	  gcc-13-aarch64)   cmd="aarch64-linux-gnu-gcc-13" ;; \
	  clang-18-aarch64) cmd="clang-18 --target=aarch64-linux-gnu" ;; \
	  gcc-13-aarch32)   cmd="arm-linux-gnueabihf-gcc-13" ;; \
	  clang-18-aarch32) cmd="clang-18 --target=arm-linux-gnueabihf" ;; \
	  gcc-13-ppc32)     cmd="powerpc-linux-gnu-gcc-13" ;; \
	  clang-18-ppc32)   cmd="clang-18 --target=powerpc-linux-gnu" ;; \
	  gcc-13-ppc64)     cmd="powerpc64le-linux-gnu-gcc-13" ;; \
	  clang-18-ppc64)   cmd="clang-18 --target=powerpc64le-linux-gnu" ;; \
	  *)                cmd="$$compiler" ;; \
	esac

.PHONY: compile golden golden-full clean help

# Compile test fixtures for each fixture's applicable compilers.
# Binaries go to tests/test-data/<fixture>.<compiler>.
# Respects //%  annotations; falls back to DEFAULT_COMPILERS.
compile:
	@for fixture in $(FIXTURES); do \
	  src=tests/test-data/$$fixture.c; \
	  compilers=$$(grep '^//%  ' $$src | sed 's|^//%  ||'); \
	  [ -n "$$compilers" ] || compilers="$(DEFAULT_COMPILERS)"; \
	  for compiler in $$compilers; do \
	    out=tests/test-data/$$fixture.$$compiler; \
	    flags=$$(grep '^//@ ' $$src | sed 's|^//@ ||'); \
	    $(RESOLVE_COMPILER); \
	    echo "Compiling $$src with $$compiler..."; \
	    $$cmd $(CFLAGS) $$flags $$src -o $$out; \
	  done; \
	done

# Generate golden files for all compilers using llvm-dwarfdump.
# Depends on compile. Run this in Docker to regenerate committed golden files.
golden: compile
	@for fixture in $(FIXTURES); do \
	  src=tests/test-data/$$fixture.c; \
	  compilers=$$(grep '^//%  ' $$src | sed 's|^//%  ||'); \
	  [ -n "$$compilers" ] || compilers="$(DEFAULT_COMPILERS)"; \
	  for compiler in $$compilers; do \
	    exe=tests/test-data/$$fixture.$$compiler; \
	    out=tests/test-data/$$fixture.$$compiler.txt; \
	    flags=$$(grep '^//# ' $$src | sed 's|^//# ||'); \
	    echo "Generating $$out..."; \
	    llvm-dwarfdump $$flags $$exe | sh tests/sanitize.sh > $$out; \
	  done; \
	done

# Generate golden files for ALL compiler/fixture combinations, ignoring //%
# annotations. Use this to prepare a complete set of golden files for running
# the full test suite (DWARF_FULL_TEST=1) without needing llvm-dwarfdump locally.
golden-full:
	@for fixture in $(FIXTURES); do \
	  src=tests/test-data/$$fixture.c; \
	  flags=$$(grep '^//@ ' $$src | sed 's|^//@ ||'); \
	  for compiler in $(ALL_COMPILERS); do \
	    out=tests/test-data/$$fixture.$$compiler; \
	    $(RESOLVE_COMPILER); \
	    echo "Compiling $$src with $$compiler..."; \
	    $$cmd $(CFLAGS) $$flags $$src -o $$out; \
	  done; \
	done
	@for fixture in $(FIXTURES); do \
	  src=tests/test-data/$$fixture.c; \
	  dflags=$$(grep '^//# ' $$src | sed 's|^//# ||'); \
	  for compiler in $(ALL_COMPILERS); do \
	    exe=tests/test-data/$$fixture.$$compiler; \
	    out=tests/test-data/$$fixture.$$compiler.txt; \
	    echo "Generating $$out..."; \
	    llvm-dwarfdump $$dflags $$exe | sh tests/sanitize.sh > $$out; \
	  done; \
	done

clean:
	@for fixture in $(FIXTURES); do \
	  for compiler in $(ALL_COMPILERS); do \
	    rm -f tests/test-data/$$fixture.$$compiler; \
	    rm -f tests/test-data/$$fixture.$$compiler.txt; \
	  done; \
	done

.PHONY: help
help:
	@echo "Golden file generation for galois-dwarf test suite"
	@echo ""
	@echo "Targets:"
	@echo "  compile      Compile test fixtures for applicable compilers (per //%  annotations)"
	@echo "  golden       Compile and generate golden files (requires llvm-dwarfdump)"
	@echo "  golden-full  Generate golden files for ALL compiler/fixture combinations"
	@echo "               (use with DWARF_FULL_TEST=1 cabal test for full local coverage)"
	@echo "  clean        Remove compiled binaries and generated golden files"
	@echo ""
	@echo "All compilers:     $(ALL_COMPILERS)"
	@echo "Default compilers: $(DEFAULT_COMPILERS)"
	@echo ""
	@echo "Per-fixture compiler selection: add //%  <compilers> in the .c file"
	@echo ""
	@echo "Run from project root via Docker (recommended):"
	@echo "  docker build --platform linux/amd64 -t galois-dwarf-golden tests/"
	@echo "  docker run --platform linux/amd64 --rm -v \$$(pwd):/work galois-dwarf-golden make -f tests/Makefile golden"
