# Developer documentation

## Test suite

The test suite validates DWARF parsing by:

1. Compiling C fixtures with embedded compiler flags
2. Running the `dwarf-dump` executable on compiled binaries
3. Comparing output against golden files using tasty-golden

### Test fixtures

C source files in `tests/test-data/` contain embedded flags:

- `//# <flag>` — flags for dwarf-dump (e.g., `//# --debug-info`)
- `//@ <flag>` — flags for the compiler (e.g., `//@ -gdwarf-4`)
- `//% <compiler>...` — compilers to use (space-separated; defaults to latest x86_64 clang and gcc)

### File layout

All files live flat in `tests/test-data/`:

- `<fixture>.c` — C source
- `<fixture>.<compiler>` — compiled binary (gitignored)
- `<fixture>.<compiler>.txt` — golden file (committed)

### Running tests

```sh
cabal test
```

Set `DWARF_FULL_TEST=1` to test all compiler×fixture combinations (not just those
with committed golden files). Any missing golden files are auto-generated from
`llvm-dwarfdump` (which must be in PATH).

```sh
docker build --platform linux/amd64 -t galois-dwarf-golden tests/
docker run --platform linux/amd64 --rm -v $(pwd):/work galois-dwarf-golden make -f tests/Makefile golden-full
DWARF_FULL_TEST=1 cabal test
```

### Golden files

Golden files in `tests/test-data/` are version controlled. They contain the
expected output from `llvm-dwarfdump` (the reference implementation) for each
supported compiler.

To regenerate golden files (e.g., when adding new tests or compilers):

1. Build Docker image: `docker build --platform linux/amd64 -t galois-dwarf-golden tests/`
2. Generate golden files: `docker run --platform linux/amd64 --rm -v $(pwd):/work galois-dwarf-golden make -f tests/Makefile golden`
3. Manually verify the golden files are correct
4. Commit the updated golden files

### Adding new tests

1. Create a focused C file testing one DWARF feature
2. Add `//# <dwarf-dump-flags>` and `//@ <compiler-flags>` at the top
3. Optionally add `//% <compilers>` to restrict which compilers run it
4. Place in `tests/test-data/`
5. Regenerate golden files (see above)
6. Manually verify golden file correctness
7. Commit both C source and golden files

### Adding new compilers

1. Add the compiler identifier to `ALL_COMPILERS` in `tests/Makefile`
2. Add a `RESOLVE_COMPILER` case for it in `tests/Makefile`
3. Add a `resolveCompiler` case and entry in `allCompilers` in `tests/Main.hs`
4. Add the apt package to `tests/install-compilers.sh`
5. Regenerate golden files (see above)
6. Commit golden files and updated files

### Architecture

- **Compiler discovery**: In normal mode, finds compilers from `*.*.txt` files in
  `tests/test-data/`. In full mode, tests all `allCompilers` against all fixtures.
- **Pre-compiled binaries**: Uses `tests/test-data/<fixture>.<compiler>` if present;
  otherwise compiles on the fly.
- **Golden files**: `tests/test-data/<fixture>.<compiler>.txt`
- **Test execution**: Runs `dwarf-dump` on compiled executables
- **Comparison**: Uses tasty-golden to diff against committed golden files

### Current limitations

- Only `.debug_info` section is supported
- DWARF v4 focus (v5 partial support)

---

## CI

### `ci.yaml` — runs on every push

Builds and tests across several GHC versions.

### `full-test.yaml` — weekly + manual dispatch

Runs every Sunday at midnight UTC, and can be triggered manually via
`workflow_dispatch` with an optional `test_filter` (tasty `-p` pattern).

Installs compilers **and** `llvm` (for `llvm-dwarfdump`), then runs the
full `DWARF_FULL_TEST=1` suite.

To trigger manually:

```
gh workflow run full-test.yaml
# or with a filter:
gh workflow run full-test.yaml -f test_filter="gcc-13-x86_64"
```
