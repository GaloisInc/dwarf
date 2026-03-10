# Dockerfile for compiling test fixtures and regenerating golden files.
# Uses install-compilers.sh for compiler pinning, matching the CI environment.
#
# Usage (run from tests/ directory):
#   docker build --platform linux/amd64 -t galois-dwarf-golden .
#
# Compile fixtures for all compilers:
#   docker run --platform linux/amd64 --rm -v $(pwd)/..:/work galois-dwarf-golden make -f tests/Makefile compile
#
# Regenerate golden files:
#   docker run --platform linux/amd64 --rm -v $(pwd)/..:/work galois-dwarf-golden make -f tests/Makefile golden

FROM ubuntu:24.04

COPY install-compilers.sh /
RUN bash /install-compilers.sh && \
    apt-get install -y --no-install-recommends llvm make && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /work
