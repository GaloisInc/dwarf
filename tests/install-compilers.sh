#!/usr/bin/env bash
# Install the pinned compiler versions used for DWARF test fixture compilation.
# Used by both tests/Dockerfile (as root) and the CI pre-hook (via sudo).
# Update these versions when the ubuntu-24.04 GitHub Actions runner is updated.
set -euo pipefail
apt-get update -q

# x86_64 native compilers.
apt-get install -y --no-install-recommends \
    gcc-13=13.3.0-6ubuntu2~24.04.1 \
    clang-16=1:16.0.6-23ubuntu4 \
    clang-17=1:17.0.6-9ubuntu1 \
    clang-18=1:18.1.3-1ubuntu1

# GCC cross-compilation toolchains.  clang-18 (above) cross-compiles to all
# non-x86_64 targets via --target=<triple>; the GCC packages provide the
# sysroots that clang also uses.
apt-get install -y --no-install-recommends \
    gcc-13-aarch64-linux-gnu=13.3.0-6ubuntu2~24.04cross1 \
    gcc-13-arm-linux-gnueabihf=13.3.0-6ubuntu2~24.04cross1 \
    gcc-13-powerpc-linux-gnu=13.3.0-6ubuntu2~24.04cross1 \
    gcc-13-powerpc64le-linux-gnu=13.3.0-6ubuntu2~24.04cross1
