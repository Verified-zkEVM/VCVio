#!/usr/bin/env bash
set -eo pipefail

# Building the examples already builds this
# echo "# Building VCVio library"
# lake build VCVio

# Pass --ffi to additionally build and run the native-backed FFI test
# executables (ML-KEM / ML-DSA / Falcon). This is opt-in because it compiles the
# vendored C backends in third_party/ and links three executables, which is far
# slower than the default Lean-only build. The same coverage runs nightly in CI
# (.github/workflows/ffi-check.yml).
run_ffi=false
[[ "${1:-}" == "--ffi" ]] && run_ffi=true

echo "# Building Project"
# `VCVioTest` is the canary library (grind capability gates, probability tactic
# regressions, universe-polymorphism consumers). It is not a default target and is
# not reachable from `Examples`, so build it explicitly — otherwise the local
# workflow reproduces the CI blind spot that let two `grind` regressions through.
lake build Examples VCVioTest

if [[ "$run_ffi" == true ]]; then
  echo "# Initializing native FFI submodules"
  git submodule update --init --recursive

  echo "# Building FFI test executables"
  lake build mlkem_test mldsa_test falcon_test

  echo "# Running FFI differential tests"
  .lake/build/bin/mlkem_test
  .lake/build/bin/mldsa_test
  .lake/build/bin/falcon_test
fi

echo "# Linting Files"
# `lake exe lint-style` resolves to Mathlib's text-based linter; pass the project
# libraries explicitly so it lints all of them (the default would be only the
# `@[default_target]` `VCVio` lib).
lake exe lint-style ToMathlib VCVio Extern LatticeCrypto Examples VCVioWidgets Interop \
  && echo "All files okay"
