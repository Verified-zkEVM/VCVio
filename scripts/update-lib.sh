#!/usr/bin/env bash

set -euo pipefail

# Active root umbrellas are generated as module files with public imports.
lake exe mk_all --lib ToMathlib --module
lake exe mk_all --lib VCVio --module
lake exe mk_all --lib LatticeCrypto --module
lake exe mk_all --lib Extern --module
lake exe mk_all --lib HashSig --module
lake exe mk_all --lib Examples --module
lake exe mk_all --lib VCVioWidgets --module
lake exe mk_all --lib VCVioTest --module

# Interop is dormant and has not yet adopted module scopes.
lake exe mk_all --lib Interop
