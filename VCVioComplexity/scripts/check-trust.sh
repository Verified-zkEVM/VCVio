#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
package_root="$(cd -- "$script_dir/.." && pwd)"

cd "$package_root"

lake build VCVioComplexityTest.Trust

if rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b' \
    VCVioComplexity VCVioComplexityTest -g '*.lean'; then
  printf '%s\n' 'trust check failed: forbidden declaration or proof escape found above'
  exit 1
fi

printf '%s\n' 'trust check passed: guarded kernel reports match and no proof escapes were found'
