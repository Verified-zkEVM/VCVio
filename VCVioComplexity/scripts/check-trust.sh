#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
package_root="$(cd -- "$script_dir/.." && pwd)"

cd "$package_root"

lake build VCVioComplexityTest.Trust

if command -v rg >/dev/null 2>&1; then
  scan_command=(rg -n '\b(sorry|admit|axiom|unsafe|native_decide)\b'
    VCVioComplexity VCVioComplexityTest -g '*.lean')
else
  scan_command=(grep -R -n -E -w --include='*.lean'
    '(sorry|admit|axiom|unsafe|native_decide)' VCVioComplexity VCVioComplexityTest)
fi

scan_status=0
"${scan_command[@]}" || scan_status="$?"
if [[ "$scan_status" == 0 ]]; then
  printf '%s\n' 'trust check failed: forbidden declaration or proof escape found above'
  exit 1
fi
if (( scan_status > 1 )); then
  printf 'trust check failed: source scanner exited with status %s\n' "$scan_status"
  exit 1
fi

printf '%s\n' 'trust check passed: guarded kernel reports match and no proof escapes were found'
