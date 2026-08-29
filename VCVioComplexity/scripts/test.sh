#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
package_root="$(cd -- "$script_dir/.." && pwd)"

cd "$package_root"

lake build VCVioComplexity VCVioComplexityTest
"$script_dir/check-trust.sh"
"$script_dir/compatibility-preflight.sh"
