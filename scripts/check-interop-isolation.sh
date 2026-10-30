#!/usr/bin/env bash
# Check optional-backend and pure-algorithm imports using Lean's source parser.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  echo "Usage: scripts/check-interop-isolation.sh"
  exit 0
fi
exec lean --run scripts/CheckImports.lean
