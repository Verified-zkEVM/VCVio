#!/usr/bin/env bash
# Keep proof libraries link-safe when the native backend submodules are absent.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "${1:-}" == "--help" || "${1:-}" == "-h" ]]; then
  echo "Usage: scripts/check-extern-isolation.sh"
  exit 0
fi
exec lean --run scripts/CheckImports.lean --extern
