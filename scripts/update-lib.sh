#!/usr/bin/env bash

set -euo pipefail

lake_cmd=(lake)
if [[ -n "${POLYFUN_PATH:-}" ]]; then lake_cmd+=(-R -K "polyfunPath=$POLYFUN_PATH"); fi

regenerate() {
  local status
  if "${lake_cmd[@]}" exe mk_all "$@"; then
    return 0
  else
    status=$?
  fi
  # Upstream returns the number of changed files: one for a successful --lib update.
  # Verify the result so a Lake/compiler failure with the same exit code is not swallowed.
  if (( status != 1 )); then return "$status"; fi
  "${lake_cmd[@]}" exe mk_all "$@" --check
}

# Active root umbrellas are generated as module files with public imports.
for library in ToMathlib VCVio VCVioCslib LatticeCrypto Extern HashSig Examples VCVioWidgets VCVioTest; do
  regenerate --lib "$library" --module
done

for component in Model Translation Bridge; do
  regenerate --lib "Interop/Cryptol/$component" --module --git
done

# The dormant backends have a separate aggregate from the active Cryptol libraries.
python3 - <<'PY'
from pathlib import Path
import subprocess
files = subprocess.check_output(['git', 'ls-files', 'Interop'], text=True).splitlines()
modules = sorted(p[:-5].replace('/', '.') for p in files
                 if p.endswith('.lean') and p.split('/')[1] in ('Hax', 'Aeneas', 'Rust'))
Path('Interop.lean').write_text(''.join('import ' + m + '\n' for m in modules))
PY
