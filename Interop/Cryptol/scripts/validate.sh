#!/usr/bin/env bash
# Optional Cryptol checks, also invoked by the repository validation wrapper.
set -euo pipefail
cd "$(dirname "$0")/../../.."
run_lint=0
run_test=0
run_axioms=0
run_external=0
for arg in "$@"; do
  case "$arg" in
    --lint) run_lint=1 ;;
    --test) run_test=1 ;;
    --axioms) run_axioms=1 ;;
    --external) run_external=1; run_test=1 ;;
    *) echo "Unknown Cryptol validation option: $arg" >&2; exit 1 ;;
  esac
done
if (( run_external )); then
  : "${CRYPTOL_BINARY:?Set CRYPTOL_BINARY to the pinned Cryptol 3.6.0 executable}"
  : "${FOUNDATION_PATH:?Set FOUNDATION_PATH to the pinned Foundation checkout}"
fi
report_dir="${CRYPTOL_REPORT_DIR:-/tmp/vcvio-cryptol-validation}"
mkdir -p "$report_dir"
lake_cmd=(lake)
if [[ -n "${POLYFUN_PATH:-}" ]]; then lake_cmd+=(-R -K "polyfunPath=$POLYFUN_PATH"); fi
audit_obligations() {
  "${lake_cmd[@]}" exe polyfun-axiomsweep --root Interop.Cryptol.Bridge \
    --root VCVio.Algorithms.Sha2 --root VCVio.Algorithms.Keccak --root VCVio.Algorithms.Encoding \
    --root VCVio.Algorithms.CRC --out "$report_dir/axioms.json"
  python3 Interop/Cryptol/scripts/audit_obligations.py --report "$report_dir/axioms.json" \
    --ledger Interop/Cryptol/obligations.json --out "$report_dir/obligations.json" "$@"
}
if python3 -c 'import json; exit(not json.load(open("Interop/Cryptol/obligations.json"))["obligations"])'; then
  # Every other warning still fails, and every admission is checked against the
  # compiled proposition and dependency graph before any test is reported green.
  "${lake_cmd[@]}" build CryptolBridge CryptolTests --iofail \
    2>&1 | tee "$report_dir/build.log"
  audit_obligations --warnings "$report_dir/build.log"
else
  "${lake_cmd[@]}" build CryptolBridge CryptolTests --wfail --iofail
fi
bash scripts/check-interop-isolation.sh
python3 scripts/test-interop-isolation.py
"${lake_cmd[@]}" env python3 - <<'PY'
import os
from pathlib import Path
search = [Path(p) for p in os.environ['LEAN_PATH'].split(os.pathsep)]
sources = [p for p in Path('Interop/Cryptol').rglob('*.lean') if 'Consumer' not in p.parts]
for source in sources:
    artifact = source.with_suffix('.olean')
    expected = (Path('.lake/build/lib/lean') / artifact).resolve()
    actual = next(((p / artifact).resolve() for p in search if (p / artifact).is_file()), None)
    # The CLI is checked after its executable build when tests are enabled.
    if source.name == 'Main.lean' and actual is None:
        continue
    if actual != expected:
        raise SystemExit(f'Import shadowed: {source}: {actual}; expected {expected}')
print(f'Import ownership: {len(sources)} Cryptol modules resolve to this package')
PY
for component in Bridge; do
  "${lake_cmd[@]}" exe mk_all --lib "Interop/Cryptol/$component" --module --git --check
done
if (( run_lint )); then
  "${lake_cmd[@]}" lint -- --style-only
  "${lake_cmd[@]}" exe batteries/runLinter Interop.Cryptol.Bridge
fi
if (( run_test )); then
  # The repository's optional native FFI archives may report that they use stubs.
  # This executable uses only the Lean implementations.
  "${lake_cmd[@]}" build cryptol-interop slhdsa_primitive_tests
  .lake/build/bin/slhdsa_primitive_tests
  # PolyFun's validation owns the model, importer, corpus and evaluator checks.
  python3 -u Interop/Cryptol/scripts/test_source.py
  python3 -u Interop/Cryptol/scripts/test_modules.py
  python3 -u Interop/Cryptol/scripts/test_obligations.py
  crc_cmd=(python3 -u Interop/Cryptol/scripts/test_crc.py)
  if (( run_external )); then
    crc_cmd+=(--cryptol "$CRYPTOL_BINARY" --foundation "$FOUNDATION_PATH")
  fi
  "${crc_cmd[@]}"
  reference_cmd=(python3 -u Interop/Cryptol/scripts/test_references.py
    --report "$report_dir/references.json")
  if (( run_external )); then
    reference_cmd+=(--cryptol "$CRYPTOL_BINARY" --foundation "$FOUNDATION_PATH")
  fi
  "${reference_cmd[@]}"
  python3 -u Interop/Cryptol/scripts/check_bridge.py --local-only --report "$report_dir/local.json"
  # Refresh the separate manifest when switching between a local override and the Git pin.
  "${lake_cmd[@]}" -R -d Interop/Cryptol/Consumer update VCVio --keep-toolchain
  "${lake_cmd[@]}" -d Interop/Cryptol/Consumer build --wfail --iofail
  if (( run_external )); then
    python3 -u Interop/Cryptol/scripts/check_bridge.py --cryptol "$CRYPTOL_BINARY" \
      --foundation "$FOUNDATION_PATH" --report "$report_dir/external.json"
    if [[ -n "${CRYPTOL_EXPORTER:-}" ]]; then
      : "${CRYPTOL_SOURCE:?Set CRYPTOL_SOURCE to the pinned Cryptol source checkout}"
      python3 -u Interop/Cryptol/scripts/export_references.py --check \
        --exporter "$CRYPTOL_EXPORTER" --foundation "$FOUNDATION_PATH" \
        --cryptol-source "$CRYPTOL_SOURCE"
      python3 -u Interop/Cryptol/scripts/import_imperative.py --check \
        --exporter "$CRYPTOL_EXPORTER" --foundation "$FOUNDATION_PATH" \
        --cryptol-source "$CRYPTOL_SOURCE"
    fi
  fi
fi
if (( run_axioms )); then
  audit_obligations
fi
