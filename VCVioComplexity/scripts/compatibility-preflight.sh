#!/usr/bin/env bash

set -euo pipefail

require_upstream_stack=false
case "$#" in
  0) ;;
  1)
    if [[ "$1" != '--require-upstream-stack' ]]; then
      printf 'usage: %s [--require-upstream-stack]\n' "${0##*/}" >&2
      exit 2
    fi
    require_upstream_stack=true
    ;;
  *)
    printf 'usage: %s [--require-upstream-stack]\n' "${0##*/}" >&2
    exit 2
    ;;
esac

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
package_root="$(cd -- "$script_dir/.." && pwd)"
dependency_root="$package_root/.lake/packages/complexitylib"
expected_revision='b6738219a3a3c50967d6bd16cba9487887ca6b66'
expected_toolchain='leanprover/lean4:v4.33.0'

cd "$package_root"

if [[ ! -d "$dependency_root/.git" ]]; then
  printf '%s\n' 'compatibility preflight failed: run `lake update` to materialize complexitylib'
  exit 1
fi

actual_revision="$(git -C "$dependency_root" rev-parse HEAD)"
if [[ "$actual_revision" != "$expected_revision" ]]; then
  printf 'compatibility preflight failed: expected complexitylib %s, found %s\n' \
    "$expected_revision" "$actual_revision"
  exit 1
fi

actual_toolchain="$(<lean-toolchain)"
if [[ "$actual_toolchain" != "$expected_toolchain" ]]; then
  printf 'compatibility preflight failed: expected %s, found %s\n' \
    "$expected_toolchain" "$actual_toolchain"
  exit 1
fi

if [[ -n "$(git -C "$dependency_root" status --short)" ]]; then
  printf '%s\n' 'compatibility preflight failed: pinned complexitylib source is dirty'
  git -C "$dependency_root" status --short
  exit 1
fi

printf 'complexitylib revision: %s\n' "$actual_revision"
printf 'validation toolchain: %s\n' "$actual_toolchain"

lake build \
  Complexitylib.Models.TuringMachine \
  Complexitylib.Encoding.Pairing \
  Complexitylib.Models.TuringMachine.SpaceTime.Defs \
  VCVioComplexity.Backend.OutputBounds \
  VCVioComplexity.Backend.Polynomial \
  VCVioComplexity.Backend.PureCanary \
  VCVioComplexity.Backend.OracleCanary

composition_log="$(mktemp)"
asymptotics_log="$(mktemp)"
trap 'rm -f -- "$composition_log" "$asymptotics_log"' EXIT

if lake build \
    Complexitylib.Models.TuringMachine.Internal \
    Complexitylib.Models.TuringMachine.Combinators >"$composition_log" 2>&1; then
  printf '%s\n' 'composition preflight: available; reevaluate the conditional closure gate'
  composition_available=true
else
  expected_composition_failures=(
    'Complexitylib/Models/TuringMachine/Internal.lean:54:4: Tactic `split` failed'
    'Complexitylib/Models/TuringMachine/Internal.lean:71:4: Tactic `split` failed'
    'Complexitylib/Models/TuringMachine/Combinators.lean:328:10: Tactic `split` failed'
    'Complexitylib/Models/TuringMachine/Combinators.lean:341:10: Tactic `split` failed'
  )

  for expected_failure in "${expected_composition_failures[@]}"; do
    if ! rg -Fq "$expected_failure" "$composition_log"; then
      printf 'composition preflight failed for an unexpected reason; missing diagnostic: %s\n' \
        "$expected_failure"
      tail -n 80 "$composition_log"
      exit 1
    fi
  done

  composition_error_count="$(rg -c '^error: .+\.lean:[0-9]+:[0-9]+:' \
    "$composition_log" || true)"
  if [[ "$composition_error_count" != "${#expected_composition_failures[@]}" ]]; then
    printf 'composition preflight found %s source errors; expected exactly %s\n' \
      "$composition_error_count" "${#expected_composition_failures[@]}"
    rg '^error:' "$composition_log" || true
    exit 1
  fi

  composition_available=false
  printf '%s\n' 'composition preflight: blocked at the four recorded Lean 4.33 tactic ports'
  printf '%s\n' \
    'unavailable upstream APIs: copyInputToOutputTM, compositionTM, Hoare, TM.OutputBounds'
fi

if lake build Complexitylib.Asymptotics >"$asymptotics_log" 2>&1; then
  printf '%s\n' \
    'asymptotics preflight: available; reevaluate a proved bridge behind the local abstraction'
  asymptotics_available=true
else
  expected_asymptotics_failures=(
    'Complexitylib/Asymptotics.lean:106:2: No applicable extensionality theorem found'
    'Complexitylib/Asymptotics.lean:110:56: unsolved goals'
    'Complexitylib/Asymptotics.lean:114:4: No applicable extensionality theorem found'
    'Complexitylib/Asymptotics.lean:115:4: No applicable extensionality theorem found'
    'Complexitylib/Asymptotics.lean:162:2: No applicable extensionality theorem found'
    'Complexitylib/Asymptotics.lean:217:2: No applicable extensionality theorem found'
  )

  for expected_failure in "${expected_asymptotics_failures[@]}"; do
    if ! rg -Fq "$expected_failure" "$asymptotics_log"; then
      printf 'asymptotics preflight failed for an unexpected reason; missing diagnostic: %s\n' \
        "$expected_failure"
      tail -n 80 "$asymptotics_log"
      exit 1
    fi
  done

  asymptotics_error_count="$(rg -c '^error: .+\.lean:[0-9]+:[0-9]+:' \
    "$asymptotics_log" || true)"
  if [[ "$asymptotics_error_count" != "${#expected_asymptotics_failures[@]}" ]]; then
    printf 'asymptotics preflight found %s source errors; expected exactly %s\n' \
      "$asymptotics_error_count" "${#expected_asymptotics_failures[@]}"
    rg '^error:' "$asymptotics_log" || true
    exit 1
  fi

  asymptotics_available=false
  printf '%s\n' \
    'asymptotics preflight: blocked at the recorded Norm.ext and coercion proof ports'
  printf '%s\n' \
    'unavailable upstream APIs: PolyBound.bigO, Classes.P.Defs, full Cobham equivalence'
fi

if [[ "$require_upstream_stack" == true ]] && \
    [[ "$composition_available" != true || "$asymptotics_available" != true ]]; then
  printf '%s\n' \
    'strict upstream-stack preflight failed: one or more recorded ports remain unavailable'
  exit 1
fi

printf '%s\n' 'compatibility preflight completed without unexpected failures'
