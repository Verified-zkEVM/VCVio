#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
cd "${repo_root}"

if [[ $# -gt 1 ]] || [[ $# -eq 1 && "$1" != "--docs-only" ]]; then
  echo "usage: $0 [--docs-only]" >&2
  exit 2
fi

PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-acvp-provenance.py

if [[ $# -eq 1 ]]; then
  echo "SLH-DSA docs-only validation: PASS"
  exit 0
fi

lake build
lake build HashSig
lake build HashSigTest
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py \
  --elaborated-s01-dependencies

parser_gate_root="$(mktemp -d)"
fixture_root=""
parser_build_override_active=0
cleanup_restore_mode="production"
cleanup_restore_marker=""
if [[ "$(stat -c '%a' -- "${parser_gate_root}")" != "700" || -L "${parser_gate_root}" ]]; then
  echo "SLH-DSA parser gate parent is not a mode-700 ordinary directory" >&2
  exit 1
fi
restore_default_lake_configuration() {
  local restore_status=0
  case "${cleanup_restore_mode}" in
    production)
      if [[ ! -d "${parser_gate_root}" || -L "${parser_gate_root}" ]]; then
        echo "SLH-DSA cannot restore Lake configuration after parser temp root disappeared" >&2
        return 1
      fi
      if PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py \
          --audit-s01-lake-config; then
        parser_build_override_active=0
        return 0
      else
        restore_status=$?
        return "${restore_status}"
      fi
      ;;
    self-test-success)
      if [[ ! -d "${parser_gate_root}" || -L "${parser_gate_root}" ]]; then
        return 75
      fi
      printf '%s\n' attempt success > "${cleanup_restore_marker}"
      parser_build_override_active=0
      return 0
      ;;
    self-test-failure)
      if [[ ! -d "${parser_gate_root}" || -L "${parser_gate_root}" ]]; then
        return 75
      fi
      printf '%s\n' attempt > "${cleanup_restore_marker}"
      return 73
      ;;
    *)
      echo "SLH-DSA invalid private cleanup restore mode" >&2
      return 74
      ;;
  esac
}
cleanup_validation() {
  local original_status=$?
  local restore_status=0
  local removal_status=0
  trap - EXIT
  set +e
  if [[ "${parser_build_override_active:-0}" -eq 1 ]]; then
    restore_default_lake_configuration
    restore_status=$?
    if [[ "${restore_status}" -ne 0 ]]; then
      echo "SLH-DSA failed to restore default Lake configuration (status ${restore_status})" >&2
    fi
  fi
  if [[ -n "${fixture_root:-}" && -d "${fixture_root}" && ! -L "${fixture_root}" ]]; then
    rm -rf -- "${fixture_root}"
    removal_status=$?
  fi
  if [[ -n "${parser_gate_root:-}" && -d "${parser_gate_root}" &&
        ! -L "${parser_gate_root}" ]]; then
    rm -rf -- "${parser_gate_root}"
    if [[ "$?" -ne 0 ]]; then
      removal_status=1
    fi
  fi
  if [[ "${original_status}" -ne 0 ]]; then
    exit "${original_status}"
  fi
  if [[ "${restore_status}" -ne 0 || "${removal_status}" -ne 0 ]]; then
    exit 1
  fi
  exit 0
}
trap cleanup_validation EXIT

# Exercise the production EXIT-cleanup state machine itself. The private restore modes only replace
# the external audit action; they still require restoration while the probe root exists, share the
# same flag/status/ordering logic, and cannot be selected by a normal invocation of this wrapper.
cleanup_probe_root="${parser_gate_root}/cleanup-probes"
mkdir -p -- "${cleanup_probe_root}"
run_cleanup_regression() {
  local label="$1"
  local expected_status="$2"
  local restore_mode="$3"
  local trigger="$4"
  local probe_root="${cleanup_probe_root}/${label}-root"
  local marker="${cleanup_probe_root}/${label}.restore"
  local stderr_file="${cleanup_probe_root}/${label}.stderr"
  local actual_status=0
  mkdir -p -- "${probe_root}"
  set +e
  (
    parser_gate_root="${probe_root}"
    fixture_root=""
    parser_build_override_active=1
    cleanup_restore_mode="${restore_mode}"
    cleanup_restore_marker="${marker}"
    trap cleanup_validation EXIT
    case "${trigger}" in
      explicit-7)
        exit 7
        ;;
      errexit)
        set -e
        false
        ;;
      sigterm)
        kill -TERM "${BASHPID}"
        ;;
      resolve-failure)
        set -e
        return 23
        ;;
      success)
        :
        ;;
      *)
        exit 76
        ;;
    esac
  ) > /dev/null 2> "${stderr_file}"
  actual_status=$?
  set -e
  if [[ "${actual_status}" -ne "${expected_status}" || -e "${probe_root}" ||
        -L "${probe_root}" ]]; then
    echo "SLH-DSA cleanup regression ${label} failed: expected status " \
      "${expected_status}, got ${actual_status}" >&2
    cat -- "${stderr_file}" >&2
    exit 1
  fi
  if [[ "${restore_mode}" == "self-test-success" ]]; then
    if [[ "$(cat -- "${marker}")" != $'attempt\nsuccess' ]]; then
      echo "SLH-DSA cleanup regression ${label} did not restore successfully" >&2
      exit 1
    fi
  elif [[ "$(cat -- "${marker}")" != "attempt" ]] ||
      ! grep -Fq 'failed to restore default Lake configuration (status 73)' "${stderr_file}"; then
    echo "SLH-DSA cleanup regression ${label} did not preserve restore failure evidence" >&2
    exit 1
  fi
}
run_cleanup_regression explicit-7 7 self-test-success explicit-7
run_cleanup_regression errexit 1 self-test-success errexit
run_cleanup_regression sigterm-143 143 self-test-success sigterm
run_cleanup_regression failure-preserves-7 7 self-test-failure explicit-7
run_cleanup_regression success-restore-failure 1 self-test-failure success
run_cleanup_regression normal-success 0 self-test-success success
run_cleanup_regression resolve-failure-23 23 self-test-success resolve-failure
echo "SLH-DSA parser override cleanup self-tests: PASS (7 cases; SIGKILL cannot run EXIT traps)"

expected_parser_stdout_file="${parser_gate_root}/expected-parser.stdout"
printf '%s\n' \
  'SLH-DSA ACVP parser positive suite: PASS (16 cases)' \
  'SLH-DSA ACVP parser negative suite: PASS (52 cases)' \
  'SLH-DSA ACVP parser runtime gate: PASS (68 cases)' \
  > "${expected_parser_stdout_file}"
if [[ "$(wc -c < "${expected_parser_stdout_file}")" -ne 154 ]]; then
  echo "SLH-DSA expected parser stdout is not exactly 154 bytes" >&2
  exit 1
fi

require_exact_parser_stdout_file() {
  local actual_file="$1"
  if ! cmp -s -- "${expected_parser_stdout_file}" "${actual_file}"; then
    echo "SLH-DSA parser stdout byte mismatch" >&2
    echo "expected bytes / actual bytes:" >&2
    wc -c -- "${expected_parser_stdout_file}" "${actual_file}" >&2
    echo "actual stdout:" >&2
    cat -- "${actual_file}" >&2
    return 1
  fi
}

run_parser_stdout_gate() {
  local actual_file="$1"
  local command_status=0
  shift
  if "$@" > "${actual_file}"; then
    command_status=0
  else
    command_status=$?
    echo "SLH-DSA parser executable failed with status ${command_status}" >&2
    return "${command_status}"
  fi
  cat -- "${actual_file}"
  require_exact_parser_stdout_file "${actual_file}"
}

require_canonical_sha256_file() {
  local hash_file="$1"
  if [[ ! -f "${hash_file}" || -L "${hash_file}" ||
        "$(wc -c < "${hash_file}")" -ne 65 ]] ||
      ! LC_ALL=C grep -Eq '^[0-9a-f]{64}$' "${hash_file}"; then
    echo "SLH-DSA SHA-256 file is not one canonical LF-terminated record: ${hash_file}" >&2
    return 1
  fi
}

require_bound_parser_hash_files() {
  local expected_file="$1"
  local before_file="$2"
  local after_file="$3"
  require_canonical_sha256_file "${expected_file}"
  require_canonical_sha256_file "${before_file}"
  require_canonical_sha256_file "${after_file}"
  if ! cmp -s -- "${expected_file}" "${before_file}" ||
      ! cmp -s -- "${expected_file}" "${after_file}"; then
    echo "SLH-DSA current parser bytes disagree before/after execution" >&2
    return 1
  fi
}

cp -- "${expected_parser_stdout_file}" "${parser_gate_root}/exact.stdout"
require_exact_parser_stdout_file "${parser_gate_root}/exact.stdout"
printf '%s\n' 'SLH-DSA-C13 KAT: PASS (valid signature accepted, tampered rejected)' \
  > "${parser_gate_root}/c13.stdout"
printf '%s\n' 'VCVio smoke test OK' > "${parser_gate_root}/smoke.stdout"
cp -- "${expected_parser_stdout_file}" "${parser_gate_root}/extra-nonblank.stdout"
printf '%s\n' 'extra output' >> "${parser_gate_root}/extra-nonblank.stdout"
sed -n '1,2p' "${expected_parser_stdout_file}" > "${parser_gate_root}/missing-line.stdout"
cp -- "${expected_parser_stdout_file}" "${parser_gate_root}/one-blank.stdout"
printf '\n' >> "${parser_gate_root}/one-blank.stdout"
cp -- "${expected_parser_stdout_file}" "${parser_gate_root}/multiple-blanks.stdout"
printf '\n\n\n' >> "${parser_gate_root}/multiple-blanks.stdout"
for mutated_parser_stdout_file in \
  "${parser_gate_root}/c13.stdout" \
  "${parser_gate_root}/smoke.stdout" \
  "${parser_gate_root}/extra-nonblank.stdout" \
  "${parser_gate_root}/missing-line.stdout" \
  "${parser_gate_root}/one-blank.stdout" \
  "${parser_gate_root}/multiple-blanks.stdout"
do
  if require_exact_parser_stdout_file "${mutated_parser_stdout_file}" >/dev/null 2>&1; then
    echo "SLH-DSA parser stdout self-test accepted mutated bytes" >&2
    exit 1
  fi
done
echo "SLH-DSA parser stdout file mutation self-tests: PASS (6 rejected)"

if run_parser_stdout_gate "${parser_gate_root}/swapped.stdout" \
    lake exe smoke_test >/dev/null 2>&1; then
  echo "SLH-DSA parser stdout gate accepted successful smoke_test output" >&2
  exit 1
fi
echo "SLH-DSA successful wrong-executable stdout self-test: PASS (smoke_test rejected)"

parser_stdout_nonzero() {
  cat -- "${expected_parser_stdout_file}"
  return 7
}
if run_parser_stdout_gate "${parser_gate_root}/nonzero.stdout" \
    parser_stdout_nonzero >/dev/null 2>&1; then
  echo "SLH-DSA parser stdout gate accepted a nonzero producer" >&2
  exit 1
fi
echo "SLH-DSA parser nonzero-exit self-test: PASS"

printf '%s\n' 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' \
  > "${parser_gate_root}/hash.expected"
cp -- "${parser_gate_root}/hash.expected" "${parser_gate_root}/hash.before"
cp -- "${parser_gate_root}/hash.expected" "${parser_gate_root}/hash.after"
require_bound_parser_hash_files \
  "${parser_gate_root}/hash.expected" \
  "${parser_gate_root}/hash.before" \
  "${parser_gate_root}/hash.after"
printf '%064d\n' 0 > "${parser_gate_root}/hash.wrong"
printf '%s\n%s\n' \
  'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa' 'extra' \
  > "${parser_gate_root}/hash.extra"
: > "${parser_gate_root}/hash.missing"
for mutated_hash_file in \
  "${parser_gate_root}/hash.wrong" \
  "${parser_gate_root}/hash.extra" \
  "${parser_gate_root}/hash.missing"
do
  if require_bound_parser_hash_files \
      "${parser_gate_root}/hash.expected" \
      "${parser_gate_root}/hash.before" \
      "${mutated_hash_file}" >/dev/null 2>&1; then
    echo "SLH-DSA parser hash-binding self-test accepted mutated after-execution bytes" >&2
    exit 1
  fi
done
if require_bound_parser_hash_files \
    "${parser_gate_root}/hash.expected" \
    "${parser_gate_root}/hash.wrong" \
    "${parser_gate_root}/hash.after" >/dev/null 2>&1; then
  echo "SLH-DSA parser hash-binding self-test accepted mutated before-execution bytes" >&2
  exit 1
fi
echo "SLH-DSA parser before/after SHA-256 mutation self-tests: PASS (4 rejected)"

# Re-elaborate and build without caches into one initially absent private root, then attest the
# ParserTests/Schema/StrictJson source-to-object-to-executable traces before exact-path execution.
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py --audit-s01-lake-config
fresh_parser_build_root="${parser_gate_root}/fresh-root-build"
if [[ -e "${fresh_parser_build_root}" || -L "${fresh_parser_build_root}" ]]; then
  echo "SLH-DSA fresh parser build root was not initially absent" >&2
  exit 1
fi
resolved_parser_path_file="${parser_gate_root}/resolved-parser.path"
expected_parser_path_file="${parser_gate_root}/expected-parser.path"
expected_parser_hash_file="${parser_gate_root}/expected-parser.hash"
before_parser_hash_file="${parser_gate_root}/before-parser.hash"
after_parser_hash_file="${parser_gate_root}/after-parser.hash"
parser_build_override_active=1
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py \
  --resolve-s01-parser-executable \
  "${fresh_parser_build_root}" \
  "${resolved_parser_path_file}" "${expected_parser_hash_file}"
printf '%s\n' "${fresh_parser_build_root}/bin/slhdsa_acvp_parser" \
  > "${expected_parser_path_file}"
if ! cmp -s -- "${expected_parser_path_file}" "${resolved_parser_path_file}"; then
  echo "SLH-DSA attested parser executable path mismatch" >&2
  cat -- "${resolved_parser_path_file}" >&2
  exit 1
fi
IFS= read -r resolved_parser_executable < "${resolved_parser_path_file}"
if [[ ! -f "${resolved_parser_executable}" || -L "${resolved_parser_executable}" ||
      ! -x "${resolved_parser_executable}" ]]; then
  echo "SLH-DSA attested parser executable is not an ordinary executable file" >&2
  exit 1
fi
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py \
  --sha256-ordinary-file "${resolved_parser_executable}" \
  "${fresh_parser_build_root}" "${before_parser_hash_file}"
require_bound_parser_hash_files \
  "${expected_parser_hash_file}" \
  "${before_parser_hash_file}" \
  "${before_parser_hash_file}"
parser_runtime_status=0
if run_parser_stdout_gate "${parser_gate_root}/parser.stdout" \
    "${resolved_parser_executable}"; then
  parser_runtime_status=0
else
  parser_runtime_status=$?
fi
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/slhdsa/check-harness.py \
  --sha256-ordinary-file "${resolved_parser_executable}" \
  "${fresh_parser_build_root}" "${after_parser_hash_file}"
require_bound_parser_hash_files \
  "${expected_parser_hash_file}" \
  "${before_parser_hash_file}" \
  "${after_parser_hash_file}"
if [[ "${parser_runtime_status}" -ne 0 ]]; then
  exit "${parser_runtime_status}"
fi
# The `-KbuildDir` query re-elaborates Lake's persistent package configuration for the disposable
# output. After every bound runtime/hash check is complete, explicitly restore the byte-pinned
# default. The EXIT trap performs the same restoration before temp-root deletion on every ordinary
# success, failure, errexit, or handled signal path; SIGKILL cannot execute shell cleanup traps.
restore_default_lake_configuration
lake env lean scripts/slhdsa/S02InventoryProbe.lean
lake env lean scripts/slhdsa/S03InventoryProbe.lean
lake env lean scripts/slhdsa/S04InventoryProbe.lean
lake env lean scripts/slhdsa/S05InventoryProbe.lean
lake env lean scripts/slhdsa/PolicyAudit.lean

fixture_root="$(mktemp -d)"
fixture_source_root="${script_dir}/fixtures"
fixture_sentinel="${fixture_root}/initializer-executed"
mkdir -p "${fixture_root}/HashSig"

lake env lean -R "${fixture_source_root}" \
  -o "${fixture_root}/SLHDSAPolicyIRMacro.olean" \
  -i "${fixture_root}/SLHDSAPolicyIRMacro.ilean" \
  -c "${fixture_root}/SLHDSAPolicyIRMacro.c" \
  "${fixture_source_root}/SLHDSAPolicyIRMacro.lean"
lake env env LEAN_PATH="${fixture_root}:${LEAN_PATH:-}" lean -R "${fixture_source_root}" \
  -o "${fixture_root}/HashSig/PolicyIRFixture.olean" \
  -i "${fixture_root}/HashSig/PolicyIRFixture.ilean" \
  -c "${fixture_root}/HashSig/PolicyIRFixture.c" \
  "${fixture_source_root}/HashSig/PolicyIRFixture.lean"
test -s "${fixture_root}/HashSig/PolicyIRFixture.ir"
test ! -e "${fixture_sentinel}"
SLHDSA_POLICY_RUN_IR_FIXTURE=1 \
SLHDSA_POLICY_SENTINEL="${fixture_sentinel}" \
  lake env env LEAN_PATH="${fixture_root}:${LEAN_PATH:-}" \
    lean scripts/slhdsa/PolicyAudit.lean
test ! -e "${fixture_sentinel}"

lake exe mk_all --lib HashSig --module --check
bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh
lake exe slhdsa_kat
lake exe slhdsa_c13_kat
lake exe slhdsa_data_codec_tests
lake exe slhdsa_primitive_tests
lake exe slhdsa_wots_tests

echo "SLH-DSA full baseline validation: PASS"
