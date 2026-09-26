#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  build_timing_report.sh run <label> <results-file> -- <command> [args...]
  build_timing_report.sh render <results-file>

Labels:
  library_build
  test_path
EOF
}

append_result() {
  local results_file="$1"
  local label="$2"
  local real_time="$3"
  local user_time="$4"
  local sys_time="$5"
  local exit_code="$6"

  python3 - "$results_file" "$label" "$real_time" "$user_time" "$sys_time" "$exit_code" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
path.parent.mkdir(parents=True, exist_ok=True)

record = {
    "label": sys.argv[2],
    "real": float(sys.argv[3]),
    "user": float(sys.argv[4]),
    "sys": float(sys.argv[5]),
    "exit_code": int(sys.argv[6]),
}

with path.open("a", encoding="utf-8") as handle:
    handle.write(json.dumps(record) + "\n")
PY
}

run_command() {
  if [ "$#" -lt 4 ]; then
    usage
    exit 2
  fi

  local label="$1"
  local results_file="$2"
  shift 2

  if [ "$1" != "--" ]; then
    usage
    exit 2
  fi
  shift

  local timing_file
  timing_file="$(mktemp)"
  local log_dir="${BUILD_TIMING_LOG_DIR:-}"
  local log_file=""

  if [ -n "$log_dir" ]; then
    mkdir -p "$log_dir"
    log_file="$log_dir/${label}.log"
  fi

  set +e
  if [ -n "$log_file" ]; then
    /usr/bin/time -p -o "$timing_file" "$@" 2>&1 | tee "$log_file"
    local exit_code=${PIPESTATUS[0]}
  else
    /usr/bin/time -p -o "$timing_file" "$@"
    local exit_code=$?
  fi
  set -e

  local real_time user_time sys_time
  real_time="$(awk '$1 == "real" { print $2 }' "$timing_file")"
  user_time="$(awk '$1 == "user" { print $2 }' "$timing_file")"
  sys_time="$(awk '$1 == "sys" { print $2 }' "$timing_file")"
  rm -f "$timing_file"

  append_result "$results_file" "$label" "$real_time" "$user_time" "$sys_time" "$exit_code"
  exit "$exit_code"
}

render_report() {
  if [ "$#" -ne 1 ]; then
    usage
    exit 2
  fi

  local results_file="$1"

  python3 - "$results_file" <<'PY'
import json
import os
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path("scripts").resolve()))
from module_times import load_table, parse_logs, source_path, total_seconds

results_path = pathlib.Path(sys.argv[1])
# Build logs and module tables sit next to each other in the timing artifact.
data_dir = pathlib.Path(os.environ.get("BUILD_TIMING_LOG_DIR") or results_path.parent)
build_command = os.environ.get("BUILD_TIMING_BUILD_COMMAND", "lake build")
test_path_name = os.environ.get("BUILD_TIMING_TEST_NAME", "Test path")
test_path_command = os.environ.get("BUILD_TIMING_TEST_COMMAND", "lake test")
source_sha = os.environ.get("BUILD_TIMING_SOURCE_SHA")
source_subject = os.environ.get("BUILD_TIMING_SOURCE_SUBJECT")
source_branch = os.environ.get("BUILD_TIMING_SOURCE_BRANCH") or os.environ.get("GITHUB_REF_NAME")
source_repo = os.environ.get("GITHUB_REPOSITORY")

display = {
    "library_build": {"name": "Library build", "command": f"`{build_command}`"},
    "test_path": {"name": test_path_name, "command": f"`{test_path_command}`"},
}
ordered_labels = ["library_build", "test_path"]


def load_records(path: pathlib.Path) -> dict[str, dict]:
    records = {}
    if not path.exists():
        return records
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            record = json.loads(line)
            records[record["label"]] = record
    return records


def fmt_change(current: float, baseline: float) -> str:
    delta = current - baseline
    if baseline == 0:
        return f"{delta:+.0f}s"
    return f"{delta:+.0f}s ({delta / baseline:+.1%})"


def status(record: dict) -> str:
    return "ok" if record["exit_code"] == 0 else f"exit {record['exit_code']}"


def fmt_entry(entry: dict) -> str:
    return f"{entry['seconds']:.{entry['decimals']}f}"


def fmt_entry_delta(current: dict, baseline: dict) -> str:
    decimals = min(current["decimals"], baseline["decimals"])
    return f"{current['seconds'] - baseline['seconds']:+.{decimals}f}"


def commit_ref(sha: str | None) -> str:
    if not sha:
        return "`unknown`"
    if source_repo:
        return f"[`{sha[:7]}`](https://github.com/{source_repo}/commit/{sha})"
    return f"`{sha[:7]}`"


records = load_records(results_path)
base_table = load_table(data_dir / "module-times-base.json")
current_table = load_table(data_dir / "module-times.json")
built = parse_logs([data_dir / "library_build.log", data_dir / "test_build.log"])

print("## Build Timing Report")
print()
if source_sha:
    print(f"- Source: {commit_ref(source_sha)}")
if source_subject:
    print(f"- Message: {source_subject}")
if source_branch:
    print(f"- Ref: `{source_branch}`")
if base_table is not None:
    print(
        f"- Build cache: restored the build of {commit_ref(base_table['commit'])}; "
        "Lake rebuilt only modules whose source or imports differ from it."
    )
else:
    print("- Build cache: none restored, so the library build is a full build.")
print(
    "- Commands: "
    + "; ".join(
        f"{display[label]['name'].lower()} {display[label]['command']}" for label in ordered_labels
    )
    + "."
)
print()

if not records:
    print("No timing data was captured.")
    sys.exit(0)

print("| Measurement | Wall (s) | CPU work (s) | Status |")
print("| --- | ---: | ---: | --- |")
for label in ordered_labels:
    record = records.get(label)
    if record is None:
        continue
    print(
        f"| {display[label]['name']} | {record['real']:.2f} | "
        f"{record['user'] + record['sys']:.2f} | {status(record)} |"
    )
print()
print(
    "CPU work is `user + sys`. Wall time depends on which modules this run had to rebuild, so "
    "compare it across runs only together with the module section below."
)
print()
print("### Rebuilt Modules")
print()
if not built:
    print("No module was rebuilt: every module was already up to date in the restored build.")
    sys.exit(0)

baseline_modules = base_table["modules"] if base_table is not None else {}
rows = sorted(built.items(), key=lambda item: item[1]["seconds"], reverse=True)
compared = [(module, entry) for module, entry in rows if module in baseline_modules]
new_count = len(rows) - len(compared)
current_sum = sum(entry["seconds"] for _, entry in compared)
baseline_sum = sum(baseline_modules[module]["seconds"] for module, _ in compared)

if base_table is not None:
    print(
        f"Rebuilt {len(rows)} modules ({new_count} without an earlier time). The "
        f"{len(compared)} with an earlier time took {current_sum:.0f}s here against "
        f"{baseline_sum:.0f}s when last built ({fmt_change(current_sum, baseline_sum)})."
    )
    if current_table is not None:
        before = total_seconds(base_table)
        after = total_seconds(current_table)
        print()
        print(
            f"Estimated clean-build compile time, summed over all "
            f"{len(current_table['modules'])} modules: {before:.0f}s before, {after:.0f}s after "
            f"({fmt_change(after, before)})."
        )
else:
    print(f"Built {len(rows)} modules.")
    if current_table is not None:
        print()
        print(
            f"Clean-build compile time, summed over all {len(current_table['modules'])} "
            f"modules: {total_seconds(current_table):.0f}s."
        )
print()
print(
    "Per-module times are wall-clock under whatever parallel load the run had, so treat small "
    "differences as noise; a large change on one module is the signal."
)
print()
shown = rows[:20]
print(f"Showing {len(shown)} slowest of {len(rows)} rebuilt modules.")
print()
print("| Current (s) | Earlier (s) | Delta (s) | Path |")
print("| ---: | ---: | ---: | --- |")
for module, entry in shown:
    baseline_entry = baseline_modules.get(module)
    baseline_time = fmt_entry(baseline_entry) if baseline_entry else "-"
    delta = fmt_entry_delta(entry, baseline_entry) if baseline_entry else "-"
    print(f"| {fmt_entry(entry)} | {baseline_time} | {delta} | `{source_path(module)}` |")
PY
}

main() {
  if [ "$#" -lt 1 ]; then
    usage
    exit 2
  fi

  local command="$1"
  shift

  case "$command" in
    run)
      run_command "$@"
      ;;
    render)
      render_report "$@"
      ;;
    *)
      usage
      exit 2
      ;;
  esac
}

main "$@"
