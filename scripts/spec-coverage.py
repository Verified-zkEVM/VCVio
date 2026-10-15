#!/usr/bin/env python3
"""Coverage of the registered `@[spec]` rules by the files that run `vcgen`.

The inventory is every `@[spec]` rule of the program logic, the scan behind the generated table
in `docs/agents/program-logic.md` (`scripts/extract-doc-fragments.py`). The applications come
from Lean's `trace.Elab.Tactic.Do.vcgen` trace over the files that exercise the rules: each line
`Applying spec SpecProof.global NAME for …` names a rule as it fires (a rule passed in brackets
fires the same way; `Failed to apply` lines do not count). The report is the matrix of rules by
file, and a rule that fires in no file is uncovered.

`scripts/spec_coverage_baseline.json` lists the rules known to be uncovered. `--check` fails when
a rule outside the list fires nowhere (a rule lost its test) or a listed rule now fires (an
obsolete entry: the list only shrinks); `--update-baseline` rewrites it. The trace runs elaborate
the files with `lake env lean`, after `lake build`; a `#guard_msgs` in a traced file fails under
the trace, which is not a verdict here (the build is the gate). `--save-traces DIR` keeps the
traces and `--traces DIR` reuses them instead of running Lean.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE = REPO_ROOT / "scripts" / "spec_coverage_baseline.json"
FRAGMENTS = REPO_ROOT / "scripts" / "extract-doc-fragments.py"
TRACE_OPTION = "trace.Elab.Tactic.Do.vcgen"
TRACE_FILES = [
    "VCVioTest/ProgramLogic/CoreVCGen.lean",
    "VCVioTest/ProgramLogic/CoreWP.lean",
    "VCVioTest/ProgramLogic/PrVCGen.lean",
    "VCVioTest/ProgramLogic/PossibleVCGen.lean",
    "VCVioTest/ProgramLogic/LowerVCGen.lean",
    "VCVioTest/ProgramLogic/UpperVCGen.lean",
]
APPLIED_RE = re.compile(r"Applying spec SpecProof\.\w+ ([^\s]+?)[.,]?(?:\s|$)")


def inventory() -> list[str]:
    """The registered rules, by full name."""
    spec = importlib.util.spec_from_file_location("fragments", FRAGMENTS)
    fragments = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fragments)
    return sorted({name for _, name, _, _ in fragments.extract_spec_rules()})


def parse_trace(text: str) -> dict[str, int]:
    """Rule applications in one trace, by rule name."""
    counts: dict[str, int] = defaultdict(int)
    for line in text.splitlines():
        match = APPLIED_RE.search(line)
        if match:
            counts[match.group(1)] += 1
    return dict(counts)


def run_trace(path: Path) -> str:
    """The trace of one file. The trace turns every `vcgen` into messages, so a `#guard_msgs`
    in the file fails under it and the status is not a verdict (the build is the gate); a file
    that does not elaborate at all leaves no trace and is reported."""
    result = subprocess.run(["lake", "env", "lean", f"-D{TRACE_OPTION}=true", str(path)],
                            cwd=REPO_ROOT, capture_output=True, text=True, encoding="utf-8")
    text = result.stdout + result.stderr
    if "[Elab.Tactic.Do.vcgen]" not in text:
        raise RuntimeError(f"no vcgen trace from {path} (status {result.returncode}):\n"
                           f"{text[-2000:]}")
    return text


def coverage(rules: list[str], traces: dict[str, str]) -> dict[str, dict[str, int]]:
    """The matrix rule → file → applications, over the inventory."""
    matrix: dict[str, dict[str, int]] = {rule: {} for rule in rules}
    for file, text in traces.items():
        for rule, count in parse_trace(text).items():
            if rule in matrix:
                matrix[rule][file] = count
    return matrix


def uncovered(matrix: dict[str, dict[str, int]]) -> list[str]:
    return sorted(rule for rule, files in matrix.items() if not files)


def compare(current: list[str], baseline: list[str]) -> tuple[list[str], list[str]]:
    """(rules uncovered but not in the baseline, baseline entries that are now covered)."""
    return (sorted(set(current) - set(baseline)), sorted(set(baseline) - set(current)))


def load_baseline(path: Path) -> list[str]:
    if not path.is_file():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    return sorted(data.get("uncovered", []))


def write_baseline(path: Path, rules: list[str]) -> None:
    path.write_text(json.dumps({"uncovered": sorted(rules)}, indent=2) + "\n", encoding="utf-8")


def render(matrix: dict[str, dict[str, int]], files: list[str]) -> str:
    short = {file: Path(file).stem for file in files}
    lines = ["| Rule | " + " | ".join(short[file] for file in files) + " |",
             "|---|" + "---:|" * len(files)]
    for rule in sorted(matrix):
        cells = [str(matrix[rule].get(file, "")) for file in files]
        lines.append(f"| `{rule}` | " + " | ".join(cells) + " |")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--check", action="store_true", help="gate against the baseline")
    parser.add_argument("--update-baseline", action="store_true",
                        help="rewrite the baseline from this run")
    parser.add_argument("--traces", type=Path, metavar="DIR",
                        help="reuse the traces saved in DIR instead of running Lean")
    parser.add_argument("--save-traces", type=Path, metavar="DIR", help="save the traces in DIR")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    parser.add_argument("files", nargs="*", default=TRACE_FILES,
                        help="files to trace (default: the program-logic test files)")
    args = parser.parse_args()
    if args.check and args.update_baseline:
        parser.error("--check and --update-baseline are mutually exclusive")
    traces: dict[str, str] = {}
    for file in args.files:
        if args.traces:
            traces[file] = (args.traces / (Path(file).stem + ".trace")).read_text(encoding="utf-8")
        else:
            traces[file] = run_trace(REPO_ROOT / file)
            if args.save_traces:
                args.save_traces.mkdir(parents=True, exist_ok=True)
                (args.save_traces / (Path(file).stem + ".trace")).write_text(
                    traces[file], encoding="utf-8")
    matrix = coverage(inventory(), traces)
    current = uncovered(matrix)
    print(render(matrix, list(args.files)))
    print(f"\nSpec coverage: {len(matrix) - len(current)} of {len(matrix)} registered rules fire "
          f"in {len(traces)} files; uncovered: {', '.join(current) or 'none'}")
    if args.update_baseline:
        write_baseline(args.baseline, current)
        print(f"Spec coverage: wrote {args.baseline}")
        return 0
    if args.check:
        regressions, obsolete = compare(current, load_baseline(args.baseline))
        for rule in regressions:
            print(f"{args.baseline}: `{rule}` fires in no traced file and is not in the baseline")
        for rule in obsolete:
            print(f"{args.baseline}: obsolete entry `{rule}` (it fires now; remove it)")
        if regressions or obsolete:
            print(f"Spec coverage: {len(regressions)} uncovered rules, {len(obsolete)} obsolete "
                  f"entries")
            return 1
        print("Spec coverage: OK (matches the baseline)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
