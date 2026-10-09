#!/usr/bin/env python3
"""Keep the retiring SPMF backend from spreading through the import graph.

The baseline lists every module whose transitive imports reach
`ToMathlib.ProbabilityTheory.SPMF`, the retiring discrete-distribution backend. A module that
newly reaches it fails the check, as does a baseline entry that no longer does: the baseline is
exact, so each conversion that frees a module records the gain. Only obsolete entries may be
removed automatically (`--prune-baseline`); a new entry needs an explicit, reviewable baseline
edit.

The graph is read from `import` lines, so the check needs no build. Library umbrella modules
(`VCVio.lean`, …) import everything and are not tracked; test libraries import those umbrellas and
are not tracked either.

Usage:
  scripts/check-spmf-closure.py                   # exact check against the baseline
  scripts/check-spmf-closure.py --prune-baseline  # drop entries that no longer reach SPMF
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

TARGET = "ToMathlib.ProbabilityTheory.SPMF"
LIBRARIES = ("ToMathlib", "VCVio", "VCVioCslib", "LatticeCrypto", "HashSig", "Examples",
             "Extern", "VCVioWidgets")
IMPORT_RE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.MULTILINE)


def module_name(root: Path, path: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def read_graph(root: Path, libraries: tuple[str, ...]) -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    for library in libraries:
        directory = root / library
        if not directory.is_dir():
            continue
        for path in sorted(directory.rglob("*.lean")):
            text = path.read_text(encoding="utf-8")
            graph[module_name(root, path)] = IMPORT_RE.findall(text)
    return graph


def reaching(graph: dict[str, list[str]], target: str) -> set[str]:
    memo: dict[str, bool] = {}

    def reaches(module: str, stack: frozenset[str]) -> bool:
        if module == target:
            return True
        if module in memo:
            return memo[module]
        if module in stack:
            return False
        result = any(reaches(imported, stack | {module}) for imported in graph.get(module, ()))
        memo[module] = result
        return result

    return {module for module in graph if module != target and reaches(module, frozenset())}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--baseline", type=Path, default=None)
    parser.add_argument("--prune-baseline", action="store_true")
    args = parser.parse_args()
    root: Path = args.root
    baseline_path: Path = args.baseline or root / "scripts" / "spmf_closure_baseline.txt"

    current = reaching(read_graph(root, LIBRARIES), TARGET)
    baseline = set()
    if baseline_path.exists():
        baseline = {line.strip() for line in baseline_path.read_text(encoding="utf-8").splitlines()
                    if line.strip() and not line.startswith("#")}

    added = sorted(current - baseline)
    obsolete = sorted(baseline - current)

    if args.prune_baseline:
        if added:
            print("SPMF closure: refusing to prune while new modules reach SPMF:", file=sys.stderr)
            for module in added:
                print(f"  {module}", file=sys.stderr)
            return 1
        baseline_path.write_text("".join(f"{m}\n" for m in sorted(baseline & current)),
                                 encoding="utf-8")
        print(f"SPMF closure: pruned {len(obsolete)} entries; {len(baseline & current)} remain.")
        return 0

    status = 0
    if added:
        status = 1
        print(f"SPMF closure: {len(added)} module(s) newly reach {TARGET}:", file=sys.stderr)
        for module in added:
            print(f"  {module}", file=sys.stderr)
        print("Import native modules instead, or add the entry to the baseline with a reason.",
              file=sys.stderr)
    if obsolete:
        status = 1
        print(f"SPMF closure: {len(obsolete)} baseline entr{'y' if len(obsolete) == 1 else 'ies'} "
              "no longer reach SPMF:", file=sys.stderr)
        for module in obsolete:
            print(f"  {module}", file=sys.stderr)
        print("Run scripts/check-spmf-closure.py --prune-baseline.", file=sys.stderr)
    if status == 0:
        print(f"SPMF closure: {len(current)} modules reach {TARGET}, matching the baseline.")
    return status


if __name__ == "__main__":
    sys.exit(main())
