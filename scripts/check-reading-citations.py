#!/usr/bin/env python3
"""Check the source citations of the reading documents.

The documents under `docs/reading/` cite sources as `K:path` or `K:path:line`, where `K` names
a tree: `V:` this repository, `M:` Mathlib, `B:` Batteries, `Cs:` cslib and `P:` PolyFun (the
checkouts under `.lake/packages`), and `C:` Lean core and Std (the toolchain's `src/lean`). A
line range `:a–b` or a list `:a,b` is checked at its first number. The path must exist in the
tree and the line must not run past the end of the file.

`V:` citations are always checked. The other trees are checked when they are present and
skipped otherwise; `--require-upstream` makes a missing tree a failure, for the local
validation run where the packages are checked out. Any failing citation fails the check.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKAGES = ROOT / ".lake" / "packages"
DOCS = ROOT / "docs" / "reading"

CITATION = re.compile(
    r"(?<![\w/])(Cs|V|M|B|C|P):([A-Za-z0-9_][A-Za-z0-9_./+-]*\.(?:lean|md|py|sh|json|toml|yml))"
    r"(?::(\d+))?"
)


def core_root() -> Path | None:
    """The `src/lean` tree of the pinned toolchain, if it is installed."""
    sysroot = os.environ.get("LEAN_SYSROOT")
    candidates = [Path(sysroot)] if sysroot else []
    toolchain_file = ROOT / "lean-toolchain"
    if toolchain_file.is_file():
        name = toolchain_file.read_text().strip().replace("/", "--").replace(":", "---")
        elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
        candidates.append(elan / "toolchains" / name)
    for candidate in candidates:
        if (candidate / "src" / "lean").is_dir():
            return candidate / "src" / "lean"
    return None


def tree_roots() -> dict[str, list[Path]]:
    roots: dict[str, list[Path]] = {
        "V": [ROOT],
        "M": [PACKAGES / "mathlib" / "Mathlib", PACKAGES / "mathlib"],
        "B": [PACKAGES / "batteries" / "Batteries", PACKAGES / "batteries"],
        "Cs": [PACKAGES / "cslib" / "Cslib", PACKAGES / "cslib"],
        "P": [PACKAGES / "PolyFun" / "PolyFun", PACKAGES / "PolyFun"],
    }
    core = core_root()
    roots["C"] = [core] if core else []
    return roots


def resolve(roots: list[Path], path: str) -> Path | None:
    for root in roots:
        candidate = root / path
        if candidate.is_file():
            return candidate
    return None


def line_count(path: Path, cache: dict[Path, int]) -> int:
    if path not in cache:
        with path.open("rb") as handle:
            cache[path] = sum(1 for _ in handle)
    return cache[path]


def check_file(doc: Path, roots: dict[str, list[Path]], require_upstream: bool,
               cache: dict[Path, int]) -> tuple[list[str], int, set[str]]:
    failures: list[str] = []
    checked = 0
    skipped: set[str] = set()
    for number, line in enumerate(doc.read_text(encoding="utf-8").splitlines(), 1):
        for tree, path, line_no in CITATION.findall(line):
            tree_paths = [root for root in roots[tree] if root.is_dir()]
            if not tree_paths:
                if require_upstream:
                    failures.append(f"{doc}:{number}: `{tree}:{path}` cites a tree that is not "
                                    f"checked out")
                else:
                    skipped.add(tree)
                continue
            target = resolve(tree_paths, path)
            if target is None:
                failures.append(f"{doc}:{number}: `{tree}:{path}` does not exist")
                continue
            checked += 1
            if line_no:
                total = line_count(target, cache)
                if int(line_no) > total:
                    failures.append(f"{doc}:{number}: `{tree}:{path}:{line_no}` runs past the end "
                                    f"of the file ({total} lines)")
    return failures, checked, skipped


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("files", nargs="*", type=Path,
                        help="documents to check (default: docs/reading/*.md)")
    parser.add_argument("--require-upstream", action="store_true",
                        help="fail on a citation into a tree that is not checked out")
    args = parser.parse_args()
    files = args.files or sorted(DOCS.glob("*.md"))
    roots = tree_roots()
    cache: dict[Path, int] = {}
    failures: list[str] = []
    checked = 0
    skipped: set[str] = set()
    for doc in files:
        doc_failures, doc_checked, doc_skipped = check_file(doc, roots, args.require_upstream,
                                                            cache)
        failures.extend(doc_failures)
        checked += doc_checked
        skipped |= doc_skipped
    for failure in failures:
        print(failure)
    note = f" (skipped trees not checked out: {', '.join(sorted(skipped))})" if skipped else ""
    if failures:
        print(f"Reading citations: {len(failures)} unresolved of {checked + len(failures)}{note}")
        return 1
    print(f"Reading citations: OK ({checked} checked in {len(files)} documents){note}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
