#!/usr/bin/env python3
"""Parity of the event laws between the flat interpretation and its transformer copies.

The event and expectation laws of `VCVio/EvalDist/ProbabilityNotation.lean` and
`VCVio/EvalDist/ProbabilityBounds.lean` (`prEvent_*`, `wp_*`, `prFail_*`) are restated for
`OptionT` in `VCVio/EvalDist/Monad/Option.lean` and for `ExceptT` in
`VCVio/EvalDist/Monad/Except.lean`, where the lifted expectation is only propositionally the
expectation over the run. This script lists the flat laws without an `OptionT` or `ExceptT`
twin, the `OptionT` laws without an `ExceptT` twin, and the twins whose rewriting attributes
(`simp`, `grind`, `expect_norm`, `expect_eval`, `expect_arith`, `gcongr`) differ from the flat
law's. `scripts/lifted_law_parity_baseline.json` lists the known gaps. `--check` fails on a gap
the baseline does not list and on an obsolete entry (the lists only shrink);
`--update-baseline` rewrites it.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE = REPO_ROOT / "scripts" / "lifted_law_parity_baseline.json"
FLAT_FILES = ["VCVio/EvalDist/ProbabilityNotation.lean", "VCVio/EvalDist/ProbabilityBounds.lean"]
LIFTED_FILES = {"OptionT": "VCVio/EvalDist/Monad/Option.lean",
                "ExceptT": "VCVio/EvalDist/Monad/Except.lean"}
LAW_PREFIXES = ("prEvent_", "wp_", "prFail_")
TRACKED_ATTRS = ("simp", "grind", "expect_norm", "expect_eval", "expect_arith", "gcongr")
DECL_RE = re.compile(
    r"^(?:@\[(?P<attrs>[^\]]*)\]\s*)?(?:protected\s+|private\s+)?(?:theorem|lemma)\s+"
    r"(?P<name>[\w.'!?₀-₉ₐ-ₜᵢ-ᵪ]+)", re.M)
NAMESPACE_RE = re.compile(r"^(namespace|end)\s+([\w.'₀-₉ₐ-ₜᵢ-ᵪ]+)\s*$", re.M)
CATEGORIES = ("optionT_missing", "exceptT_missing", "exceptT_missing_of_optionT",
              "attribute_mismatch")


def attribute_kinds(attrs: str | None) -> set[str]:
    """The tracked attribute kinds in an attribute list, by their first word."""
    kinds: set[str] = set()
    for token in (attrs or "").split(","):
        head = token.strip().split(" ")[0].rstrip("↓↑")
        head = head.split("]")[0]
        if head in TRACKED_ATTRS:
            kinds.add(head)
    return kinds


def namespace_at(text: str, position: int) -> str:
    stack: list[str] = []
    for m in NAMESPACE_RE.finditer(text, 0, position):
        if m.group(1) == "namespace":
            stack.append(m.group(2))
        elif stack and stack[-1] == m.group(2):
            stack.pop()
    return ".".join(stack)


def declarations(text: str) -> dict[str, tuple[str, set[str]]]:
    """Theorems of a file: short name ↦ (namespace, tracked attribute kinds)."""
    decls: dict[str, tuple[str, set[str]]] = {}
    for m in DECL_RE.finditer(text):
        decls[m.group("name")] = (namespace_at(text, m.start()), attribute_kinds(m.group("attrs")))
    return decls


def flat_laws(sources: dict[str, str]) -> dict[str, set[str]]:
    laws: dict[str, set[str]] = {}
    for text in sources.values():
        for name, (ns, kinds) in declarations(text).items():
            if ns == "" and name.startswith(LAW_PREFIXES):
                laws[name] = kinds
    return laws


def lifted_laws(text: str, stack: str) -> dict[str, set[str]]:
    return {name: kinds for name, (ns, kinds) in declarations(text).items() if ns == stack}


def parity(flat: dict[str, set[str]], optionT: dict[str, set[str]],
           exceptT: dict[str, set[str]]) -> dict[str, list[str]]:
    report = {c: [] for c in CATEGORIES}
    for name in sorted(flat):
        if name not in optionT:
            report["optionT_missing"].append(name)
        if name not in exceptT:
            report["exceptT_missing"].append(name)
    for name in sorted(optionT):
        if name not in exceptT:
            report["exceptT_missing_of_optionT"].append(name)
    for name in sorted(flat):
        for stack, laws in (("OptionT", optionT), ("ExceptT", exceptT)):
            if name in laws and laws[name] != flat[name]:
                report["attribute_mismatch"].append(
                    f"{name}: flat {sorted(flat[name])}, {stack} {sorted(laws[name])}")
    return report


def load_baseline(path: Path) -> dict[str, list[str]]:
    if not path.exists():
        return {c: [] for c in CATEGORIES}
    data = json.loads(path.read_text(encoding="utf-8"))
    return {c: list(data.get(c, [])) for c in CATEGORIES}


def write_baseline(path: Path, report: dict[str, list[str]]) -> None:
    path.write_text(json.dumps({c: sorted(report[c]) for c in CATEGORIES}, indent=2) + "\n",
                    encoding="utf-8")


def compare(report: dict[str, list[str]], baseline: dict[str, list[str]]) -> list[str]:
    """The failures of a check: new gaps, and baseline entries that no longer exist."""
    failures = []
    for c in CATEGORIES:
        for entry in sorted(set(report[c]) - set(baseline[c])):
            failures.append(f"new gap ({c}): {entry}")
        for entry in sorted(set(baseline[c]) - set(report[c])):
            failures.append(f"obsolete baseline entry ({c}): {entry}")
    return failures


def render(report: dict[str, list[str]]) -> str:
    lines = []
    for c in CATEGORIES:
        lines.append(f"{c}: {len(report[c])}")
        lines.extend(f"  {entry}" for entry in report[c])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--check", action="store_true", help="gate against the baseline")
    parser.add_argument("--update-baseline", action="store_true",
                        help="rewrite the baseline from this run")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args()
    if args.check and args.update_baseline:
        parser.error("--check and --update-baseline are mutually exclusive")
    flat = flat_laws({f: (REPO_ROOT / f).read_text(encoding="utf-8") for f in FLAT_FILES})
    lifted = {stack: lifted_laws((REPO_ROOT / f).read_text(encoding="utf-8"), stack)
              for stack, f in LIFTED_FILES.items()}
    report = parity(flat, lifted["OptionT"], lifted["ExceptT"])
    if args.update_baseline:
        write_baseline(args.baseline, report)
        print(f"lifted-law parity: baseline written to {args.baseline.relative_to(REPO_ROOT)}")
        return 0
    print(render(report))
    if args.check:
        failures = compare(report, load_baseline(args.baseline))
        if failures:
            print("lifted-law parity: FAIL")
            print("\n".join(failures))
            return 1
        print("lifted-law parity: OK (matches the baseline)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
