#!/usr/bin/env python3
"""Compare two per-module compile-time tables against a budget.

Both tables have the format `module_times.py` writes: `{"schema_version", "commit", "modules":
{module: {"seconds", "decimals"}}}`. A module is over budget when it is in both tables and its time
grew by more than `--budget-abs` seconds and by more than `--budget-rel` of its earlier time: the
absolute threshold keeps fast modules from tripping on noise, the relative one keeps slow modules
from tripping on proportionally small changes. The total over the modules in both tables is over
budget when it grew by more than `--total-rel`.

The times are wall-clock under whatever parallel load the measuring build had, so a module over
budget in one CI run is a pointer for a sequential profile (`lake env lean -Dprofiler=true`), not a
verdict. `--gate` exits 1 when anything is over budget, for comparisons whose measurements are
comparable, such as two sequential replays on one machine.
"""

from __future__ import annotations

import argparse
import pathlib
import sys
from dataclasses import dataclass
from typing import Any

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from module_times import load_table, source_path  # noqa: E402

DEFAULT_BUDGET_ABS = 5.0
DEFAULT_BUDGET_REL = 0.5
DEFAULT_TOTAL_REL = 0.05


@dataclass(frozen=True)
class Change:
    """A module measured in both tables."""

    module: str
    before: float
    after: float

    @property
    def delta(self) -> float:
        return self.after - self.before

    @property
    def ratio(self) -> float:
        return self.after / self.before if self.before > 0 else float("inf")


@dataclass(frozen=True)
class Comparison:
    """The modules of two tables, compared."""

    changes: list[Change]
    added: list[str]
    removed: list[str]

    @property
    def total_before(self) -> float:
        return sum(change.before for change in self.changes)

    @property
    def total_after(self) -> float:
        return sum(change.after for change in self.changes)


def compare(base: dict[str, Any], current: dict[str, Any]) -> Comparison:
    """Pair the modules the two tables share; list the ones only one of them has."""
    before, after = base["modules"], current["modules"]
    changes = [Change(module, before[module]["seconds"], after[module]["seconds"])
               for module in sorted(before.keys() & after.keys())]
    return Comparison(changes, sorted(after.keys() - before.keys()),
                      sorted(before.keys() - after.keys()))


def over_budget(comparison: Comparison, budget_abs: float, budget_rel: float) -> list[Change]:
    """The modules whose time grew by more than both thresholds, largest growth first."""
    over = [change for change in comparison.changes
            if change.delta > budget_abs and change.delta > budget_rel * change.before]
    return sorted(over, key=lambda change: change.delta, reverse=True)


def total_over_budget(comparison: Comparison, total_rel: float) -> bool:
    before = comparison.total_before
    return before > 0 and comparison.total_after - before > total_rel * before


def render_markdown(comparison: Comparison, budget_abs: float, budget_rel: float,
                    total_rel: float) -> str:
    """The budget section of a timing report."""
    over = over_budget(comparison, budget_abs, budget_rel)
    before, after = comparison.total_before, comparison.total_after
    lines = [
        f"Budget: a module is over when its time grows by more than {budget_abs:g}s and more "
        f"than {budget_rel:.0%} of its earlier time; the total, when it grows by more than "
        f"{total_rel:.0%}.",
        "",
    ]
    if before > 0:
        flag = " (over budget)" if total_over_budget(comparison, total_rel) else ""
        lines += [f"Total over the {len(comparison.changes)} modules measured in both tables: "
                  f"{before:.0f}s before, {after:.0f}s after "
                  f"({(after - before) / before:+.1%}){flag}.", ""]
    if not over:
        lines.append("No module is over budget.")
        return "\n".join(lines)
    lines += ["| Module | Before (s) | After (s) | Delta (s) | Ratio |",
              "| --- | ---: | ---: | ---: | ---: |"]
    for change in over:
        lines.append(f"| `{source_path(change.module)}` | {change.before:.1f} | "
                     f"{change.after:.1f} | {change.delta:+.1f} | {change.ratio:.2f} |")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("base", type=pathlib.Path, help="the earlier table")
    parser.add_argument("current", type=pathlib.Path, help="the later table")
    parser.add_argument("--budget-abs", type=float, default=DEFAULT_BUDGET_ABS,
                        help="seconds a module may grow by (default %(default)s)")
    parser.add_argument("--budget-rel", type=float, default=DEFAULT_BUDGET_REL,
                        help="fraction of its earlier time a module may grow by "
                             "(default %(default)s)")
    parser.add_argument("--total-rel", type=float, default=DEFAULT_TOTAL_REL,
                        help="fraction the total may grow by (default %(default)s)")
    parser.add_argument("--gate", action="store_true",
                        help="exit 1 when a module or the total is over budget")
    args = parser.parse_args(argv)
    base, current = load_table(args.base), load_table(args.current)
    if base is None or current is None:
        missing = args.base if base is None else args.current
        print(f"compare_module_times: no readable module table at {missing}", file=sys.stderr)
        return 2
    comparison = compare(base, current)
    print(render_markdown(comparison, args.budget_abs, args.budget_rel, args.total_rel))
    over = over_budget(comparison, args.budget_abs, args.budget_rel)
    if args.gate and (over or total_over_budget(comparison, args.total_rel)):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
