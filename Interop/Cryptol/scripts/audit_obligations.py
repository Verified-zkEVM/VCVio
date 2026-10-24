#!/usr/bin/env python3
"""Audit named Cryptol proof obligations against compiled kernel dependencies.

This is a local policy over PolyFun's axiom report. PolyFun's own zero-debt
policy is unchanged. Only explicitly recorded theorem admissions are eligible;
admitted definitions, native trust, extra axioms, and stale ledger rows fail.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

STANDARD = {"propext", "Classical.choice", "Quot.sound", "sorryAx"}


def audit(report, ledger):
    if ledger.get("version") != 1 or "sorryGraph" not in report:
        raise ValueError("unsupported ledger or dependency report; rebuild the scanner")
    entries = {e["name"]: e for e in report["declarations"]}
    graph = {e["name"]: e for e in report["sorryGraph"]}
    obligations = {e["declaration"]: e for e in ledger["obligations"]}
    if len(obligations) != len(ledger["obligations"]):
        raise ValueError("duplicate obligation identity")
    for entry in entries.values():
        if set(entry["axioms"]) - STANDARD:
            raise ValueError(f"nonstandard axiom dependency: {entry['name']}")
    direct = {n for n, e in graph.items() if e["direct"]}
    if direct != obligations.keys():
        raise ValueError(f"unlisted admissions: {sorted(direct - obligations.keys())}; "
                         f"stale obligations: {sorted(obligations.keys() - direct)}")
    for name, obligation in obligations.items():
        entry = graph[name]
        if entry["kind"] != "theorem" or not name.startswith("Cryptol."):
            raise ValueError(f"only named Cryptol proof admissions are eligible: {name}")
        if hashlib.sha256(entry["type"].encode()).hexdigest() != obligation["type_sha256"]:
            raise ValueError(f"changed obligation proposition: {name}")
        for field in ("proposition", "source", "owner", "reason"):
            if not obligation.get(field):
                raise ValueError(f"missing {field} for {name}")
        if obligation["proposition"] != entry["type"]:
            raise ValueError(f"ledger proposition differs from the elaborated type: {name}")
    # A fixed point handles mutual declaration cycles and generated auxiliaries.
    inherited = {n: ({n} if e["direct"] else set()) for n, e in graph.items()}
    changed = True
    while changed:
        changed = False
        for name, entry in graph.items():
            for dependency in entry["dependencies"]:
                if dependency not in graph:
                    raise ValueError(f"incomplete dependency graph: {name} -> {dependency}")
                before = len(inherited[name])
                inherited[name].update(inherited[dependency])
                changed |= len(inherited[name]) != before
    result = []
    for name, entry in sorted(entries.items()):
        debt = sorted(inherited.get(name, set()))
        if ("sorryAx" in entry["axioms"]) != bool(debt):
            raise ValueError(f"unexplained or inconsistent sorry taint: {name}")
        result.append({"declaration": name, "obligations": debt,
                       "status": "conditional" if debt else "no-admissions"})
    return {"version": 1, "obligations": ledger["obligations"], "declarations": result}


def audit_warnings(log, report, ledger, root):
    """Permit only the exact sorry diagnostic at a recorded theorem's source location."""
    names = {o["declaration"] for o in ledger["obligations"]}
    allowed = {(str((root / (e["module"].replace(".", "/") + ".lean")).resolve()), e["line"])
               for e in report["declarations"] if e["name"] in names}
    for line in log.splitlines():
        if not line.startswith("warning:"):
            continue
        match = re.fullmatch(r"warning: (.+):(\d+):(\d+): declaration uses `sorry`", line)
        if not match or (str((root / match[1]).resolve()), int(match[2])) not in allowed:
            raise ValueError(f"unaccounted build warning: {line}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--warnings", type=Path)
    args = parser.parse_args()
    report, ledger = json.loads(args.report.read_text()), json.loads(args.ledger.read_text())
    result = audit(report, ledger)
    if args.warnings:
        audit_warnings(args.warnings.read_text(), report, ledger, Path.cwd())
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"Obligations: {len(result['obligations'])} named admissions; "
          f"{sum(bool(d['obligations']) for d in result['declarations'])} conditional declarations")


if __name__ == "__main__":
    main()
