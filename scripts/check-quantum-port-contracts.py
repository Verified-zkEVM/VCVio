#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Compare elaborated QROM statements and exposed semantic definitions.

No rename or alpha normalization is silently accepted. Raw differences are always
reported; --rename provides a separately labelled comparison view for review.
The optional --modules file scopes a comparison to a reconstructed PR's modules.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path


def canonical(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def digest(value: object) -> str:
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def alpha(expr: object, levels: list[str], renames: dict[str, str]) -> object:
    if not isinstance(expr, list):
        return expr
    if not expr:
        return []
    tag = expr[0]
    if not isinstance(tag, str):
        return [alpha(e, levels, renames) for e in expr]
    if tag in {"forall", "lam"}:
        return [tag, "_", expr[2], alpha(expr[3], levels, renames),
                alpha(expr[4], levels, renames)]
    if tag == "let":
        return [tag, "_", expr[2], *(alpha(e, levels, renames) for e in expr[3:])]
    if tag == "param" and expr[1] in levels:
        return [tag, levels.index(expr[1])]
    if tag in {"const", "proj"}:
        return [tag, renames.get(expr[1], expr[1]),
                *(alpha(e, levels, renames) for e in expr[2:])]
    return [alpha(e, levels, renames) for e in expr]


def compare(before: dict, after: dict, renames: dict[str, str]) -> dict:
    changed = []
    for field in ["kind", "levelParameters", "type", "reducibility", "value"]:
        if before[field] != after[field]:
            changed.append(field)
    return {
        "name": before["name"],
        "changed": changed,
        "rawTypeEqual": before["type"] == after["type"],
        "alphaTypeEqual": alpha(before["type"], before["levelParameters"], {}) ==
            alpha(after["type"], after["levelParameters"], {}),
        "approvedRenameAlphaTypeEqual":
            alpha(before["type"], before["levelParameters"], renames) ==
            alpha(after["type"], after["levelParameters"], {}),
        "rawValueEqual": before["value"] == after["value"],
        "alphaValueEqual": alpha(before["value"], before["levelParameters"], {}) ==
            alpha(after["value"], after["levelParameters"], {}),
        "beforeTypeSHA256": digest(before["type"]),
        "afterTypeSHA256": digest(after["type"]),
        "beforeValueSHA256": digest(before["value"]),
        "afterValueSHA256": digest(after["value"]),
        "typeDiff": list(difflib.unified_diff(
            before["typePretty"].splitlines(), after["typePretty"].splitlines(),
            fromfile="before", tofile="after", lineterm="")),
        "valueDiff": list(difflib.unified_diff(
            (before["valuePretty"] or "").splitlines(),
            (after["valuePretty"] or "").splitlines(),
            fromfile="before", tofile="after", lineterm="")),
    }


def noncomment_lines(path: Path | None) -> list[str]:
    if path is None:
        return []
    return [line.strip() for line in path.read_text().splitlines()
            if line.strip() and not line.lstrip().startswith("#")]


def capture(a) -> int:
    tool = Path(__file__).with_name("QuantumPortContracts.lean")
    args = ["lake", "env", "lean", "--run", str(tool), ""]
    for name in a.root:
        args += ["--root", name]
    modules = a.module + noncomment_lines(a.modules_file)
    declarations = a.decl + noncomment_lines(a.declarations_file)
    if a.modules_file is not None and not modules:
        raise ValueError("requested module scope is empty")
    if a.declarations_file is not None and not declarations:
        raise ValueError("requested declaration scope is empty")
    if modules and declarations:
        raise ValueError("choose module scope or declaration scope, not both")
    for name in modules:
        args += ["--module", name]
    for name in declarations:
        args += ["--decl", name]
    if a.check_against:
        args += ["--check-against", str(a.check_against.resolve())]
    with tempfile.TemporaryDirectory(prefix=".qrom-contract-capture-",
                                     dir=a.output.resolve().parent) as scratch:
        intermediate = Path(scratch) / "snapshot.json"
        args[5] = str(intermediate)
        result = subprocess.run(args, cwd=a.worktree)
        if result.returncode not in {0, 1} or not intermediate.exists():
            raise subprocess.CalledProcessError(result.returncode or 2, args)
        d = json.loads(intermediate.read_text())
        compatibility = d.get("kernelCompatibility")
        rejected = bool(compatibility and any(not r["kernelAccepted"]
                        for r in compatibility["declarations"]))
        if result.returncode != int(rejected):
            raise ValueError("inspector status disagrees with kernel-compatibility report")
        # Keep the complete freshly generated document in memory before publishing it below.
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=a.worktree, text=True).strip()
    module_names = set(d["selectedModules"] + d["semanticModules"] + modules +
                       [r["module"] for r in d["declarations"]])
    source_hashes = {}
    for module in sorted(module_names):
        path = a.worktree / (module.replace(".", "/") + ".lean")
        if path.exists():
            source_hashes[module] = hashlib.sha256(path.read_bytes()).hexdigest()
    d["provenance"] = {
        "commit": git("rev-parse", "HEAD"),
        "workingTreeStatus": git("status", "--porcelain"),
        "toolchain": (a.worktree / "lean-toolchain").read_text().strip(),
        "lakeManifest": json.loads((a.worktree / "lake-manifest.json").read_text()),
        "inspectorSHA256": hashlib.sha256(tool.read_bytes()).hexdigest(),
        "sourceSHA256": source_hashes,
    }
    with tempfile.TemporaryDirectory(prefix=".qrom-contract-publish-",
                                     dir=a.output.resolve().parent) as scratch:
        final = Path(scratch) / "snapshot.json"
        final.write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n")
        final.replace(a.output)
    print(f"Captured {len(d['declarations'])} declarations from {d['provenance']['commit']}")
    compatibility = d.get("kernelCompatibility")
    if compatibility and any(not r["kernelAccepted"] for r in compatibility["declarations"]):
        return 1
    return 0


def compare_command(a) -> int:
    renames = dict(s.split("=", 1) for s in a.rename)
    old = json.loads(a.before.read_text())
    new = json.loads(a.after.read_text())
    if old.get("format") != "qrom-port-signatures-v1" or old.get("format") != new.get("format"):
        raise ValueError("missing or incompatible contract schemas")
    old_tool = old.get("provenance", {}).get("inspectorSHA256")
    new_tool = new.get("provenance", {}).get("inspectorSHA256")
    if not old_tool or old_tool != new_tool:
        raise ValueError("snapshots must use the same recorded inspector SHA-256")
    modules = set(noncomment_lines(a.modules)) if a.modules else None
    if modules is not None and not modules:
        raise ValueError("module scope is empty")
    def index(blob):
        names = [r["name"] for r in blob["declarations"]]
        if len(names) != len(set(names)):
            raise ValueError("duplicate declaration names in contract snapshot")
        coverage = {r["module"] for r in blob["declarations"]}
        if modules is not None and modules - coverage:
            raise ValueError("requested module has no captured declarations: " +
                             ", ".join(sorted(modules - coverage)))
        return {r["name"]: r for r in blob["declarations"]
                if modules is None or r["module"] in modules}
    before, after = index(old), index(new)
    shared = sorted(before.keys() & after.keys())
    if not before or not after or not shared:
        raise ValueError("contract scope must contain shared declarations")
    reports = [compare(before[n], after[n], renames) for n in shared]
    priority = set(old["priorityHeadlines"])
    changed = [r for r in reports if r["changed"]]
    compatibility = new.get("kernelCompatibility")
    kernel_failures = [r["name"] for r in compatibility["declarations"]
                       if not r["kernelAccepted"]] if compatibility else []
    missing = sorted(before.keys() - after.keys())
    added = sorted(after.keys() - before.keys())
    result = {
        "beforeFileSHA256": hashlib.sha256(a.before.read_bytes()).hexdigest(),
        "afterFileSHA256": hashlib.sha256(a.after.read_bytes()).hexdigest(),
        "beforeLean": old["leanVersion"], "afterLean": new["leanVersion"],
        "renamesForSeparateComparisonOnly": renames,
        "moduleScope": sorted(modules) if modules else None,
        "beforeDeclarations": len(before), "afterDeclarations": len(after),
        "sharedDeclarations": len(shared), "missing": missing, "added": added,
        "priorityHeadlines": [r for r in reports if r["name"] in priority],
        "priorityMissing": sorted(priority & before.keys() - after.keys()),
        "kernelCompatibilityFailures": kernel_failures,
        "changes": changed,
        "summary": {
            "rawTypeChanges": sum(not r["rawTypeEqual"] for r in reports),
            "alphaTypeChanges": sum(not r["alphaTypeEqual"] for r in reports),
            "approvedRenameAlphaTypeChanges":
                sum(not r["approvedRenameAlphaTypeEqual"] for r in reports),
            "definitionValueChanges": sum(not r["rawValueEqual"] for r in reports),
            "reducibilityChanges": sum("reducibility" in r["changed"] for r in reports),
            "priorityRawTypeChanges":
                sum(not r["rawTypeEqual"] for r in reports if r["name"] in priority),
            "priorityAlphaTypeChanges":
                sum(not r["alphaTypeEqual"] for r in reports if r["name"] in priority),
        },
    }
    a.out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({k: result[k] for k in ["beforeDeclarations", "afterDeclarations",
        "sharedDeclarations", "missing", "added", "summary"]}, indent=2))
    return int(bool(changed or missing or added or kernel_failures))

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    cap = sub.add_parser("capture", help="inspect a compiled worktree with its own toolchain")
    cap.add_argument("worktree", type=Path)
    cap.add_argument("output", type=Path)
    cap.add_argument("--root", action="append", default=[])
    cap.add_argument("--module", action="append", default=[])
    cap.add_argument("--modules-file", type=Path)
    cap.add_argument("--decl", action="append", default=[])
    cap.add_argument("--declarations-file", type=Path)
    cap.add_argument("--check-against", type=Path)
    cmp = sub.add_parser("compare", help="report every raw type/body/reducibility difference")
    cmp.add_argument("before", type=Path)
    cmp.add_argument("after", type=Path)
    cmp.add_argument("--out", type=Path, required=True)
    cmp.add_argument("--modules", type=Path)
    cmp.add_argument("--rename", action="append", default=[], metavar="OLD=NEW")
    a = p.parse_args()
    try:
        if a.command == "capture":
            return capture(a)
        return compare_command(a)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f"Quantum port contracts: infrastructure error: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
