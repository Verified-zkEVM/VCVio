#!/usr/bin/env python3
"""Check frozen SLH-DSA contracts against fresh Lean elaboration and semantic capture.

This is a read-only baseline check. It never regenerates expected artifacts. JSON reads in
Lean commands are not Lake dependencies, so the four witness sources are always elaborated
freshly after their imports have been built. See the R0 README for the baseline's scope.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "docs/design/slh-dsa-reuse-evidence/r0"
CAPTURE_MODULE = "HashSigTest.SLHDSA.Refactor.Capture"
STRENGTH_MODULE = "HashSigTest.SLHDSA.Refactor.StrengthContracts"


def canonical(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def semantic_records(capture: dict) -> dict[str, dict]:
    """Fingerprint all kernel syntax, ownership, calling convention and axioms, not rendering."""
    records = {}
    for row in capture["records"]:
        name = row["name"]
        if name in records:
            raise ValueError(f"Duplicate captured declaration: {name}")
        metadata = {key: row[key] for key in (
            "module", "levels", "levelNames", "shape", "dependencies", "axioms")}
        records[name] = {
            "module": row["module"], "kind": row["shape"][0],
            "type": sha256(canonical(row["type"])),
            "bodies": sha256(canonical(row["values"])),
            "metadata": sha256(canonical(metadata)),
        }
    return records


INDEX_COMPAT_SHA256 = "8382ec04b84e6b22286a2b3720dbabced70b8582592c8c6c629baac29fb791f8"


def load_index_compat() -> dict:
    """Load the reviewed finite protocol inside the verifier's source frame."""
    encoded = (DATA / "index-universe-compat.json").read_bytes()
    if sha256(encoded) != INDEX_COMPAT_SHA256:
        raise ValueError("Index-universe compatibility data changed")
    rules = json.loads(encoded)
    if sha256((DATA / "semantic-fingerprints.tsv").read_bytes()) != rules[
            "frozenFingerprintTableSHA256"]:
        raise ValueError("Index-universe recovery targets a different frozen table")
    return rules


def recover_index_universes(capture: dict, rules: dict) -> dict:
    """Recover four old level interfaces at seven checked sites, without rewriting terms.

    Legacy captures are unchanged. Indexed captures must contain the entire exact protocol;
    no partial activation or absent-protocol fallback is permitted. The unchanged raw semantic
    comparator still checks every type, body and metadata field after this finite conversion.
    """
    recovered = copy.deepcopy(capture)
    records = {row["name"]: row for row in recovered["records"]}
    if len(records) != len(recovered["records"]):
        raise ValueError("Duplicate captured declaration in index-universe protocol")
    maps = {row["name"]: row for row in rules["declarationMaps"]}
    modes = []
    for name, rule in maps.items():
        row = records.get(name)
        if row is None or row["module"] != rule["module"] or row["shape"][0] != rule["kind"]:
            raise ValueError(f"Missing or changed index-universe owner: {name}")
        if row["levels"] == rule["oldLevels"] and row["levelNames"] == rule["oldLevelNames"]:
            modes.append("legacy")
        elif row["levels"] == rule["newLevels"] and row["levelNames"] == rule["newLevelNames"]:
            modes.append("indexed")
        else:
            raise ValueError(f"Unknown index-universe level interface: {name}")
    if len(set(modes)) != 1:
        raise ValueError("Mixed legacy and indexed universe interfaces")
    indexed = modes[0] == "indexed"
    sites = {(row["caller"], tuple(row["path"])): row for row in rules["referenceSites"]}
    if len(sites) != 7 or len(maps) != 4:
        raise ValueError("Incomplete reviewed index-universe protocol")
    visited = set()

    def level(value: list, substitution: dict) -> list:
        if value[0] == "param":
            return copy.deepcopy(substitution.get(canonical(value[1]), value))
        if value[0] not in ("zero", "succ", "max", "imax"):
            raise ValueError("Unsupported level syntax in index-universe protocol")
        return [value[0]] + [level(child, substitution) for child in value[1:]]

    def expression(value: object, substitution: dict, caller: str, path: tuple) -> object:
        if not isinstance(value, list):
            return value
        if value and value[0] == "sort":
            return ["sort", level(value[1], substitution)]
        if value and value[0] == "const":
            levels = [level(item, substitution) for item in value[2]]
            matching = [rule for rule in maps.values()
                        if rule["name"] == name_from_json(value[1])]
            key = (caller, path)
            if matching:
                site = sites.get(key)
                if site is None or value[1] != site["targetName"]:
                    raise ValueError(f"Unlisted or changed index-universe reference: {caller} {path}")
                if key in visited:
                    raise ValueError("Duplicate index-universe reference site")
                visited.add(key)
                expected_arity = site["newArity"] - (not indexed)
                if len(levels) != expected_arity:
                    raise ValueError(f"Changed index-universe reference arity: {caller} {path}")
                if indexed:
                    position = site["indexPosition"]
                    retained = [item for i, item in enumerate(levels) if i != position]
                    expected = ["zero"] if site["extraRule"] == "zero" else retained[0]
                    if levels[position] != expected or levels[position] != site[
                            "actualExtraAfterCallerSubstitution"]:
                        raise ValueError(f"Changed index-universe index: {caller} {path}")
                    levels = retained
                if levels != site["retainedLevels"]:
                    raise ValueError(f"Changed retained universe roles: {caller} {path}")
            elif key in sites:
                raise ValueError(f"Changed index-universe reference name: {caller} {path}")
            return ["const", value[1], levels]
        return [expression(item, substitution, caller, path + (i,))
                for i, item in enumerate(value)]

    for name, row in records.items():
        substitution = {}
        if name in maps and indexed:
            rule = maps[name]
            substitution = {canonical(item["newParameter"]): item["oldLevel"]
                            for item in rule["parameterSubstitution"]}
            row["levels"] = rule["oldLevels"]
            row["levelNames"] = rule["oldLevelNames"]
        row["type"] = expression(row["type"], substitution, name, ("type",))
        row["values"] = [expression(value, substitution, name, ("values", i))
                         for i, value in enumerate(row["values"])]
    if visited != sites.keys():
        raise ValueError("Missing index-universe reference sites")
    return recovered


def name_from_json(value: list) -> str:
    """Render captured Names only for exact lookup; encoded Names are checked at each site."""
    if value[0] == "anonymous":
        return ""
    if value[0] not in ("str", "num"):
        raise ValueError("Unsupported captured Name")
    prefix = name_from_json(value[1])
    return (prefix + "." if prefix else "") + str(value[2])


def compare_semantics(expected: dict, actual: dict) -> list[str]:
    """Compare semantic records alone, also used by independent-environment mutation controls."""
    differences = []
    for name in sorted(expected.keys() | actual.keys()):
        if name not in expected:
            differences.append(f"new semantic dependency: {name}")
        elif name not in actual:
            differences.append(f"missing semantic dependency: {name}")
        else:
            for key in expected[name]:
                if expected[name][key] != actual[name].get(key):
                    differences.append(f"changed {key}: {name}")
    return differences


def decode_dag(bundle: dict) -> list:
    expanded = []
    for node in bundle["nodes"]:
        tag = node[0]
        if tag == 0:
            if any(type(i) is not int or i < 0 or i >= len(expanded) for i in node[1:]):
                raise ValueError("DAG references must point to earlier nodes")
            value = [expanded[i] for i in node[1:]]
        elif tag in (1, 2, 3):
            if len(node) != 2:
                raise ValueError("Invalid literal DAG node")
            value = node[1]
            if tag == 1 and not isinstance(value, str):
                raise ValueError("Invalid string DAG literal")
            if tag == 2 and (type(value) is not int or value < 0):
                raise ValueError("Invalid natural DAG literal")
            if tag == 3 and type(value) is not bool:
                raise ValueError("Invalid Boolean DAG literal")
        elif tag == 4 and len(node) == 1:
            value = None
        else:
            raise ValueError("Unknown DAG node")
        expanded.append(value)
    return expanded


def load_table(path: Path) -> dict[str, dict]:
    records = {}
    for line in path.read_text().splitlines():
        name, module, kind, type_hash, body_hash, metadata_hash = line.split("\t")
        if name in records:
            raise ValueError(f"Duplicate baseline declaration: {name}")
        records[name] = dict(module=module, kind=kind, type=type_hash,
                             bodies=body_hash, metadata=metadata_hash)
    return records


def check_completeness(spec: dict, bundle: dict, expected: dict) -> None:
    original = json.loads((DATA.parent / "strength-manifest.json").read_text())
    names = [entry["name"] for group in original["groups"] for entry in group["declarations"]]
    contracts = bundle["contracts"]
    sources = [entry["source"] for entry in contracts]
    witnesses = [entry["witness"] for entry in contracts]
    if len(names) != 77 or len(set(names)) != 77 or len(sources) != 77:
        raise ValueError("The strength inventory must contain exactly 77 distinct contracts")
    if len(set(sources)) != 77 or set(sources) != set(names) or len(set(witnesses)) != 77:
        raise ValueError("Literal contract completeness differs from the strength inventory")
    if spec["strengthNames"] != names or len(spec["semanticGroups"]) != 11:
        raise ValueError("The 77 strength entries or 11 semantic groups changed")
    expanded = decode_dag(bundle)
    for entry in contracts:
        if entry["kind"] not in ("theorem", "definition"):
            raise ValueError("Unsupported literal witness kind")
        node = expanded[entry["typeRoot"]]
        if sha256(canonical(node)) != expected[entry["source"]]["type"]:
            raise ValueError(f"Literal type differs from the baseline: {entry['source']}")
    pattern = re.compile(
        r'slhdsa_r0_witness\s+"([^"\n]+)"\s+for\s+"([^"\n]+)"\s+as\s+(\w+)')
    found = []
    for module in spec["witnessModules"]:
        text = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        for path, source, name in pattern.findall(text):
            if path != "docs/design/slh-dsa-reuse-evidence/r0/kernel-types.json":
                raise ValueError("A witness reads a different literal artifact")
            found.append((source, "SLHDSA.Refactor.R0." + name))
    wanted = [(entry["source"], entry["witness"]) for entry in contracts]
    if len(found) != 77 or sorted(found) != sorted(wanted):
        raise ValueError("A family module omitted, duplicated or redirected a contract witness")


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()


def frame() -> dict:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = {}
    for package in manifest["packages"]:
        path = ROOT / ".lake/packages" / package["name"]
        dependencies[package["name"]] = {
            "head": git("rev-parse", "HEAD", cwd=path),
            "status": git("status", "--porcelain=v1", "--untracked-files=all", cwd=path),
        }
    index = subprocess.check_output(["git", "ls-files", "--stage", "-z"], cwd=ROOT)
    tracked = {}
    for entry in index.decode().split("\0"):
        if entry:
            metadata, relative = entry.split("\t", 1)
            mode, blob, stage = metadata.split()
            if stage != "0":
                raise ValueError("An unresolved index entry prevents a stable source frame")
            tracked[relative] = (mode, blob)
    others = subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard", "-z"], cwd=ROOT
    ).decode().split("\0")
    source_hash = hashlib.sha256()
    for relative in sorted(set(tracked) | set(filter(None, others))):
        path = ROOT / relative
        row = {"path": relative, "index": tracked.get(relative)}
        if not path.exists() and not path.is_symlink():
            row["working"] = "missing"
        else:
            mode = path.lstat().st_mode
            row["mode"] = stat.S_IMODE(mode)
            if path.is_symlink():
                row["symlink"] = os.readlink(path)
            elif stat.S_ISREG(mode):
                row["sha256"] = sha256(path.read_bytes())
            elif tracked.get(relative, (None,))[0] == "160000":
                if (path / ".git").exists():
                    if Path(git("rev-parse", "--show-toplevel", cwd=path)).resolve() != path.resolve():
                        raise ValueError(f"Gitlink checkout has unexpected repository ownership: {relative}")
                    row["gitlinkHead"] = git("rev-parse", "HEAD", cwd=path)
                    row["gitlinkStatus"] = git("status", "--porcelain=v1", "--untracked-files=all", cwd=path)
                elif any(path.iterdir()):
                    raise ValueError(f"Uninitialized gitlink contains untracked data: {relative}")
                else:
                    row["working"] = "uninitialized-gitlink"
            elif path.is_dir():
                row["working"] = "directory"
            else:
                raise ValueError(f"Unsupported source file kind: {relative}")
        source_hash.update(canonical(row) + b"\n")
    return {
        "head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
        "sourceFingerprint": source_hash.hexdigest(), "indexSha256": sha256(index),
        "status": git("status", "--porcelain=v1", "--untracked-files=all"),
        "manifestSha256": sha256((ROOT / "lake-manifest.json").read_bytes()),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(), "dependencies": dependencies,
    }


def check_pins(current: dict, expected: dict) -> None:
    for key in ("manifestSha256", "toolchain"):
        if current[key] != expected[key]:
            raise ValueError(f"Recorded {key} changed")
    for name, pin in expected["dependencyRevisions"].items():
        actual = current["dependencies"][name]
        if actual["head"] != pin or actual["status"]:
            raise ValueError(f"Dependency {name} is dirty or differs from its recorded revision")


def boundary_packages(boundary: list[dict], local_roots: list[str]) -> list[dict]:
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    resolved = []
    for entry in boundary:
        module = entry["module"]
        if not module:
            raise ValueError(f"External declaration has no module owner: {entry['name']}")
        if module.split(".")[0] in local_roots:
            raise ValueError(f"Repository-owned module escaped semantic capture: {module}")
        if module.split(".")[0] in ("Init", "Lean", "Std", "Lake"):
            package = "lean-toolchain"
        else:
            relative = Path(module.replace(".", "/") + ".lean")
            owners = [p["name"] for p in packages
                      if (ROOT / ".lake/packages" / p["name"] / relative).is_file()]
            if len(owners) != 1:
                raise ValueError(f"External module {module} has no unique pinned package owner")
            package = owners[0]
        resolved.append({**entry, "package": package})
    return resolved


def run(argv: list[str], log: Path) -> None:
    environment = {key: value for key, value in os.environ.items()
                   if key not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    with log.open("wb") as output:
        result = subprocess.run(argv, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                                env={**environment, "LEAN_NUM_THREADS": "4"})
    if result.returncode:
        raise RuntimeError(f"Command exited {result.returncode}; see {log}")


def verify(report: Path) -> dict:
    before = frame()
    (report / "before.json").write_text(json.dumps(before, indent=2) + "\n")
    baseline = json.loads((DATA / "baseline.json").read_text())
    for name, expected_hash in baseline["artifactSha256"].items():
        if sha256((DATA / name).read_bytes()) != expected_hash:
            raise ValueError(f"Frozen artifact changed: {name}")
    index_compat = load_index_compat()
    spec = json.loads((DATA / "capture-input.json").read_text())
    bundle = json.loads((DATA / "kernel-types.json").read_text())
    expected = load_table(DATA / "semantic-fingerprints.tsv")
    check_completeness(spec, bundle, expected)
    check_pins(before, baseline)
    run(["lake", "env", "lean", "--version"], report / "lean-version.log")
    if (report / "lean-version.log").read_text().strip() != baseline["leanVersionOutput"]:
        raise ValueError("The actual commit-bearing Lean evaluator changed")
    run(["lake", "build", CAPTURE_MODULE, STRENGTH_MODULE], report / "build.log")
    # IO.FS.readFile inside the witness command is not a Lake file dependency.
    for index, module in enumerate(spec["witnessModules"]):
        source = module.replace(".", "/") + ".lean"
        run(["lake", "env", "lean", "-DautoImplicit=false", source], report / f"witness-{index}.log")
    driver = report / "CaptureDriver.lean"
    driver.write_text(
        "\n".join("import " + module for module in spec["imports"])
        + f"\nimport {CAPTURE_MODULE}\nimport {STRENGTH_MODULE}\n\n"
        + "slhdsa_r0_validate_witnesses " + json.dumps(str(DATA / "kernel-types.json")) + "\n"
        + "slhdsa_r0_capture " + json.dumps(str(DATA / "capture-input.json"))
        + " to " + json.dumps(str(report / "observed.json")) + "\n")
    run(["lake", "env", "lean", "-DautoImplicit=false", str(driver)], report / "capture.log")
    if "Validated 77 literal kernel contract witnesses" not in (report / "capture.log").read_text():
        raise ValueError("The complete kernel witness check did not execute")
    actual = json.loads((report / "observed.json").read_text())
    if actual["selected"] != spec["names"] or actual["localModuleRoots"] != spec["localModuleRoots"]:
        raise ValueError("Capture roots or local module ownership policy changed")
    if actual["leanVersion"] != baseline["leanVersion"]:
        raise ValueError("Actual Lean version changed")
    recovered = recover_index_universes(actual, index_compat)
    differences = compare_semantics(expected, semantic_records(recovered))
    if differences:
        raise ValueError("Semantic baseline changed:\n" + "\n".join(differences[:30]))
    resolved_boundary = boundary_packages(actual["externalBoundary"], spec["localModuleRoots"])
    if resolved_boundary != baseline["externalBoundary"]:
        raise ValueError("The pinned external semantic boundary changed")
    after = frame()
    (report / "after.json").write_text(json.dumps(after, indent=2) + "\n")
    if after != before:
        raise ValueError("Source or dependency state changed during verification")
    return {"accepted": True, "scope": "R0a frozen baseline, not R0b or P5 recovery",
            "contracts": 77, "semanticGroups": 11, "semanticRecords": len(expected)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path)
    args = parser.parse_args()
    report = args.report_dir or Path(tempfile.mkdtemp(prefix="vcvio-slh-dsa-r0-"))
    report = report.resolve()
    if report.is_relative_to(ROOT):
        parser.error("Use a report directory outside the source tree")
    report.mkdir(parents=True, exist_ok=True)
    if any(report.iterdir()):
        parser.error("The report directory must be empty")
    try:
        result = verify(report)
        status = 0
    except (ValueError, RuntimeError, OSError, KeyError) as error:
        result = {"accepted": False, "error": str(error)}
        status = 1
    (report / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({**result, "reportDir": str(report)}))
    return status


if __name__ == "__main__":
    raise SystemExit(main())
