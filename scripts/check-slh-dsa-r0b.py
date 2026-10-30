#!/usr/bin/env python3
"""Freshly check current SLH-DSA strength, operational and readable contracts.

Normal `lake test` calls this after its registered executables and exact table check. This
command checks their bindings; it never reruns those runtimes or recursively invokes `lake test`.
The unchanged check-slh-dsa-r0.py remains the separately callable historical construction-syntax
audit. Changed protected construction identity is a historical nonPASS, not a refreshed baseline.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "docs/design/slh-dsa-reuse-evidence/r0b"
MODULE = "HashSigTest.SLHDSA.Refactor.SemanticContracts"
LEAVES = ["HashSigTest.SLHDSA.Refactor.Semantics." + name
          for name in ("Legacy", "Bounds", "Game", "Construction")]
RUNTIMES = {"slhdsa_shake128s_compiler_tests", "slhdsa_shake128s_game_tests",
            "slhdsa_shake128s_wire_bridge_tests", "slhdsa_fors_secret_order_tests"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# This archived digest describes a whole implementation, rather than a runtime/parser binding.
# Its historical value stays in bindings.json; current construction claims are checked below.
HISTORICAL_SCHEME_SOURCE = "HashSig/SLHDSA/SHAKE128s/Statement/Scheme.lean"
WOTS_RUNTIME = "slhdsa_wots_integration_tests"
WOTS_TARGET = {"root": "SLHDSAWotsIntegrationTests", "srcDir": "scripts"}
WOTS_JOINT_MODULE = "HashSigTest.SLHDSA.Refactor.WotsIntegration"
WOTS_JOINT_NAMES = ["SLHDSA.Refactor.WotsIntegration." + name
                    for name in ("observePublicKey", "observeSign", "observeRecovery")]

spec = importlib.util.spec_from_file_location("slh_dsa_r0a", ROOT / "scripts/check-slh-dsa-r0.py")
if spec is None or spec.loader is None:
    raise RuntimeError("The original R0a verifier is unavailable")
r0a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r0a)


def execute(argv: list[str], log: Path, steps: list[dict]) -> None:
    environment = {key: value for key, value in os.environ.items()
                   if key not in ("LEAN_PATH", "LEAN_SRC_PATH")}
    started = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run(argv, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT,
                                env={**environment, "LEAN_NUM_THREADS": "4"})
    steps.append({"argv": argv, "exitCode": result.returncode,
                  "seconds": round(time.monotonic() - started, 3),
                  "log": str(log), "sha256": r0a.sha256(log.read_bytes())})
    if result.returncode:
        raise RuntimeError(f"Command exited {result.returncode}; see {log}")


def test_driver(source: str) -> str:
    """Select the ordinary driver's complete control-flow scaffold."""
    marker = "script test (args) do"
    if source.count(marker) != 1:
        raise ValueError("The ordinary test-driver declaration is ambiguous")
    return source.split(marker, 1)[1].split("/-- ML-KEM test executable", 1)[0]


def driver_scaffold(driver: str) -> str:
    """Allow additive standalone unprotected exe entries; retain every other source byte."""
    result = []
    pattern = re.compile(r'\s*#\["exe", "([A-Za-z0-9_]+)"\],?\s*')
    for line in driver.splitlines(keepends=True):
        match = pattern.fullmatch(line)
        if match and match[1] not in RUNTIMES:
            continue
        result.append(line)
    return "".join(result)


def target_binding(source: str, name: str) -> dict:
    """Fail closed on nonliteral or extra configuration of a protected executable."""
    prefix = r"^lean_exe " + re.escape(name) + r"\b"
    if len(re.findall(prefix, source, re.MULTILINE)) != 1:
        raise ValueError(f"Protected target declaration is ambiguous: {name}")
    match = re.search(prefix + r" where\n((?:[ \t].*\n|\n)*)", source, re.MULTILINE)
    if match is None:
        raise ValueError(f"Protected target configuration is unsupported: {name}")
    values = {"srcDir": "."}
    seen = set()
    for line in match[1].splitlines():
        line = line.split("--", 1)[0].strip()
        if not line:
            continue
        root = re.fullmatch(r"root\s*:=\s*`([A-Za-z0-9_.]+)", line)
        directory = re.fullmatch(r'srcDir\s*:=\s*("[^"\\]*")', line)
        if root:
            field, value = "root", root[1]
        elif directory:
            field, value = "srcDir", json.loads(directory[1])
        else:
            raise ValueError(f"Protected target has unsupported configuration: {name}: {line}")
        if field in seen:
            raise ValueError(f"Protected target field is duplicated: {name}.{field}")
        seen.add(field)
        values[field] = value
    if "root" not in values:
        raise ValueError(f"Protected target has no literal module root: {name}")
    return values


def check_bindings(bindings: dict) -> list[str]:
    for field in ("r0aProtectedFiles", "semanticSourceSha256", "runtimeSourceSha256"):
        for relative, digest in bindings[field].items():
            if field == "runtimeSourceSha256" and relative == HISTORICAL_SCHEME_SOURCE:
                continue
            if r0a.sha256((ROOT / relative).read_bytes()) != digest:
                raise ValueError(f"Frozen {field} binding changed: {relative}")
    original = json.loads((ROOT / "docs/design/slh-dsa-reuse-evidence/r0/capture-input.json").read_text())
    groups = bindings["semanticGroups"]
    if groups.keys() != original["semanticGroups"].keys():
        raise ValueError("The readable contracts must cover exactly the original eleven groups")
    declared = []
    for module in LEAVES:
        source = ROOT / (module.replace(".", "/") + ".lean")
        declared.extend(re.findall(r"^theorem (\w+)", source.read_text(), re.MULTILINE))
    selected = [name for names in groups.values() for name in names]
    if len(set(declared)) != len(declared) or set(selected) != set(declared):
        raise ValueError("Readable contract coverage omitted or redirected a public equation")
    if set(bindings["registeredRuntimes"]) != RUNTIMES:
        raise ValueError("The four original runtime bindings changed")
    lakefile = (ROOT / "lakefile.lean").read_text()
    driver = test_driver(lakefile)
    targets = bindings["targetBindings"]
    if set(targets) != RUNTIMES | {"slhdsa_bound_table"}:
        raise ValueError("The protected executable/table target inventory changed")
    for name, expected in targets.items():
        if target_binding(lakefile, name) != expected:
            raise ValueError(f"Protected target root/srcDir changed: {name}")
    if r0a.sha256(driver_scaffold(driver).encode()) != bindings["driverScaffoldSha256"]:
        raise ValueError("The protected test-driver control-flow scaffold changed")
    for name in sorted(RUNTIMES):
        pattern = r'#\[\s*"exe"\s*,\s*"' + re.escape(name) + r'"\s*\]'
        if len(re.findall(pattern, driver)) != 1:
            raise ValueError(f"Ordinary lake test must register {name} exactly once")
    if target_binding(lakefile, WOTS_RUNTIME) != WOTS_TARGET:
        raise ValueError("The WOTS integration runtime root/srcDir changed")
    wots_registration = r'#\[\s*"exe"\s*,\s*"' + WOTS_RUNTIME + r'"\s*\]'
    if len(re.findall(wots_registration, driver)) != 1:
        raise ValueError("Ordinary lake test must register the WOTS integration runtime exactly once")
    if len(re.findall(r'"scripts/check-slh-dsa-r0b\.py"', driver)) != 1:
        raise ValueError("Ordinary lake test must register its R0b tail gate exactly once")
    csv = ROOT / "docs/design/slh-dsa-security-bounds.csv"
    if r0a.sha256(csv.read_bytes()) != bindings["csvSha256"]:
        raise ValueError("The original exact eighteen-row CSV changed")
    return ["SLHDSA.Refactor.Semantics." + name for name in sorted(declared)]


def check_axioms(names: list[str], report: Path, steps: list[dict]) -> None:
    probe = report / "Axioms.lean"
    imports = [MODULE, r0a.STRENGTH_MODULE, WOTS_JOINT_MODULE]
    probe.write_text("".join("import " + module + "\n" for module in imports) +
                     "".join("#print axioms " + name + "\n" for name in names))
    log = report / "axioms.log"
    execute(["lake", "env", "lean", "-DautoImplicit=false", str(probe)], log, steps)
    actual = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for match in re.finditer(pattern, log.read_text(), re.MULTILINE):
        actual[match[1]] = set(filter(None, (name.strip() for name in (match[2] or "").split(","))))
    if set(actual) != set(names):
        raise ValueError("The standard-axiom audit did not cover every current source, witness and joint claim")
    for name, axioms in actual.items():
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(f"Nonstandard axioms in {name}: {sorted(axioms - ALLOWED_AXIOMS)}")


def verify(report: Path, steps: list[dict]) -> dict:
    before = r0a.frame()
    (report / "before.json").write_text(json.dumps(before, indent=2) + "\n")
    bindings = json.loads((DATA / "bindings.json").read_text())
    names = check_bindings(bindings)
    historical = ROOT / "docs/design/slh-dsa-reuse-evidence/r0"
    baseline = json.loads((historical / "baseline.json").read_text())
    contracts = json.loads((historical / "kernel-types.json").read_text())["contracts"]
    contract_spec = json.loads((historical / "capture-input.json").read_text())
    if len(contracts) != baseline["strengthContracts"]:
        raise ValueError("The current strength-contract inventory is incomplete")
    source_names = [entry["source"] for entry in contracts]
    witness_names = [entry["witness"] for entry in contracts]
    if len(set(source_names)) != len(contracts) or len(set(witness_names)) != len(contracts):
        raise ValueError("A current strength source or witness occurs more than once")
    r0a.check_pins(before, baseline)
    version_log = report / "lean-version.log"
    execute(["lake", "env", "lean", "--version"], version_log, steps)
    if version_log.read_text().strip() != baseline["leanVersionOutput"]:
        raise ValueError("The actual commit-bearing Lean evaluator changed")
    execute(["lake", "build", MODULE, r0a.CAPTURE_MODULE, r0a.STRENGTH_MODULE,
             WOTS_JOINT_MODULE], report / "build.log", steps)
    for index, module in enumerate(LEAVES):
        execute(["lake", "env", "lean", "-DautoImplicit=false",
                 module.replace(".", "/") + ".lean"], report / f"semantic-{index}.log", steps)
    # Literal JSON reads are not Lake dependencies: elaborate each family freshly.
    for index, module in enumerate(contract_spec["witnessModules"]):
        execute(["lake", "env", "lean", "-DautoImplicit=false",
                 module.replace(".", "/") + ".lean"], report / f"witness-{index}.log", steps)
    driver = report / "StrengthWitnesses.lean"
    driver.write_text("\n".join("import " + module for module in contract_spec["imports"]) +
                      f"\nimport {r0a.CAPTURE_MODULE}\nimport {r0a.STRENGTH_MODULE}\n\n" +
                      "slhdsa_r0_validate_witnesses " +
                      json.dumps(str(historical / "kernel-types.json")) + "\n")
    witness_log = report / "strength-witnesses.log"
    execute(["lake", "env", "lean", "-DautoImplicit=false", str(driver)], witness_log, steps)
    if f"Validated {len(contracts)} literal kernel contract witnesses" not in witness_log.read_text():
        raise ValueError("The complete current strength-witness validation did not execute")
    axiom_names = list(dict.fromkeys(names + source_names + witness_names + WOTS_JOINT_NAMES))
    check_axioms(axiom_names, report, steps)
    after = r0a.frame()
    (report / "after.json").write_text(json.dumps(after, indent=2) + "\n")
    if after != before:
        raise ValueError("Source or dependencies changed during the readable-contract gate")
    return {"accepted": True, "semanticGroups": 11, "publicEquations": len(names),
            "freshStrengthContracts": len(contracts), "standardAxiomClaims": len(axiom_names),
            "wotsJointClaims": WOTS_JOINT_NAMES,
            "requiredRuntimeBindings": sorted(RUNTIMES | {WOTS_RUNTIME}),
            "runtimeScope": "Bindings only here; preceding ordinary lake-test steps execute once",
            "historicalConstructionAudit": {
                "executed": False, "accepted": None,
                "command": "python3 scripts/check-slh-dsa-r0.py --report-dir FRESH_EXTERNAL_DIR",
                "scope": "Separate historical construction identity; mismatch is nonPASS, never refreshed"},
            "retiredRuntimeSourceIdentity": {
                "path": HISTORICAL_SCHEME_SOURCE,
                "recordedSha256": bindings["runtimeSourceSha256"][HISTORICAL_SCHEME_SOURCE]},
            "scope": "Current quantified strength, readable and WOTS joint operational contracts; "
                     "no historical private-body identity or future-family recovery claim"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path)
    args = parser.parse_args()
    report = (args.report_dir or Path(tempfile.mkdtemp(prefix="vcvio-slh-dsa-r0b-"))).resolve()
    if report.is_relative_to(ROOT):
        parser.error("Use a report directory outside the checkout")
    report.mkdir(parents=True, exist_ok=True)
    if any(report.iterdir()):
        parser.error("The report directory must be empty")
    steps = []
    try:
        result = verify(report, steps)
        status = 0
    except (ValueError, RuntimeError, OSError, KeyError, IndexError) as error:
        result = {"accepted": False, "error": str(error)}
        status = 1
    result["steps"] = steps
    (report / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({**result, "reportDir": str(report)}))
    return status


if __name__ == "__main__":
    raise SystemExit(main())
