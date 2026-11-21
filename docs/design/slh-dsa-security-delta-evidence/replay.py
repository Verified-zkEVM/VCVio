#!/usr/bin/env python3
"""Replay three bounded Lean probes against an immutable, already built checkout."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

os.environ["GIT_OPTIONAL_LOCKS"] = "0"

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--artifacts", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--recorded-head", help="Require this clean source commit after review")
args = parser.parse_args()
sources = Path(__file__).resolve().parent
artifacts = args.artifacts.resolve()
output = args.output.resolve()
checkout = sources.parents[2]


def git(directory, *arguments):
    return subprocess.check_output(["git", *arguments], cwd=directory, text=True).strip()


def frame():
    assert git(artifacts, "status", "--porcelain") == ""
    manifest = artifacts / "lake-manifest.json"
    packages = {}
    for package in json.loads(manifest.read_text())["packages"]:
        directory = artifacts / ".lake/packages" / package["name"]
        assert git(directory, "status", "--porcelain") == ""
        packages[package["name"]] = git(directory, "rev-parse", "HEAD")
        assert packages[package["name"]] == package["rev"]
    assert len(packages) == 12
    return {
        "sourceHead": git(checkout, "rev-parse", "HEAD"),
        "sourceStatus": git(checkout, "status", "--porcelain", "--untracked-files=all"),
        "sourceHashes": {
            str(path.relative_to(checkout)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [*sorted(sources.glob("*.lean")), sources / "replay.py",
                         sources / "compare_bounds.py", sources.parent / "slh-dsa-security-delta.md"]
        },
        "artifactHead": git(artifacts, "rev-parse", "HEAD"),
        "artifactManifestSHA256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
        "lockedDependencies": packages,
    }


assert not output.exists(), "Use a fresh output directory"
before = frame()
assert before["artifactHead"] == "b63fede77cfcf9e23fda94c28e951e4520fdeb91"
if args.recorded_head:
    assert before["sourceHead"] == args.recorded_head and before["sourceStatus"] == ""
libraries = [artifacts / ".lake/build/lib/lean"] + sorted(
    (artifacts / ".lake/packages").glob("*/.lake/build/lib/lean")
)
assert all(path.is_dir() for path in libraries)
environment = os.environ.copy()
environment["LEAN_PATH"] = ":".join(str(path) for path in [output, *libraries])
environment["LEAN_NUM_THREADS"] = "4"
output.mkdir(parents=True)
version = subprocess.check_output(["lean", "--version"], cwd=artifacts, text=True)
assert "version 4.35.0," in version
records = []
for name in ["StructuralRecovery", "EligibleComparison", "OperationalRecovery"]:
    source = sources / f"{name}.lean"
    destination = output / f"{name}.olean"
    argv = [
        "lean", "-j4", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
        "-Dweak.linter.mathlibStandardSet=true", "-Dweak.linter.redundantVisibility=true",
        f"--root={sources}", "-o", str(destination), str(source),
    ]
    started = time.monotonic()
    with (output / f"{name}.log").open("w") as log:
        result = subprocess.run(
            argv, cwd=artifacts, env=environment, stdout=log, stderr=subprocess.STDOUT,
            timeout=240, check=False,
        )
    records.append({
        "module": name, "argv": argv, "exit": result.returncode,
        "seconds": time.monotonic() - started,
        "sourceSHA256": hashlib.sha256(source.read_bytes()).hexdigest(),
    })
    (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
    assert result.returncode == 0, name
    text = (output / f"{name}.log").read_text()
    assert not any(marker in text for marker in ["error:", "warning:", "sorryAx"]), name
    claims = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    assert len(claims) == {"StructuralRecovery": 4, "EligibleComparison": 4,
                           "OperationalRecovery": 2}[name]
    for claim in claims:
        assert set(claim.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}
    records[-1]["oleanSHA256"] = hashlib.sha256(destination.read_bytes()).hexdigest()
    records[-1]["logSHA256"] = hashlib.sha256((output / f"{name}.log").read_bytes()).hexdigest()
    (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
after = frame()
assert before == after
(output / "context.json").write_text(json.dumps({"before": before, "after": after}, indent=2) + "\n")
print(json.dumps({"status": "PASS", "compiler": version.strip(), "modules": records}, indent=2))
