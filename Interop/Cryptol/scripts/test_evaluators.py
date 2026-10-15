#!/usr/bin/env python3
"""Reproduce the versioned evaluator audit when upgrading the Cryptol boundary.

The upstream binary is SHA-pinned independently of the production import pin.
Known disagreements are checked outcomes, not semantic agreements. An external
timeout fails the check and is never classified as semantic divergence.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from extract_foundation import CRYPTOL, FOUNDATION
from export_references import verify_checkout
from test_model import check_reference_demand

UPSTREAM = "51405420cb90cf9959ca4349eea0ae8b77487855"
INTEGER_ISSUE = "https://github.com/GaloisInc/cryptol/issues/2060"


def observe(binary, expression, expected, mode, foundation, source=None):
    env = dict(os.environ)
    env["PATH"] = str(binary.parent) + os.pathsep + env.get("PATH", "")
    command = [str(binary), "--ignore-cryptolrc", "--color=none", "-e"]
    if source:
        command += ["-c", f":load {source}"]
    command += ["-c", ":set base=10", "-c",
                (":eval " if mode == "reference" else "") + expression]
    result = subprocess.run(command, cwd=foundation, env=env, capture_output=True,
                            text=True, timeout=30)
    output = result.stdout + result.stderr
    error = expected in ("division by 0", "invalid sequence index: -1")
    expected_exit = 1 if error and mode == "normal" else 0
    assert result.returncode == expected_exit, (expression, mode, output)
    assert re.search("^" + re.escape(expected) + "$", output, re.MULTILINE), \
        (expression, mode, output)
    assert not re.search(r"parse error|type error|\[error\]", output, re.IGNORECASE), output
    return {"expression": expression, "mode": mode, "result": expected}


def audit(binary, revision, foundation, temporary):
    version = subprocess.check_output([str(binary), "--version"], text=True)
    assert f"Git commit {revision}" in version, version
    observations = check_reference_demand(str(binary))
    for expression, expected in (
        ('((xs : [inf]Integer) @ 12 where xs = [0] # [x + 1 | x <- xs])', "12"),
        ('(([] : [0]) >>> (3 : Integer)) == []', "True"),
    ):
        for mode in ("reference", "normal"):
            observations.append(observe(binary, expression, expected, mode, foundation))
    for x, y in ((7, 3), (-7, 3), (7, -3), (-7, -3), (-1, 5)):
        quotient = (abs(x) // abs(y)) * (-1 if (x < 0) != (y < 0) else 1)
        for op in ("/", "%"):
            reference = quotient if op == "/" else x - quotient * y
            normal = x // y if op == "/" else x % y
            expression = f"({x} : Integer) {op} ({y} : Integer)"
            for mode, expected in (("reference", reference), ("normal", normal)):
                row = observe(binary, expression, str(expected), mode, foundation)
                row["upstream_issue"] = INTEGER_ISSUE
                observations.append(row)
    for op in ("/", "%"):
        for mode in ("reference", "normal"):
            observations.append(observe(binary, f"(1 : Integer) {op} 0",
                                        "division by 0", mode, foundation))

    original = (foundation / "algorithms/Keccak/StepMappings.cry").read_text()
    assert original.count("((x-1) % 5)") == 1
    portable = temporary / "ThetaPortable.cry"
    portable.write_text(original.replace("module algorithms::Keccak::StepMappings where",
                                         "module ThetaPortable where")
                        .replace("((x-1) % 5)", "((x+4) % 5)"))
    source = temporary / "EvaluatorAudit.cry"
    source.write_text("module EvaluatorAudit where\n"
                      "import algorithms::Keccak::StepMappings as Theta\n"
                      "import ThetaPortable as Portable\n")
    for mode in ("reference", "normal"):
        observations.append(observe(binary, "~((Theta::θ`{1} zero) @ 0 @ 0 @ 0)",
            "invalid sequence index: -1" if mode == "reference" else "True",
            mode, foundation, source))
        for width in (1, 8, 64):
            expression = f"(Portable::θ`{{{width}}} zero) == zero"
            observations.append(observe(binary, expression, "True", mode, foundation, source))
    return {"revision": revision, "version": version.splitlines()[0],
            "observations": observations}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", required=True, type=Path)
    parser.add_argument("--upstream-cryptol", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    args = parser.parse_args()
    foundation = args.foundation.resolve()
    verify_checkout(foundation, FOUNDATION)
    with tempfile.TemporaryDirectory(prefix="cryptol-evaluator-audit-") as directory:
        temporary = Path(directory)
        reports = [audit(binary.resolve(), revision, foundation, temporary)
                   for binary, revision in ((args.cryptol, CRYPTOL),
                                            (args.upstream_cryptol, UPSTREAM))]
    report = {"foundation_revision": FOUNDATION, "integer_disagreement": INTEGER_ISSUE,
              "portable_theta": "separate test variant using (x+4)%5; original source unchanged",
              "meaning": "Versioned executable observations, not Haskell correctness proofs",
              "evaluators": reports}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Evaluator audit passed: {sum(len(r['observations']) for r in reports)} observations")


if __name__ == "__main__":
    main()
