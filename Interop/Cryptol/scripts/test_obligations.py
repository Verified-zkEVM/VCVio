#!/usr/bin/env python3
"""Policy mutations complement the scanner's compiled kernel fixtures."""

from copy import deepcopy
import hashlib
import json
import os
import subprocess
import tempfile

from pathlib import Path
from audit_obligations import audit, audit_warnings

ROOT = "Cryptol.Tests.Obligations.sourceLaw"
CLIENT = "Cryptol.Tests.Obligations.clientLaw"
TYPE = "True"
LEDGER = {"version": 1, "obligations": [{"declaration": ROOT, "proposition": TYPE,
    "type_sha256": hashlib.sha256(TYPE.encode()).hexdigest(), "source": "test fixture",
    "owner": "test", "reason": "synthetic admission for policy testing"}]}
REPORT = {"declarations": [{"name": n, "axioms": ["sorryAx"]} for n in [ROOT, CLIENT]],
    "sorryGraph": [{"name": ROOT, "kind": "theorem", "type": TYPE, "direct": True,
                    "dependencies": []},
                   {"name": CLIENT, "kind": "theorem", "type": TYPE, "direct": False,
                    "dependencies": [ROOT]}]}


def compiled_policy():
    """Exercise the local policy on real temporary oleans and compiler warnings."""
    repo = Path(__file__).resolve().parents[3]
    lake = ["lake"]
    if os.environ.get("POLYFUN_PATH"):
        lake += ["-R", "-K", "polyfunPath=" + os.environ["POLYFUN_PATH"]]

    def run(command, *, stdout_only=False, **kwargs):
        result = subprocess.run(command, cwd=repo, capture_output=True, text=True,
                                timeout=120, **kwargs)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)
        # A local dependency override makes Lake warn on stderr.
        return result.stdout if stdout_only else result.stdout + result.stderr

    run([*lake, "build", "polyfun-axiomsweep"])
    config = json.loads(run([*lake, "env", "python3", "-c",
        "import json,os,shutil; print(json.dumps({'path':os.environ['LEAN_PATH'],"
        "'lean':shutil.which('lean'),'sweep':shutil.which('polyfun-axiomsweep')}))"],
        stdout_only=True))
    assert config["lean"] and config["sweep"]
    with tempfile.TemporaryDirectory(prefix="cryptol-obligation-fixture-") as temporary:
        root = Path(temporary)
        environment = dict(os.environ, LEAN_PATH=str(root) + os.pathsep + config["path"])
        module = "Interop.Cryptol.Tests.ObligationFixture"
        namespace = "Cryptol.Tests.ObligationFixture"
        source = root / (module.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True)
        source.write_text("module\npublic import Init\npublic section\nnamespace " + namespace +
            "\ntheorem sourceLaw : True := by sorry\n"
            "theorem clientLaw : True := sourceLaw\n"
            "def implementation (n : Nat) : Nat := n + 1\nend " + namespace + "\n")
        warnings = run([config["lean"], "--root=" + str(root), str(source),
                        "-o", str(source.with_suffix(".olean")),
                        "-i", str(source.with_suffix(".ilean"))], env=environment)
        path = root / "report.json"
        run([config["sweep"], "--root", module, "--out", str(path)], env=environment)
        report = json.loads(path.read_text())
        direct = [e for e in report["sorryGraph"] if e["direct"]]
        assert len(direct) == 1 and direct[0]["name"] == namespace + ".sourceLaw"
        proposition = direct[0]["type"]
        ledger = {"version": 1, "obligations": [{"declaration": direct[0]["name"],
            "proposition": proposition, "type_sha256": hashlib.sha256(proposition.encode()).hexdigest(),
            "source": "temporary compiled fixture", "owner": "test", "reason": "policy regression"}]}
        results = {d["declaration"]: d for d in audit(report, ledger)["declarations"]}
        assert results[namespace + ".clientLaw"]["obligations"] == [namespace + ".sourceLaw"]
        assert results[namespace + ".implementation"]["obligations"] == []
        assert "declaration uses `sorry`" in warnings
        audit_warnings(warnings, report, ledger, root)
        # Same compiled report must fail without the explicit local admission.
        try:
            audit(report, {"version": 1, "obligations": []})
        except ValueError:
            pass
        else:
            raise AssertionError("compiled admission accepted without a ledger entry")
        source.write_text(source.read_text().replace("n + 1", "by sorry"))
        run([config["lean"], "--root=" + str(root), str(source),
             "-o", str(source.with_suffix(".olean")),
             "-i", str(source.with_suffix(".ilean"))], env=environment)
        run([config["sweep"], "--root", module, "--out", str(path)], env=environment)
        admitted = json.loads(path.read_text())
        definition = next(e for e in admitted["sorryGraph"]
                          if e["name"] == namespace + ".implementation")
        assert definition["direct"]
        illegal = deepcopy(ledger)
        illegal["obligations"].append(dict(ledger["obligations"][0],
            declaration=definition["name"], proposition=definition["type"],
            type_sha256=hashlib.sha256(definition["type"].encode()).hexdigest()))
        try:
            audit(admitted, illegal)
        except ValueError as error:
            assert "only named Cryptol proof admissions" in str(error)
        else:
            raise AssertionError("compiled admitted implementation accepted")
    print("Obligation policy: compiled admissions, client propagation, implementation rejection and warnings")


def main():
    result = audit(REPORT, LEDGER)
    assert all(d["obligations"] == [ROOT] for d in result["declarations"])
    mutations = [
        lambda r, l: l.update(obligations=[]),
        lambda r, l: r["sorryGraph"][0].update(kind="def"),
        lambda r, l: r["sorryGraph"][0].update(type="False"),
        lambda r, l: r["declarations"][1]["axioms"].append("nativeTrust"),
        lambda r, l: r["sorryGraph"][1].update(dependencies=["missing"]),
        lambda r, l: r["sorryGraph"][1].update(dependencies=[]),
        lambda r, l: l["obligations"][0].update(owner=""),
        lambda r, l: r.update(sorryGraph=[]),
    ]
    for mutate in mutations:
        report, ledger = deepcopy(REPORT), deepcopy(LEDGER)
        mutate(report, ledger)
        try:
            audit(report, ledger)
        except ValueError:
            continue
        raise AssertionError("invalid obligation policy accepted")
    assert audit({"declarations": [], "sorryGraph": []},
                 {"version": 1, "obligations": []})["declarations"] == []
    report = deepcopy(REPORT)
    report["declarations"][0].update(module="Interop.Cryptol.Tests.Obligations", line=12)
    warning = "warning: Interop/Cryptol/Tests/Obligations.lean:12:0: declaration uses `sorry`"
    audit_warnings(warning, report, LEDGER, Path.cwd())
    for bad in (warning.replace(":12:", ":13:"), warning.replace("uses `sorry`", "has a linter error"),
                warning.replace("Obligations.lean", "Other.lean"), "warning: unrelated build warning"):
        try:
            audit_warnings(bad, report, LEDGER, Path.cwd())
        except ValueError:
            continue
        raise AssertionError("unaccounted warning accepted")
    print(f"Obligation policy: conditional propagation and {len(mutations)} rejection mutations")
    compiled_policy()


if __name__ == "__main__":
    main()
