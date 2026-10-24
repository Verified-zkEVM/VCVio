#!/usr/bin/env python3
"""Foundation bundle provenance, scalar and specialization imports, and malformed-source rejection.

PolyFun's own source tests cover the language-level cases and importer canaries.
"""

from copy import deepcopy
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

import polyfun_tools  # noqa: F401

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT.parents[1] / ".lake/build/bin/cryptol-interop"


def run(path, mode="inspect"):
    result = subprocess.run([str(LEAN), "source", mode, str(path)],
                            text=True, capture_output=True)
    return result.returncode, json.loads(result.stdout)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)

    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def specialization_checks(artifacts, manifest):
    assert hashlib.sha256((artifacts / "specialized-scalar-bundle.json").read_bytes()).hexdigest() == \
        manifest["specialization"]["bundle_sha256"]
    code, report = run(artifacts / "specialized-scalar-bundle.json", "elaborate")
    assert code == 0 and all(r["status"] == "typed" for r in report), report
    specialized = json.loads((artifacts / "specialized-scalar-bundle.json").read_bytes())
    mutant = deepcopy(specialized)
    mutant["roots"][0]["expression"]["args"][1].reverse()
    with tempfile.TemporaryDirectory(prefix="cryptol-extended-import-") as temporary:
        path = Path(temporary) / "mutated.json"
        path.write_text(json.dumps(mutant))
        code, report = run(path, "elaborate")
        assert code != 0 and report["status"] == "rejected", report

        # A same-typed semantic mutation must pass typing and fail the kernel certificate.
        mutant = deepcopy(specialized)
        next(n for n in nodes(mutant) if n.get("tag") == "num" and n["args"] == ["7"])["args"] = ["8"]
        path.write_text(json.dumps(mutant))
        code, report = run(path, "elaborate")
        assert code == 0, report
        source = f"""module
public import Interop.Cryptol.Bridge.ImportedSpecialization
import PolyFunCryptol.Translation.SourceElaboration
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Model.Reference.Kinds
import PolyFunCryptol.Model.Reference.Types
import PolyFunCryptol.Model.Reference.Syntax
import PolyFunCryptol.Model.Types
open Cryptol Translation SourceElaboration
cryptol_import Mutated from "{path}" as smallSigma256Zero
set_option maxRecDepth 10000 in
example : check Mutated.bundle Mutated.smallSigma256Zero.root =
    .ok ⟨_, Bridge.ImportedSpecialization.smallSigma256Zero⟩ := by
  with_unfolding_all rfl
"""
        proof = Path(temporary) / "MutatedSpecialization.lean"
        proof.write_text(source)
        lake = ["lake"]
        if os.environ.get("POLYFUN_PATH"):
            lake += ["-R", "-K", "polyfunPath=" + os.environ["POLYFUN_PATH"]]
        result = subprocess.run([*lake, "env", "lean", str(proof)], cwd=ROOT.parents[1],
                                text=True, capture_output=True)
        assert result.returncode != 0 and "Tactic `rfl` failed" in result.stdout, result.stdout
        assert result.stdout.count("error:") == 1, result.stdout
    print("Specialization: typed candidate, dependency-order mutation rejected, "
          "same-typed mutation rejected by the kernel certificate")


def main():
    argparse.ArgumentParser(description=__doc__).parse_args()
    artifacts = ROOT / "artifacts/references"
    source = artifacts / "bundle.json"
    data = source.read_bytes()
    bundle = json.loads(data)
    foreign = [n for n in nodes(bundle) if n.get("tag") == "foreign"]
    assert foreign, "the retained reference corpus should exercise foreign ABI metadata"
    for declaration in foreign:
        interface = json.loads(declaration["args"][0])
        assert interface["convention"] in {"c", "abstract"}
        assert set(interface) == {"convention", "parameters", "arguments", "result"}
        assert "/private/tmp/" not in declaration["args"][0]
    manifest = json.loads((artifacts / "manifest.json").read_text())
    assert hashlib.sha256(data).hexdigest() == manifest["bundle_sha256"]
    assert hashlib.sha256((artifacts / "FoundationReferences.cry").read_bytes()).hexdigest() == \
        manifest["entry_sha256"]
    assert hashlib.sha256(polyfun_tools.EXPORTER_SOURCE.read_bytes()).hexdigest() == \
        manifest["exporter_sha256"]
    code, report = run(source)
    assert code == 0 and report["status"] == "scoped", report
    assert report["declarations"] == manifest["validation"]["declarations"]
    assert report["roots"] == [e["root"] for e in manifest["entries"]]
    mutations = []

    def add(label, change):
        altered = deepcopy(bundle)
        change(altered)
        mutations.append((label, altered))

    add("format", lambda b: b.update(format="unversioned"))
    add("version", lambda b: b.update(version=2))
    add("frontend pin", lambda b: b.update(cryptol_revision="0" * 40))
    add("empty roots", lambda b: b.update(roots=[]))
    add("missing dependency", lambda b: b["groups"].pop(0))
    add("duplicate binding", lambda b: b["groups"].append(deepcopy(b["groups"][0])))
    add("reordered dependencies", lambda b: b["groups"].reverse())
    add("empty recursive group", lambda b: b["groups"].append({"tag": "recursive", "args": [[]]}))
    add("unbound root", lambda b: b["roots"][0].update(expression={"tag": "var", "args": [
        {"id": 99999999, "text": "missing", "origin": "missing"}]}))
    add("unknown constructor", lambda b: next(n for n in nodes(b) if n.get("tag") == "con")
        ["args"].__setitem__(0, "TC NotCryptol"))
    add("numeric underflow literal", lambda b: next(n for n in nodes(b) if n.get("tag") == "num"
        and n.get("args"))["args"].__setitem__(0, "-1"))
    add("primitive redirect", lambda b: b["primitive_fallbacks"][0][1].update(id=99999999))
    add("duplicate redirect", lambda b: b["primitive_fallbacks"].append(b["primitive_fallbacks"][0]))
    add("source traversal", lambda b: b["modules"][0].update(path="../Cryptol.cry"))
    add("source digest", lambda b: b["modules"][0].update(sha256="not-a-digest"))
    with tempfile.TemporaryDirectory(prefix="cryptol-rejections-") as temporary:
        path = Path(temporary) / "mutated.json"
        for label, changed in mutations:
            path.write_text(json.dumps(changed))
            code, report = run(path)
            assert code != 0 and report["status"] == "rejected", (label, report)
    print(f"Source bundle: 31 scoped roots, {len(mutations)} malformed bundles rejected")
    scalar_path = artifacts / "scalar-bundle.json"
    scalar_bytes = scalar_path.read_bytes()
    assert hashlib.sha256(scalar_bytes).hexdigest() == manifest["scalar_bundle_sha256"]
    scalar = json.loads(scalar_bytes)
    code, report = run(scalar_path, "elaborate")
    assert code == 0 and len(report) == 1 and report[0]["status"] == "typed", report
    mutations = []
    bundle = scalar
    add("root result type", lambda b: b["roots"][0]["schema"].update(
        body={"tag": "con", "args": ["TC TCInteger", []]}))
    add("missing proof argument", lambda b: b["roots"][0].update(
        expression=b["roots"][0]["expression"]["args"][0]))
    add("unsatisfied width constraint", lambda b: next(n for n in nodes(b["roots"][0])
        if n.get("tag") == "num")["args"].__setitem__(0, "1"))
    add("lambda annotation", lambda b: next(n for n in nodes(b["groups"])
        if n.get("tag") == "abs")["args"].__setitem__(1,
            {"tag": "con", "args": ["TC TCInteger", []]}))
    add("unsupported primitive", lambda b: [n.update(text="unsupported", origin="Cryptol::unsupported")
        for n in nodes(b) if n.get("text") == "^"])
    add("application argument", lambda b: b["roots"][0].update(expression={"tag": "app",
        "args": [deepcopy(b["roots"][0]["expression"]), deepcopy(b["roots"][0]["expression"])]}))
    with tempfile.TemporaryDirectory(prefix="cryptol-typing-rejections-") as temporary:
        path = Path(temporary) / "mutated.json"
        for label, changed in mutations:
            path.write_text(json.dumps(changed))
            code, report = run(path)
            assert code == 0 and report["status"] == "scoped", (label, report)
            code, report = run(path, "elaborate")
            assert code != 0 and report["status"] == "rejected", (label, report)
    print(f"Scalar elaboration: imported root typed, {len(mutations)} malformed terms rejected")
    specialization_checks(artifacts, manifest)


if __name__ == "__main__":
    main()
