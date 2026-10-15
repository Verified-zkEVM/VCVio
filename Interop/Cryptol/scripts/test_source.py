#!/usr/bin/env python3
"""Scope/kind acceptance, malformed-source rejection, and reference provenance."""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

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


def main():
    artifacts = ROOT / "artifacts/references"
    source = artifacts / "bundle.json"
    data = source.read_bytes()
    bundle = json.loads(data)
    manifest = json.loads((artifacts / "manifest.json").read_text())
    assert hashlib.sha256(data).hexdigest() == manifest["bundle_sha256"]
    assert hashlib.sha256((artifacts / "FoundationReferences.cry").read_bytes()).hexdigest() == \
        manifest["entry_sha256"]
    assert hashlib.sha256((ROOT / "exporter/Main.hs").read_bytes()).hexdigest() == \
        manifest["exporter_sha256"]
    code, report = run(source)
    assert code == 0 and report["status"] == "scoped", report
    assert report["declarations"] == manifest["validation"]["declarations"]
    assert report["roots"] == [e["root"] for e in manifest["entries"]]
    numeric = json.loads((artifacts / "numeric-cases.json").read_text())
    classes = json.loads((artifacts / "class-cases.json").read_text())
    assert hashlib.sha256((artifacts / "numeric-cases.json").read_bytes()).hexdigest() == \
        manifest["numeric_sha256"]
    assert hashlib.sha256((artifacts / "class-cases.json").read_bytes()).hexdigest() == \
        manifest["class_sha256"]
    assert len(numeric) == manifest["numeric_cases"]
    assert len(classes) == manifest["class_cases"]
    assert numeric == json.loads(subprocess.check_output([str(LEAN), "model", "numeric"]))
    assert classes == json.loads(subprocess.check_output([
        str(LEAN), "source", "constraints", str(artifacts / "class-cases.json")]))
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
    assert hashlib.sha256((ROOT / "Bridge/ImportedScalarSource.lean").read_bytes()).hexdigest() == \
        manifest["scalar_lean_sha256"]
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


if __name__ == "__main__":
    main()
