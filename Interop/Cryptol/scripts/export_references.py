#!/usr/bin/env python3
"""Export full Foundation dependency graphs through the pinned typed-AST exporter.

The committed bundle is an input to Lean validation, not a typing certificate.
This driver checks source provenance and compares the numeric semantics before
writing any artifacts. The existing compression certificate is independent.
"""

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

from extract_foundation import COMPRESSION, CRYPTOL, FOUNDATION, ROOT
from quote_reference import quote_scalar

FAMILIES = {"SHA2", "SHA3", "SHAKE", "Keccak", "AES", "CRC"}
ARTIFACTS = ROOT / "artifacts" / "references"


def run(*args):
    return subprocess.run(args, check=True, text=True, capture_output=True).stdout


def digest(data):
    return hashlib.sha256(data).hexdigest()


def entry_module(entries):
    modules = list(dict.fromkeys(e["source"]["module"] for e in entries[1:]))
    imports = "\n".join(
        f'import {module[:-4].replace("/", "::")} as R{i}'
        for i, module in enumerate(modules))
    wrapper = COMPRESSION.replace(
        "module PolyFunCompression where",
        "module FoundationReferences where\n"
        "import Cryptol::Reference as OfficialReference\n" + imports)
    roots = ["result"] + [
        f'R{modules.index(e["source"]["module"])}::{e["source"]["symbol"]}'
        for e in entries[1:]]
    return wrapper, roots


def verify_checkout(path, revision):
    if run("git", "-C", str(path), "rev-parse", "HEAD").strip() != revision:
        raise ValueError(f"wrong source revision: {path}")
    if run("git", "-C", str(path), "status", "--porcelain", "--untracked-files=no").strip():
        raise ValueError(f"modified tracked source files: {path}")


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--cryptol-source", required=True, type=Path)
    parser.add_argument("--lean", type=Path, default=ROOT.parents[1] / ".lake/build/bin/cryptol-interop")
    parser.add_argument("--check", action="store_true", help="require byte-identical committed artifacts")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    verify_checkout(args.cryptol_source, CRYPTOL)
    entries = [e for e in json.loads((ROOT / "coverage.json").read_text())["entries"]
               if e["family"] in FAMILIES]
    if len(entries) != 31 or entries[0]["id"] != "sha256-compression":
        raise ValueError("reference catalogue selection changed; review the entry module")
    wrapper, roots = entry_module(entries)
    numeric = json.loads(run(str(args.exporter), "--numeric"))
    if numeric != json.loads(run(str(args.lean), "model", "numeric")):
        raise ValueError("Lean numeric semantics differs from pinned InfNat")
    with tempfile.TemporaryDirectory(prefix="cryptol-reference-") as temporary:
        classes = json.loads(run(str(args.exporter), "--classes"))
        case_file = Path(temporary) / "classes.json"
        case_file.write_bytes(canonical(classes))
        if classes != json.loads(run(str(args.lean), "source", "constraints", str(case_file))):
            raise ValueError("Lean class resolution differs from the pinned class solver")
        path = Path(temporary) / "FoundationReferences.cry"
        path.write_text(wrapper)
        bundle = json.loads(run(str(args.exporter), str(args.foundation), str(path), *roots))
        if bundle["cryptol_revision"] != CRYPTOL:
            raise ValueError("exporter reports an unsupported Cryptol revision")
        if [r["text"] for r in bundle["roots"]] != roots:
            raise ValueError("exporter changed the requested roots")
        for module in bundle["modules"]:
            name = module["path"]
            if name == "$entry/FoundationReferences.cry":
                contents = wrapper.encode()
            elif name.startswith("$builtin/"):
                # Cryptol embeds these exact library bytes in its executable.
                relative = name[len("$builtin/"):].replace("::", "/") + ".cry"
                run("git", "-C", str(args.cryptol_source), "ls-files", "--error-unmatch",
                    "--", "lib/" + relative)
                contents = (args.cryptol_source / "lib" / relative).read_bytes()
            elif name.startswith("$cryptol/"):
                raise ValueError(f"unaccounted external source: {name}")
            else:
                source = (args.foundation / name).resolve()
                if not source.is_relative_to(args.foundation.resolve()):
                    raise ValueError(f"source escapes Foundation: {name}")
                run("git", "-C", str(args.foundation), "ls-files", "--error-unmatch", "--", name)
                contents = source.read_bytes()
            if digest(contents) != module["sha256"]:
                raise ValueError(f"source digest mismatch: {name}")
        data = canonical(bundle)
        source = Path(temporary) / "bundle.json"
        source.write_bytes(data)
        inspection = json.loads(run(str(args.lean), "source", "inspect", str(source)))
        if inspection["status"] != "scoped":
            raise ValueError("Lean scope/kind validation did not succeed")
        scalar = json.loads(run(str(args.exporter), str(args.foundation), str(path),
                                "(sigma_256_0 : [32] -> [32])"))
        if scalar["cryptol_revision"] != CRYPTOL or scalar["modules"] != bundle["modules"]:
            raise ValueError("scalar export changed the validated source provenance")
        scalar_data = canonical(scalar)
        scalar_lean = quote_scalar(scalar)
    manifest = {
        "schema_version": 1, "cryptol_revision": CRYPTOL, "foundation_revision": FOUNDATION,
        "bundle_sha256": digest(data), "entry_sha256": digest(wrapper.encode()),
        "exporter_sha256": digest((ROOT / "exporter/Main.hs").read_bytes()),
        "numeric_cases": len(numeric),
        "class_cases": len(classes),
        "numeric_sha256": digest(canonical(numeric)), "class_sha256": digest(canonical(classes)),
        "scalar_bundle_sha256": digest(scalar_data),
        "scalar_lean_sha256": digest(scalar_lean),
        "entries": [{"id": e["id"], "root": root} for e, root in zip(entries, roots)],
        "validation": {k: inspection[k] for k in ["status", "groups", "declarations", "modules"]},
        "trust_boundary": ["Pinned Cryptol parser, renamer, type checker and module elaborator",
                           "Haskell typed-AST serialization and provenance collection"],
        "not_established": ["Expression typing and constraint entailment in Lean",
                            "Semantic correspondence with the Haskell evaluator",
                            "Implementation equivalence for these entry points"],
    }
    outputs = {"bundle.json": data, "FoundationReferences.cry": wrapper.encode(),
               "scalar-bundle.json": scalar_data,
               "numeric-cases.json": canonical(numeric), "class-cases.json": canonical(classes),
               "cryptol-license.txt": (args.cryptol_source / "LICENSE").read_bytes(),
               "manifest.json": (json.dumps(manifest, indent=2) + "\n").encode()}
    for name, contents in outputs.items():
        path = ARTIFACTS / name
        if args.check:
            if not path.is_file() or path.read_bytes() != contents:
                raise ValueError(f"stale reference artifact: {path}")
        else:
            ARTIFACTS.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)
    scalar_path = ROOT / "Bridge/ImportedScalarSource.lean"
    if args.check:
        if not scalar_path.is_file() or scalar_path.read_bytes() != scalar_lean:
            raise ValueError(f"stale scalar quotation: {scalar_path}")
    else:
        scalar_path.write_bytes(scalar_lean)
    print(f"31 roots; {inspection['declarations']} declarations; {len(numeric)} numeric cases; "
          f"{len(classes)} class cases; "
          "source digests and Lean scope/kind checks passed")


if __name__ == "__main__":
    main()
