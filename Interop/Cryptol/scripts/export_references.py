#!/usr/bin/env python3
"""Export full Foundation dependency graphs through PolyFun's pinned typed-AST exporter.

The committed bundle is an input to Lean validation, not a typing certificate.
This driver checks source provenance before writing any artifacts. PolyFun owns
the language-level numeric, class and canary cases. The existing compression
certificate is independent.
"""

import argparse
import json
import tempfile
from pathlib import Path

import polyfun_tools
from pins import canonical, digest, run, verify_checkout
from frontend import frontend_patches, check_frontend
from extract_foundation import COMPRESSION, CRYPTOL, FOUNDATION, ROOT

FAMILIES = {"SHA2", "SHA3", "SHAKE", "Keccak", "AES", "CRC"}
ARTIFACTS = ROOT / "artifacts" / "references"


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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--cryptol-source", required=True, type=Path)
    parser.add_argument("--lean", type=Path, default=ROOT.parents[1] / ".lake/build/bin/cryptol-interop")
    parser.add_argument("--check", action="store_true", help="require byte-identical committed artifacts")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    patches = frontend_patches(args.cryptol_source)
    entries = [e for e in json.loads((ROOT / "coverage.json").read_text())["entries"]
               if e["family"] in FAMILIES]
    if len(entries) != 31 or entries[0]["id"] != "sha256-compression":
        raise ValueError("reference catalogue selection changed; review the entry module")
    wrapper, roots = entry_module(entries)
    with tempfile.TemporaryDirectory(prefix="cryptol-reference-") as temporary:
        path = Path(temporary) / "FoundationReferences.cry"
        path.write_text(wrapper)
        bundle = json.loads(run(str(args.exporter), str(args.foundation), str(path), *roots))
        check_frontend(bundle, args.cryptol_source)
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
        specialization = json.loads(run(str(args.exporter), "--specialize",
            str(args.foundation), str(path), "(sigma_256_0 : [32] -> [32])"))
        if specialization["source"] != scalar:
            raise ValueError("specialization changed its unspecialized endpoint")
        specialized_data = canonical(specialization["candidate"])
        checked = Path(temporary) / "candidate.json"
        checked.write_bytes(specialized_data)
        reports = json.loads(run(str(args.lean), "source", "elaborate", str(checked)))
        if not reports or any(r["status"] != "typed" for r in reports):
            raise ValueError("typed import failed: candidate")
    manifest = {
        "schema_version": 1, "cryptol_revision": CRYPTOL, "foundation_revision": FOUNDATION,
        "frontend_patches": patches,
        "bundle_sha256": digest(data), "entry_sha256": digest(wrapper.encode()),
        "exporter_sha256": digest(polyfun_tools.EXPORTER_SOURCE.read_bytes()),
        "scalar_bundle_sha256": digest(scalar_data),
        "specialization": {"pass": specialization["pass"],
            "primitive_policy": specialization["primitive_policy"],
            "bundle_sha256": digest(specialized_data),
            "evidence": "Cryptol.Bridge.ImportedSpecialization.correct"},
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
               "specialized-scalar-bundle.json": specialized_data,
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
    print(f"31 roots; {inspection['declarations']} declarations; "
          "source digests and Lean scope/kind checks passed")


if __name__ == "__main__":
    main()
