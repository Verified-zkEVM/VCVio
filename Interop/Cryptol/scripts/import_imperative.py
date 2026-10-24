#!/usr/bin/env python3
"""Export Foundation's utility modules, including the complete Imperative module.

The official exporter owns parsing and elaboration; PolyFun's Lean checker types
the module. `Bridge/Imperative.lean` imports the committed bundle with
`cryptol_import`, which checks whole-module elaboration in the kernel.
"""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

import polyfun_tools  # noqa: F401
from pins import FOUNDATION, canonical, verify_checkout
from frontend import check_frontend
from corpus import elaborate_module
from extract_foundation import ROOT

BUNDLE = ROOT / "artifacts/modules/list.json"
IMPERATIVE = "shared::common::utils::Imperative"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=Path)
    parser.add_argument("--foundation", required=True, type=Path)
    parser.add_argument("--cryptol-source", required=True, type=Path)
    parser.add_argument("--lean", type=Path, default=ROOT.parents[1] / ".lake/build/bin/cryptol-interop")
    parser.add_argument("--check", action="store_true", help="require byte-identical committed outputs")
    args = parser.parse_args()
    verify_checkout(args.foundation, FOUNDATION)
    result = subprocess.run([str(args.exporter), "--module-bundle", str(args.foundation),
                             str(args.foundation / "shared/common/utils/List.cry")],
                            check=True, capture_output=True, text=True, timeout=120)
    bundle = json.loads(result.stdout)
    check_frontend(bundle, args.cryptol_source)
    data = canonical(bundle)
    with tempfile.TemporaryDirectory(prefix="cryptol-imperative-") as temporary:
        path = Path(temporary) / "list.json"
        path.write_bytes(data)
        typed = elaborate_module(args.lean, path, IMPERATIVE, code=True)
    if typed["expression_typing"] != "accepted":
        raise ValueError(f"Imperative no longer elaborates: {typed}")
    if args.check:
        if BUNDLE.read_bytes() != data:
            raise ValueError(f"stale Imperative artifact: {BUNDLE}")
    else:
        BUNDLE.write_bytes(data)
    print(f"Imperative: {typed['shared_declarations']} shared declarations typed")


if __name__ == "__main__":
    main()
