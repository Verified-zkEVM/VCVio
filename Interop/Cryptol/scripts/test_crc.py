#!/usr/bin/env python3
"""CRC chunking regressions and optional comparisons with actual Foundation code.

The executable checks supplement the register's all-input append theorem. They
are not source-preservation certificates, and they do not turn the retained
whole-module AST into a semantic import.
"""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

import polyfun_tools  # noqa: F401
from pins import CRYPTOL, FOUNDATION, verify_checkout
from test_evaluators import observe
from extract_foundation import ROOT

PROFILES = [
    ("CCITT", "CRC16_CCITT_FALSE", dict(width=16, polynomial=0x1021, initial=0xffff,
        reflectInput=False, reflectOutput=False, xorMask=0), 0x29b1),
    ("Ethernet", "CRC32_IEEE_802_3_Ethernet", dict(width=32, polynomial=0x04c11db7,
        initial=0xffffffff, reflectInput=True, reflectOutput=True, xorMask=0xffffffff), 0xcbf43926),
    ("Asymmetric", None, dict(width=7, polynomial=0x09, initial=0x43,
        reflectInput=True, reflectOutput=True, xorMask=0x12), None),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cryptol", type=Path)
    parser.add_argument("--foundation", type=Path)
    args = parser.parse_args()
    if args.cryptol:
        verify_checkout(args.foundation, FOUNDATION)
        version = subprocess.check_output([str(args.cryptol), "--version"], text=True)
        assert "Git commit " + CRYPTOL in version
    lean = ROOT.parents[1] / ".lake/build/bin/cryptol-interop"
    messages = [[], [0], [255], list(b"123456789"), [1, 128, 3, 255, 0, 17, 64]]
    comparisons = 0
    with tempfile.TemporaryDirectory(prefix="cryptol-crc-") as temporary:
        temporary = Path(temporary)
        request = temporary / "request.json"

        def native(profile, chunks):
            request.write_text(json.dumps(profile | {"chunks": chunks}))
            return json.loads(subprocess.check_output([str(lean), "foundation", "crc", str(request)],
                                                     text=True))

        for label, module, profile, check in PROFILES:
            observations = []
            for message in messages:
                whole = native(profile, [message])
                chunks = [[], message[:1], message[1:4], [], message[4:]]
                split = native(profile, chunks)
                assert split["updates"][-1] == whole["updates"][-1]
                assert split["concatenated"] == whole["concatenated"]
                if check is not None and message == list(b"123456789"):
                    assert whole["concatenated"] == check
                observations.append((message, whole["updates"][-1]))
            if args.cryptol:
                if module:
                    source = args.foundation / "shared/CRC" / (module + ".cry")
                else:
                    source = temporary / "Asymmetric.cry"
                    source.write_text("module Asymmetric = shared::CRC::Main where\n"
                        "type CRCResultWidth = 7\npolynomial = 0x89\n"
                        "initialValue : [7]\ninitialValue = 67\n"
                        "inputDataReflected = True\nresultDataReflected = True\n"
                        "XORValue : [7]\nXORValue = 18\n"
                        "check : [7]\ncheck = 0\nmagicCheck : [7]\nmagicCheck = 0\n")
                checks = []
                for message, result in observations:
                    data = "join (" + json.dumps(message) + f" : [{len(message)}][8])"
                    checks.append(f"(CRCUpdate {profile['initial']} ({data})).crc == {result['crc']}")
                    checks.append(f"(CRCUpdate {profile['initial']} ({data})).state == {result['state']}")
                expression = " && ".join("(" + c + ")" for c in checks)
                for mode in ("normal", "reference"):
                    observe(args.cryptol, expression, "True", mode, args.foundation, source)
                    comparisons += len(checks)
    print(f"CRC: {len(PROFILES) * len(messages)} native chunking cases; "
          f"{comparisons} official evaluator field comparisons")


if __name__ == "__main__":
    main()
