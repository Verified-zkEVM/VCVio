"""Locate the shared Cryptol tooling in the PolyFun package checkout.

PolyFun owns the pins, the frontend identity check, the quotation helpers, the
exporter and the evaluator observations. A local override uses the same
`POLYFUN_PATH` as the Lake build. Scripts in this directory take precedence.
"""

import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[1]
POLYFUN = Path(os.environ.get("POLYFUN_PATH") or REPOSITORY / ".lake/packages/PolyFun").resolve()
SCRIPTS = POLYFUN / "PolyFunCryptol/scripts"
EXPORTER_SOURCE = POLYFUN / "PolyFunCryptol/exporter/Main.hs"
if not (SCRIPTS / "pins.py").is_file():
    raise SystemExit(f"PolyFun Cryptol tooling not found at {SCRIPTS}; "
                     "run `lake update PolyFun` or set POLYFUN_PATH")
sys.path.append(str(SCRIPTS))
