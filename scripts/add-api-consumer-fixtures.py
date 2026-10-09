#!/usr/bin/env python3
"""Add ordinary-import semantic fixtures to an existing scratch Lake consumer."""

import json
from pathlib import Path
import re
import shutil
import sys


ROOT = Path(__file__).resolve().parents[1]
FIXTURES = {
    "APIHeap": "VCVioTest/ModuleAPI/Heap.lean",
    "APIVector": "LatticeCryptoTest/Ring/VectorAPI.lean",
    "APIFacade": "VCVioTest/PFunctorFacade.lean",
    "APINativeWP": "VCVioTest/ProgramLogic/MeasureWP.lean",
    "APICoreWP": "VCVioTest/ProgramLogic/CoreWP.lean",
    "APISupportMeasure": "VCVioTest/OracleComp/SupportMeasure.lean",
    "APIComplexity": "VCVioTest/CryptoFoundations/ComputationalComplexitySoundness.lean",
    "APIComplexityAdapters": "VCVioTest/CryptoFoundations/ComplexityAdapters.lean",
    "APIReactive": "VCVioTest/ReactiveKernel.lean",
    "APIReactiveAdversarial": "VCVioTest/ReactiveNetworkAdversarial.lean",
    "APIRuntime": "VCVioTest/Runtime.lean",
}


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: add-api-consumer-fixtures.py CONSUMER_DIRECTORY")
    consumer = Path(sys.argv[1]).resolve()
    lakefile = consumer / "lakefile.toml"
    source = lakefile.read_text()
    target_match = re.search(r"(?m)^defaultTargets\s*=\s*(\[[^\n]*\])$", source)
    if target_match is None:
        raise SystemExit("expected a single-line JSON-compatible defaultTargets array")
    targets = json.loads(target_match.group(1))
    libraries = set(re.findall(r'\[\[lean_lib\]\]\s*name\s*=\s*"([^"]+)"', source))
    for name, relative in FIXTURES.items():
        shutil.copyfile(ROOT / relative, consumer / f"{name}.lean")
        if name not in targets:
            targets.append(name)
        if name not in libraries:
            source += f'\n[[lean_lib]]\nname = "{name}"\n'
    source, count = re.subn(
        r"(?m)^defaultTargets\s*=\s*\[[^\n]*\]$",
        "defaultTargets = " + json.dumps(targets),
        source,
    )
    if count != 1:
        raise SystemExit("expected one single-line defaultTargets declaration")
    lakefile.write_text(source)
    print(f"Registered {len(FIXTURES)} API consumer modules in {consumer}")


if __name__ == "__main__":
    main()
