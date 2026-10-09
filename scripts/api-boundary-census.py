#!/usr/bin/env python3
"""Report API-boundary source signals; this is an inventory, not a defect linter."""

from pathlib import Path
import re
import runpy


ROOT = Path(__file__).resolve().parent.parent
SCANNER = runpy.run_path(str(ROOT / "scripts/count-expose-boundary.py"))
ROOTS = (
    "ToMathlib", "VCVio", "LatticeCrypto", "HashSig", "Extern", "Examples",
    "VCVioWidgets", "VCVioCslib", "VCVioComplexity/VCVioComplexity",
)


def signals(path: Path) -> tuple[int, ...]:
    """Count tokenized command/proof spellings without reading comments or literals."""
    stream = SCANNER["tokens"](path.read_text(encoding="utf-8"))
    code = " ".join(token for token in stream
                    if re.fullmatch(r"[\w'.]+|@\[|\[|\]|:=", token))
    return (
        int(SCANNER["broadly_exposed"](path)),
        len(re.findall(r"\bimport all\b", code)),
        len(re.findall(r"\battribute \[ local (?:implicit_)?reducible\b", code)),
        stream.count("expose"),
        stream.count("rfl"),
        sum(stream.count(word) for word in ("change", "unfold", "dsimp", "convert")),
    )


if __name__ == "__main__":
    print("module\tbroad_expose\timport_all\tlocal_reducibility\texpose_tokens"
          "\trfl_tokens\tunfolding_tokens")
    for library in ROOTS:
        for path in sorted((ROOT / library).rglob("*.lean")):
            print(str(path.relative_to(ROOT)), *signals(path), sep="\t")
