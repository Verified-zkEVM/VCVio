#!/usr/bin/env python3
"""The retained Foundation utility bundle and its quoted Imperative import.

PolyFun's own module tests cover whole-module checking, diagnosis and the broader
Foundation corpus. This check ties the committed bundle to the Bridge quotations
and to typed elaboration, and rejects an ill-typed and a meaning-changing body.
"""

from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile

import polyfun_tools  # noqa: F401
from corpus import elaborate_module
from quote_imperative import quote_imperative, quote_imperative_bodies
from extract_foundation import ROOT
from test_source import nodes

IMPERATIVE = "shared::common::utils::Imperative"


def main():
    lean = ROOT.parents[1] / ".lake/build/bin/cryptol-interop"
    path = ROOT / "artifacts/modules/list.json"
    utility = json.loads(path.read_text())
    result = subprocess.run([str(lean), "source", "modules", str(path)],
                            capture_output=True, text=True)
    report = json.loads(result.stdout)
    assert result.returncode == 0 and all(r["scope"]["status"] == "accepted" for r in report), report
    assert (ROOT / "Bridge/ImperativeSource.lean").read_bytes() == quote_imperative(utility)
    typed = elaborate_module(lean, path, IMPERATIVE, code=True)
    assert typed["expression_typing"] == "accepted" and typed["shared_declarations"] == 2
    assert typed["source_correspondence"] == "not-established"
    assert (ROOT / "Bridge/ImperativeBodies.lean").read_bytes() == quote_imperative_bodies(utility, typed)

    def mutate(type_preserving):
        mutant = deepcopy(utility)
        module = next(m for m in mutant["modules"] if m["provenance"]["name"] == IMPERATIVE)
        condition = next(n for n in nodes(module["groups"]) if n.get("tag") == "if")
        if type_preserving:
            # Returning the initial state has the right polymorphic type but changes the loop.
            replacement = deepcopy(condition["args"][2])
            condition.clear()
            condition.update(replacement)
            # The loop's self call disappeared. Metadata must reflect the changed body.
            next(d for d in module["declarations"] if d["name"]["text"] == "while")["dependencies"] = []
        else:
            # A type parameter cannot be used as Bit; this still passes scope/kind checking.
            condition["args"][0] = deepcopy(condition["args"][2])
        with tempfile.TemporaryDirectory(prefix="cryptol-typed-module-") as temporary:
            mutant_path = Path(temporary) / "mutant.json"
            mutant_path.write_text(json.dumps(mutant))
            return elaborate_module(lean, mutant_path, IMPERATIVE, code=True)

    rejected = mutate(False)
    assert rejected["status"] == "rejected" and "scheme mismatch" in rejected["message"], rejected
    changed = mutate(True)
    assert changed["expression_typing"] == "accepted" and changed["bodies"] != typed["bodies"]
    print("Imperative: retained utility bundle, exact quotations, typed import, "
          "2 typing/meaning mutations")


if __name__ == "__main__":
    main()
