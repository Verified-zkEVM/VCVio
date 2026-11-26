#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""List the `Interop/` sub-projects and the roots of their axiom sweeps.

A sub-project is a directory `Interop/<Sub>/` holding its own Lake package, `lakefile.toml`. Its
axiom-sweep roots are the `roots` of the libraries its package builds by default
(`defaultTargets`), so they are written once, in the lakefile. CI's `Interop Sub-projects` job
builds and sweeps each sub-project this lists.

  interop-subprojects.py list        the sub-project directory names, as a JSON array
  interop-subprojects.py roots DIR   the sweep roots of the package in DIR, one per line

Run from the repository root (`list`) or from anywhere (`roots`).
"""

import json
import sys
import tomllib
from pathlib import Path


def subprojects(interop: Path) -> list[str]:
    return sorted(path.parent.name for path in interop.glob("*/lakefile.toml"))


def sweep_roots(package: Path) -> list[str]:
    config = tomllib.loads((package / "lakefile.toml").read_text())
    libraries = {lib["name"]: lib for lib in config.get("lean_lib", [])}
    defaults = [name for name in config.get("defaultTargets", []) if name in libraries]
    if not defaults:
        raise SystemExit(f"{package}/lakefile.toml: no default `lean_lib` to sweep")
    roots = []
    for name in defaults:
        lib = libraries[name]
        if "globs" in lib and "roots" not in lib:
            raise SystemExit(f"{package}/lakefile.toml: default library {name} has `globs` but "
                             "no `roots`; the sweep imports its roots")
        # Lake's default: a library without `roots` has the single root named after it.
        roots.extend(lib.get("roots", [name]))
    # `lake exe axiomsweep` with no `--root` sweeps VCVio's own libraries instead.
    if not roots:
        raise SystemExit(f"{package}/lakefile.toml: no sweep roots")
    return roots


def main(args: list[str]) -> int:
    if args == ["list"]:
        print(json.dumps(subprojects(Path("Interop"))))
    elif len(args) == 2 and args[0] == "roots":
        print("\n".join(sweep_roots(Path(args[1]))))
    else:
        print("usage: interop-subprojects.py list | roots DIR", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
