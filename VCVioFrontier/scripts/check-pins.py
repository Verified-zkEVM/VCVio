#!/usr/bin/env python3
"""Check the nested lockfiles or update them from a local PolyFun commit (Python 3.11+)."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
PINNED = ("PolyFun", "PolyFunFrontier", "cslib-frontier", "cslib", "mathlib")
FRONTIER_NAMES = {"VCVioFrontier", "PolyFunFrontier", "CslibFrontier", "cslib-frontier"}
sys.path.insert(0, str(ROOT.parent / "scripts"))
from lean_source_tokens import token_matches


def revisions(manifest):
    return {p["name"].strip("«»"): p.get("rev") for p in json.loads(manifest)["packages"]}


def check_root(root):
    """Catch an accidental root requirement even before someone regenerates the lockfile."""
    stable = revisions((root / "lake-manifest.json").read_text())
    for name in stable:
        if name in FRONTIER_NAMES:
            sys.exit(f"stable VCVio unexpectedly resolves {name}")
    for token in token_matches((root / "lakefile.lean").read_text()):
        name = token[0].strip('«»"').removesuffix(".git").rsplit("/", 1)[-1]
        if name in FRONTIER_NAMES:
            sys.exit(f"stable VCVio lakefile names the optional dependency {name}")


def check(root=ROOT):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    locked = {p["name"].strip("«»"): p for p in manifest["packages"]}
    ours = {name: package.get("rev") for name, package in locked.items()}
    declared = {r["name"]: r for r in tomllib.loads((root / "lakefile.toml").read_text())["require"]}
    errors = []
    for name in PINNED:
        rev = declared.get(name, {}).get("rev", "")
        if not re.fullmatch("[0-9a-f]{40}", rev) or rev != ours.get(name):
            errors.append(f"{name} requires one full revision shared by lakefile and manifest")
    if ours.get("PolyFun") != ours.get("PolyFunFrontier"):
        errors.append("PolyFun and its nested package must come from the same commit")

    # The fork carries the review series until the pair of packages lands upstream.
    upstream = "https://github.com/Verified-zkEVM/PolyFun"
    polyfun_url = declared.get("PolyFun", {}).get("git")
    if polyfun_url not in (upstream, "https://github.com/dtumad/PolyFun"):
        errors.append("unexpected PolyFun repository")
    for name, subdir in (("PolyFun", None), ("PolyFunFrontier", "PolyFunFrontier")):
        expected = polyfun_url if subdir is None else {"url": polyfun_url, "subDir": subdir}
        entry = locked.get(name, {})
        if (declared.get(name, {}).get("git") != expected or entry.get("type") != "git"
                or entry.get("url") != polyfun_url or entry.get("subDir") != subdir):
            errors.append(f"{name} must resolve from the shared PolyFun repository at {subdir or '.'}")

    packages = root / manifest["packagesDir"]
    toolchain = (root / "lean-toolchain").read_text().strip()
    for peer in (packages / "PolyFunFrontier/PolyFunFrontier", packages / "cslib-frontier"):
        if (peer / "lean-toolchain").read_text().strip() != toolchain:
            errors.append(f"lean-toolchain differs from {peer.name}")
        for name, rev in revisions((peer / "lake-manifest.json").read_text()).items():
            # PolyFunFrontier's local parent path resolves to our pinned PolyFun checkout.
            if rev is not None and ours.get(name) != rev:
                errors.append(f"{name} must match {peer.name}'s lockfile at {rev}")
    if errors:
        sys.exit("\n".join(errors))
    print(f"VCVioFrontier agrees with PolyFun {ours['PolyFun'][:12]} and "
          f"cslib-frontier {ours['cslib-frontier'][:12]} on {toolchain}")


def sync(repo, ref):
    def git(*args):
        return subprocess.check_output(["git", "-C", repo, *args], text=True)

    sha = git("rev-parse", "--verify", ref + "^{commit}").strip()
    pins = revisions(git("show", sha + ":PolyFunFrontier/lake-manifest.json"))
    pins.update(PolyFun=sha, PolyFunFrontier=sha)
    config = ROOT / "lakefile.toml"
    contents = config.read_text()
    for name in PINNED:
        pattern = rf'(^name = "{re.escape(name)}"\n[^\[]*?^rev = ")[0-9a-f]{{40}}(")'
        contents, count = re.subn(pattern, rf"\g<1>{pins[name]}\2", contents, flags=re.M)
        if count != 1:
            sys.exit(f"expected exactly one revision for {name}")
    toolchain = git("show", sha + ":PolyFunFrontier/lean-toolchain")
    config.write_text(contents)
    (ROOT / "lean-toolchain").write_text(toolchain)
    subprocess.run(["lake", "update", "--keep-toolchain", *PINNED], cwd=ROOT, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group()
    actions.add_argument("--sync-from", nargs=2, metavar=("POLYFUN_CHECKOUT", "REF"),
                         help="resolve the pins from this PolyFun commit, then run the check")
    actions.add_argument("--root-only", action="store_true",
                         help="check root dependency isolation without fetching any packages")
    args = parser.parse_args()
    check_root(ROOT.parent)
    if args.sync_from:
        sync(*args.sync_from)
    if not args.root_only:
        check()
