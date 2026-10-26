#!/usr/bin/env python3
"""Run a validation command against a clean commit and its checked-out dependency lock."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def source_inputs(root: Path) -> dict:
    """Capture checked inputs without invoking Lake or other build commands."""
    if git(root, "status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"):
        raise ValueError("source tree is dirty, including staged or untracked source files")
    manifest_bytes = (root / "lake-manifest.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    dependencies = {}
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError(f"unsupported dependency kind for pinned plan: {package['name']}")
        checkout = root / manifest["packagesDir"] / package["name"]
        if not (checkout / ".git").exists():
            raise ValueError(f"missing dependency checkout: {package['name']}")
        actual = git(checkout, "rev-parse", "HEAD")
        if actual != package["rev"]:
            raise ValueError(f"dependency revision differs from lock: {package['name']}")
        if git(checkout, "status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"):
            raise ValueError(f"dependency source tree is dirty: {package['name']}")
        dependencies[package["name"]] = actual
    toolchain = (root / "lean-toolchain").read_text().strip()
    return {
        "commit": git(root, "rev-parse", "HEAD"),
        "tree": git(root, "rev-parse", "HEAD^{tree}"),
        "leanToolchain": toolchain,
        "manifestSha256": hashlib.sha256(manifest_bytes).hexdigest(),
        "dependencyRevisions": dependencies,
    }


def snapshot(root: Path) -> dict:
    # Even a version query can update generated sources or dependency checkouts.
    # Check every invariant on both sides before accepting its output.
    before = source_inputs(root)
    lean_version = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=root, text=True
    ).strip()
    after = source_inputs(root)
    if after != before:
        raise ValueError("source or dependency inputs changed during Lean version query")
    expected = before["leanToolchain"].rsplit(":", 1)[-1].removeprefix("v")
    if not re.search(r"\bversion " + re.escape(expected) + r"(?:,|\))", lean_version):
        raise ValueError("active Lean version differs from lean-toolchain")
    return {**before, "activeLeanVersion": lean_version}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-dir", type=Path, help="evidence directory outside the source tree")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("provide a validation command after --")
    root = Path(git(Path.cwd(), "rev-parse", "--show-toplevel")).resolve()
    report = (args.report_dir or Path(tempfile.mkdtemp(prefix="vcvio-validation-"))).resolve()
    if report.is_relative_to(root):
        parser.error("write validation evidence outside the source tree")
    report.mkdir(parents=True, exist_ok=True)
    record = {"command": command, "status": "failed"}
    try:
        record["before"] = snapshot(root)
        (report / "lean-toolchain").write_bytes((root / "lean-toolchain").read_bytes())
        (report / "lake-manifest.json").write_bytes((root / "lake-manifest.json").read_bytes())
        print(f"Validating {record['before']['commit']}; command log: {report / 'command.log'}", flush=True)
        with (report / "command.log").open("w") as log:
            record["commandExitCode"] = subprocess.run(
                command, cwd=root, stdout=log, stderr=subprocess.STDOUT, check=False
            ).returncode
        record["after"] = snapshot(root)
        if record["after"] != record["before"]:
            raise ValueError("commit, source tree, toolchain, lock, or dependency revisions changed")
        if record["commandExitCode"] != 0:
            raise ValueError(f"validation command exited {record['commandExitCode']}")
        record["status"] = "passed"
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        record["error"] = str(error)
    (report / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Validation {record['status']}; evidence: {report}", flush=True)
    if record["status"] != "passed":
        print(record.get("error", "validation failed"), flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
