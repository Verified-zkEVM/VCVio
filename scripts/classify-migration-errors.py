#!/usr/bin/env python3
"""Classify the build errors of a migration dry run.

usage: python3 scripts/classify-migration-errors.py OUT

OUT is the directory `scripts/migration-dry-run.sh` filled: one `pr-N/` per pull request with its
`build.log`, `pr-files.txt` and `shared-files.txt`. Every `error:` of a build log becomes a row of
OUT/migration-dry-run.csv with its pull request, file, line, kind, the name the message is about,
the file's scope, and the first line of the message. The scope tells a migration error from an
error of the automatic merge: `pr` for a file only the pull request touched, `shared` for one this
branch touched as well since `main`, where the merge took the pull request's side of a conflicting
hunk, and `other` for a file the pull request did not touch, which fails because of one it did.
An unknown name is looked up in the codemod's `RENAMES` and `LEGACY_HINTS`, so a name the codemod
knows but did not rewrite is told apart from a name it has no entry for. OUT/summary.md counts the
rows by pull request, kind and scope, and lists the unknown names and modules.
"""

from __future__ import annotations

import collections
import csv
import importlib.util
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
ERROR = re.compile(r"^error: (?P<file>[^:\n]+\.lean):(?P<line>\d+):(?P<col>\d+): (?P<msg>.*)$")
KINDS = [
    ("unknown-name", re.compile(
        r"[Uu]nknown (?:identifier|constant)(?: `(?P<name>[^`]+)`| '(?P<name2>[^']+)')")),
    ("unknown-module", re.compile(
        r"unknown module prefix|bad import '(?P<name>[^']+)'|object file .* of module "
        r"(?P<name2>\S+) does not exist|unknown module '(?P<name3>[^']+)'")),
    ("instance", re.compile(r"failed to synthesize(?: instance of type class)?\s*(?P<name>.*)")),
    ("type-mismatch", re.compile(r"[Tt]ype mismatch|Application type mismatch")),
    ("unsolved-goals", re.compile(r"unsolved goals")),
    ("tactic-failed", re.compile(
        r"Tactic `[^`]+` failed|failed to apply|made no progress|linarith failed|omega could not|"
        r"did not find an occurrence|motive is not type correct")),
    ("field", re.compile(r"Invalid field|invalid field notation|Unknown constant .*\.")),
    ("syntax", re.compile(r"unexpected token|expected '")),
]
FIELDS = ["pr", "file", "line", "scope", "kind", "name", "known", "message"]


def load_codemod_tables() -> tuple[dict[str, str], dict[str, str]]:
    """The codemod's renames, and every name it reports with a hint: its hint table, the names it
    reports by name, and the report patterns (kept as patterns, under the key `"/regex/"`)."""
    spec = importlib.util.spec_from_file_location("codemod", HERE / "migrate-native-probability.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules["codemod"] = module
    spec.loader.exec_module(module)
    hints = dict(module.LEGACY_HINTS)
    hints.update(module.REPORT_NAMES)
    hints.update({f"/{regex}/": hint for regex, hint in module.LEGACY_TOKENS})
    return module.RENAMES, hints


def classify(message: str) -> tuple[str, str]:
    """The kind of an error message and the name it is about, when it names one."""
    for kind, pattern in KINDS:
        match = pattern.search(message)
        if match:
            groups = match.groupdict()
            name = next((value for value in groups.values() if value), "")
            return kind, name.strip()
    return "other", ""


def known(name: str, renames: dict[str, str], hints: dict[str, str]) -> str:
    """Whether the codemod has an entry for a name: `rename`, `hint`, or empty."""
    short = name.rsplit(".", 1)[-1]
    for table, label in ((renames, "rename"), (hints, "hint")):
        if name in table or short in table or any(key.endswith("." + short) for key in table):
            return label
    if any(key.startswith("/") and re.search(key[1:-1], name) for key in hints):
        return "hint"
    return ""


def errors(log: pathlib.Path) -> list[tuple[str, int, str]]:
    """The errors of a build log, with the first line of each message."""
    rows = []
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
        match = ERROR.match(line.strip())
        if match:
            rows.append((match["file"], int(match["line"]), match["msg"]))
    return rows


def lines(path: pathlib.Path) -> set[str]:
    return set(path.read_text().split()) if path.exists() else set()


def rows_for(pr_dir: pathlib.Path, renames, hints) -> list[dict[str, str]]:
    pr = pr_dir.name.removeprefix("pr-")
    pr_files, shared = lines(pr_dir / "pr-files.txt"), lines(pr_dir / "shared-files.txt")
    log = pr_dir / "build.log"
    rows = []
    for file, line, message in (errors(log) if log.exists() else []):
        scope = "shared" if file in shared else "pr" if file in pr_files else "other"
        kind, name = classify(message)
        rows.append({"pr": pr, "file": file, "line": str(line), "scope": scope, "kind": kind,
                     "name": name, "known": known(name, renames, hints) if kind == "unknown-name"
                     else "", "message": message[:200]})
    return rows


def summary(out: pathlib.Path, rows: list[dict[str, str]]) -> str:
    prs = sorted({path.name.removeprefix("pr-") for path in out.glob("pr-*")}, key=int)
    kinds = [kind for kind, _ in KINDS] + ["other"]
    text = ["# Migration dry run", "",
            "Errors of building each pull request's modules after the automatic merge and the "
            "codemod, by kind; `pr` counts files only the pull request touched, `shared` files "
            "this branch touched too, `other` files it did not touch.", "",
            "| PR | Status | Errors | pr | shared | other | " + " | ".join(kinds) + " |",
            "| --- | --- | ---: | ---: | ---: | ---: | " + " | ".join("---:" for _ in kinds) + " |"]
    for pr in prs:
        status_file = out / f"pr-{pr}" / "status.txt"
        status = status_file.read_text().strip() if status_file.exists() else "-"
        mine = [row for row in rows if row["pr"] == pr]
        scopes = collections.Counter(row["scope"] for row in mine)
        counts = collections.Counter(row["kind"] for row in mine)
        text.append(f"| #{pr} | {status} | {len(mine)} | {scopes['pr']} | {scopes['shared']} | "
                    f"{scopes['other']} | " + " | ".join(str(counts[kind]) for kind in kinds)
                    + " |")
    names = collections.Counter((row["name"], row["known"]) for row in rows
                                if row["kind"] == "unknown-name")
    text += ["", "## Unknown names", "",
             "`known` is `rename` or `hint` when the codemod has an entry for the name.", "",
             "| Name | Known | Errors | PRs |", "| --- | --- | ---: | --- |"]
    for (name, label), count in names.most_common(60):
        where = sorted({row["pr"] for row in rows if row["name"] == name}, key=int)
        text.append(f"| `{name}` | {label} | {count} | {', '.join('#' + p for p in where)} |")
    modules = collections.Counter(row["name"] for row in rows if row["kind"] == "unknown-module")
    if modules:
        text += ["", "## Unknown modules", "", "| Module | Errors |", "| --- | ---: |"]
        text += [f"| `{name or '?'}` | {count} |" for name, count in modules.most_common()]
    instances = collections.Counter(row["name"].split("\n")[0][:80] for row in rows
                                    if row["kind"] == "instance")
    if instances:
        text += ["", "## Instances that failed to synthesize", "", "| Class | Errors |",
                 "| --- | ---: |"]
        text += [f"| `{name or '?'}` | {count} |" for name, count in instances.most_common(30)]
    return "\n".join(text) + "\n"


def main(argv: list[str]) -> int:
    if len(argv) != 1:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    out = pathlib.Path(argv[0])
    renames, hints = load_codemod_tables()
    rows = []
    for pr_dir in sorted(out.glob("pr-*"), key=lambda path: int(path.name.removeprefix("pr-"))):
        rows += rows_for(pr_dir, renames, hints)
    with (out / "migration-dry-run.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    (out / "summary.md").write_text(summary(out, rows), encoding="utf-8")
    print(f"{len(rows)} errors over {len(list(out.glob('pr-*')))} pull requests: "
          f"{out / 'migration-dry-run.csv'}, {out / 'summary.md'}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
