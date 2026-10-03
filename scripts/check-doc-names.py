#!/usr/bin/env python3
"""Check the declaration names the documentation cites.

Two checks over the agent guides (`docs/agents/*.md`, `AGENTS.md`, `CONTRIBUTING.md`,
`README.md`), the design notes (`docs/design/*.md`) and the reading documents
(`docs/reading/*.md`), the first also over the docstrings and comments of the Lean libraries:

1. Retired names (needs no build). A name the downstream codemod renames or removes
   (`scripts/migrate-native-probability.py`: `RENAMES`, `MODULES`, `LEGACY_HINTS`,
   `LEGACY_TOKENS`), or a retired label of a reading of `OracleComp` ("structural reading",
   "angelic triple", "structural support", "structurally reachable"), may appear only in the
   migration guide, in a
   document whose status line calls it historical (a record of past work), and on a line that
   says it is retired (one mentioning the migration guide, the codemod, or a legacy, retired or
   removed name). A label is also allowed on a line that mentions PolyFun, whose own API names
   its readings demonic and angelic, and inside a code span. In Lean sources, the check reads
   only docstrings and comments.
2. Resolution (`--resolve`, after `lake build`). Every inline code span that looks like a
   declaration name — an identifier path with a dot, an underscore or a capital letter — must
   resolve in the compiled environment of the proof libraries: `lake exe docnames` accepts a
   declaration, a namespace, a module, an option, a simp set, an attribute, a parser token or a
   suffix of a declaration name (see `scripts/DocNames.lean`); a Lake target or keyword
   (`lean_lib`, `extern_lib`) resolves too. The codemod's own targets (`RENAMES` and `MODULES`
   values, the names its hints cite) are resolved with the guides. Not resolved: the design
   notes, which describe work that may not exist yet; the migration guide's retired names (every
   table column but the ones whose header says replacement, current or fix, and a name followed
   by `→`) and a retired name on a line that says it is retired; the interop guide, whose library is not a default build target;
   name fragments (`_of_support`, `prEvent_`) and tokens of fewer than three characters.

`scripts/doc_names_allowlist.txt` lists the tokens that may stay unresolved, one per line with
an optional `# reason`; an entry that resolves, or is no longer cited, is obsolete and fails the
check, so the list only shrinks. `--emit FILE` writes the tokens for the resolver and exits.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CODEMOD = REPO_ROOT / "scripts" / "migrate-native-probability.py"
ALLOWLIST = REPO_ROOT / "scripts" / "doc_names_allowlist.txt"
MIGRATION_GUIDE = REPO_ROOT / "docs" / "agents" / "probability-migration.md"
DESIGN_DIR = REPO_ROOT / "docs" / "design"

IDENT = r"[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪ]*"
TOKEN_RE = re.compile(rf"^\.?{IDENT}(?:\.{IDENT})*$")
CODE_SPAN_RE = re.compile(r"`([^`\n]+)`")
FENCE_RE = re.compile(r"^\s*(```|~~~)")
FILE_SUFFIXES = (".lean", ".md", ".py", ".sh", ".json", ".toml", ".yml", ".yaml", ".tsv", ".txt",
                 ".csv", ".c", ".h")
SORTS = {"Prop", "Type", "Sort"}
LAKEFILE = REPO_ROOT / "lakefile.lean"
LAKE_DSL = {"lean_lib", "lean_exe", "extern_lib", "input_file", "input_dir", "leanOptions"}
TABLE_SEPARATOR_RE = re.compile(r"^\s*\|?\s*:?-{2,}")
CURRENT_HEADER_RE = re.compile(r"replacement|current|fix|instead|\bnow\b", re.I)
ARROW_AFTER_RE = re.compile(r"^\s*\)?\s*(?:→|->)")
LAKE_TARGET_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:lean_lib|lean_exe|extern_lib|input_file|input_dir)\s+(\S+)", re.M)
RESOLUTION_EXEMPT = {REPO_ROOT / "docs" / "agents" / "interop.md"}
RETIRED_CONTEXT_RE = re.compile(r"migration guide|codemod|legacy|retired|removed", re.I)
READING_DIR = REPO_ROOT / "docs" / "reading"
STATUS_RE = re.compile(r"^\W*status\W", re.I)
RETIRED_LABEL_RE = re.compile(
    r"\b(?:structural|angelic|demonic)\s+(?:readings?|interpretations?|triples?|WP|"
    r"weakest\s+preconditions?)\b|\bstructural\s+support\b|\bstructurally\s+"
    r"(?:reachable|possible)\b", re.I)
LEAN_ROOTS = ("ToMathlib/", "VCVio/", "VCVioCslib/", "LatticeCrypto/", "HashSig/", "Examples/",
              "Extern/", "VCVioWidgets/", "VCVioTest/", "LatticeCryptoTest/", "HashSigTest/")


def default_docs() -> tuple[list[Path], list[Path]]:
    """The documents of the two checks: (retired-name scan, resolution)."""
    guides = sorted((REPO_ROOT / "docs" / "agents").glob("*.md")) + [
        REPO_ROOT / "AGENTS.md", REPO_ROOT / "CONTRIBUTING.md", REPO_ROOT / "README.md"]
    guides = [doc for doc in guides if doc.is_file()]
    designs = sorted(DESIGN_DIR.glob("*.md"))
    readings = sorted(READING_DIR.glob("*.md"))
    return guides + designs + readings, guides


def historical(text: str) -> bool:
    """Whether a document's status line, among its first fifteen lines, calls it historical."""
    for line in text.splitlines()[:15]:
        if STATUS_RE.match(line):
            return "historical" in line.lower()
    return False


def lean_sources() -> list[Path]:
    """The tracked Lean sources of the libraries and test libraries."""
    listed = subprocess.run(["git", "ls-files", "*.lean"], cwd=REPO_ROOT, capture_output=True,
                            text=True, encoding="utf-8").stdout.split()
    return [REPO_ROOT / name for name in listed if name.startswith(LEAN_ROOTS)]


def lean_prose(text: str):
    """(line number, text) of the docstring and comment parts of each line of a Lean source."""
    depth = 0
    for number, line in enumerate(text.splitlines(), 1):
        prose = []
        j = 0
        while j < len(line):
            if line.startswith("/-", j):
                depth += 1
                j += 2
            elif depth and line.startswith("-/", j):
                depth -= 1
                j += 2
            elif not depth and line.startswith("--", j):
                prose.append(line[j:])
                break
            elif not depth and line[j] == '"':
                j += 1
                while j < len(line) and line[j] != '"':
                    j += 2 if line[j] == "\\" else 1
                j += 1
            else:
                if depth:
                    prose.append(line[j])
                j += 1
        if prose:
            yield number, "".join(prose)


def declaration_like(token: str) -> bool:
    if not TOKEN_RE.match(token) or "/" in token or token.endswith(FILE_SUFFIXES):
        return False
    if token in SORTS or len(token) < 3 or token.startswith("_") or token.endswith("_"):
        return False
    return "." in token or "_" in token or any(c.isupper() for c in token)


def lake_targets() -> set[str]:
    if not LAKEFILE.is_file():
        return set(LAKE_DSL)
    return set(LAKE_TARGET_RE.findall(LAKEFILE.read_text(encoding="utf-8"))) | LAKE_DSL


def table_cells(line: str) -> list[str]:
    """The cells of a Markdown table row, or the whole line as one cell."""
    if not line.lstrip().startswith("|"):
        return [line]
    return re.split(r"(?<!\\)\|", line.strip().strip("|"))


def code_spans(text: str):
    """(line number, span, line) for every inline code span outside fenced blocks."""
    fence = None
    for number, line in enumerate(text.splitlines(), 1):
        opened = FENCE_RE.match(line)
        if opened:
            if fence is None:
                fence = opened.group(1)
            elif opened.group(1) == fence:
                fence = None
            continue
        if fence is not None:
            continue
        for span in CODE_SPAN_RE.findall(line):
            yield number, span.strip(), line


def guide_spans(text: str):
    """The spans of the migration guide that name current declarations: in a table with a
    replacement, current or fix column, only those columns count, and a span followed by `→` is
    the retired side of a rename."""
    lines = text.splitlines()
    fence = None
    current_columns: set[int] = set()
    for index, line in enumerate(lines):
        number = index + 1
        opened = FENCE_RE.match(line)
        if opened:
            if fence is None:
                fence = opened.group(1)
            elif opened.group(1) == fence:
                fence = None
            continue
        if fence is not None:
            continue
        next_line = lines[index + 1] if index + 1 < len(lines) else ""
        if line.lstrip().startswith("|"):
            if TABLE_SEPARATOR_RE.match(line):
                continue
            cells = table_cells(line)
            if TABLE_SEPARATOR_RE.match(next_line):
                current_columns = {k for k, cell in enumerate(cells)
                                   if CURRENT_HEADER_RE.search(cell)}
                continue
            segments = [(cell, "") for k, cell in enumerate(cells)
                        if not current_columns or k in current_columns]
        else:
            current_columns = set()
            segments = [(line, next_line)]
        for segment, continuation in segments:
            for match in CODE_SPAN_RE.finditer(segment):
                rest = segment[match.end():]
                following = rest if rest.strip() else rest + " " + continuation
                if ARROW_AFTER_RE.match(following):
                    continue
                yield number, match.group(1).strip(), line


def collect_tokens(docs: list[Path], patterns) -> dict[str, list[tuple[Path, int]]]:
    """Resolution sites by token; retired names in their place are not sites."""
    sites: dict[str, list[tuple[Path, int]]] = defaultdict(list)
    targets = lake_targets()
    for doc in docs:
        if doc in RESOLUTION_EXEMPT:
            continue
        text = doc.read_text(encoding="utf-8")
        spans = guide_spans(text) if doc == MIGRATION_GUIDE else code_spans(text)
        for number, span, line in spans:
            if not declaration_like(span) or span in targets:
                continue
            if doc == MIGRATION_GUIDE or RETIRED_CONTEXT_RE.search(line):
                if any(pattern.search(span) for pattern, _ in patterns):
                    continue
            sites[span].append((doc, number))
    return sites


def codemod_targets(sites: dict[str, list[tuple[Path, int]]]) -> None:
    """The codemod's own targets: `RENAMES` and `MODULES` values and the names its hints cite."""
    spec = importlib.util.spec_from_file_location("codemod", CODEMOD)
    codemod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(codemod)
    lines = CODEMOD.read_text(encoding="utf-8").splitlines()

    def add(name: str) -> None:
        if declaration_like(name):
            number = next((k for k, text in enumerate(lines, 1) if name in text), 0)
            sites[name].append((CODEMOD, number))

    for name in codemod.RENAMES.values():
        add(name)
    for modules in codemod.MODULES.values():
        for module in modules:
            add(module)
    for hint in list(codemod.LEGACY_HINTS.values()) + list(codemod.REPORT_NAMES.values()):
        for span in CODE_SPAN_RE.findall(hint):
            add(span.strip())


def retired_patterns() -> list[tuple[re.Pattern[str], str]]:
    spec = importlib.util.spec_from_file_location("codemod", CODEMOD)
    codemod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(codemod)
    patterns = []
    names = set(codemod.RENAMES) | set(codemod.MODULES) | set(codemod.LEGACY_HINTS)
    for regex, _ in codemod.CLASS_BINDERS:  # the retired answer-measure classes
        names |= set(re.findall(r"\b(Is[A-Za-z]*Spec)\b", regex.pattern))
    for name in sorted(names):
        patterns.append((re.compile(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'.])"), name))
    for pattern, _ in codemod.LEGACY_TOKENS:
        if "\\s" not in pattern and "\\(" not in pattern:  # identifier-level patterns only
            patterns.append((re.compile(pattern), pattern))
    return patterns


def retired_in(line: str, patterns) -> str | None:
    """The retired name or reading label a line uses, if it does not say it is retired."""
    if RETIRED_CONTEXT_RE.search(line):
        return None
    for pattern, name in patterns:
        if pattern.search(line):
            return f"retired name `{name}`"
    if "PolyFun" not in line:
        label = RETIRED_LABEL_RE.search(CODE_SPAN_RE.sub("", line))
        if label:
            return f"retired reading label \"{label.group(0)}\""
    return None


def check_retired(docs: list[Path], patterns) -> list[str]:
    failures = []
    for doc in docs:
        if doc == MIGRATION_GUIDE:
            continue
        text = doc.read_text(encoding="utf-8")
        lines = (lean_prose(text) if doc.suffix == ".lean"
                 else [] if historical(text) else enumerate(text.splitlines(), 1))
        for number, line in lines:
            found = retired_in(line, patterns)
            if found:
                failures.append(f"{rel(doc)}:{number}: {found} (see the migration guide)")
    return failures


def read_allowlist(path: Path) -> dict[str, str]:
    entries: dict[str, str] = {}
    if not path.is_file():
        return entries
    for line in path.read_text(encoding="utf-8").splitlines():
        body = line.split("#", 1)[0].strip()
        if body:
            entries[body] = line.strip()
    return entries


def resolve(tokens: list[str]) -> tuple[dict[str, str], int]:
    """Unresolved tokens with their suggestions, by `lake exe docnames`; the second component is
    its exit status."""
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False,
                                     encoding="utf-8") as handle:
        json.dump({"names": tokens}, handle, ensure_ascii=False)
        names_path = handle.name
    try:
        result = subprocess.run(["lake", "exe", "docnames", names_path], cwd=REPO_ROOT,
                                capture_output=True, text=True, encoding="utf-8")
    finally:
        Path(names_path).unlink(missing_ok=True)
    if result.stderr:
        print(result.stderr.rstrip(), file=sys.stderr)
    if result.returncode != 0:
        print(result.stdout.rstrip())
        return {}, result.returncode
    unresolved: dict[str, str] = {}
    for line in result.stdout.splitlines():
        if line.startswith("UNRESOLVED\t"):
            _, token, hints = (line.split("\t", 2) + [""])[:3]
            unresolved[token] = hints
    return unresolved, 0


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("files", nargs="*", type=Path,
                        help="documents or Lean sources to check (default: the guides, design "
                             "notes, reading documents and library sources)")
    parser.add_argument("--resolve", action="store_true",
                        help="also resolve the tokens with `lake exe docnames`")
    parser.add_argument("--emit", type=Path, metavar="FILE",
                        help="write the tokens as the resolver's input and exit")
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST,
                        help="tokens that may stay unresolved")
    args = parser.parse_args()
    if args.files:
        retired_docs = [doc.resolve() for doc in args.files]
        resolve_docs = [doc for doc in retired_docs if doc.suffix != ".lean"]
    else:
        retired_docs, resolve_docs = default_docs()
        retired_docs = retired_docs + lean_sources()
    patterns = retired_patterns()
    sites = collect_tokens(resolve_docs, patterns)
    if not args.files:
        codemod_targets(sites)
    tokens = sorted(sites)
    if args.emit:
        args.emit.write_text(json.dumps({"names": tokens}, ensure_ascii=False, indent=1) + "\n",
                             encoding="utf-8")
        print(f"Documentation names: wrote {len(tokens)} tokens to {args.emit}")
        return 0
    failures = check_retired(retired_docs, patterns)
    resolved_count = 0
    if args.resolve:
        unresolved, status = resolve(tokens)
        if status != 0:
            print(f"Documentation names: the resolver failed with status {status}")
            return 2
        allowlist = read_allowlist(args.allowlist)
        for token in sorted(set(unresolved) - set(allowlist)):
            hint = f" (constants named like it: {unresolved[token]})" if unresolved[token] else ""
            for doc, number in sites[token]:
                failures.append(f"{rel(doc)}:{number}: `{token}` does not resolve to a "
                                f"declaration, namespace, module, option, simp set, attribute "
                                f"or parser token{hint}")
        for token in sorted(set(allowlist) - set(unresolved)):
            failures.append(f"{rel(args.allowlist)}: obsolete allowlist entry `{token}` "
                            f"({'resolves' if token in sites else 'no longer cited'})")
        resolved_count = len(tokens) - len(unresolved)
    for failure in failures:
        print(failure)
    scope = f"{len(tokens)} tokens in {len(resolve_docs)} documents"
    if failures:
        print(f"Documentation names: {len(failures)} problems ({scope})")
        return 1
    detail = f"{resolved_count} resolved, " if args.resolve else "retired names only, "
    print(f"Documentation names: OK ({detail}{scope})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
