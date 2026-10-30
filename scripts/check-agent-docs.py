#!/usr/bin/env python3
"""Validate first-party documentation references against the actual codebase.

Checks:
1. Local links, Markdown anchors and repository paths across all Markdown and Lean prose
2. Tactic coverage: every `macro "name" : tactic` in ProgramLogic/ is documented
3. Notation coverage: every `notation`/`scoped notation` in VCVio/ is documented
4. Dead references: no doc references to files that were deleted/renamed

Exit code 0 if all checks pass, 1 if any fail.
"""

import os
import re
import sys
from pathlib import Path

from doc_refs import local_references, source_files

REPO_ROOT = Path(__file__).resolve().parent.parent

DOC_FILES = source_files(REPO_ROOT, "*.md")

PROGRAM_LOGIC_DIR = REPO_ROOT / "VCVio" / "ProgramLogic"
VCVIO_DIR = REPO_ROOT / "VCVio"

TACTIC_MACRO_RE = re.compile(r'(?:macro|syntax)\s+"([\w\']+)".*:\s*tactic')

NOTATION_RE = re.compile(
    r'(?:scoped\s+)?notation(?:\s*:\s*\d+)?\s+'
    r'(?:\(name\s*:=\s*\w+\)\s*)?'
    r'"([^"]+)"'
)


def read_all_docs() -> str:
    """Read and concatenate all documentation files."""
    contents = []
    for f in DOC_FILES:
        if f.exists():
            contents.append(f.read_text())
    return "\n".join(contents)


def find_tactic_macros() -> set[str]:
    """Find all tactic macro declarations in ProgramLogic/."""
    macros = set()
    for lean_file in PROGRAM_LOGIC_DIR.rglob("*.lean"):
        text = lean_file.read_text()
        for m in TACTIC_MACRO_RE.finditer(text):
            macros.add(m.group(1))
    return macros


def check_tactic_coverage(doc_text: str) -> list[str]:
    """Check that all tactic macros are mentioned in docs."""
    errors = []
    macros = find_tactic_macros()
    for macro in sorted(macros):
        if macro not in doc_text:
            errors.append(
                f"Undocumented tactic: `{macro}` "
                f"(defined in VCVio/ProgramLogic/)"
            )
    return errors


def find_notations() -> list[tuple[str, str]]:
    """Find notation declarations in VCVio/."""
    notations = []
    for lean_file in VCVIO_DIR.rglob("*.lean"):
        text = lean_file.read_text()
        rel_path = lean_file.relative_to(REPO_ROOT)
        for m in NOTATION_RE.finditer(text):
            notations.append((m.group(1).strip(), str(rel_path)))
    return notations


def check_notation_coverage(doc_text: str) -> list[str]:
    """Check that notations are mentioned in docs."""
    errors = []
    notations = find_notations()
    for symbol, source_file in notations:
        if len(symbol) < 2:
            continue
        if symbol not in doc_text:
            errors.append(
                f"Undocumented notation: `{symbol}` "
                f"(defined in {source_file})"
            )
    return errors


def main():
    if not DOC_FILES:
        print("ERROR: No documentation files found")
        sys.exit(1)

    doc_text = read_all_docs()
    all_errors: list[str] = []

    sources = source_files(REPO_ROOT, "*.md", "*.lean")
    print(f"Checking links and file references in {len(sources)} Markdown and Lean files...")
    for path in sources:
        all_errors.extend(local_references(REPO_ROOT, path))

    print("Checking tactic coverage...")
    all_errors.extend(check_tactic_coverage(doc_text))

    print("Checking notation coverage...")
    all_errors.extend(check_notation_coverage(doc_text))

    if all_errors:
        print(f"\n{len(all_errors)} issue(s) found:\n")
        for err in all_errors:
            print(f"  - {err}")
        sys.exit(1)
    else:
        print("\nAll documentation checks passed.")
        sys.exit(0)


if __name__ == "__main__":
    main()
