#!/usr/bin/env python3
"""Extract structured documentation fragments from the VCVio codebase.

Generates markdown tables for:
1. Tactic declarations (from ProgramLogic/)
2. Notation declarations (from VCVio/)
3. Simp lemma catalog (from EvalDist/Monad/)
4. Registered `@[spec]` rules of the program logic, by namespace

Usage:
  python scripts/extract-doc-fragments.py           # print fragments
  python scripts/extract-doc-fragments.py --write   # splice the fragments into docs/agents
  python scripts/extract-doc-fragments.py --check    # check if docs are up to date
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

PROGRAM_LOGIC_DIR = REPO_ROOT / "VCVio" / "ProgramLogic"
VCVIO_DIR = REPO_ROOT / "VCVio"
EVALDIST_MONAD_DIR = REPO_ROOT / "VCVio" / "EvalDist" / "Monad"

TACTIC_MACRO_RE = re.compile(r'(?:macro|syntax)\s+"([\w\']+)".*:\s*tactic')

NOTATION_RE = re.compile(
    r'(?:scoped\s+)?notation(?:\s*:\s*\d+)?\s+'
    r'(?:\(name\s*:=\s*(\w+)\)\s*)?'
    r'"([^"]+)"'
)

SIMP_LEMMA_RE = re.compile(
    r'@\[(?:[^\]]*\b(?:simp|grind)\b[^\]]*)\]\s*'
    r'(?:protected\s+)?(?:theorem|lemma|def)\s+(\w+)'
)

SPEC_RULE_DIRS = [
    PROGRAM_LOGIC_DIR,
    REPO_ROOT / "ToMathlib" / "Control" / "WriterT",
    REPO_ROOT / "ToMathlib" / "Control" / "Monad" / "Fold",
]
SPEC_ATTR_RE = re.compile(
    r'@\[([^\]]*)\]\s*(?:protected\s+)?(?:theorem|lemma)\s+([\w.\'!?₀-₉ₐ-ₜᵢ-ᵪ]+)'
)
SPEC_TOKEN_RE = re.compile(r'^spec(?:\s+(?:high|low|mid)(?:\s*[+-]\s*\d+)?)?$')
SPEC_ATTRIBUTE_CMD_RE = re.compile(r'^attribute\s+\[(spec[^\]]*)\]\s+([\w.\'!?₀-₉ₐ-ₜᵢ-ᵪ]+)', re.M)
NAMESPACE_RE = re.compile(r'^(namespace|end)\s+([\w.\'₀-₉ₐ-ₜᵢ-ᵪ]+)\s*$', re.M)
BEGIN_AUTO_RE = re.compile(r'<!--\s*BEGIN AUTO:(\w+)\s*-->')
END_AUTO_RE = re.compile(r'<!--\s*END AUTO:(\w+)\s*-->')


def extract_tactics() -> list[tuple[str, str]]:
    """Extract tactic macro names and source files."""
    tactics = []
    for lean_file in sorted(PROGRAM_LOGIC_DIR.rglob("*.lean")):
        text = lean_file.read_text()
        rel_path = lean_file.relative_to(REPO_ROOT)
        for m in TACTIC_MACRO_RE.finditer(text):
            line_num = text[:m.start()].count('\n') + 1
            tactics.append((m.group(1), f"{rel_path}:{line_num}"))
    return tactics


def extract_notations() -> list[tuple[str, str, str]]:
    """Extract notation symbols, names, and source files."""
    notations = []
    for lean_file in sorted(VCVIO_DIR.rglob("*.lean")):
        text = lean_file.read_text()
        rel_path = lean_file.relative_to(REPO_ROOT)
        for m in NOTATION_RE.finditer(text):
            name = m.group(1) or ""
            symbol = m.group(2).strip()
            if len(symbol) < 2:
                continue
            notations.append((symbol, name, str(rel_path)))
    return notations


def extract_simp_lemmas() -> list[tuple[str, str]]:
    """Extract @[simp]/@[grind] lemma names from EvalDist/Monad/."""
    lemmas = []
    for lean_file in sorted(EVALDIST_MONAD_DIR.rglob("*.lean")):
        text = lean_file.read_text()
        rel_path = lean_file.relative_to(REPO_ROOT)
        for m in SIMP_LEMMA_RE.finditer(text):
            lemmas.append((m.group(1), str(rel_path)))
    return lemmas


def format_tactic_table(tactics: list[tuple[str, str]]) -> str:
    lines = ["| Tactic | Defined in |", "|--------|------------|"]
    for name, source in tactics:
        lines.append(f"| `{name}` | `{source}` |")
    return "\n".join(lines)


def format_notation_table(notations: list[tuple[str, str, str]]) -> str:
    lines = ["| Notation | Name | Defined in |",
             "|----------|------|------------|"]
    for symbol, name, source in notations:
        name_col = f"`{name}`" if name else "—"
        lines.append(f"| `{symbol}` | {name_col} | `{source}` |")
    return "\n".join(lines)


def namespace_at(text: str, position: int) -> str:
    """The namespace open at `position`, from the `namespace`/`end` commands before it."""
    stack: list[str] = []
    for m in NAMESPACE_RE.finditer(text, 0, position):
        if m.group(1) == "namespace":
            stack.append(m.group(2))
        elif stack and stack[-1] == m.group(2):
            stack.pop()
    return ".".join(stack)


def extract_spec_rules() -> list[tuple[str, str, str, str]]:
    """Registered `@[spec]` rules: (namespace, full name, attribute, source file)."""
    rules = []
    for base in SPEC_RULE_DIRS:
        for lean_file in sorted(base.rglob("*.lean")):
            text = lean_file.read_text()
            rel_path = str(lean_file.relative_to(REPO_ROOT))
            for m in SPEC_ATTR_RE.finditer(text):
                tokens = [t.strip() for t in m.group(1).split(",")]
                attr = next((t for t in tokens if SPEC_TOKEN_RE.match(t)), None)
                if attr is None:
                    continue
                ns = namespace_at(text, m.start())
                raw = m.group(2)
                name = raw.removeprefix("_root_.") if raw.startswith("_root_.") else (
                    f"{ns}.{raw}" if ns else raw)
                rules.append((ns, name, attr, rel_path))
            for m in SPEC_ATTRIBUTE_CMD_RE.finditer(text):
                ns = namespace_at(text, m.start())
                rules.append((ns, m.group(2), m.group(1), rel_path))
    return sorted(set(rules))


def format_spec_rules(rules: list[tuple[str, str, str, str]]) -> str:
    lines = ["| Namespace | Rule | Attribute | Defined in |",
             "|-----------|------|-----------|------------|"]
    for _, name, attr, source in rules:
        ns = name.rpartition(".")[0]
        lines.append(f"| `{ns or '(root)'}` | `{name}` | `@[{attr}]` | `{source}` |")
    return "\n".join(lines)


def format_simp_catalog(lemmas: list[tuple[str, str]]) -> str:
    lines = ["| Lemma | Defined in |", "|-------|------------|"]
    for name, source in lemmas:
        lines.append(f"| `{name}` | `{source}` |")
    return "\n".join(lines)


def splice_auto_sections(filepath: Path, fragments: dict[str, str]) -> str | None:
    """Replace AUTO sections in a file. Returns new content if changed, None otherwise."""
    if not filepath.exists():
        return None

    text = filepath.read_text()
    changed = False

    for section_name, new_content in fragments.items():
        begin_pattern = f"<!-- BEGIN AUTO:{section_name} -->"
        end_pattern = f"<!-- END AUTO:{section_name} -->"

        begin_idx = text.find(begin_pattern)
        end_idx = text.find(end_pattern)

        if begin_idx == -1 or end_idx == -1:
            continue

        before = text[:begin_idx + len(begin_pattern)]
        after = text[end_idx:]
        new_text = f"{before}\n{new_content}\n{after}"

        if new_text != text:
            changed = True
            text = new_text

    return text if changed else None


def main():
    check_mode = "--check" in sys.argv
    write_mode = "--write" in sys.argv

    tactics = extract_tactics()
    notations = extract_notations()
    simp_lemmas = extract_simp_lemmas()
    spec_rules = extract_spec_rules()

    fragments = {
        "tacticTable": format_tactic_table(tactics),
        "notationTable": format_notation_table(notations),
        "simpCatalog": format_simp_catalog(simp_lemmas),
        "specRules": format_spec_rules(spec_rules),
    }

    if write_mode:
        docs_dir = REPO_ROOT / "docs" / "agents"
        for doc_file in sorted(docs_dir.glob("*.md")):
            new_content = splice_auto_sections(doc_file, fragments)
            if new_content is not None:
                doc_file.write_text(new_content)
                print(f"updated {doc_file.relative_to(REPO_ROOT)}")
        return

    if not check_mode:
        print("## Tactic Declarations\n")
        print(fragments["tacticTable"])
        print(f"\n({len(tactics)} tactics found)\n")

        print("## Notation Declarations\n")
        print(fragments["notationTable"])
        print(f"\n({len(notations)} notations found)\n")

        print("## Simp/Grind Lemmas (EvalDist/Monad/)\n")
        print(fragments["simpCatalog"])
        print(f"\n({len(simp_lemmas)} lemmas found)\n")

        print("## Registered `@[spec]` rules\n")
        print(fragments["specRules"])
        print(f"\n({len(spec_rules)} rules found)\n")
        return

    docs_dir = REPO_ROOT / "docs" / "agents"
    drifted = []

    for doc_file in sorted(docs_dir.glob("*.md")):
        new_content = splice_auto_sections(doc_file, fragments)
        if new_content is not None:
            drifted.append(doc_file.relative_to(REPO_ROOT))

    if drifted:
        print(f"Auto-generated sections are stale in {len(drifted)} file(s):")
        for f in drifted:
            print(f"  - {f}")
        print("\nRun `python scripts/extract-doc-fragments.py` to see current values.")
        sys.exit(1)
    else:
        print("All auto-generated doc sections are up to date.")
        sys.exit(0)


if __name__ == "__main__":
    main()
