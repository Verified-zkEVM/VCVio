"""Repository documentation inventory and local-reference validation.

Works without Lean or optional dependencies. External package paths, external URLs and historical
bare paths are outside the local-reference check.
"""

from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit


def source_files(root: Path, *patterns: str) -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", *patterns],
        cwd=root, text=True, capture_output=True, check=True)
    return sorted({root / p for p in result.stdout.split("\0")
                   if p and not p.startswith("third_party/") and not (root / p).is_symlink()
                   and (root / p).is_file()})


def prose(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    if path.suffix != ".lean":
        return text
    # Preserve source line numbers while masking Lean code, strings and nested delimiters.
    out = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        if not depth and quoted:
            if text[i] == "\\":
                out.extend("\n" if c == "\n" else " " for c in text[i:i + 2])
                i += 2
                continue
            if text[i] == '"':
                quoted = False
        elif pair == "/-":
            depth += 1
            out.extend("  ")
            i += 2
            continue
        elif depth and pair == "-/":
            depth -= 1
            out.extend("  ")
            i += 2
            continue
        elif not depth and pair == "--":
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(text[i:end])
            i = end
            continue
        elif not depth and text[i] == '"':
            quoted = True
        out.append(text[i] if depth or text[i] == "\n" else " ")
        i += 1
    return "".join(out)


def anchors(text: str) -> set[str]:
    found = set(re.findall(r'<(?:a|h[1-6])\b[^>]*(?:id|name)=["\']([^"\']+)', text))
    counts = {}
    fenced = False
    for line in text.splitlines():
        if re.match(r"\s*(```|~~~)", line):
            fenced = not fenced
        if fenced:
            continue
        match = re.match(r"^#{1,6}\s+(.+?)(?:\s+#+)?$", line)
        if match:
            title = re.sub(r"<[^>]+>", "", match[1]).lower()
            slug = re.sub(r"[^\w\- ]", "", title).replace(" ", "-")
            n = counts.get(slug, 0)
            counts[slug] = n + 1
            found.add(slug if n == 0 else f"{slug}-{n}")
    return found


def historical(text: str) -> bool:
    return any(re.match(r"^\W*status\W", line, re.I) and "historical" in line.lower()
               for line in text.splitlines()[:15])


def local_references(root: Path, path: Path) -> list[str]:
    text = prose(path)
    errors = []
    # Links, including reference-style definitions. A parenthesized title is not a path.
    links = list(re.finditer(r"\]\(\s*(<[^>]+>|[^\s)]+)", text))
    links += list(re.finditer(r"(?m)^\s*\[[^\]]+\]:\s*(<[^>]+>|\S+)", text))
    for match in links:
        raw = match[1].strip("<>")
        url = urlsplit(raw)
        if url.scheme or url.netloc or raw.startswith("/"):
            continue
        target = (path.parent / unquote(url.path)).resolve() if url.path else path
        line = text.count("\n", 0, match.start()) + 1
        if not target.exists():
            errors.append(f"{path.relative_to(root)}:{line}: missing link target {raw}")
        elif url.fragment and target.suffix == ".md":
            if unquote(url.fragment) not in anchors(target.read_text(encoding="utf-8")):
                errors.append(f"{path.relative_to(root)}:{line}: missing anchor {raw}")
    if historical(text):
        return errors
    # Bare repository-root paths in prose and snippets, including every library and script root.
    roots = {p.name for p in root.iterdir() if p.is_dir() and not p.name.startswith(".")}
    pattern = r"(?<![\w/])(?:" + "|".join(sorted(map(re.escape, roots))) + r")/" \
        r"[\w/.-]+\.(?:lean|md|json|toml|py|sh|tsv|ya?ml)(?![\w.])"
    for match in re.finditer(pattern, text):
        # Markdown destinations were already resolved relative to the document above.
        if any(link.start() <= match.start() < link.end() for link in links):
            continue
        line = text.count("\n", 0, match.start()) + 1
        content = text.splitlines()[line - 1]
        # URLs are immutable source citations, not paths in the adjacent checkout.
        if re.search(r"https?://\S*" + re.escape(match[0]), content):
            continue
        if re.search(r"\b(?:historical|retired|removed|planned|proposed|branch-only)\b", content, re.I):
            continue
        if not (root / match[0]).is_file():
            errors.append(f"{path.relative_to(root)}:{line}: missing file {match[0]}")
    return errors
