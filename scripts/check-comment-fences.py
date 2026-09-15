#!/usr/bin/env python3
"""Keep a top-level block comment from hiding the declaration that follows it.

A declaration written after the `-/` of the comment that documents it parses, builds and
runs, and is invisible to a reader scanning the left margin for declarations. That is not
hypothetical: a docstring reflow in `lakefile.lean` once produced

    at least one. -/ lean_exe slhdsa_limited_profile_tests where root :=

and every gate in the repository passed it. Lean's own `linter.style.whitespace`, which
Mathlib's standard set enables here and which rejects a command that does not start at the
beginning of a line, does not see it either: a doc comment is part of the command it
documents, so the command *does* start at the beginning of the line — the line where the
comment opened, several lines earlier.

The rule, in one sentence: *a block comment that begins its line, or that spans more than
one line, must be the last thing on the line where it ends.* Both halves say the same
thing — such a comment is a top-level comment, and code after it is a declaration that no
longer starts its own line. An inline annotation that opens and closes inside a line of
code (`f (x /- the seed -/) y`) is untouched: it hides nothing, because the code around it
is on the line the reader is already reading.

Scope: every Lean source the repository tracks, plus untracked ones that are not ignored,
and `third_party/` excluded as vendored. `lakefile.lean` is in scope and is the file the
rule was written for; it is also outside `scripts/lint.py`'s style pass, which covers the
library and test roots only.

What this cannot catch: a single-line comment that starts mid-line and is followed by a
declaration (`def a := 1 /- note -/ def b := 2`), which is legal and hides `b` just as
well; and anything a comment does not mediate, such as two declarations written on one
line. Neither occurs in the tracked sources today. Widening to "nothing may ever follow
`-/`" would cover the first and would also reject inline annotations, which have no defect
behind them.

Usage:
    scripts/check-comment-fences.py            # every tracked/untracked Lean source
    scripts/check-comment-fences.py PATH...    # those files, or every .lean under them
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

EXCLUDED_TOP_LEVEL = {"third_party"}


def block_comments(source: str) -> list[tuple[int, int, int, str]]:
    """Every block comment, as `(open line, open column, close line, text after `-/`)`.

    Line and column numbers are 1- and 0-based. Lean's block comments nest and ignore
    string syntax inside themselves, so only `/-` and `-/` are tracked once one is open;
    outside them, string, raw-string and character literals are skipped whole so their
    contents cannot be read as delimiters. A comment left unterminated at end of file is
    reported as closing there, which is what Lean would report too.
    """
    result: list[tuple[int, int, int, str]] = []
    index, size, line = 0, len(source), 1
    line_start = 0
    while index < size:
        character = source[index]
        if character == "\n":
            line += 1
            index += 1
            line_start = index
            continue
        if source.startswith("--", index):
            newline = source.find("\n", index)
            index = size if newline < 0 else newline
            continue
        if source.startswith("/-", index):
            open_line, open_column = line, index - line_start
            depth, cursor = 0, index
            while cursor < size:
                if source.startswith("/-", cursor):
                    depth += 1
                    cursor += 2
                elif source.startswith("-/", cursor):
                    depth -= 1
                    cursor += 2
                    if depth == 0:
                        break
                else:
                    if source[cursor] == "\n":
                        line += 1
                        line_start = cursor + 1
                    cursor += 1
            newline = source.find("\n", cursor)
            trailing = source[cursor:size if newline < 0 else newline]
            result.append((open_line, open_column, line, trailing))
            index = cursor
            continue
        if character == "r" and source.startswith('"', index + 1):
            index = skip_raw_string(source, index + 1, 0)
            continue
        if character == "r" and source.startswith("#", index + 1):
            hashes = 0
            while source.startswith("#", index + 1 + hashes):
                hashes += 1
            if source.startswith('"', index + 1 + hashes):
                index = skip_raw_string(source, index + 1 + hashes, hashes)
                continue
        if character == '"':
            index, line, line_start = skip_string(source, index, line, line_start)
            continue
        if character == "'" and not is_identifier_tail(source, index - 1):
            skipped = skip_character_literal(source, index)
            if skipped is not None:
                index = skipped
                continue
        if character == "«":
            closing = source.find("»", index)
            index = size if closing < 0 else closing + 1
            continue
        index += 1
    return result


def is_identifier_tail(source: str, index: int) -> bool:
    """Whether `source[index]` can continue a Lean identifier, so a following `'` is a
    prime rather than the opening of a character literal."""
    if index < 0:
        return False
    return source[index].isalnum() or source[index] in "_'!?"


def skip_character_literal(source: str, index: int) -> int | None:
    """The index just past the character literal starting at `index`, or `None` if what is
    there is not one (a stray `'` is then ordinary text)."""
    cursor = index + 1
    if cursor >= len(source):
        return None
    if source[cursor] == "\\":
        cursor += 1
        while cursor < len(source) and source[cursor] != "'":
            cursor += 1
        return cursor + 1 if cursor < len(source) else None
    if source.startswith("'", cursor + 1):
        return cursor + 2
    return None


def skip_string(source: str, index: int, line: int, line_start: int) -> tuple[int, int, int]:
    """The index just past the string literal starting at `index`, with the line counter
    advanced. A backslash escapes the next character, including the newline of a gap
    escape — not counting that newline is how a naive scanner drifts off by a line."""
    cursor = index + 1
    while cursor < len(source):
        if source[cursor] == "\\":
            if cursor + 1 < len(source) and source[cursor + 1] == "\n":
                line += 1
                line_start = cursor + 2
            cursor += 2
            continue
        if source[cursor] == '"':
            return cursor + 1, line, line_start
        if source[cursor] == "\n":
            line += 1
            line_start = cursor + 1
        cursor += 1
    return cursor, line, line_start


def skip_raw_string(source: str, index: int, hashes: int) -> int:
    """The index just past the raw string literal whose opening quote is at `index`.

    Raw strings honour no escapes, so only the closing quote and its hashes end them.
    Raw strings containing a newline are rare enough that the line counter is not advanced
    here; a comment opened after one would be reported on the wrong line rather than
    missed, and the check reports positions only for errors it has already found.
    """
    terminator = '"' + "#" * hashes
    closing = source.find(terminator, index + 1)
    return len(source) if closing < 0 else closing + len(terminator)


def violations(path: Path, source: str) -> list[str]:
    """Every place in `source` where a top-level block comment hides what follows it."""
    found = []
    for open_line, open_column, close_line, trailing in block_comments(source):
        if not trailing.strip():
            continue
        spans_lines = close_line > open_line
        starts_line = open_column == 0
        if not (spans_lines or starts_line):
            continue
        shape = "spans lines" if spans_lines else "starts its line"
        found.append(
            f"{path}:{close_line}: a block comment that {shape} is followed by "
            f"{trailing.strip()!r} on the line where it ends"
        )
    return found


def tracked_lean_sources() -> list[Path]:
    """Tracked and untracked-but-not-ignored Lean sources, vendored trees excluded."""
    paths: list[str] = []
    for arguments in (["ls-files", "-z", "--", "*.lean"],
                      ["ls-files", "--others", "--exclude-standard", "-z", "--", "*.lean"]):
        output = subprocess.run(["git", *arguments], check=True, text=True,
                                stdout=subprocess.PIPE).stdout
        paths.extend(entry for entry in output.split("\0") if entry)
    selected = [Path(path) for path in sorted(set(paths))
                if Path(path).parts[0] not in EXCLUDED_TOP_LEVEL]
    return [path for path in selected if path.is_file()]


def expand(arguments: list[str]) -> list[Path]:
    """The Lean sources named by `arguments`: files as given, directories recursively."""
    selected: list[Path] = []
    for argument in arguments:
        path = Path(argument)
        if path.is_dir():
            selected.extend(sorted(path.rglob("*.lean")))
        else:
            selected.append(path)
    return selected


def main(arguments: list[str]) -> int:
    try:
        paths = expand(arguments) if arguments else tracked_lean_sources()
    except (OSError, subprocess.CalledProcessError) as error:
        # Exit 2, never 1: a broken file listing is an infrastructure failure, and must not
        # be reported as if the sources had been read and found wanting.
        print(f"comment fences: cannot list Lean sources: {error}", file=sys.stderr)
        return 2
    if not paths:
        print("comment fences: no Lean sources to check.", file=sys.stderr)
        return 2
    found = []
    for path in paths:
        try:
            source = path.read_text(encoding="utf-8")
        except OSError as error:
            print(f"comment fences: {error}", file=sys.stderr)
            return 2
        found.extend(violations(path, source))
    if found:
        for message in found:
            print(f"ERROR: {message}", file=sys.stderr)
        print(f"Comment fences: {len(found)} block comment(s) hide what follows them. "
              "Move the declaration to its own line; a reader scanning the left margin "
              "cannot see it where it is.", file=sys.stderr)
        return 1
    print(f"Comment fences: OK ({len(paths)} Lean sources).")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
