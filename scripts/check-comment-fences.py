#!/usr/bin/env python3
"""Keep a block comment at the left margin from hiding the declaration that follows it.

A declaration written after the `-/` of the comment that documents it parses, builds and
runs, and is invisible to a reader scanning the left margin for declarations. That is not
hypothetical: a docstring reflow in `lakefile.lean` once produced

    at least one. -/ lean_exe slhdsa_limited_profile_tests where root :=

and every gate in the repository passed it.

Lean's own `linter.style.whitespace` rejects a command that does not start at the beginning
of a line, and this package turns it on through `weak.linter.mathlibStandardSet`. It is
silent on the *doc-comment* form of the shape above, and that is positional rather than a
property of the lakefile: a doc comment is part of the command it documents, so the command
*does* start at the beginning of a line — the line where the `/--` opened, several lines
earlier. The other forms it does catch. (Everything below was measured by elaborating
probes with that option on and `Mathlib.Init` imported: unless something in the import
closure registers it the `weak.` option is silently dropped, which is the mechanism of the
`scripts/` case.)

So the shape divides by what a warning *does*, not by whether a linter exists:

* the `/--` form draws nothing anywhere, the libraries the elaboration linters do run over
  included, because the linter's position for such a command is the `/--` at column 0 and
  there is nothing left to report. Witnessed for four spellings: a wrapped `/--` and a
  one-line `/--`, each before a `def` and before `@[simp] theorem` / `instance`. *That is
  the historical defect, and it is what this gate is for.*
* the `/-` and `/-!` forms, wrapped or on one line, each draw a warning, as an indented
  `def` and a second `def` after a mid-line `/- … -/` do. In the seven proof libraries and
  the three test libraries that warning is already a CI failure, because
  `scripts/check-warning-log.py` reads the build log with a `--path-prefix` per library.
  This gate is redundant there and deliberately says the same thing.
* four places elaborate no such warning, or elaborate one that fails nothing, and every
  form of the shape survives in them:

  - `lakefile.lean` and `VCVioComplexity/lakefile.lean`: Lake elaborates each from
    `import Lake`, with no Mathlib linter registered.
  - `Interop/`: not a default target and no CI job builds it, so nothing elaborates it.
  - `scripts/`: per-PR CI *does* build it (`lake build VCVioAxiomSweepTestFixtures`, then
    `lake exe axiomsweep --check`), but no source there has Mathlib in its import closure —
    `AxiomSweep.lean` imports `Lean`, the axiom-sweep fixture modules import nothing outside
    their own library — so `weak.linter.mathlibStandardSet` is dropped and the linter is
    never registered. One Mathlib import in one fixture would flip that.
  - `VCVioComplexity/`: its own lakefile sets `linter.style.whitespace` explicitly, its
    sources do import Mathlib, and the `complexity_backend` job builds it on every pull
    request, so the linter runs and warns. What is missing there is the *gate*:
    `check-warning-log.py` is invoked only with the proof- and test-library prefixes, and
    `VCVioComplexity/scripts/test.sh` pipes its build log nowhere.

  `scripts/lint.py`'s text-based style pass reaches only `Interop/` of those four, and
  catches none of this in any file: its four linters have no model of a comment at all.

The rule, in one sentence: *a block comment that begins its line must be the last thing on
the line where it ends.* The test is positional — where the comment opens, not what the text
after it turns out to be. A comment at column 0 is a top-level comment wherever the code
around it is indented, and code written after its `-/` is then a declaration that no longer
starts its own line. A comment that opens part-way into a line is untouched however many
lines it spans: it is an annotation inside an expression, a field, a constructor or a tactic
block, the code around it is on the line the reader is already reading, and it hides
nothing. Reaching those would cost innocent code — a wrapped field docstring, a `/--`
opening indented inside a `structure` or `class` body and closing on the line of the field
it documents, is this repository's commonest documentation idiom, and a rule that also keyed
on "spans more than one line" would put every one of them one reflow away from failing CI,
with a message telling the author to move a declaration off a left margin it was never on.

Two things written after the `-/` hide nothing and are skipped: further complete `/- … -/`
comments, and a `--` comment running to the end of the line.

Rejected by design, and not a declaration: Lean also lets a term, a structure field, a
tactic or a list element begin at column 0, where the enclosing command's indentation has
run out, and a comment written in front of one of those is rejected like a top-level one.
Four such shapes are asserted in the fixture matrix (`Lib/ColumnZero.lean`), each of them
Lean that elaborates with no error and no warning, so the boundary is written down rather
than rediscovered. Nothing in the repository is written that way: the check's baseline is
zero and it re-establishes that on every run.

Scope: every Lean source the repository tracks or would track — tracked files plus untracked
ones that are not ignored — with the vendored `third_party/` tree excluded. `lakefile.lean`
is in scope and is the file the rule was written for; it is also outside `scripts/lint.py`'s
style pass, which covers the library and test roots only.

What this cannot catch. One shape is uncovered everywhere, as the same-line `/--` form is:

* a comment at the left margin whose declaration is *indented on the next line*.  The
  comment is the last thing on its line, so the rule does not apply; and
  `linter.style.whitespace` measures the command from the `/--` at column 0, so it draws no
  warning either.  Measured in a library file with the standard set on: an indented `def`
  is flagged, the same `def` under a margin docstring is not.

The other four are reported by `linter.style.whitespace` wherever it is registered, so they
fail CI in the ten built libraries and survive in the four places above:

* an *indented* comment followed by a declaration on its closing line,
  `  /-- Doc. -/ lean_exe hidden where`;
* a single-line comment that starts mid-line and is followed by a declaration,
  `def a := 1 /- note -/ def b := 2`;
* a bare indented command, or two declarations on one line, with no comment involved;
* a declaration written after the closing quote of a *multi-line string literal* — the same
  hiding with a different delimiter, in all three spellings (a plain string over two lines,
  one held together by a gap escape, and a raw string):

      def banner : String := "first line
      second line" def hidden : Nat := 2

  `lakefile.lean` uses multi-line strings itself, and nothing checks what follows one:
  not this rule, which is about comments, and not the linter, which does not run there.

All five are asserted accepted in the fixture matrix (`Lib/Uncovered.lean`), so a documented
gap cannot move without the test saying so.  For the file this rule was written for it
closes the doc-comment sub-case and leaves the rest of the class open.  Widening to "nothing
may ever follow `-/`" would cover the mid-line form and would also reject the wrapped field
docstrings above, which have no defect behind them — and would still not reach the string
form.

Usage:
    scripts/check-comment-fences.py            # every tracked/untracked Lean source
    scripts/check-comment-fences.py PATH...    # those files, or every .lean under them
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

EXCLUDED_TOP_LEVEL = {"third_party"}
REPOSITORY_ROOT = Path(__file__).resolve().parent.parent


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
            index, line, line_start = skip_raw_string(source, index + 1, 0, line, line_start)
            continue
        if character == "r" and source.startswith("#", index + 1):
            hashes = 0
            while source.startswith("#", index + 1 + hashes):
                hashes += 1
            if source.startswith('"', index + 1 + hashes):
                index, line, line_start = skip_raw_string(source, index + 1 + hashes, hashes,
                                                          line, line_start)
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


def skip_raw_string(source: str, index: int, hashes: int, line: int,
                    line_start: int) -> tuple[int, int, int]:
    """The index just past the raw string literal whose opening quote is at `index`, with
    the line counter advanced.

    Raw strings honour no escapes, so only the closing quote and its hashes end them. Every
    newline inside one still has to be counted: a comment opened after an uncounted one
    would be reported on the wrong line, naming innocent code, for the rest of the file.
    """
    terminator = '"' + "#" * hashes
    closing = source.find(terminator, index + 1)
    end = len(source) if closing < 0 else closing + len(terminator)
    for offset in range(index, end):
        if source[offset] == "\n":
            line += 1
            line_start = offset + 1
    return end, line, line_start


def hidden_code(trailing: str) -> str:
    """What is left of the text after a `-/` once the things that hide nothing are removed.

    Two of them: further complete `/- ... -/` comments, and a `--` comment running to the
    end of the line. So `/- a -/ /- b -/ def x` still reports `def x`, while `/- a -/ /- b
    -/` and `/- a -/ -- note` report nothing and are accepted. A block comment that opens
    here and does not close on this line is left in place: whatever follows it is on a later
    line, and the rule reports rather than guesses.
    """
    rest = trailing.strip()
    while rest.startswith("/-"):
        depth, cursor = 0, 0
        while cursor < len(rest):
            if rest.startswith("/-", cursor):
                depth += 1
                cursor += 2
            elif rest.startswith("-/", cursor):
                depth -= 1
                cursor += 2
                if depth == 0:
                    break
            else:
                cursor += 1
        if depth != 0:
            return rest
        rest = rest[cursor:].strip()
    return "" if rest.startswith("--") else rest


def violations(path: Path, source: str) -> list[str]:
    """Every place in `source` where a block comment at the left margin hides what follows
    it. A comment that opens part-way into a line is an annotation inside some larger piece
    of syntax and is skipped however many lines it spans; see the module docstring."""
    found = []
    for _open_line, open_column, close_line, trailing in block_comments(source):
        if open_column != 0:
            continue
        hidden = hidden_code(trailing)
        if not hidden:
            continue
        found.append(
            f"{path}:{close_line}: a block comment that starts its line is followed by "
            f"{hidden!r} on the line where it ends"
        )
    return found


def tracked_lean_sources() -> list[Path]:
    """Tracked and untracked-but-not-ignored Lean sources, vendored trees excluded.

    `git ls-files` lists the current directory downwards, so `main` moves to the repository
    root before calling this: run from a subdirectory it would otherwise scan a subtree and
    report a clean tree, and the vendored filter below would have nothing to match.
    """
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
    """The Lean sources named by `arguments`: files as given, directories recursively.
    Resolved against the caller's directory, which is why `main` does not move first when
    it has arguments."""
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
        if arguments:
            paths = expand(arguments)
        else:
            os.chdir(REPOSITORY_ROOT)
            paths = tracked_lean_sources()
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
        except (OSError, UnicodeDecodeError) as error:
            # Same reasoning: a file that cannot be decoded has not been read and found
            # wanting either. `UnicodeDecodeError` is a `ValueError`, not an `OSError`.
            print(f"comment fences: {path}: {error}", file=sys.stderr)
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
