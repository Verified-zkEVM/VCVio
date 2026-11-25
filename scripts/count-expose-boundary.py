#!/usr/bin/env -S uv run --no-project --python 3.12 python
"""Count files with exposed public sections, ignoring Lean comments and literals.

This is a lexical check, not elaboration: macro-generated sections are outside its scope.
"""

from pathlib import Path
import sys

from lean_source_tokens import token_matches


def broadly_exposed(path: Path) -> bool:
    stream = [match[0] for match in token_matches(path.read_text(encoding='utf-8'))]
    # Lean.Parser.Command.sectionHeader permits expose, public, noncomputable, meta,
    # in that order. Attributes on declarations are deliberately not matched here.
    for start in range(len(stream)):
        if stream[start:start + 4] != ['@[', 'expose', ']', 'public']:
            continue
        end = start + 4
        for modifier in ('noncomputable', 'meta'):
            if stream[end:end + 1] == [modifier]:
                end += 1
        if stream[end:end + 1] == ['section']:
            return True
    return False


if __name__ == '__main__':
    root = Path(sys.argv[1])
    for library in sorted(sys.argv[2:]):
        directory = root / library
        if directory.is_dir():
            count = sum(broadly_exposed(path) for path in directory.rglob('*.lean'))
            print(f'{library}\t{count}')
