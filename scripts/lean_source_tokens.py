"""Lexical tokens for text-based checks on Lean source."""

from collections.abc import Iterator
import re


TOKEN = re.compile(
    r'--[^\n]*|/-|-/'
    r'|r(?P<hashes>#+)".*?"(?P=hashes)|r".*?"'
    r'|"(?:\\.|[^"\\])*"|«[^»]*»'
    r"|'(?:\\.|[^'\\])'"
    r"|[^\W\d][\w'.]*|@\[|\S",
    re.DOTALL,
)


def token_matches(source: str) -> Iterator[re.Match[str]]:
    """Yield lexical matches outside comments, keeping each literal in one match."""
    depth = 0
    # Inside block comments only delimiters have meaning (quotes are ordinary text).
    position = 0
    while position < len(source):
        if depth:
            marker = re.search(r'/-|-/', source[position:])
            if marker is None:
                break
            depth += 1 if marker[0] == '/-' else -1
            position += marker.end()
            continue
        match = TOKEN.search(source, position)
        if match is None:
            break
        position = match.end()
        token = match[0]
        if token == '/-':
            depth = 1
        elif not token.startswith('--'):
            # Keep literals as whole tokens so their contents cannot match commands.
            yield match
