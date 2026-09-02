"""Shared lightweight scanning helpers for repository-owned LaTeX sources."""

from __future__ import annotations

import re
from dataclasses import dataclass


def is_escaped(text: str, position: int) -> bool:
    """Return whether the character at position has an odd backslash prefix."""
    backslashes = 0
    position -= 1
    while position >= 0 and text[position] == "\\":
        backslashes += 1
        position -= 1
    return backslashes % 2 == 1


def without_comments(text: str) -> str:
    """Remove unescaped TeX comments while preserving line and column positions."""
    output: list[str] = []
    in_comment = False
    for position, character in enumerate(text):
        if in_comment:
            if character in "\r\n":
                in_comment = False
                output.append(character)
            else:
                output.append(" ")
        elif character == "%" and not is_escaped(text, position):
            in_comment = True
            output.append(" ")
        else:
            output.append(character)
    return "".join(output)


def braced_argument(text: str, start: int) -> tuple[str, int]:
    """Read one balanced braced argument starting at or after start."""
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text) or text[start] != "{":
        raise ValueError("expected a braced LaTeX argument")
    depth = 1
    position = start + 1
    while position < len(text):
        character = text[position]
        if character == "{" and not is_escaped(text, position):
            depth += 1
        elif character == "}" and not is_escaped(text, position):
            depth -= 1
            if depth == 0:
                return text[start + 1 : position], position + 1
        position += 1
    raise ValueError("unterminated braced LaTeX argument")


def has_balanced_braces(text: str) -> bool:
    """Return whether text can safely be embedded in one braced argument."""
    wrapped = "{" + text + "}"
    try:
        _, end = braced_argument(wrapped, 0)
    except ValueError:
        return False
    return end == len(wrapped)


@dataclass(frozen=True)
class CommandArgument:
    name: str
    argument: str
    position: int


def command_arguments(text: str, names: set[str]) -> list[CommandArgument]:
    """Return required braced arguments for named commands outside comments."""
    if not names:
        return []
    clean = without_comments(text)
    pattern = re.compile(
        r"\\(?P<name>" + "|".join(re.escape(name) for name in sorted(names)) + r")"
        r"(?![A-Za-z@])\*?"
    )
    found: list[CommandArgument] = []
    for match in pattern.finditer(clean):
        try:
            argument, _ = braced_argument(clean, match.end())
        except ValueError:
            continue
        found.append(CommandArgument(match.group("name"), argument, match.start()))
    return found
