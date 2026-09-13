"""Ignore Lean comments and literals when checking source-level proof markers."""

from __future__ import annotations

import re


def without_comments_and_literals(text: str) -> str:
    """Preserve positions while masking nested comments, strings, and quoted names."""
    output = list(text)
    position = 0
    while position < len(text):
        start = position
        if text.startswith("--", position):
            end = text.find("\n", position)
            position = len(text) if end < 0 else end
        elif text.startswith("/-", position):
            depth = 1
            position += 2
            while position < len(text) and depth:
                if text.startswith("/-", position):
                    depth += 1
                    position += 2
                elif text.startswith("-/", position):
                    depth -= 1
                    position += 2
                else:
                    position += 1
        elif text[position] in ('"', "«"):
            closing = '"' if text[position] == '"' else "»"
            position += 1
            while position < len(text):
                char = text[position]
                position += 1
                if char == "\\" and closing == '"':
                    position += 1
                elif char == closing:
                    break
        else:
            position += 1
            continue
        for index in range(start, min(position, len(text))):
            if output[index] not in "\r\n":
                output[index] = " "
    return "".join(output)


def escape_hatch_lines(text: str) -> list[int]:
    """Find unfinished proofs and axiom declarations, including anonymous examples."""
    clean = without_comments_and_literals(text)
    return [
        clean.count("\n", 0, match.start()) + 1
        for match in re.finditer(r"\b(?:sorry|admit|axiom)\b", clean)
    ]
