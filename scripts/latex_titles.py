"""Extract balanced LaTeX sectioning titles and their plain-text fallbacks."""

from __future__ import annotations

import re

CHAPTER_COMMAND = re.compile(r"\\chapter\*?\s*")
TEXORPDFSTRING = re.compile(r"\\texorpdfstring\s*")


def braced_argument(text: str, start: int) -> tuple[str, int]:
    while start < len(text) and text[start].isspace():
        start += 1
    if start >= len(text) or text[start] != "{":
        raise ValueError("expected a braced LaTeX argument")
    depth = 1
    position = start + 1
    while position < len(text):
        character = text[position]
        escaped = position > 0 and text[position - 1] == "\\"
        if character == "{" and not escaped:
            depth += 1
        elif character == "}" and not escaped:
            depth -= 1
            if depth == 0:
                return text[start + 1 : position], position + 1
        position += 1
    raise ValueError("unterminated braced LaTeX argument")


def chapter_titles(text: str) -> list[str]:
    titles: list[str] = []
    for match in CHAPTER_COMMAND.finditer(text):
        title, _ = braced_argument(text, match.end())
        titles.append(title)
    return titles


def plain_text_title(title: str) -> str:
    """Replace each texorpdfstring with its recursively normalized PDF string."""
    output: list[str] = []
    position = 0
    while match := TEXORPDFSTRING.search(title, position):
        output.append(title[position : match.start()])
        _, after_tex = braced_argument(title, match.end())
        pdf, after_pdf = braced_argument(title, after_tex)
        output.append(plain_text_title(pdf))
        position = after_pdf
    output.append(title[position:])
    return "".join(output)
