"""Small structural scanner for BibTeX database entry keys."""

from __future__ import annotations

try:
    from scripts.latex_scan import is_escaped
except ModuleNotFoundError:
    from latex_scan import is_escaped

NON_ENTRY_TYPES = {"comment", "preamble", "string"}


def entry_keys(text: str) -> list[str]:
    """Return database entry keys without treating @ inside values as entries."""
    keys: list[str] = []
    position = 0
    length = len(text)
    while position < length:
        marker = text.find("@", position)
        if marker < 0:
            break
        position = marker + 1
        while position < length and text[position].isspace():
            position += 1
        start = position
        while position < length and (
            text[position].isalnum() or text[position] in "_-"
        ):
            position += 1
        entry_type = text[start:position].lower()
        while position < length and text[position].isspace():
            position += 1
        if not entry_type or position >= length or text[position] not in "{(":
            continue
        opening = text[position]
        closing = "}" if opening == "{" else ")"
        body_start = position + 1
        position += 1
        while position < length and text[position].isspace():
            position += 1
        key_start = position
        while position < length and text[position] not in ",\r\n":
            position += 1
        key = text[key_start:position].strip()
        if (
            entry_type not in NON_ENTRY_TYPES
            and key
            and position < length
            and text[position] == ","
        ):
            keys.append(key)
        depth = 1
        position = body_start
        quoted = False
        while position < length and depth:
            character = text[position]
            if character == '"' and not is_escaped(text, position):
                quoted = not quoted
            elif not quoted:
                if character == opening:
                    depth += 1
                elif character == closing:
                    depth -= 1
            position += 1
    return keys
