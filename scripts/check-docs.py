#!/usr/bin/env python3
"""Check repository Markdown links and the documented theorem environments.

Supports the repository's inline/reference links and ATX headings, excluding
fenced code and inline code. This is an offline check, not a Markdown renderer.
The snapshot README's pdf/ link is resolved on its publication branch, not main.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

from latex_scan import without_comments

ROOT = Path(__file__).resolve().parent.parent


def prose(text: str) -> str:
    lines = []
    fence = None
    for line in text.splitlines():
        match = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
        if fence:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence):
                fence = None
            lines.append("")
        elif match:
            fence = match[1]
            lines.append("")
        else:
            lines.append(line)
    return "\n".join(lines)


def anchors(text: str) -> set[str]:
    found: set[str] = set()
    for line in prose(text).splitlines():
        match = re.match(r"^ {0,3}#{1,6}\s+(.+?)\s*#*\s*$", line)
        if not match:
            continue
        title = re.sub(r"<[^>]+>", "", match[1])
        title = re.sub(r"\[([^]]+)\]\([^)]*\)", r"\1", title)
        slug = re.sub(r"[^\w\- ]", "", title.lower()).replace(" ", "-")
        candidate = slug
        number = 0
        while candidate in found:
            number += 1
            candidate = f"{slug}-{number}"
        found.add(candidate)
    return found


def link_errors(path: Path, root: Path) -> list[str]:
    text = prose(path.read_text(encoding="utf-8"))

    def inline_code(match: re.Match[str]) -> str:
        # Keep code-formatted link labels, but ignore standalone code examples.
        if (
            text[max(0, match.start() - 1) : match.start()] == "["
            and text[match.end() : match.end() + 1] == "]"
        ):
            return match[2]
        return ""

    text = re.sub(r"(`+)(.*?)\1", inline_code, text)
    definitions = dict(
        (key.casefold(), target)
        for key, target in re.findall(r"^\s*\[([^]]+)\]:\s*(\S+)", text, re.M)
    )
    links = re.findall(r"\[[^]\n]+\]\(([^)\n]+)\)", text)
    errors = []
    for label, key in re.findall(r"\[([^]\n]+)\]\[([^]\n]*)\]", text):
        key = (key or label).casefold()
        if key not in definitions:
            errors.append(f"undefined link reference: {key}")
        else:
            links.append(definitions[key])
    for target in links:
        # Optional titles follow a whitespace separator; angle brackets allow spaces.
        match = re.match(r"<([^>]+)>|([^\s]+)", target.strip())
        if not match:
            continue
        target = match[1] or match[2]
        url = urlsplit(target)
        if url.scheme or url.netloc:
            continue
        if (
            path.relative_to(root).as_posix() == ".github/generated-pdfs-README.md"
            and target == "pdf/"
        ):
            continue
        dest = (
            (
                root / unquote(url.path).lstrip("/")
                if url.path.startswith("/")
                else path.parent / unquote(url.path)
            )
            if url.path
            else path
        )
        if not dest.exists():
            errors.append(f"missing link target: {target}")
        elif url.fragment and dest.suffix.lower() == ".md":
            if unquote(url.fragment) not in anchors(dest.read_text(encoding="utf-8")):
                errors.append(f"missing heading anchor: {target}")
    return errors


def environment_errors(root: Path) -> list[str]:
    guide = (root / "docs/writing-guide.md").read_text(encoding="utf-8")
    sections = guide.split("### Theorem environments\n", 1)
    if len(sections) != 2:
        return ["writing guide is missing its theorem-environment section"]
    section = sections[1].split("###", 1)[0]
    match = re.search(r"The public environments are (.*?)\. Use", section, re.S)
    if not match:
        return ["writing guide is missing its public environment list"]
    documented = set(re.findall(r"`([a-z]+)`", match[1]))
    style = without_comments(
        (root / "common/styles/textbook-theorems.sty").read_text(encoding="utf-8")
    )
    implemented = set(re.findall(r"\\newtheorem\*?\{([^}]+)\}", style))
    # proof is supplied by amsthm, not a repository newtheorem declaration.
    if re.search(r"\\RequirePackage(?:\[[^]]*\])?\{amsthm\}", style):
        implemented.add("proof")
    errors = []
    for name in sorted(documented - implemented):
        errors.append(f"documented environment is undefined: {name}")
    for name in sorted(implemented - documented):
        errors.append(f"shared environment is undocumented: {name}")
    return errors


def markdown_files(root: Path) -> list[Path]:
    result = subprocess.run(
        [
            "git",
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "--",
            "*.md",
        ],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if result.returncode == 0:
        return sorted(
            {
                root / name.decode()
                for name in result.stdout.split(b"\0")
                if name and (root / name.decode()).is_file()
            }
        )
    # Source archives have no Git metadata; exclude generated pages and dependencies.
    candidates = [root / "README.md", root / "AGENTS.md"]
    for directory in ("docs", "books", "common/templates", ".github"):
        candidates.extend((root / directory).rglob("*.md"))
    return sorted(path for path in candidates if path.is_file())


def main() -> int:
    errors = []
    paths = markdown_files(ROOT)
    for path in paths:
        errors.extend(
            f"{path.relative_to(ROOT)}: {error}" for error in link_errors(path, ROOT)
        )
    errors.extend(environment_errors(ROOT))
    for error in errors:
        print(f"error: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"Documentation checks passed ({len(paths)} Markdown files).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
