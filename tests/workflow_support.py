"""Evaluate the boolean subset used by repository workflow gates."""

from __future__ import annotations

import ast
import re


def condition_allows(condition: str, context: dict[str, str | bool]) -> bool:
    expression = condition.strip().removeprefix("${{").removesuffix("}}").strip()
    tokens = re.compile(
        r"'(?:[^']|'')*'|(?:github|needs)\.[\w.-]+|always\(\)|cancelled\(\)"
        r"|&&|\|\||!(?!=)|\b(?:true|false)\b"
    )

    def translate(match: re.Match[str]) -> str:
        token = match.group()
        if token.startswith("'"):
            return repr(token[1:-1].replace("''", "'"))
        if token.startswith(("github.", "needs.")):
            return repr(context[token])
        return {
            "always()": "True",
            "cancelled()": repr(context.get("cancelled", False)),
            "&&": " and ",
            "||": " or ",
            "!": " not ",
            "true": "True",
            "false": "False",
        }[token]

    tree = ast.parse(tokens.sub(translate, expression).strip(), mode="eval")
    allowed = (
        ast.Expression,
        ast.BoolOp,
        ast.And,
        ast.Or,
        ast.UnaryOp,
        ast.Not,
        ast.Compare,
        ast.Eq,
        ast.NotEq,
        ast.Constant,
    )
    if any(not isinstance(node, allowed) for node in ast.walk(tree)):
        raise ValueError("unsupported workflow condition")
    return bool(
        eval(compile(tree, "<workflow condition>", "eval"), {"__builtins__": {}})
    )
