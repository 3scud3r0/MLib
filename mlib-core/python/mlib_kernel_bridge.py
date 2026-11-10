"""Explicit adapter from MLib Polynomial into the Rust JSON AST protocol.

This file is *untrusted*. The Rust kernel re-checks the entire proposition.
No floats, eval, Python AST execution or hidden simplification are used.
"""
from __future__ import annotations
import json
from fractions import Fraction
from typing import Any


def _const(value: Fraction | int) -> dict[str, Any]:
    if isinstance(value, float):
        raise TypeError("Coeficientes float não são admitidos no kernel")
    q = Fraction(value)
    return {"op": "const", "num": str(q.numerator), "den": str(q.denominator)}


def _binary(op: str, left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return {"op": op, "left": left, "right": right}


def polynomial_to_ast(poly: Any) -> dict[str, Any]:
    """Translate MLib's exact Polynomial terms without assuming they are trustworthy.

    Expected: poly.dimension and poly.terms as ((powers, Fraction), ...).
    Rust still parses and re-evaluates each arithmetic operation independently.
    """
    n = poly.dimension
    if not isinstance(n, int) or not 1 <= n <= 128:
        raise ValueError("Dimensão inválida")
    result = _const(0)
    for exponents, coefficient in poly.terms:
        if len(exponents) != n:
            raise ValueError("Expoentes incompatíveis")
        term = _const(coefficient)
        for i, exponent in enumerate(exponents):
            if not isinstance(exponent, int) or exponent < 0:
                raise ValueError("Expoente inválido")
            if exponent:
                variable = {"op": "var", "index": i}
                factor = variable if exponent == 1 else {"op": "pow", "base": variable, "exponent": exponent}
                term = _binary("mul", term, factor)
        result = _binary("add", result, term)
    return result


def verify_noether(ctx: Any, hamiltonian: Any, observable: Any) -> Any:
    """Submit candidate and Hamiltonian to *Rust*, returning an opaque theorem or error."""
    if hamiltonian.dimension != observable.dimension or hamiltonian.dimension % 2:
        raise ValueError("O espaço de fase deve ter 2n variáveis")
    pairs = hamiltonian.dimension // 2
    return ctx.verify_noether(
        pairs,
        json.dumps(polynomial_to_ast(hamiltonian), separators=(",", ":")),
        json.dumps(polynomial_to_ast(observable), separators=(",", ":")),
    )
