"""Ergonomic, UNTRUSTED Python AST builder for the native mlib_core Rust kernel.

The Python Expr class is **not** a theorem. Only mlib_core.MlibKernelContext
can return a native PyCertifiedTheorem. Never treat a digest as a signature.

Variables are ordered (q0, ..., q[n-1], p0, ..., p[n-1]).
Only exact int / Fraction coefficients are accepted. No eval or floats.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
from typing import Any, Iterable

MAX_AST_NODES = 20_000
MAX_AST_DEPTH = 64
MAX_EXPONENT = 100_000  # Rust TermArena limit. Resource-limited by the kernel.


def _fraction(value: object) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise TypeError("Apenas inteiros e Fraction exatos são aceitos; float é proibido")
    return Fraction(value)


class PhaseSpace:
    """Canonical cotangent phase space with 2*pairs ordered coordinates.

    PhaseSpace(2).coordinates() returns (q0, q1, p0, p1). Expressions from
    distinct PhaseSpace instances cannot be mixed, even with matching sizes.
    """

    __slots__ = ("pairs",)

    def __init__(self, pairs: int):
        if isinstance(pairs, bool) or not isinstance(pairs, int) or not 1 <= pairs <= 64:
            raise ValueError("pairs deve ser um inteiro de 1 a 64")
        self.pairs = pairs

    @property
    def dimension(self) -> int:
        return 2 * self.pairs

    def coordinate(self, index: int) -> Expr:
        if isinstance(index, bool) or not isinstance(index, int) or not 0 <= index < self.dimension:
            raise IndexError("índice de coordenada fora do espaço de fase")
        return Expr(self, ("var", index))

    def coordinates(self) -> tuple[Expr, ...]:
        return tuple(self.coordinate(i) for i in range(self.dimension))

    def constant(self, value: int | Fraction) -> Expr:
        q = _fraction(value)
        return Expr(self, ("const", q.numerator, q.denominator))

    def from_polynomial(self, polynomial: Any) -> Expr:
        """Safely build an expression from the legacy ML-MATHLIB Polynomial.

        No trust is placed in this conversion: Rust reparses and proves the
        resulting AST. Mismatched dimensions and nonexact coefficients fail.
        """
        if polynomial.dimension != self.dimension:
            raise ValueError("dimensão polinomial não coincide com o espaço")
        terms = polynomial.terms
        output = self.constant(0)
        for exponents, coefficient in terms:
            if len(exponents) != self.dimension:
                raise ValueError("expoente com dimensão incompatível")
            term = self.constant(_fraction(coefficient))
            for index, exponent in enumerate(exponents):
                if isinstance(exponent, bool) or not isinstance(exponent, int) or exponent < 0:
                    raise ValueError("expoente inválido")
                if exponent:
                    term = term * (self.coordinate(index) ** exponent)
            output = output + term
        return output


@dataclass(frozen=True, slots=True, eq=False)
class Expr:
    """Immutable symbolic syntax, NEVER a mathematical certificate."""

    _space: PhaseSpace
    _node: tuple[Any, ...]

    @property
    def space(self) -> PhaseSpace:
        return self._space

    def _coerce(self, other: object) -> Expr:
        if isinstance(other, Expr):
            if other._space is not self._space:
                raise ValueError("expressões de espaços de fase distintos")
            return other
        return self._space.constant(_fraction(other))

    def _binary(self, op: str, other: object) -> Expr:
        rhs = self._coerce(other)
        return Expr(self._space, (op, self._node, rhs._node))

    def _reverse(self, op: str, other: object) -> Expr:
        lhs = self._coerce(other)
        return Expr(self._space, (op, lhs._node, self._node))

    def __add__(self, other: object) -> Expr:
        return self._binary("add", other)

    def __radd__(self, other: object) -> Expr:
        return self._reverse("add", other)

    def __sub__(self, other: object) -> Expr:
        return self._binary("sub", other)

    def __rsub__(self, other: object) -> Expr:
        return self._reverse("sub", other)

    def __mul__(self, other: object) -> Expr:
        return self._binary("mul", other)

    def __rmul__(self, other: object) -> Expr:
        return self._reverse("mul", other)

    def __truediv__(self, other: object) -> Expr:
        rhs = self._coerce(other)
        if rhs._node == ("const", 0, 1):
            raise ZeroDivisionError("divisão exata por zero")
        return Expr(self._space, ("div", self._node, rhs._node))

    def __rtruediv__(self, other: object) -> Expr:
        if self._node == ("const", 0, 1):
            raise ZeroDivisionError("divisão exata por zero")
        return self._reverse("div", other)

    def __pow__(self, exponent: int, modulo: object = None) -> Expr:
        if modulo is not None:
            raise TypeError("potência modular não é definida para Expr")
        if isinstance(exponent, bool) or not isinstance(exponent, int) or not 0 <= exponent <= MAX_EXPONENT:
            raise ValueError("expoente deve ser inteiro não negativo <= 100000")
        return Expr(self._space, ("pow", self._node, exponent))

    def __neg__(self) -> Expr:
        return Expr(self._space, ("sub", ("const", 0, 1), self._node))

    def __pos__(self) -> Expr:
        return self

    def partial(self, var: Expr | int) -> Expr:
        if isinstance(var, Expr):
            if var._space is not self._space or var._node[0] != "var":
                raise ValueError("derivada parcial exige coordenada do mesmo espaço")
            index = var._node[1]
        elif isinstance(var, int) and not isinstance(var, bool) and 0 <= var < self._space.dimension:
            index = var
        else:
            raise ValueError("índice da derivada inválido")
        return Expr(self._space, ("partial_deriv", self._node, index))

    def poisson(self, other: Expr) -> Expr:
        rhs = self._coerce(other)
        return Expr(self._space, ("poisson_bracket", self._node, rhs._node))

    def to_ast(self) -> dict[str, Any]:
        """Convert immutable syntax into the strict Rust JSON AST protocol."""
        remaining = [MAX_AST_NODES]

        def convert(node: tuple[Any, ...], depth: int) -> dict[str, Any]:
            remaining[0] -= 1
            if remaining[0] < 0 or depth > MAX_AST_DEPTH:
                raise ValueError("expressão excede orçamento de AST")
            op = node[0]
            if op == "const":
                return {"op": op, "num": str(node[1]), "den": str(node[2])}
            if op == "var":
                return {"op": op, "index": node[1]}
            if op in ("add", "sub", "mul", "div"):
                return {"op": op, "left": convert(node[1], depth + 1), "right": convert(node[2], depth + 1)}
            if op == "pow":
                return {"op": op, "base": convert(node[1], depth + 1), "exponent": node[2]}
            if op == "partial_deriv":
                return {"op": op, "target": convert(node[1], depth + 1), "var_index": node[2]}
            if op == "poisson_bracket":
                return {"op": op, "pairs": self._space.pairs,
                        "f": convert(node[1], depth + 1), "g": convert(node[2], depth + 1)}
            raise ValueError(f"operação AST desconhecida: {op}")

        return convert(self._node, 0)

    def to_json(self) -> str:
        return json.dumps(self.to_ast(), ensure_ascii=True, separators=(",", ":"))


class Kernel:
    """Strict native Rust verifier facade; no Python proof fallback.

    Fails with ImportError if the compiled extension is not installed. That
    behavior is intentional: Python must never 'certify' its own proposals.
    """

    __slots__ = ("_native",)

    def __init__(self):
        try:
            from mlib_core import MlibKernelContext
        except ImportError as error:
            raise ImportError("O verificador Rust não está instalado. Use maturin develop --features python") from error
        self._native = MlibKernelContext()

    def verify_conservation(self, phase: PhaseSpace, *, hamiltonian: Expr, candidate: Expr) -> Any:
        for name, value in (("hamiltonian", hamiltonian), ("candidate", candidate)):
            if not isinstance(value, Expr) or value.space is not phase:
                raise ValueError(f"{name} deve pertencer ao PhaseSpace informado")
        return self._native.verify_noether(phase.pairs, hamiltonian.to_json(), candidate.to_json())

    def verify_symplectic(self, phase: PhaseSpace, mapping: Iterable[Expr]) -> Any:
        outputs = tuple(mapping)
        if len(outputs) != phase.dimension or any(not isinstance(e, Expr) or e.space is not phase for e in outputs):
            raise ValueError("mapa deve conter exatamente 2n expressões do mesmo espaço")
        return self._native.verify_symplectic(phase.pairs, json.dumps([expr.to_ast() for expr in outputs], separators=(",", ":")))

    def verify_polynomial_gcd(self, phase: PhaseSpace, a: Expr, b: Expr, hint: Expr) -> Any:
        """Certify an untrusted proposed multivariate GCD over Q[x].

        Both exact divisibilities and the coprimality of the remaining
        cofactors are checked inside Rust; a mere common divisor is rejected.
        """
        if any(not isinstance(e, Expr) or e.space is not phase for e in (a, b, hint)):
            raise ValueError("entradas do GCD devem pertencer ao mesmo espaço")
        return self._native.verify_gcd_hint(phase.dimension, a.to_json(), b.to_json(), hint.to_json())

    def verify_positive_gram(self, matrix: Iterable[Iterable[int | Fraction]]) -> Any:
        rows = [[str(_fraction(v)) for v in row] for row in matrix]
        return self._native.verify_positive_gram(rows)
