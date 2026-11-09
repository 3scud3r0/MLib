#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ML-MATHLIB 0.1 — núcleo matemático executável, sem dependências externas.

Hierarquia e contratos:
  [0] ℚ-espaços vetoriais, produtos internos, dualidade e operadores lineares.
  [1] Atlas afim, fibrados tangente/cotangente, álgebras de Lie e simplética.
  [2] Probabilidade finita, entropia, KL e métrica de Fisher-Rao.
  [3] Campos hamiltonianos e Euler simplético com certificação polinomial.
  [4] Roteamento de máxima entropia e representação de rotações SO(2).
  [5] Noether e descoberta algébrica de primeiros integrais.

A aritmética algébrica é EXATA (frações de inteiros). Logaritmos,
trigonometria e softmax são APROXIMADOS (float da biblioteca padrão).

Alcance: variedades afins e hamiltonianos POLINOMIAIS em dimensão finita.
Não é um assistente de provas geral nem uma implementação de GPU, autodiff,
variedades gerais, SDEs ou um Transformer completo.

Execução:
    python ml_mathlib.py --test
    python ml_mathlib.py --demo
"""

from __future__ import annotations

import argparse
import itertools
import math
import unittest
from dataclasses import dataclass, field
from fractions import Fraction
from functools import reduce
from typing import Iterable, Sequence


# ──────────────────────────────────────────────────────────────────────────
# ESTRATO 0 — CORPO, ÁLGEBRA LINEAR, DUALIDADE
# ──────────────────────────────────────────────────────────────────────────


def Q(x: int | str | Fraction) -> Fraction:
    """Injeta um racional EXATO em ℚ; float é proibido (evita falsas provas)."""
    if isinstance(x, bool) or not isinstance(x, (int, str, Fraction)):
        raise TypeError("Coeficientes exatos devem ser int, str ou Fraction; não float")
    return Fraction(x)


@dataclass(frozen=True)
class Vector:
    """Elemento de ℚ^n com soma e multiplicação por escalares de ℚ."""

    entries: tuple[Fraction, ...]

    def __post_init__(self):
        object.__setattr__(self, "entries", tuple(Q(x) for x in self.entries))

    @property
    def dim(self) -> int:
        return len(self.entries)

    def _same(self, other: Vector) -> None:
        if self.dim != other.dim:
            raise ValueError("Dimensões vetoriais incompatíveis")

    def __add__(self, other: Vector) -> Vector:
        self._same(other)
        return Vector(tuple(a + b for a, b in zip(self.entries, other.entries)))

    def __neg__(self) -> Vector:
        return Vector(tuple(-a for a in self.entries))

    def __sub__(self, other: Vector) -> Vector:
        return self + (-other)

    def scale(self, scalar: int | str | Fraction) -> Vector:
        c = Q(scalar)
        return Vector(tuple(c * x for x in self.entries))

    def dot(self, other: Vector) -> Fraction:
        self._same(other)
        return sum((a * b for a, b in zip(self.entries, other.entries)), Fraction(0))

    def l1(self) -> Fraction:
        """Norma L1: não é induzida por produto interno quando n > 1."""
        return sum((abs(x) for x in self.entries), Fraction(0))


@dataclass(frozen=True)
class VectorSpace:
    """ℚ^n: o fechamento e as leis seguem dos axiomas do corpo ℚ."""

    dimension: int

    def __post_init__(self):
        if self.dimension < 1:
            raise ValueError("A dimensão deve ser positiva")

    def element(self, *entries: int | str | Fraction) -> Vector:
        if len(entries) != self.dimension:
            raise ValueError("Quantidade de coordenadas incorreta")
        return Vector(tuple(Q(x) for x in entries))

    def zero(self) -> Vector:
        return Vector((Fraction(0),) * self.dimension)


@dataclass(frozen=True)
class Matrix:
    """Matriz exata sobre ℚ, representada por tupla imutável de linhas."""

    rows: tuple[tuple[Fraction, ...], ...]

    def __post_init__(self):
        rows = tuple(tuple(Q(x) for x in row) for row in self.rows)
        if not rows or not rows[0] or any(len(r) != len(rows[0]) for r in rows):
            raise ValueError("Matriz deve ser retangular e não vazia")
        object.__setattr__(self, "rows", rows)

    @property
    def shape(self) -> tuple[int, int]:
        return len(self.rows), len(self.rows[0])

    @classmethod
    def identity(cls, n: int) -> Matrix:
        if n < 1:
            raise ValueError("Dimensão inválida")
        return cls(tuple(tuple(int(i == j) for j in range(n)) for i in range(n)))

    @classmethod
    def zero(cls, n: int, m: int) -> Matrix:
        if n < 1 or m < 1:
            raise ValueError("Dimensão inválida")
        return cls(tuple((Fraction(0),) * m for _ in range(n)))

    def transpose(self) -> Matrix:
        return Matrix(tuple(zip(*self.rows)))

    def __matmul__(self, other: Matrix | Vector) -> Matrix | Vector:
        n, k = self.shape
        if isinstance(other, Vector):
            if other.dim != k:
                raise ValueError("Domínio da matriz não coincide com dimensão do vetor")
            return Vector(tuple(sum((self.rows[i][t] * other.entries[t] for t in range(k)), Fraction(0))
                                for i in range(n)))
        r, m = other.shape
        if k != r:
            raise ValueError("Matrizes não podem ser compostas nessas dimensões")
        return Matrix(tuple(tuple(sum((self.rows[i][t] * other.rows[t][j] for t in range(k)), Fraction(0))
                                  for j in range(m)) for i in range(n)))

    def _same(self, other: Matrix):
        if self.shape != other.shape:
            raise ValueError("Formas de matrizes incompatíveis")

    def __add__(self, other: Matrix) -> Matrix:
        self._same(other)
        return Matrix(tuple(tuple(a + b for a, b in zip(ra, rb))
                            for ra, rb in zip(self.rows, other.rows)))

    def __neg__(self) -> Matrix:
        return self.scale(-1)

    def __sub__(self, other: Matrix) -> Matrix:
        return self + (-other)

    def scale(self, scalar: int | str | Fraction) -> Matrix:
        c = Q(scalar)
        return Matrix(tuple(tuple(c * v for v in row) for row in self.rows))

    def inverse(self) -> Matrix:
        """Gauss-Jordan racional, sem heurística de tolerância."""
        n, m = self.shape
        if n != m:
            raise ValueError("Somente matrizes quadradas são inversíveis")
        a = [[*row, *(int(i == j) for j in range(n))] for i, row in enumerate(self.rows)]
        for j in range(n):
            pivot = next((i for i in range(j, n) if a[i][j] != 0), None)
            if pivot is None:
                raise ValueError("Matriz singular")
            a[j], a[pivot] = a[pivot], a[j]
            c = a[j][j]
            a[j] = [x / c for x in a[j]]
            for i in range(n):
                if i != j:
                    c = a[i][j]
                    a[i] = [x - c * y for x, y in zip(a[i], a[j])]
        return Matrix(tuple(tuple(row[n:]) for row in a))

    def determinant(self) -> Fraction:
        n, m = self.shape
        if n != m:
            raise ValueError("Determinante exige matriz quadrada")
        a = [list(row) for row in self.rows]
        determinant = Fraction(1)
        for j in range(n):
            pivot = next((i for i in range(j, n) if a[i][j] != 0), None)
            if pivot is None:
                return Fraction(0)
            if pivot != j:
                a[j], a[pivot] = a[pivot], a[j]
                determinant = -determinant
            p = a[j][j]
            determinant *= p
            for i in range(j + 1, n):
                c = a[i][j] / p
                for t in range(j + 1, n):
                    a[i][t] -= c * a[j][t]
        return determinant


@dataclass(frozen=True)
class InnerProductSpace:
    """Produto interno racional com matriz de Gram simétrica positiva definida."""

    vector_space: VectorSpace
    gram: Matrix

    def __post_init__(self):
        d = self.vector_space.dimension
        if self.gram.shape != (d, d) or self.gram != self.gram.transpose():
            raise ValueError("Matriz de Gram precisa ser simétrica e d × d")
        # Critério de Sylvester (válido sobre os racionais ordenados).
        for k in range(1, d + 1):
            principal = Matrix(tuple(tuple(self.gram.rows[i][j] for j in range(k))
                                     for i in range(k)))
            if principal.determinant() <= 0:
                raise ValueError("Produto interno exige Gram positiva definida")

    def inner(self, u: Vector, v: Vector) -> Fraction:
        if u.dim != self.vector_space.dimension or v.dim != u.dim:
            raise ValueError("Vetores fora do espaço")
        return u.dot(self.gram @ v)

    def norm_squared(self, v: Vector) -> Fraction:
        return self.inner(v, v)

    def riesz(self, functional: LinearFunctional) -> Vector:
        """Resolve Gv = α. Isto é identificação métrica V* → V."""
        if functional.space != self.vector_space:
            raise ValueError("O funcional pertence a outro espaço")
        return self.gram.inverse() @ functional.coefficients


@dataclass(frozen=True)
class LinearFunctional:
    """Elemento de V*: forma linear α(v) = Σ α_i v_i."""

    space: VectorSpace
    coefficients: Vector

    def __post_init__(self):
        if self.space.dimension != self.coefficients.dim:
            raise ValueError("Dimensão errada do espaço dual")

    def __call__(self, vector: Vector) -> Fraction:
        if vector.dim != self.space.dimension:
            raise ValueError("Vetor fora do domínio")
        return self.coefficients.dot(vector)


@dataclass(frozen=True)
class DualSpace:
    primal: VectorSpace

    def element(self, *coefficients: int | str | Fraction) -> LinearFunctional:
        return LinearFunctional(self.primal, self.primal.element(*coefficients))


@dataclass(frozen=True)
class LinearOperator:
    domain: VectorSpace
    codomain: VectorSpace
    matrix: Matrix

    def __post_init__(self):
        if self.matrix.shape != (self.codomain.dimension, self.domain.dimension):
            raise ValueError("Matriz incompatível com o morfismo linear")

    def __call__(self, vector: Vector) -> Vector:
        if vector.dim != self.domain.dimension:
            raise ValueError("Vetor do domínio incorreto")
        return self.matrix @ vector

    def compose(self, other: LinearOperator) -> LinearOperator:
        if other.codomain != self.domain:
            raise ValueError("Domínio/codomínio não são composicionais")
        return LinearOperator(other.domain, self.codomain, self.matrix @ other.matrix)


class MatrixLieAlgebra:
    """gl(n,ℚ), com colchete [A,B] = AB - BA e identidade de Jacobi."""

    @staticmethod
    def bracket(a: Matrix, b: Matrix) -> Matrix:
        if a.shape != b.shape or a.shape[0] != a.shape[1]:
            raise ValueError("Geradores devem ser matrizes quadradas do mesmo tamanho")
        return a @ b - b @ a


# ──────────────────────────────────────────────────────────────────────────
# ESTRATO 1 — ATLAS AFIM, FIBRADOS, ESTRUTURA SIMPLÉTICA
# ──────────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class AffineChart:
    """Carta global φ(x)=Ax+b; transições são difeomorfismos afins suaves."""

    linear: Matrix
    offset: Vector

    def __post_init__(self):
        if self.linear.shape != (self.offset.dim, self.offset.dim):
            raise ValueError("Uma carta precisa ser endomorfismo quadrado")
        self.linear.inverse()  # prova computacional exata da invertibilidade

    def coordinates(self, x: Vector) -> Vector:
        return self.linear @ x + self.offset

    def inverse_coordinates(self, c: Vector) -> Vector:
        return self.linear.inverse() @ (c - self.offset)


@dataclass(frozen=True)
class AffineManifold:
    """M = ℚ^n com atlas global afim; NÃO representa variedades arbitrárias."""

    ambient: VectorSpace
    atlas: tuple[AffineChart, ...]

    def __post_init__(self):
        if not self.atlas or any(ch.offset.dim != self.ambient.dimension for ch in self.atlas):
            raise ValueError("É necessário atlas não vazio da dimensão correta")

    def transition(self, source: int, target: int, coords: Vector) -> Vector:
        return self.atlas[target].coordinates(self.atlas[source].inverse_coordinates(coords))


@dataclass(frozen=True)
class TangentVector:
    point: Vector
    components: Vector

    def in_chart(self, chart: AffineChart) -> Vector:
        """Componentes contravariantes v' = Av."""
        return chart.linear @ self.components


@dataclass(frozen=True)
class CotangentVector:
    point: Vector
    coefficients: Vector

    def in_chart(self, chart: AffineChart) -> Vector:
        """Componentes covariantes α' = (A⁻¹)^T α."""
        return chart.linear.inverse().transpose() @ self.coefficients

    def pair(self, tangent: TangentVector) -> Fraction:
        if self.point != tangent.point:
            raise ValueError("Emparelhamento deve ocorrer na mesma fibra")
        return self.coefficients.dot(tangent.components)


@dataclass(frozen=True)
class TangentBundle:
    manifold: AffineManifold

    def element(self, point: Vector, velocity: Vector) -> TangentVector:
        d = self.manifold.ambient.dimension
        if point.dim != d or velocity.dim != d:
            raise ValueError("Dimensão de TM incompatível")
        return TangentVector(point, velocity)


@dataclass(frozen=True)
class CotangentBundle:
    manifold: AffineManifold

    def element(self, point: Vector, covector: Vector) -> CotangentVector:
        d = self.manifold.ambient.dimension
        if point.dim != d or covector.dim != d:
            raise ValueError("Dimensão de T*M incompatível")
        return CotangentVector(point, covector)


@dataclass(frozen=True)
class Polynomial:
    """Elemento canônico de ℚ[x_0,...,x_(n-1)] sem erros de arredondamento.

    Um monômio é (expoentes, coeficiente). Termos repetidos são somados;
    coeficientes nulos são eliminados. Identidade de polinômios é decidível
    por comparação dos termos normalizados.
    """

    dimension: int
    terms: tuple[tuple[tuple[int, ...], Fraction], ...] = ()

    def __post_init__(self):
        if self.dimension < 1:
            raise ValueError("Polinômio precisa de pelo menos uma variável")
        result: dict[tuple[int, ...], Fraction] = {}
        for powers, coefficient in self.terms:
            powers = tuple(powers)
            if len(powers) != self.dimension or any(not isinstance(p, int) or p < 0 for p in powers):
                raise ValueError("Monômio possui expoentes inválidos")
            result[powers] = result.get(powers, Fraction(0)) + Q(coefficient)
        object.__setattr__(self, "terms", tuple(sorted((p, c) for p, c in result.items() if c)))

    @classmethod
    def constant(cls, n: int, c: int | str | Fraction) -> Polynomial:
        return cls(n, (((0,) * n, Q(c)),))

    @classmethod
    def variable(cls, n: int, i: int) -> Polynomial:
        if not 0 <= i < n:
            raise ValueError("Índice da variável inexistente")
        powers = tuple(int(j == i) for j in range(n))
        return cls(n, ((powers, Fraction(1)),))

    @property
    def is_zero(self) -> bool:
        return not self.terms

    def _same(self, other: Polynomial):
        if self.dimension != other.dimension:
            raise ValueError("Anéis polinomiais diferentes")

    def __add__(self, other: Polynomial | int | str | Fraction) -> Polynomial:
        if not isinstance(other, Polynomial):
            other = Polynomial.constant(self.dimension, other)
        self._same(other)
        return Polynomial(self.dimension, self.terms + other.terms)

    __radd__ = __add__

    def __neg__(self) -> Polynomial:
        return Polynomial(self.dimension, tuple((p, -c) for p, c in self.terms))

    def __sub__(self, other: Polynomial | int | str | Fraction) -> Polynomial:
        return self + (-other if isinstance(other, Polynomial) else -Q(other))

    def __rsub__(self, other: int | str | Fraction) -> Polynomial:
        return (-self) + other

    def __mul__(self, other: Polynomial | int | str | Fraction) -> Polynomial:
        if not isinstance(other, Polynomial):
            other = Polynomial.constant(self.dimension, other)
        self._same(other)
        terms = []
        for powers_a, ca in self.terms:
            for powers_b, cb in other.terms:
                terms.append((tuple(a + b for a, b in zip(powers_a, powers_b)), ca * cb))
        return Polynomial(self.dimension, tuple(terms))

    __rmul__ = __mul__

    def __truediv__(self, scalar: int | str | Fraction) -> Polynomial:
        return self * (1 / Q(scalar))

    def __pow__(self, power: int) -> Polynomial:
        if not isinstance(power, int) or power < 0:
            raise ValueError("O expoente polinomial deve ser inteiro não-negativo")
        ans = Polynomial.constant(self.dimension, 1)
        base = self
        while power:
            if power & 1:
                ans = ans * base
            base = base * base
            power >>= 1
        return ans

    def diff(self, index: int) -> Polynomial:
        if not 0 <= index < self.dimension:
            raise ValueError("Variável de derivação fora do anel")
        terms = []
        for p, c in self.terms:
            if p[index]:
                new_p = list(p)
                new_p[index] -= 1
                terms.append((tuple(new_p), c * p[index]))
        return Polynomial(self.dimension, tuple(terms))

    def evaluate(self, coordinates: Sequence[Fraction | float | int]) -> Fraction | float:
        if len(coordinates) != self.dimension:
            raise ValueError("Coordenadas incompatíveis com o polinômio")
        return sum((c * math.prod(x ** p for x, p in zip(coordinates, exponents))
                    for exponents, c in self.terms), Fraction(0))

    def substitute(self, images: Sequence[Polynomial]) -> Polynomial:
        if len(images) != self.dimension or any(p.dimension != self.dimension for p in images):
            raise ValueError("Substituição deve ser um endomorfismo do anel")
        result = Polynomial.constant(self.dimension, 0)
        for powers, coeff in self.terms:
            term = Polynomial.constant(self.dimension, coeff)
            for image, exponent in zip(images, powers):
                if exponent:
                    term = term * (image ** exponent)
            result = result + term
        return result

    def expression(self, symbols: Sequence[str] | None = None) -> str:
        """Representação legível de uma identidade; não envolve avaliação."""
        names = symbols or tuple(f"x{i}" for i in range(self.dimension))
        if len(names) != self.dimension:
            raise ValueError("Número errado de símbolos")
        if self.is_zero:
            return "0"
        chunks = []
        for powers, c in sorted(self.terms, key=lambda t: (-sum(t[0]), t[0])):
            variables = "*".join(f"{name}^{p}" if p != 1 else name
                                  for name, p in zip(names, powers) if p)
            coefficient = ("" if c == 1 and variables else "-" if c == -1 and variables else str(c))
            chunks.append(coefficient + ("*" if variables and coefficient not in ("", "-") else "") + variables)
        return " + ".join(chunks).replace("+ -", "- ")


@dataclass(frozen=True)
class SymplecticSpace:
    """(ℚ^(2n), ω); ω = Σ dq_i∧dp_i, matriz J=[0 I; -I 0]."""

    pairs: int
    J: Matrix = field(init=False)

    def __post_init__(self):
        if self.pairs < 1:
            raise ValueError("Espaço de fase requer pelo menos um par (q,p)")
        n = self.pairs
        j = Matrix(tuple(tuple(int(i + n == k) - int(k + n == i)
                               for k in range(2 * n)) for i in range(2 * n)))
        object.__setattr__(self, "J", j)
        assert j.transpose() == -j
        assert j @ j == Matrix.identity(2 * n).scale(-1)

    @property
    def dimension(self) -> int:
        return 2 * self.pairs

    def omega(self, u: Vector, v: Vector) -> Fraction:
        if u.dim != self.dimension or v.dim != self.dimension:
            raise ValueError("Vetores de fase de dimensão incorreta")
        return u.dot(self.J @ v)

    def is_symplectic(self, linear: Matrix) -> bool:
        return (linear.shape == (self.dimension, self.dimension)
                and linear.transpose() @ self.J @ linear == self.J)

    def poisson(self, f: Polynomial, g: Polynomial) -> Polynomial:
        if f.dimension != self.dimension or g.dimension != self.dimension:
            raise ValueError("Funções não pertencem ao espaço de fase")
        result = Polynomial.constant(self.dimension, 0)
        n = self.pairs
        for i in range(n):
            result += f.diff(i) * g.diff(n + i) - f.diff(n + i) * g.diff(i)
        return result

    def hamiltonian_field(self, h: Polynomial) -> tuple[Polynomial, ...]:
        if h.dimension != self.dimension:
            raise ValueError("Hamiltoniano sobre espaço de fase errado")
        n = self.pairs
        return tuple(h.diff(n + i) for i in range(n)) + tuple(-h.diff(i) for i in range(n))


# ──────────────────────────────────────────────────────────────────────────
# ESTRATO 2 — PROBABILIDADE FINITA E GEOMETRIA DA INFORMAÇÃO
# ──────────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class FiniteProbabilitySpace:
    """(Ω, 2^Ω, P), com massas racionais não-negativas cuja soma é 1."""

    outcomes: tuple[str, ...]
    probabilities: tuple[Fraction, ...]

    def __post_init__(self):
        p = tuple(Q(x) for x in self.probabilities)
        if not p or len(p) != len(self.outcomes) or len(set(self.outcomes)) != len(self.outcomes):
            raise ValueError("Eventos devem ser distintos e corresponder às massas")
        if any(v < 0 for v in p) or sum(p) != 1:
            raise ValueError("Probabilidades devem ser não-negativas e somar 1")
        object.__setattr__(self, "probabilities", p)

    def event_probability(self, event: Iterable[str]) -> Fraction:
        e = set(event)
        if not e.issubset(self.outcomes):
            raise ValueError("Evento fora da sigma-álgebra")
        return sum((p for name, p in zip(self.outcomes, self.probabilities) if name in e), Fraction(0))

    def entropy(self) -> float:
        """Shannon em nats; log é aproximado numericamente."""
        return -sum(float(p) * math.log(float(p)) for p in self.probabilities if p > 0)

    def kl(self, other: FiniteProbabilitySpace) -> float:
        if self.outcomes != other.outcomes:
            raise ValueError("KL exige o mesmo espaço amostral ordenado")
        if any(p > 0 and q == 0 for p, q in zip(self.probabilities, other.probabilities)):
            return math.inf
        return sum(float(p) * math.log(float(p / q)) for p, q in
                   zip(self.probabilities, other.probabilities) if p > 0)

    def fisher_rao_matrix(self) -> Matrix:
        """g_ij=δ_ij/p_i + 1/p_k, em coordenadas p_1,...,p_(k-1).

        Apenas no INTERIOR do simplex. A métrica de Fisher é definida
        no espaço tangente às distribuições, não nos logits redundantes.
        """
        if len(self.probabilities) < 2 or any(p <= 0 for p in self.probabilities):
            raise ValueError("Fisher requer simplex interior com ≥2 estados")
        p = self.probabilities
        n = len(p) - 1
        return Matrix(tuple(tuple(Fraction(int(i == j), 1) / p[i] + 1 / p[-1]
                                  for j in range(n)) for i in range(n)))


# ──────────────────────────────────────────────────────────────────────────
# ESTRATO 3 — DINÂMICA HAMILTONIANA E PASSO SIMPLÉTICO
# ──────────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class HamiltonianFlow:
    phase: SymplecticSpace
    energy: Polynomial

    def __post_init__(self):
        if self.energy.dimension != self.phase.dimension:
            raise ValueError("Energia incompatível com o espaço simplético")

    def velocity(self, z: Vector) -> Vector:
        if z.dim != self.phase.dimension:
            raise ValueError("Estado fora do espaço de fase")
        return Vector(tuple(Q(p.evaluate(z.entries)) for p in self.phase.hamiltonian_field(self.energy)))

    def derivative_of(self, observable: Polynomial) -> Polynomial:
        """d f / dt = {f,H}, identidade exata no anel polinomial."""
        return self.phase.poisson(observable, self.energy)


@dataclass(frozen=True)
class PolynomialMap:
    """φ: ℚ^n → ℚ^n; representação de cada coordenada por polinômio."""

    components: tuple[Polynomial, ...]

    def __post_init__(self):
        d = len(self.components)
        if not d or any(f.dimension != d for f in self.components):
            raise ValueError("Mapa polinomial precisa ser endomorfismo de ℚ^n")

    def __call__(self, z: Vector) -> Vector:
        if z.dim != len(self.components):
            raise ValueError("Estado de dimensão incorreta")
        return Vector(tuple(Q(f.evaluate(z.entries)) for f in self.components))

    def pullback(self, f: Polynomial) -> Polynomial:
        return f.substitute(self.components)

    def is_symplectic(self, phase: SymplecticSpace) -> bool:
        """Certifica Dφ(z)^T J Dφ(z) = J como identidade polinomial GLOBAL."""
        d = len(self.components)
        if phase.dimension != d:
            return False
        derivatives = [[component.diff(i) for i in range(d)] for component in self.components]
        for i in range(d):
            for j in range(d):
                lhs = Polynomial.constant(d, 0)
                for a in range(d):
                    for b in range(d):
                        if phase.J.rows[a][b]:
                            lhs += (derivatives[a][i] * derivatives[b][j]
                                    * phase.J.rows[a][b])
                if lhs != Polynomial.constant(d, phase.J.rows[i][j]):
                    return False
        return True


@dataclass(frozen=True)
class SymplecticEuler:
    """Mapa kick-drift para H(q,p) = T(p)+V(q), com h racional.

    p' = p - h ∂_q H(q,p); q' = q + h ∂_p H(q,p').
    Simplicidade do algoritmo NÃO implica conservação exata da energia.
    """

    flow: HamiltonianFlow
    step_size: Fraction

    def __post_init__(self):
        object.__setattr__(self, "step_size", Q(self.step_size))
        n = self.flow.phase.pairs
        h = self.flow.energy
        if any(not h.diff(i).diff(n + j).is_zero for i in range(n) for j in range(n)):
            raise ValueError("Euler kick-drift exige H separável T(p)+V(q)")

    def as_polynomial_map(self) -> PolynomialMap:
        n = self.flow.phase.pairs
        d = 2 * n
        x = tuple(Polynomial.variable(d, i) for i in range(d))
        h = self.flow.energy
        p_new = tuple(x[n + i] - self.step_size * h.diff(i) for i in range(n))
        substitution = x[:n] + p_new
        q_new = tuple(x[i] + self.step_size * h.diff(n + i).substitute(substitution)
                      for i in range(n))
        return PolynomialMap(q_new + p_new)

    def step(self, state: Vector) -> Vector:
        """Passo calculado numericamente com coeficientes exatos (Fraction)."""
        n = self.flow.phase.pairs
        if state.dim != 2 * n:
            raise ValueError("Estado fora do espaço de fase")
        q = state.entries[:n]
        p = state.entries[n:]
        dH_dq = tuple(self.flow.energy.diff(i).evaluate(state.entries) for i in range(n))
        p_new = tuple(p[i] - self.step_size * dH_dq[i] for i in range(n))
        intermediate = q + p_new
        dH_dp = tuple(self.flow.energy.diff(n + i).evaluate(intermediate) for i in range(n))
        q_new = tuple(q[i] + self.step_size * dH_dp[i] for i in range(n))
        return Vector(q_new + p_new)


# ──────────────────────────────────────────────────────────────────────────
# ESTRATO 4 — MORFISMOS DE ROTEAMENTO E ROTAÇÕES
# ──────────────────────────────────────────────────────────────────────────


class EntropicRouter:
    """Solução única de max_{w∈Δ} Σ_j w_j s_j + τ H(w), τ>0.

    w_j = exp(s_j/τ) / Σ_k exp(s_k/τ). Implementação com float;
    NÃO afirma que atenção genérica preserve forma simplética.
    """

    @staticmethod
    def weights(scores: Sequence[float], temperature: float = 1.0) -> tuple[float, ...]:
        if not scores or not math.isfinite(temperature) or temperature <= 0:
            raise ValueError("Roteamento requer scores e temperatura positiva")
        if any(not math.isfinite(v) for v in scores):
            raise ValueError("Scores devem ser finitos")
        scaled = [s / temperature for s in scores]
        peak = max(scaled)
        exps = [math.exp(s - peak) for s in scaled]
        norm = sum(exps)
        return tuple(v / norm for v in exps)

    @staticmethod
    def attend(query: Sequence[float], keys: Sequence[Sequence[float]],
               values: Sequence[Sequence[float]], temperature: float | None = None) -> tuple[float, ...]:
        if not query or not keys or len(keys) != len(values):
            raise ValueError("Q, K e V devem ser não vazios e ter comprimentos compatíveis")
        d = len(query)
        if any(len(k) != d for k in keys):
            raise ValueError("Chaves incompatíveis com consulta")
        v_dim = len(values[0])
        if not v_dim or any(len(v) != v_dim for v in values):
            raise ValueError("Valores precisam ter dimensão comum")
        tau = math.sqrt(d) if temperature is None else temperature
        scores = [sum(a * b for a, b in zip(query, key)) for key in keys]
        w = EntropicRouter.weights(scores, tau)
        return tuple(sum(w[i] * values[i][j] for i in range(len(values)))
                     for j in range(v_dim))


@dataclass(frozen=True)
class RotarySO2:
    """Soma direta de representações 2D de SO(2), no emparelhamento split-half."""

    dimension: int
    base: float = 10000.0

    def __post_init__(self):
        if self.dimension < 2 or self.dimension % 2 or not math.isfinite(self.base) or self.base <= 0:
            raise ValueError("RoPE exige dimensão par e base positiva")

    def apply(self, v: Sequence[float], position: float) -> tuple[float, ...]:
        if len(v) != self.dimension:
            raise ValueError("Dimensão errada do embedding")
        half = self.dimension // 2
        left, right = [], []
        for i in range(half):
            angle = position * self.base ** (-2 * i / self.dimension)
            c, s = math.cos(angle), math.sin(angle)
            left.append(c * v[i] - s * v[i + half])
            right.append(s * v[i] + c * v[i + half])
        return tuple(left + right)


# ──────────────────────────────────────────────────────────────────────────
# ESTRATO 5 — NOETHER E DESCOBERTA EXATA DE INVARIANTES
# ──────────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class ConservationCertificate:
    observable: Polynomial
    hamiltonian: Polynomial
    bracket: Polynomial

    @property
    def verified(self) -> bool:
        """Certificado: {F,H}=0 em ℚ[q,p], não apenas em pontos amostrados."""
        return self.bracket.is_zero


@dataclass(frozen=True)
class NoetherEngine:
    phase: SymplecticSpace

    def certify(self, charge: Polynomial, energy: Polynomial) -> ConservationCertificate:
        return ConservationCertificate(charge, energy, self.phase.poisson(charge, energy))

    def cotangent_lift_angular_momentum(self) -> Polynomial:
        """Momento mapa para a ação SO(2): δq=(-q_y,q_x), L=p·δq.

        Requer dois graus de liberdade, z=(qx,qy,px,py).
        """
        if self.phase.pairs != 2:
            raise ValueError("Gerador SO(2) implementado para dois pares (q,p)")
        qx, qy, px, py = (Polynomial.variable(4, i) for i in range(4))
        return px * (-qy) + py * qx

    def symmetry_certificate(self, generator: Polynomial, energy: Polynomial) -> Polynomial:
        """Derivada de Lie X_generator[H] = {H,generator}; 0 indica simetria."""
        return self.phase.poisson(energy, generator)


class SymbolicCrystallizer:
    """Encontra integrais polinomiais resolvendo ker(F ↦ {F,H}) por ℚ-RREF.

    Busca limitada por grau; completa SOMENTE dentro do ansatz escolhido.
    Não induz automaticamente leis arbitrárias ou transcendentes.
    """

    @staticmethod
    def _nullspace(columns: Sequence[Polynomial]) -> tuple[tuple[Fraction, ...], ...]:
        n = len(columns)
        if n == 0:
            return ()
        monomials = sorted({powers for col in columns for powers, _ in col.terms})
        if not monomials:
            return tuple(tuple(Fraction(int(i == j)) for i in range(n)) for j in range(n))
        cd = [dict(col.terms) for col in columns]
        a = [[d.get(m, Fraction(0)) for d in cd] for m in monomials]
        row, pivots = 0, []
        for column in range(n):
            pivot = next((r for r in range(row, len(a)) if a[r][column]), None)
            if pivot is None:
                continue
            a[row], a[pivot] = a[pivot], a[row]
            scale = a[row][column]
            a[row] = [x / scale for x in a[row]]
            for r in range(len(a)):
                if r != row:
                    scale = a[r][column]
                    if scale:
                        a[r] = [x - scale * y for x, y in zip(a[r], a[row])]
            pivots.append(column)
            row += 1
            if row == len(a):
                break
        free = [j for j in range(n) if j not in pivots]
        basis = []
        for col in free:
            v = [Fraction(0)] * n
            v[col] = Fraction(1)
            for r, pivot_col in enumerate(pivots):
                v[pivot_col] = -a[r][col]
            basis.append(tuple(v))
        return tuple(basis)

    @staticmethod
    def _primitive(f: Polynomial) -> Polynomial:
        """Normaliza uma expressão proporcional por coeficientes inteiros primitivos."""
        if f.is_zero:
            return f
        den = math.lcm(*(c.denominator for _, c in f.terms))
        integers = [int(c * den) for _, c in f.terms]
        divisor = reduce(math.gcd, (abs(c) for c in integers))
        sign = 1 if integers[0] > 0 else -1
        return f * Fraction(sign * den, divisor)

    def discover(self, phase: SymplecticSpace, energy: Polynomial,
                 maximum_degree: int = 2) -> tuple[Polynomial, ...]:
        if maximum_degree < 1 or energy.dimension != phase.dimension:
            raise ValueError("Grau ou espaço de fase inválido")
        n = phase.dimension
        exponents = [p for p in itertools.product(range(maximum_degree + 1), repeat=n)
                     if 1 <= sum(p) <= maximum_degree]
        exponents.sort(key=lambda p: (sum(p), p))
        basis = [Polynomial(n, ((p, Fraction(1)),)) for p in exponents]
        kernel = self._nullspace([phase.poisson(f, energy) for f in basis])
        candidates = []
        for weights in kernel:
            candidate = Polynomial.constant(n, 0)
            for w, monomial in zip(weights, basis):
                if w:
                    candidate += monomial * w
            candidate = self._primitive(candidate)
            assert phase.poisson(candidate, energy).is_zero
            if not candidate.is_zero and candidate not in candidates:
                candidates.append(candidate)
        return tuple(candidates)


# ──────────────────────────────────────────────────────────────────────────
# EXPERIÊNCIA REPRODUZÍVEL + AUTOTESTES (biblioteca padrão)
# ──────────────────────────────────────────────────────────────────────────


def canonical_example():
    """Oscilador central ANARMÔNICO; quebra degenerescência de leis quadráticas.

    H = (px²+py²)/2 + (qx²+qy²)/2 + (qx²+qy²)²/4.
    A invariância por SO(2) conduz a L = qx py - qy px.
    """
    phase = SymplecticSpace(2)
    qx, qy, px, py = (Polynomial.variable(4, i) for i in range(4))
    r2 = qx**2 + qy**2
    h = (px**2 + py**2) / 2 + r2 / 2 + r2**2 / 4
    return phase, h


class AxiomaticTests(unittest.TestCase):
    def test_rational_field_and_vector_axioms(self):
        space = VectorSpace(3)
        u, v, w = space.element(1, 2, -3), space.element(2, -1, 4), space.element(3, 5, 1)
        self.assertEqual((u + v) + w, u + (v + w))
        self.assertEqual(u + v, v + u)
        self.assertEqual(u + (-u), space.zero())
        self.assertEqual(u.scale(3) + u.scale(-2), u)
        self.assertEqual((u + v).scale(2), u.scale(2) + v.scale(2))
        with self.assertRaises(TypeError):
            Q(0.1)

    def test_matrix_inverse_and_lie_jacobi(self):
        a = Matrix(((1, 2), (3, 5)))
        b = Matrix(((0, 1), (-1, 0)))
        c = Matrix(((2, 0), (1, -1)))
        self.assertEqual(a @ a.inverse(), Matrix.identity(2))
        self.assertEqual(a.determinant(), -1)
        bracket = MatrixLieAlgebra.bracket
        self.assertEqual(bracket(a, bracket(b, c)) + bracket(b, bracket(c, a))
                         + bracket(c, bracket(a, b)), Matrix.zero(2, 2))

    def test_gram_and_riesz(self):
        space = VectorSpace(2)
        inner = InnerProductSpace(space, Matrix(((2, 1), (1, 3))))
        alpha = DualSpace(space).element(5, 7)
        u = space.element(2, -3)
        self.assertEqual(inner.inner(inner.riesz(alpha), u), alpha(u))
        self.assertGreater(inner.norm_squared(u), 0)
        with self.assertRaises(ValueError):
            InnerProductSpace(space, Matrix(((1, 2), (2, 1))))

    def test_atlas_and_tangent_cotangent_pairing(self):
        sp = VectorSpace(2)
        chart = AffineChart(Matrix(((2, 1), (0, 3))), sp.element(1, -2))
        manifold = AffineManifold(sp, (AffineChart(Matrix.identity(2), sp.zero()), chart))
        point, velocity, covector = sp.element(1, 2), sp.element(3, 4), sp.element(5, 7)
        tangent = TangentBundle(manifold).element(point, velocity)
        cotangent = CotangentBundle(manifold).element(point, covector)
        self.assertEqual(chart.inverse_coordinates(chart.coordinates(point)), point)
        self.assertEqual(cotangent.pair(tangent), cotangent.in_chart(chart).dot(tangent.in_chart(chart)))
        self.assertEqual(manifold.transition(0, 1, point), chart.coordinates(point))

    def test_symplectic_axioms_and_poisson(self):
        phase = SymplecticSpace(2)
        j = phase.J
        self.assertEqual(j.transpose(), -j)
        self.assertEqual(j @ j, -Matrix.identity(4))
        self.assertTrue(phase.is_symplectic(j))
        x = [Polynomial.variable(4, i) for i in range(4)]
        self.assertEqual(phase.poisson(x[0], x[2]), Polynomial.constant(4, 1))
        self.assertEqual(phase.poisson(x[2], x[0]), Polynomial.constant(4, -1))
        self.assertTrue(phase.poisson(x[0], x[0]).is_zero)
        self.assertEqual(phase.poisson(x[0], x[1]), Polynomial.constant(4, 0))

    def test_probability_measure_and_fisher(self):
        p = FiniteProbabilitySpace(("a", "b", "c"), (Fraction(1, 2), Fraction(1, 3), Fraction(1, 6)))
        self.assertEqual(p.event_probability(("a", "c")), Fraction(2, 3))
        self.assertAlmostEqual(p.kl(p), 0.0)
        self.assertGreater(p.entropy(), 0)
        self.assertEqual(p.fisher_rao_matrix(), Matrix(((8, 6), (6, 9))))
        self.assertEqual(p.fisher_rao_matrix().determinant(), 36)
        q = FiniteProbabilitySpace(("a", "b", "c"), (0, 1, 0))
        self.assertEqual(p.kl(q), math.inf)

    def test_rope_group_action_and_entropy_router(self):
        rope = RotarySO2(4)
        v = (1.0, 2.0, -3.0, 4.0)
        a = rope.apply(rope.apply(v, 2), 3)
        b = rope.apply(v, 5)
        for x, y in zip(a, b):
            self.assertAlmostEqual(x, y, places=12)
        self.assertAlmostEqual(sum(x*x for x in v), sum(x*x for x in b), places=12)
        w = EntropicRouter.weights((1.0, 2.0, 3.0))
        self.assertAlmostEqual(sum(w), 1.0)
        self.assertGreater(w[2], w[1])
        self.assertEqual(EntropicRouter.attend((0., 0.), ((1., 0.), (0., 1.)),
                                               ((1., 3.), (3., 1.))), (2., 2.))

    def test_noether_and_crystallizer(self):
        phase, h = canonical_example()
        engine = NoetherEngine(phase)
        charge = engine.cotangent_lift_angular_momentum()
        self.assertTrue(engine.certify(charge, h).verified)
        self.assertTrue(engine.symmetry_certificate(charge, h).is_zero)
        found = SymbolicCrystallizer().discover(phase, h, maximum_degree=2)
        self.assertEqual(len(found), 1)  # Para este H genérico, só L no grau ≤2.
        self.assertTrue(found[0] == charge or found[0] == -charge)

    def test_symplectic_euler_certificates(self):
        phase, h = canonical_example()
        integrator = SymplecticEuler(HamiltonianFlow(phase, h), Fraction(1, 10))
        phi = integrator.as_polynomial_map()
        self.assertTrue(phi.is_symplectic(phase))  # identidade GLOBAL, não amostragem
        angular = NoetherEngine(phase).cotangent_lift_angular_momentum()
        self.assertEqual(phi.pullback(angular), angular)  # lei discreta exata
        self.assertNotEqual(phi.pullback(h), h)  # energia não é exatamente conservada
        z = Vector((1, 2, 3, 5))
        self.assertEqual(integrator.step(z), phi(z))
        energy_initial = h.evaluate(z.entries)
        for _ in range(5):
            z = integrator.step(z)
            self.assertEqual(angular.evaluate(z.entries), Fraction(-1))
        self.assertNotEqual(h.evaluate(z.entries), energy_initial)

    def test_negative_cross_hamiltonian(self):
        phase = SymplecticSpace(1)
        q, p = Polynomial.variable(2, 0), Polynomial.variable(2, 1)
        with self.assertRaises(ValueError):
            SymplecticEuler(HamiltonianFlow(phase, q * p), Fraction(1, 10))


def demo():
    print("ML-MATHLIB — Estratos 0→5, núcleo verificável sobre ℚ")
    phase, h = canonical_example()
    engine = NoetherEngine(phase)
    symbols = ("qx", "qy", "px", "py")
    print("Hamiltoniano H =", h.expression(symbols))
    print("1. Descoberta: buscando invariantes de grau 1 e 2, sem fornecer L...")
    found = SymbolicCrystallizer().discover(phase, h, 2)
    for i, invariant in enumerate(found, 1):
        proof = engine.certify(invariant, h)
        print(f"   F{i} = {invariant.expression(symbols)}")
        print(f"   {{F{i}, H}} = {proof.bracket.expression(symbols)} | provado: {proof.verified}")
    charge = engine.cotangent_lift_angular_momentum()
    print("2. Noether: gerador de rotações infinitesimais →")
    print("   L =", charge.expression(symbols))
    print("   X_L[H] =", engine.symmetry_certificate(charge, h).expression(symbols))
    flow = HamiltonianFlow(phase, h)
    print("3. Campo contínuo X_H(z) =", tuple(p.expression(symbols) for p in phase.hamiltonian_field(h)))
    stepper = SymplecticEuler(flow, Fraction(1, 10))
    phi = stepper.as_polynomial_map()
    print("4. Passo simplético (h=1/10):")
    print("   DΦᵀ J DΦ = J (identidade polinomial):", phi.is_symplectic(phase))
    print("   L∘Φ - L =", (phi.pullback(charge) - charge).expression(symbols))
    print("   H∘Φ - H = 0 ?", phi.pullback(h) == h)
    z = Vector((1, 2, 3, 5))
    print("5. Evolução exata com frações; estados exibidos em decimais:")
    print("   passo |        H(z)       |      L(z)")
    for k in range(6):
        print(f"   {k:>5} | {float(h.evaluate(z.entries)):>17.9f} | {str(charge.evaluate(z.entries)):>12}")
        z = stepper.step(z)
    print("Resultado: L é invariante exato; H geralmente oscila no passo discreto.")


def main():
    parser = argparse.ArgumentParser(description="ML-MATHLIB: álgebra e invariantes exatos")
    parser.add_argument("--test", action="store_true", help="Executa a suíte de axiomas e certificados")
    parser.add_argument("--demo", action="store_true", help="Executa a prova de fogo de Noether")
    args = parser.parse_args()
    if args.test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(AxiomaticTests)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        if not result.wasSuccessful():
            raise SystemExit(1)
    if args.demo or not args.test:
        demo()


if __name__ == "__main__":
    main()
