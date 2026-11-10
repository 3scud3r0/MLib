"""Exact rectangular linear algebra with independently checkable witnesses.

Certificates prove E A = R and E E_inv = I over Q. RREF then certifies rank,
the complete nullspace and either an affine solution space or inconsistency.
This module makes no claim of modular acceleration or Lean verification.
"""
from dataclasses import dataclass
from fractions import Fraction
import json

from ml_mathlib import Matrix, Vector, Q


def _pivots(reduced):
    """Validate reduced row echelon form, without performing elimination."""
    pivots = []
    zero_seen = False
    for row in reduced.rows:
        pivot = next((j for j, value in enumerate(row) if value), None)
        if pivot is None:
            zero_seen = True
            continue
        if zero_seen or (pivots and pivot <= pivots[-1]) or row[pivot] != 1:
            raise ValueError('Not reduced row echelon form')
        pivots.append(pivot)
    for i, pivot in enumerate(pivots):
        if any(row[pivot] != int(i == k) for k, row in enumerate(reduced.rows)):
            raise ValueError('Pivot column is not a unit vector')
    return tuple(pivots)


@dataclass(frozen=True)
class LinearSystemCertificate:
    matrix: Matrix
    rhs: Vector
    reduced: Matrix
    transform: Matrix
    inverse_transform: Matrix
    particular: Vector | None
    kernel: tuple[Vector, ...]
    inconsistency: Vector | None

    @property
    def rank(self):
        return len(_pivots(self.reduced))

    @property
    def consistent(self):
        return self.particular is not None

    def verify(self):
        """Check identities and completeness; never invoke the solver."""
        try:
            m, n = self.matrix.shape
            if (self.rhs.dim != m or self.reduced.shape != (m, n)
                    or self.transform.shape != (m, m)
                    or self.inverse_transform.shape != (m, m)):
                return False
            if self.transform @ self.inverse_transform != Matrix.identity(m):
                return False
            if self.transform @ self.matrix != self.reduced:
                return False
            pivots = _pivots(self.reduced)
            free = tuple(j for j in range(n) if j not in pivots)
            if len(self.kernel) != len(free):
                return False
            zero = Vector((0,) * m)
            for k, vector in enumerate(self.kernel):
                if vector.dim != n or self.matrix @ vector != zero:
                    return False
                if any(vector.entries[j] != int(k == i) for i, j in enumerate(free)):
                    return False
            transformed_rhs = self.transform @ self.rhs
            consistent = not any(transformed_rhs.entries[len(pivots):])
            if consistent:
                return (self.inconsistency is None and self.particular is not None
                        and self.particular.dim == n
                        and self.matrix @ self.particular == self.rhs)
            witness = self.inconsistency
            return (self.particular is None and witness is not None
                    and witness.dim == m
                    and self.matrix.transpose() @ witness == Vector((0,) * n)
                    and sum((x*y for x, y in zip(witness.entries, self.rhs.entries)), Q(0)) != 0)
        except (ValueError, TypeError, AttributeError, IndexError):
            return False

    def to_json(self):
        """Canonical version 1 encoding: rationals are reduced strings."""
        rows = lambda matrix: [[str(x) for x in row] for row in matrix.rows]
        vector = lambda value: None if value is None else [str(x) for x in value.entries]
        return json.dumps(dict(schema='mlib.linear-system', version=1,
            matrix=rows(self.matrix), rhs=vector(self.rhs), reduced=rows(self.reduced),
            transform=rows(self.transform), inverse_transform=rows(self.inverse_transform),
            particular=vector(self.particular), kernel=[vector(v) for v in self.kernel],
            inconsistency=vector(self.inconsistency)), sort_keys=True, separators=(',', ':'))

    @classmethod
    def from_json(cls, source, *, max_bytes=1_000_000, max_entries=100_000):
        """Parse bounded untrusted input. Parsing does not establish validity."""
        if not isinstance(source, str) or len(source.encode('utf-8')) > max_bytes:
            raise ValueError('Certificate exceeds byte budget')
        def unique(pairs):
            result = {}
            for key, value in pairs:
                if key in result:
                    raise ValueError('Duplicate certificate field')
                result[key] = value
            return result
        try:
            data = json.loads(source, object_pairs_hook=unique)
            fields = {'schema', 'version', 'matrix', 'rhs', 'reduced', 'transform',
                      'inverse_transform', 'particular', 'kernel', 'inconsistency'}
            if (not isinstance(data, dict) or set(data) != fields
                    or data['schema'] != 'mlib.linear-system'
                    or type(data['version']) is not int or data['version'] != 1):
                raise ValueError('Unknown certificate schema')
            count = 0
            def scalar(value):
                nonlocal count
                count += 1
                if count > max_entries or not isinstance(value, str) or len(value) > 1024:
                    raise ValueError('Invalid rational or entry budget exceeded')
                result = Fraction(value)
                if str(result) != value:
                    raise ValueError('Noncanonical rational')
                return result
            def vector(value):
                if not isinstance(value, list) or len(value) > max_entries:
                    raise ValueError('Expected vector')
                return Vector(tuple(scalar(x) for x in value))
            def matrix(value):
                if not isinstance(value, list) or not value or len(value) > max_entries:
                    raise ValueError('Expected matrix')
                return Matrix(tuple(vector(row).entries for row in value))
            if not isinstance(data['kernel'], list) or len(data['kernel']) > max_entries:
                raise ValueError('Expected kernel basis')
            return cls(matrix(data['matrix']), vector(data['rhs']), matrix(data['reduced']),
                       matrix(data['transform']), matrix(data['inverse_transform']),
                       None if data['particular'] is None else vector(data['particular']),
                       tuple(vector(v) for v in data['kernel']),
                       None if data['inconsistency'] is None else vector(data['inconsistency']))
        except (TypeError, KeyError, ZeroDivisionError, RecursionError) as error:
            raise ValueError('Malformed linear certificate') from error


def exact_linear_solve(matrix, rhs, *, max_cells=1_000_000):
    """Solve any nonempty rational matrix, including rank zero and singular A.

    Uses rational Gauss-Jordan with row pivoting. Storage is bounded before
    allocation; coefficient growth and CPU are not bounded by this cell limit.
    A consistent result represents x = particular + span(kernel).
    """
    m, n = matrix.shape
    if rhs.dim != m:
        raise ValueError('RHS dimension does not match matrix')
    if type(max_cells) is not int or max_cells < 1:
        raise ValueError('Positive integer cell budget required')
    if m*n + 2*m*m > max_cells:
        raise MemoryError('Elimination exceeds cell budget')
    a = [list(row) for row in matrix.rows]
    e = [list(row) for row in Matrix.identity(m).rows]
    inverse = [list(row) for row in Matrix.identity(m).rows]
    pivots = []
    for j in range(n):
        r = len(pivots)
        p = next((i for i in range(r, m) if a[i][j]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        e[r], e[p] = e[p], e[r]
        for row in inverse:
            row[r], row[p] = row[p], row[r]
        scale = a[r][j]
        a[r] = [x/scale for x in a[r]]
        e[r] = [x/scale for x in e[r]]
        for row in inverse:
            row[r] *= scale
        for i in range(m):
            if i == r:
                continue
            scale = a[i][j]
            if scale:
                a[i] = [x-scale*y for x, y in zip(a[i], a[r])]
                e[i] = [x-scale*y for x, y in zip(e[i], e[r])]
                for row in inverse:
                    row[r] += scale*row[i]
        pivots.append(j)
        if len(pivots) == m:
            break
    transform = Matrix(tuple(tuple(row) for row in e))
    b = (transform @ rhs).entries
    bad = next((i for i in range(len(pivots), m) if b[i]), None)
    particular = [Q(0)] * n
    for i, j in enumerate(pivots):
        particular[j] = b[i]
    kernel = []
    for j in range(n):
        if j in pivots:
            continue
        v = [Q(0)] * n
        v[j] = Q(1)
        for i, p in enumerate(pivots):
            v[p] = -a[i][j]
        kernel.append(Vector(tuple(v)))
    result = LinearSystemCertificate(matrix, rhs, Matrix(tuple(tuple(row) for row in a)),
        transform, Matrix(tuple(tuple(row) for row in inverse)),
        Vector(tuple(particular)) if bad is None else None, tuple(kernel),
        None if bad is None else Vector(tuple(e[bad])))
    if not result.verify():
        raise ArithmeticError('Internal linear certificate verification failed')
    return result


def verify_linear_certificate(source, **budgets):
    """Reject invalid or oversized serialized witnesses without trusting a solver."""
    try:
        return LinearSystemCertificate.from_json(source, **budgets).verify()
    except (ValueError, TypeError, OverflowError):
        return False
