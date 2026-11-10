"""Linear algebra acceptance checks, hostile certificates and sparse integration."""
from dataclasses import replace
from fractions import Fraction as F
from itertools import product
import json
import random
import unittest
from unittest.mock import patch

from ml_mathlib import Matrix, Vector, Polynomial, SymplecticSpace, SymbolicCrystallizer
from ml_mathlib_linear import exact_linear_solve, verify_linear_certificate


class LinearTests(unittest.TestCase):
    def solve(self, rows, rhs, rank, consistent):
        result = exact_linear_solve(Matrix(rows), Vector(rhs))
        self.assertTrue(result.verify())
        self.assertEqual(result.rank, rank)
        self.assertEqual(result.consistent, consistent)
        self.assertEqual(len(result.kernel), len(rows[0])-rank)
        self.assertTrue(verify_linear_certificate(result.to_json()))
        return result

    def test_underdetermined(self):
        c = self.solve(((1, 2, 3), (2, 4, 6)), (1, 2), 1, True)
        for a, b in product(range(-2, 3), repeat=2):
            x = Vector(tuple(x+a*u+b*v for x, u, v in
                             zip(c.particular.entries, c.kernel[0].entries, c.kernel[1].entries)))
            self.assertEqual(c.matrix @ x, c.rhs)

    def test_overdetermined(self):
        self.solve(((0, 1), (1, 0), (2, 3)), (2, 1, 8), 2, True)

    def test_singular_inconsistent(self):
        self.solve(((1, 2), (2, 4)), (1, 3), 1, False)

    def test_rank_zero(self):
        self.solve(((0, 0, 0),), (0,), 0, True)
        self.solve(((0,), (0,)), (0, 1), 0, False)

    def test_fractional_pivoting(self):
        self.solve(((0, F(2, 3)), (F(5, 7), F(4, 9))), (1, 2), 2, True)

    def test_seeded_rectangular_systems(self):
        rng = random.Random(90210)
        for m, n in product(range(1, 6), repeat=2):
            for _ in range(8):
                a = Matrix(tuple(tuple(F(rng.randrange(-4, 5), rng.randrange(1, 5))
                                       for _ in range(n)) for _ in range(m)))
                x = Vector(tuple(rng.randrange(-3, 4) for _ in range(n)))
                c = exact_linear_solve(a, a @ x)
                self.assertTrue(c.verify())
                self.assertTrue(c.consistent)

    def test_tampered_witnesses(self):
        c = self.solve(((1, 2, 3), (2, 4, 6)), (1, 2), 1, True)
        for bad in (replace(c, transform=Matrix.identity(2)),
                    replace(c, inverse_transform=Matrix.zero(2, 2)),
                    replace(c, reduced=Matrix.zero(2, 3)),
                    replace(c, kernel=()), replace(c, kernel=(c.kernel[0],)*2),
                    replace(c, particular=Vector((0, 0, 0))),
                    replace(c, inconsistency=Vector((0, 0)))):
            self.assertFalse(bad.verify())
        bad = self.solve(((1,), (1,)), (0, 1), 1, False)
        self.assertFalse(replace(bad, inconsistency=Vector((0, 0))).verify())

    def test_verifier_independent_of_solver(self):
        c = exact_linear_solve(Matrix(((1, 2),)), Vector((3,)))
        with patch('ml_mathlib_linear.exact_linear_solve', side_effect=AssertionError):
            self.assertTrue(verify_linear_certificate(c.to_json()))

    def test_hostile_json_and_budgets(self):
        c = exact_linear_solve(Matrix(((1,),)), Vector((1,)))
        source = c.to_json()
        self.assertFalse(verify_linear_certificate(source, max_bytes=10))
        self.assertFalse(verify_linear_certificate(source, max_entries=1))
        self.assertFalse(verify_linear_certificate(source.replace('"version":1', '"version":true')))
        self.assertFalse(verify_linear_certificate(source.replace('"version":1', '"version":1,"version":1')))
        for change in ({'version': 2}, {'rhs': ['1/0']}, {'rhs': ['1.0']},
                       {'rhs': [1]}, {'kernel': {}}, {'extra': 1}, {'matrix': [[]]}):
            data = json.loads(source)
            data.update(change)
            self.assertFalse(verify_linear_certificate(json.dumps(data)))
        for source in ('null', '[]', '{', '['*2000+']'*2000):
            self.assertFalse(verify_linear_certificate(source))

    def test_limits_and_shape(self):
        with self.assertRaises(MemoryError):
            exact_linear_solve(Matrix.identity(2), Vector((0, 0)), max_cells=1)
        with self.assertRaises(ValueError):
            exact_linear_solve(Matrix.identity(2), Vector((0,)))

    def test_canonical_roundtrip(self):
        c = exact_linear_solve(Matrix(((F(1, 2), 1),)), Vector((3,)))
        self.assertEqual(type(c).from_json(c.to_json()).to_json(), c.to_json())

    def test_sparse_discovery_matches_dense(self):
        phase = SymplecticSpace(1)
        q, p = (Polynomial.variable(2, i) for i in range(2))
        h = q*q+p*p
        miner = SymbolicCrystallizer()
        for degree in (2, 4, 6):
            dense = miner.discover(phase, h, degree, backend='dense')
            sparse = miner.discover(phase, h, degree, backend='sparse')
            self.assertEqual(dense, sparse)
            self.assertTrue(all(phase.poisson(f, h).is_zero for f in sparse))
        with self.assertRaises(MemoryError):
            miner.discover(phase, h, 4, max_nonzeros=1)
        with self.assertRaises(RuntimeError):
            miner.discover(phase, h, 4, max_basis=1)
        with self.assertRaises(ValueError):
            miner.discover(phase, h, backend='unknown')


if __name__ == '__main__':
    unittest.main()
