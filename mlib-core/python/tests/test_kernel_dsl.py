"""Pure-Python protocol/security tests; native Rust integration runs when installed."""
from __future__ import annotations

import json
from fractions import Fraction
import unittest

from mlib_core import Expr, Kernel, PhaseSpace
from mlib_core import CandidateSyntaxError, DiscoverySession, parse_candidate


class DslTests(unittest.TestCase):
    def setUp(self):
        self.phase = PhaseSpace(1)
        self.q, self.p = self.phase.coordinates()

    def test_coordinates_order(self):
        space = PhaseSpace(2)
        self.assertEqual([e.to_ast()["index"] for e in space.coordinates()], [0, 1, 2, 3])

    def test_exact_fraction(self):
        x = self.p**2 / 2 + self.q**4 / 4
        js = x.to_json()
        self.assertIn('"den":"1"', js)
        self.assertNotIn('0.5', js)
        self.assertIn('"op":"div"', js)

    def test_explicit_fraction(self):
        x = Fraction(1, 7) * self.q
        self.assertIn('"num":"1","den":"7"', x.to_json())

    def test_float_and_bool_rejected(self):
        for value in (0.5, True, False, complex(1), "1/2"):
            with self.assertRaises(TypeError):
                _ = self.q + value

    def test_spaces_not_mixed(self):
        with self.assertRaises(ValueError):
            _ = self.q + PhaseSpace(1).coordinate(0)

    def test_exponent_rejected(self):
        for exponent in (-1, 100001, 2.5, True):
            with self.assertRaises(ValueError):
                _ = self.q**exponent

    def test_derivative_and_poisson_ast(self):
        self.assertEqual(self.q.partial(self.q).to_ast()["var_index"], 0)
        self.assertEqual(self.q.poisson(self.p).to_ast()["pairs"], 1)

    def test_no_division_by_literal_zero(self):
        with self.assertRaises(ZeroDivisionError):
            _ = self.q / 0
        with self.assertRaises(ZeroDivisionError):
            _ = 1 / self.phase.constant(0)

    def test_long_ast_rejected(self):
        expr = self.q
        for _ in range(100):
            expr += self.q
        with self.assertRaises(ValueError):
            expr.to_json()

    def test_polynomial_adapter(self):
        # The production MLib Polynomial uses pairs (exponents, coefficient).
        class Poly:
            dimension = 2
            terms = (((1, 0), Fraction(2, 3)), ((0, 2), Fraction(1, 2)))
        ast = self.phase.from_polynomial(Poly()).to_ast()
        self.assertEqual(ast["op"], "add")
        with self.assertRaises(ValueError):
            PhaseSpace(2).from_polynomial(Poly())


class ProposerTests(unittest.TestCase):
    def setUp(self):
        self.phase = PhaseSpace(1)

    def test_valid_integer_polynomials(self):
        for s in ("Q = q0**2 + p0**2", "candidate = (q0 + p0) / 2", "-q0**4 + 3*p0"):
            self.assertIsInstance(parse_candidate(s, self.phase), Expr)

    def test_untrusted_syntax_rejected(self):
        malicious = [
            "__import__('os').system('true')", "(1).__class__", "q0[0]", "q0 and p0",
            "q0^2", "q0**(-1)", "q0**(1+1)", "q0**33", "p1", "1.0 * q0",
            "[q0]", "(x for x in (q0,))", "q0\np0", "q0; q0", "True", "q0 // 2",
            "lambda: q0", "q0 if True else p0", "q0**100000", "Q = q0\np0",
        ]
        for text in malicious:
            with self.subTest(text=text), self.assertRaises(CandidateSyntaxError):
                parse_candidate(text, self.phase)

    def test_large_text_and_depth_rejected(self):
        with self.assertRaises(CandidateSyntaxError):
            parse_candidate("q0+" * 1500, self.phase)
        with self.assertRaises(CandidateSyntaxError):
            parse_candidate("-" * 200 + "q0", self.phase)

    def test_no_python_evaluation(self):
        with self.assertRaises(CandidateSyntaxError):
            parse_candidate("Q = __import__('pathlib').Path('/tmp').touch()", self.phase)

    def test_reporting_rejections_without_stopping(self):
        class MockBackend:
            def verify_conservation(self, phase, *, hamiltonian, candidate):
                if candidate.to_ast() == phase.coordinate(0).to_ast():
                    raise ValueError("NonZeroResidual")
                return type("Fake", (), {"digest": "TEST_ONLY_NOT_A_PROOF"})()
        q, p = self.phase.coordinates()
        session = DiscoverySession(MockBackend(), self.phase, p**2 / 2 + q**2 / 2)
        out = session.verify(["Q = q0", "Q = p0**2 + q0**2", "Q = p0**2 + q0**2", "eval('1')"])
        self.assertEqual([o.accepted for o in out], [False, True, False, False])
        self.assertIn("duplicado", out[2].error)

    def test_bounded_sample_count(self):
        class MockBackend:
            def verify_conservation(self, *args, **kwargs):
                raise ValueError("not checked")
        q, p = self.phase.coordinates()
        session = DiscoverySession(MockBackend(), self.phase, q + p)
        with self.assertRaises(ValueError):
            session.verify([], limit=101)
        self.assertEqual(len(session.verify(["q0"]*5, limit=2)), 2)


try:
    from mlib_core._mlib_core import MlibKernelContext  # noqa: F401
except ImportError:
    NATIVE_INSTALLED = False
else:
    NATIVE_INSTALLED = True


@unittest.skipUnless(NATIVE_INSTALLED, "PyO3 native module not installed in this environment")
class NativeEndToEndTests(unittest.TestCase):
    def test_hamiltonian_is_conserved(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        kernel = Kernel()
        h = p**2 / 2 + q**4 / 4
        cert = kernel.verify_conservation(s, hamiltonian=h, candidate=h)
        self.assertEqual(len(cert.digest), 64)
        self.assertIn("NoetherInvariant", cert.claim)

    def test_false_invariant_fails(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        kernel = Kernel()
        with self.assertRaisesRegex(ValueError, "resíduo|residual|Poisson|Q,H"):
            kernel.verify_conservation(s, hamiltonian=p**2 / 2 + q**4 / 4, candidate=q)

    def test_kick_drift_symplectic(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        kernel = Kernel()
        cert = kernel.verify_symplectic(s, [q + p - q**3, p - q**3])
        self.assertEqual(len(cert.digest), 64)

    def test_bad_scaling_fails(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        with self.assertRaises(ValueError):
            Kernel().verify_symplectic(s, [q, 2 * p])

    def test_original_pole_excluded(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        cert = Kernel().verify_conservation(s, hamiltonian=p**2, candidate=(q/q) * p**2)
        self.assertTrue(cert.original_domain_exclusions)

    def test_certificate_constructor_is_not_available_in_python(self):
        from mlib_core import PyCertifiedTheorem
        with self.assertRaises(TypeError):
            PyCertifiedTheorem()

    def test_certificate_digest_is_stable_across_contexts(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        h = p**2 / 2 + q**4 / 4
        first = Kernel().verify_conservation(s, hamiltonian=h, candidate=h)
        second = Kernel().verify_conservation(s, hamiltonian=h, candidate=h)
        self.assertEqual(first.digest, second.digest)

    def test_polynomial_gcd_hint_exact(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        factor = q + p
        kernel = Kernel()
        cert = kernel.verify_polynomial_gcd(s, factor*q, factor*p, factor)
        self.assertIn("IsGcdPolynomial", cert.claim)
        with self.assertRaises(ValueError):
            kernel.verify_polynomial_gcd(s, factor*q, factor*p, s.constant(1))

    def test_candidate_stream_real_kernel(self):
        s = PhaseSpace(1)
        q, p = s.coordinates()
        session = DiscoverySession(Kernel(), s, p**2 / 2 + q**4 / 4)
        results = session.verify(["Q = q0", "Q = p0**2/2 + q0**4/4", "Q = __import__('os')"])
        self.assertEqual([r.accepted for r in results], [False, True, False])
        self.assertEqual(len(results[1].digest), 64)


if __name__ == "__main__":
    unittest.main()
