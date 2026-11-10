"""ML-MATHLIB 0.5: exact regression suite for new certified structures."""
from __future__ import annotations

import random
import unittest
from fractions import Fraction as F

from ml_mathlib import Matrix, Vector, Polynomial as P
from ml_mathlib_advanced import RationalFunction as RF
from ml_mathlib_exact import RationalLieAlgebra
from ml_mathlib_foundations import (
    ModularSolveCertificate, modular_solve, characteristic_polynomial,
    isolate_real_roots, real_spectrum_intervals, IsolatedRealRoot,
    RationalAtlasCocycle, DenseTensor, GeometricCountableMeasure,
    MultivariateGaussianLaw, FisherSimplexStrata, PolynomialContactFlow,
    CayleySO3, SoftmaxJet, killing_casimir,
)


class ExactFoundationsTests(unittest.TestCase):
    def test_01_modular_simple(self):
        a=Matrix(((2,1),(1,3)));b=Vector((1,2))
        proof=modular_solve(a,b)
        self.assertEqual(proof.solution,Vector((F(1,5),F(3,5))))
        self.assertTrue(proof.verify())

    def test_02_modular_rational(self):
        a=Matrix(((F(1,3),F(2,7)),(F(-5,11),F(7,13))))
        x=Vector((F(211,13),F(-111,17)))
        self.assertEqual(modular_solve(a,a@x).solution,x)

    def test_03_modular_large_random(self):
        rng=random.Random(1625)
        for n in range(1,7):
            for trial in range(4):
                a=Matrix(tuple(tuple((rng.randint(-7,7) if i!=j else rng.randint(8,17))
                               for j in range(n)) for i in range(n)))
                if not a.determinant():continue
                x=Vector(tuple(F(rng.randint(-70,70),rng.randint(1,15)) for _ in range(n)))
                cert=modular_solve(a,a@x)
                self.assertTrue(cert.verify())
                self.assertEqual(cert.solution,x)

    def test_04_modular_singular(self):
        with self.assertRaises(ValueError):
            modular_solve(Matrix(((1,2),(2,4))),Vector((1,2)),primes=(2,3,5))

    def test_05_modular_invalid_primes(self):
        with self.assertRaises(ValueError):
            modular_solve(Matrix(((37,),)),Vector((1,)),primes=(4,))
        with self.assertRaises(ValueError):
            modular_solve(Matrix(((2,0),(0,1))),Vector((1,1)),primes=(2,2))

    def test_06_modular_proof_tamper(self):
        a=Matrix(((3,1),(4,5)));b=Vector((1,2))
        cert=modular_solve(a,b)
        self.assertFalse(ModularSolveCertificate(a,b,Vector((1,1)),cert.nonsingular_prime).verify())
        self.assertFalse(ModularSolveCertificate(a,b,cert.solution,1).verify())

    def test_07_sturm_irrational(self):
        roots=isolate_real_roots((-2,0,1),bits=20)
        self.assertEqual(len(roots),2)
        self.assertTrue(all(r.verify() for r in roots))
        self.assertLess(roots[0].hi,0)
        self.assertGreater(roots[1].lo,0)
        self.assertLessEqual(roots[1].hi-roots[1].lo,F(1,2**20))
        self.assertLessEqual(roots[1].lo**2,2)
        self.assertGreaterEqual(roots[1].hi**2,2)

    def test_08_sturm_repeated(self):
        self.assertEqual(len(isolate_real_roots((4,0,-4,0,1),bits=14)),2)

    def test_09_sturm_rational_three(self):
        roots=isolate_real_roots((0,-1,0,1),bits=16)
        self.assertEqual(len(roots),3)
        self.assertTrue(any(r.lo==r.hi==0 for r in roots))

    def test_10_sturm_none(self):
        self.assertEqual(isolate_real_roots((1,0,1)),())
        with self.assertRaises(ValueError):isolate_real_roots((7,))

    def test_11_sturm_tamper(self):
        self.assertFalse(IsolatedRealRoot((1,0,1),0,1).verify())
        self.assertFalse(IsolatedRealRoot((-2,0,1),2,3).verify())

    def test_12_charpoly(self):
        a=Matrix(((1,2),(3,4)))
        self.assertEqual(characteristic_polynomial(a),(-2,-5,1))
        self.assertEqual(len(real_spectrum_intervals(a)),2)

    def test_13_charpoly_complex(self):
        a=Matrix(((0,-1),(1,0)))
        self.assertEqual(characteristic_polynomial(a),(1,0,1))
        self.assertEqual(real_spectrum_intervals(a),())

    def test_14_charpoly_diagonal_repeated(self):
        a=Matrix(((2,0,0),(0,2,0),(0,0,-3)))
        self.assertEqual(characteristic_polynomial(a),(12,-8,-1,1))
        self.assertEqual(len(real_spectrum_intervals(a)),2)

    @staticmethod
    def _rf(n,i):return RF.from_polynomial(P.variable(n,i))

    def test_15_cocycle_two_charts(self):
        x=self._rf(1,0)
        iden=(x,);inv=(RF.from_polynomial(P.constant(1,1))/x,)
        atlas=RationalAtlasCocycle(((iden,inv),(inv,iden)))
        self.assertEqual(atlas.dimension,1)

    def test_16_cocycle_three_charts(self):
        x=self._rf(1,0)
        scale=(F(1),F(2),F(3))
        a=RationalAtlasCocycle(tuple(tuple((scale[i]/scale[j]*x,) for j in range(3)) for i in range(3)))
        self.assertEqual(a.transition(2,1),(F(3,2)*x,))

    def test_17_cocycle_violated(self):
        x=self._rf(1,0)
        with self.assertRaises(ValueError):
            RationalAtlasCocycle(( ((x,),(2*x,)), ((2*x,),(x,)) ))

    def test_18_tensor_contract(self):
        T=DenseTensor(2,(1,-1),(((0,0),3),((1,1),5),((0,1),7)))
        self.assertEqual(T.contract(0,1).components,(((),F(8)),))
        A=Matrix(((2,1),(0,1)))
        self.assertEqual(T.coordinate_transform(A).contract(0,1).components,(((),F(8)),))

    def test_19_tensor_product(self):
        v=DenseTensor(2,(1,),(((0,),2),((1,),3)))
        cov=DenseTensor(2,(-1,),(((0,),5),((1,),7)))
        self.assertEqual(v.tensor_product(cov).contract(0,1).components,(((),F(31)),))

    def test_20_tensor_bad_variance(self):
        x=DenseTensor(2,(1,1),(((0,0),2),))
        with self.assertRaises(ValueError):x.contract(0,1)
        with self.assertRaises(ValueError):x.coordinate_transform(Matrix(((1,0),(0,0))))

    def test_21_geometric_mass_tails(self):
        for p in (F(1,2),F(2,3),F(1,100),F(1)):
            g=GeometricCountableMeasure(p)
            for k in (0,1,2,17):
                self.assertEqual(g.prefix(k)+g.tail(k),1)
                self.assertEqual(g.atom(k),g.tail(k)-g.tail(k+1))

    def test_22_geometric_moments(self):
        g=GeometricCountableMeasure(F(1,2))
        self.assertEqual([g.raw_moment(k) for k in range(5)],[1,1,3,13,75])
        x=P.variable(1,0)
        self.assertEqual(g.expectation(x*x+3*x),6)

    def test_23_geometric_degenerate(self):
        g=GeometricCountableMeasure(F(1))
        self.assertEqual(g.atom(0),1)
        self.assertEqual(g.raw_moment(5),0)
        with self.assertRaises(ValueError):GeometricCountableMeasure(0)

    def test_24_gaussian_centered(self):
        g=MultivariateGaussianLaw((0,0),Matrix(((1,F(1,2)),(F(1,2),1))))
        x,y=P.variable(2,0),P.variable(2,1)
        self.assertEqual(g.expectation(x*x*y*y),F(3,2))
        self.assertEqual(g.expectation(x**4),3)
        self.assertEqual(g.expectation(x*y),F(1,2))
        self.assertEqual(g.expectation(x**3*y),F(3,2))

    def test_25_gaussian_noncentered(self):
        g=MultivariateGaussianLaw((1,-2),Matrix(((2,0),(0,3))))
        x,y=P.variable(2,0),P.variable(2,1)
        self.assertEqual(g.expectation(x*x),3)
        self.assertEqual(g.expectation(x*y),-2)
        self.assertEqual(g.expectation((x-1)**4),12)

    def test_26_gaussian_affine_pushforward(self):
        g=MultivariateGaussianLaw((1,2),Matrix(((2,0),(0,3))))
        A=Matrix(((1,1),(1,-1)));b=Vector((-3,4))
        h=g.affine_pushforward(A,b)
        self.assertEqual(h.mean,(0,3))
        self.assertEqual(h.covariance,Matrix(((5,-1),(-1,5))))

    def test_27_gaussian_invalid_covariance(self):
        with self.assertRaises(ValueError):
            MultivariateGaussianLaw((0,0),Matrix(((1,2),(2,1))))
        with self.assertRaises(ValueError):
            MultivariateGaussianLaw((0,0),Matrix(((1,2),(0,1))))

    def test_28_fisher_face_boundary(self):
        x=FisherSimplexStrata((1,0,0));y=FisherSimplexStrata((0,F(1,3),F(2,3)))
        self.assertEqual(x.support(),(0,))
        self.assertEqual(x.face_dimension(),0)
        self.assertIsNone(x.interior_metric())
        self.assertEqual(y.face_dimension(),1)
        self.assertEqual(y.interior_metric().probabilities,(F(1,3),F(2,3)))
        interval=x.distance_interval(y)
        self.assertTrue(F(3)<interval.lo<interval.hi<F(4))

    def test_29_fisher_geodesic_midpoint(self):
        x=FisherSimplexStrata((1,0));y=FisherSimplexStrata((0,1))
        self.assertEqual(x.midpoint_intervals(y)[0].lo,F(1,2))
        self.assertEqual(x.midpoint_intervals(y)[1].hi,F(1,2))

    def test_30_fisher_equal(self):
        x=FisherSimplexStrata((F(1,3),F(2,3)))
        interval=x.distance_interval(x)
        self.assertTrue(interval.lo<=0<=interval.hi)

    def test_31_contact_damped(self):
        q,p,s=(P.variable(3,i) for i in range(3))
        H=(q*q+p*p)/2+F(1,3)*s
        f=PolynomialContactFlow(H)
        self.assertTrue(f.verify_identities())
        self.assertEqual(f.field()[0],p)
        self.assertEqual(f.field()[1],-q-F(1,3)*p)
        self.assertEqual(f.lie(H),-H/3)

    def test_32_contact_general(self):
        q,p,s=(P.variable(3,i) for i in range(3))
        H=q*q*p*p+s*s*q+p*s
        self.assertTrue(PolynomialContactFlow(H).verify_identities())
        with self.assertRaises(ValueError):PolynomialContactFlow(P.variable(4,0))

    def test_33_cayley(self):
        A=Matrix(((0,-F(1,7),0),(F(1,7),0,0),(0,0,0)))
        R=CayleySO3.from_generator(A)
        self.assertEqual(R.matrix.transpose()@R.matrix,Matrix.identity(3))
        self.assertEqual(CayleySO3.adjoint(R,A),A)

    def test_34_cayley_nonabelian(self):
        X=Matrix(((0,0,0),(0,0,-1),(0,1,0)))
        Y=Matrix(((0,0,1),(0,0,0),(-1,0,0)))
        U=CayleySO3.from_generator(X)
        V=CayleySO3.from_generator(Y)
        self.assertNotEqual((U@V).matrix,(V@U).matrix)
        with self.assertRaises(ValueError):CayleySO3.from_generator(Matrix.identity(3))

    def test_35_softmax_jet(self):
        w=(F(1,2),F(1,3),F(1,6))
        J=SoftmaxJet.jacobian(w,2)
        H=SoftmaxJet.hessian(w,2)
        for i in range(3):
            self.assertEqual(sum(J[i]),0)
            self.assertEqual(sum(J[k][i] for k in range(3)),0)
            self.assertTrue(all(H[i][j][k]==H[i][k][j] for j in range(3) for k in range(3)))
            self.assertTrue(all(sum(H[i][j][k] for j in range(3))==0 for k in range(3)))
        self.assertEqual(SoftmaxJet.vector_jacobian_product(w,(1,1,1),2),(0,0,0))

    def test_36_softmax_invalid(self):
        with self.assertRaises(ValueError):SoftmaxJet.jacobian((F(1,2),F(1,2)),-1)
        with self.assertRaises(ValueError):SoftmaxJet.hessian((1,1),1)
        with self.assertRaises(ValueError):SoftmaxJet.vector_jacobian_product((1,),(1,2))

    @staticmethod
    def _so3():
        c=[[[0]*3 for _ in range(3)] for _ in range(3)]
        for i,j,k in ((0,1,2),(1,2,0),(2,0,1)):
            c[i][j][k]=1;c[j][i][k]=-1
        return RationalLieAlgebra(tuple(tuple(tuple(t) for t in row) for row in c))

    def test_37_killing_casimir(self):
        cert=killing_casimir(self._so3())
        self.assertTrue(cert.verify())
        self.assertEqual(cert.killing,Matrix(((-2,0,0),(0,-2,0),(0,0,-2))))
        x,y,z=(P.variable(3,i) for i in range(3))
        self.assertEqual(cert.casimir,-(x*x+y*y+z*z)/4)

    def test_38_killing_degenerate(self):
        c=RationalLieAlgebra((((0,0),(0,0)),((0,0),(0,0))))
        with self.assertRaises(ValueError):killing_casimir(c)

    def test_39_killing_tamper(self):
        cert=killing_casimir(self._so3())
        altered=type(cert)(cert.lie_algebra,cert.killing,P.variable(3,0))
        self.assertFalse(altered.verify())

    def test_40_tensors_covariant(self):
        T=DenseTensor(2,(-1,-1),(((0,0),1),((1,1),1)))
        A=Matrix(((2,0),(0,3)))
        t=T.coordinate_transform(A)
        self.assertEqual(t.components,(((0,0),F(1,4)),((1,1),F(1,9))))


if __name__=='__main__':
    unittest.main(verbosity=2)

# Additional tests are appended as a separate TestCase class so that both
# direct module and unittest discovery find them without metaprogramming.
from ml_mathlib_foundations import (
    formal_midpoint_symplectic, ImplicitMidpointSymplecticCertificate,
    RationalSE3Adjoint,
)
from ml_mathlib_advanced import SE3


class GeometryExtensionsTests(unittest.TestCase):
    def test_41_midpoint_quadratic_mixed(self):
        q,p=(P.variable(2,i) for i in range(2))
        H=q*p+(q*q+p*p)/2
        c=formal_midpoint_symplectic(H,F(1,7))
        self.assertTrue(c.verify())

    def test_42_midpoint_nonlinear(self):
        q,p=(P.variable(2,i) for i in range(2))
        H=q**3*p+q*p**2+p**3/3
        c=formal_midpoint_symplectic(H,F(1,10))
        self.assertTrue(c.verify())
        bad=ImplicitMidpointSymplecticCertificate(H,F(1,10),tuple(
            tuple(RF.from_polynomial(P.constant(2,int(i==j))) for j in range(2)) for i in range(2)))
        self.assertFalse(bad.verify())

    def test_43_midpoint_singular(self):
        q,p=(P.variable(2,i) for i in range(2))
        with self.assertRaises((ZeroDivisionError,ValueError,ArithmeticError)):
            formal_midpoint_symplectic(q*p,2)

    def test_44_se3_adjoint(self):
        Rx=CayleySO3.from_generator(Matrix(((0,0,0),(0,0,-F(2,5)),(0,F(2,5),0))))
        g=SE3(Rx,Vector((F(1,3),2,-1)))
        a=Vector((2,-3,5,7,11,13));b=Vector((3,4,1,-2,6,7))
        self.assertTrue(RationalSE3Adjoint.verify_homomorphism(g,a,b))

    def test_45_se3_adjoint_composition(self):
        R1=CayleySO3.from_generator(Matrix(((0,-F(1,2),0),(F(1,2),0,0),(0,0,0))))
        R2=CayleySO3.from_generator(Matrix(((0,0,F(1,3)),(0,0,0),(-F(1,3),0,0))))
        g1=SE3(R1,Vector((1,2,3)));g2=SE3(R2,Vector((-2,0,5)))
        self.assertEqual(RationalSE3Adjoint.matrix(g1@g2),
                         RationalSE3Adjoint.matrix(g1)@RationalSE3Adjoint.matrix(g2))

    def test_46_se3_invalid_twist(self):
        with self.assertRaises(ValueError):RationalSE3Adjoint.bracket(Vector((1,2)),Vector((1,2)))

class HigherDimensionalTests(unittest.TestCase):
    def test_47_midpoint_four_dimensional(self):
        v=[P.variable(4,i) for i in range(4)]
        H=sum((x*x for x in v),P.constant(4,0))/2+v[0]*v[2]+v[1]*v[3]
        self.assertTrue(formal_midpoint_symplectic(H,F(1,20)).verify())

    def test_48_casimir_zero_tamper(self):
        cert=ExactFoundationsTests._so3()
        c=killing_casimir(cert)
        zero=P.constant(3,0)
        self.assertFalse(type(c)(cert,c.killing,zero).verify())

    def test_49_gaussian_reduced_dimension(self):
        g=MultivariateGaussianLaw((3,4),Matrix(((2,1),(1,3))))
        A=Matrix(((1,2),))
        h=g.affine_pushforward(A,Vector((5,)))
        self.assertEqual(h.mean,(16,))
        self.assertEqual(h.covariance,Matrix(((18,),)))

    def test_50_cocycle_stereographic(self):
        u=RF.from_polynomial(P.variable(2,0));v=RF.from_polynomial(P.variable(2,1))
        r=u*u+v*v
        f=(u/r,v/r)
        eye=(u,v)
        self.assertEqual(RationalAtlasCocycle(((eye,f),(f,eye))).dimension,2)

class CompleteRootCertificateTests(unittest.TestCase):
    def test_complete_quadratic(self):
        from ml_mathlib_foundations import certify_all_real_roots
        c = certify_all_real_roots((-2, 0, 1), bits=18)
        self.assertTrue(c.verify())
        self.assertEqual(len(c.intervals), 2)

    def test_complete_repeated_rational(self):
        from ml_mathlib_foundations import certify_all_real_roots
        c = certify_all_real_roots((4, 0, -4, 0, 1), bits=12)
        self.assertTrue(c.verify())
        self.assertEqual(len(c.intervals), 2)

    def test_missing_root_rejected(self):
        from ml_mathlib_foundations import certify_all_real_roots, CompleteRealRootCertificate
        c = certify_all_real_roots((-2, 0, 1), bits=12)
        self.assertFalse(CompleteRealRootCertificate(c.polynomial, c.intervals[:1]).verify())

    def test_overlap_rejected(self):
        from ml_mathlib_foundations import certify_all_real_roots, CompleteRealRootCertificate
        c = certify_all_real_roots((-2, 0, 1), bits=12)
        self.assertFalse(CompleteRealRootCertificate(c.polynomial, c.intervals * 2).verify())

    def test_no_real_roots(self):
        from ml_mathlib_foundations import certify_all_real_roots
        c = certify_all_real_roots((1, 0, 1))
        self.assertTrue(c.verify())
        self.assertEqual(c.intervals, ())
