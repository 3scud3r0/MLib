"""Regression suite for ML-MATHLIB 0.2; Python standard library only."""
import math
import unittest
from fractions import Fraction as F
from ml_mathlib import (Matrix, Vector, Polynomial as P, SymplecticSpace,
                        HamiltonianFlow, canonical_example)
from ml_mathlib_advanced import *

class AdvancedTests(unittest.TestCase):
    def test_01_bareiss(self):
        m=Matrix(((F(1,2),F(1,3),2),(1,5,7),(4,11,3)))
        self.assertEqual(bareiss_determinant(m),m.determinant())
        self.assertEqual(bareiss_determinant(Matrix(((0,1),(3,4)))),-3)
        self.assertEqual(bareiss_determinant(Matrix(((1,2),(2,4)))),0)

    def test_02_quadratic_field(self):
        x=QuadraticNumber(0,1,2)
        self.assertEqual(x*x,QuadraticNumber(2,0,2))
        self.assertEqual((x+1)* (x+1).inverse(), QuadraticNumber(1,0,2))
        with self.assertRaises(ValueError): QuadraticNumber(0,1,4)

    def test_03_ldlt(self):
        m=Matrix(((2,1,0),(1,3,1),(0,1,5)))
        L,D=rational_ldlt(m)
        self.assertTrue(all(x>0 for x in D))
        diagonal=Matrix(tuple(tuple(D[i] if i==j else 0 for j in range(3)) for i in range(3)))
        self.assertEqual(L@diagonal@L.transpose(),m)

    def test_04_tensor_form(self):
        x,y=(P.variable(2,i) for i in range(2))
        a=CovariantTensor(2,1,(((0,),2),((1,),3)))
        self.assertEqual(a.tensor_product(a).contract_with((Vector((1,0)),Vector((0,1)))),6)
        f=DifferentialForm(2,0,(((),x*y),))
        df=f.exterior_derivative()
        self.assertEqual(df.exterior_derivative().components,())
        dx=DifferentialForm(2,1,(((0,),P.constant(2,1)),))
        dy=DifferentialForm(2,1,(((1,),P.constant(2,1)),))
        self.assertEqual(dx.wedge(dy).components[0][1],P.constant(2,1))
        self.assertEqual(dy.wedge(dx).components[0][1],P.constant(2,-1))

    def test_05_rational_functions(self):
        x=P.variable(1,0)
        f=RationalFunction(x*x-1,x-1)
        self.assertEqual(f,RationalFunction.from_polynomial(x+1))
        self.assertEqual(f.diff(0),RationalFunction.from_polynomial(P.constant(1,1)))
        g=RationalFunction(1+x*x, x)
        self.assertEqual(g.evaluate((F(2),)),F(5,2))
        with self.assertRaises(ZeroDivisionError):g.evaluate((F(0),))

    def test_06_local_chart(self):
        x=P.variable(1,0);one=RationalFunction.from_polynomial(P.constant(1,1))
        rx=RationalFunction.from_polynomial(x)
        forward=(rx/(one+rx),)
        backward=(rx/(one-rx),)
        ch=RationalChart(forward,backward)
        self.assertEqual(ch.apply((F(1,2),)),(F(1,3),))
        self.assertEqual(len(ch.jacobian()),1)

    def test_07_exterior(self):
        x,y,z=(P.variable(3,i) for i in range(3))
        a=DifferentialForm(3,1,(((1,),x),((2,),y)))
        self.assertEqual(a.exterior_derivative().exterior_derivative().components,())
        self.assertEqual(a.wedge(a).components,())

    def test_08_groebner(self):
        x,y=(P.variable(2,i) for i in range(2))
        gb=groebner_basis((x*y-1,x-y))
        for g in (x*y-1,x-y):self.assertTrue(ideal_contains(g,gb))
        self.assertTrue(ideal_contains(x*x-1,gb))
        self.assertFalse(ideal_contains(x-1,gb))

    def test_09_gaussian_fisher(self):
        N=GaussianFamily(2,3)
        self.assertEqual(N.fisher_metric(),Matrix(((F(1,3),0),(0,F(1,18)))))
        self.assertEqual(N.natural_gradient(Vector((2,3))),Vector((6,54)))

    def test_10_fisher_sphere(self):
        a=(F(1,2),F(1,2));b=(F(1),F(0))
        self.assertAlmostEqual(FisherSphere.distance(a,b),math.pi/2)
        self.assertAlmostEqual(FisherSphere.distance(a,a),0,places=7)

    def test_11_christoffel_alpha(self):
        N=GaussianFamily(0,2)
        self.assertEqual(N.chentsov(0,0,1),F(1,4))
        self.assertEqual(N.chentsov(1,1,1),F(1,8))
        self.assertEqual(N.christoffel(0,1,0),F(-1,4))
        self.assertEqual(N.christoffel(0,0,1),1)
        self.assertEqual(N.christoffel(0,0,1,1),0)  # Γ^v_μμ−(1/2)*2v²*(1/v²)=0

    def test_12_implicit_midpoint(self):
        phase=SymplecticSpace(1);q,p=(P.variable(2,i) for i in range(2))
        h=(q*q+p*p)/2
        solver=ImplicitMidpoint(HamiltonianFlow(phase,h),F(1,10))
        a=solver.step(Vector((1,0)))
        self.assertEqual(h.evaluate(a.entries),F(1,2))
        b=ImplicitMidpoint(HamiltonianFlow(phase,q*p),F(1,10)).step(Vector((1,2)))
        self.assertEqual(b.entries[0],F(21,19))
        self.assertEqual(b.entries[1],F(38,21))

    def test_13_verlet_yoshida(self):
        phase,h=canonical_example();flow=HamiltonianFlow(phase,h)
        v=VelocityVerlet(flow,F(1,20));z=Vector((1,2,3,5))
        y=v.step(z)
        self.assertEqual(v.step(Vector((1,0,0,0))).dim,4)
        yz=VelocityVerlet(flow,-F(1,20)).step(y)
        self.assertEqual(yz,z)
        self.assertEqual(Yoshida4(flow,F(1,20)).step(z).dim,4)

    def test_14_contact(self):
        q,p,z=(P.variable(3,i) for i in range(3))
        H=p*p/2+q*q/2+z*2
        flow=ContactFlow(1,H)
        self.assertEqual(flow.field(),(p,-q-2*p,p*p-H))
        self.assertEqual(flow.derivative_of_hamiltonian(),-2*H)

    def test_15_router_derivative(self):
        s=SymbolicExpr.var(0)
        w=DifferentiableRouter.weights((s,SymbolicExpr.const(0)))
        g=w[0].diff(0)
        self.assertAlmostEqual(g.eval([0]),F(1,4))
        self.assertAlmostEqual(DifferentiableRouter.jacobian(w)[0][0].eval([0]),F(1,4))

    def test_16_so3_se3(self):
        a=SO3.about_z(F(1,2));b=SO3.about_x(F(1,3))
        self.assertNotEqual((a@b).matrix,(b@a).matrix)
        self.assertEqual((a@b).matrix.transpose()@(a@b).matrix,Matrix.identity(3))
        e=SE3(a,Vector((1,2,3)))
        self.assertEqual(e.act(Vector((0,0,0))),Vector((1,2,3)))

    def test_17_causal_multihead(self):
        eye=Matrix.identity(2)
        attn=CausalMultiHeadAttention((eye,eye),(eye,eye),(eye,eye))
        tokens=(Vector((1,0)),Vector((0,1)),Vector((3,4)))
        masked=attn.apply(tokens,causal=True)
        changed=attn.apply(tokens[:2]+(Vector((99,99)),),causal=True)
        self.assertEqual(masked[:2],changed[:2]);self.assertEqual(len(masked[0]),4)

    def test_18_parasitic(self):
        phase,h=canonical_example();q0,q1,p0,p1=(P.variable(4,i) for i in range(4))
        L=q0*p1-q1*p0
        self.assertEqual(algebraic_independence_rank((h,L,L*L)),2)
        self.assertEqual(independent_invariants((L*L,h*L),known=(h,L)),())

    def test_19_sparse_enumeration(self):
        from math import comb
        self.assertEqual(sum(1 for _ in pruned_monomials(12,4)),comb(16,4))
        self.assertEqual(sum(1 for _ in pruned_monomials(4,2,parity=1)),4)
        with self.assertRaises(RuntimeError):list(pruned_monomials(12,4,max_terms=100))

    def test_20_noether_general(self):
        x,y=P.variable(2,0),P.variable(2,1)
        charge=noether_charge((-y,x))
        p=P.variable(4,2);q=P.variable(4,3)
        self.assertEqual(charge,-P.variable(4,1)*p+P.variable(4,0)*q)
        self.assertEqual(noether_charge((P.constant(2,1),P.constant(2,0))),p)

    def test_21_casimir(self):
        Pso=so3_lie_poisson();x,y,z=(P.variable(3,i) for i in range(3))
        c=x*x+y*y+z*z
        self.assertTrue(Pso.casimir_certificate(c))
        self.assertFalse(Pso.casimir_certificate(x))
        self.assertTrue(Pso.bracket(c,x*y).is_zero)

    def test_22_lean_export(self):
        phase,h=canonical_example();x,y,px,py=(P.variable(4,i) for i in range(4))
        script=export_lean_conservation(x*py-y*px,h,phase)
        self.assertIn('import Mathlib',script)
        self.assertIn(':= by\n  ring',script)
        with self.assertRaises(ValueError):export_lean_conservation(x,h,phase)

    def test_A_rational_intervals(self):
        for fn,x,true in ((interval_exp,F(1,2),math.exp(0.5)),(interval_sin,F(1,2),math.sin(.5)),
                          (interval_cos,F(1,2),math.cos(.5)),(interval_log,F(3,2),math.log(1.5))):
            interval=fn(x)
            self.assertLessEqual(float(interval.lo),true+1e-14)
            self.assertGreaterEqual(float(interval.hi),true-1e-14)
        pi=interval_pi(14)
        self.assertLessEqual(float(pi.lo),math.pi+1e-15)
        self.assertGreaterEqual(float(pi.hi),math.pi-1e-15)
        with self.assertRaises(ZeroDivisionError): RationalInterval(-1,1).reciprocal()

    def test_B_softmax_variational(self):
        s=SymbolicExpr.var(0)
        weights=DifferentiableRouter.weights((s,SymbolicExpr.const(0)))
        self.assertAlmostEqual(sum(w.eval([3.4]) for w in weights),1.0)
        self.assertAlmostEqual(sum(w.diff(0).eval([1.2]) for w in weights),0.0)

if __name__=='__main__':unittest.main(verbosity=2)
