"""Exact/regression tests for ML-MATHLIB 0.3 (Python standard library only)."""
import math
import random
import unittest
from fractions import Fraction as F
from ml_mathlib import Matrix, Vector, Polynomial as P, SymplecticSpace, HamiltonianFlow
from ml_mathlib_advanced import RationalFunction as RF, so3_lie_poisson, SO3, polynomial_division
from ml_mathlib_exact import (
    crt_pair,crt_many,modular_determinant,primitive_integer_kernel,
    irreducible_mod_prime,NumberField,ExactYoshida4,interval_sqrt,
    interval_exp_global,interval_log_global,interval_sin_cos_global,
    interval_arccos_unit,RationalInterval,MidpointContractionCertificate,
    MixedTensor,RationalRiemannianMetric,SU2,RationalLieAlgebra,
    StereographicSphere2,SymbolicAttention,PolynomialItoDiffusion,
    discover_casimirs,reduced_groebner_basis,interval_eval,
    QuadraticAlgebraicFunction, AnalyticExpression, SparseExactKernel,
    UniformIntervalMeasure, SymbolicMultiHeadAttention, CertifiedFisherSphere,
    GaussianNaturalExponentialFamily, CertifiedGaussianFisher,
    serialize_conservation_certificate,verify_conservation_certificate)

class ExactExpansionTests(unittest.TestCase):
    def test_01_crt(self):
        self.assertEqual(crt_pair(2,3,3,5),(8,15))
        x,m=crt_many(((2,3),(3,5),(2,7)))
        self.assertEqual((x,m),(23,105))
        with self.assertRaises(ValueError):crt_pair(1,4,2,6)

    def test_02_modular_det(self):
        cases=[Matrix(((1,2),(3,4))),Matrix(((0,1),(3,2))),
               Matrix(((F(1,3),F(2,5)),(F(7,11),F(5,4)))),
               Matrix(((1,2,3),(2,4,6),(0,2,2))),
               Matrix(((137,723,27),(-271,29,7),(333,15,91)))]
        for a in cases:self.assertEqual(modular_determinant(a),a.determinant())
        with self.assertRaises(RuntimeError):modular_determinant(Matrix(((10**20,0),(0,10**20))),primes=(101,))
        big=Matrix(((10**20+3,7),(11,10**20-1)))
        self.assertEqual(modular_determinant(big),big.determinant())

    def test_03_integer_kernel(self):
        cases=[[[2,4,6],[1,2,3]],[[F(1,2),F(1,3),F(1,5)],[3,2,1]],
               [[3,5,7],[1,0,1],[2,2,2]],[[0,0,0]],[[1,0],[0,1]]]
        for rows in cases:
            v=primitive_integer_kernel(rows)
            for x in v:
                for row in rows:self.assertEqual(sum((F(a)*b for a,b in zip(row,x)),F(0)),F(0))
        self.assertEqual(len(primitive_integer_kernel([[1,2,3]])),2)

    def test_04_irreducible_certificate(self):
        self.assertTrue(irreducible_mod_prime((-2,0,0,1),7))
        self.assertTrue(irreducible_mod_prime((-2,0,1),3))
        self.assertTrue(irreducible_mod_prime((1,1),7))
        self.assertTrue(irreducible_mod_prime((1,1,0,0,1),2))
        self.assertFalse(irreducible_mod_prime((-1,0,1),3))
        with self.assertRaises(ValueError):NumberField((-1,0,1),3)

    def test_05_number_field(self):
        K=NumberField((-2,0,0,1),7);a=K.alpha()
        self.assertEqual(a**3,2)
        self.assertEqual((a+1)*(a+1).inverse(),1)
        self.assertEqual(1/a*a,1)
        x=K.element((1,2,3))
        self.assertEqual(x*x.inverse(),1)
        self.assertEqual(K.element((1,0,0,1)),3)
        with self.assertRaises(ZeroDivisionError):K.element(0).inverse()

    def test_06_yoshida_algebraic(self):
        q,p=P.variable(2,0),P.variable(2,1)
        phase=SymplecticSpace(1)
        flow=HamiltonianFlow(phase,(q*q+p*p)/2)
        solver=ExactYoshida4(flow,F(1,10))
        z=solver.step(Vector((1,0)))
        self.assertEqual(len(z),2)
        self.assertNotEqual(z[0],solver.field.element(1))
        reverse=ExactYoshida4(flow,F(-1,10))
        self.assertEqual(reverse.step(z),tuple(solver.field.element(x) for x in (1,0)))
        self.assertEqual(2*solver.coefficients[0]+solver.coefficients[1],1)

    def test_07_interval_sqrt(self):
        for x in [F(0),F(2),F(4),F(1,3),F(400,9)]:
            z=interval_sqrt(x,10)
            self.assertLessEqual(z.lo*z.lo,x)
            self.assertGreaterEqual(z.hi*z.hi,x)
        self.assertEqual(interval_sqrt(F(4,9),12).lo,F(666666666666,10**12))

    def test_08_global_exponentials(self):
        for x in [F(-10),F(-2),F(-1,2),F(0),F(1,2),F(3),F(5)]:
            z=interval_exp_global(x,20)
            y=math.exp(float(x))
            self.assertLessEqual(float(z.lo),y+5e-13)
            self.assertGreaterEqual(float(z.hi),y-5e-13)
        for x in [F(1,100),F(1,2),F(1),F(2),F(10),F(100)]:
            z=interval_log_global(x,24)
            y=math.log(float(x))
            self.assertLessEqual(float(z.lo),y+1e-12)
            self.assertGreaterEqual(float(z.hi),y-1e-12)

    def test_09_global_trig(self):
        for x in [F(0),F(1,3),F(3),F(12),F(-7)]:
            s,c=interval_sin_cos_global(x,22)
            self.assertTrue(float(s.lo)-1e-12<=math.sin(float(x))<=float(s.hi)+1e-12)
            self.assertTrue(float(c.lo)-1e-12<=math.cos(float(x))<=float(c.hi)+1e-12)

    def test_10_arccos_bound(self):
        for x in [RationalInterval(F(1,2),F(1,2)),RationalInterval(0,0),RationalInterval(F(-1,2),F(-1,2))]:
            a=interval_arccos_unit(x,bits=12,terms=24)
            self.assertTrue(float(a.lo)-1e-12<=math.acos(float(x.lo))<=float(a.hi)+1e-12)

    def test_11_interval_polynomials(self):
        x=P.variable(1,0)
        self.assertEqual(interval_eval(x*x,(RationalInterval(-1,1),)),RationalInterval(0,1))
        self.assertEqual(interval_eval(x**3,(RationalInterval(-1,1),)),RationalInterval(-1,1))

    def test_12_midpoint_banach_certification(self):
        q,p=P.variable(2,0),P.variable(2,1)
        flow=HamiltonianFlow(SymplecticSpace(1),q*p+q*q*p*p)
        z=Vector((F(1,10),F(1,10)))
        B=(RationalInterval(F(9,100),F(12,100)),RationalInterval(F(8,100),F(11,100)))
        c=MidpointContractionCertificate.certify(flow,z,F(1,10),B)
        self.assertLess(c.contraction_bound,1)
        r=c.enclose(6)
        self.assertLess(r[0].hi-r[0].lo,B[0].hi-B[0].lo)
        with self.assertRaises(ValueError):MidpointContractionCertificate.certify(flow,z,F(10),B)

    def test_13_mixed_tensor(self):
        t=MixedTensor(2,1,1,(((0,0),2),((1,1),3),((0,1),5)))
        scalar=t.contract(0,0)
        self.assertEqual(scalar.entries,(((),F(5)),))
        co=MixedTensor(2,0,1,(((0,),1),))
        self.assertEqual(t.tensor(co).upper,1)
        self.assertEqual(t.tensor(co).lower,2)

    def test_14_rational_curvature_flat(self):
        one=RF.from_polynomial(P.constant(2,1));zero=RF.from_polynomial(P.constant(2,0))
        x=P.variable(2,0);xx=RF.from_polynomial(x*x)
        g=RationalRiemannianMetric(((one,zero),(zero,xx)))
        # Polar metric dr²+r²dθ² is intrinsically flat wherever r ≠ 0.
        self.assertEqual(g.christoffel(1,0,1),RF.from_polynomial(P.constant(2,1))/x)
        self.assertEqual(g.riemann(0,1,0,1),0)

    def test_15_su2_group(self):
        a=SU2.stereographic(F(1,2),0,0)
        b=SU2.stereographic(0,F(1,3),0)
        self.assertNotEqual(a@b,b@a)
        self.assertEqual((a@b).to_so3().matrix,(a.to_so3()@b.to_so3()).matrix)
        self.assertEqual((a@a.inverse()).to_so3(),SO3(Matrix.identity(3)))
        self.assertEqual(SU2(-1,0,0,0).to_so3(),SO3(Matrix.identity(3)))

    def test_16_lie_algebra(self):
        z=[[[F(0) for _ in range(3)] for _ in range(3)] for _ in range(3)]
        for i,j,k in ((0,1,2),(1,2,0),(2,0,1)):
            z[i][j][k]=F(1);z[j][i][k]=F(-1)
        L=RationalLieAlgebra(tuple(tuple(tuple(a) for a in row) for row in z))
        self.assertEqual(L.bracket(Vector((1,0,0)),Vector((0,1,0))),Vector((0,0,1)))
        z[0][0][0]=F(1)
        with self.assertRaises(ValueError):RationalLieAlgebra(tuple(tuple(tuple(a) for a in row) for row in z))

    def test_17_s2_stereographic(self):
        self.assertTrue(StereographicSphere2.verify())
        u=RF.from_polynomial(P.variable(2,0));v=RF.from_polynomial(P.variable(2,1))
        xyz=StereographicSphere2.embed(u,v)
        self.assertEqual(tuple(f.evaluate((0,0)) for f in xyz),(0,0,-1))
        with self.assertRaises(ZeroDivisionError):
            StereographicSphere2.transition(u,v)[0].evaluate((0,0))

    def test_18_symbolic_attention_gradients(self):
        m=SymbolicAttention(1,1)
        o=m.forward(((1,),(2,)))
        self.assertEqual(len(o),2)
        self.assertAlmostEqual(o[0][0].eval([1,2,3]),3.)
        loss=(o[1][0]-F(4))**2
        val,grad=m.value_and_gradient(loss,[F(1),F(1),F(1)])
        self.assertEqual(len(grad),3)
        h=1e-5
        for i in range(3):
            a=[1.,1.,1.];b=a.copy();a[i]+=h;b[i]-=h
            numeric=(loss.eval(a)-loss.eval(b))/(2*h)
            self.assertAlmostEqual(grad[i],numeric,places=4)

    def test_19_ito_polynomial_generator(self):
        x=P.variable(1,0);drift=(P.constant(1,0),)
        sigma=((P.constant(1,1),),)
        W=PolynomialItoDiffusion(drift,sigma)
        self.assertEqual(W.generator(x*x),P.constant(1,1))
        self.assertEqual(W.generator(x),P.constant(1,0))

    def test_20_casimir_discovery(self):
        Poisson=so3_lie_poisson();C=discover_casimirs(Poisson,degree=2)
        self.assertEqual(len(C),1)
        self.assertTrue(Poisson.casimir_certificate(C[0]))
        self.assertTrue(all(sum(exp)==2 for exp,_ in C[0].terms))

    def test_21_reduced_groebner(self):
        x,y=P.variable(2,0),P.variable(2,1)
        G=reduced_groebner_basis((x*y-1,x-y))
        self.assertTrue(all(polynomial_division(f,G)[1].is_zero for f in (x*y-1,x-y)))
        self.assertEqual(polynomial_division(x*x-1,G)[1],P.constant(2,0))
        self.assertEqual(len(G),2)

    def test_22_quadratic_algebraic_function(self):
        x,y=P.variable(2,0),P.variable(2,1)
        r=RF.from_polynomial(x*x+y*y)
        root=QuadraticAlgebraicFunction.sqrt(r)
        self.assertEqual(root*root,QuadraticAlgebraicFunction(r,RF.from_polynomial(P.constant(2,0)),r))
        self.assertEqual((root.inverse()*root).a,RF.from_polynomial(P.constant(2,1)))
        dx=root.diff(0)
        z=dx.evaluate_interval((F(3),F(4)),24)
        self.assertTrue(z.lo<=F(3,5)<=z.hi)
        grav=root.inverse()
        self.assertTrue(grav.evaluate_interval((F(3),F(4)),24).contains(F(1,5)))
        with self.assertRaises(ZeroDivisionError):grav.evaluate_interval((F(0),F(0)))

    def test_23_analytic_transcendentals_certified(self):
        x=AnalyticExpression.variable(0)
        pendulum=x.cos()+x*x/2
        dpend=pendulum.diff(0)
        for val in [F(0),F(1,5),F(-3,4),F(2)]:
            z=(RationalInterval(val,val),)
            original=pendulum.enclose(z,20)
            slope=dpend.enclose(z,20)
            self.assertTrue(original.lo<=math.cos(float(val))+float(val*val/2)+1e-12 and original.hi>=math.cos(float(val))+float(val*val/2)-1e-12)
            self.assertTrue(slope.lo<=-math.sin(float(val))+float(val)+1e-12 and slope.hi>=-math.sin(float(val))+float(val)-1e-12)
        e=(x.sqrt().log()).diff(0)
        z=e.enclose((RationalInterval(4,4),),20)
        self.assertTrue(z.lo<=F(1,8)<=z.hi)
        with self.assertRaises(ValueError):x.log().enclose((RationalInterval(-1,1),))

    def test_24_sparse_elimination(self):
        rows=[{0:2,2:4},{1:3,2:6},{0:1,1:1,3:1}]
        S=SparseExactKernel(4)
        for row in rows:S.add_equation(row)
        self.assertEqual(S.rank,3)
        for x in S.basis():
            for row in rows:
                self.assertEqual(sum((v*x[i] for i,v in row.items()),F(0)),0)
        with self.assertRaises(RuntimeError):SparseExactKernel(4).basis(max_basis=1)
        with self.assertRaises(MemoryError):SparseExactKernel(4,max_nonzeros=1).add_equation({0:1,1:2})

    def test_25_uniform_continuous_measure(self):
        u=UniformIntervalMeasure(-1,2)
        x=P.variable(1,0)
        self.assertEqual(u.expectation(x),F(1,2))
        self.assertEqual(u.moment(2),F(1))
        self.assertEqual(u.expectation(x*x+2*x+3),F(5))
        self.assertEqual(u.cdf(F(1,2)),F(1,2))
        with self.assertRaises(ValueError):UniformIntervalMeasure(1,1)

    def test_26_lie_jacobi_four_dimensions(self):
        # Failure of Jacobi on span(e0,e1,e2), with e3 central.
        c=[[[F(0) for _ in range(4)] for _ in range(4)] for _ in range(4)]
        c[0][1][0]=1;c[1][0][0]=-1
        c[2][0][2]=1;c[0][2][2]=-1
        # [e1,e2]=e1 creates nonzero Jacobi on e0,e1,e2.
        c[1][2][1]=1;c[2][1][1]=-1
        with self.assertRaises(ValueError):RationalLieAlgebra(tuple(tuple(tuple(row) for row in slab) for slab in c))

    def test_27_randomized_modular_and_kernel(self):
        rng=random.Random(271828)
        for _ in range(15):
            m=Matrix(tuple(tuple(F(rng.randint(-9,9),rng.randint(1,6)) for j in range(4)) for i in range(4)))
            self.assertEqual(modular_determinant(m),m.determinant())
        for _ in range(10):
            rows=[[rng.randint(-4,4) for _ in range(5)] for _ in range(3)]
            V=primitive_integer_kernel(rows)
            E=SparseExactKernel(5)
            for r in rows:E.add_equation(dict(enumerate(r)))
            self.assertEqual(len(V),len(E.basis()))
            for x in E.basis():
                for r in rows:self.assertEqual(sum((a*b for a,b in zip(r,x)),F(0)),0)

    def test_28_fisher_sphere_interval(self):
        p=(F(1,2),F(1,2));q=(F(1,4),F(3,4))
        I=CertifiedFisherSphere.distance_interval(p,q,digits=26,bits=32)
        expected=2*math.acos(sum(math.sqrt(float(a*b)) for a,b in zip(p,q)))
        self.assertLessEqual(float(I.lo),expected+1e-12)
        self.assertGreaterEqual(float(I.hi),expected-1e-12)
        self.assertLess(float(I.hi-I.lo),0.05)
        equal=CertifiedFisherSphere.distance_interval(p,p,digits=24)
        self.assertEqual(equal.lo,0)
        self.assertLess(float(equal.hi),1e-6)
        orthogonal=CertifiedFisherSphere.distance_interval((F(1),F(0)),(F(0),F(1)))
        self.assertLess(float(orthogonal.lo),math.pi+1e-9)
        self.assertGreater(float(orthogonal.hi),math.pi-1e-9)

    def test_29_gaussian_natural_family(self):
        e=GaussianNaturalExponentialFamily()
        self.assertEqual(e.euclidean_parameters(0,F(-1,2)),(0,F(1)))
        M=e.fisher_at(F(0),F(-1,2))
        for row,expected in zip(M,((F(1),F(0)),(F(0),F(2)))):
            for interval,x in zip(row,expected):
                self.assertTrue(interval.lo<=x<=interval.hi)
        with self.assertRaises(ValueError):e.fisher_at(0,0)

    def test_30_gaussian_fisher_distance(self):
        A=CertifiedGaussianFisher.distance_interval(0,1,1,1,digits=25)
        expected=math.sqrt(2)*math.acosh(1+F(1,4))
        self.assertLessEqual(float(A.lo),expected+1e-11)
        self.assertGreaterEqual(float(A.hi),expected-1e-11)
        self.assertLess(float(A.hi-A.lo),1e-6)
        B=CertifiedGaussianFisher.distance_interval(0,1,0,1,digits=20)
        self.assertEqual((B.lo,B.hi),(0,0))

    def test_31_certificate_json_replay_and_tamper(self):
        qx,qy,px,py=(P.variable(4,i) for i in range(4))
        h=(qx*qx+qy*qy+px*px+py*py)/2
        L=qx*py-qy*px
        record=serialize_conservation_certificate(SymplecticSpace(2),h,L)
        self.assertTrue(verify_conservation_certificate(record))
        self.assertFalse(verify_conservation_certificate(record.replace('"pairs": 2','"pairs": 1')))
        import json
        obj=json.loads(record);obj['observable']=[[list((0,0,0,0)),'1']]
        self.assertFalse(verify_conservation_certificate(json.dumps(obj)))
        with self.assertRaises(ValueError):serialize_conservation_certificate(SymplecticSpace(2),h,qx)

    def test_32_sparse_large_low_fill_in(self):
        # 12 phase coordinates, degree <=4 => C(16,4)=1820 columns.
        self.assertEqual(math.comb(16,4),1820)
        S=SparseExactKernel(1820,max_nonzeros=2000)
        for j in range(1819):self.assertTrue(S.add_equation({j:1}))
        self.assertEqual(S.rank,1819)
        vectors=S.basis(max_basis=1)
        self.assertEqual(vectors[0][-1],F(1))
        self.assertTrue(all(not a for a in vectors[0][:-1]))

    def test_33_symbolic_multihead_causal_gradients(self):
        net=SymbolicMultiHeadAttention(2,1)
        self.assertEqual(net.nparams,10)
        output=net.forward(((1,),(2,)))
        self.assertEqual((len(output),len(output[0])),(2,2))
        w=[F(1) for _ in range(net.nparams)]
        base=output[0][0].eval(w)
        changed=net.forward(((1,),(999,)))
        self.assertAlmostEqual(base,changed[0][0].eval(w))
        loss=(output[1][0]-F(3))**2
        y,g=net.value_and_gradient(loss,w)
        self.assertTrue(math.isfinite(y))
        self.assertEqual(len(g),net.nparams)
        self.assertGreater(sum(abs(t) for t in g),0)
        eps=1e-5
        for k in (0,4,6,9):
            a=list(map(float,w));b=a.copy();a[k]+=eps;b[k]-=eps
            v=(loss.eval(a)-loss.eval(b))/(2*eps)
            self.assertAlmostEqual(g[k],v,places=3)

if __name__=='__main__':unittest.main(verbosity=2)
