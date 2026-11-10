"""Propriedades e contraexemplos da versão 0.4; somente biblioteca padrão."""
import unittest
from fractions import Fraction as F
from math import exp
from ml_mathlib import Polynomial as P, Vector
from ml_mathlib_advanced import RationalFunction as RF, RationalInterval as I
from ml_mathlib_verified import (
 poly_exact_quotient,multivariate_gcd,ReducedRational,RationalDifferentialForm,
 groebner_witness, GaussianPolynomialLaw,GaussianMixturePolynomialLaw,
 CategoricalInformationGeometry,RationalRotationSO2,IntervalSoftmax,
 DampedHarmonicMidpoint,SparseBlockKernel)

class VerifiedExpansionTests(unittest.TestCase):
 def test_01_gcd_univariate(self):
  x=P.variable(1,0)
  self.assertEqual(multivariate_gcd((x-1)*(x+2),(x-1)*(x*x+1)),x-1)
  self.assertEqual(multivariate_gcd(x*x-1,x*x+1),P.constant(1,1))

 def test_02_gcd_multivariate_nonlinear(self):
  x,y=P.variable(2,0),P.variable(2,1)
  g=x+y
  self.assertEqual(multivariate_gcd(g*(x+1),g*(y+2)),g)
  self.assertEqual(multivariate_gcd(g*g*(x+1),g*(y+2)),g)

 def test_03_gcd_multivariate_nonconstant_content(self):
  x,y=P.variable(2,0),P.variable(2,1)
  a=(x+1)*(y+2)*(x+y)
  b=(x+1)*(y+3)*(x+y)
  self.assertEqual(multivariate_gcd(a,b),(x+1)*(x+y))

 def test_04_gcd_dimension_three(self):
  x,y,z=[P.variable(3,i) for i in range(3)]
  common=x+y+z
  self.assertEqual(multivariate_gcd(common*(x+1),common*(y*z+1)),common)

 def test_05_reduced_fraction(self):
  x,y=P.variable(2,0),P.variable(2,1)
  r=ReducedRational((x+y)*(x+1),(x+y)*(y+1))
  self.assertEqual(r.numerator,x+1)
  self.assertEqual(r.denominator,y+1)
  with self.assertRaises(ValueError):poly_exact_quotient(x,y)

 def test_06_gcd_zero_and_degree_limit(self):
  x,y=P.variable(2,0),P.variable(2,1)
  self.assertEqual(multivariate_gcd(x,P.constant(2,0)),x)
  with self.assertRaises(RuntimeError):multivariate_gcd(x*x,y,max_degree=1)

 def test_07_differential_form_d_squared(self):
  x,y=[P.variable(2,i) for i in range(2)]
  f=RF.from_polynomial(x*x*y)
  omega=RationalDifferentialForm.scalar(f)
  self.assertEqual(omega.exterior_derivative().exterior_derivative().components,())

 def test_08_differential_form_rational_wedge(self):
  x,y=[P.variable(2,i) for i in range(2)]
  f=RF.from_polynomial(x)/RF.from_polynomial(y+1)
  g=RF.from_polynomial(y)
  dx=RationalDifferentialForm(2,1,(((0,),f),))
  dy=RationalDifferentialForm(2,1,(((1,),g),))
  self.assertEqual(dx.wedge(dy).components[0][1],f*g)
  self.assertEqual(dy.wedge(dx).components[0][1],-f*g)
  self.assertEqual(dx.exterior_derivative().exterior_derivative().components,())

 def test_09_pullback_and_d_commute(self):
  x,y=[P.variable(2,i) for i in range(2)]
  r=lambda p:RF.from_polynomial(p)
  omega=RationalDifferentialForm.scalar(r(x*y+x))
  map_=(r(x+y),r(x-y))
  self.assertEqual(omega.pullback(map_).exterior_derivative(),omega.exterior_derivative().pullback(map_))

 def test_10_groebner_positive_witness(self):
  x,y=P.variable(2,0),P.variable(2,1)
  gs=(x*y-1,x-y)
  candidate=x*x-1
  c=groebner_witness(candidate,gs)
  self.assertIsNotNone(c)
  self.assertTrue(c.verify())
  self.assertEqual(len(c.coefficients),2)

 def test_11_groebner_negative_and_limits(self):
  x,y=P.variable(2,0),P.variable(2,1)
  self.assertIsNone(groebner_witness(x,(x*y,)))
  self.assertTrue(groebner_witness(P.constant(2,0),(x*y,)).verify())
  with self.assertRaises(ValueError):groebner_witness(x,())

 def test_12_gaussian_moments(self):
  law=GaussianPolynomialLaw(F(1,3),F(2))
  x=P.variable(1,0)
  self.assertEqual(law.expectation(x*x),F(19,9))
  self.assertEqual(law.expectation((x-F(1,3))**4),3*F(2)**2)
  self.assertEqual(law.expectation((x-F(1,3))**3),0)

 def test_13_gaussian_mixture(self):
  mix=GaussianMixturePolynomialLaw((F(1,4),F(3,4)),
     (GaussianPolynomialLaw(-1,2),GaussianPolynomialLaw(2,3)))
  x=P.variable(1,0)
  self.assertEqual(mix.expectation(x),F(5,4))
  with self.assertRaises(ValueError):GaussianMixturePolynomialLaw((1,1),mix.components)

 def test_14_information_inverse_fisher(self):
  g=CategoricalInformationGeometry((F(1,2),F(1,3),F(1,6)))
  for i in range(2):
   for j in range(2):
    self.assertEqual(sum((g.metric(i,k)*g.metric_inverse(k,j) for k in range(2)),F(0)),int(i==j))

 def test_15_alpha_connections(self):
  g=CategoricalInformationGeometry((F(1,2),F(1,3),F(1,6)))
  for i in range(2):
   for j in range(2):
    for k in range(2):
     self.assertEqual(g.alpha_lower(i,j,k,-1),0)
     self.assertEqual(g.alpha_lower(i,j,k,0),-g.chentsov(i,j,k)/2)
     self.assertEqual(g.alpha_lower(i,j,k,1),-g.chentsov(i,j,k))

 def test_16_alpha_geodesic(self):
  g=CategoricalInformationGeometry((F(1,2),F(1,3),F(1,6)))
  t=F(1,4);q=(F(1,3),F(1,3),F(1,3))
  self.assertEqual(g.m_geodesic(q,t),tuple((1-t)*a+t*b for a,b in zip(g.probabilities,q)))
  with self.assertRaises(ValueError):CategoricalInformationGeometry((0,1))

 def test_17_exact_rope_rotations(self):
  R=RationalRotationSO2.from_stereographic(F(2,3))
  self.assertEqual(R.cos*R.cos+R.sin*R.sin,1)
  v=Vector((3,4));w=R.power(10).apply(v)
  self.assertEqual(w.dot(w),v.dot(v))
  self.assertEqual(R.inverse().apply(R.apply(v)),v)

 def test_18_exact_rope_relative_positions(self):
  R=RationalRotationSO2.from_stereographic(F(1,5))
  a=Vector((2,3));b=Vector((7,-3))
  for i,j in ((0,1),(2,5),(10,3)):
   self.assertEqual(R.power(i).apply(a).dot(R.power(j).apply(b)),a.dot(R.power(j-i).apply(b)))

 def test_19_softmax_point_interval(self):
  z=IntervalSoftmax((I(F(0),F(0)),I(F(1,2),F(1,2))),terms=25)
  ws=z.weights()
  expected=[1/(1+exp(.5)),exp(.5)/(1+exp(.5))]
  for w,e in zip(ws,expected):self.assertLessEqual(float(w.lo),e+1e-12);self.assertGreaterEqual(float(w.hi),e-1e-12)
  self.assertTrue((sum(ws,I(0,0))).contains(1))

 def test_20_softmax_jacobian(self):
  z=IntervalSoftmax((I(0,0),I(0,0)),terms=26)
  j=z.jacobian()
  self.assertTrue(j[0][0].contains(F(1,4)))
  self.assertTrue(j[0][1].contains(-F(1,4)))
  with self.assertRaises(ValueError):IntervalSoftmax((I(0,0),),temperature=0)

 def test_21_softmax_uncertain(self):
  z=IntervalSoftmax((I(F(-1,10),F(1,10)),I(F(1),F(11,10))))
  for w in z.weights():self.assertTrue(0<=w.lo<=w.hi<=1)

 def test_22_damped_midpoint(self):
  model=DampedHarmonicMidpoint(2,F(1,4))
  z=Vector((F(4),F(3)))
  for _ in range(5):
   y=model.step(z,F(1,8))
   self.assertLessEqual(model.energy(y),model.energy(z))
   z=y

 def test_23_damped_midpoint_no_dissipation(self):
  model=DampedHarmonicMidpoint(3,0)
  z=Vector((F(4),F(3)));y=model.step(z,F(1,4))
  self.assertEqual(model.energy(y),model.energy(z))
  with self.assertRaises(ValueError):DampedHarmonicMidpoint(1,-1)

 def test_24_sparse_blocks(self):
  k=SparseBlockKernel(8)
  k.append({0:1,1:2});k.append({3:3,4:4})
  self.assertEqual(k.components(),((0,1),(2,),(3,4),(5,),(6,),(7,)))
  b=k.basis()
  self.assertEqual(len(b),6)
  for vec in b:
   self.assertEqual(vec[0]+2*vec[1],0)
   self.assertEqual(3*vec[3]+4*vec[4],0)

 def test_25_sparse_larger(self):
  k=SparseBlockKernel(1820,max_nnz=10000)
  for i in range(0,100,2):k.append({i:1,i+1:-1})
  b=k.basis(max_vectors=1800)
  self.assertEqual(len(b),1770)

 def test_26_sparse_budget(self):
  k=SparseBlockKernel(4,max_nnz=1)
  with self.assertRaises(MemoryError):k.append({0:1,1:1})

if __name__=='__main__':unittest.main()

class NonSquarePullbackTests(unittest.TestCase):
 def test_dimension_increase(self):
  x=P.variable(1,0);u,v=(P.variable(2,i) for i in range(2))
  r=RF.from_polynomial
  omega=RationalDifferentialForm.scalar(r(x*x))
  Fmap=(r(u+v),)
  self.assertEqual(omega.pullback(Fmap).exterior_derivative(),omega.exterior_derivative().pullback(Fmap))

 def test_dimension_decrease_zero_two_form(self):
  x,y=(P.variable(2,i) for i in range(2));t=P.variable(1,0)
  r=RF.from_polynomial
  omega=RationalDifferentialForm(2,2,(((0,1),r(x*y+1)),))
  pull=omega.pullback((r(t),r(t*t)))
  self.assertEqual(pull.degree,2)
  self.assertEqual(pull.components,())
  self.assertEqual(pull.exterior_derivative().degree,3)

 def test_rational_pullback_with_pole(self):
  x=P.variable(1,0);u,v=P.variable(2,0),P.variable(2,1)
  r=RF.from_polynomial
  f=r(x).inverse()
  omega=RationalDifferentialForm.scalar(f)
  pb=omega.pullback((r(u+v),))
  self.assertEqual(pb.components[0][1],r(u+v).inverse())

class DynamicsExpansionTests(unittest.TestCase):
 def test_midpoint_nonseparable(self):
  from ml_mathlib_verified import ExactQuadraticMidpoint
  q,p=P.variable(2,0),P.variable(2,1)
  H=q*p+(q*q+p*p)/2
  integrator=ExactQuadraticMidpoint(H,1,F(1,5))
  state=Vector((F(1,3),F(-4,5)))
  end=integrator.step(state)
  self.assertEqual(H.evaluate(state.entries),H.evaluate(end.entries))
  rev=ExactQuadraticMidpoint(H,1,F(-1,5))
  self.assertEqual(rev.step(end),state)

 def test_midpoint_symplectic_all_pairs(self):
  from ml_mathlib_verified import ExactQuadraticMidpoint
  q0,q1,p0,p1=[P.variable(4,i) for i in range(4)]
  H=(q0*q1+p0*p1+q0*p0+q1*p1)/2
  integrator=ExactQuadraticMidpoint(H,2,F(1,7))
  self.assertTrue(integrator.phase.is_symplectic(integrator.linear))
  z=Vector((1,2,3,4))
  self.assertEqual(integrator.energy.evaluate(z.entries),integrator.energy.evaluate(integrator.step(z).entries))

 def test_midpoint_singular(self):
  from ml_mathlib_verified import ExactQuadraticMidpoint
  q,p=P.variable(2,0),P.variable(2,1)
  with self.assertRaises(ValueError):ExactQuadraticMidpoint(q*p,1,F(2))
  with self.assertRaises(ValueError):ExactQuadraticMidpoint(q**3+p*p,1,F(1,10))

 def test_ou_zero_decay(self):
  from ml_mathlib_verified import OrnsteinUhlenbeckMoments
  model=OrnsteinUhlenbeckMoments(0,2,3,4)
  m,v=model.at_time(F(1,2))
  self.assertEqual(m,I(3,3));self.assertEqual(v,I(5,5))

 def test_ou_positive_decay(self):
  from ml_mathlib_verified import OrnsteinUhlenbeckMoments
  from math import exp
  model=OrnsteinUhlenbeckMoments(F(1,2),F(2),F(3),F(1,4))
  m,v=model.at_time(F(4,3),terms=26)
  exact_mean=3*exp(-2/3)
  exact_var=.25*exp(-4/3)+2*(1-exp(-4/3))
  self.assertTrue(float(m.lo)-1e-12<=exact_mean<=float(m.hi)+1e-12)
  self.assertTrue(float(v.lo)-1e-12<=exact_var<=float(v.hi)+1e-12)
  with self.assertRaises(ValueError):model.at_time(-1)
