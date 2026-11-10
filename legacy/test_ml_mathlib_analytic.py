from fractions import Fraction as F
import unittest
from ml_mathlib import Polynomial
from ml_mathlib_advanced import RationalFunction, RationalInterval as I
from ml_mathlib_exact import AnalyticExpression as E, QuadraticAlgebraicFunction, interval_nth_root


class AnalyticIntegrationTests(unittest.TestCase):
    def test_root_bounds_by_exact_powers(self):
        for degree in (1,2,3,5,12):
            for value in (F(0),F(1),F(2),F(1,1000),F(1234567,19)):
                box=interval_nth_root(value,degree,8)
                self.assertLessEqual(box.lo**degree,value)
                self.assertGreaterEqual(box.hi**degree,value)
                self.assertLessEqual(box.hi-box.lo,F(1,10**8))
        for degree,digits in ((0,8),(1025,8),(2,0),(2,4097)):
            with self.assertRaises(ValueError):interval_nth_root(F(2),degree,digits)

    def test_polynomial_and_fraction_conversion(self):
        x=Polynomial.variable(1,0)
        for value in (x*x+2*x+1,RationalFunction(x+1,x*x+2)):
            expression=E.cast(value)
            point=F(3,2)
            self.assertTrue(expression.enclose((I(point,point),)).contains(value.evaluate((point,))))

    def test_quadratic_conversion(self):
        rad=RationalFunction.from_polynomial(Polynomial.constant(1,4))
        root=QuadraticAlgebraicFunction.sqrt(rad)
        self.assertTrue(E.cast(root).enclose((I(0,0),)).contains(2))

    def test_positive_rational_powers(self):
        x=E.variable(0)
        expression=x**F(1,3)
        self.assertTrue(expression.enclose_adaptive((I(8,8),),F(1,10**8)).contains(2))
        self.assertTrue((x**F(-2,3)).enclose((I(8,8),)).contains(F(1,4)))
        self.assertTrue(expression.diff(0).enclose((I(8,8),)).contains(F(1,12)))
        for point in (-1,0):
            with self.assertRaises(ValueError):expression.enclose((I(point,point),))

    def test_nested_radicals(self):
        x=E.variable(0)
        self.assertTrue(((x**F(1,3)+1)**F(1,2)).enclose((I(27,27),)).contains(2))

    def test_precision_refines_spurious_zero_denominator(self):
        x=E.variable(0)
        expression=x**F(-1,2)
        box=expression.enclose_adaptive((I(F(1,10**100),F(1,10**100)),),F(1,100))
        self.assertTrue(box.contains(10**50))

    def test_simultaneous_composition(self):
        x,y=E.variable(0),E.variable(1)
        swapped=(x+2*y).compose((y,x))
        self.assertTrue(swapped.enclose((I(3,3),I(5,5))).contains(11))

    def test_gradient_hessian_enclosures(self):
        x,y=E.variable(0),E.variable(1)
        f=x*x*y+y*y
        point=(I(2,2),I(3,3))
        self.assertEqual(tuple(d.enclose(point).lo for d in f.gradient(2)),(12,10))
        self.assertEqual(tuple(tuple(d.enclose(point).lo for d in row) for row in f.hessian(2)),((6,4),(4,2)))

    def test_refinement_budget_and_singularities(self):
        x=E.variable(0)
        with self.assertRaises(RuntimeError):x.enclose_adaptive((I(1,2),),F(1,100),max_digits=8)
        with self.assertRaises(ZeroDivisionError):(1/x).enclose((I(-1,1),))
        with self.assertRaises(ValueError):x.log().enclose((I(0,1),))
        with self.assertRaises(ValueError):x.enclose_adaptive((I(1,1),),tolerance=0)


if __name__=='__main__':unittest.main()
