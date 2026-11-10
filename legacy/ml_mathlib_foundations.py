#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ML-MATHLIB 0.5 — new certified, *bounded-scope* mathematical components.

Python standard library only. All algebraic equalities use Fraction, never float.
A mathematical claim is exposed as a certificate whose verifier recomputes it.
No assertion of universality, efficient worst-case Gröbner, or Lean verification.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from typing import Sequence
import math

from ml_mathlib import Matrix, Vector, Polynomial as P, Q
from ml_mathlib_advanced import RationalFunction as RF, RationalInterval as I
from ml_mathlib_advanced import SO3, SE3
from ml_mathlib_exact import _qdivmod, _qextended_gcd, RationalLieAlgebra, interval_sqrt
from ml_mathlib_verified import rational_substitution


# ESTRATO 0 — modular exact linear solve with a checkable witness

def _prime(p: int) -> bool:
    if not isinstance(p, int) or isinstance(p, bool) or p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1 if d == 2 else 2
    return True


def _modular_gauss(a: Sequence[Sequence[int]], b: Sequence[int], p: int):
    """Return (det mod p, solution mod p), or (0,None) on rank deficiency."""
    n = len(a)
    rows = [[*map(lambda v: v % p, row), b[i] % p] for i, row in enumerate(a)]
    determinant = 1
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j]), None)
        if pivot is None:
            return 0, None
        if pivot != j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            determinant = -determinant
        v = rows[j][j]
        determinant = determinant * v % p
        inv = pow(v, -1, p)
        rows[j] = [t * inv % p for t in rows[j]]
        for i in range(n):
            if i == j:
                continue
            c = rows[i][j]
            if c:
                rows[i] = [(s - c * t) % p for s, t in zip(rows[i], rows[j])]
    return determinant % p, tuple(row[-1] for row in rows)


def _crt_update(a: int, modulus: int, b: int, p: int) -> int:
    return (a + modulus * ((b-a) * pow(modulus, -1, p) % p)) % (modulus*p)


@dataclass(frozen=True)
class ModularSolveCertificate:
    """Exact solution and a prime for which det(A) mod p != 0.

    Verification of A*x=b and the invertible modular minor proves the solution
    exists and is UNIQUE over Q. No trust in the modular reconstruction needed.
    """
    matrix: Matrix
    rhs: Vector
    solution: Vector
    nonsingular_prime: int

    def verify(self) -> bool:
        n, m = self.matrix.shape
        if n != m or self.rhs.dim != n or self.solution.dim != n:
            return False
        if not _prime(self.nonsingular_prime):
            return False
        p = self.nonsingular_prime
        denominators = [math.lcm(*(t.denominator for t in row)) for row in self.matrix.rows]
        a = [[int(v * d) for v in row] for row, d in zip(self.matrix.rows, denominators)]
        det, _ = _modular_gauss(a, [0]*n, p)
        return det != 0 and self.matrix @ self.solution == self.rhs


def modular_solve(matrix: Matrix, rhs: Vector, *, max_primes: int = 128,
                  primes: Sequence[int] | None = None) -> ModularSolveCertificate:
    """Certified CRT rational linear solver for NONSINGULAR square systems.

    Clears denominators row-wise, reconstructs det(A) and each Cramer numerator
    from modular solves and rechecks A*x=b in Q. Stops only after exact proof.
    For singular matrices or an exhausted prime budget, raises ValueError or
    RuntimeError instead of returning a potentially incorrect solution.
    """
    n, m = matrix.shape
    if n != m or rhs.dim != n or max_primes < 1:
        raise ValueError('Require a square system, matching RHS and positive budget')
    a, b = [], []
    for row, yi in zip(matrix.rows, rhs.entries):
        d = math.lcm(*(t.denominator for t in row), yi.denominator)
        a.append([int(v*d) for v in row])
        b.append(int(yi*d))
    if primes is None:
        def generator():
            t = (1 << 31)-1
            while t > 2:
                if _prime(t):
                    yield t
                t -= 2
        primes = generator()
    modulus, det_res, cramer = 1, 0, [0]*n
    first_good = None
    seen = set()
    for index, prime in enumerate(primes):
        if index >= max_primes:
            break
        if not _prime(prime) or prime in seen:
            raise ValueError('Primes must be distinct primes')
        seen.add(prime)
        det, x = _modular_gauss(a, b, prime)
        if x is None:
            continue
        first_good = prime if first_good is None else first_good
        det_res = _crt_update(det_res, modulus, det, prime)
        cramer = [_crt_update(v, modulus, det*xj % prime, prime)
                  for v, xj in zip(cramer, x)]
        modulus *= prime
        D = det_res if det_res <= modulus//2 else det_res - modulus
        nums = [v if v <= modulus//2 else v-modulus for v in cramer]
        if not D:
            continue
        result = Vector(tuple(F(t,D) for t in nums))
        certificate = ModularSolveCertificate(matrix, rhs, result, first_good)
        if certificate.verify():
            return certificate
    if matrix.determinant() == 0:
        raise ValueError('Singular rational system: unique solve impossible')
    raise RuntimeError('CRT budget exhausted before exact verification')


# ESTRATO 0 — certified real algebraic isolations and spectral polynomials

def _trim(a):
    b = [Q(x) for x in a]
    while b and b[-1] == 0:
        b.pop()
    return b


def _poly_value(p: Sequence[F], x: F) -> F:
    v = F(0)
    for a in reversed(p):
        v = v*x+a
    return v


def _poly_derivative(p: Sequence[F]):
    return _trim([i*c for i,c in enumerate(p)][1:])


def _squarefree(a: Sequence[F]):
    a = _trim(a)
    if len(a) <= 1:
        raise ValueError('Nonconstant univariate polynomial required')
    gcd, _, _ = _qextended_gcd(a, _poly_derivative(a))
    if not gcd:
        raise ArithmeticError('Invalid gcd')
    q, r = _qdivmod(a, gcd)
    if r:
        raise ArithmeticError('Inexact squarefree quotient')
    return _trim([v/q[-1] for v in q])


def _sturm(a: Sequence[F]):
    f = _squarefree(a)
    s = [f, _poly_derivative(f)]
    while s[-1]:
        _, r = _qdivmod(s[-2], s[-1])
        if not r:
            break
        s.append([-v for v in r])
    return tuple(s)


def _sign_at_side(p: Sequence[F], x: F, side: int):
    if side not in (-1,1):
        raise ValueError('One-sided direction must be ±1')
    degree = 0
    p = list(p)
    while p:
        s = _poly_value(p, x)
        if s:
            if degree % 2 and side < 0:
                s = -s
            return 1 if s > 0 else -1
        p = _poly_derivative(p)
        degree += 1
    return 0


def _variation(sturm, x: F, side: int):
    signs = [_sign_at_side(p, x, side) for p in sturm]
    signs = [s for s in signs if s]
    return sum(x != y for x,y in zip(signs, signs[1:]))


@dataclass(frozen=True)
class IsolatedRealRoot:
    """One real root of a rational univariate polynomial in [lo,hi].

    Revalidation uses Sturm variation at one-sided endpoints; a singleton
    interval is permitted only for an exact rational root.
    """
    polynomial: tuple[F, ...]
    lo: F
    hi: F

    def verify(self) -> bool:
        try:
            a = _trim(self.polynomial)
            lo, hi = Q(self.lo), Q(self.hi)
            if len(a) <= 1 or lo > hi:
                return False
            if lo == hi:
                return _poly_value(a, lo) == 0
            sturm = _sturm(a)
            if _poly_value(a, lo) == 0 or _poly_value(a, hi) == 0:
                return False
            return _variation(sturm, lo, 1) - _variation(sturm, hi, -1) == 1
        except (ValueError, ZeroDivisionError, ArithmeticError):
            return False


def isolate_real_roots(coefficients: Sequence[F], *, bits: int = 20,
                       max_splits: int = 100000) -> tuple[IsolatedRealRoot,...]:
    """Dyadic isolation of ALL DISTINCT real roots via a Sturm sequence.

    Multiple roots are handled through squarefree factorization. Rational
    roots discovered at bisection boundaries become singleton certificates.
    Returns only certified intervals and raises if the split budget is hit.
    """
    p = _trim(coefficients)
    if len(p) <= 1 or bits < 0 or max_splits < 1:
        raise ValueError('Polynomial degree, precision or split budget invalid')
    sf = _squarefree(p)
    R = 2 + max(abs(c/sf[-1]) for c in sf[:-1])
    st = _sturm(sf)
    count = lambda a,b: _variation(st,a,1)-_variation(st,b,-1)
    stack = [(-R,R)]
    roots = []
    splits = 0
    while stack:
        a,b = stack.pop()
        if a == b:
            roots.append(IsolatedRealRoot(tuple(p),a,b))
            continue
        amount = count(a,b)
        if amount == 0:
            continue
        if amount == 1 and b-a <= F(1,2**bits):
            roots.append(IsolatedRealRoot(tuple(p),a,b))
            continue
        if splits >= max_splits:
            raise RuntimeError('Sturm split budget exhausted')
        splits += 1
        m = (a+b)/2
        if _poly_value(sf,m) == 0:
            stack.extend([(a,m),(m,b),(m,m)])
        else:
            stack.extend([(a,m),(m,b)])
    roots.sort(key=lambda r:(r.lo,r.hi))
    if not all(r.verify() for r in roots):
        raise ArithmeticError('Root isolation verification failed')
    return tuple(roots)


def characteristic_polynomial(a: Matrix) -> tuple[F,...]:
    """Coefficients low-to-high of det(tI-A) via Faddeev–LeVerrier over Q."""
    n,m = a.shape
    if n != m:
        raise ValueError('Square matrix required')
    B = Matrix.identity(n)
    coefficients = [F(1)]
    for k in range(1,n+1):
        C = a @ B
        ck = -sum((C.rows[i][i] for i in range(n)),F(0))/k
        coefficients.append(ck)
        B = C + Matrix.identity(n).scale(ck)
    return tuple(reversed(coefficients))


def real_spectrum_intervals(a: Matrix, bits: int=20):
    """Isolate distinct real eigenvalues; no claim about complex spectrum/SVD."""
    return isolate_real_roots(characteristic_polynomial(a),bits=bits)


# ESTRATO 1 — rational atlas cocycle and generic tensor contraction

@dataclass(frozen=True)
class RationalAtlasCocycle:
    """Finite local atlas transition cocycle over rational function fields.

    transitions[i][j] sends coordinates of chart j to chart i.
    Algebraic equalities are certified in Q(x), including g_ij g_jk = g_ik.
    This alone DOES NOT verify coverage of the underlying topological space.
    """
    transitions: tuple[tuple[tuple[RF,...],...],...]

    def __post_init__(self):
        N = len(self.transitions)
        if N < 1 or any(len(row) != N for row in self.transitions):
            raise ValueError('Square transition matrix required')
        dim = len(self.transitions[0][0])
        if dim < 1 or any(len(t) != dim or any(f.numerator.dimension!=dim for f in t)
                             for row in self.transitions for t in row):
            raise ValueError('Transition dimensions mismatch')
        identity = tuple(RF.from_polynomial(P.variable(dim,k)) for k in range(dim))
        for i in range(N):
            if self.transitions[i][i] != identity:
                raise ValueError('Identity transition violated')
            for j in range(N):
                for k in range(N):
                    composition = tuple(rational_substitution(f,self.transitions[j][k])
                                        for f in self.transitions[i][j])
                    if composition != self.transitions[i][k]:
                        raise ValueError('Cocycle identity violated')

    @property
    def dimension(self):
        return len(self.transitions[0][0])

    def transition(self,i,j):
        return self.transitions[i][j]


@dataclass(frozen=True)
class DenseTensor:
    """Mixed-variance coordinate tensor on Q^n (finite dimensions).

    Components map an index tuple to Q. Variance +1 contravariant and -1
    covariant. Contractions pair one of each, never two upper/lower slots.
    """
    dimension:int
    variance:tuple[int,...]
    components:tuple[tuple[tuple[int,...],F],...]

    def __post_init__(self):
        if self.dimension<1 or any(v not in (-1,1) for v in self.variance):
            raise ValueError('Invalid tensor rank/variance')
        clean = {}
        for indices, coeff in self.components:
            if len(indices)!=len(self.variance) or any(i not in range(self.dimension) for i in indices):
                raise ValueError('Tensor index out of range')
            clean[tuple(indices)] = clean.get(tuple(indices),F(0))+Q(coeff)
        object.__setattr__(self,'components',tuple(sorted((k,v) for k,v in clean.items() if v)))

    @property
    def rank(self):
        return len(self.variance)

    def tensor_product(self,other:'DenseTensor') -> 'DenseTensor':
        if self.dimension!=other.dimension:
            raise ValueError('Tensor dimensions mismatch')
        return DenseTensor(self.dimension,self.variance+other.variance,tuple(
            (a+b,x*y) for a,x in self.components for b,y in other.components))

    def contract(self,i:int,j:int)->'DenseTensor':
        if not 0<=i<self.rank or not 0<=j<self.rank or i==j or self.variance[i]==self.variance[j]:
            raise ValueError('Contraction requires one upper and one lower slot')
        var=tuple(x for k,x in enumerate(self.variance) if k not in (i,j))
        entries=[]
        for ix,v in self.components:
            if ix[i]==ix[j]:
                entries.append((tuple(x for k,x in enumerate(ix) if k not in (i,j)),v))
        return DenseTensor(self.dimension,var,tuple(entries))

    def coordinate_transform(self,jacobian:Matrix)->'DenseTensor':
        """Transform tensor with a linear coordinate map y=A x.

        Upper slots get A; lower slots get A^{-T}. Checks all dimensions;
        this transformation is exact, including mixed tensors and traces.
        """
        n=self.dimension
        if jacobian.shape!=(n,n):raise ValueError('Square Jacobian required')
        cov=jacobian.inverse().transpose()
        tensors=[jacobian if v==1 else cov for v in self.variance]
        rows=[]
        for out in product(range(n),repeat=self.rank):
            coef=F(0)
            for orig,value in self.components:
                term=value
                for axis,(i,j) in enumerate(zip(out,orig)):
                    term*=tensors[axis].rows[i][j]
                coef+=term
            if coef:rows.append((out,coef))
        return DenseTensor(n,self.variance,tuple(rows))


# ESTRATO 2 — infinite discrete measure and rational Gaussian moments

@dataclass(frozen=True)
class GeometricCountableMeasure:
    """Probability on (N, P(N)) with mass p*(1-p)^k, 0<p<=1.

    Every finite prefix and infinite tail has an exact rational measure.
    Factorial moments follow from the pgf p/(1-q t), an analytic identity.
    Does not encode arbitrary subsets of N as decidable Python objects.
    """
    p:F

    def __post_init__(self):
        object.__setattr__(self,'p',Q(self.p))
        if not F(0)<self.p<=1:
            raise ValueError('Geometric parameter must lie in (0,1]')

    def atom(self,k:int)->F:
        if not isinstance(k,int) or k<0:
            raise ValueError('Atom index must be a nonnegative integer')
        return self.p*(1-self.p)**k

    def tail(self,k:int)->F:
        if not isinstance(k,int) or k<0:
            raise ValueError('Tail threshold must be a nonnegative integer')
        return (1-self.p)**k

    def prefix(self,k:int)->F:
        return 1-self.tail(k)

    def factorial_moment(self,n:int)->F:
        if not isinstance(n,int) or n<0:raise ValueError('Order must be nonnegative')
        return F(math.factorial(n)) * ((1-self.p)/self.p)**n

    def raw_moment(self,n:int)->F:
        """E[X^n] = Σ_{k=0}^n S(n,k) E[(X)_k], using Stirling(2)."""
        if not isinstance(n,int) or n<0:raise ValueError('Order must be nonnegative')
        S=[[0]*(n+1) for _ in range(n+1)]
        S[0][0]=1
        for i in range(1,n+1):
            for k in range(1,i+1):
                S[i][k]=S[i-1][k-1]+k*S[i-1][k]
        return sum((S[n][k]*self.factorial_moment(k) for k in range(n+1)),F(0))

    def expectation(self,polynomial:P)->F:
        if polynomial.dimension!=1:raise ValueError('Univariate polynomial required')
        return sum((c*self.raw_moment(ex[0]) for ex,c in polynomial.terms),F(0))


@dataclass(frozen=True)
class MultivariateGaussianLaw:
    """Exact polynomial moment functional of N(mu,Sigma) over Q.

    Input covariance must be strictly positive-definite (rational LDL^T).
    Mixed moments satisfy Gaussian integration-by-parts / Wick recursion.
    This represents analytic polynomial expectations, NOT numerical samples.
    """
    mean:tuple[F,...]
    covariance:Matrix

    def __post_init__(self):
        mu=tuple(Q(v) for v in self.mean)
        n=len(mu)
        if n<1 or self.covariance.shape!=(n,n) or self.covariance.transpose()!=self.covariance:
            raise ValueError('Gaussian dimension/covariance mismatch')
        from ml_mathlib_advanced import rational_ldlt
        _, pivots = rational_ldlt(self.covariance)
        if any(v <= 0 for v in pivots):
            raise ValueError('Covariance must be strictly positive-definite')
        object.__setattr__(self,'mean',mu)

    @property
    def dimension(self):return len(self.mean)

    def monomial_moment(self,exponents:Sequence[int])->F:
        e=tuple(exponents);n=self.dimension
        if len(e)!=n or any(not isinstance(k,int) or k<0 for k in e):
            raise ValueError('Monomial exponents invalid')
        mu, covariance=self.mean,self.covariance.rows
        @lru_cache(None)
        def recurse(exp):
            if not any(exp):return F(1)
            i=next(j for j,v in enumerate(exp) if v)
            below=list(exp);below[i]-=1
            value=mu[i]*recurse(tuple(below))
            for j in range(n):
                if below[j]:
                    reduced=below[:];reduced[j]-=1
                    value+=covariance[i][j]*below[j]*recurse(tuple(reduced))
            return value
        return recurse(e)

    def expectation(self,f:P)->F:
        if f.dimension!=self.dimension:raise ValueError('Dimension mismatch')
        return sum((c*self.monomial_moment(exp) for exp,c in f.terms),F(0))

    def affine_pushforward(self,A:Matrix,b:Vector)->'MultivariateGaussianLaw':
        rows,cols=A.shape
        if cols!=self.dimension or b.dim!=rows:raise ValueError('Affine map mismatch')
        m=A@Vector(self.mean)+b
        return MultivariateGaussianLaw(m.entries,A@self.covariance@A.transpose())


@dataclass(frozen=True)
class FisherSimplexStrata:
    """Stratified closed simplex, with exact support and certified distances.

    Fisher metric is regular only ON EACH positive-probability face. Distances
    on the metric completion are calculated using the sqrt embedding.
    """
    probabilities:tuple[F,...]

    def __post_init__(self):
        p=tuple(Q(v) for v in self.probabilities)
        if len(p)<2 or any(v<0 for v in p) or sum(p)!=1:
            raise ValueError('Must be a point of the CLOSED probability simplex')
        object.__setattr__(self,'probabilities',p)

    def support(self)->tuple[int,...]:
        return tuple(i for i,p in enumerate(self.probabilities) if p>0)

    def face_dimension(self)->int:
        return len(self.support())-1

    def interior_metric(self):
        from ml_mathlib_verified import CategoricalInformationGeometry
        support=self.support()
        if len(support)<2:
            return None
        return CategoricalInformationGeometry(tuple(self.probabilities[i] for i in support))

    def distance_interval(self,other:'FisherSimplexStrata',bits:int=24):
        from ml_mathlib_exact import CertifiedFisherSphere
        if len(self.probabilities)!=len(other.probabilities):
            raise ValueError('Probability spaces differ')
        return CertifiedFisherSphere.distance_interval(self.probabilities,other.probabilities,bits=bits)

    def midpoint_intervals(self,other:'FisherSimplexStrata',digits:int=22):
        """Enclose the Fisher geodesic midpoint on the CLOSED simplex.

        If u_i=√p_i and v_i=√q_i, m_i=(u_i+v_i)^2 / (2+2 u·v).
        Positive orthant ensures denominator strictly positive even on faces.
        """
        if len(self.probabilities)!=len(other.probabilities):
            raise ValueError('Probability spaces differ')
        U=[interval_sqrt(v,digits) for v in self.probabilities]
        V=[interval_sqrt(v,digits) for v in other.probabilities]
        inner=sum((a*b for a,b in zip(U,V)),I(0,0))
        denom=I(2,2)*(I(1,1)+inner)
        result=[]
        for u,v in zip(U,V):
            w=u+v
            square=w*w  # all w>=0
            result.append(I(max(F(0),(square/denom).lo),min(F(1),(square/denom).hi)))
        return tuple(result)


# ESTRATO 3 — general polynomial contact dynamics

@dataclass(frozen=True)
class PolynomialContactFlow:
    """Contact Hamiltonian equations with eta=ds-Σp_i dq_i on Q^(2n+1).

    X_H(q,p,s) = (H_p, -H_q-p H_s, Σ p H_p-H).
    Universal polynomial identities: η(X_H)=-H,
    L_(X_H)η=-H_s η, and X_H[H]=-H_s H.
    For H=H0(q,p)+γs, E=H is exponentially damped for γ>0,
    but no claim of general contact integrator is made.
    """
    hamiltonian:P

    def __post_init__(self):
        d=self.hamiltonian.dimension
        if d<3 or d%2 != 1:raise ValueError('Contact phase dimension must be 2n+1')

    @property
    def pairs(self):return (self.hamiltonian.dimension-1)//2

    def field(self)->tuple[P,...]:
        H=self.hamiltonian;n=self.pairs;d=H.dimension
        p=tuple(P.variable(d,n+i) for i in range(n))
        hz=H.diff(d-1)
        return (tuple(H.diff(n+i) for i in range(n))+
                tuple(-H.diff(i)-p[i]*hz for i in range(n))+
                (sum((p[i]*H.diff(n+i) for i in range(n)),P.constant(d,0))-H,))

    def lie(self,f:P)->P:
        if f.dimension!=self.hamiltonian.dimension:
            raise ValueError('Incorrect contact dimension')
        return sum((v*f.diff(i) for i,v in enumerate(self.field())),P.constant(f.dimension,0))

    def verify_identities(self)->bool:
        H=self.hamiltonian;hz=H.diff(H.dimension-1)
        X=self.field();n=self.pairs;d=H.dimension
        p=[P.variable(d,n+i) for i in range(n)]
        eta=-sum((p[i]*X[i] for i in range(n)),P.constant(d,0))+X[-1]
        if eta != -H or self.lie(H)!=-hz*H:return False
        # Cartan: L_X eta = i_X d eta + d(i_X eta).
        # Evaluate all coefficient polynomials of the resulting one-form.
        for i in range(n):
            if -X[n+i]-H.diff(i) != p[i]*hz:return False
            if not (X[i]-H.diff(n+i)).is_zero:return False
        return -H.diff(d-1) == -hz


# ESTRATO 4 — exact rational Lie-group actions and softmax derivatives

class CayleySO3:
    """Exact Cayley transform from rational so(3) skew matrix to SO(3)."""
    @staticmethod
    def from_generator(A:Matrix)->SO3:
        if A.shape!=(3,3) or A.transpose()!=-A:
            raise ValueError('Cayley input must be skew-symmetric 3x3')
        identity=Matrix.identity(3)
        return SO3((identity-A).inverse()@(identity+A))

    @staticmethod
    def adjoint(rotation:SO3,generator:Matrix)->Matrix:
        if generator.shape!=(3,3) or generator.transpose()!=-generator:
            raise ValueError('Expected skew 3x3 Lie algebra element')
        return rotation.matrix @ generator @ rotation.matrix.transpose()


class SoftmaxJet:
    """Symbolic first and second derivatives of softmax in terms of weights.

    Returned expressions have no numeric approximations. They can be
    evaluated with IntervalSoftmax's rational interval weights as enclosures.
    """
    @staticmethod
    def jacobian(weights:Sequence[F],temperature:F=1):
        w=tuple(Q(v) for v in weights);t=Q(temperature)
        if t<=0 or not w or any(v<0 for v in w) or sum(w)!=1:
            raise ValueError('Normalized positive weights and temperature required')
        return tuple(tuple(w[i]*(int(i==j)-w[j])/t for j in range(len(w)))
                     for i in range(len(w)))

    @staticmethod
    def hessian(weights:Sequence[F],temperature:F=1):
        w=tuple(Q(v) for v in weights);t=Q(temperature)
        SoftmaxJet.jacobian(w,t)
        n=len(w)
        return tuple(tuple(tuple(w[i]*((int(i==j)-w[j])*(int(i==k)-w[k])
                   - w[j]*(int(j==k)-w[k]))/t**2 for k in range(n))
                     for j in range(n)) for i in range(n))

    @staticmethod
    def vector_jacobian_product(weights:Sequence[F],cotangent:Sequence[F],temperature:F=1):
        w=tuple(Q(v) for v in weights);v=tuple(Q(x) for x in cotangent)
        if len(w)!=len(v):raise ValueError('Cotangent mismatch')
        J=SoftmaxJet.jacobian(w,temperature)
        return tuple(sum((v[i]*J[i][j] for i in range(len(w))),F(0)) for j in range(len(w)))


# ESTRATO 5 — generic semisimple Lie-Poisson quadratic Casimir

@dataclass(frozen=True)
class KillingCasimirCertificate:
    """Nondegenerate Killing form determines a Lie–Poisson quadratic Casimir.

    The verifier checks π∇C = 0 as an exact polynomial identity, after
    independently reconstructing π from structure constants. A degenerate
    Killing form raises instead of silently returning an invalid Casimir.
    """
    lie_algebra:RationalLieAlgebra
    killing:Matrix
    casimir:P

    def verify(self)->bool:
        n=self.lie_algebra.dimension
        c=self.lie_algebra.structure
        K=Matrix(tuple(tuple(sum((c[i][a][b]*c[j][b][a] for a in range(n) for b in range(n)),F(0))
                                 for j in range(n)) for i in range(n)))
        if K!=self.killing or K.determinant()==0:return False
        xs=[P.variable(n,i) for i in range(n)]
        inverse=K.inverse()
        canonical=sum((inverse.rows[i][j]*xs[i]*xs[j]/2
                       for i in range(n) for j in range(n)),P.constant(n,0))
        if self.casimir != canonical:
            return False
        for i in range(n):
            field=sum((sum((c[i][j][k]*xs[k] for k in range(n)),P.constant(n,0)) * self.casimir.diff(j)
                       for j in range(n)),P.constant(n,0))
            if not field.is_zero:return False
        return True


def killing_casimir(algebra:RationalLieAlgebra)->KillingCasimirCertificate:
    n=algebra.dimension;c=algebra.structure
    K=Matrix(tuple(tuple(sum((c[i][a][b]*c[j][b][a] for a in range(n) for b in range(n)),F(0))
                         for j in range(n)) for i in range(n)))
    if K.determinant()==0:
        raise ValueError('Killing form degenerate: formula does not apply')
    inverse=K.inverse()
    x=[P.variable(n,i) for i in range(n)]
    C=sum((inverse.rows[i][j]*x[i]*x[j]/2 for i in range(n) for j in range(n)),P.constant(n,0))
    certificate=KillingCasimirCertificate(algebra,K,C)
    if not certificate.verify():raise ArithmeticError('Casimir verification failed')
    return certificate


# ESTRATO 3 — formal symplectic Jacobian of arbitrary polynomial midpoint maps

@dataclass(frozen=True)
class ImplicitMidpointSymplecticCertificate:
    """Exact Jacobian identity for the locally defined midpoint branch.

    The implicit equation is y = z + h J∇H((z+y)/2). Where the implicit
    Jacobian M=I-(h/2)JH'' is invertible, Dy/Dz=M^{-1}(I+(h/2)JH'').
    For ANY polynomial H with symmetric Hessian, Dy/Dz is symplectic.
    This certificate is an identity of rational functions in the formal
    midpoint m; it does NOT prove existence of a solution for a given z.
    Combine with MidpointContractionCertificate to prove a local solution.
    """
    hamiltonian:P
    step_size:F
    jacobian:tuple[tuple[RF,...],...]

    @staticmethod
    def _zero(d:int):return RF.from_polynomial(P.constant(d,0))

    def verify(self)->bool:
        H=self.hamiltonian
        d=H.dimension
        if d%2 or d<2 or len(self.jacobian)!=d or any(len(row)!=d for row in self.jacobian):
            return False
        zero=self._zero(d)
        J=lambda i,j: (1 if i<d//2 and j==i+d//2 else
                       -1 if i>=d//2 and j==i-d//2 else 0)
        try:
            for i in range(d):
                for j in range(d):
                    entry=sum((self.jacobian[k][i]*self.jacobian[l][j]*J(k,l)
                               for k in range(d) for l in range(d) if J(k,l)),zero)
                    if entry!=J(i,j):return False
            # Recompute and check the defining linear implicit identity.
            half=Q(self.step_size)/2
            for i in range(d):
                for j in range(d):
                    expected=RF.from_polynomial(P.constant(d,int(i==j)))
                    lhs=sum((RF.from_polynomial(
                        P.constant(d,int(i==k))-half*sum((J(i,t)*H.diff(t).diff(k)
                        for t in range(d)),P.constant(d,0))) * self.jacobian[k][j]
                        for k in range(d)),zero)
                    rhs=expected + RF.from_polynomial(half*sum((J(i,t)*H.diff(t).diff(j)
                        for t in range(d)),P.constant(d,0)))
                    if lhs!=rhs:return False
            return True
        except (ZeroDivisionError,ValueError,ArithmeticError):
            return False


def formal_midpoint_symplectic(hamiltonian:P,step_size:F)->ImplicitMidpointSymplecticCertificate:
    """Construct M^{-1}N in Frac(Q[m]) and independently verify symplecticity."""
    from ml_mathlib_exact import rational_matrix_inverse
    H=hamiltonian;d=H.dimension
    if d<2 or d%2:raise ValueError('Canonical phase must have 2n coordinates')
    n=d//2;h=Q(step_size);zero=RF.from_polynomial(P.constant(d,0))
    eye=lambda i,j: RF.from_polynomial(P.constant(d,int(i==j)))
    G=tuple(tuple((H.diff(n+i).diff(j) if i<n else -H.diff(i-n).diff(j))
                  for j in range(d)) for i in range(d))
    M=tuple(tuple(eye(i,j)-h*G[i][j]/2 for j in range(d)) for i in range(d))
    N=tuple(tuple(eye(i,j)+h*G[i][j]/2 for j in range(d)) for i in range(d))
    inv=rational_matrix_inverse(M)
    J=tuple(tuple(sum((inv[i][k]*N[k][j] for k in range(d)),zero)
                      for j in range(d)) for i in range(d))
    cert=ImplicitMidpointSymplecticCertificate(H,h,J)
    if not cert.verify():raise ArithmeticError('Implicit symplectic identity not certified')
    return cert


# ESTRATO 4 — exact adjoint representation of the rational SE(3) group

def _skew3(v:Sequence[F])->Matrix:
    x,y,z=map(Q,v)
    return Matrix(((0,-z,y),(z,0,-x),(-y,x,0)))


def _cross3(a:Sequence[F],b:Sequence[F])->tuple[F,F,F]:
    return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])


class RationalSE3Adjoint:
    """Ad_(R,t) on twists (linear v, angular ω): (Rv+t×Rω,Rω).

    The Lie bracket is [(v,ω),(v',ω')] =
    (ω×v'−ω'×v,ω×ω'). All operations are rational and exact.
    """
    @staticmethod
    def matrix(group:SE3)->Matrix:
        if not isinstance(group,SE3):raise TypeError('SE3 element required')
        R=group.rotation.matrix
        tr=_skew3(group.translation.entries)@R
        return Matrix(tuple(tuple((R.rows[i][j] if j<3 else tr.rows[i][j-3])
                                  if i<3 else (0 if j<3 else R.rows[i-3][j-3])
                                  for j in range(6)) for i in range(6)))

    @staticmethod
    def bracket(a:Vector,b:Vector)->Vector:
        if a.dim!=6 or b.dim!=6:raise ValueError('Twists must have six coordinates')
        av,aw=a.entries[:3],a.entries[3:]
        bv,bw=b.entries[:3],b.entries[3:]
        upper=tuple(x-y for x,y in zip(_cross3(aw,bv),_cross3(bw,av)))
        return Vector(upper+_cross3(aw,bw))

    @classmethod
    def verify_homomorphism(cls,g:SE3,a:Vector,b:Vector)->bool:
        D=cls.matrix(g)
        return D@cls.bracket(a,b)==cls.bracket(D@a,D@b)

@dataclass(frozen=True)
class CompleteRealRootCertificate:
    """Certify a complete, disjoint cover of all DISTINCT real roots of p.

    Uses Sturm's theorem for the squarefree part and a strict rational Cauchy
    bound. This checks completeness independently of the isolator's search.
    """
    polynomial: tuple[F, ...]
    intervals: tuple[IsolatedRealRoot, ...]

    def verify(self) -> bool:
        try:
            p = _trim(self.polynomial)
            if len(p) <= 1:
                return False
            sf = _squarefree(p)
            bound = F(2) + max(abs(c / sf[-1]) for c in sf[:-1])
            st = _sturm(sf)
            total = _variation(st, -bound, 1) - _variation(st, bound, -1)
            roots = sorted(self.intervals, key=lambda x: (x.lo, x.hi))
            if any(r.polynomial != tuple(p) or not r.verify() for r in roots):
                return False
            if any(r.lo < -bound or r.hi > bound for r in roots):
                return False
            if any(a.hi >= b.lo for a, b in zip(roots, roots[1:])):
                return False
            return len(roots) == total
        except (ValueError, ZeroDivisionError, ArithmeticError, TypeError):
            return False


def certify_all_real_roots(coefficients: Sequence[F], *, bits: int = 20,
                           max_splits: int = 100000) -> CompleteRealRootCertificate:
    p = tuple(_trim(coefficients))
    cert = CompleteRealRootCertificate(p, isolate_real_roots(p, bits=bits,
                                                            max_splits=max_splits))
    if not cert.verify():
        raise ArithmeticError('Root completeness proof failed')
    return cert
