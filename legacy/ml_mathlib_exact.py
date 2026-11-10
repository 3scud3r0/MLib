#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ML-MATHLIB 0.3 — independent, exact and explicitly bounded extensions.

No PyTorch, NumPy, SymPy, SciPy, or hidden numerical proof assumptions.
The objects here certify mathematical statements only in their documented domains.
Most important distinctions:
* exact rational/algebraic arithmetic != an external proof-kernel certificate;
* a certified interval fixed point != a rational closed-form fixed point;
* a polynomial invariant discovered under degree cutoff != a complete invariant algebra.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from collections import defaultdict
import math
from typing import Sequence
from ml_mathlib import Q, Vector, Matrix, Polynomial, SymplecticSpace, HamiltonianFlow
from ml_mathlib_advanced import (RationalFunction, RationalInterval, interval_exp,
    interval_sin, interval_cos, interval_log, interval_pi, groebner_basis,
    polynomial_division, leading_term, independent_invariants, pruned_monomials,
    VelocityVerlet, SymbolicExpr, SO3)

# ────────────────────────────── Exact modular arithmetic ──────────────
def _is_prime(p: int) -> bool:
    if not isinstance(p, int) or isinstance(p, bool) or p < 2:
        return False
    return all(p % d for d in range(2, math.isqrt(p) + 1))

def crt_pair(a: int, m: int, b: int, n: int) -> tuple[int, int]:
    """Chinese remainder theorem for coprime moduli; result in [0,m*n)."""
    if m <= 0 or n <= 0 or math.gcd(m,n) != 1:
        raise ValueError('CRT requires positive, coprime moduli')
    k = ((b-a)*pow(m,-1,n)) % n
    return (a+m*k) % (m*n), m*n

def crt_many(congruences: Sequence[tuple[int,int]]) -> tuple[int,int]:
    if not congruences: raise ValueError('At least one congruence required')
    a,m = 0,1
    for b,n in congruences: a,m = crt_pair(a,m,b,n)
    return a,m

def _integer_rows(rows: Sequence[Sequence[F]]) -> tuple[list[list[int]], int]:
    if not rows or not rows[0] or any(len(r)!=len(rows[0]) for r in rows):
        raise ValueError('Nonempty rectangular matrix required')
    result=[]; multiplier=1
    # Product of row denominators is the determinant scaling factor.
    for row in rows:
        f=math.lcm(*(Q(x).denominator for x in row))
        result.append([int(Q(x)*f) for x in row]);multiplier*=f
    return result,multiplier

def modular_determinant(a:Matrix, primes:Sequence[int]|None=None, max_primes:int=128) -> F:
    """Certified determinant using modular Gaussian elimination + Hadamard/L1 bound.

    Reconstructs until product of moduli >2*determinant bound. Generates
    additional 31-bit primes by default, with explicit max_primes cap; a
    caller-supplied prime list may also be used. Never returns an uncertified
    residue if the bound is not reached.
    """
    n,m=a.shape
    if n!=m: raise ValueError('Square matrix required')
    rows,den=_integer_rows(a.rows)
    bound=math.prod(sum(abs(x) for x in row) for row in rows)
    if bound == 0: return F(0)
    if max_primes<1:raise ValueError('Positive prime cap required')
    if primes is None:
        def prime_generator():
            candidate=(1<<31)-1
            while candidate>2:
                if _is_prime(candidate):yield candidate
                candidate-=2
        primes=prime_generator()
    mods=[]; residue,mod=0,1
    for index,p in enumerate(primes):
        if index>=max_primes:break
        if not _is_prime(p) or p in mods: raise ValueError('Distinct primes required')
        mods.append(p)
        b=[[x%p for x in row] for row in rows]
        det=1
        for col in range(n):
            pivot=next((k for k in range(col,n) if b[k][col]),None)
            if pivot is None:det=0;break
            if pivot!=col:
                b[pivot],b[col]=b[col],b[pivot];det=-det
            v=b[col][col];det=det*v%p;inv=pow(v,-1,p)
            for i in range(col+1,n):
                factor=b[i][col]*inv%p
                if factor:
                    for j in range(col+1,n):b[i][j]=(b[i][j]-factor*b[col][j])%p
                    b[i][col]=0
        residue,mod=crt_pair(residue,mod,det,p)
        if mod>2*bound:
            signed=residue if residue<=mod//2 else residue-mod
            if not -bound<=signed<=bound:raise ArithmeticError('CRT determinant exceeded proven bound')
            return F(signed,den)
    raise RuntimeError('More primes needed to certify determinant')

def primitive_integer_kernel(matrix:Sequence[Sequence[F]]) -> tuple[tuple[F,...],...]:
    """Rational nullspace via integer row elimination and gcd normalization.

    Faster than dense Fraction RREF on some problems, but *not* a polynomial-bit
    complexity guarantee. Each returned vector is checked against input rows.
    """
    if not matrix:return ()
    rows,_=_integer_rows(matrix);n=len(rows[0]);m=len(rows)
    pivot_cols=[];r=0
    for j in range(n):
        k=next((i for i in range(r,m) if rows[i][j]),None)
        if k is None:continue
        rows[r],rows[k]=rows[k],rows[r]
        for i in range(r+1,m):
            if not rows[i][j]:continue
            a,b=rows[r][j],rows[i][j]
            g=math.gcd(a,b)
            rows[i]=[(a//g)*x-(b//g)*y for x,y in zip(rows[i],rows[r])]
            content=math.gcd(*rows[i])
            if content>1:rows[i]=[x//content for x in rows[i]]
        pivot_cols.append(j);r+=1
        if r==m:break
    free=[j for j in range(n) if j not in pivot_cols]
    basis=[]
    for k in free:
        x=[F(0)]*n;x[k]=F(1)
        for i in range(len(pivot_cols)-1,-1,-1):
            j=pivot_cols[i]
            x[j]=-sum((rows[i][col]*x[col] for col in range(j+1,n)),F(0))/rows[i][j]
        if any(sum((Q(a)*v for a,v in zip(row,x)),F(0)) for row in matrix):
            raise ArithmeticError('Integer nullspace verification failed')
        basis.append(tuple(x))
    return tuple(basis)

# ─────────────────────────── Certified general number fields ─────────
def _trim(a):
    b=list(a)
    while b and b[-1]==0:b.pop()
    return b

def _pdivmod(a,b,p):
    a=_trim([x%p for x in a]);b=_trim([x%p for x in b])
    if not b:raise ZeroDivisionError('zero polynomial')
    q=[0]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b):
        shift=len(a)-len(b);c=a[-1]*pow(b[-1],-1,p)%p;q[shift]=c
        for j,v in enumerate(b):a[shift+j]=(a[shift+j]-c*v)%p
        a=_trim(a)
    return _trim(q),a

def _pmulmod(a,b,f,p):
    c=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):c[i+j]=(c[i+j]+u*v)%p
    return _pdivmod(c,f,p)[1]

def _ppowmod(a,e,f,p):
    result=[1]
    while e:
        if e&1:result=_pmulmod(result,a,f,p)
        e>>=1
        if e:a=_pmulmod(a,a,f,p)
    return result

def _pgcd(a,b,p):
    while b:a,b=b,_pdivmod(a,b,p)[1]
    if not a:return []
    v=pow(a[-1],-1,p)
    return [(t*v)%p for t in a]

def _prime_factors(n):
    ans=[];d=2
    while d*d<=n:
        if n%d==0:
            ans.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:ans.append(n)
    return ans

def irreducible_mod_prime(f:Sequence[F],p:int)->bool:
    """Rabin irreducibility test over F_p (a sufficient Q-irreducibility certificate).

    Requires leading coefficient not divisible by p after reduction. Coefficient
    denominators must be invertible modulo p.
    """
    if not _is_prime(p):raise ValueError('p must be prime')
    if len(f)<2:raise ValueError('Positive degree expected')
    poly=[]
    for v in f:
        v=Q(v)
        if v.denominator%p==0:raise ValueError('Bad reduction: denominator divisible by p')
        poly.append(v.numerator*pow(v.denominator,-1,p)%p)
    poly=_trim(poly)
    if len(poly)!=len(f):return False
    n=len(poly)-1;poly=[x*pow(poly[-1],-1,p)%p for x in poly]
    x=_pdivmod([0,1],poly,p)[1];u=x[:]
    for k in range(1,n+1):
        u=_ppowmod(u,p,poly,p)
        if k in {n//q for q in _prime_factors(n)}:
            diff=[(u[i] if i<len(u) else 0)-(x[i] if i<len(x) else 0) for i in range(max(len(u),len(x)))]
            if len(_pgcd(diff,poly,p))>1:return False
    return _trim([ (u[i] if i<len(u) else 0)-(x[i] if i<len(x) else 0) for i in range(max(len(u),len(x))) ])==[]

def _qdivmod(a,b):
    a=_trim([Q(v) for v in a]);b=_trim([Q(v) for v in b])
    if not b:raise ZeroDivisionError
    q=[F(0)]*max(0,len(a)-len(b)+1)
    while len(a)>=len(b):
        k=len(a)-len(b);v=a[-1]/b[-1];q[k]=v
        for j,t in enumerate(b):a[j+k]-=v*t
        a=_trim(a)
    return _trim(q),a

def _qextended_gcd(a,b):
    s0,s1=[F(1)],[];t0,t1=[],[F(1)]
    while b:
        q,r=_qdivmod(a,b);a,b=b,r
        def sub(u,v):
            out=[F(0)]*max(len(u),len(q)+len(v)-1)
            for i,c in enumerate(u):out[i]+=c
            for i,c in enumerate(q):
                for j,d in enumerate(v):out[i+j]-=c*d
            return _trim(out)
        s0,s1=s1,sub(s0,s1)
        t0,t1=t1,sub(t0,t1)
    return a,s0,t0

@dataclass(frozen=True)
class NumberField:
    """Q[α]/(m(α)), with machine-verifiable irreducibility modulo one prime.

    This sufficient criterion is intentionally conservative: a Q-irreducible
    polynomial may be rejected when no suitable certifying prime is supplied.
    """
    minimal_polynomial:tuple[F,...]
    certifying_prime:int

    def __post_init__(self):
        f=tuple(Q(x) for x in self.minimal_polynomial)
        if len(f)<2 or f[-1]==0:raise ValueError('Nonconstant minimal polynomial needed')
        f=tuple(c/f[-1] for c in f)
        if not irreducible_mod_prime(f,self.certifying_prime):
            raise ValueError('Polynomial not proven irreducible by supplied prime')
        object.__setattr__(self,'minimal_polynomial',f)

    @property
    def degree(self):return len(self.minimal_polynomial)-1

    def element(self,values=0):
        if isinstance(values,AlgebraicElement):
            if values.field!=self:raise ValueError('Different algebraic fields')
            return values
        if isinstance(values,(int,str,F)):values=(Q(values),)
        _,remainder=_qdivmod(tuple(Q(t) for t in values),self.minimal_polynomial)
        return AlgebraicElement(self,tuple(remainder)+(F(0),)*(self.degree-len(remainder)))

    def alpha(self):return self.element((0,1))

@dataclass(frozen=True)
class AlgebraicElement:
    field:NumberField
    coefficients:tuple[F,...]

    def _to(self,other):return self.field.element(other)
    def __add__(self,other):
        b=self._to(other)
        return self.field.element(tuple(x+y for x,y in zip(self.coefficients,b.coefficients)))
    __radd__=__add__
    def __neg__(self):return self.field.element(tuple(-x for x in self.coefficients))
    def __sub__(self,other):return self+(-self._to(other))
    def __rsub__(self,other):return self._to(other)+(-self)
    def __mul__(self,other):
        b=self._to(other);n=self.field.degree;z=[F(0)]*(2*n-1)
        for i,a in enumerate(self.coefficients):
            for j,c in enumerate(b.coefficients):z[i+j]+=a*c
        return self.field.element(z)
    __rmul__=__mul__
    def __eq__(self,other):
        try:b=self._to(other)
        except (TypeError,ValueError):return False
        return self.coefficients==b.coefficients
    def __pow__(self,e:int):
        if not isinstance(e,int):raise TypeError('Integer powers only')
        if e<0:return self.inverse()**(-e)
        r=self.field.element(1);x=self
        while e:
            if e&1:r=r*x
            x=x*x;e>>=1
        return r
    def inverse(self):
        if not any(self.coefficients):raise ZeroDivisionError('Zero algebraic element')
        gcd,s,_=_qextended_gcd(list(self.coefficients),list(self.field.minimal_polynomial))
        if len(gcd)!=1 or gcd[0]==0:raise ArithmeticError('Invalid number field inverse')
        return self.field.element([x/gcd[0] for x in s])
    def __truediv__(self,other):return self*self._to(other).inverse()
    def __rtruediv__(self,other):return self._to(other)*self.inverse()

# ────────────────────── Exactly algebraic fourth order Yoshida ───────
class ExactYoshida4:
    """Fourth order symmetric splitting with coefficients in Q(2^(1/3)).

    The order conditions 2a+b=1 and 2a^3+b^3=0 are checked algebraically.
    Only separable polynomial Hamiltonians are supported; no global energy
    conservation is claimed. Coordinates live in an exact cubic number field.
    """
    def __init__(self,flow:HamiltonianFlow,h:F):
        self.field=NumberField((-2,0,0,1),7)
        self.flow=flow;self.h=Q(h)
        n=flow.phase.pairs;H=flow.energy
        if any(not H.diff(i).diff(n+j).is_zero for i in range(n) for j in range(n)):
            raise ValueError('Yoshida requires a separable Hamiltonian')
        alpha=self.field.alpha();a=(2-alpha).inverse();b=-alpha*a
        if 2*a+b!=1 or 2*a**3+b**3!=0:
            raise ArithmeticError('Fourth order composition conditions failed')
        self.coefficients=(a,b,a)
        self.grad_q=tuple(H.diff(i) for i in range(n))
        self.grad_p=tuple(H.diff(n+i) for i in range(n))

    def _eval(self,p:Polynomial,z):
        total=self.field.element(0)
        for ex,c in p.terms:
            term=self.field.element(c)
            for x,k in zip(z,ex):term=term*(x**k)
            total+=term
        return total

    def _verlet(self,z,h):
        n=self.flow.phase.pairs
        q=list(z[:n]);p=list(z[n:]);half=h/2
        gradient=self.grad_q
        for i in range(n):p[i]-=half*self._eval(gradient[i],q+p)
        for i in range(n):q[i]+=h*self._eval(self.grad_p[i],q+p)
        for i in range(n):p[i]-=half*self._eval(gradient[i],q+p)
        return q+p

    def step(self,z:Vector|Sequence[AlgebraicElement]):
        coords=([self.field.element(v) for v in z.entries] if isinstance(z,Vector)
                else [self.field.element(v) for v in z])
        if len(coords)!=2*self.flow.phase.pairs:raise ValueError('Phase dimension mismatch')
        for c in self.coefficients:coords=self._verlet(coords,c*self.h)
        return tuple(coords)

# ─────────────────────────── Certified interval analysis ──────────────
def interval_nth_root(x:F,degree:int,digits:int=18)->RationalInterval:
    """Nonnegative real root with rational bounds proved by integer powers.

    The explicit limits bound the requested scale and root degree. No log,
    float conversion, or approximate root is used in the certificate bounds.
    """
    x=Q(x)
    if (x<0 or type(degree) is not int or not 1<=degree<=1024
            or type(digits) is not int or not 1<=digits<=4096):
        raise ValueError('Require x>=0, degree in 1..1024 and digits in 1..4096')
    scale=10**digits
    scaled=x*scale**degree
    target=scaled.numerator//scaled.denominator
    lo=0;hi=1<<((target.bit_length()+degree-1)//degree)
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**degree<=target:lo=mid
        else:hi=mid
    if hi**degree<=target:lo=hi
    lower=F(lo,scale)
    upper=lower if lower**degree==x else F(lo+1,scale)
    return RationalInterval(lower,upper)


def interval_sqrt(x:F,digits:int=16)->RationalInterval:
    """sqrt(x) with exact rational outer bounds at 10^-digits resolution."""
    x=Q(x)
    if x<0 or not 1<=digits<=1000:raise ValueError('sqrt domain/precision')
    scale=10**digits
    k=math.isqrt(x.numerator*scale*scale//x.denominator)
    lo=F(k,scale)
    hi=lo if lo*lo==x else F(k+1,scale)
    return RationalInterval(lo,hi)

def _intersect(a:RationalInterval,b:RationalInterval):
    lo=max(a.lo,b.lo);hi=min(a.hi,b.hi)
    if lo>hi:raise ArithmeticError('Certified interval intersection empty')
    return RationalInterval(lo,hi)

def interval_power(a:RationalInterval,k:int):
    if k<0: return interval_power(a.reciprocal(),-k)
    if k==0:return RationalInterval(1,1)
    # Preserve the exact nonnegative range of even powers across zero.
    if k%2==0:
        extrema=[a.lo**k,a.hi**k]
        return RationalInterval(0 if a.lo<=0<=a.hi else min(extrema),max(extrema))
    return RationalInterval(a.lo**k,a.hi**k)

def interval_eval(p:Polynomial,point:Sequence[RationalInterval]):
    if len(point)!=p.dimension:raise ValueError('Point dimension mismatch')
    result=RationalInterval(0,0)
    for ex,c in p.terms:
        term=RationalInterval(c,c)
        for x,k in zip(point,ex):
            if k:term=term*interval_power(x,k)
        result+=term
    return result

def interval_exp_global(x:F,terms=20):
    x=Q(x);t=x;halvings=0
    while abs(t)>1:t/=2;halvings+=1
    z=interval_exp(t,terms)
    for _ in range(halvings):z=z*z
    return z

def interval_log_global(x:F,terms=20):
    x=Q(x)
    if x<=0:raise ValueError('log needs x>0')
    k=0;t=x
    while t>2:t/=2;k+=1
    while t<F(1,2):t*=2;k-=1
    return interval_log(t,terms)+interval_log(F(2),terms)*k

def interval_sin_cos_global(x:F,terms=20):
    x=Q(x);t=x;halvings=0
    while abs(t)>1:t/=2;halvings+=1
    s,c=interval_sin(t,terms),interval_cos(t,terms)
    unit=RationalInterval(-1,1)
    for _ in range(halvings):
        s,c=_intersect(2*s*c,unit),_intersect(interval_power(c,2)-interval_power(s,2),unit)
    return s,c

def interval_arccos_unit(x:RationalInterval,bits=20,terms=26):
    """Bounds acos(x), x subset [-1,1], via cosine monotonicity on [0,π].

    Interval uncertain comparisons are conservatively handled; no equality
    between floating-point approximations and exact transcendental values.
    """
    if x.lo<-1 or x.hi>1 or bits<1:raise ValueError('acos input domain')
    pi=interval_pi(terms)
    lo=F(0);hi=pi.hi
    for _ in range(bits):
        m=(lo+hi)/2
        c=interval_sin_cos_global(m,terms)[1]
        if c.lo>x.hi:lo=m
        elif c.hi<x.lo:hi=m
        else:
            # Cannot prove a side at this precision; preserve valid bounds.
            break
    return RationalInterval(lo,hi)

# ────────────────────────── Unique nonlinear midpoint root ───────────
@dataclass(frozen=True)
class MidpointContractionCertificate:
    """Banach-certified *local* root of implicit midpoint on a rational box.

    Φ(y) = z + h f((z+y)/2). Verified Φ(B)⊆B and max_i Σ_j
    |h/2 * ∂_j f_i((z+B)/2)| < 1 in l∞. Existence and uniqueness *in B*
    follow by Banach's theorem. Does not claim a rational closed form.
    """
    flow:HamiltonianFlow
    initial:Vector
    step_size:F
    box:tuple[RationalInterval,...]
    contraction_bound:F

    @classmethod
    def certify(cls,flow:HamiltonianFlow,z:Vector,h:F,box:Sequence[RationalInterval]):
        h=Q(h);d=flow.phase.dimension;box=tuple(box)
        if z.dim!=d or len(box)!=d:raise ValueError('Invalid phase box')
        field=flow.phase.hamiltonian_field(flow.energy)
        mid=[(RationalInterval(v,v)+i)/2 for v,i in zip(z.entries,box)]
        image=[RationalInterval(v,v)+h*interval_eval(f,mid) for v,f in zip(z.entries,field)]
        for target,b in zip(image,box):
            if not (b.lo<=target.lo<=target.hi<=b.hi):
                raise ValueError('Midpoint image is not provably contained in box')
        bounds=[]
        for f in field:
            upper=F(0)
            for j in range(d):
                J=interval_eval(f.diff(j),mid)
                upper+=max(abs(J.lo),abs(J.hi))*abs(h)/2
            bounds.append(upper)
        contraction=max(bounds)
        if contraction>=1:raise ValueError('No contraction certificate: derivative bound >= 1')
        return cls(flow,z,h,box,contraction)

    def enclose(self,iterations:int=5):
        if iterations<0:raise ValueError('Nonnegative iterations only')
        box=list(self.box)
        field=self.flow.phase.hamiltonian_field(self.flow.energy)
        for _ in range(iterations):
            mid=[(RationalInterval(v,v)+i)/2 for v,i in zip(self.initial.entries,box)]
            box=[_intersect(a,RationalInterval(v,v)+self.step_size*interval_eval(f,mid))
                 for a,v,f in zip(box,self.initial.entries,field)]
        return tuple(box)

# ──────────────────────── Tensor and differential geometry ────────────
@dataclass(frozen=True)
class MixedTensor:
    """Tensor of type (p,q) represented in one finite-dimensional basis."""
    dimension:int
    upper:int
    lower:int
    entries:tuple[tuple[tuple[int,...],F],...]

    def __post_init__(self):
        if self.dimension<1 or self.upper<0 or self.lower<0:raise ValueError('Invalid tensor type')
        values=defaultdict(F)
        for ix,c in self.entries:
            if len(ix)!=self.upper+self.lower or any(not 0<=j<self.dimension for j in ix):
                raise ValueError('Invalid tensor index')
            values[tuple(ix)]+=Q(c)
        object.__setattr__(self,'entries',tuple(sorted((k,c) for k,c in values.items() if c)))

    def tensor(self,other:'MixedTensor'):
        if self.dimension!=other.dimension:raise ValueError('Dimension mismatch')
        result=[]
        for i,a in self.entries:
            for j,b in other.entries:
                indices=i[:self.upper]+j[:other.upper]+i[self.upper:]+j[other.upper:]
                result.append((indices,a*b))
        return MixedTensor(self.dimension,self.upper+other.upper,self.lower+other.lower,tuple(result))

    def contract(self,upper_index:int,lower_index:int):
        if not 0<=upper_index<self.upper or not 0<=lower_index<self.lower:
            raise ValueError('Illegal contraction')
        result=[]
        for ix,c in self.entries:
            if ix[upper_index]==ix[self.upper+lower_index]:
                index=ix[:upper_index]+ix[upper_index+1:self.upper]+ix[self.upper:self.upper+lower_index]+ix[self.upper+lower_index+1:]
                result.append((index,c))
        return MixedTensor(self.dimension,self.upper-1,self.lower-1,tuple(result))

def _rf_zero(n):return RationalFunction.from_polynomial(Polynomial.constant(n,0))
def _rf_one(n):return RationalFunction.from_polynomial(Polynomial.constant(n,1))

def rational_matrix_inverse(a:Sequence[Sequence[RationalFunction]]):
    n=len(a)
    if n<1 or any(len(row)!=n for row in a):raise ValueError('Square matrix required')
    dim=a[0][0].numerator.dimension
    if any(x.numerator.dimension!=dim for row in a for x in row):raise ValueError('Mismatched rings')
    zero,one=_rf_zero(dim),_rf_one(dim)
    b=[list(row)+[one if i==j else zero for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        k=next((i for i in range(j,n) if not b[i][j].numerator.is_zero),None)
        if k is None:raise ValueError('Degenerate rational metric')
        b[j],b[k]=b[k],b[j];c=b[j][j];b[j]=[v/c for v in b[j]]
        for i in range(n):
            if i==j:continue
            c=b[i][j]
            if not c.numerator.is_zero:
                b[i]=[x-c*y for x,y in zip(b[i],b[j])]
    return tuple(tuple(row[n:]) for row in b)

class RationalRiemannianMetric:
    """Local metric on rational coordinate chart, exact rational Christoffels.

    Curvature is computed without assuming flatness; global topology and metric
    positive definiteness on the entire real domain require separate proofs.
    """
    def __init__(self,g:Sequence[Sequence[RationalFunction]]):
        self.n=len(g)
        if self.n<1 or any(len(row)!=self.n for row in g):raise ValueError('Square metric')
        self.g=tuple(tuple(row) for row in g)
        if any(self.g[i][j]!=self.g[j][i] for i in range(self.n) for j in range(self.n)):
            raise ValueError('Symmetric metric needed')
        self.inv=rational_matrix_inverse(self.g)
        self._gamma={}

    def christoffel(self,i,j,k):
        """Γ^i_{jk}."""
        if not all(0<=x<self.n for x in (i,j,k)):raise ValueError('Invalid index')
        key=i,j,k
        if key not in self._gamma:
            ans=_rf_zero(self.n)
            for l in range(self.n):
                ans+=self.inv[i][l]*(self.g[l][k].diff(j)+self.g[l][j].diff(k)-self.g[j][k].diff(l))
            self._gamma[key]=ans/2
        return self._gamma[key]

    def riemann(self,i,j,k,l):
        """R^i_{jkl}= ∂_k Γ^i_{lj}-∂_l Γ^i_{kj}+Γ^i_{km}Γ^m_{lj}-Γ^i_{lm}Γ^m_{kj}."""
        out=self.christoffel(i,l,j).diff(k)-self.christoffel(i,k,j).diff(l)
        for m in range(self.n):
            out+=self.christoffel(i,k,m)*self.christoffel(m,l,j)
            out-=self.christoffel(i,l,m)*self.christoffel(m,k,j)
        return out

# ────────────────────── Exact SU(2) and Lie algebra ───────────────────
@dataclass(frozen=True)
class SU2:
    """Unit rational Hamilton quaternion, representing SU(2)."""
    w:F;x:F;y:F;z:F

    def __post_init__(self):
        for k in ('w','x','y','z'):object.__setattr__(self,k,Q(getattr(self,k)))
        if self.w*self.w+self.x*self.x+self.y*self.y+self.z*self.z!=1:
            raise ValueError('SU(2) requires unit quaternion')

    @classmethod
    def stereographic(cls,a:F,b:F,c:F):
        a,b,c=Q(a),Q(b),Q(c);r=a*a+b*b+c*c;d=1+r
        return cls((1-r)/d,2*a/d,2*b/d,2*c/d)

    def __matmul__(self,other:'SU2'):
        if not isinstance(other,SU2):return NotImplemented
        a,b,c,d=self.w,self.x,self.y,self.z
        e,f,g,h=other.w,other.x,other.y,other.z
        return SU2(a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
                   a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)

    def inverse(self):return SU2(self.w,-self.x,-self.y,-self.z)

    def to_so3(self):
        a,b,c,d=self.w,self.x,self.y,self.z
        return SO3(Matrix(((1-2*(c*c+d*d),2*(b*c-a*d),2*(b*d+a*c)),
                           (2*(b*c+a*d),1-2*(b*b+d*d),2*(c*d-a*b)),
                           (2*(b*d-a*c),2*(c*d+a*b),1-2*(b*b+c*c)))))

@dataclass(frozen=True)
class RationalLieAlgebra:
    """Finite-dimensional Lie algebra over Q, structure constants C^k_ij.

    Antisymmetry and Jacobi validated identically over Q on basis elements.
    """
    structure:tuple[tuple[tuple[F,...],...],...]

    def __post_init__(self):
        n=len(self.structure)
        if not n or any(len(row)!=n or any(len(t)!=n for t in row) for row in self.structure):
            raise ValueError('C[i][j][k] must be n×n×n')
        c=tuple(tuple(tuple(Q(t) for t in row) for row in block) for block in self.structure)
        object.__setattr__(self,'structure',c)
        for i in range(n):
            for j in range(n):
                for k in range(n):
                    if c[i][j][k]!=-c[j][i][k]:raise ValueError('Not antisymmetric')
                for k in range(n):
                    for t in range(n):
                        jac=sum((c[i][j][l]*c[l][k][t]+c[j][k][l]*c[l][i][t]+c[k][i][l]*c[l][j][t]
                                 for l in range(n)),F(0))
                        if jac:raise ValueError('Jacobi identity fails')

    @property
    def dimension(self):return len(self.structure)

    def bracket(self,u:Vector,v:Vector):
        if u.dim!=self.dimension or v.dim!=self.dimension:raise ValueError('Wrong Lie dimension')
        n=self.dimension
        return Vector(tuple(sum((u.entries[i]*v.entries[j]*self.structure[i][j][k]
                    for i in range(n) for j in range(n)),F(0)) for k in range(n)))

# ──────────────────────── Sphere charts and topology scope ────────────
class StereographicSphere2:
    """Two explicit rational charts of S² minus opposite poles.

    Does NOT implement all topological axioms globally. The two images cover
    the entire sphere: each misses only its own projection pole; overlap is
    R²\\{(0,0)} where transition u→u/(u²+v²) is an involution.
    """
    @staticmethod
    def embed(u:RationalFunction,v:RationalFunction,north=True):
        t=1+u*u+v*v
        return (2*u/t,2*v/t,(u*u+v*v-1)/t if north else (1-u*u-v*v)/t)

    @staticmethod
    def transition(u:RationalFunction,v:RationalFunction):
        t=u*u+v*v
        return u/t,v/t

    @staticmethod
    def verify():
        n=2;u=RationalFunction.from_polynomial(Polynomial.variable(n,0))
        v=RationalFunction.from_polynomial(Polynomial.variable(n,1))
        xyz=StereographicSphere2.embed(u,v)
        if sum((t*t for t in xyz),_rf_zero(n))!=1:return False
        a,b=StereographicSphere2.transition(u,v)
        c,d=StereographicSphere2.transition(a,b)
        return c==u and d==v and all(k==l for k,l in
                 zip(StereographicSphere2.embed(u,v,True),StereographicSphere2.embed(a,b,False)))

# ─────────────────── Symbolic attention with trainable parameters ─────
class SymbolicAttention:
    """Single-head differentiable causal attention, exact expression graph.

    Each weight WQ/WK/WV is a SymbolicExpr variable. Its gradients follow the
    chain rule through softmax (exp is formal, not a rational function).
    Numerical evaluation of expressions uses floats and is not a proof.
    """
    def __init__(self,dimension:int,temperature:F=1):
        if dimension<1 or Q(temperature)<=0:raise ValueError('Invalid attention specification')
        self.d=dimension;self.tau=Q(temperature)
        self.nparams=3*dimension*dimension

    def parameters(self,offset:int=0):return tuple(SymbolicExpr.var(offset+i) for i in range(self.nparams))

    def forward(self,tokens:Sequence[Sequence[int|F]],offset:int=0):
        d=self.d
        if not tokens or any(len(t)!=d for t in tokens):raise ValueError('Wrong token shapes')
        w=self.parameters(offset)
        def linear(offset,token):
            return tuple(sum((w[offset+i*d+j]*Q(token[j]) for j in range(d)),SymbolicExpr.const(0))
                         for i in range(d))
        q=[linear(0,t) for t in tokens]
        k=[linear(d*d,t) for t in tokens]
        v=[linear(2*d*d,t) for t in tokens]
        output=[]
        for i in range(len(tokens)):
            scores=[sum((q[i][c]*k[j][c] for c in range(d)),SymbolicExpr.const(0))/self.tau
                    for j in range(i+1)]
            exps=[s.exp() for s in scores]
            denom=sum(exps,SymbolicExpr.const(0))
            weights=[e/denom for e in exps]
            output.append(tuple(sum((weights[j]*v[j][c] for j in range(i+1)),SymbolicExpr.const(0))
                                for c in range(d)))
        return tuple(output)

    def value_and_gradient(self,loss:SymbolicExpr,parameters:Sequence[F|float]):
        if len(parameters)!=self.nparams:raise ValueError('Parameter length mismatch')
        return loss.eval(parameters),tuple(loss.diff(i).eval(parameters) for i in range(self.nparams))

# ─────────────────── Generators of continuous stochastic dynamics ────
@dataclass(frozen=True)
class PolynomialItoDiffusion:
    """Exact Itô infinitesimal generator for polynomial coefficients.

    L f = b·∇f + 1/2 ∑_ij (ΣΣᵀ)_ij ∂_ij f.
    Does not provide a pathwise SDE solver or a stochastic measure space.
    """
    drift:tuple[Polynomial,...]
    diffusion:tuple[tuple[Polynomial,...],...]

    def __post_init__(self):
        d=len(self.drift)
        if d<1 or len(self.diffusion)!=d or not self.diffusion[0]:raise ValueError('Dimensions')
        m=len(self.diffusion[0]);
        if any(f.dimension!=d for f in self.drift):raise ValueError('Drift ring')
        if any(len(row)!=m or any(f.dimension!=d for f in row) for row in self.diffusion):
            raise ValueError('Diffusion ring')

    def generator(self,f:Polynomial):
        d=len(self.drift)
        if f.dimension!=d:raise ValueError('Test function ring')
        result=Polynomial.constant(d,0)
        for i in range(d):result+=self.drift[i]*f.diff(i)
        for i in range(d):
            for j in range(d):
                covariance=sum((x*y for x,y in zip(self.diffusion[i],self.diffusion[j])),Polynomial.constant(d,0))
                result+=covariance*f.diff(i).diff(j)/2
        return result

# ──────────────────── Sparse invariant discovery, including Casimirs ─
def polynomial_kernel(columns:Sequence[Polynomial]):
    if not columns:return ()
    monos=sorted({exp for f in columns for exp,_ in f.terms})
    if not monos:return tuple(tuple(F(int(i==j)) for i in range(len(columns))) for j in range(len(columns)))
    columns=[dict(p.terms) for p in columns]
    return primitive_integer_kernel([[c.get(m,F(0)) for c in columns] for m in monos])

def discover_casimirs(poisson_tensor,degree:int=2,max_terms:int=2000):
    """Find polynomial Casimirs within a bounded total-degree ansatz.

    No completeness claim beyond this finite-dimensional ansatz. A candidate
    satisfies {C,x_i}=0 for each coordinate, hence {C,F}=0 for all polynomials F.
    """
    n=len(poisson_tensor.pi)
    xs=tuple(Polynomial.variable(n,j) for j in range(n))
    monos=tuple(pruned_monomials(n,degree,max_terms=max_terms))
    basis=[Polynomial(n,((ex,F(1)),)) for ex in monos if any(ex)]
    cols=[]
    for p in basis:
        brackets=[poisson_tensor.bracket(p,x) for x in xs]
        entries=tuple(((j,)+ex,c) for j,b in enumerate(brackets) for ex,c in b.terms)
        cols.append(entries)
    labels=sorted({name for col in cols for name,_ in col})
    dicts=[dict(c) for c in cols]
    kernel=primitive_integer_kernel([[d.get(label,F(0)) for d in dicts] for label in labels]) if labels else tuple(tuple(F(int(i==j)) for i in range(len(cols))) for j in range(len(cols)))
    candidates=[]
    for vec in kernel:
        c=sum((w*p for w,p in zip(vec,basis)),Polynomial.constant(n,0))
        if not c.is_zero and poisson_tensor.casimir_certificate(c):candidates.append(c)
    return independent_invariants(candidates)

# ─────────────────────── Reduced canonical Gröbner bases ──────────────
def reduced_groebner_basis(generators:Sequence[Polynomial],max_pairs:int=2000):
    """Reduced monic Gröbner basis of ideal on graded-lex order (small systems).

    This is an exact Buchberger completion followed by interreduction; memory
    and runtime remain exponential in worst case. No F4/F5 efficiency claim.
    """
    G=list(groebner_basis(generators,max_pairs=max_pairs))
    if not G:return ()
    def divides(a,b):return all(i<=j for i,j in zip(a,b))
    # One leading monomial cannot be a multiple of another minimal generator.
    minimal=[]
    for i,f in enumerate(G):
        lt=leading_term(f)[0]
        if any((j!=i and divides(leading_term(g)[0],lt) and
                (leading_term(g)[0]!=lt or j<i)) for j,g in enumerate(G)):
            continue
        minimal.append(f)
    result=[]
    for i,g in enumerate(minimal):
        _,rem=polynomial_division(g,[h for j,h in enumerate(minimal) if j!=i])
        if not rem.is_zero:result.append(rem/leading_term(rem)[1])
    result=tuple(sorted(set(result),key=lambda f:leading_term(f)[0]))
    for f in result:
        for g in result:
            if f is g:continue
            if f==g:continue
            # A reduced basis contains no monomial divisible by other's LM.
            if any(divides(leading_term(g)[0],ex) for ex,_ in f.terms):
                raise ArithmeticError('Interreduction is not complete')
    return result

# ─────────── Algebraic functions: fractional exponents without float ───
@dataclass(frozen=True)
class QuadraticAlgebraicFunction:
    """Formal a(x)+b(x) sqrt(r(x)), with a,b,r in Q(x).

    Arithmetic holds in Q(x)[T]/(T²-r). If r is not a square in Q(x) this
    quotient is a field; irreducibility is NOT established automatically.
    For evaluation, require r(point) >= 0 and the denominator restrictions.
    """
    a:RationalFunction
    b:RationalFunction
    r:RationalFunction

    @classmethod
    def sqrt(cls,r:RationalFunction):
        zero=_rf_zero(r.numerator.dimension);one=_rf_one(r.numerator.dimension)
        return cls(zero,one,r)

    def _to(self,x):
        if isinstance(x,QuadraticAlgebraicFunction):
            if x.r!=self.r:raise ValueError('Different algebraic radicals')
            return x
        return QuadraticAlgebraicFunction(self.a._to(x),_rf_zero(self.a.numerator.dimension),self.r)

    def __add__(self,x):
        y=self._to(x)
        return QuadraticAlgebraicFunction(self.a+y.a,self.b+y.b,self.r)
    __radd__=__add__
    def __neg__(self):return QuadraticAlgebraicFunction(-self.a,-self.b,self.r)
    def __sub__(self,x):return self+(-self._to(x))
    def __rsub__(self,x):return self._to(x)+(-self)
    def __mul__(self,x):
        y=self._to(x)
        return QuadraticAlgebraicFunction(self.a*y.a+self.b*y.b*self.r,
                                          self.a*y.b+self.b*y.a,self.r)
    __rmul__=__mul__
    def inverse(self):
        norm=self.a*self.a-self.b*self.b*self.r
        if norm.numerator.is_zero:raise ZeroDivisionError('Zero algebraic norm')
        return QuadraticAlgebraicFunction(self.a/norm,-self.b/norm,self.r)
    def __truediv__(self,x):return self*self._to(x).inverse()
    def __rtruediv__(self,x):return self._to(x)*self.inverse()
    def __pow__(self,k:int):
        if not isinstance(k,int):raise TypeError('Integer power required')
        if k<0:return self.inverse()**(-k)
        out=self._to(1)
        while k:
            if k&1:out=out*self
            k>>=1
            if k:self=self*self
        return out
    def diff(self,i):
        if self.r.numerator.is_zero:raise ZeroDivisionError('Radicand identically zero')
        # d sqrt(r) = (r' / (2r)) sqrt(r), valid wherever r>0.
        return QuadraticAlgebraicFunction(self.a.diff(i),
                self.b.diff(i)+self.b*self.r.diff(i)/(2*self.r),self.r)
    def evaluate_interval(self,point:Sequence[F],digits=24):
        rad=self.r.evaluate(point)
        if rad<0:raise ValueError('Radicand negative')
        return RationalInterval(self.a.evaluate(point),self.a.evaluate(point))+\
               RationalInterval(self.b.evaluate(point),self.b.evaluate(point))*interval_sqrt(rad,digits)

@dataclass(frozen=True)
class AnalyticExpression:
    """Formal real-analytic expression with exact symbolic differentiation.

    Syntax is a typed operation DAG. Equality of arbitrary transcendental
    expressions is intentionally NOT asserted decidable. Interval evaluation
    uses explicit conservative rational bounds for all primitives.
    """
    operation:str
    args:tuple=()

    @staticmethod
    def constant(x):return AnalyticExpression('const',(Q(x),))
    @staticmethod
    def variable(i:int):
        if i<0:raise ValueError('Variable index must be nonnegative')
        return AnalyticExpression('var',(i,))
    @staticmethod
    def cast(x):
        if isinstance(x,AnalyticExpression):return x
        if isinstance(x,Polynomial):
            result=AnalyticExpression.constant(0)
            for powers,coefficient in x.terms:
                term=AnalyticExpression.constant(coefficient)
                for i,power in enumerate(powers):
                    if power:term=term*AnalyticExpression.variable(i)**power
                result=result+term
            return result
        if isinstance(x,RationalFunction):
            # Restrictions already removed by RationalFunction normalization
            # cannot be recovered; the current denominator is preserved.
            return AnalyticExpression.cast(x.numerator)/AnalyticExpression.cast(x.denominator)
        if isinstance(x,QuadraticAlgebraicFunction):
            return (AnalyticExpression.cast(x.a)+AnalyticExpression.cast(x.b)
                    *AnalyticExpression.cast(x.r).sqrt())
        return AnalyticExpression.constant(x)
    def __add__(self,x):return AnalyticExpression('add',(self,self.cast(x)))
    __radd__=__add__
    def __neg__(self):return AnalyticExpression('neg',(self,))
    def __sub__(self,x):return self+(-self.cast(x))
    def __rsub__(self,x):return self.cast(x)+(-self)
    def __mul__(self,x):return AnalyticExpression('mul',(self,self.cast(x)))
    __rmul__=__mul__
    def __truediv__(self,x):return self*self.cast(x)**-1
    def __rtruediv__(self,x):return self.cast(x)*self**-1
    def __pow__(self,k):
        if isinstance(k,F) and k.denominator!=1:
            return AnalyticExpression('rpow',(self,k))
        if isinstance(k,F):k=k.numerator
        if not isinstance(k,int):raise TypeError('Integer power only; use sqrt for half powers')
        return AnalyticExpression('pow',(self,k))
    def exp(self):return AnalyticExpression('exp',(self,))
    def log(self):return AnalyticExpression('log',(self,))
    def sin(self):return AnalyticExpression('sin',(self,))
    def cos(self):return AnalyticExpression('cos',(self,))
    def sqrt(self):return AnalyticExpression('sqrt',(self,))

    def compose(self,components):
        """Simultaneous substitution; does not substitute inside replacements."""
        op=self.operation;a=self.args
        if op=='const':return self
        if op=='var':return self.cast(components[a[0]])
        if op in ('pow','rpow'):
            return AnalyticExpression(op,(a[0].compose(components),a[1]))
        if op in ('add','mul','neg','exp','log','sin','cos','sqrt'):
            return AnalyticExpression(op,tuple(x.compose(components) for x in a))
        raise ValueError('Unknown formal primitive')

    def gradient(self,dimension):
        if type(dimension) is not int or dimension<1:raise ValueError('Positive dimension required')
        return tuple(self.diff(i) for i in range(dimension))

    def hessian(self,dimension):
        return tuple(tuple(d.diff(j) for j in range(dimension)) for d in self.gradient(dimension))

    def enclose_adaptive(self,point,tolerance=F(1,10**12),*,initial_digits=8,max_digits=128):
        """Refine until a guaranteed width is met, or fail explicitly.

        A box's intrinsic range or dependency overestimation may prevent
        convergence. Precision is a work parameter, not a decimal guarantee.
        """
        tolerance=Q(tolerance)
        if (tolerance<=0 or type(initial_digits) is not int or type(max_digits) is not int
                or initial_digits<1 or max_digits<initial_digits):
            raise ValueError('Positive tolerance and valid precision budget required')
        digits=initial_digits
        while True:
            try:
                box=self.enclose(point,digits)
            except ZeroDivisionError:
                # A rounded positive root can still have lower bound zero.
                # Retrying is safe; an actual pole still fails at the budget.
                if digits==max_digits:raise
                digits=min(2*digits,max_digits)
                continue
            if box.hi-box.lo<=tolerance:return box
            if digits==max_digits:raise RuntimeError('Enclosure width exceeds tolerance at precision budget')
            digits=min(2*digits,max_digits)

    def diff(self,i):
        op=self.operation;a=self.args
        if op=='const':return self.constant(0)
        if op=='var':return self.constant(int(i==a[0]))
        if op=='add':return a[0].diff(i)+a[1].diff(i)
        if op=='neg':return -a[0].diff(i)
        if op=='mul':return a[0].diff(i)*a[1]+a[0]*a[1].diff(i)
        if op=='pow':return self.constant(a[1])*a[0]**(a[1]-1)*a[0].diff(i) if a[1] else self.constant(0)
        if op=='rpow':return a[1]*a[0]**(a[1]-1)*a[0].diff(i)
        if op=='exp':return self*a[0].diff(i)
        if op=='log':return a[0].diff(i)/a[0]
        if op=='sin':return a[0].cos()*a[0].diff(i)
        if op=='cos':return -a[0].sin()*a[0].diff(i)
        if op=='sqrt':return a[0].diff(i)/(2*self)
        raise ValueError('Unknown formal primitive')

    def enclose(self,point:Sequence[RationalInterval],digits=18):
        op=self.operation;a=self.args
        if op=='const':return RationalInterval(a[0],a[0])
        if op=='var':return point[a[0]]
        if op=='add':return a[0].enclose(point,digits)+a[1].enclose(point,digits)
        if op=='neg':return -a[0].enclose(point,digits)
        if op=='mul':return a[0].enclose(point,digits)*a[1].enclose(point,digits)
        if op=='pow':return interval_power(a[0].enclose(point,digits),a[1])
        if op=='rpow':
            box=a[0].enclose(point,digits)
            if box.lo<=0:raise ValueError('Rational power requires the strictly positive real branch')
            lower=interval_nth_root(box.lo,a[1].denominator,digits).lo
            upper=interval_nth_root(box.hi,a[1].denominator,digits).hi
            return interval_power(RationalInterval(lower,upper),a[1].numerator)
        if op=='sqrt':
            box=a[0].enclose(point,digits)
            if box.lo<0:raise ValueError('sqrt input interval not proven nonnegative')
            return RationalInterval(interval_sqrt(box.lo,digits).lo,interval_sqrt(box.hi,digits).hi)
        if op=='log':
            box=a[0].enclose(point,digits)
            if box.lo<=0:raise ValueError('log input interval not proven positive')
            return RationalInterval(interval_log_global(box.lo,digits).lo,interval_log_global(box.hi,digits).hi)
        if op=='exp':
            box=a[0].enclose(point,digits)
            return RationalInterval(interval_exp_global(box.lo,digits).lo,interval_exp_global(box.hi,digits).hi)
        if op in ('sin','cos'):
            box=a[0].enclose(point,digits)
            m=(box.lo+box.hi)/2;radius=(box.hi-box.lo)/2
            approxim=interval_sin_cos_global(m,digits)[0 if op=='sin' else 1]
            return _intersect(RationalInterval(approxim.lo-radius,approxim.hi+radius),RationalInterval(-1,1))
        raise ValueError('Unknown formal primitive')

# ────────────── Streaming sparse exact linear constraints ──────────────
class SparseExactKernel:
    """Incremental exact sparse homogeneous elimination, fraction-free rows.

    Sparse elimination minimizes storage for sparse constraints. Worst-case
    fill-in and output kernel size may still be exponential; explicit caps
    prevent uncontrolled memory growth.
    """
    def __init__(self,ncols:int,max_nonzeros:int=200_000):
        if ncols<1 or max_nonzeros<1:raise ValueError('Positive dimensions and cap')
        self.n=ncols;self.max_nonzeros=max_nonzeros;self.pivots={};self._nonzeros=0

    @staticmethod
    def _primitive(row:dict[int,int]):
        row={i:v for i,v in row.items() if v}
        if not row:return {}
        g=math.gcd(*row.values());return {i:v//g for i,v in row.items()}

    def add_equation(self,values:dict[int,F|int]):
        if any(not isinstance(k,int) or not 0<=k<self.n for k in values):
            raise ValueError('Sparse row index invalid')
        den=math.lcm(*(Q(x).denominator for x in values.values())) if values else 1
        row=self._primitive({i:int(Q(v)*den) for i,v in values.items()})
        # Follow only encountered leading pivots. Scanning every stored pivot
        # makes even diagonal input quadratic in the number of equations.
        while row:
            j=min(row)
            if j not in self.pivots:break
            p=self.pivots[j];a=row[j];b=p[j];g=math.gcd(a,b)
            keys=row.keys()|p.keys()
            row=self._primitive({k:(b//g)*row.get(k,0)-(a//g)*p.get(k,0) for k in keys})
        if not row:return False
        pivot=min(row)
        if row[pivot]<0:row={i:-v for i,v in row.items()}
        if self._nonzeros+len(row)>self.max_nonzeros:
            raise MemoryError('Sparse elimination nonzero cap exceeded')
        self.pivots[pivot]=row
        self._nonzeros+=len(row)
        return True

    @property
    def rank(self):return len(self.pivots)

    def basis(self,max_basis:int=100):
        free=[j for j in range(self.n) if j not in self.pivots]
        if len(free)>max_basis:raise RuntimeError('Kernel basis size exceeds explicit cap')
        result=[]
        for j in free:
            v=[F(0)]*self.n;v[j]=F(1)
            for k in sorted(self.pivots,reverse=True):
                row=self.pivots[k]
                v[k]=-sum((a*v[i] for i,a in row.items() if i>k),F(0))/row[k]
            result.append(tuple(v))
        return tuple(result)

# ───────────── Exact integration on a continuous probability space ─────
@dataclass(frozen=True)
class UniformIntervalMeasure:
    """Lebesgue-absolutely-continuous uniform law on [a,b].

    Normalization and all polynomial moments are computed exactly in Q.
    This is one parametric distribution, not a construction of Lebesgue measure.
    """
    a:F
    b:F
    def __post_init__(self):
        object.__setattr__(self,'a',Q(self.a));object.__setattr__(self,'b',Q(self.b))
        if self.a>=self.b:raise ValueError('Nondegenerate bounded interval required')
    def moment(self,k:int):
        if not isinstance(k,int) or k<0:raise ValueError('Nonnegative moment order')
        return (self.b**(k+1)-self.a**(k+1))/((k+1)*(self.b-self.a))
    def expectation(self,f:Polynomial):
        if f.dimension!=1:raise ValueError('Univariate polynomial only')
        return sum((c*self.moment(ex[0]) for ex,c in f.terms),F(0))
    def cdf(self,x:F):
        x=Q(x)
        return F(0) if x<=self.a else F(1) if x>=self.b else (x-self.a)/(self.b-self.a)

# ─────────────── Certified information geometry of finite/normal laws ──
class CertifiedFisherSphere:
    """Rational interval enclosure of the Fisher–Rao geodesic distance.

    2 acos(Σ sqrt(p_i q_i)), including boundary probability vectors.
    The result is a certified real interval, not a float approximation.
    """
    @staticmethod
    def distance_interval(p:Sequence[F],q:Sequence[F],digits=24,bits=32):
        if not p or len(p)!=len(q):raise ValueError('Incompatible simplexes')
        p=tuple(Q(x) for x in p);q=tuple(Q(x) for x in q)
        if any(x<0 for x in p+q) or sum(p)!=1 or sum(q)!=1:
            raise ValueError('Inputs must be normalized probabilities')
        similarity=sum((interval_sqrt(a*b,digits) for a,b in zip(p,q)),RationalInterval(0,0))
        similarity=_intersect(similarity,RationalInterval(0,1))
        return interval_arccos_unit(similarity,bits=bits,terms=max(24,digits))*2

class GaussianNaturalExponentialFamily:
    """Normal exponential family in natural (η₁, η₂), η₂<0.

    Log-partition ψ(η) = -η₁²/(4η₂) + (1/2) log(-π/η₂).
    The symbolic ψ_0 omits only constant (log π)/2; derivatives and
    Bregman/KL differences are therefore unaffected.
    """
    @staticmethod
    def log_partition_up_to_constant():
        a=AnalyticExpression.variable(0);b=AnalyticExpression.variable(1)
        return -(a*a)/(4*b) - ((-b).log()/2)

    @staticmethod
    def fisher_at(eta1:F,eta2:F,precision=24):
        eta1,eta2=Q(eta1),Q(eta2)
        if eta2>=0:raise ValueError('Gaussian natural variance parameter must be negative')
        psi=GaussianNaturalExponentialFamily.log_partition_up_to_constant()
        x=(RationalInterval(eta1,eta1),RationalInterval(eta2,eta2))
        return tuple(tuple(psi.diff(i).diff(j).enclose(x,precision) for j in range(2)) for i in range(2))

    @staticmethod
    def euclidean_parameters(eta1:F,eta2:F):
        eta1,eta2=Q(eta1),Q(eta2)
        if eta2>=0:raise ValueError('eta2 must be negative')
        return -eta1/(2*eta2),-F(1)/(2*eta2)

class CertifiedGaussianFisher:
    """Fisher distance between univariate normals with rational μ, variance.

    The Riemannian metric is hyperbolic of constant sectional curvature -1/2.
    d = sqrt(2) acosh(1+((μ1-μ2)²+2(σ1-σ2)²)/(4σ1σ2)).
    """
    @staticmethod
    def distance_interval(mu1:F,v1:F,mu2:F,v2:F,digits=25):
        mu1,v1,mu2,v2=Q(mu1),Q(v1),Q(mu2),Q(v2)
        if v1<=0 or v2<=0:raise ValueError('Variances must be positive')
        s1=interval_sqrt(v1,digits);s2=interval_sqrt(v2,digits)
        a=RationalInterval((mu1-mu2)**2,(mu1-mu2)**2)
        delta=s1-s2
        numerator=a+2*interval_power(delta,2)
        cosh=RationalInterval(1,1)+numerator/(4*s1*s2)
        # acosh is monotone for t>=1.
        cosh=_intersect(cosh,RationalInterval(1,max(1,cosh.hi)))
        def acosh_interval(t:F):
            sq=interval_sqrt(t*t-1,digits)
            return RationalInterval(interval_log_global(t+sq.lo,digits).lo,
                                    interval_log_global(t+sq.hi,digits).hi)
        angle=RationalInterval(acosh_interval(cosh.lo).lo,acosh_interval(cosh.hi).hi)
        return angle*interval_sqrt(F(2),digits)

# ────────────── Reproducible exact conservation proof certificates ─────
def serialize_conservation_certificate(phase:SymplecticSpace,
                                       h:Polynomial,observable:Polynomial)->str:
    """Portable deterministic JSON proof witness, replayable without pickle/eval.

    A digest detects accidental corruption. Verification is an exact Python
    recomputation, **not** formal verification by Lean's trusted kernel.
    """
    import json,hashlib
    if h.dimension!=phase.dimension or observable.dimension!=phase.dimension:
        raise ValueError('Phase dimension mismatch')
    if not phase.poisson(observable,h).is_zero:
        raise ValueError('Observable does not commute with Hamiltonian')
    def encode(p):return [[list(ex),str(c)] for ex,c in p.terms]
    payload={'schema':'ml-mathlib.conservation.v1','pairs':phase.pairs,
             'hamiltonian':encode(h),'observable':encode(observable)}
    canonical=json.dumps(payload,sort_keys=True,separators=(',',':'),ensure_ascii=True)
    payload['sha256']=hashlib.sha256(canonical.encode()).hexdigest()
    return json.dumps(payload,sort_keys=True,indent=2)

def verify_conservation_certificate(source:str)->bool:
    """Fail closed on invalid JSON, altered digest, or incorrect Poisson bracket."""
    import json,hashlib
    try:
        obj=json.loads(source)
        if not isinstance(obj,dict) or set(obj)!={'schema','pairs','hamiltonian','observable','sha256'}:
            return False
        checksum=obj.pop('sha256')
        if obj['schema']!='ml-mathlib.conservation.v1':return False
        canonical=json.dumps(obj,sort_keys=True,separators=(',',':'),ensure_ascii=True)
        if hashlib.sha256(canonical.encode()).hexdigest()!=checksum:return False
        pairs=obj['pairs']
        if type(pairs) is not int or not 1<=pairs<=64:return False
        d=2*pairs
        def decode(data):
            if not isinstance(data,list) or len(data)>100_000:raise ValueError
            items=[]
            for ex,c in data:
                if len(ex)!=d or any(type(e) is not int or e<0 or e>10_000 for e in ex):
                    raise ValueError
                items.append((tuple(ex),Q(c)))
            return Polynomial(d,tuple(items))
        h,obs=decode(obj['hamiltonian']),decode(obj['observable'])
        return SymplecticSpace(pairs).poisson(obs,h).is_zero
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OverflowError):
        return False

class SymbolicMultiHeadAttention:
    """End-to-end symbolically differentiable causal multihead reference model.

    Each head has separate WQ/WK/WV matrices of size d×d, followed by an
    output projection Wo of size (heads*d)²; all weights are formal variables.
    Data are exact rational constants; exp and its derivatives remain symbolic.
    This reference is intentionally exponential in graph size and is NOT a
    scalable substitute for a GPU Transformer.
    """
    def __init__(self,heads:int,head_dimension:int,temperature:F=1):
        if heads<1 or head_dimension<1:raise ValueError('Heads and sizes must be positive')
        self.heads=heads;self.d=head_dimension;self.tau=Q(temperature)
        self.head=SymbolicAttention(head_dimension,temperature)
        self.output_dimension=heads*head_dimension
        self.head_parameters=heads*self.head.nparams
        self.nparams=self.head_parameters+self.output_dimension**2

    def forward(self,tokens:Sequence[Sequence[int|F]]):
        if not tokens or any(len(t)!=self.d for t in tokens):raise ValueError('Token dimensions')
        streams=[self.head.forward(tokens,h*self.head.nparams) for h in range(self.heads)]
        o=self.output_dimension
        W=tuple(SymbolicExpr.var(self.head_parameters+i) for i in range(o*o))
        out=[]
        for t in range(len(tokens)):
            concat=tuple(x for head in streams for x in head[t])
            out.append(tuple(sum((W[i*o+j]*concat[j] for j in range(o)),SymbolicExpr.const(0))
                             for i in range(o)))
        return tuple(out)

    def value_and_gradient(self,loss:SymbolicExpr,parameters:Sequence[F|float]):
        if len(parameters)!=self.nparams:raise ValueError('Parameter mismatch')
        return loss.eval(parameters),tuple(loss.diff(i).eval(parameters) for i in range(self.nparams))
