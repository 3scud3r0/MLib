#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ML-MATHLIB 0.2 — extensões matemáticas verificáveis da biblioteca base.

Somente biblioteca padrão. Identidades algébricas são exatas sobre Q; funções
transcendentais têm certificados de intervalo apenas no domínio documentado.
Algoritmos iterativos em float NÃO produzem provas de existência/erro global.
Este módulo depende de ml_mathlib.py, mas não de PyTorch/NumPy/SymPy.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
import math
from typing import Sequence

from ml_mathlib import (Q, Vector, Matrix, Polynomial, SymplecticSpace,
                        HamiltonianFlow, FiniteProbabilitySpace, EntropicRouter)


def bareiss_determinant(a: Matrix) -> Fraction:
    """Determinante fraction-free: escala cada linha racional para inteiros.

    A eliminação de Bareiss é exata e tem O(n³) operações aritméticas; não
    estabelece limite polinomial sobre a complexidade em bits.
    """
    n, m = a.shape
    if n != m:
        raise ValueError('Determinante exige matriz quadrada')
    factors = [math.lcm(*(v.denominator for v in row)) for row in a.rows]
    b = [[int(v * factor) for v in row] for row, factor in zip(a.rows, factors)]
    denominator, sign = 1, 1
    for k in range(n - 1):
        pivot = next((i for i in range(k, n) if b[i][k]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != k:
            b[k], b[pivot] = b[pivot], b[k]
            sign = -sign
        p = b[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = p * b[i][j] - b[i][k] * b[k][j]
                if num % denominator:
                    raise ArithmeticError('Violação da divisão exata de Bareiss')
                b[i][j] = num // denominator
            b[i][k] = 0
        denominator = p
    return Fraction(sign * b[-1][-1], math.prod(factors))


def rational_ldlt(a: Matrix) -> tuple[Matrix, tuple[Fraction, ...]]:
    """Fatora matriz simétrica G = L D Lᵀ, sem raízes quadradas nem pivoteamento.

    L unitriangular. Uma matriz simétrica é positiva definida sse D_i > 0.
    Para matrizes indefinidas, pivôs nulos podem exigir pivoteamento 2×2.
    """
    n, m = a.shape
    if n != m or a != a.transpose():
        raise ValueError('LDLᵀ exige matriz simétrica quadrada')
    L = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    D = [Fraction(0)] * n
    for j in range(n):
        D[j] = a.rows[j][j] - sum(L[j][k] ** 2 * D[k] for k in range(j))
        if D[j] == 0:
            raise ValueError('Pivô nulo; LDLᵀ sem pivoteamento não aplicável')
        for i in range(j + 1, n):
            L[i][j] = (a.rows[i][j] - sum(L[i][k] * L[j][k] * D[k]
                                                 for k in range(j))) / D[j]
    return Matrix(tuple(tuple(row) for row in L)), tuple(D)


@dataclass(frozen=True)
class QuadraticNumber:
    """Representa a+b√d em Q(√d), com d racional não quadrado positivo."""
    a: Fraction
    b: Fraction
    d: Fraction

    def __post_init__(self):
        for name in ('a', 'b', 'd'):
            object.__setattr__(self, name, Q(getattr(self, name)))
        if self.d <= 0 or (math.isqrt(self.d.numerator) ** 2 == self.d.numerator
                           and math.isqrt(self.d.denominator) ** 2 == self.d.denominator):
            raise ValueError('d deve ser racional positivo que não é quadrado')

    def _coerce(self, x):
        if isinstance(x, QuadraticNumber):
            if x.d != self.d:
                raise ValueError('Extensões quadráticas diferentes')
            return x
        return QuadraticNumber(Q(x), 0, self.d)

    def __add__(self, other):
        t = self._coerce(other)
        return QuadraticNumber(self.a + t.a, self.b + t.b, self.d)

    __radd__ = __add__

    def __neg__(self):
        return QuadraticNumber(-self.a, -self.b, self.d)

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __mul__(self, other):
        t = self._coerce(other)
        return QuadraticNumber(self.a*t.a + self.d*self.b*t.b,
                               self.a*t.b + self.b*t.a, self.d)

    __rmul__ = __mul__

    def inverse(self):
        den = self.a*self.a - self.d*self.b*self.b
        if den == 0:
            raise ZeroDivisionError('Elemento nulo')
        return QuadraticNumber(self.a/den, -self.b/den, self.d)

    def __truediv__(self, other):
        return self * self._coerce(other).inverse()


@dataclass(frozen=True)
class CovariantTensor:
    """Tensor covariante de ordem k por componentes em uma base racional fixa."""
    dimension: int
    rank: int
    components: tuple[tuple[tuple[int, ...], Fraction], ...]

    def __post_init__(self):
        if self.dimension < 1 or self.rank < 0:
            raise ValueError('Dimensão ou ordem inválida')
        vals = defaultdict(Fraction)
        for ix, c in self.components:
            if len(ix) != self.rank or any(i < 0 or i >= self.dimension for i in ix):
                raise ValueError('Índices do tensor inválidos')
            vals[tuple(ix)] += Q(c)
        object.__setattr__(self, 'components', tuple(sorted((k, v) for k, v in vals.items() if v)))

    def tensor_product(self, other):
        if self.dimension != other.dimension:
            raise ValueError('Dimensão incompatível')
        return CovariantTensor(self.dimension, self.rank+other.rank,
            tuple((a+b, x*y) for a,x in self.components for b,y in other.components))

    def contract_with(self, vectors: Sequence[Vector]) -> Fraction:
        if len(vectors) != self.rank or any(v.dim != self.dimension for v in vectors):
            raise ValueError('Número de argumentos ou dimensão incompatível')
        return sum((c * math.prod(v.entries[i] for v,i in zip(vectors,indices))
                    for indices,c in self.components), Fraction(0))


def _sign_merge(a: tuple[int, ...], b: tuple[int, ...]) -> int:
    return -1 if sum(x>y for x in a for y in b) % 2 else 1


@dataclass(frozen=True)
class DifferentialForm:
    """k-forma polinomial sobre espaço afim: Σ f_I dx_{i1}∧...∧dx_{ik}."""
    dimension: int
    degree: int
    components: tuple[tuple[tuple[int, ...], Polynomial], ...]

    def __post_init__(self):
        if self.dimension < 1 or not 0 <= self.degree <= self.dimension:
            raise ValueError('Grau impossível')
        accum = {}
        for inds, f in self.components:
            if f.dimension != self.dimension or len(inds) != self.degree:
                raise ValueError('Índices ou anel incompatíveis')
            if any(i<0 or i>=self.dimension for i in inds) or len(set(inds)) != len(inds):
                raise ValueError('Índices devem ser distintos')
            sign = -1 if sum(inds[i] > inds[j] for i in range(len(inds)) for j in range(i+1,len(inds)))%2 else 1
            ordered = tuple(sorted(inds))
            accum[ordered] = accum.get(ordered, Polynomial.constant(self.dimension,0)) + f*sign
        object.__setattr__(self,'components',tuple(sorted((k,v) for k,v in accum.items() if not v.is_zero)))

    def wedge(self, other):
        if self.dimension != other.dimension or self.degree+other.degree > self.dimension:
            raise ValueError('Produto exterior inválido')
        values=[]
        for a,f in self.components:
            for b,g in other.components:
                if not set(a).intersection(b):
                    values.append((a+b,f*g))
        return DifferentialForm(self.dimension, self.degree+other.degree, tuple(values))

    def exterior_derivative(self):
        if self.degree == self.dimension:
            return DifferentialForm(self.dimension, self.degree, ())  # d=0, grau superior não representável
        values=[]
        for inds,f in self.components:
            for j in range(self.dimension):
                if j not in inds:
                    values.append(((j,)+inds,f.diff(j)))
        return DifferentialForm(self.dimension,self.degree+1,tuple(values))


# Anéis de funções e ideais polinomiais.
def leading_term(f: Polynomial):
    return max(f.terms, key=lambda v: (sum(v[0]), v[0])) if f.terms else None


def polynomial_division(f: Polynomial, divisors: Sequence[Polynomial]):
    """Divisão multivariada por graus totais, desempate lexicográfico."""
    if any(g.is_zero or g.dimension != f.dimension for g in divisors):
        raise ValueError('Divisores precisam ser não nulos e do mesmo anel')
    n=f.dimension
    q=[Polynomial.constant(n,0) for _ in divisors]
    r=Polynomial.constant(n,0)
    p=f
    while not p.is_zero:
        ex,coef=leading_term(p)
        for i,g in enumerate(divisors):
            ge,gc=leading_term(g)
            if all(x>=y for x,y in zip(ex,ge)):
                term=Polynomial(n,((tuple(x-y for x,y in zip(ex,ge)),coef/gc),))
                q[i]=q[i]+term
                p=p-term*g
                break
        else:
            term=Polynomial(n,((ex,coef),))
            r=r+term
            p=p-term
    return tuple(q),r


def groebner_basis(generators: Sequence[Polynomial], max_pairs: int=2000):
    """Buchberger, ordem graded lex; limitado explicitamente para evitar OOM.

    Garante base de Gröbner apenas ao concluir todos os pares S. Numa falha
    por limite computacional, levanta exceção em vez de devolver base incompleta.
    """
    if not generators:
        raise ValueError('Ideal requer ao menos um gerador')
    n=generators[0].dimension
    if any(f.dimension != n for f in generators):
        raise ValueError('Anéis incompatíveis')
    basis=[]
    for f in generators:
        if not f.is_zero:
            _,r=polynomial_division(f,basis) if basis else ((),f)
            if not r.is_zero:
                basis.append(r/leading_term(r)[1])
    pending=list(combinations(range(len(basis)),2))
    processed=0
    while pending:
        if processed>=max_pairs:
            raise RuntimeError('Limite explícito de pares de Buchberger')
        i,j=pending.pop(0);processed+=1
        f,g=basis[i],basis[j]
        af,cf=leading_term(f);ag,cg=leading_term(g)
        lm=tuple(max(x,y) for x,y in zip(af,ag))
        u=Polynomial(n,((tuple(x-y for x,y in zip(lm,af)),1/cf),))
        v=Polynomial(n,((tuple(x-y for x,y in zip(lm,ag)),1/cg),))
        _,r=polynomial_division(u*f-v*g,basis)
        if not r.is_zero:
            k=len(basis);basis.append(r/leading_term(r)[1]);pending.extend((i,k) for i in range(k))
    return tuple(basis)


def ideal_contains(candidate: Polynomial, basis: Sequence[Polynomial]) -> bool:
    return polynomial_division(candidate, basis)[1].is_zero if basis else candidate.is_zero


@dataclass(frozen=True)
class RationalFunction:
    """Elemento de Frac(Q[x]); denominador não nulo como polinômio.

    Redução por MDC implementada no caso univariado. Em dimensão >1 a
    representação não é canônica; igualdade é decidida por multiplicação cruzada.
    O domínio de avaliação exclui os zeros do denominador NORMALIZADO; fatores cancelados não preservam restrições do representante original.
    """
    numerator: Polynomial
    denominator: Polynomial

    def __post_init__(self):
        p,q=self.numerator,self.denominator
        if p.dimension!=q.dimension or q.is_zero:
            raise ValueError('Fração racional: anéis incompatíveis ou denominador zero')
        if p.is_zero:
            object.__setattr__(self,'denominator',Polynomial.constant(p.dimension,1))
        elif p.dimension==1:
            a,b=p,q
            while not b.is_zero:
                _,r=polynomial_division(a,(b,));a,b=b,r
            if not a.is_zero:
                p=polynomial_division(p,(a,))[0][0]
                q=polynomial_division(q,(a,))[0][0]
            c=leading_term(q)[1]
            object.__setattr__(self,'numerator',p/c)
            object.__setattr__(self,'denominator',q/c)

    @classmethod
    def from_polynomial(cls, p):
        return cls(p,Polynomial.constant(p.dimension,1))

    def _to(self,v):
        if isinstance(v,RationalFunction):
            if v.numerator.dimension!=self.numerator.dimension:
                raise ValueError('Anéis incompatíveis')
            return v
        if not isinstance(v,Polynomial):
            v=Polynomial.constant(self.numerator.dimension,v)
        return RationalFunction.from_polynomial(v)

    def __add__(self,v):
        w=self._to(v)
        return RationalFunction(self.numerator*w.denominator+w.numerator*self.denominator,
                                self.denominator*w.denominator)

    __radd__=__add__

    def __neg__(self):
        return RationalFunction(-self.numerator,self.denominator)

    def __sub__(self,v):
        return self+(-self._to(v))

    def __rsub__(self,v):
        return self._to(v)+(-self)

    def __mul__(self,v):
        w=self._to(v)
        return RationalFunction(self.numerator*w.numerator,self.denominator*w.denominator)

    __rmul__=__mul__

    def inverse(self):
        if self.numerator.is_zero:
            raise ZeroDivisionError('Função racional nula')
        return RationalFunction(self.denominator,self.numerator)

    def __truediv__(self,v):
        return self*self._to(v).inverse()

    def __pow__(self,e):
        if not isinstance(e,int):
            raise TypeError('Potências do corpo racional são inteiras')
        return RationalFunction(self.numerator**e,self.denominator**e) if e>=0 else self.inverse()**(-e)

    def __eq__(self,v):
        if not isinstance(v,(RationalFunction,Polynomial,int,Fraction)):
            return NotImplemented
        w=self._to(v)
        return self.numerator*w.denominator == w.numerator*self.denominator

    def diff(self,i):
        p,q=self.numerator,self.denominator
        return RationalFunction(p.diff(i)*q-p*q.diff(i),q*q)

    def evaluate(self,values):
        denominator=self.denominator.evaluate(values)
        if denominator==0:
            raise ZeroDivisionError('Polo ou ponto excluído do domínio')
        return self.numerator.evaluate(values)/denominator

    def substitute(self,images: Sequence["RationalFunction"]):
        if len(images)!=self.numerator.dimension:
            raise ValueError('Dimensão incompatível')
        def eval_poly(p):
            z=RationalFunction.from_polynomial(Polynomial.constant(p.dimension,0))
            for ex,c in p.terms:
                t=z._to(c)
                for image,k in zip(images,ex):
                    t=t*image**k
                z=z+t
            return z
        return eval_poly(self.numerator)/eval_poly(self.denominator)

# ─── Estrato 1: cartas locais e variedades algébricas suaves ─────────────
@dataclass(frozen=True)
class RationalChart:
    """Transição birracional em domínio aberto, com inversa declarada.

    A verificação é algébrica no corpo racional; NÃO é verificação completa
    de cobertura topológica, suavidade global ou do domínio real.
    """
    forward: tuple[RationalFunction, ...]
    backward: tuple[RationalFunction, ...]

    def __post_init__(self):
        d=len(self.forward)
        if not d or len(self.backward)!=d or any(f.numerator.dimension!=d for f in self.forward+self.backward):
            raise ValueError('Cartas de mesma dimensão necessárias')
        identity=tuple(RationalFunction.from_polynomial(Polynomial.variable(d,i)) for i in range(d))
        for fs,gs in ((self.forward,self.backward),(self.backward,self.forward)):
            if any(f.substitute(gs)!=x for f,x in zip(fs,identity)):
                raise ValueError('Cartas não são inversas como aplicações racionais')

    def jacobian(self):
        return tuple(tuple(f.diff(i) for i in range(len(self.forward))) for f in self.forward)

    def apply(self,point):
        return tuple(f.evaluate(point) for f in self.forward)


@dataclass(frozen=True)
class RationalAtlas:
    """Coleção de cartas com transições declaradas, sem alegação de cobertura global."""
    dimension: int
    transitions: tuple[RationalChart,...]

    def __post_init__(self):
        if self.dimension<1 or any(len(t.forward)!=self.dimension for t in self.transitions):
            raise ValueError('Dimensão inválida')


# ─── Estrato 0/2: intervalos certificados por desigualdades racionais ────
@dataclass(frozen=True)
class RationalInterval:
    lo: Fraction
    hi: Fraction

    def __post_init__(self):
        object.__setattr__(self,'lo',Q(self.lo))
        object.__setattr__(self,'hi',Q(self.hi))
        if self.lo>self.hi:
            raise ValueError('Intervalo invertido')

    def __add__(self,other):
        if not isinstance(other,RationalInterval): other=RationalInterval(Q(other),Q(other))
        return RationalInterval(self.lo+other.lo,self.hi+other.hi)

    __radd__=__add__

    def __neg__(self):
        return RationalInterval(-self.hi,-self.lo)

    def __sub__(self,other):
        return self+(-other if isinstance(other,RationalInterval) else -Q(other))

    def __mul__(self,other):
        if not isinstance(other,RationalInterval): other=RationalInterval(Q(other),Q(other))
        vals=(self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi)
        return RationalInterval(min(vals),max(vals))

    __rmul__=__mul__

    def reciprocal(self):
        if self.lo<=0<=self.hi:
            raise ZeroDivisionError('Intervalo contém zero')
        return RationalInterval(Fraction(1,self.hi),Fraction(1,self.lo))

    def __truediv__(self,other):
        if not isinstance(other,RationalInterval): other=RationalInterval(Q(other),Q(other))
        return self*other.reciprocal()

    def contains(self,v):
        return self.lo<=v<=self.hi


def _enclose(v: Fraction, error: Fraction) -> RationalInterval:
    return RationalInterval(v-error,v+error)


def interval_exp(x: Fraction, terms: int=20):
    """e^x certificado por Taylor; somente |x|≤1, resto ≤3/(n!) |x|^n."""
    x=Q(x)
    if abs(x)>1 or terms<1:
        raise ValueError('exp certificado exige |x|≤1 e terms≥1')
    partial=sum((x**k/Fraction(math.factorial(k)) for k in range(terms)),Fraction(0))
    bound=3*abs(x)**terms/Fraction(math.factorial(terms))
    return _enclose(partial,bound)


def interval_sin(x: Fraction, terms: int=12):
    """sen(x) para |x|≤1. Resto de Taylor ≤ |x|^(2N+1)/(2N+1)! ."""
    x=Q(x)
    if abs(x)>1 or terms<1:
        raise ValueError('sin certificado exige |x|≤1')
    partial=sum(((-1)**k*x**(2*k+1)/Fraction(math.factorial(2*k+1))
                 for k in range(terms)),Fraction(0))
    return _enclose(partial,abs(x)**(2*terms+1)/math.factorial(2*terms+1))


def interval_cos(x: Fraction, terms: int=12):
    x=Q(x)
    if abs(x)>1 or terms<1:
        raise ValueError('cos certificado exige |x|≤1')
    partial=sum(((-1)**k*x**(2*k)/Fraction(math.factorial(2*k))
                 for k in range(terms)),Fraction(0))
    return _enclose(partial,abs(x)**(2*terms)/math.factorial(2*terms))


def interval_log(x: Fraction, terms: int=20):
    """ln(x) para x∈[1/2,2] via artanh; resto majorado por série geométrica."""
    x=Q(x)
    if not Fraction(1,2)<=x<=2 or terms<1:
        raise ValueError('log certificado exige 1/2≤x≤2')
    t=(x-1)/(x+1)
    s=2*sum((t**(2*k+1)/Fraction(2*k+1) for k in range(terms)),Fraction(0))
    rem=2*abs(t)**(2*terms+1)/(Fraction(2*terms+1)*(1-t*t))
    return _enclose(s,rem)


def interval_pi(terms: int=18):
    """Machin: π=16 atan(1/5)−4 atan(1/239), alternância com resto exato."""
    if terms<1:
        raise ValueError('terms≥1')
    def atan_inv(k):
        t=Fraction(1,k)
        s=sum(((-1)**j*t**(2*j+1)/(2*j+1) for j in range(terms)),Fraction(0))
        rem=t**(2*terms+1)/(2*terms+1)
        return _enclose(s,rem)
    return atan_inv(5)*16-atan_inv(239)*4


# ─── Estrato 2: informação geométrica e famílias normais ───────────────
class FisherSphere:
    """Isometria Fisher-Rao interior do simplex → ortante positiva da esfera.

    Coordenadas u=√p; a métrica induzida é 4 du·du, NÃO du·du.
    Bordas são estratos, não coordenadas regulares da mesma variedade.
    """
    @staticmethod
    def embed(probabilities: Sequence[Fraction]):
        if not probabilities or any(p<0 for p in probabilities) or sum(probabilities)!=1:
            raise ValueError('Vetor de probabilidade inválido')
        return tuple(math.sqrt(float(p)) for p in probabilities)

    @staticmethod
    def distance(a: Sequence[Fraction],b: Sequence[Fraction]) -> float:
        if len(a)!=len(b):
            raise ValueError('Simplexes incompatíveis')
        u,v=FisherSphere.embed(a),FisherSphere.embed(b)
        cosangle=sum(x*y for x,y in zip(u,v))
        return 2*math.acos(min(1.,max(-1.,cosangle)))

    @staticmethod
    def distance_interval_bounds(a,b):
        """A distância em si é aproximada; este método fornece intervalo trivial 0..π."""
        if len(a)!=len(b): raise ValueError('Dimensões incompatíveis')
        FisherSphere.embed(a);FisherSphere.embed(b)
        return (0.0,math.pi)


@dataclass(frozen=True)
class GaussianFamily:
    """Distribuição Normal N(μ,v), v>0. Tensor Fisher e α-conexões exatos em Q."""
    mu: Fraction
    variance: Fraction

    def __post_init__(self):
        object.__setattr__(self,'mu',Q(self.mu));object.__setattr__(self,'variance',Q(self.variance))
        if self.variance<=0: raise ValueError('Variância deve ser positiva')

    def fisher_metric(self):
        v=self.variance
        return Matrix(((1/v,0),(0,1/(2*v*v))))

    def chentsov(self,i,j,k):
        """T_μμv=1/v²; T_vvv=1/v³; outros = 0."""
        if any(x not in (0,1) for x in (i,j,k)):
            raise ValueError('Coordenadas: 0=μ, 1=v')
        count=i+j+k
        return Fraction(1,self.variance**2) if count==1 else (Fraction(1,self.variance**3) if count==3 else Fraction(0))

    def christoffel(self,i,j,k,alpha: Fraction=Fraction(0)):
        """Γ^(α)k_ij = Γ^(0)k_ij − α/2 g^{kl}T_ijl."""
        if any(x not in (0,1) for x in (i,j,k)):
            raise ValueError('Índice inválido')
        v=self.variance
        gamma=Fraction(0)
        if (i,j,k) in ((0,1,0),(1,0,0)):gamma=-1/(2*v)
        if (i,j,k)==(0,0,1):gamma=Fraction(1)
        if (i,j,k)==(1,1,1):gamma=-1/v
        return gamma-Q(alpha)/2*self.fisher_metric().inverse().rows[k][k]*self.chentsov(i,j,k)

    def natural_gradient(self,covector: Vector):
        if covector.dim!=2:raise ValueError('Dimensão incorreta')
        return self.fisher_metric().inverse()@covector


# ─── Estrato 3: métodos e modelos dinâmicos ────────────────────────────
class ImplicitMidpoint:
    """Ponto médio simplético para H polinomial não necessariamente separável.

    Mapa exato para Hamiltonianos QUADRÁTICOS (resolver sistema linear em Q).
    Para grau ≥3, Newton numérico com resíduo explícito sem certificado
    de solução única/global; nesse caso a preservação é apenas aproximada.
    """
    def __init__(self,flow: HamiltonianFlow,h: Fraction):
        self.flow=flow;self.h=Q(h)
        self.field=flow.phase.hamiltonian_field(flow.energy)

    def _quadratic(self):
        return all(sum(p)<=1 for f in self.field for p,_ in f.terms)

    def step(self,z: Vector,iterations=100,tol=1e-12):
        d=self.flow.phase.dimension
        if z.dim!=d:raise ValueError('Dimensão inválida')
        if self._quadratic():
            zero=(Fraction(0),)*d
            b=Vector(tuple(f.evaluate(zero) for f in self.field))
            a=Matrix(tuple(tuple(f.diff(j).evaluate(zero) for j in range(d)) for f in self.field))
            I=Matrix.identity(d)
            y=(I-a.scale(self.h/2)).inverse()@(z+(a@z).scale(self.h/2)+b.scale(self.h))
            return y
        # Newton numérico para resolução aproximada do ponto médio não-linear.
        x=[float(u) for u in z.entries]
        z0=[float(u) for u in z.entries]
        h=float(self.h)
        for _ in range(iterations):
            mid=[(u+v)/2 for u,v in zip(x,z0)]
            f=[float(fi.evaluate(mid)) for fi in self.field]
            residual=[x[i]-z0[i]-h*f[i] for i in range(d)]
            if max(map(abs,residual))<tol:
                return tuple(x),max(map(abs,residual))
            jac=Matrix(tuple(tuple(Fraction.from_float(float(i==j)-h/2*float(self.field[i].diff(j).evaluate(mid)))
                                   for j in range(d)) for i in range(d)))
            delta=jac.inverse()@Vector(tuple(Fraction.from_float(r) for r in residual))
            x=[x[i]-float(delta.entries[i]) for i in range(d)]
        raise RuntimeError('Newton não convergiu dentro do limite; nenhuma prova de convergência')


class VelocityVerlet:
    """Verlet kick-drift-kick; somente H=T(p)+V(q), aritmética Q exata."""
    def __init__(self,flow: HamiltonianFlow,h: Fraction):
        self.flow=flow;self.h=Q(h)
        n=flow.phase.pairs;H=flow.energy
        if any(not H.diff(i).diff(n+j).is_zero for i in range(n) for j in range(n)):
            raise ValueError('Verlet requer Hamiltoniano separável')

    def step(self,z: Vector):
        n=self.flow.phase.pairs
        if z.dim!=2*n: raise ValueError('Dimensão inválida')
        H=self.flow.energy;h=self.h
        q=z.entries[:n];p=z.entries[n:]
        ph=tuple(p[i]-h/2*H.diff(i).evaluate(z.entries) for i in range(n))
        qn=tuple(q[i]+h*H.diff(n+i).evaluate(q+ph) for i in range(n))
        pn=tuple(ph[i]-h/2*H.diff(i).evaluate(qn+ph) for i in range(n))
        return Vector(qn+pn)


class Yoshida4:
    """Composição simétrica de Verlet com coeficientes aproximados em float.

    Ordem formal 4 para coeficientes reais exatos c=1/(2−2^(1/3)); as frações
    adotadas são aproximações, logo NÃO garantem rigor de ordem 4 assintótico.
    """
    def __init__(self,flow: HamiltonianFlow,h: Fraction,digits: int=35):
        from decimal import Decimal,localcontext
        if digits<10: raise ValueError('Precisão muito pequena')
        with localcontext() as ctx:
            ctx.prec=digits+10
            two=Decimal(2); root=two**(Decimal(1)/3)
            c=Decimal(1)/(two-root)
            self.coefficients=(Fraction(str(+c)),Fraction(str(+(1-2*c))),Fraction(str(+c)))
        self.flow=flow;self.h=Q(h)

    def step(self,z: Vector):
        for c in self.coefficients:
            z=VelocityVerlet(self.flow,self.h*c).step(z)
        return z


@dataclass(frozen=True)
class ContactFlow:
    """Contato η=dz−Σp_i dq_i; H(q,p,z) polinomial em 2n+1 variáveis.

    q'=∂pH, p'=−∂qH−p∂zH, z'=Σ p∂pH−H.
    """
    pairs: int
    H: Polynomial

    def __post_init__(self):
        if self.pairs<1 or self.H.dimension!=2*self.pairs+1:
            raise ValueError('Hamiltoniano de contato deve ter 2n+1 variáveis')

    def field(self):
        n=self.pairs;H=self.H;d=2*n+1
        p=tuple(Polynomial.variable(d,n+i) for i in range(n))
        dz=H.diff(2*n)
        return (tuple(H.diff(n+i) for i in range(n))+
                tuple(-H.diff(i)-p[i]*dz for i in range(n))+
                (sum((p[i]*H.diff(n+i) for i in range(n)),Polynomial.constant(d,0))-H,))

    def derivative_of_hamiltonian(self):
        return -self.H*self.H.diff(2*self.pairs)

# ─── Estrato 4: diferenciabilidade, atenção causal e grupos 3D ─────────
@dataclass(frozen=True)
class SymbolicExpr:
    """Árvore de expressões formais com regra da cadeia exata (sem float no AD).

    Funções exp/log/sin/cos permanecem primitivas simbólicas; o valor
    numérico é aproximado via math, não há prova de intervalo implícita.
    """
    op: str
    args: tuple=()

    @staticmethod
    def const(x):
        return SymbolicExpr('const',(Q(x),))

    @staticmethod
    def var(i):
        if i<0:raise ValueError('Índice negativo')
        return SymbolicExpr('var',(i,))

    @staticmethod
    def coerce(x):
        return x if isinstance(x,SymbolicExpr) else SymbolicExpr.const(x)

    def __add__(self,v):return SymbolicExpr('add',(self,self.coerce(v)))
    __radd__=__add__
    def __neg__(self):return SymbolicExpr('neg',(self,))
    def __sub__(self,v):return self+(-self.coerce(v))
    def __mul__(self,v):return SymbolicExpr('mul',(self,self.coerce(v)))
    __rmul__=__mul__
    def __truediv__(self,v):return self*self.coerce(v)**-1
    def __pow__(self,v):
        if not isinstance(v,int):raise TypeError('Expoente inteiro exigido')
        return SymbolicExpr('pow',(self,v))
    def exp(self):return SymbolicExpr('exp',(self,))
    def log(self):return SymbolicExpr('log',(self,))
    def sin(self):return SymbolicExpr('sin',(self,))
    def cos(self):return SymbolicExpr('cos',(self,))

    def diff(self,i):
        op=self.op; a=self.args
        if op=='const':return self.const(0)
        if op=='var':return self.const(int(a[0]==i))
        if op=='add':return a[0].diff(i)+a[1].diff(i)
        if op=='neg':return -a[0].diff(i)
        if op=='mul':return a[0].diff(i)*a[1]+a[0]*a[1].diff(i)
        if op=='pow':return self.const(a[1])*a[0]**(a[1]-1)*a[0].diff(i)
        if op=='exp':return self*a[0].diff(i)
        if op=='log':return a[0].diff(i)/a[0]
        if op=='sin':return a[0].cos()*a[0].diff(i)
        if op=='cos':return -a[0].sin()*a[0].diff(i)
        raise ValueError('Operação formal não cadastrada')

    def eval(self,z):
        op=self.op;a=self.args
        if op=='const':return float(a[0])
        if op=='var':return float(z[a[0]])
        if op=='add':return a[0].eval(z)+a[1].eval(z)
        if op=='neg':return -a[0].eval(z)
        if op=='mul':return a[0].eval(z)*a[1].eval(z)
        if op=='pow':return a[0].eval(z)**a[1]
        if op in ('exp','log','sin','cos'):return getattr(math,op)(a[0].eval(z))
        raise ValueError('Operação formal não cadastrada')


class DifferentiableRouter:
    """Softmax como operador simbólico de scores; gradiente analítico formal.

    A função objetivo é max_{w∈Δ} w·s + τH(w). Para τ racional >0,
    J_ij= (δ_ij−w_j) w_i/τ, uma identidade formal, não erro de float.
    """
    @staticmethod
    def weights(scores: Sequence[SymbolicExpr],temperature: Fraction=Fraction(1)):
        tau=Q(temperature)
        if tau<=0 or not scores:raise ValueError('Temperatura positiva necessária')
        exps=[(SymbolicExpr.coerce(s)/tau).exp() for s in scores]
        normal=sum(exps,SymbolicExpr.const(0))
        return tuple(v/normal for v in exps)

    @staticmethod
    def jacobian(weights:Sequence[SymbolicExpr],temperature:Fraction=Fraction(1)):
        tau=Q(temperature)
        return tuple(tuple(w*(SymbolicExpr.const(int(i==j))-weights[j])/tau
                           for j in range(len(weights))) for i,w in enumerate(weights))


@dataclass(frozen=True)
class SO3:
    """SO(3) como grupo de matrizes ortogonais racionais com det=+1.

    Rotações via parâmetro de Cayley t=tan(θ/2) racional; não cobre θ=π.
    """
    matrix: Matrix

    def __post_init__(self):
        if self.matrix.shape!=(3,3) or self.matrix.transpose()@self.matrix!=Matrix.identity(3) or bareiss_determinant(self.matrix)!=1:
            raise ValueError('Matriz não pertence a SO(3)')

    @classmethod
    def about_z(cls,t:Fraction):
        t=Q(t);den=1+t*t;c=(1-t*t)/den;s=2*t/den
        return cls(Matrix(((c,-s,0),(s,c,0),(0,0,1))))

    @classmethod
    def about_x(cls,t:Fraction):
        t=Q(t);den=1+t*t;c=(1-t*t)/den;s=2*t/den
        return cls(Matrix(((1,0,0),(0,c,-s),(0,s,c))))

    def __matmul__(self,other):
        return SO3(self.matrix@other.matrix)

    def act(self,v:Vector):return self.matrix@v


@dataclass(frozen=True)
class SE3:
    rotation: SO3
    translation: Vector

    def __post_init__(self):
        if self.translation.dim!=3:raise ValueError('SE(3) exige translação 3D')

    def __matmul__(self,other):
        return SE3(self.rotation@other.rotation,
                   self.translation+self.rotation.act(other.translation))

    def act(self,v:Vector):return self.rotation.act(v)+self.translation


class CausalMultiHeadAttention:
    """Atenção escalada multi-head em listas Python; projeções explícitas.

    É uma referência funcional, NÃO um motor eficiente de treinamento;
    não há inferência de gradientes de pesos via floats neste método.
    """
    def __init__(self,wq: Sequence[Matrix],wk: Sequence[Matrix],wv:Sequence[Matrix]):
        if not wq or len(wq)!=len(wk) or len(wq)!=len(wv):
            raise ValueError('As três famílias de cabeças devem coincidir')
        self.wq=tuple(wq);self.wk=tuple(wk);self.wv=tuple(wv)
        for q,k,v in zip(wq,wk,wv):
            if q.shape[0]!=k.shape[0] or q.shape[1]!=k.shape[1] or k.shape[1]!=v.shape[1]:
                raise ValueError('Projeções incompatíveis')

    def apply(self,tokens:Sequence[Vector],causal=True):
        if not tokens or any(x.dim!=tokens[0].dim for x in tokens):
            raise ValueError('Sequência inválida')
        T=len(tokens)
        results=[]
        for q,k,v in zip(self.wq,self.wk,self.wv):
            qs=[q@x for x in tokens];ks=[k@x for x in tokens];vs=[v@x for x in tokens]
            output=[]
            for i in range(T):
                max_index=i+1 if causal else T
                scores=[float(qs[i].dot(ks[j])) for j in range(max_index)]
                weights=EntropicRouter.weights(scores,math.sqrt(q.shape[0]))
                output.append(tuple(sum(weights[j]*float(vs[j].entries[c]) for j in range(max_index))
                                    for c in range(v.shape[0])))
            results.append(tuple(output))
        return tuple(tuple(v for head in results for v in head[i]) for i in range(T))


# ─── Estrato 5: simetrias gerais, independência e tensores de Poisson ───
def noether_charge(generators:Sequence[Polynomial]):
    """Levantamento cotangente de X=Σ ξ_i(q)∂q_i: P_X=Σ p_iξ_i(q).

    As entradas são polinômios em n coordenadas q e retornamos polinômio
    em 2n variáveis (q,p), com substituição algébrica exata.
    """
    n=len(generators)
    if not n or any(f.dimension!=n for f in generators):
        raise ValueError('Campo X deve possuir n componentes em Q[q_1,..,q_n]')
    xs=[Polynomial.variable(2*n,i) for i in range(2*n)]
    total=Polynomial.constant(2*n,0)
    for i,f in enumerate(generators):
        transplanted=Polynomial.constant(2*n,0)
        for exp,c in f.terms:
            term=Polynomial.constant(2*n,c)
            for x,k in zip(xs[:n],exp):term*=x**k
            transplanted+=term
        total+=xs[n+i]*transplanted
    return total


def _field_rank(matrix:Sequence[Sequence[RationalFunction]]):
    """Posto exato sobre Q(x), usando eliminação gaussiana no corpo racional."""
    if not matrix:return 0
    a=[list(row) for row in matrix]
    m,n=len(a),len(a[0]);row=0
    for j in range(n):
        k=next((i for i in range(row,m) if a[i][j].numerator.terms),None)
        if k is None:continue
        a[row],a[k]=a[k],a[row]
        pivot=a[row][j]
        a[row]=[v/pivot for v in a[row]]
        for i in range(row+1,m):
            z=a[i][j]
            if not z.numerator.is_zero:
                a[i]=[x-z*y for x,y in zip(a[i],a[row])]
        row+=1
        if row==m:break
    return row


def algebraic_independence_rank(invariants:Sequence[Polynomial]):
    """Posto genérico do Jacobiano = grau de transcendência (característica 0).

    Pode ser caro quando as expressões racionais explodem.
    """
    if not invariants:return 0
    n=invariants[0].dimension
    if any(p.dimension!=n for p in invariants):raise ValueError('Dimensões incompatíveis')
    rows=[[RationalFunction.from_polynomial(f.diff(j)) for j in range(n)] for f in invariants]
    return _field_rank(rows)


def independent_invariants(candidates:Sequence[Polynomial],known:Sequence[Polynomial]=()):
    """Retém candidatos que aumentam o posto jacobiano sobre Q(x)."""
    found=list(known);rank=algebraic_independence_rank(found)
    novel=[]
    for c in candidates:
        new_rank=algebraic_independence_rank(found+[c])
        if new_rank>rank:
            novel.append(c);found.append(c);rank=new_rank
    return tuple(novel)


def pruned_monomials(n:int,degree:int,parity:int|None=None,
                     weights:Sequence[int]|None=None,target_weight:int|None=None,
                     max_terms:int=200_000):
    """Enumeração incremental sem produto cartesiano (d+1)^n.

    parity refere-se ao grau total mod 2; pesos devem ser estritamente
    positivos e são usados somente se target_weight for fornecido.
    """
    if n<1 or degree<0 or (parity is not None and parity not in (0,1)):
        raise ValueError('Argumentos inválidos')
    if weights is not None and (len(weights)!=n or any(w<=0 for w in weights)):
        raise ValueError('Pesos dimensionais positivos necessários')
    count=0
    def recur(prefix,index,remaining):
        nonlocal count
        if index==n:
            exp=tuple(prefix)
            if (parity is None or sum(exp)%2==parity) and (target_weight is None or sum(w*e for w,e in zip(weights,exp))==target_weight):
                count+=1
                if count>max_terms:raise RuntimeError('Limite de monômios atingido')
                yield exp
        else:
            for k in range(remaining+1):
                yield from recur(prefix+[k],index+1,remaining-k)
    yield from recur([],0,degree)


@dataclass(frozen=True)
class PolynomialPoissonTensor:
    """Estrutura de Poisson π^{ij}(z), inclusive degenerada, sobre Q[z]."""
    pi: tuple[tuple[Polynomial,...],...]

    def __post_init__(self):
        n=len(self.pi)
        if not n or any(len(row)!=n for row in self.pi) or any(f.dimension!=n for row in self.pi for f in row):
            raise ValueError('Bivetor inválido')
        if any(self.pi[i][j]!=-self.pi[j][i] for i in range(n) for j in range(n)):
            raise ValueError('Bivetor deve ser antissimétrico')
        for i in range(n):
            for j in range(i+1,n):
                for k in range(j+1,n):
                    jac=Polynomial.constant(n,0)
                    for ell in range(n):
                        jac+=self.pi[i][ell]*self.pi[j][k].diff(ell)
                        jac+=self.pi[j][ell]*self.pi[k][i].diff(ell)
                        jac+=self.pi[k][ell]*self.pi[i][j].diff(ell)
                    if not jac.is_zero:
                        raise ValueError('O bivetor não satisfaz Jacobi')

    def bracket(self,f,g):
        n=len(self.pi)
        if f.dimension!=n or g.dimension!=n:raise ValueError('Anéis incompatíveis')
        out=Polynomial.constant(n,0)
        for i in range(n):
            for j in range(n):out+=f.diff(i)*self.pi[i][j]*g.diff(j)
        return out

    def casimir_certificate(self,c):
        """Equivalência local: C é Casimir sse π ∇C = 0 (identidade polinomial)."""
        n=len(self.pi)
        if c.dimension!=n:raise ValueError('Dimensão incorreta')
        return all(sum((self.pi[i][j]*c.diff(j) for j in range(n)),Polynomial.constant(n,0)).is_zero
                   for i in range(n))


def so3_lie_poisson():
    x,y,z=(Polynomial.variable(3,i) for i in range(3))
    O=Polynomial.constant(3,0)
    # Convenção {x,y}=z, {y,z}=x, {z,x}=y.
    return PolynomialPoissonTensor(((O,z,-y),(-z,O,x),(y,-x,O)))


# ─── Exportação de identidades para Lean 4 ────────────────────────────
def lean_polynomial(p:Polynomial,variables:Sequence[str]):
    """Expressão ℚ-polynomial sem definições externas, para Lean + Mathlib."""
    if len(variables)!=p.dimension:raise ValueError('Número incorreto de símbolos')
    def coef(c):return f'(({c.numerator} : ℚ) / ({c.denominator} : ℚ))'
    if p.is_zero:return '(0 : ℚ)'
    terms=[]
    for power,c in p.terms:
        pieces=[coef(c)]
        pieces.extend(f'({v} ^ {e})' for v,e in zip(variables,power) if e)
        terms.append('('+' * '.join(pieces)+')')
    return '('+' + '.join(terms)+')'


def export_lean_conservation(f:Polynomial,h:Polynomial,phase:SymplecticSpace,
                             theorem_name='conserved_poisson_identity') -> str:
    """Gera prova Lean via `ring` do parêntese EXPANDIDO, e não define ∂/Poisson.

    A saída deve ser verificada em `lake env lean` com Mathlib instalado;
    a execução local do Python NÃO substitui esse kernel de prova.
    """
    if f.dimension!=phase.dimension or h.dimension!=phase.dimension:
        raise ValueError('Espaço incorreto')
    vars=tuple(f'x{i}' for i in range(phase.dimension))
    bracket=phase.poisson(f,h)
    if not bracket.is_zero:
        raise ValueError('Observável não conservado')
    terms=[]
    for i in range(phase.pairs):
        terms.append('('+lean_polynomial(f.diff(i),vars)+' * '+lean_polynomial(h.diff(phase.pairs+i),vars)+
                     ' - '+lean_polynomial(f.diff(phase.pairs+i),vars)+' * '+lean_polynomial(h.diff(i),vars)+')')
    expr='('+' + '.join(terms)+')'
    return ('import Mathlib\n\n'
            f'theorem {theorem_name} ('+' '.join(f'({x} : ℚ)' for x in vars)+
            f') : {expr} = 0 := by\n  ring\n')
