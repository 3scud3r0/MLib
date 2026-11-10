#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ML-MATHLIB 0.4 — extensão auditável da matemática exata.

Convenções: igualdade polinomial é identidade sobre Q; intervalos inclusivos
em Q provam inclusão real, condicionados às hipóteses expressamente testadas.
Nenhuma rotina converte uma aproximação numérica em prova formal de Lean.

Este módulo NÃO fornece uma solução universal para teoria da medida, cálculo
simbólico transcendental, geometria global nem complexidade de Gröbner.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from typing import Sequence

from ml_mathlib import Q, Polynomial as P, Vector, Matrix
from ml_mathlib_advanced import (RationalFunction as RF, RationalInterval as I,
    polynomial_division, leading_term, groebner_basis, interval_pi)
from ml_mathlib_exact import (interval_sqrt, interval_exp_global, interval_log_global,
    CertifiedFisherSphere, primitive_integer_kernel)


def poly_exact_quotient(a:P,b:P)->P:
    """a/b se e somente se b divide a no anel de polinômios (não no corpo)."""
    if a.dimension!=b.dimension or b.is_zero:raise ValueError('Divisor incompatível ou nulo')
    quotient,remainder=polynomial_division(a,(b,))
    if not remainder.is_zero:raise ValueError('Divisão polinomial não exata')
    return quotient[0]


def _normalize_gcd(a:P)->P:
    if a.is_zero:return a
    return a/leading_term(a)[1]


def multivariate_gcd(a:P,b:P, max_degree:int=16)->P:
    """MDC multivariado exato por Gauss + Euclides em Q(x₁,…)[xₙ].

    O conteúdo em Q[x₁,…,xₙ₋₁] é extraído recursivamente. O MDC da parte
    primitiva é computado no corpo de frações dos coeficientes, e seus
    denominadores são eliminados antes de reextrair o conteúdo. Portanto o
    resultado divide ambos os polinômios, a menos de unidades de Q.

    Este algoritmo é completo matematicamente, mas pode crescer
    exponencialmente em tamanho. `max_degree` rejeita entradas descontroladas.
    """
    if a.dimension != b.dimension:raise ValueError('Anéis incompatíveis')
    n=a.dimension
    if max_degree < 0:raise ValueError('Limite de grau inválido')
    if a.is_zero:return _normalize_gcd(b)
    if b.is_zero:return _normalize_gcd(a)
    if max(sum(ex) for ex,_ in a.terms+b.terms)>max_degree:
        raise RuntimeError('Limite de grau excedido; sem resultado incompleto')
    if n==1:
        while not b.is_zero:
            _,r=polynomial_division(a,(b,));a,b=b,r
        return _normalize_gcd(a)

    def split(p:P):
        coeff={}
        for exp,c in p.terms:
            e=exp[-1];re=exp[:-1]
            coeff[e]=coeff.get(e,P.constant(n-1,0))+P(n-1,((re,c),))
        return coeff

    def lift(c:P,degree:int=0):
        return P(n,tuple((ex+(degree,),v) for ex,v in c.terms))

    def poly_content(coeff:dict[int,P]):
        if not coeff:return P.constant(n-1,0)
        it=iter(coeff.values());g=next(it)
        for item in it:g=multivariate_gcd(g,item,max_degree=max_degree)
        return _normalize_gcd(g)

    sa,sb=split(a),split(b)
    ca,cb=poly_content(sa),poly_content(sb)
    cg=multivariate_gcd(ca,cb,max_degree=max_degree)
    # Convert coefficients to rational functions of the first n-1 variables.
    aa={e: RF.from_polynomial(poly_exact_quotient(v,ca)) for e,v in sa.items()}
    bb={e: RF.from_polynomial(poly_exact_quotient(v,cb)) for e,v in sb.items()}
    zero=RF.from_polynomial(P.constant(n-1,0))
    def trim(c):return {j:v for j,v in c.items() if v!=zero}
    def monic(c):
        c=trim(c)
        if not c:return c
        top=c[max(c)];return {e:v/top for e,v in c.items()}
    def rem(p,q):
        p=trim(p)
        while p and max(p)>=max(q):
            shift=max(p)-max(q);factor=p[max(p)]/q[max(q)]
            for j,v in q.items():p[j+shift]=p.get(j+shift,zero)-factor*v
            p=trim(p)
        return p
    aa,bb=monic(aa),monic(bb)
    steps=0
    while bb:
        aa,bb=bb,monic(rem(aa,bb));steps+=1
        if steps>max_degree+2:raise ArithmeticError('Euclides não terminou no limite de grau')
    if not aa:return _normalize_gcd(lift(cg))
    # Clear all denominators by their product. This preserves the K[x]-gcd
    # up to a nonzero coefficient factor; primitive-part removal cancels it.
    common=P.constant(n-1,1)
    for v in aa.values():common=common*v.denominator
    cleared={}
    for e,v in aa.items():
        t=RF.from_polynomial(common)*v
        cleared[e]=poly_exact_quotient(t.numerator,t.denominator)
    cc=poly_content(cleared)
    primitive=sum((lift(poly_exact_quotient(v,cc),e) for e,v in cleared.items()),P.constant(n,0))
    answer=_normalize_gcd(primitive*lift(cg))
    # Independently verify that this is a common divisor: never expose a
    # candidate that has not passed the exact algebraic division checks.
    poly_exact_quotient(a,answer);poly_exact_quotient(b,answer)
    return answer


@dataclass(frozen=True)
class ReducedRational:
    """Forma reduzida de elemento de Q(x₁,…,xₙ) com MDC multivariado exato.

    Na linguagem de corpos, os zeros de fatores cancelados não são polos da
    função reduzida; aplicações com domínio original precisam guardar o
    domínio separadamente. Esta classe representa a função no corpo de frações.
    """
    numerator:P
    denominator:P

    def __post_init__(self):
        a,b=self.numerator,self.denominator
        if a.dimension!=b.dimension or b.is_zero:raise ValueError('Fração inválida')
        if a.is_zero:
            object.__setattr__(self,'denominator',P.constant(a.dimension,1));return
        g=multivariate_gcd(a,b)
        a=poly_exact_quotient(a,g);b=poly_exact_quotient(b,g)
        c=leading_term(b)[1]
        object.__setattr__(self,'numerator',a/c)
        object.__setattr__(self,'denominator',b/c)

    def as_rational(self):return RF(self.numerator,self.denominator)


@dataclass(frozen=True)
class RationalDifferentialForm:
    """k-forma racional local ω=Σ f_I(x) dx_{i1}∧…∧dx_{ik}."""
    dimension:int
    degree:int
    components:tuple[tuple[tuple[int,...],RF],...]

    def __post_init__(self):
        n,k=self.dimension,self.degree
        if n<1 or k<0 or (k>n and self.components):raise ValueError('Grau inválido')
        coeff=defaultdict(lambda: RF.from_polynomial(P.constant(n,0)))
        for inds,f in self.components:
            if f.numerator.dimension!=n or len(inds)!=k or len(set(inds))!=k or any(not 0<=j<n for j in inds):
                raise ValueError('Componente inválido')
            sign=(-1)**sum(inds[i]>inds[j] for i in range(k) for j in range(i+1,k))
            coeff[tuple(sorted(inds))]=coeff[tuple(sorted(inds))]+f*sign
        object.__setattr__(self,'components',tuple(sorted((ix,v) for ix,v in coeff.items() if v!=0)))

    @classmethod
    def scalar(cls,p:RF):return cls(p.numerator.dimension,0,(((),p),))

    def exterior_derivative(self):
        n,k=self.dimension,self.degree
        if k>=n:return RationalDifferentialForm(n,k+1,())
        return RationalDifferentialForm(n,k+1,tuple(((j,)+ix,f.diff(j))
            for ix,f in self.components for j in range(n) if j not in ix))

    def wedge(self,other:'RationalDifferentialForm'):
        if self.dimension!=other.dimension:
            raise ValueError('Produto exterior inválido')
        if self.degree+other.degree>self.dimension:
            return RationalDifferentialForm(self.dimension,self.degree+other.degree,())
        return RationalDifferentialForm(self.dimension,self.degree+other.degree,tuple((ix+jx,f*g)
            for ix,f in self.components for jx,g in other.components if not set(ix)&set(jx)))

    def pullback(self,map_components:Sequence[RF]):
        """Pullback local por mapa racional F:Q^m ⇢ Q^n.

        O coeficiente de du_J é Σ_I (f_I∘F) det ∂F_I/∂u_J.
        Pontos onde qualquer denominador desapareça ficam fora da carta.
        """
        n,k=self.dimension,self.degree
        if len(map_components)!=n:raise ValueError('Dimensão de alvo incompatível')
        m=map_components[0].numerator.dimension
        if any(f.numerator.dimension!=m for f in map_components):raise ValueError('Mapa incompatível')
        if k>m:return RationalDifferentialForm(m,k,())
        result=[]
        for J in combinations(range(m),k):
            coef=RF.from_polynomial(P.constant(m,0))
            for A,f in self.components:
                jac=tuple(tuple(map_components[a].diff(j) for j in J) for a in A)
                det=rational_determinant(jac,m)
                coef+=rational_substitution(f,map_components)*det
            if coef!=0:result.append((J,coef))
        return RationalDifferentialForm(m,k,tuple(result))



def rational_substitution(f:RF, map_components:Sequence[RF])->RF:
    """Substituição racional Q(x_1,...,x_n)→Q(u_1,...,u_m).

    Diferentemente da API antiga, aceita n != m. A substituição só é
    definida se o denominador substituído não for o polinômio nulo.
    """
    n=f.numerator.dimension
    if len(map_components)!=n:raise ValueError('Aridade incorreta')
    m=map_components[0].numerator.dimension
    if any(x.numerator.dimension!=m for x in map_components):raise ValueError('Anéis incompatíveis')
    def eval_poly(p):
        result=RF.from_polynomial(P.constant(m,0))
        for ex,c in p.terms:
            term=RF.from_polynomial(P.constant(m,c))
            for image,deg in zip(map_components,ex):term=term*image**deg
            result=result+term
        return result
    return eval_poly(f.numerator)/eval_poly(f.denominator)

def rational_determinant(rows:Sequence[Sequence[RF]],dimension:int)->RF:
    """Determinante alternado por permutações, adequado a pequenas k-formas."""
    n=len(rows);zero=RF.from_polynomial(P.constant(dimension,0))
    if any(len(r)!=n for r in rows):raise ValueError('Matriz não quadrada')
    if n==0:return RF.from_polynomial(P.constant(dimension,1))
    z=zero
    for perm in permutations(range(n)):
        s=(-1)**sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        v=RF.from_polynomial(P.constant(dimension,s))
        for i,j in enumerate(perm):v=v*rows[i][j]
        z+=v
    return z


@dataclass(frozen=True)
class IdealMembershipCertificate:
    """Testemunho de pertença f=Σ h_i g_i, verificado por multiplicação exata."""
    candidate:P
    generators:tuple[P,...]
    coefficients:tuple[P,...]

    def verify(self)->bool:
        return (len(self.generators)==len(self.coefficients) and
                self.candidate==sum((a*b for a,b in zip(self.coefficients,self.generators)),
                                    P.constant(self.candidate.dimension,0)))


def groebner_witness(candidate:P,generators:Sequence[P],max_pairs:int=3000)->IdealMembershipCertificate|None:
    """Buchberger com rastreamento da combinação dos geradores originais.

    Retorna testemunho positivo com igualdade polinomial exata, ou None após
    completar a base (caso negativo). Se esgotar orçamento, levanta exceção.
    """
    gens=tuple(generators)
    if not gens or any(g.dimension!=candidate.dimension for g in gens):
        raise ValueError('Geradores inválidos')
    n=candidate.dimension;m=len(gens);Z=P.constant(n,0)
    def unit(j):return tuple(P.constant(n,int(j==k)) for k in range(m))
    def normal(f,rep):
        if f.is_zero:return f,rep
        c=leading_term(f)[1]
        return f/c,tuple(t/c for t in rep)
    basis=[];reps=[]
    for j,g in enumerate(gens):
        if g.is_zero:continue
        if basis:
            quot,rem=polynomial_division(g,basis)
            rep=tuple(unit(j)[k]-sum((quot[i]*reps[i][k] for i in range(len(basis))),Z)
                      for k in range(m))
        else:rem=g;rep=unit(j)
        if not rem.is_zero:
            rem,rep=normal(rem,rep);basis.append(rem);reps.append(rep)
    queue=list(combinations(range(len(basis)),2));processed=0
    while queue:
        if processed>=max_pairs:raise RuntimeError('Limite de pares; não é prova de não pertinência')
        i,j=queue.pop(0);processed+=1
        fi,fj=basis[i],basis[j]
        li,ci=leading_term(fi);lj,cj=leading_term(fj)
        common=tuple(max(a,b) for a,b in zip(li,lj))
        ai=P(n,((tuple(a-b for a,b in zip(common,li)),1/ci),))
        aj=P(n,((tuple(a-b for a,b in zip(common,lj)),1/cj),))
        s=ai*fi-aj*fj
        sr=tuple(ai*reps[i][k]-aj*reps[j][k] for k in range(m))
        quot,rem=polynomial_division(s,basis)
        rep=tuple(sr[k]-sum((quot[t]*reps[t][k] for t in range(len(basis))),Z)
                  for k in range(m))
        if not rem.is_zero:
            rem,rep=normal(rem,rep)
            k=len(basis);basis.append(rem);reps.append(rep)
            queue.extend((i,k) for i in range(k))
    if not basis:return IdealMembershipCertificate(candidate,gens,tuple(Z for _ in gens)) if candidate.is_zero else None
    quot,rem=polynomial_division(candidate,basis)
    if not rem.is_zero:return None
    coeff=tuple(sum((quot[t]*reps[t][k] for t in range(len(basis))),Z) for k in range(m))
    cert=IdealMembershipCertificate(candidate,gens,coeff)
    if not cert.verify():raise ArithmeticError('Falha no certificado de ideal')
    return cert


@dataclass(frozen=True)
class GaussianPolynomialLaw:
    """Probabilidade Normal N(μ,σ²), integrada exatamente para Q[x].

    Momentos seguem integração por partes gaussiana:
        E[X^k] = μ E[X^(k−1)] + (k−1)σ² E[X^(k−2)].
    A existência da medida Normal é pressuposta pela teoria clássica; esta
    classe certifica valores de integrais polinomiais, não constrói Lebesgue.
    """
    mean:F
    variance:F
    def __post_init__(self):
        object.__setattr__(self,'mean',Q(self.mean))
        object.__setattr__(self,'variance',Q(self.variance))
        if self.variance<=0:raise ValueError('Variância deve ser positiva')

    def moments(self,degree:int)->tuple[F,...]:
        if degree<0:raise ValueError('Grau inválido')
        a=[F(1)]
        if degree>=1:a.append(self.mean)
        for k in range(2,degree+1):a.append(self.mean*a[-1]+(k-1)*self.variance*a[-2])
        return tuple(a)

    def expectation(self,p:P)->F:
        if p.dimension!=1:raise ValueError('Observável univariado necessário')
        degree=max((exp[0] for exp,_ in p.terms),default=0)
        moments=self.moments(degree)
        return sum((c*moments[exp[0]] for exp,c in p.terms),F(0))


@dataclass(frozen=True)
class GaussianMixturePolynomialLaw:
    """Mistura finita de Normais, funcional positivo para polinômios ≥0."""
    weights:tuple[F,...]
    components:tuple[GaussianPolynomialLaw,...]
    def __post_init__(self):
        w=tuple(Q(x) for x in self.weights)
        if not w or len(w)!=len(self.components) or any(x<0 for x in w) or sum(w)!=1:
            raise ValueError('Pesos devem formar distribuição finita')
        object.__setattr__(self,'weights',w)

    def expectation(self,p:P):
        return sum((w*m.expectation(p) for w,m in zip(self.weights,self.components)),F(0))


@dataclass(frozen=True)
class CategoricalInformationGeometry:
    """Métrica Fisher e conexões α do interior do simplex em coordenadas mistura.

    Para n=k−1 coordenadas p_i>0 e p_k=1−Σp_i>0,
    g_ij=δ_ij/p_i+1/p_k. Tensor de Amari-Chentsov:
    T_ijk=δ_{i=j=k}/p_i²−1/p_k².
    Γ^(α)_{ij,k}=−(1+α)T_ijk/2 nesta carta.
    A conexão α=−1 é plana nas coordenadas mistura, enquanto α=0
    corresponde a Levi-Civita. A fronteira é estratificada, não suave.
    """
    probabilities:tuple[F,...]
    def __post_init__(self):
        p=tuple(Q(x) for x in self.probabilities)
        if len(p)<2 or any(x<=0 for x in p) or sum(p)!=1:
            raise ValueError('Exige simplex interior estrito')
        object.__setattr__(self,'probabilities',p)

    @property
    def dimension(self):return len(self.probabilities)-1

    def metric(self,i,j):
        p=self.probabilities;n=self.dimension
        if not 0<=i<n or not 0<=j<n:raise IndexError('Coordenada inválida')
        return (1/p[i] if i==j else F(0))+1/p[-1]

    def metric_inverse(self,i,j):
        p=self.probabilities;n=self.dimension
        if not 0<=i<n or not 0<=j<n:raise IndexError('Coordenada inválida')
        return (p[i] if i==j else F(0))-p[i]*p[j]

    def chentsov(self,i,j,k):
        n=self.dimension;p=self.probabilities
        if any(not 0<=t<n for t in (i,j,k)):raise IndexError('Coordenada inválida')
        return (1/p[i]**2 if i==j==k else F(0))-1/p[-1]**2

    def alpha_lower(self,i,j,k,alpha=0):
        return -(1+Q(alpha))*self.chentsov(i,j,k)/2

    def alpha_upper(self,i,j,k,alpha=0):
        return sum((self.metric_inverse(k,t)*self.alpha_lower(i,j,t,alpha)
                    for t in range(self.dimension)),F(0))

    def m_geodesic(self,target:Sequence[F],t:F):
        t=Q(t);q=tuple(Q(v) for v in target)
        if len(q)!=len(self.probabilities) or any(v<=0 for v in q) or sum(q)!=1:
            raise ValueError('Geodésica mistura requer extremos no interior')
        if not 0<=t<=1:raise ValueError('Parâmetro deve estar em [0,1]')
        return tuple((1-t)*a+t*b for a,b in zip(self.probabilities,q))


@dataclass(frozen=True)
class RationalRotationSO2:
    """Representação matricial SO(2) exata usando t=tan(θ/2) racional.

    cosθ=(1−t²)/(1+t²), senθ=2t/(1+t²). O ponto θ=π pode
    ser representado explicitamente por (cos,sen)=(-1,0), sem t.
    """
    cos:F
    sin:F
    def __post_init__(self):
        c,s=Q(self.cos),Q(self.sin)
        if c*c+s*s!=1:raise ValueError('Rotação deve satisfazer c²+s²=1')
        object.__setattr__(self,'cos',c);object.__setattr__(self,'sin',s)

    @classmethod
    def from_stereographic(cls,t:F):
        t=Q(t);return cls((1-t*t)/(1+t*t),2*t/(1+t*t))

    def compose(self,b:'RationalRotationSO2'):
        return RationalRotationSO2(self.cos*b.cos-self.sin*b.sin,
                                   self.sin*b.cos+self.cos*b.sin)

    def power(self,n:int):
        if not isinstance(n,int):raise TypeError('Expoente inteiro necessário')
        if n<0:return self.inverse().power(-n)
        r=RationalRotationSO2(1,0);a=self
        while n:
            if n&1:r=r.compose(a)
            a=a.compose(a);n>>=1
        return r

    def inverse(self):return RationalRotationSO2(self.cos,-self.sin)

    def apply(self,v:Vector)->Vector:
        if v.dim!=2:raise ValueError('Rotação age em Q²')
        x,y=v.entries
        return Vector((self.cos*x-self.sin*y,self.sin*x+self.cos*y))

    def rope(self,embeddings:Sequence[Vector],positions:Sequence[int])->tuple[Vector,...]:
        if len(embeddings)!=len(positions):raise ValueError('Tamanhos incompatíveis')
        if any(v.dim!=2 for v in embeddings):raise ValueError('Apenas um plano bidimensional')
        return tuple(self.power(k).apply(v) for v,k in zip(embeddings,positions))


class IntervalSoftmax:
    """Softmax em intervalo racional com Jacobiano intervalar certificado.

    Para logits z_i∈I_i, computa w_i=e^(z_i/τ)/Σ_j e^(z_j/τ)
    com extensão inclusiva de exp. O jacobiano é
    ∂w_i/∂z_j=(δ_ij w_i−w_i w_j)/τ.
    A dimensão é finita; a largura de intervalo pode crescer por dependência.
    """
    def __init__(self,logits:Sequence[I],temperature:F=1,terms:int=24):
        self.logits=tuple(logits);self.tau=Q(temperature);self.terms=terms
        if not self.logits or self.tau<=0 or terms<4:
            raise ValueError('Logits, temperatura e precisão inválidos')
        if any(not isinstance(x,I) for x in self.logits):raise TypeError('Logits devem ser intervalos')

    def weights(self)->tuple[I,...]:
        exps=tuple(I(interval_exp_global(z.lo/self.tau,self.terms).lo,
                      interval_exp_global(z.hi/self.tau,self.terms).hi) for z in self.logits)
        denom=sum(exps,I(0,0))
        return tuple(I(max(F(0),(v/denom).lo),min(F(1),(v/denom).hi)) for v in exps)

    def jacobian(self):
        ws=self.weights()
        return tuple(tuple((ws[i]*(I(1,1)-ws[j]) if i==j else -ws[i]*ws[j])/self.tau
                           for j in range(len(ws))) for i in range(len(ws)))


@dataclass(frozen=True)
class DampedHarmonicMidpoint:
    """Passo dissipativo com identidade exata ΔE=−hγ p_mid².

    Modelo q'=p, p'=−ω² q−γp, ω²>0, γ≥0. Método do ponto
    médio implícito linear preserva estabilidade energética para h≥0;
    não é uma discretização de geometria de contato universal.
    """
    stiffness:F
    friction:F
    def __post_init__(self):
        object.__setattr__(self,'stiffness',Q(self.stiffness))
        object.__setattr__(self,'friction',Q(self.friction))
        if self.stiffness<=0 or self.friction<0:raise ValueError('Modelo exige rigidez positiva e atrito não negativo')

    def energy(self,z:Vector)->F:
        if z.dim!=2:raise ValueError('Fase bidimensional')
        q,p=z.entries
        return (self.stiffness*q*q+p*p)/2

    def step(self,z:Vector,h:F)->Vector:
        if z.dim!=2:raise ValueError('Fase bidimensional')
        h=Q(h)
        if h<0:raise ValueError('Passo adiante necessário para dissipação')
        q,p=z.entries;k=self.stiffness;g=self.friction
        # q1−h p1/2 = q0+h p0/2
        # (h k/2)q1+(1+h g/2)p1 = p0−h k q0/2−h g p0/2
        a=1;b=-h/2;c=h*k/2;d=1+h*g/2
        det=a*d-b*c
        if det==0:raise ArithmeticError('Sistema linear singular')
        r=q+h*p/2;s=p-h*k*q/2-h*g*p/2
        out=Vector(((d*r-b*s)/det,(-c*r+a*s)/det))
        # Identity verified independently: energy cannot spuriously increase.
        pmid=(p+out.entries[1])/2
        if self.energy(out)-self.energy(z)!=-h*g*pmid*pmid:
            raise ArithmeticError('Falha de identidade de dissipação')
        return out


class SparseBlockKernel:
    """Decomposição exata do núcleo de uma matriz esparsa por componentes.

    Cada linha induz arestas entre as colunas onde é não nula. Componentes
    desconectadas são resolvidas isoladamente por eliminação racional. Em
    problemas esparsos favoráveis, reduz custos; no pior caso o grafo é denso.
    """
    def __init__(self,ncols:int,max_nnz:int=100_000):
        if ncols<1 or max_nnz<1:raise ValueError('Limites inválidos')
        self.n=ncols;self.rows=[];self.cap=max_nnz;self.nnz=0

    def append(self,row:dict[int,F]):
        if any(type(i)!=int or not 0<=i<self.n for i in row):raise ValueError('Índice inválido')
        data={i:Q(v) for i,v in row.items() if Q(v)}
        if self.nnz+len(data)>self.cap:raise MemoryError('Orçamento de memória excedido')
        self.rows.append(data);self.nnz+=len(data)

    def components(self):
        parent=list(range(self.n))
        def root(i):
            while parent[i]!=i:
                parent[i]=parent[parent[i]];i=parent[i]
            return i
        for row in self.rows:
            inds=list(row)
            for i in inds[1:]:parent[root(i)]=root(inds[0])
        blocks=defaultdict(list)
        for i in range(self.n):blocks[root(i)].append(i)
        return tuple(tuple(v) for _,v in sorted(blocks.items(),key=lambda kv:min(kv[1])))

    def basis(self,max_vectors=1000):
        components=self.components();result=[]
        for block in components:
            rows=[[row.get(j,F(0)) for j in block] for row in self.rows if any(j in row for j in block)]
            if not rows:
                k=[tuple(F(int(i==block[0])) for i in range(self.n))]
            else:
                basis=primitive_integer_kernel(rows)
                k=[tuple(next((vec[t] for t,j in enumerate(block) if j==i),F(0))
                         for i in range(self.n)) for vec in basis]
            result.extend(k)
            if len(result)>max_vectors:raise RuntimeError('Dimensão do núcleo excede limite')
        for v in result:
            if any(sum((a*v[j] for j,a in row.items()),F(0))!=0 for row in self.rows):
                raise ArithmeticError('Vetor do núcleo não verificado')
        return tuple(result)


@dataclass(frozen=True)
class ExactQuadraticMidpoint:
    """Mapa simplético afim para H polinomial quadrático, até termos q·p.

    Escreva H(z)=1/2 zᵀSz+bᵀz+c. Seja A=JS. O ponto médio satisfaz
    (I−hA/2)z₁=(I+hA/2)z₀+hJb. Como S=Sᵀ, o mapa linear de Cayley
    preserva J, e o Hamiltoniano quadrático é conservado exatamente.
    A matriz de passo singular causa exceção, não fallback aproximado.
    """
    energy:P
    pairs:int
    step_size:F

    def __post_init__(self):
        from ml_mathlib import SymplecticSpace
        n=2*self.pairs
        if self.pairs<1 or self.energy.dimension!=n or self.step_size==0:
            raise ValueError('Dimensão, grau ou passo inválido')
        if any(sum(ex)>2 for ex,_ in self.energy.terms):
            raise ValueError('A energia precisa ser quadrática')
        object.__setattr__(self,'step_size',Q(self.step_size))
        space=SymplecticSpace(self.pairs)
        S=Matrix(tuple(tuple(self.energy.diff(i).diff(j).evaluate((0,)*n)
             for j in range(n)) for i in range(n)))
        b=Vector(tuple(self.energy.diff(i).evaluate((0,)*n) for i in range(n)))
        A=space.J@S;h=self.step_size
        lhs=Matrix.identity(n)-A.scale(h/2)
        rhs=Matrix.identity(n)+A.scale(h/2)
        try:inv=lhs.inverse()
        except ValueError as exc:raise ValueError('Passo singular: mapa implícito não definido') from exc
        M=inv@rhs;t=inv@(space.J@b).scale(h)
        if not space.is_symplectic(M):raise ArithmeticError('Mapa não simplético')
        object.__setattr__(self,'linear',M)
        object.__setattr__(self,'translation',t)
        object.__setattr__(self,'phase',space)

    def step(self,z:Vector)->Vector:
        if z.dim!=self.phase.dimension:raise ValueError('Estado inválido')
        out=self.linear@z+self.translation
        if self.energy.evaluate(z.entries)!=self.energy.evaluate(out.entries):
            raise ArithmeticError('Energia não preservada pelo ponto médio quadrático')
        return out


@dataclass(frozen=True)
class OrnsteinUhlenbeckMoments:
    """Intervalos racionais da média/variância do processo Ornstein–Uhlenbeck.

    dX_t = −λ X_t dt + σ dW_t, λ>=0. Para variância inicial v0>=0:
      E[X_t]=m0 exp(−λt)
      Var[X_t]=v0 exp(−2λt)+σ²(1−exp(−2λt))/(2λ), λ>0.
    O processo estocástico é o OU clássico; esta classe calcula momentos,
    não prova a construção geral do Wiener nem integra todas as SDEs.
    """
    decay:F
    noise_variance:F
    initial_mean:F
    initial_variance:F

    def __post_init__(self):
        for name in ('decay','noise_variance','initial_mean','initial_variance'):
            object.__setattr__(self,name,Q(getattr(self,name)))
        if self.decay<0 or self.noise_variance<0 or self.initial_variance<0:
            raise ValueError('Parâmetros físicos inválidos')

    def at_time(self,t:F,terms:int=28)->tuple[I,I]:
        t=Q(t)
        if t<0:raise ValueError('Tempo não negativo requerido')
        if self.decay==0:
            return I(self.initial_mean,self.initial_mean),I(self.initial_variance+self.noise_variance*t,
                                                          self.initial_variance+self.noise_variance*t)
        c=interval_exp_global(-self.decay*t,terms)
        vfactor=interval_exp_global(-2*self.decay*t,terms)
        mean=I(self.initial_mean,self.initial_mean)*c
        variance=I(self.initial_variance,self.initial_variance)*vfactor + \
                 I(self.noise_variance/(2*self.decay),self.noise_variance/(2*self.decay))*(I(1,1)-vfactor)
        return mean,variance
