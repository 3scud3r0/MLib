# ML-MATHLIB 0.4 — extensão algébrica e geométrica com verificação exata

**Estado:** execução em Python puro, sem dependências de tempo de execução. **104 testes** locais aprovados (13 do núcleo, 24 da v0.2, 33 da v0.3 e 34 da v0.4). Não é Mathlib em Lean e não constitui uma teoria matemática universal completa.

## Executar

```bash
python ml_mathlib.py --test-all
python ml_mathlib.py --demo
python -m unittest discover -p 'test_ml_mathlib*.py' -v
python replay_certificate.py examples/central_force_conservation.json
```

O arquivo `ml_mathlib.py` mantém as APIs de 0.1–0.3, incluindo importação preguiçosa das extensões. A 0.4 acrescenta `ml_mathlib_verified.py` e `test_ml_mathlib_verified.py`.

## Avanços da versão 0.4

### Aritmética algébrica e Gröbner

1. **MDC multivariado exato** `multivariate_gcd(P,Q)`: método recursivo de Gauss/Euclides em `Frac(Q[x_1,…,x_(n-1)])[x_n]`, com extração de conteúdo e verificação por divisões polinomiais. Por padrão há limite de grau de entrada 16; coeficientes e número de termos podem crescer muito. `ReducedRational` normaliza frações de polinômios multivariados e preserva a semântica de elementos do corpo racional — zeros de fatores cancelados NÃO são singularidades da função reduzida. Para preservar uma restrição de domínio da expressão original é necessário um objeto separado de domínio.
2. **Testemunho de ideal** `groebner_witness`: acompanha a combinação de geradores em Buchberger e, quando positivo, entrega polinômios `h_i` com igualdade exata `f = Σ h_i g_i`. `IdealMembershipCertificate.verify()` recalcula a igualdade diretamente; ao exceder orçamento, produz exceção, nunca certificado falso. O resultado negativo exige conclusão de todos os pares S.
3. **Kernel exato por blocos** `SparseBlockKernel`: constrói o grafo de acoplamento das colunas e elimina cada componente separadamente. Demonstração com 1.820 colunas esparsas. Não elimina a complexidade combinatória de pior caso.

### Geometria, informação e funções analíticas

4. **Formas diferenciais racionais** `RationalDifferentialForm`: produto exterior, derivada exterior de Cartan e pullback racional entre espaços de dimensões possivelmente diferentes. `rational_substitution` substitui mapas `Q^m ⇢ Q^n`. Teste da identidade natural `F*(dω) = d(F*ω)` e de `d²ω=0`.
5. **Conexões-α no simplex** `CategoricalInformationGeometry`: métrica Fisher, inversa exata, tensor de Amari–Chentsov, Christoffel de primeira e segunda espécies e geodésicas de mistura. A fórmula testada é `Γ^(α)_(ij,k) = −(1+α) T_(ijk)/2` em coordenadas mistura (incluindo conexão `α=−1` plana). Exige probabilidades estritamente positivas; a fronteira é estratificada, não uma variedade regular.
6. **Momentos contínuos exatos** `GaussianPolynomialLaw` e `GaussianMixturePolynomialLaw`: momentos de normais univariadas e misturas finitas por recorrência de integração por partes, sem quadratura float.
7. **RoPE exato em um plano** `RationalRotationSO2`: parametrização racional estereográfica de SO(2), ação ortogonal certificada, lei de grupo, potência posicional e identidade de atenção relativa. Não representa exatamente ângulos arbitrários com seno/cosseno transcendentes; a implementação legado float permanece para esse caso.
8. **Softmax intervalar** `IntervalSoftmax`: exponenciais envolvidas em limites racionais e Jacobiano formal `∂w_i/∂z_j = w_i(δij−w_j)/τ`, propagado por intervalos. Os intervalos são rigorosos, mas podem ser largos por correlação.

### Dinâmica conservativa, dissipativa e estocástica

9. **Ponto médio quadrático geral** `ExactQuadraticMidpoint`: aceita termos mistos coordenada–momento. Para `H(z)=zᵀSz/2+bᵀz+c`, computa exatamente a transformação de Cayley `(I−hJS/2)⁻¹(I+hJS/2)` e checa `MᵀJM=J` e `H(z')=H(z)`. Rejeita passos singulares e graus maiores que 2. Para H não linear, continua disponível o certificado local de Banach da v0.3.
10. **Dissipação exata** `DampedHarmonicMidpoint`: integra `q'=p`, `p'=−kq−γp` com identidade racional exata `E(z')−E(z) = −hγ p_mid² ≤ 0` para `k>0,γ≥0,h≥0`. Isto não é um integrador de contato genérico.
11. **Processo OU** `OrnsteinUhlenbeckMoments`: fornece intervalos racionais certificados para média e variância de Ornstein–Uhlenbeck com tempo e parâmetros racionais. Não é um solver universal de EDE.

## Código exemplificado

```python
from fractions import Fraction as Q
from ml_mathlib import Polynomial, Vector
from ml_mathlib_verified import (
    multivariate_gcd, groebner_witness, ExactQuadraticMidpoint,
    GaussianPolynomialLaw, RationalRotationSO2,
)

x, y = Polynomial.variable(2, 0), Polynomial.variable(2, 1)
g = multivariate_gcd((x+y)*(x+1), (x+y)*(y+2))
assert g == x+y

proof = groebner_witness(x*x-1, (x*y-1, x-y))
assert proof is not None and proof.verify()

H = x*y + (x*x + y*y)/2
phi = ExactQuadraticMidpoint(H, pairs=1, step_size=Q(1, 10))
z = Vector((1, 2))
assert H.evaluate(z.entries) == H.evaluate(phi.step(z).entries)

normal = GaussianPolynomialLaw(mean=Q(1, 3), variance=Q(2))
t = Polynomial.variable(1, 0)
assert normal.expectation((t-Q(1, 3))**4) == 12

R = RationalRotationSO2.from_stereographic(Q(1, 5))
assert R.power(3).apply(z).dot(R.power(3).apply(z)) == z.dot(z)
```

## Escopo formal e limites

- Toda igualdade racional/polinomial da nova camada é verificada sobre `Fraction` ou corpos algébricos previamente certificados. Os resultados de funções transcendentais são intervalos racionais, não identidades simbólicas universais.
- MDC multivariado exato **não** implica custo eficiente em entradas grandes; Gröbner pode ser duplamente exponencial no pior caso. Orçamentos interrompem uma computação sem transformá-la em conclusão matemática.
- A formulação ampla de teoria da medida requer σ-álgebras, mensurabilidade, convergência de medidas, integração de Lebesgue e espaços funcionais — ainda não construída.
- Há exemplos locais de atlas e curvatura, mas não um verificador de cobertura topológica de variedades arbitrárias.
- O exportador Lean gera uma obrigação textual; não foi executado `lake env lean`, pois Lean/lake não estão instalados no ambiente. **Nenhum item é considerado provado pelo kernel Lean**.
- Os 25 itens originais não estão todos esgotados. Veja `CHECKLIST_25_0_4.md` para o status individual, critérios e limitação residual.

## Referência de execução

Os **104 testes** passaram com Python 3.13.5 no ambiente de desenvolvimento. Testes adicionais de robustez compararam 390 casos sintéticos de MDC com SymPy (utilizado somente como oráculo de testes, **não** dependência do projeto) e validaram 120 testemunhos de pertencimento a ideais; esses ensaios adicionais não fazem parte dos 104 testes normativos da suíte e não são uma prova de completude.
