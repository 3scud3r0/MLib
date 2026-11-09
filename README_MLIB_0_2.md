# MLib / ML-MATHLIB 0.2

Núcleo matemático escrito em Python puro, baseado em **ℚ** e sem dependências de PyTorch/NumPy/SymPy. Os estratos 0–5 do protótipo 0.1 permanecem em `ml_mathlib.py`, enquanto funcionalidades adicionais ficam em `ml_mathlib_advanced.py`.

> **Rigor:** identidades de polinômios e matrizes racionais são exatas. A integração não linear por Newton, as funções trigonométricas usadas em geometria estatística e o processamento de atenção em ponto flutuante são aproximados. Os intervalos racionais certificados exigem domínios explícitos. O exportador Lean 4 produz uma obrigação de prova de identidade polinomial, mas **não há evidência de verificação no kernel do Lean neste ambiente**.

## Execução

Python 3.10+ (preferencialmente Python 3.11+). Sem dependências externas.

```bash
python ml_mathlib.py --test
python ml_mathlib.py --demo
python -m unittest -v test_ml_mathlib_advanced
```

### Uso direto

```python
from fractions import Fraction as F
from ml_mathlib import Polynomial as P, Matrix
from ml_mathlib_advanced import (
    RationalFunction, groebner_basis, ideal_contains,
    interval_pi, GaussianFamily, SO3, noether_charge
)

x, y = P.variable(2, 0), P.variable(2, 1)
r = RationalFunction(x + y, x*x + 1)  # função racional formal
print(r.diff(0))  # regra do quociente em Q(x,y)
print(ideal_contains(x*x - 1, groebner_basis((x*y - 1, x-y))))
print(interval_pi(12))  # limites racionais certificados
print(GaussianFamily(0, 2).fisher_metric())
print(SO3.about_z(F(1, 3)))
print(noether_charge((-y, x)))
```

## Arquitetura

| Estrato | Objetos novos principais | Contratos matemáticos |
|---|---|---|
| 0 | Bareiss, LDLᵀ, `QuadraticNumber`, `CovariantTensor` | Aritmética racional e álgebra quadrática exatas |
| 1 | `RationalFunction`, Buchberger, `RationalChart`, `DifferentialForm` | Frações formais; Gröbner terminado; diferenciação exterior |
| 2 | `RationalInterval`, `FisherSphere`, `GaussianFamily` | Bounds certificados em subdomínios; Fisher/α-Gauss |
| 3 | `ImplicitMidpoint`, `VelocityVerlet`, `Yoshida4`, `ContactFlow` | Quadráticos exatos; não lineares e Yoshida aproximados |
| 4 | `SymbolicExpr`, `DifferentiableRouter`, `SO3`, `SE3`, `CausalMultiHeadAttention` | Regra da cadeia formal; cabeças e máscara causal funcionais |
| 5 | `independent_invariants`, `noether_charge`, `PolynomialPoissonTensor`, `export_lean_conservation` | Posto genérico exato; certificado de Casimir; exportação textual |

## O que não foi solucionado integralmente

Esta atualização **não** equivale à Mathlib do Lean, nem a um CAS do porte de Singular ou Macaulay2. Faltam, entre outros: corpo de números algébricos de grau arbitrário com certificado de irredutibilidade; MDC polinomial multivariado canônico; sistema de atlas com domínios abertos e cobertura comprovada; teoria da medida de Lebesgue; álgebras de Lie gerais/SU(2); otimização escalável por CRT e técnicas F4/F5; integração simplética não linear com provas de convergência, modelos estocásticos e verificação efetiva pelo kernel Lean. Veja o inventário das 25 frentes para classificação item a item.

## Correções conceituais preservadas

- √p produz a **métrica de Fisher igual a 4 vezes a métrica esférica unitária**, não uma isometria sem fator de escala.
- O simplex na borda é estratificado; o mapeamento não remove a degenerescência como variedade regular do mesmo tipo.
- O gradiente natural é o dual métrico do diferencial, não a derivada covariante.
- Integradores simpléticos preservam a forma simplética; **não** conservam a energia exata genericamente.
- Atenção softmax é solução variacional entrópica, não projeção simplética por definição.
- A pesquisa de invariantes em grau limitado prova identidades dentro do ansatz, não descobre toda a dinâmica possível.

## Testes

O projeto executou **37 testes unitários**: 13 regressões da versão base e 24 testes das extensões, todos aprovados localmente. Esses testes não certificam desempenho em sistemas grandes nem equivalem a provas formais verificadas externamente. Não havia comandos `lean` ou `lake` disponíveis.
