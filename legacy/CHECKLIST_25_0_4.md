# Checklist auditável — ML-MATHLIB 0.4

**Legenda:** `✅` = implementação exata e testada dentro do domínio matemático explicitamente declarado (não significa solução irrestrita do campo); `◐` = implementação parcial, requisito geral não cumprido. **Não marque um resultado como verde só por ter um nome de classe.** O pedido tem 25 entradas porque as três primeiras sobrepõem questões da lista de 22.

| Nº | Limitação original | Estado | Correção testada | O que falta para a especificação geral |
|---:|---|:---:|---|---|
| A1 | Corpo Q(x) + transcendentes formais | ◐ | `ReducedRational`, `AnalyticExpression`, radicais | Corpo diferencial geral e equivalência transcendental completa |
| A2 | Floats em ln/exp/trig/RoPE | ◐ | Aritmética intervalar, `RationalRotationSO2`, `IntervalSoftmax` | RoPE arbitrário com ângulos não racionais e todas as operações com enclosure global eficiente |
| A3 | Explosão monomial | ◐ | `SparseBlockKernel`, poda e `SparseExactKernel` | Não existe garantia de evitar complexidade exponencial no caso geral |
| 1 | Bit swell racional | ◐ | Bareiss, determinantes CRT certificados e kernel inteiro | RREF/rank/solvers modularizados escaláveis com reconstrução racional global |
| 2 | Extensões algébricas | ◐ | `NumberField` e `AlgebraicElement` | Teste completo de irredutibilidade, isolação de raízes, ordem e decomposição espectral/SVD exata |
| 3 | Sylvester O(d⁴) | ✅ | LDLᵀ racional em O(d³) | Extensão a operadores infinitos e campos de métricas é fora do contrato finito |
| 4 | Tensores e álgebra exterior | ◐ | `MixedTensor`, `RationalDifferentialForm` | Tensores sobre fibrados gerais e integração/cohomologia |
| 5 | Ausência de Q(x) e MDC multivariado | ✅ | `multivariate_gcd`, `ReducedRational`, quocientes exatos | Correção rigorosa no domínio polinomial finito sob limite de grau; desempenho geral não assegurado |
| 6 | Apenas atlas afins | ◐ | `RationalAtlas`, `StereographicSphere2`, métrica de curvatura | Cobertura e colagem globais, topologia geral e provas de compatibilidade |
| 7 | Sem k-formas e derivada exterior | ✅ | Derivada `d`, wedge e pullback de formas racionais, `d²=0` | Para variedades arbitrárias requer gluing/cobertura global; escopo verde é carta racional local |
| 8 | Falta Gröbner, divisão e testemunho de ideal | ✅ | Buchberger, base reduzida e `groebner_witness` (f=Σhᵢgᵢ) | Completo para Q[x] quando a execução termina no orçamento; algoritmos F4/F5 não incluídos |
| 9 | Sem medida contínua geral | ◐ | Uniforme, Normal e misturas com momentos polinomiais exatos | Teoria abstrata de Lebesgue, integração mensurável geral, convergência e famílias não-paramétricas |
| 10 | Singularidade de Fisher na borda | ◐ | Esfera de Fisher e distância certificada | A fronteira é estratificada, nunca uma variedade riemanniana regular única |
| 11 | Sem conexões α/geodésicas | ◐ | `CategoricalInformationGeometry`, GaussianFamily | Conexões em famílias arbitrárias, geodésicas globais/certificadas fora dos exemplos |
| 12 | H não separável | ◐ | `ExactQuadraticMidpoint`, certificado Banach local para H polinomial | Solver implícito universal, garantia de existência global, H transcendente |
| 13 | Apenas integrador de 1ª ordem | ✅ | Verlet 2ª; `ExactYoshida4` com extensão cúbica exata | Ordem 4 para sistemas separáveis polinomiais; ordem global não garantida para todos os H |
| 14 | Sem dissipação e contato | ◐ | `ContactFlow`, `DampedHarmonicMidpoint` com ΔE exata | Variedades de contato arbitrárias, integradores contato gerais, termodinâmica completa |
| 15 | Roteador não diferenciável | ◐ | Atenção simbólica e `IntervalSoftmax` com derivada certificada | AD/treinamento geral de redes profundas, GPUs, convergência global |
| 16 | Apenas SO(2) | ◐ | `SO3`, `SE3`, `SU2`, SO2 racional e Lie racional | Grupos reais arbitrários, representações gerais e superfícies globais |
| 17 | Falta máscara causal e multi-head | ✅ | `CausalMultiHeadAttention` + `SymbolicMultiHeadAttention` | Exato no modelo funcional de referência; performance industrial fica fora do contrato |
| 18 | Invariantes parasitas | ✅ | Posto jacobiano exato, filtro de independência | Independência algébrica genérica em Q de característica 0, não classificação universal |
| 19 | Busca esparsa explode | ◐ | Poda, `SparseExactKernel`, `SparseBlockKernel` em 1.820 colunas | Preenchimento esparso e dimensão da solução podem ser exponenciais no pior caso |
| 20 | Noether hardcoded | ✅ | `noether_charge` para campos polinomiais arbitrários | Ações suaves não polinomiais e variedades gerais fora do contrato |
| 21 | Sem Casimirs | ◐ | Tensor de Poisson jacobiano, `discover_casimirs` por grau | Algoritmo de classificação global sem limite de grau |
| 22 | Sem compilação comprovada de Lean | ◐ | Exportador de expressões + `replay_certificate` + obrigação `.lean` | **Ainda não compilado pelo kernel Lean**; sem formalização Mathlib completa do Poisson |

## Resultado

- **8/25** atendidos **no domínio delimitado**: `3,5,7,8,13,17,18,20`.
- **17/25** parcialmente atendidos: `A1,A2,A3,1,2,4,6,9,10,11,12,14,15,16,19,21,22`.
- **104/104 testes locais aprovados**: `python ml_mathlib.py --test-all`.
- **390 verificações cruzadas de MDC** contra SymPy e **120 verificações aleatórias de testemunhos de ideal** adicionais, sem dependência de SymPy em tempo de execução.
- **0 certificados verificados pelo Lean 4** nesta execução (`lean` e `lake` ausentes).

**Resposta objetiva:** 25/25 NÃO estão verdes. Os problemas restantes não podem ser declarados resolvidos sem trabalhos científicos adicionais, desenvolvimento de um kernel formal, teoria geral da medida e testes de integração/escala. A produção deste checklist recusa promover resultados parciais a completos.
