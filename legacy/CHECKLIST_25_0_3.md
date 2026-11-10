# Checklist técnico verificável — 25 frentes, MLib 0.3

**Interpretação:** `[x]` significa **solução funcional no domínio finito ou local declarado**, não uma solução geral de todas as teorias matemáticas envolvidas; `[~]` significa **melhora implementada, mas a limitação geral permanece**. As frentes A1–A3 são repetições parciais do inventário 1–22 e aparecem separadamente a pedido. A versão 0.3 NÃO esgota os 25 problemas no sentido matemático irrestrito.

| Item | Limitação | Estado | Implementação verificável | Restrição residual |
|---|---|:---:|---|---|
| A1 | Polinômios apenas em Q[x] | [~] | `QuadraticAlgebraicFunction`, `AnalyticExpression`, `RationalFunction` | Não há corpo diferencial geral nem decidibilidade simbólica transcendental |
| A2 | Float não certificado em π, exp, log, sin, cos | [~] | `interval_*_global`, `interval_sqrt`, `AnalyticExpression.enclose`, `CertifiedFisherSphere` | RoPE legado usa float; precisão pode se degradar em intervalos largos |
| A3 | Explosão da base de monômios | [~] | `SparseExactKernel`, `pruned_monomials`, `primitive_integer_kernel` | Preenchimento esparso e tamanho do núcleo têm pior caso exponencial |
| 1 | Inchaço de bits em Q | [~] | `modular_determinant` (CRT + parada certificada), eliminação inteira primitiva | Não substitui RREF global; CRT para soluções ainda não é geral |
| 2 | Q(α) ausente | [~] | `NumberField`, `AlgebraicElement`, `irreducible_mod_prime` | Certificação por redução módulo primo é suficiente, não universal; sem SVD |
| 3 | Sylvester O(d⁴) | [x] | `InnerProductSpace` com LDLᵀ racional O(d³) | SPD em Q finito, não métricas variáveis gerais |
| 4 | Sem tensores/exterior | [~] | `MixedTensor` com produto e contração, `DifferentialForm` da 0.2 | Sem toda a teoria de tensores em fibrados, cohomologia, integrais |
| 5 | Sem corpo Q(x) | [~] | `RationalFunction` e radicais algébricos, derivadas racionais | Falta MDC multivariado e normalização canônica geral |
| 6 | Apenas variedades afins | [~] | `StereographicSphere2`, `RationalAtlas`, `RationalRiemannianMetric` | Atlas global arbitrário e verificação formal de topologia/cobertura ausentes |
| 7 | Sem d, k-formas | [~] | `DifferentialForm.wedge`, `.exterior_derivative`, d²=0 testado | Coeficientes racionais gerais e cohomologia sem cobertura |
| 8 | Sem bases de Gröbner | [~] | Buchberger + `reduced_groebner_basis`, redução e pertinência ideal | Não há técnicas F4/F5, eliminação avançada nem limites escaláveis |
| 9 | Apenas simplex discreto | [~] | `UniformIntervalMeasure`, `GaussianNaturalExponentialFamily`, Gauss v0.2 | Não há σ-álgebras / medida de Lebesgue / famílias genéricas |
| 10 | Singularidade da métrica Fisher na borda | [~] | `FisherSphere`, `CertifiedFisherSphere.distance_interval` inclusive suportes disjuntos | Não existe variedade riemanniana regular na borda: estratificação é indispensável |
| 11 | Sem α-conexões/geodésicas | [~] | `GaussianFamily.christoffel`, `CertifiedGaussianFisher.distance_interval` | Famílias arbitrárias e integração numérica de geodésicas não cobertas |
| 12 | Hamiltonianos não separáveis | [~] | `ImplicitMidpoint`, `MidpointContractionCertificate` prova raiz local por Banach | Para não linear geral exige caixa contrativa; não resolve todos os passos |
| 13 | Ordem 1 apenas | [x] | Verlet 2ª e `ExactYoshida4` com coeficientes cúbicos e condições algébricas de 4ª | Domínio: separável polinomial; não é integrador universal de ordem 4 |
| 14 | Sem dissipação/contato | [~] | `ContactFlow` com campo e identidade de dissipação exatos | Não há integrador certificado nem sistema termodinâmico completo |
| 15 | Roteador sem AD | [~] | `SymbolicAttention`, `SymbolicMultiHeadAttention`, `AnalyticExpression` | AD formal em modelos pequenos, sem treino completo/generalidade |
| 16 | Apenas SO(2) | [~] | `SO3`, `SE3`, `SU2`, `RationalLieAlgebra` com Jacobi validado | Representações racionais, não grupos de Lie reais arbitrários |
| 17 | Sem máscara causal/multi-head | [x] | `CausalMultiHeadAttention`, `SymbolicMultiHeadAttention` com gradientes | Modelo de referência, não atenção otimizada / flash / KV cache |
| 18 | Invariantes H^k parasitas | [x] | `algebraic_independence_rank` e `independent_invariants` | Posto jacobiano genérico, em característica zero e ansatz finito |
| 19 | Kernel denso e ansatz explosivo | [~] | `SparseExactKernel` incremental e poda por grau/paridade/pesos | Sem garantias assintóticas globais ou computação F4/F5 |
| 20 | Noether hardcoded | [x] | `noether_charge` para campos vetoriais polinomiais em dimensão n | Não cobre ações suaves transcendentes arbitrárias |
| 21 | Casimir ausente | [~] | `PolynomialPoissonTensor`, `discover_casimirs` certificado | Descoberta somente em grau limitado, sem algoritmo geral global |
| 22 | Sem exportação Lean | [~] | `export_lean_conservation`, JSON reexecutável, arquivo `.lean` exportado | **Lean NÃO executado**; Poisson/MvPolynomial não formalizados em Mathlib |

## Contagem

- **5/25** atendidos **apenas no domínio matemático declarado** (`3`, `13`, `17`, `18`, `20`).
- **20/25** ainda parciais, embora tenham sido implementadas correções/reduções verificáveis.
- **0/25** ignorados.
- **70 testes** locais aprovados: 13 base + 24 v0.2 + 33 v0.3.
- **0 certificados Lean formalmente compilados** nesta execução (executáveis `lean`/`lake` ausentes).

### Evidências reproduzíveis

```bash
python ml_mathlib.py --test
python -m unittest discover -p 'test_ml_mathlib*.py' -v
python replay_certificate.py examples/central_force_conservation.json
```

Os testes 0.3 incluem contraexemplos para entrada fora do domínio, certificados insuficientes de CRT, primos que não certificam irredutibilidade, Hamiltonianos que não satisfazem contratividade, alterações no JSON e violação de Jacobi em álgebras de dimensão 4.

**Resposta à pergunta "esgotou os 25 problemas?": NÃO.** A amplitude originalmente solicitada equivale à construção de um novo assistente de provas e um CAS geral; partes essenciais permanecem abertas e não devem ser marcadas como resolvidas sem uma especificação formal completa, infraestrutura de prova e validação extensa.
