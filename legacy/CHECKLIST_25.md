# CHECKLIST AUDITÁVEL — 25 limitações da ML-MATHLIB

**Legenda:** [x] = atendida no domínio anunciado; [~] = implementação parcial/limitada; [ ] = não resolvida. As três limitações iniciais se sobrepõem a itens da lista de 22, mas são auditadas separadamente como solicitado.

| Nº | Limitação solicitada | Situação | Evidência e restrição residual |
|---:|---|:---:|---|
| A1 | Polinômios não admitem frações/transcendentes | [~] | `RationalFunction`, diferenciação exata; raízes gerais e funções transcendentais no corpo diferencial faltam |
| A2 | Float em π, exp, log, sen e cos | [~] | `RationalInterval`, `interval_pi/exp/log/sin/cos` fornecem bounds para argumentos racionais em domínios restritos; não integrados a RoPE/Fisher |
| A3 | Explosão combinatória do grau | [~] | Enumeração limitada e com paridade, cota `max_terms`; ainda existe RREF denso e não há escalabilidade comprovada |
| 1 | Inchaço de bits de Fractions | [~] | Bareiss no determinante e utilitário independente; RREF ainda não usa CRT/fração-livre |
| 2 | Ausência de extensões Q(α) | [~] | `QuadraticNumber` suporta Q(√d) com d racional não quadrado positivo; não implementa extensão irrestrita/SVD |
| 3 | Critério de Sylvester O(d⁴) | [x] | `InnerProductSpace` passou a usar LDLᵀ em O(d³), exata, para SPD |
| 4 | Sem álgebra tensorial e exterior | [~] | `CovariantTensor`, produto tensorial, avaliação multilinear; `DifferentialForm` com ∧ e d, mas não tensores mistos e curvatura geral |
| 5 | Sem corpo de frações Q(x) | [~] | `RationalFunction` com +, ×, /, composição, derivada e avaliação; MDC univariado, falta MDC multivariado canônico |
| 6 | Variedades apenas afins | [~] | `RationalChart` e `RationalAtlas` locais com inversas algébricas; falta prova de domínios abertos, cobertura e topologia global |
| 7 | Sem k-formas ou d de Cartan | [~] | `DifferentialForm` exterior polinomial, wedge e d²=0 testado; sem formas gerais com coeficientes racionais ou integração de formas |
| 8 | Multiplicação polinomial e Gröbner | [~] | Multiplicação esparsa acumulativa; Buchberger e teste de pertinência para exemplos finitos, sem otimizações F4/F5 |
| 9 | Apenas simplex discreto | [~] | `GaussianFamily` fornece métricas e cumulantes analíticos de N(μ,v); não formaliza medidas contínuas gerais |
| 10 | Fisher singular na fronteira | [~] | `FisherSphere` usa coordenadas √p com fator métrico correto 4; borda é estratificada, não uma carta regular |
| 11 | Sem α-conexões/geodésicas | [~] | Christoffel Levi-Civita/α e Chentsov na família Gaussiana; outras famílias e geodésicas gerais faltam |
| 12 | Hamiltonianos não separáveis | [~] | `ImplicitMidpoint` exato para quadráticos, Newton aproximado para grau maior; sem prova de convergência não linear |
| 13 | Integrador de ordem 1 somente | [~] | `VelocityVerlet` de ordem 2 e `Yoshida4` com coeficientes racionais aproximados; ordem 4 formal não certificada em Q |
| 14 | Falta mecânica dissipativa/de contato | [~] | `ContactFlow` implementa campo do contato canônico de H polinomial; integrações e hipóteses termodinâmicas faltam |
| 15 | Falta autodiff através do roteador | [~] | `SymbolicExpr` e `DifferentiableRouter` propagam derivadas formais; sem treinamento end-to-end integrado |
| 16 | Falta SO(3)/SE(3)/SU(2) | [~] | `SO3`, `SE3` exatos na representação racional por Cayley; SU(2) e rotações por π não implementadas |
| 17 | Atenção sem causalidade/multi-head | [~] | `CausalMultiHeadAttention` funcional com projeções e máscara; sem treinamento/gradiente de matrizes |
| 18 | Invariantes parasitas Hᵏ | [x] | `algebraic_independence_rank` usa Jacobiano simbólico sobre Q(x), e `independent_invariants` elimina dependência algébrica genérica |
| 19 | Ansatz monomial explosivo | [~] | `pruned_monomials` produz sequencialmente grau ≤d, paridade, pesos e limite; kernel ainda usa eliminação densa |
| 20 | Cotangente só hardcoded em SO(2) | [x] | `noether_charge(ξ)` constrói P_X=Σp_i ξ_i(q) para qualquer gerador polinomial em n variáveis |
| 21 | Sem Casimirs | [~] | `PolynomialPoissonTensor` valida Jacobi e certifica candidatos Casimir; motor geral de busca não está integrado |
| 22 | Sem exportação Lean 4 | [~] | `export_lean_conservation` produz teorema de identidade expandida com `by ring`; não define Poisson formal no Lean, e sem teste `lake env lean` |

**Balanço:** 3/25 atendidas integralmente **no escopo explícito**, 22/25 parcialmente tratadas, 0 totalmente ignoradas. **A tarefa de esgotar as 25 limitações não está concluída**: cobertura funcional pontual não equivale à solução axiomática e computacional geral exigida. Os três itens marcados [x] também têm escopo especificado e não representam completude da biblioteca como um todo.
