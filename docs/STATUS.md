# Inventário formal LeanML

A estrutura tem os 22 módulos pedidos. A tabela descreve o conteúdo matemático
implementado; o build e os testes de axiomas devem passar para uma revisão ser
considerada verificada. As limitações abaixo fazem parte do contrato público.

| Módulo | Resultado implementado | Limite / trabalho restante |
|---|---|---|
| `Information/Shannon` | Probabilidades finitas com zeros, ponte de `ProbabilityMeasure`, não negatividade, limite `log N` por Jensen | Entropia diferencial e unicidade da maximização |
| `Information/Divergence` | KL estendida de medidas, igualdade de Gibbs, definição de Jensen-Shannon | Expansão discreta e caracterizações adicionais de JS |
| `Information/DataProcessing` | Contração KL por mapas mensuráveis e kernels de Markov, via Mathlib | Informação mútua e formulação explícita da cadeia X→Y→Z |
| `Optimization/Smoothness` | Gradiente genuíno, suavidade, forte convexidade, lema da descida e passo 1/L | Domínios convexos restritos |
| `Optimization/GradientDescent` | Passo geral admissível, potencial de distância, taxa convexa O(1/k), taxa linear em valor para forte convexidade | Taxa linear em distância |
| `Optimization/Nesterov` | Operador de extrapolação e passo acelerado; redução a GD sem momentum | Prova da taxa O(1/k²) para uma sequência de parâmetros especificada |
| `Optimization/Stochastic` | Operador SGD e condições de passos Robbins-Monro | Convergência estocástica, filtração e hipóteses de ruído |
| `Optimization/Backpropagation` | Nós diferenciáveis tipados, composição, ramificação, pullback e acumulação reversa nas ramificações | Algoritmo reverso completo com compartilhamento de nós e scheduler de DAG |
| `LearningTheory/Loss` | Riscos, excesso de risco do ERM e controle uniforme em classes finitas por união de eventos | Leis amostrais IID e existência mensurável de minimizadores |
| `LearningTheory/Concentration` | Hoeffding subgaussiana, versão limitada centrada e cota da média amostral, via Mathlib | McDiarmid e especializações Markov/Chebyshev |
| `LearningTheory/PAC` | Especificação explícita de garantia PAC por lei amostral | Produto IID, quantificação distribution-free e equivalência PAC ↔ VC finita |
| `LearningTheory/VCDimension` | Classes finitas via Mathlib, shattering de classes arbitrárias e dimensão estendida em ℕ∞ | Ponte entre as representações finita e geral |
| `LearningTheory/SauerShelah` | Cota combinatória binomial em domínio finito, via Mathlib | Cota exponencial `(eN/d)^d` e crescimento em amostras de domínio infinito |
| `LearningTheory/Rademacher` | Correlação assinada e complexidade empírica para classe finita | Simetrização e cotas de generalização |
| `Representation/Activation` | ReLU, seus ramos e continuidade; sigmoide do Mathlib | Propriedades de não polinomialidade e derivadas adicionais |
| `Representation/MLP` | Camadas densas, redes rasas e composição feedforward com dimensões nos tipos; continuidade | Integração com DAGs e treinamento |
| `Representation/Cybenko` | Propriedade precisa de aproximação uniforme e restrição de domínio | Prova de Cybenko para sigmoides contínuas em compactos |
| `Representation/Convolution` | Convolução em grupos abelianos finitos e equivariância por translação | Grupos infinitos e condições de integrabilidade |
| `Representation/Attention` | Softmax positiva e normalizada, atenção por produto escalar e equivariância de self-attention | Máscaras causais, padding e codificações posicionais modificam as simetrias |
| `Generative/OptimalTransport` | Acoplamentos finitos, acoplamento independente, custo e infimum de Kantorovich | Monge, dualidade e axiomas métricos de Wasserstein |
| `Generative/ELBO` | ELBO finita com joint positivo, cota por Jensen; identidade algébrica do gap | Densidades gerais e identificação integral do gap KL |
| `Generative/SDEConvergence` | Interfaces de coeficientes, convergência fraca de leis e reversão de caminhos | SDE efetiva, solução fraca/forte e reversão temporal de Anderson |

## Hipóteses que não podem ser omitidas

- A suavidade relaciona o gradiente à função por `HasGradientAt`, além da constante Lipschitz.
- GD exige passo positivo e `η L ≤ 1`; a taxa explícita usa `k > 0`.
- A taxa linear implementada é para o valor objetivo, não para a norma da distância.
- KL usa valores estendidos para representar corretamente casos singulares e infinitos.
- Risco populacional é uma integral de Bochner; sua interpretação estatística exige integrabilidade.
- O Hoeffding importado expressa independência e limitações quase certamente.
- Softmax usa somas não vazias nos resultados de normalização e positividade.
- Equivariança da atenção refere-se a atenção sem máscara, com projeções compartilhadas.
- A prova finita de ELBO requer massas variacionais e joint estritamente positivos.
- A definição de aproximação uniforme não é uma demonstração de densidade.

## Continuação

A prioridade é ampliar resultados completos sem introduzir buracos: integrar a prova de generalização finita à lei amostral IID, ampliar a
acumulação reversa a um scheduler de DAG com compartilhamento e só então estender a classes infinitas, aceleração, aproximação universal e difusões.
Este repositório não alega prioridade histórica nem cobertura completa da teoria de ML.
