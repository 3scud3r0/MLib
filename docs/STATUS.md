# Inventário formal LeanML

A estrutura preserva os 22 módulos iniciais e acrescenta 18 módulos relacionados a LeanML. A tabela descreve o conteúdo matemático
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
| `LearningTheory/Concentration` | Hoeffding subgaussiana, versão limitada centrada e cota da média amostral, via Mathlib | McDiarmid e especialização Markov; Chebyshev está em Martingales |
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

## Inventário adicional: convenções

**Completo no domínio indicado** significa prova verificada, com todas as hipóteses
no tipo. **Parcial** identifica lemas auxiliares ou um domínio menor: não significa
a demonstração do teorema amplo solicitado. **Pendente** significa que o resultado
não está formalizado nesta revisão. Reutilização de um teorema do Mathlib é atribuída
explicitamente. Os identificadores A01–A43 seguem o anexo; C01–C15 seguem a mensagem.

## Os 15 tópicos da mensagem

| ID | Pedido | Estado e evidência |
|---|---|---|
| C01 | Lipschitz da composição | **Completo** para listas finitas de camadas certificadas; `Robustness/Composition`, `network_lipschitz`. Composição heterogênea por `LipschitzLayer.comp`. |
| C02 | Esfera adversarial | **Completo** para escores Lipschitz, margem estrita contra todos os concorrentes e classificador que seleciona um máximo; `Robustness/Margin`. Não trata empates como decisões invariantes. |
| C03 | Equilíbrio DEQ | **Completo** em espaço normado completo, ativação 1-Lipschitz e norma de W < 1; existência única e convergência de Picard em `Robustness/Equilibrium`, via Banach do Mathlib. |
| C04 | McAllester PAC-Bayes | **Parcial**: mudança de medida variacional e Gibbs para distribuições finitas de suporte positivo em `LearningTheory/PACBayes`. Falta a cota probabilística uniforme nos posteriores sob amostragem IID, perda limitada e prior independente dos dados. |
| C05 | Simetrização | **Pendente**: a complexidade empírica finita existe; falta a prova com amostra fantasma, sinais independentes e supremum mensurável. |
| C06 | Dudley | **Pendente**: números de cobertura, processo subgaussiano, hipóteses de separabilidade e integral de entropia. |
| C07 | Polyak–Łojasiewicz | **Completo**: estacionariedade implica ótimo e GD tem taxa linear em valor sem hipótese de convexidade; `Optimization/PolyakLojasiewicz`, com gradiente genuíno, L > 0 e 0 < μ ≤ L. |
| C08 | NTK infinito | **Parcial**: kernels de features finitas são simétricos e positivos semidefinidos (`Representation/Kernels`). Falta convergência de redes aleatórias em largura, inicialização e regime de treinamento especificados. |
| C09 | Viés de norma mínima | **Parcial**: decomposição pitagórica, minimalidade de interpolante na imagem do adjunto e preservação dessa imagem por GD (`Optimization/LeastSquares`). Falta convergência das iterações com passo admissível e distinção entre GD e SGD. |
| C10 | Cybenko | **Pendente**: há especificação de aproximação uniforme, sem demonstração de densidade. Hahn–Banach sozinho não prova que uma ativação é discriminatória. |
| C11 | Telgarsky | **Pendente**: construção triangular, contagem de oscilações e limite inferior para arquitetura rasa precisamente especificada. |
| C12 | Universalidade Transformer | **Pendente**: atenção equivariante está demonstrada; densidade das pilhas de blocos exige arquitetura, domínio e norma de aproximação especificados. |
| C13 | Kantorovich–Rubinstein | **Parcial**: toda função 1-Lipschitz dá limite inferior para qualquer acoplamento e para o custo ótimo finito (`Generative/TransportDuality`). Falta dualidade forte e caso compacto geral. |
| C14 | Quantização | **Completo para os limites corrigidos**: norma de operador e erro por entrada, ativação Lipschitz e dependência de dimensão (`Robustness/Quantization`). O limite fornecido sem fator de colunas é falso para erro por entrada. Não há compilador FP32→INT4 ou certificado de um modelo concreto. |
| C15 | Anderson | **Pendente**: as interfaces de leis/caminhos não provam existência de SDE, Fokker–Planck ou reversão temporal. |

## Os 43 tópicos do anexo

| ID | Pedido | Estado e evidência / obrigação restante |
|---|---|---|
| A01 | Limite inferior de Nesterov | **Pendente**: oráculo de primeira ordem, dimensão, família adversária e limite inferior. |
| A02 | Subgradientes | **Pendente**: oráculo de subgradientes e convergência O(1/√k). |
| A03 | FISTA | **Pendente**: operador proximal, aceleração e potencial telescópico. |
| A04 | Escape de selas | **Pendente**: regularidade de Hessiana, perturbações e controle probabilístico. |
| A05 | Kurdyka–Łojasiewicz | **Pendente**: propriedade KL e prova de convergência sob hipóteses analíticas. Não confundir com a condição PL já implementada. |
| A06 | AMSGrad | **Pendente**: estado adaptativo e prova de regret/convergência sob hipóteses explícitas. |
| A07 | Fenchel–Moreau / KKT | **Pendente**: conjugação, semicontinuidade, qualificação de restrições e dualidade. |
| A08 | McDiarmid | **Pendente**: diferenças limitadas em produto independente. |
| A09 | Bernstein | **Pendente**: controle por variância e limite uniforme dos incrementos. |
| A10 | Azuma–Hoeffding | **Completo no domínio subgaussiano condicional do Mathlib**: `LearningTheory/Martingales.azuma_hoeffding`, com filtração, adaptação forte e hipóteses mensuráveis explícitas. Falta especialização de diferenças limitadas. |
| A11 | Contração de Talagrand | **Pendente**: transformação Lipschitz de classes e sinais independentes. |
| A12 | Massart | **Pendente**: desigualdade maximal para classe finita. |
| A13 | Estabilidade uniforme | **Pendente**: algoritmo, amostras vizinhas e transferência para generalização. |
| A14 | Double descent | **Pendente**: modelo probabilístico de design/ruído e regime de interpolação. Não é fenômeno universal para qualquer rede. |
| A15 | Hornik Lp | **Pendente**: medida, integrabilidade e densidade Lp. |
| A16 | Leshno | **Pendente**: classe de ativações e equivalência com não polinomialidade quase sempre. |
| A17 | Largura mínima universal | **Pendente**: domínio, norma, dimensão e arquitetura. |
| A18 | Mercer / RKHS | **Parcial**: Gram finita positiva demonstrada em `Representation/Kernels`; faltam construção RKHS e decomposição espectral de Mercer. |
| A19 | Teorema do representador | **Pendente**: RKHS, funcional regularizado e existência de minimizador. |
| A20 | Kolmogorov–Arnold | **Pendente**: representação contínua por superposições univariadas. |
| A21 | Pinsker / Bretagnolle–Huber | **Pendente**: desigualdades entre variação total e KL. |
| A22 | Fano | **Pendente**: entropia condicional e probabilidade de erro. |
| A23 | Le Cam / Assouad | **Pendente**: redução de estimação a testes e separação de famílias. |
| A24 | Cramér–Rao multivariado | **Parcial**: desigualdade de informação de Hilbert derivada de Cauchy–Schwarz (`Information/CramerRao`); faltam modelos estatísticos regulares, score centrado e limite matricial. |
| A25 | DeepSets | **Parcial**: invariância de ρ(∑φ(x)) demonstrada em `Representation/DeepSets`. Falta o teorema de representação recíproca sob hipóteses de domínio/cardinalidade e dimensão latente. |
| A26 | Limites WL de GNNs | **Pendente**: grafos, message passing e refinamento de Weisfeiler–Leman. |
| A27 | Convolução equivariante | **Completo para grupos finitos e sinais reais escalares**: equivariância e prova recíproca de que todo operador linear equivariante é uma convolução em `Representation/GroupConvolution`. Faltam grupos infinitos e representações vetoriais gerais. |
| A28 | Chentsov | **Pendente**: métricas monotônicas e embeddings de Markov, com dimensão e normalização. |
| A29 | Brenier | **Pendente**: medidas com momentos, continuidade absoluta e existência/unicidade do mapa gradiente de potencial convexo. Convexidade estrita não é garantida em geral. |
| A30 | Benamou–Brenier | **Pendente**: equação de continuidade e problema variacional dinâmico. |
| A31 | Tweedie | **Completo para prior discreto finito escalar e ruído gaussiano de variância positiva**: positividade, derivada da densidade, derivada logarítmica e identidade em `Generative/Tweedie`. Falta versão vetorial e prior contínuo. |
| A32 | Hyvärinen | **Pendente**: integração por partes, condições de fronteira e equivalência de objetivos. |
| A33 | Flow matching | **Pendente**: fluxo de medidas, velocidade condicional e equação de continuidade. |
| A34 | Contração de Bellman | **Completo para MDPs finitos descontados**: probabilidades normalizadas, norma sup, contração, ponto fixo único e convergência da iteração de valor (`Reinforcement/Bellman`). |
| A35 | Q-learning | **Pendente**: exploração persistente, passos Robbins–Monro e convergência quase certa. |
| A36 | Policy gradient | **Pendente**: trajetória, política diferenciável, ocupação e troca de derivada/integral. |
| A37 | Performance difference | **Pendente**: políticas e ocupações; a fórmula com ocupação normalizada precisa do fator 1/(1−γ). |
| A38 | Sion / von Neumann | **Completo na forma de ponto de sela em dois conjuntos compactos convexos não vazios**: `GameTheory/Minimax.minimax_saddle`, reutilizando Sion do Mathlib. Não implica convergência de treinamento de GANs não convexas. |
| A39 | Composição avançada DP | **Pendente**: mecanismos adaptativos, transcritos e contabilização de privacidade. |
| A40 | Pós-processamento DP | **Completo para pós-processamento determinístico mensurável**: medidas e mecanismos de probabilidade em `Privacy/Differential`; preserva (ε,δ). Falta generalização explícita a kernels aleatorizados. |
| A41 | Predição conformal | **Pendente**: exchangeability, ranks com empates e cobertura marginal finita. |
| A42 | Brier | **Completo como identidade algébrica finita agrupada**: `Reliability/Brier.brier_decomposition`. A interpretação estatística requer frequências em [0,1] e agrupamento por previsão; não é uma prova de calibração de um modelo treinado. |
| A43 | Davis–Kahan | **Pendente**: operadores autoadjuntos, separação espectral e ângulo de subespaços. |

## Correções matemáticas e limites

- Para erro **por entrada** Δ em uma matriz com r linhas e c colunas e ‖x‖₂ ≤ B,
  provamos `‖(W−Q)x‖₂ ≤ √r √c Δ B`. A expressão `√r Δ B` exige controle da
  norma de cada linha, em vez do erro individual de cada entrada. Uma linha (1,1)
  e entrada (1,1) dão saída 2, enquanto o limite incorreto seria √2.
- Banach exige completude e contração do mapa inteiro; ‖W‖ < 1 sozinho não
  controla uma ativação arbitrária.
- PL não afirma que toda rede satisfaz PL. O teorema não transforma automaticamente
  pontos estacionários de perdas arbitrárias em ótimos globais.
- Um limite PAC-Bayes não é sempre não vacuoso. Ele exige probabilidades,
  quantificadores e hipóteses de amostragem que não podem ser omitidos.
- Equivariância não demonstra aproximação universal, e aproximação contínua em
  compactos não significa execução de todo algoritmo computável.
- Uma prova para SDE idealizada com score exato não certifica o treinamento ou a
  distribuição final de um modelo de difusão concreto.
- Nenhum destes resultados implica ausência de alucinações semânticas, segurança
  global de aviões/dispositivos médicos ou economia garantida de inferência.

Não há alegação de que os 58 tópicos estejam concluídos, nem de prioridade histórica.
