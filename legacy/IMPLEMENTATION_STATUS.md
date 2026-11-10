# Implementação incremental após a auditoria 0.5

Esta entrega não conclui as 204 tarefas citadas na solicitação. O texto recebido
descreve frentes, mas não contém o arquivo com os 204 identificadores individuais.
Os critérios abaixo registram somente o escopo efetivamente implementado.

## Fundação de exatidão

- [x] Resolver sistemas racionais retangulares, singulares, sobredeterminados e de posto zero.
- [x] Produzir solução particular e base completa do núcleo quando existe solução.
- [x] Produzir testemunho de inconsistência `y` com `Aᵀy = 0` e `yᵀb ≠ 0`.
- [x] Certificar posto e completude com RREF e transformações inversíveis verificáveis.
- [x] Serializar certificados em JSON canônico versionado e rejeitar adulterações.
- [x] Limitar bytes, entradas e tamanho de escalares na leitura de certificados.
- [x] Limitar células antes de alocar a eliminação densa.
- [x] Converter polinômios, frações e radicais quadráticos para expressões analíticas.
- [x] Compor expressões por substituição simultânea.
- [x] Avaliar potências racionais e radicais aninhados no ramo real estritamente positivo.
- [x] Calcular limites de raízes por potências inteiras exatas.
- [x] Refinar intervalos até uma largura exigida ou falhar ao esgotar o orçamento.
- [x] Construir gradientes e Hessianas simbólicas avaliáveis por intervalos.

Ainda faltam eliminação modular retangular, reconstrução racional adaptativa,
normalização certificada geral, recuperação de domínios cancelados, extensões
algébricas gerais, intervalos ilimitados/uniões, aritmética afim e modelos de Taylor.
O limite de células não constitui limite de RAM em bytes: coeficientes racionais
podem crescer. Também não limita o tempo de CPU.

## Descoberta de invariantes

- [x] Integrar `SymbolicCrystallizer.discover` ao `SparseExactKernel`.
- [x] Construir restrições esparsas sem matriz densa de coeficientes.
- [x] Aplicar limites de monômios, coeficientes não nulos e tamanho da base.
- [x] Verificar explicitamente o bracket de cada resultado, inclusive com `python -O`.
- [x] Comparar os backends esparso e denso em problemas de regressão.

Ainda faltam reconstrução modular integrada, geração por órbitas, análise
dimensional, checkpoints, paralelismo e benchmarks completos de 12 variáveis
nos graus 4 e 6. A geração e a saída ainda podem consumir memória significativa.

## Distribuição e validação

- [x] Adicionar metadados PEP 517/621 e instalação editável via pip.
- [x] Manter imports existentes e expor o solucionador pela API principal.
- [x] Integrar as novas suítes ao comando de regressão existente.
- [x] Acrescentar testes positivos, negativos, limites de recursos e certificados adulterados.

Não foi escolhida uma licença em nome do titular. Publicação em registro,
compatibilidade oficial multiplataforma, assinatura de releases e cobertura
formal ampliada continuam pendentes. Os certificados novos são verificados em
Python com aritmética racional; não foram formalizados no kernel Lean.

## Demais frentes

Geometria global, teoria da medida geral, conexões de informação, integração
implícita geral, contato e termodinâmica, autodiff reverso universal, Transformers
treináveis, representações gerais, redução de Poisson e formalização de todos os
estratos continuam como trabalho futuro. As implementações anteriores não são
promovidas a soluções gerais por esta entrega.
