# Validação LeanML

Verificação local da revisão com 41 módulos matemáticos e 47 arquivos Lean ativos
(41 módulos, entrada pública, três arquivos de testes e dois exemplos gerados).

- Lean `4.36.0-rc2`, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`.
- Mathlib `e58cf8d261d79b3803ed199b7afe8253fe6672f8`.
- Dependências transitivas fixadas em `lake-manifest.json`.

| Comando | Resultado observado |
|---|---|
| `LEAN_NUM_THREADS=4 lake --wfail --no-cache build` | Biblioteca completa compilada; avisos tratados como falhas |
| `bash scripts/check.sh` | Build, exemplos básicos e avançados, inspeção de axiomas aprovados |
| `python3 scripts/check_proofs.py` | 47 arquivos Lean sem lacunas ou novos axiomas |
| `git diff --check` | Sem erros de whitespace |
| `python3 scripts/export_code.py` | TXT UTF-8 com fontes ativas e índice de hashes |

## Exemplos verificados

`LeanMLTest/Basic.lean`: moeda equilibrada, normalização de softmax, permutação de
atenção, translação de convolução, ReLU, gradiente quadrático genuíno, diminuição
de perda e taxa convexa de GD. O teste negativo rejeita a antiga definição de
suavidade que admitia campo nulo como gradiente da função identidade.

`LeanMLTest/Advanced.lean`: margem binária com perturbação não nula, rejeição de
empate como vencedor estrito, equilíbrio DEQ, condição PL quadrática e taxa de GD,
Brier de previsão enviesada, valor de MDP de um estado descontado, posterior de
prior pontual gaussiano e identidade de Tweedie com derivada real da log-densidade.
O exemplo de quantização rejeita o limite com dependência de dimensão incompleta.

## Auditoria de axiomas

`LeanMLTest/Axioms.lean` inspeciona 70 resultados: os 68 anteriores e dois teoremas de programas.
As dependências reportadas pertencem somente aos axiomas lógicos usuais (alguns
resultados não dependem de nenhum axioma):

```text
[propext, Classical.choice, Quot.sound]
```

O script rejeita `sorryAx`, `Lean.ofReduceBool` e `Lean.trustCompiler` na saída.
A inspeção textual prévia rejeita lacunas, novos axiomas e `native_decide` nas fontes.
Os testes Lean também tratam avisos como erros. O log da auditoria fica em
`.lake/leanml-axioms.log` após executar o script.

## Alcance e reprodução

A validação é local; uma execução futura de GitHub Actions precisa ser observada
separadamente. Compilar uma propriedade em `Prop` não prova essa propriedade.
Consulte [STATUS.md](STATUS.md) para os teoremas de pesquisa ainda pendentes.

O cache oficial estava bloqueado pela rede deste ambiente. As dependências foram
compiladas a partir dos fontes; não se usou artefato não verificado para substituir
uma prova. A primeira compilação sem cache pode exceder o timeout do CI.

O código histórico alheio a LeanML foi removido da árvore ativa. É recuperável pelo
commit anterior `faae94e77de16235319cc00524387701b124f405`. Antes da remoção, uma cópia
integral externa foi verificada arquivo a arquivo (977 arquivos regulares, além de
links). Arquivo local: `/workspace/archives/MLib_legacy_faae94e.tar.gz`.
SHA-256: `d51a2ef1cf945c0a032e7a41f13f7db57cbfada5a062b58207e769844a6e8e9c`.
Essa cópia não é uma dependência de build nem integra a exportação do código ativo.


## Ponte Godel → LeanML

O anexo C++ passou nos 2.194 testes originais, incluindo 1.700 casos de identidades
polinomiais (1.600 válidos e 100 rejeitados). A nova suíte de unidade cobre 24 casos
com AddressSanitizer/UBSan: estado de loop, índices aninhados, condicionais,
tensores, multiplicação matricial, forma/tamanho/aridade inválidos, limites de
parser, coleta de lixo, replay de ASTv2, constante negativa canônica e rejeição de
certificado adulterado na exportação.

A integração testa 11 pares de programas equivalentes e mais as otimizações dos comandos `--optimize` e `--evolve` da
GNN, com geração/replay BLAKE3 e verificação real no Lean. Inclui loops vazios,
loops aninhados, condicional dependente do índice, estado tensorial, condicional
com saída tensorial, aritmética racional negativa e multiplicação matricial.

Os casos IPC cobrem cliente manual, adaptador de modelo externo via subprocesso,
proposta falsa, sintaxe inválida, ID antigo, hash incorreto, tamanho adulterado e
timeout. A proposta do processo externo também passa pela verificação Lean. A
adulteração de uma prova emitida é rejeitada e invalida seu status. Os exemplos em
`examples/godel/` guardam os metadados e o SHA-256 dos fontes verificados.

Reprodução: `bash scripts/check_godel.sh`. Os geradores usam um modelo fixo de
táticas, com os linters de táticas/argumentos inutilizados desabilitados somente
nos arquivos gerados. Isso não altera o kernel ou os axiomas permitidos. Os demais
avisos de Lean continuam sendo tratados como erros. Os testes não demonstram a
correção formal da implementação nativa do C++ ou de todo programa C++ arbitrário.
