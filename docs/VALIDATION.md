# Validação da migração LeanML

A árvore de trabalho da migração foi compilada e verificada localmente com:

- Lean `4.36.0-rc2`, commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`.
- Mathlib `e58cf8d261d79b3803ed199b7afe8253fe6672f8`.
- Dependências transitivas fixadas em `lake-manifest.json`.

| Comando | Resultado observado |
|---|---|
| `lake --wfail build` | Biblioteca completa compilada, sem avisos |
| `bash scripts/check.sh` | Build, exemplos e auditoria de axiomas aprovados |
| `python3 scripts/check_proofs.py` | 25 arquivos Lean ativos sem lacunas ou novos axiomas |
| `python3 scripts/verify_legacy.py` | 939 arquivos originais e links preservados conforme manifesto |
| `python3 scripts/verify_legacy.py --sources-only` | 36 arquivos-fonte e de configuração originais preservados |
| `git bundle verify legacy/HISTORY.bundle` | Histórico Git completo e bundle válido |
| `git diff --check` | Sem erros de whitespace |

A biblioteca contém os 22 módulos do roteiro mais a entrada `LeanML.lean`.
Os dois arquivos de teste completam os 25 arquivos Lean ativos.

## Exemplos verificados

`LeanMLTest/Basic.lean` verifica entropia de uma moeda equilibrada, normalização
de softmax, permutação de atenção, translação de convolução, ramos da ReLU,
o gradiente de uma perda quadrática, diminuição da perda e a taxa de GD.
Um teste negativo demonstra que o campo identicamente zero não é o gradiente
da função identidade: a antiga condição de suavidade insuficiente é rejeitada.

## Axiomas

`LeanMLTest/Axioms.lean` inspeciona 22 resultados centrais, incluindo o lema da
descida, as taxas de GD, atenção matricial, entropia máxima, KL, processamento
de dados, Hoeffding, Sauer-Shelah, ELBO e acumulação reversa.
Todos reportaram somente:

```text
[propext, Classical.choice, Quot.sound]
```

O verificador rejeita `sorryAx`, `Lean.ofReduceBool` e `Lean.trustCompiler`
na saída dessa auditoria. As provas-fonte ativas também são verificadas contra
lacunas, novos axiomas e `native_decide` antes de compilar.

## Alcance

Esta validação refere-se à árvore local da migração. A execução do workflow no
GitHub só será conhecida depois de ele ser disparado. A compilação de uma
especificação em `Prop` não demonstra a propriedade que ela define; consulte
`STATUS.md` para os grandes teoremas que continuam pendentes.

O cache oficial do Mathlib estava bloqueado pela rede do ambiente, então as
dependências foram compiladas a partir dos fontes. A instalação de elan e do
compilador usou os artefatos oficiais do GitHub com TLS habilitado.
