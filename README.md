# LeanML

Formalização axiomática de fundamentos do aprendizado de máquina em **Lean 4 / Mathlib**.
O projeto ativo é uma biblioteca Lean. O projeto anterior foi preservado em
[`legacy/`](legacy/ARCHIVE.md), com manifesto de hashes e cópia do histórico Git.

```sh
source scripts/activate.sh
lake exe cache get
lake build
bash scripts/check.sh
```

Instale [elan](https://github.com/leanprover/elan) e inclua `~/.elan/bin` no `PATH`.
O arquivo `lean-toolchain` seleciona o compilador. O commit do Mathlib e as
revisões transitivas estão fixados em `lakefile.lean` e `lake-manifest.json`.
A configuração atual usa Lean **v4.36.0-rc2**, compatível com o Mathlib consultado
na migração. O v4.15.0 citado no roteiro não é compatível com esse Mathlib.
Não atualizar a dependência flutuantemente é uma escolha de reprodutibilidade.

Para compilar sem cache de rede, use `lake --no-cache build`.
Para rematerializar dependências sem disparar o download automático do cache,
use `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`. O cache oficial requer acesso a
`cache.mathlib.org`; o compilador e as dependências usam também GitHub e seus
hosts de download. A compilação a partir dos fontes é consideravelmente mais demorada.

A entrada pública é [`LeanML.lean`](LeanML.lean), com cinco áreas:

| Pilar | Diretório | Conteúdo |
|---|---|---|
| Informação | `LeanML/Information/` | Entropia finita, KL de medidas e processamento de dados |
| Otimização | `LeanML/Optimization/` | Gradientes, descida, taxas e regras de diferenciação |
| Aprendizagem | `LeanML/LearningTheory/` | Riscos, concentração, VC, Sauer-Shelah e especificações PAC |
| Representação | `LeanML/Representation/` | Ativações, redes dimensionadas, convolução e atenção |
| Modelos generativos | `LeanML/Generative/` | Acoplamentos finitos, ELBO e interfaces de difusão |

O [estado dos teoremas](docs/STATUS.md) distingue resultados demonstrados,
resultados reutilizados do Mathlib e especificações ainda sem prova. A presença
de um arquivo com o nome de um grande teorema não significa que ele já esteja
formalizado. Nenhum resultado pendente é introduzido como axioma.

A definição de suavidade inclui `HasGradientAt f (g x) x`: exigir apenas que um
campo vetorial arbitrário seja Lipschitz não implica o lema da descida para `f`.
As hipóteses de suporte, integrabilidade, positividade e mensurabilidade aparecem
nos tipos das definições e dos teoremas correspondentes.

A migração passou no build, nos exemplos e na auditoria de 22 teoremas centrais;
veja [docs/VALIDATION.md](docs/VALIDATION.md) para a evidência e o alcance.

Veja [CONTRIBUTING.md](CONTRIBUTING.md) para os critérios de contribuição.

O arquivo [exports/LeanML_codigo_completo.txt](exports/LeanML_codigo_completo.txt)
reúne todas as fontes ativas, testes, scripts, configurações e documentação em
texto UTF-8. Para regenerá-lo, execute `python3 scripts/export_code.py`.
