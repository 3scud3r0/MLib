# LeanML

Biblioteca de fundamentos matemáticos de aprendizado de máquina em **Lean 4 / Mathlib**.
A entrada pública é [`LeanML.lean`](LeanML.lean). As provas são verificadas pelo kernel;
nenhum teorema pendente é introduzido como axioma.

```sh
source scripts/activate.sh
lake exe cache get
bash scripts/check.sh
python3 scripts/export_code.py
```

Instale [elan](https://github.com/leanprover/elan) antes de executar esses comandos.
O projeto fixa Lean **v4.36.0-rc2** e o commit do Mathlib em `lakefile.lean` e
`lake-manifest.json`. O Lean 4.15 do roteiro inicial é incompatível com essa revisão.
Para compilar as dependências a partir dos fontes, use `lake --no-cache build`.
Para rematerializar dependências sem baixar automaticamente o cache, use
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`. O cache oficial requer `cache.mathlib.org`.

| Área | Resultados e interfaces |
|---|---|
| Informação | Entropia finita, KL de medidas, processamento de dados, desigualdade de informação |
| Otimização | Suavidade com gradiente genuíno, descida, taxas convexas e PL, geometria de mínimos quadrados |
| Aprendizagem | Risco, Hoeffding, Azuma-Hoeffding, Chebyshev, VC, Sauer-Shelah, mudança de medida variacional |
| Representação | MLP, atenção equivariante, kernels finitos positivos, DeepSets invariantes, classificação de convoluções em grupos finitos |
| Robustez | Produto de constantes Lipschitz, margem adversarial estrita, equilíbrio de DEQs, erro de quantização |
| Generativos | Acoplamentos finitos, dualidade fraca de transporte, ELBO, Tweedie para misturas gaussianas escalares |
| Reforço | Bellman para MDPs finitos descontados, unicidade e convergência de iteração de valor |
| Privacidade | Preservação de privacidade diferencial por pós-processamento mensurável determinístico |
| Confiabilidade | Decomposição finita de Brier em calibração, resolução e incerteza |
| Jogos | Minimax de Sion na forma de ponto de sela, reutilizado do Mathlib |

Há **40 módulos**, além da entrada e três arquivos de testes. O
[inventário](docs/STATUS.md) identifica as provas completas, especializações e
pendências dos 58 tópicos adicionais solicitados. Cybenko, NTK no limite infinito,
PAC-Bayes de alta probabilidade e reversão de Anderson **ainda não estão provados**.
Uma especificação em `Prop` não demonstra o teorema que descreve.

Os limites de robustez preservam decisões sob hipóteses explícitas de margem e
Lipschitz. Eles não certificam a verdade semântica das respostas de um modelo.
A cota de erro de quantização por entrada inclui os fatores de dimensão necessários.

O [relatório de validação](docs/VALIDATION.md) descreve os comandos e o alcance dos testes.
As [regras de contribuição](CONTRIBUTING.md) exigem hipóteses explícitas e provas sem lacunas.

O código Python/Rust e a documentação sem relação com LeanML foram retirados da
árvore ativa. Permanecem recuperáveis no histórico Git; esta versão não depende deles.

[Baixar todo o código em TXT](exports/LeanML_codigo_completo.txt).
A exportação UTF-8 inclui fontes, testes, scripts, CI, configurações e documentação,
com índice de tamanhos e hashes SHA-256. Não inclui dependências de terceiros ou binários.
