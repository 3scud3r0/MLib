# Arquivo histórico ML-MATHLIB

O conteúdo da raiz anterior foi movido integralmente para este diretório,
conservando nomes, conteúdo e links simbólicos. O manifesto `ARCHIVE_MANIFEST.json`
registra SHA-256 dos 939 arquivos, os 4 links simbólicos, o HEAD e o estado Git
anteriores à migração. `HISTORY.bundle` preserva as referências e objetos Git.
O diretório `.git` ativo permanece na raiz para manter a continuidade do repositório.

Fontes, documentação, exemplos, workflows e alterações locais da biblioteca
Python estão preservados. Ambientes virtuais, caches e produtos de build também
permanecem no disco, mas são ignorados pelo Git por serem regeneráveis.

Nada neste diretório integra o build ativo LeanML. Os workflows históricos em
`legacy/.github/` estão arquivados e não são executados pelo GitHub Actions.

Não confunda os testes Python históricos com provas verificadas pelo Lean.

A preparação do PR também incorporou as adições de `main` até o commit
`ea9cf827fea7f35ad57e3873c7a81c9cf218cd22`: 33 arquivos do núcleo Rust,
integração Python/NABLA, testes, documentação e workflows. Eles foram movidos
para seus mesmos caminhos relativos dentro de `legacy/`, sem alterar conteúdo.
`UPSTREAM_ARCHIVE_MANIFEST.json` registra seus hashes e `UPSTREAM_HISTORY.bundle`
preserva o histórico atualizado. O verificador confere ambos os manifestos.
