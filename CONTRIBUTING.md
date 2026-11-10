# Contribuir com LeanML

Use o compilador fixado em `lean-toolchain` e as revisões de `lake-manifest.json`.
Não substitua hipóteses ausentes por axiomas, `sorry`, `admit` ou avaliação nativa.
Use `module`, `public import` e `@[expose] public section`, conforme o sistema
de módulos do Lean fixado no projeto. Prefira definições existentes do Mathlib e imports específicos. Teoremas reutilizados
devem manter as hipóteses e a atribuição ao Mathlib claramente documentadas.

Para cada mudança matemática:

1. Declare domínio, normalização, integrabilidade, suporte e mensurabilidade necessários.
2. Acrescente uma aplicação concreta ou teste de regressão em `LeanMLTest/Basic.lean`.
3. Liste os resultados principais em `LeanMLTest/Axioms.lean`.
4. Execute `bash scripts/check.sh` e atualize `docs/STATUS.md`.

O script verifica ausência de lacunas, compila a biblioteca e os exemplos e
inspeciona os axiomas dos principais teoremas. Os axiomas lógicos usuais de Lean
(`propext`, `Classical.choice`, `Quot.sound`) são permitidos; lacunas e dependência
da avaliação nativa não são aceitas como provas.

Resultados ainda não demonstrados podem ser definidos como propriedades em `Prop`,
com status explícito de especificação. Não crie um teorema que apenas recebe como
hipótese a conclusão desejada e o anuncie como demonstração do resultado original.

`legacy/` é um arquivo histórico: não importe seus módulos no projeto ativo e não
reative seus workflows. O escopo ativo é aprendizado de máquina formalizado.
