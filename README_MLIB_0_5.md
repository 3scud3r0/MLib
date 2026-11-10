# ML-MATHLIB 0.5 — certificação em domínios delimitados

## Execução

```bash
python ml_mathlib.py --test-all
```

## Implementações adicionadas

- **Álgebra:** solucionador modular CRT com `ModularSolveCertificate` que revalida `Ax=b` exatamente e prova unicidade por determinante modular não nulo.
- **Espectro:** polinômio característico racional, isolamento por Sturm e `CompleteRealRootCertificate`, que revalida quantidade e separação de todas as raízes reais distintas.
- **Geometria:** cociclos racionais de atlas, tensores densos, rotações SO(3) por Cayley e adjunta SE(3).
- **Probabilidade:** medida geométrica contável, gaussianas multivariadas e estratificação do simplex de Fisher.
- **Dinâmica:** fluxo de contato polinomial e certificado formal de simpléticidade local do ponto médio implícito.
- **Aprendizado e simetrias:** derivadas de softmax e Casimir da forma de Killing.

## Contratos e limites

Identidades algébricas são verificadas sobre racionais exatos. Certificados de existência local não são teoremas globais de existência. A isolação espectral contempla raízes reais, não espectro complexo/SVD geral. A álgebra simbólica pode ser exponencial no pior caso. Teoria geral de medida de Lebesgue, variedades suaves arbitrárias e provas Lean de todos os componentes não foram formalizadas.

O arquivo Lean é uma obrigação de prova; sua verificação depende de execução bem-sucedida do job Lean 4 no CI. Os testes Python não substituem o kernel Lean.

## Testes

A suíte totaliza 159 testes locais (104 anteriores + 55 novos), incluindo cinco testes para a certificação de completude da isolação espectral.
