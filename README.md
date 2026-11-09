# MLib — ML-MATHLIB 0.2

Biblioteca de matemática simbólica e geometria para aprendizado de máquina em Python puro (sem PyTorch, NumPy ou SymPy).

## Comece aqui

```bash
python ml_mathlib.py --test
python -m unittest -v test_ml_mathlib_advanced
python ml_mathlib.py --demo
```

**Arquivos:** [núcleo](ml_mathlib.py) · [extensões](ml_mathlib_advanced.py) · [testes](test_ml_mathlib_advanced.py) · [guia técnico](README_MLIB_0_2.md) · [auditoria das 25 limitações](CHECKLIST_25.md).

Aritmética racional, operações polinomiais e parte da geometria são exatas. Integração não linear, modelos de atenção numéricos e muitas funções transcendentais ainda dependem de aproximações ou de domínios restritos. Os **37 testes locais** cobrem propriedades específicas; a biblioteca não substitui o kernel de provas Lean 4 nem é equivalente à Mathlib, Singular ou Macaulay2.

### Estado das 25 frentes

Três frentes foram atendidas no escopo anunciado; as outras 22 têm implementações parciais e limitações remanescentes documentadas no [checklist](CHECKLIST_25.md). Não há alegação de completude formal ou de desempenho de produção.

Licenciamento e condições de contribuição: consulte os arquivos do repositório.
