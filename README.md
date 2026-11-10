# MLib — ML-MATHLIB 0.4

Biblioteca de álgebra, geometria da informação, dinâmica hamiltoniana e descoberta simbólica em **Python puro**. Não depende de PyTorch, NumPy, SymPy ou SciPy para executar.

## Começar

```bash
python ml_mathlib.py --test-all
python ml_mathlib.py --demo
python replay_certificate.py examples/central_force_conservation.json
```

A suíte de regressão executada localmente em Python 3.13.5 passou com **104/104 testes**. O comando `--test-all` reúne núcleo 0.1, extensões 0.2/0.3 e novas verificações 0.4.

## Arquivos

- [Núcleo canônico e APIs](ml_mathlib.py)
- [Extensões 0.2](ml_mathlib_advanced.py)
- [Extensões exatas 0.3](ml_mathlib_exact.py)
- [Extensões verificáveis 0.4](ml_mathlib_verified.py)
- [Testes de todas as versões](test_ml_mathlib_verified.py)
- [Guia técnico 0.4](README_MLIB_0_4.md)
- [Auditoria detalhada dos 25 problemas](CHECKLIST_25_0_4.md)

O resultado não é equivalente à Mathlib do Lean. **8/25 frentes** têm soluções completas em domínios expressamente delimitados e **17/25 permanecem parciais**. A complexidade combinatória e a necessidade de um verificador de provas externo impedem alegar conclusão plena.

## Cuidados de rigor

Identidades no domínio racional/polinomial são calculadas e verificadas exatamente. Logaritmos, trigonometria arbitrária e distribuições contínuas mais gerais exigem intervalos certificados ou hipóteses adicionais. A prova exportada a Lean ainda **não foi compilada e verificada** pelo kernel Lean.
