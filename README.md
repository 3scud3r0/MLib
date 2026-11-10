# MLib — ML-MATHLIB 0.3

Biblioteca experimental de **álgebra exata, geometria, dinâmica e aprendizado simbólico** em Python puro, organizada em seis estratos matemáticos. **Sem dependências de PyTorch, NumPy ou SymPy.**

## Executar

```bash
python ml_mathlib.py --test-all
python ml_mathlib.py --test
python -m unittest discover -p 'test_ml_mathlib*.py' -v
python ml_mathlib.py --demo
python replay_certificate.py examples/central_force_conservation.json
```

**70 testes locais passaram**: 13 do núcleo, 24 da versão 0.2, 33 da versão 0.3. Os componentes operam com aritmética exata quando declarado; transcendentes e integrações podem usar intervalos racionais certificados ou aproximações explicitamente sinalizadas.

## Componentes

| Arquivo | Função |
|---|---|
| [`ml_mathlib.py`](ml_mathlib.py) | Núcleo e interface de importação da biblioteca |
| [`ml_mathlib_advanced.py`](ml_mathlib_advanced.py) | Expansão 0.2: Gröbner, frações, informações de Fisher, contato, Noether, atenção |
| [`ml_mathlib_exact.py`](ml_mathlib_exact.py) | Expansão 0.3: CRT, corpos algébricos, intervalos, ponto médio certificado, SU(2), curvatura, atenção diferenciável, Casimirs |
| [`test_ml_mathlib_advanced.py`](test_ml_mathlib_advanced.py) | Testes da 0.2 |
| [`test_ml_mathlib_exact.py`](test_ml_mathlib_exact.py) | Testes da 0.3 |
| [`README_MLIB_0_3.md`](README_MLIB_0_3.md) | Derivações, exemplos e hipóteses matemáticas |
| [`CHECKLIST_25_0_3.md`](CHECKLIST_25_0_3.md) | Auditoria dos 25 itens e suas restrições |
| [`examples/central_force_conservation.json`](examples/central_force_conservation.json) | Certificado de conservação portátil que pode ser reexecutado |
| [`lean/CentralForceConservation.lean`](lean/CentralForceConservation.lean) | Obrigação Lean gerada: **não compilada nem certificada pelo Lean 4** |

## Precisão sobre o escopo

**Não é uma Mathlib completa.** Uma identidade polinomial validada em Python não equivale a um teorema verificado por Lean; uma classe de corpo de números algébricos não resolve automaticamente qualquer decomposição espectral; um cálculo local em atlas não prova a topologia de variedades gerais. O inventário atualizado é **5/25 atendidos em domínios restritos e 20/25 parciais**, não 25/25 esgotados. Consulte o [checklist](CHECKLIST_25_0_3.md) para evidências.
