# Fundação de exatidão — desenvolvimento 0.6

Python 3.11 ou posterior; nenhuma dependência de execução externa.

```sh
python -m venv .venv
.venv/bin/python -m pip install -e .
.venv/bin/python ml_mathlib.py --test-all
.venv/bin/mlib-replay examples/central_force_conservation.json
```

Execute a regressão no checkout. `ml-mathlib --demo` também funciona depois da
instalação fora do diretório do projeto. Nenhum serviço ou credencial é necessário
para o fluxo Python. A compilação Lean é um fluxo separado, definido no CI.

## Sistemas lineares e certificados

```python
from ml_mathlib import Matrix, Vector, exact_linear_solve, verify_linear_certificate

certificate = exact_linear_solve(Matrix(((1, 2, 3), (2, 4, 6))), Vector((1, 2)))
assert certificate.verify()
assert certificate.rank == 1
assert certificate.consistent
assert len(certificate.kernel) == 2
assert verify_linear_certificate(certificate.to_json())
```

Todas as soluções são `particular + Σ tᵢ kernel[i]` com parâmetros racionais
livres. Para um sistema inconsistente, `particular` é `None` e `inconsistency`
contém o testemunho. O núcleo é calculado mesmo nesses sistemas.

`verify()` verifica as identidades matriciais, a RREF e a independência e
completude do núcleo sem chamar o solucionador. `from_json()` apenas interpreta
o formato; chame `verify()` ou use `verify_linear_certificate()`. O formato
`mlib.linear-system`, versão 1, exige campos exatos, racionais reduzidos em
strings e ausência de chaves duplicadas. Valores booleanos, decimais e campos
desconhecidos são rejeitados.

`exact_linear_solve(..., max_cells=...)` lança `MemoryError` antes da alocação
se exceder o orçamento; incompatibilidade dimensional lança `ValueError`.
Não é um algoritmo modular nem uma garantia de tempo polinomial em todos os
parâmetros de entrada. Veja as limitações em [IMPLEMENTATION_STATUS.md](IMPLEMENTATION_STATUS.md).

## Expressões e precisão

```python
from fractions import Fraction as F
from ml_mathlib import AnalyticExpression as E, RationalInterval as I

x = E.variable(0)
f = (x ** F(1, 3) + 1) ** F(1, 2)
enclosure = f.enclose_adaptive((I(27, 27),), tolerance=F(1, 10**12))
assert enclosure.contains(2)
gradient = f.gradient(1)
hessian = f.hessian(1)
```

`E.cast` aceita `Polynomial`, `RationalFunction`, `QuadraticAlgebraicFunction`
e constantes racionais. Use `f.compose((g0, g1, ...))` para substituir variáveis.
Restrições já removidas pelo cancelamento de uma fração antiga não podem ser
recuperadas na conversão.

Potências fracionárias usam o ramo real estritamente positivo, com denominador
do expoente até 1024 e precisão de raízes até 4096 dígitos de escala. Radicais
quadráticos por `sqrt()` mantêm o domínio não negativo. Derivadas podem exigir
domínios menores, como `sqrt(x)` em `x > 0`.

`enclose_adaptive` exige tolerância positiva e aumenta o parâmetro de precisão
até `max_digits`. Esse parâmetro não promete dígitos decimais corretos: a largura
do intervalo retornado é a garantia. Caixas largas e dependências repetidas
podem impedir a convergência; nesse caso lança `RuntimeError`. Domínios inválidos
lançam `ValueError`; intervalos de denominadores contendo zero lançam
`ZeroDivisionError`.

## Invariantes esparsos

`SymbolicCrystallizer.discover` usa `backend='sparse'` por padrão. O backend
`'dense'` continua disponível como referência. `max_terms`, `max_nonzeros` e
`max_basis` limitam respectivamente ansatz, armazenamento de restrições e tamanho
da base. Cada candidato é revalidado por seu bracket de Poisson exato.

Essa enumeração é completa apenas no ansatz escolhido e não elimina a
complexidade combinatória nem estabelece independência algébrica dos resultados.

`python benchmark_sparse.py` mede tempo e pico de memória rastreada em núcleos
esparsos sintéticos com 1.820 e 18.564 colunas, correspondentes aos tamanhos dos
ansätze de 12 variáveis e graus 4 e 6, incluindo a constante. Verifica posto e
base contra a solução conhecida. Não mede a mineração completa de invariantes
nem estabelece limites de desempenho para outros sistemas esparsos.

As instruções locais da nuvem estão em [CLOUD_ENVIRONMENT.md](CLOUD_ENVIRONMENT.md).
