# MLib / ML-MATHLIB 0.3 — álgebra exata e validação por domínio

A versão 0.3 mantém as 6 camadas da implementação original, preserva as extensões da 0.2 e acrescenta **`ml_mathlib_exact.py`**. Requer somente Python >= 3.10 e sua biblioteca padrão. Não é uma implementação de Lean 4, Mathlib, Singular ou um motor de treinamento de redes neurais de escala industrial.

## Começo rápido

```bash
python ml_mathlib.py --test-all
python ml_mathlib.py --test
python -m unittest discover -p 'test_ml_mathlib*.py' -v
python ml_mathlib.py --demo
python replay_certificate.py examples/central_force_conservation.json
```

Resultado local: **70 testes aprovados** (13 no módulo principal, 24 na expansão 0.2 e 33 na expansão 0.3), além de conferência de sintaxe e reprodução de um certificado de conservação. A infraestrutura de prova do Lean 4 (`lean`/`lake`) **não estava instalada**: o arquivo `.lean` gerado não foi compilado e **não deve ser identificado como um teorema formalmente verificado**.

## Arquitetura (0.3)

- **Estrato 0 — Álgebra:** determinante modular por CRT com majorante inteiro de Hadamard/L1 e parada apenas após unicidade; kernel racional com linhas inteiras primitivas; anéis quocientes `NumberField` com certificado de irredutibilidade por redução módulo primo, multiplicação e inversão exatas; `MixedTensor` (tensor de tipo (p,q)).
- **Estrato 1 — Geometria:** radicais simbólicos `QuadraticAlgebraicFunction`; expressões com `exp`, `log`, `sin`, `cos`, `sqrt` e derivadas formais; métrica racional, conexão de Levi-Civita e tensor de Riemann locais; cartas estereográficas explícitas de S²; `SU2` com quatérnions racionais e ação exata em SO(3); verificador de Jacobi para álgebras de Lie racionais.
- **Estrato 2 — Informação:** cálculo exato de momentos para uma distribuição uniforme contínua; representação natural de uma família exponencial gaussiana; distâncias geodésicas Fisher–Rao com limites racionais certificados nos simplexes e nas normais univariadas; extensão de `exp`, `log`, `sin` e `cos` a argumentos racionais sem um corte fixo de intervalo.
- **Estrato 3 — Dinâmica:** `MidpointContractionCertificate` usa intervalo racional e teorema de Banach para provar **existência e unicidade local** da solução implícita não linear; `ExactYoshida4` opera com coeficientes exatos em Q(∛2), com duas equações de ordem quatro verificadas simbolicamente; `PolynomialItoDiffusion` aplica o gerador de Itô a observáveis polinomiais.
- **Estrato 4 — Arquiteturas:** `SymbolicAttention` e `SymbolicMultiHeadAttention` calculam atenção causal com pesos simbólicos e derivam sua saída em relação aos parâmetros; a avaliação numérica via `math.exp` continua aproximada e a representação cresce rapidamente com a dimensão.
- **Estrato 5 — Descoberta:** `SparseExactKernel` recebe equações com entradas esparsas e limites de memória; `discover_casimirs` descobre invariantes de Poisson em grau limitado; Buchberger interreduzido via `reduced_groebner_basis`; certificados JSON de conservação verificáveis por reconstrução exata do parêntese de Poisson.

As APIs adicionais podem ser importadas diretamente de `ml_mathlib` (via resolução preguiçosa) ou de `ml_mathlib_exact`.

## Exemplos matemáticos comentados

### 1. Corpos de extensão sem arredondamento

```python
from ml_mathlib import NumberField
K = NumberField((-2, 0, 0, 1), certifying_prime=7)
a = K.alpha()                         # a representa a raiz real formal de X³ − 2
assert a**3 == 2                    # igualdade EXATA no corpo quociente
assert (a + 1)*(a + 1).inverse() == 1
```

`certifying_prime=7` é aceito porque o polinômio X³−2 é irredutível em F₇[X]. Isso **não** implica que qualquer extensão algébrica de Q tenha certificado do mesmo tipo. O objeto mantém a classe algébrica formal; escolher uma imersão real específica exige dados adicionais.

### 2. Hamiltoniano central não polinomial

```python
from ml_mathlib import Polynomial, RationalFunction, QuadraticAlgebraicFunction
q, p = Polynomial.variable(2, 0), Polynomial.variable(2, 1)
r2 = RationalFunction.from_polynomial(q*q + p*p)
root = QuadraticAlgebraicFunction.sqrt(r2)
V = 1/root                          # 1/sqrt(q²+p²), identidade formal
print(V.diff(0))                   # derivação da regra da cadeia, sem float
print(V.evaluate_interval((3,4))) # contém rigorosamente 1/5
```

O domínio real exige `q²+p² > 0`; caso contrário a inversa da raiz não está definida. O objeto representa uma **extensão quadrática da álgebra de funções racionais**, não um algoritmo de integração analítica de qualquer potencial físico.

### 3. Teorema do ponto fixo para ponto médio implícito

Com um campo hamiltoniano polinomial f, o passo é definido por:

\[
Y=z+h f\left(\frac{z+Y}{2}\right).
\]

A classe `MidpointContractionCertificate.certify(flow,z,h,box)` verifica duas condições com frações exatas:

\[
\Phi(B)\subseteq B,\qquad
\sup_{y\in B}\|D\Phi(y)\|_{\infty}\le q<1.
\]

Pelo teorema de Banach, existe uma única solução **dentro da caixa B**. `enclose(iterations)` diminui a caixa que contém essa solução. Não há alegação de unicidade global nem substituição de um solver simbólico geral.

### 4. Yoshida: constantes algébricas sem heurística decimal

Tomando α³=2, o método utiliza:

\[
a=\frac{1}{2-\alpha},\qquad b=-\frac{\alpha}{2-\alpha},\qquad
2a+b=1,\qquad 2a^3+b^3=0.
\]

As duas últimas identidades são verificadas no corpo `NumberField((-2,0,0,1),7)` e fornecem as condições algébricas habituais da composição simétrica de ordem quatro. `ExactYoshida4` implementa a composição para Hamiltonianos **polinomiais separáveis**; preservação simplética não implica conservação exata da energia.

### 5. Prova reproduzível de conservação

```python
from ml_mathlib import canonical_example, Polynomial, serialize_conservation_certificate
phase, h = canonical_example()
qx, qy, px, py = (Polynomial.variable(4,i) for i in range(4))
L = qx*py - qy*px
record = serialize_conservation_certificate(phase, h, L)
# O certificado armazena os dois polinômios, a dimensão e um resumo SHA-256.
# A verificação RELÊ o conteúdo e recalcula {L,H}=0 exatamente.
```

Um exemplo certificado é incluído em `examples/central_force_conservation.json`; sua verificação pode ser repetida em outro computador pelo script `replay_certificate.py`. O código `lean/CentralForceConservation.lean` é uma obrigação de prova exportada, **ainda não validada pelo kernel Lean**.

### 6. Atenção diferenciável, multi-head e causal

`SymbolicMultiHeadAttention(heads=2, head_dimension=1)` produz uma sequência de vetores simbólicos, com `3 × heads × d²` pesos de Q/K/V e `(heads × d)²` pesos de saída. A janela causal garante que a saída de posição i depende somente das posições j≤i. Derivadas analíticas são calculadas por `loss.diff(k)`; a avaliação de `exp` e a atualização dos parâmetros ainda são numéricas, sem garantias de treinamento em grande escala.

## Limites matemáticos ainda relevantes

1. O teste de irredutibilidade por redução módulo p é suficiente, mas não necessário para todos os polinômios irredutíveis em Q[X]. Não há raiz isolada, ordem total algébrica nem SVD geral.
2. Expressões transcendentes possuem regras de diferenciação formais e avaliadores por intervalos, mas não há uma teoria completa de corpos diferenciais, equivalência simbólica decidível ou integração transcendental geral.
3. `RationalFunction` continua sem MDC multivariado completo e, portanto, não tem forma reduzida canônica geral. A igualdade usa multiplicação cruzada. Instâncias não canônicas não devem ser utilizadas como chaves hash.
4. Atlas racionais e campos métricos são locais; suavidade global, topologia arbitrária, singularidades, condições de borda e conexões α para todas as famílias ainda não estão formalizados.
5. Gröbner e eliminação esparsa têm limites explícitos, mas **não** possuem garantia de complexidade polinomial em tempo ou memória. A verificação de um caso com 1.820 colunas esparsas é somente um teste favorável, não benchmark geral.
6. Integração de Itô é implementada somente no nível do gerador diferencial exato para coeficientes polinomiais; espaço de Wiener, existência forte/fraca e solver de SDEs não foram construídos.
7. Aritmética intervalar usa limites conservadores em subdomínios onde os operadores são definidos. Nem toda expressão pode ser certificada com precisão útil.
8. A biblioteca não executa Lean e não demonstra os axiomas matemáticos no kernel de um assistente de provas. A prova computacional em Python e o exportador textual não são substitutos de Mathlib formal.

**Auditoria completa:** consulte `CHECKLIST_25_0_3.md`, que distingue rigorosamente resoluções *no escopo anunciado* de questões ainda parciais. As primeiras três limitações são listadas separadamente dos 22 itens porque foram solicitadas como 25 pontos, apesar das sobreposições.
