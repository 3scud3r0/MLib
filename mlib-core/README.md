# `mlib-core` — micro-kernel categórico-geométrico em Rust

**Versão inicial do núcleo verificador.** Este crate é separado do código de busca e treinamento Python/GPU. Implementa verificações matemáticas restritas, **não** um verificador geral de tipos dependentes equivalente ao Lean.

## Modelo de confiança

- `src/kernel/` é o TCB em Rust puro, com `#![forbid(unsafe_code)]`, sem `pyo3`, `f64`, `f32` nem Python.
- `src/ffi/` traduz JSON AST estrito em termos internados e reporta erros, sem produzir teoremas por conta própria.
- `CertifiedTheorem` possui **campos privados** e só o verificador o instancia. Uma string, JSON ou SHA-256/BLAKE3 avulso **não** vira uma prova.
- O digest BLAKE3 é uma **impressão digital de integridade** sobre a afirmação e termos canônicos. Não é assinatura digital, não autentica autores e não substitui replay por kernel independente.
- Hash-consing torna a igualdade **sintática** de IDs O(1) *dentro da mesma arena*. Igualdade algébrica requer normalização e não pode ser inferida de IDs brutos entre arenas.
- Identidades racionais são comprovadas somente no domínio explícito onde os denominadores **originais** não são zero. Cancelamentos não alargam silenciosamente o domínio.
- A identidade `DΦᵀJ DΦ=J` prova que o mapa **preserva localmente** a forma simplética, não sua bijetividade global.
- Operações sem algoritmo exato implementado são rejeitadas, não aproximadas.

## Preparação

```bash
# Rust estável + cargo
cd mlib-core
cargo test --all-targets --no-default-features
cargo test --all-targets --features python

# Python: maturin com o recurso opcional ativado
python -m pip install maturin
maturin develop --features python
```

O código foi concebido para Rust edition 2021. Não usa `unsafe` no TCB.

## Exemplos de AST Python

```python
import json
from mlib_core import MlibKernelContext

kernel = MlibKernelContext()
q = {"op": "var", "index": 0}
p = {"op": "var", "index": 1}
H = {"op": "add", "left": {"op": "pow", "base": q, "exponent": 2},
                  "right": {"op": "pow", "base": p, "exponent": 2}}
certificate = kernel.verify_noether(1, json.dumps(H), json.dumps(H))
print(certificate.claim, certificate.digest)
print(certificate.to_lean4_code())  # obrigação algébrica, não prova do fluxo

# Q=q NÃO é um invariante do oscilador: gera ValueError
kernel.verify_noether(1, json.dumps(H), json.dumps(q))
```

### Gram positiva definida

```python
certificate = kernel.verify_positive_gram([["2", "1"], ["1", "2"]])
```

### Testes de som integridade

- Invariante falso deve ser rejeitado com resíduo simbólico não nulo.
- `x/x` nunca pode provar igualdade global ignorando `x=0`.
- O mapeamento `q→q, p→2p` deve ser rejeitado como não simplético.
- Estruturas antis simétricas sem Jacobi devem ser rejeitadas.
- Matriz de Gram indefinida deve ser rejeitada.
- O objeto de certificado não possui construtor público em Rust ou Python.

## Escopo implementado

`ExactScalar`, polinômios esparsos `ℚ[x]`, frações racionais `ℚ(x)` com MDC recursivo e restrições de domínio, AST interning, derivadas simbólicas, Poisson, formas diferenciais exteriores locais, colchetes de Lie finitos, Bareiss, LDLᵀ, posto, Casimirs de Lie–Poisson e checagens de conservação/simpléticidade. Exportação Lean gera **apenas a identidade polinomial expandida** para `ring`; não formaliza o teorema de conservação de trajetórias nem demonstra correção do kernel.

## Limites explícitos

Sem tipos dependentes gerais, física em variedades arbitrárias, integrais transcendentais, teoria geral da medida, eliminação algébrica com escala industrial, SVD geral ou garantia de terminação/tempo polinomial de normalização multivariada. Regras de inferência são decidíveis somente no escopo matemático aqui documentado. Testes de unidade não substituem análise de soundness nem prova formal externa.

## Integração Python / NABLA-GPT (revisão 0.2)

Consulte [`../README_MLIB_KERNEL_INTEGRATION.md`](../README_MLIB_KERNEL_INTEGRATION.md) para a sintaxe de `PhaseSpace`, `Kernel`, `DiscoverySession`, a execução com checkpoint seguro e os limites dos caminhos rápidos de MDC.
