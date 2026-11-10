# Integração MLib × Rust × NABLA-GPT — revisão 0.2

## 1. Modelo de confiança

```text
NABLA-GPT (PyTorch, CPU/CUDA, não confiável)
      ↓  apenas textos candidatos (e.g. "Q = p0**2/2 + q0**4/4")
Parser AST Python restrito (não confiável, sem eval)
      ↓  JSON AST exato e limitado
PyO3 (desserializa; nova arena com orçamento por proposição)
      ↓
Rust TCB (`#![forbid(unsafe_code)]` no kernel, BigRational)
      ↓  `verify_conservation` ou `NonZeroResidual`
`PyCertifiedTheorem` (somente criado pelo verificador Rust)
```

**Não são provas:** uma expressão Python, um retorno da rede, um digest BLAKE3 isolado ou um teste Python com verificador falso. A verificação externa em Lean ainda cobre somente obrigações aritméticas no subconjunto polinomial.

## 2. Instalação

No diretório do repositório MLib, com Rust e Python instalados:

```bash
cd mlib-core
cargo test --all-targets --no-default-features
cargo test --all-targets --features python
python -m pip install maturin
maturin develop --features python
python -m unittest discover -s python/tests -v
```

Ou, para construir a roda (`wheel`):

```bash
maturin build --release --features python --out dist
python -m pip install dist/*.whl
```

## 3. API simbólica sem JSON manual

```python
from fractions import Fraction
from mlib_core import PhaseSpace, Kernel

phase = PhaseSpace(1)
q, p = phase.coordinates()  # Ordem: q0, p0
H = p**2 / 2 + q**4 / 4

kernel = Kernel()  # Exige o binário Rust real
proved = kernel.verify_conservation(phase, hamiltonian=H, candidate=H)
print(proved.claim, proved.digest)

# Invariante falso: lança ValueError com resíduo simbólico
kernel.verify_conservation(phase, hamiltonian=H, candidate=q)
```

Para coeficientes exatos não inteiros: `Fraction(1, 7) * q`. O Python rejeita `0.1 * q` para não introduzir coerções silenciosas de `float`.

`phase.from_polynomial(p)` converte polinômios exatos da implementação legada do MLib, preservando coeficientes racionais e verificando dimensões.

## 4. Descoberta com propostas do modelo

```python
from mlib_core import PhaseSpace, Kernel
from mlib_core import DiscoverySession

phase = PhaseSpace(1)
q, p = phase.coordinates()
H = p**2 / 2 + q**4 / 4

session = DiscoverySession(Kernel(), phase, H)
proposals = ["Q = q0", "Q = p0**2/2 + q0**4/4", "Q = os.system('whoami')"]
for item in session.verify(proposals):
    print(item.text, item.accepted, item.digest, item.error)
```

Apenas o segundo candidato recebe um certificado. O primeiro produz um resíduo não nulo; o terceiro é rejeitado pelo parser antes de chegar ao Rust. O modelo pode usar CPU ou GPU, mas a verificação exata permanece no kernel.

Para executar a demonstração completa:

```bash
python examples/nabla_verified_discovery.py
```

## 5. NABLA-GPT treinado — adaptador opcional

Para checkpoints criados por `nabla_gpt_cuda.py` (módulo instalado ou importável):

```bash
PYTHONPATH=. python examples/nabla_verified_discovery.py \
  --checkpoint /caminho/checkpoint.pt --samples 8 --device cuda
```

O `NablaCheckpointSampler` exige `torch.load(weights_only=True)` e **não** invoca o `load_ckpt` permissivo do script original. Carregamentos que exigirem tipos Python arbitrários falham, de propósito. Módulos Python executados pelo propositor precisam ser obtidos de fonte confiável; a fronteira de confiança do TCB começa **depois** da FFI.

A rede deve ser treinada para emitir uma expressão **por amostra** na gramática: inteiros, `q0`, `p0`, `+`, `-`, `*`, `/`, `**` (expoentes de 0 a 32). Uma rede sem treinamento matemático pode retornar texto inválido ou nenhum candidato correto; isso resulta em **zero certificados**, nunca em certificados fabricados.

## 6. Redução dos custos algébricos

O `ring.rs` foi otimizado sem introduzir álgebra probabilística no TCB:

- Denominador racional não nulo e constante: normalização direta, sem MDC recursivo.
- Numerador identicamente zero: mantém as exclusões de domínio, mas dispensa MDC.
- Numerador igual a denominador: retorna `1` mantendo a exclusão do denominador original.
- MDC de polinômios iguais, unidades e monômios: caminhos determinísticos com provas aritméticas triviais.
- Soma de frações com o mesmo denominador: evita produto cruzado desnecessário.
- FFI: arena de termos descartada ao fim de cada verificação, evitando consumo cumulativo por candidatos inválidos.
- `verify_polynomial_gcd`: admite um MDC sugerido por Zippel ou qualquer outro propositor, mas só o certifica após verificar divisibilidades exatas e que os cofatores são coprimos.

A interpolação modular esparsa de Zippel e sua reconstrução certificada **não** foram implementadas. Para polinômios esparsos genéricos de grau elevado ainda há explosão combinatória no pior caso.

## 7. Testes e limites da validação

A suíte Python testa a gramática contra chamadas, atributos, `eval`, expressões perigosas, floats, mistura de espaços, tamanho e profundidade excessivos, regressões e a ligação real com PyO3 **quando instalada**. Os testes Rust cobrem os atalhos matemáticos exatos e a preservação do domínio original.

O GitHub Actions compila e testa Rust sem Python e com PyO3, constrói a wheel, importa a extensão e roda o exemplo completo. Testes com GPU não estão previstos no CI CPU.

O kernel **não** é um Lean completo e `CertifiedTheorem` não é um certificado universalmente transferível sem reexecução de suas condições matemáticas. Um PR verde significa compilação e testes do escopo declarado — não prova formal da implementação Rust inteira.

## 8. GCD acelerado por candidato não confiável (mas verificado)

```python
from mlib_core import PhaseSpace, Kernel
phase = PhaseSpace(1)
q, p = phase.coordinates()
factor = q + p
a, b = factor*q, factor*p
cert = Kernel().verify_polynomial_gcd(phase, a, b, factor)
print(cert.claim, cert.digest)
```

A identidade `a = g*a'`, `b = g*b'` **não basta** para provar que `g` é máximo. O kernel ainda exige `gcd(a', b') = 1` em ℚ[x]. Essa verificação permite aproveitar candidatos produzidos externamente, inclusive por busca modular, sem aceitar uma prova falsa. O motor de descoberta Zippel propriamente dito continua fora do escopo desta revisão.
