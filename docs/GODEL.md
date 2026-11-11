# Godel: propostas externas e provas LeanML

O C++ fornecido foi integrado em `tools/godel/godel.cpp`, com componentes separados
para AST, parser, exportação e IPC. Origem: anexo `godel.cpp`, SHA-256
`6e927956d2afcb7b5cc03ba5e6e03f2ccb930ca1605d78ddbd3ce1b25ff591a1`.
O catálogo de regressões e os comandos anteriores foram preservados. Os comandos
nativos/JIT e exemplos físicos do anexo continuam opcionais; não participam da
certificação LeanML de reescritas.

## Compilar e testar

Requisitos: Linux/POSIX, C++17, GMP (`libgmp-dev`), Python 3 e o Lean fixado no projeto.

```sh
source scripts/activate.sh
bash scripts/check_godel.sh
```

O script compila com avisos como erros, executa os testes originais, testa o novo
AST com AddressSanitizer/UBSan e verifica propostas IPC e provas geradas no Lean.
Os binários ficam em `.lake/godel/`.

## DSL exato

As entradas `x0` a `x15` são racionais. A aridade declarada limita quais existem.
Soma, produto, negação e potência natural operam em escalares ou ponto a ponto em
tensores de mesma forma. Não há broadcasting implícito.

| Construção | Significado |
|---|---|
| `iflt(a,b,t,e)` | Se a < b, retorna t; caso contrário e. Guardas escalares e ramos de mesma forma. |
| `tensor([2,2],[x0,0,0,x1])` | Tensor em ordem de linhas; produto das dimensões igual ao número de células. |
| `matmul(A,B)` | Multiplicação de tensores literais de rank 2, reduzida a somas/produtos exatos. |
| `fold(3,x0,a0+i0)` | Três iterações: acumulador começa em x0 e soma os índices 0,1,2. |
| `a0`, `i0` | Acumulador/índice do loop mais interno; `a1`, `i1` referem-se ao loop externo. |
| `q(-1/2)` | Constante racional negativa canônica; distingue uma constante de uma operação de negação no cálculo de custo. |

Exemplo de estado tensorial: `fold(2,tensor([2],[x0,x1]),a0+tensor([2],[1,i0]))`.
A forma do estado é invariável. Os loops são puros, com número de iterações
estaticamente conhecido, inclusive zero; não há `while`, efeitos externos ou
interpretação de C++ arbitrário. `matmul` atualmente aceita tensores literais,
inclusive células escalares com controle de fluxo; não aceita diretamente o estado
tensorial de um loop como operando matricial.

Limites explícitos: 16 entradas escalares, rank até 4, até 1.024 células, até 64
iterações por loop, expoentes até 128 e profundidade de parser inferior a 128.
A avaliação simbólica tem orçamento de 50.000 visitas, até 10.000 termos e 65.536
bits por coeficiente. Há limites adicionais de tamanho de AST, representação e
expansão da prova. Um programa fora desses limites é rejeitado. Não há backend de
ponto flutuante: os teoremas se referem à semântica racional.

## Gerar uma prova

```sh
.lake/godel/godel --lean-out LeanML/Generated \
  --certify 1 'fold(3,x0,a0+i0)' 'x0+3'
python3 scripts/verify_godel_exports.py LeanML/Generated/Rewrite_*.lean
```

`--optimize n programa passos` usa a GNN local; `--evolve N` também exporta
automaticamente seus certificados de melhoria de AST. A GNN é instanciada somente
na busca local. A via IPC não executa inferência neural embutida.

São gerados `Rewrite_<hash>.lean` e `.lean.json`. O hash BLAKE3 identifica a
estrutura canônica dos dois ASTs, a aridade, os custos e a evidência normalizada.
O certificado C++ exige equivalência exata e custo estritamente menor. Condicionais
são tratados conservadoramente como átomos após normalizar guardas e ramos; algumas
identidades verdadeiras podem ser rejeitadas. Não se usa amostragem como prova.

O arquivo Lean contém os programas como `Term`, com loops e condicionais, e um
teorema `VerifiedRewrite before after`. Tensores usam funções `Fin n → ℚ`; sua
forma multidimensional é preservada em `outputShape`, com prova do produto das
dimensões. O kernel verifica a redução das projeções e dos custos; os números
informados pelo C++ não são hipóteses do teorema. O custo é uma medida estrutural,
não tempo de execução ou consumo de memória de uma máquina real.

A exportação começa com `lean_status: pending-kernel`. O verificador Python
reconstrói os ASTs com o C++, refaz custos e hashes e exige a tradução determinística
exata. Depois compila o teorema, confere seu tipo e audita os axiomas. Somente então
registra `kernel-verified`, a versão Lean e o SHA-256 dos bytes verificados. Uma
mudança nesses bytes exige nova verificação. Hashes não substituem provas nem
assinaturas. O gerador de táticas é limitado; uma falha de compilação mantém o
resultado sem certificação Lean.

Os arquivos podem ser adicionados ao Git normalmente. Para reexportar um resultado
pela API central, acrescente seu `public import` em `LeanML.lean` após revisão.
Os certificados históricos de Noether do anexo não são exportados por esta ponte.

## Propor por memória compartilhada

Em um terminal:

```sh
.lake/godel/godel --lean-out LeanML/Generated \
  --ipc-optimize /leanml_proposals 1 '(x0+0)' 30000
```

Em outro:

```sh
python3 tools/godel/propose.py --shm /leanml_proposals --replacement 'x0'
```

Para conectar um modelo local, use
`--command python3 meu_adaptador.py` no lugar de `--replacement`.
O adaptador recebe um pedido JSON no stdin e devolve **uma expressão DSL** no stdout.
Ele pode usar um LLM/GNN externo. O verificador não recebe código nativo nem táticas
Lean desse processo. Não há dependência de um modelo, SDK ou serviço específico.

O mailbox tem uma requisição por execução, nome exclusivo, permissões 0600 e é
removido ao fechar. Falhas/timeout não são convertidos em aprovação. Um modelo pode
estar errado: o C++ reavalia toda a proposta e o Lean verifica o teorema depois.
Essa separação é uma fronteira de confiança matemática; processos do mesmo usuário
no sistema operacional não são isolados entre si por memória compartilhada.

### Protocolo v1

Todos os acessos usam `flock(LOCK_EX)` no descritor shm. Inteiros little-endian;
sem ABI de `std::atomic` compartilhada. Cabeçalho de 32 bytes (`<8sIIQII` em Python):

| Offset | Campo |
|---|---|
| 0 | magic `GDIPC001` (8 bytes) |
| 8 | versão uint32 = 1 |
| 12 | estado uint32: 0 inicial, 1 pedido, 2 proposta, 3 resultado |
| 16 | request_id uint64 |
| 24 | tamanho uint32 do payload (máximo 1 MiB) |
| 28 | reservado uint32 = 0 |

O JSON de pedido inclui aridade, AST canônico, custo, `request_id` como string e
`source_blake3`. A resposta tem exatamente quatro linhas, sem newline final:

```text
GODEL_REPLACE_V1
<request_id decimal>
<source_blake3>
<expressão DSL proposta>
```

O resultado é JSON com `accepted`, estado C++ e caminho Lean ou erro. IDs/hash
incorretos, sintaxe inválida, tamanhos excessivos, mudança de forma, semântica
diferente e custo não menor são rejeitados. O tempo de espera é de 1 a 60.000 ms;
a verificação tem seus próprios orçamentos. Consulte `tools/godel/propose.py` para
um cliente funcional sem dependências Python externas.
