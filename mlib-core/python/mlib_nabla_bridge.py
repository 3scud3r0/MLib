"""Untrusted NABLA-GPT candidate sampling, strict parsing and Rust verification.

Nothing in this file proves a theorem: all accepted certificates are native
Rust PyCertifiedTheorem objects returned by mlib_core. Requires no torch unless
NablaCheckpointSampler.from_checkpoint() is explicitly invoked.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Any

from mlib_kernel import Expr, PhaseSpace, Kernel

MAX_TEXT_CHARS = 4096
MAX_PARSE_NODES = 500
MAX_PARSE_DEPTH = 32
MAX_SAMPLE_COUNT = 100
MAX_MODEL_EXPONENT = 32


class CandidateSyntaxError(ValueError):
    """Candidate rejected before calling the trusted kernel."""


def parse_candidate(text: str, phase: PhaseSpace) -> Expr:
    """Parse only arithmetic in q0,..,p0,.., never eval or exec.

    Grammar: integers; q0, p0; +, -, *, /, ** with bounded integer exponent.
    Optional prefix `Q =` or `candidate =` is accepted. All other Python
    constructs (calls, attributes, floats, lists, comprehensions) fail closed.
    """
    if not isinstance(text, str) or len(text) > MAX_TEXT_CHARS:
        raise CandidateSyntaxError("candidato excede 4096 caracteres")
    source = text.strip()
    for prefix in ("Q =", "Q=", "candidate =", "candidate="):
        if source.startswith(prefix):
            source = source[len(prefix):].strip()
            break
    if not source or "\n" in source or "\r" in source:
        raise CandidateSyntaxError("cada candidato deve conter uma única expressão")
    try:
        node = ast.parse(source, mode="eval")
    except (SyntaxError, ValueError) as error:
        raise CandidateSyntaxError("sintaxe inválida") from error
    quota = [MAX_PARSE_NODES]
    coordinate_names = {f"q{i}": phase.coordinate(i) for i in range(phase.pairs)}
    coordinate_names.update({f"p{i}": phase.coordinate(phase.pairs + i) for i in range(phase.pairs)})

    def visit(n: ast.AST, depth: int) -> Expr:
        quota[0] -= 1
        if quota[0] < 0 or depth > MAX_PARSE_DEPTH:
            raise CandidateSyntaxError("complexidade do candidato excedida")
        if isinstance(n, ast.Constant):
            if type(n.value) is not int:
                raise CandidateSyntaxError("somente constantes inteiras exatas são admitidas")
            return phase.constant(n.value)
        if isinstance(n, ast.Name):
            if n.id not in coordinate_names:
                raise CandidateSyntaxError(f"variável desconhecida: {n.id!r}")
            return coordinate_names[n.id]
        if isinstance(n, ast.UnaryOp):
            if isinstance(n.op, ast.USub):
                return -visit(n.operand, depth+1)
            if isinstance(n.op, ast.UAdd):
                return visit(n.operand, depth+1)
            raise CandidateSyntaxError("operador unário não permitido")
        if isinstance(n, ast.BinOp):
            if isinstance(n.op, ast.Pow):
                if type(n.right) is not ast.Constant or type(n.right.value) is not int:
                    raise CandidateSyntaxError("potência deve ter expoente inteiro literal")
                exponent = n.right.value
                if not 0 <= exponent <= MAX_MODEL_EXPONENT:
                    raise CandidateSyntaxError("expoente fora do limite 0..32")
                return visit(n.left, depth+1) ** exponent
            left = visit(n.left, depth+1)
            right = visit(n.right, depth+1)
            if isinstance(n.op, ast.Add):
                return left + right
            if isinstance(n.op, ast.Sub):
                return left - right
            if isinstance(n.op, ast.Mult):
                return left * right
            if isinstance(n.op, ast.Div):
                return left / right
        raise CandidateSyntaxError(f"nó AST proibido: {type(n).__name__}")

    try:
        return visit(node.body, 0)
    except (TypeError, ValueError, ZeroDivisionError, RecursionError) as error:
        if isinstance(error, CandidateSyntaxError):
            raise
        raise CandidateSyntaxError(f"candidato aritmeticamente inválido: {error}") from error


@dataclass(frozen=True, slots=True)
class CandidateReport:
    text: str
    accepted: bool
    theorem: Any | None = None
    error: str | None = None

    @property
    def digest(self) -> str | None:
        return self.theorem.digest if self.theorem is not None else None


class DiscoverySession:
    """Verify a bounded stream of untrusted text proposals, with full rejection logs."""

    __slots__ = ("kernel", "phase", "hamiltonian")

    def __init__(self, kernel: Kernel, phase: PhaseSpace, hamiltonian: Expr):
        if not isinstance(hamiltonian, Expr) or hamiltonian.space is not phase:
            raise ValueError("Hamiltoniano deve pertencer ao espaço de fase")
        self.kernel, self.phase, self.hamiltonian = kernel, phase, hamiltonian

    def verify(self, proposals: Iterable[str], *, limit: int = 32, stop_on_first: bool = False) -> list[CandidateReport]:
        if type(limit) is not int or not 1 <= limit <= MAX_SAMPLE_COUNT:
            raise ValueError("limit deve estar entre 1 e 100")
        reports: list[CandidateReport] = []
        seen: set[str] = set()
        for number, raw in enumerate(proposals):
            if number >= limit:
                break
            if not isinstance(raw, str):
                reports.append(CandidateReport(repr(type(raw)), False, error="proposta deve ser texto"))
                continue
            if raw in seen:
                reports.append(CandidateReport(raw[:MAX_TEXT_CHARS], False, error="candidato duplicado"))
                continue
            seen.add(raw)
            try:
                candidate = parse_candidate(raw, self.phase)
                theorem = self.kernel.verify_conservation(self.phase, hamiltonian=self.hamiltonian, candidate=candidate)
            except (CandidateSyntaxError, ValueError, OverflowError, RecursionError, MemoryError) as error:
                reports.append(CandidateReport(raw[:MAX_TEXT_CHARS], False, error=str(error)))
            else:
                reports.append(CandidateReport(raw, True, theorem=theorem))
                if stop_on_first:
                    break
        return reports

    def run_sampler(self, sampler: Callable[[str, int], Iterable[str]], *, prompt: str, count: int = 8) -> list[CandidateReport]:
        if type(count) is not int or not 1 <= count <= MAX_SAMPLE_COUNT:
            raise ValueError("count deve estar entre 1 e 100")
        return self.verify(sampler(prompt, count), limit=count)


class NablaCheckpointSampler:
    """Optional NVIDIA/CUDA or CPU NABLA checkpoint text proposer.

    Importing this class does not import torch. The checkpoint loader uses
    torch.load(weights_only=True): it refuses arbitrary pickle objects.
    The NABLA module must be installed/trusted code and expose Cfg, GPT,
    tok_from_dict, and generate from nabla_gpt_cuda.py.
    """

    __slots__ = ("_nabla", "_model", "_tokenizer", "_device", "_max_new", "_seed")

    def __init__(self, nabla: Any, model: Any, tokenizer: Any, device: str, max_new: int, seed: int):
        self._nabla, self._model, self._tokenizer = nabla, model, tokenizer
        self._device, self._max_new, self._seed = device, max_new, seed

    @classmethod
    def from_checkpoint(cls, path: str | Path, *, module: str = "nabla_gpt_cuda", device: str = "cpu",
                        use_ema: bool = True, max_new: int = 80, seed: int = 0) -> NablaCheckpointSampler:
        if type(max_new) is not int or not 1 <= max_new <= 1024:
            raise ValueError("max_new deve estar entre 1 e 1024")
        import importlib
        import torch  # Lazy: GPU dependency remains outside the trusted kernel.
        nabla = importlib.import_module(module)
        # Safe checkpoint load: explicitly DO NOT use nabla.load_ckpt(weights_only=False).
        checkpoint = torch.load(str(path), map_location=device, weights_only=True)
        config = nabla.Cfg(**checkpoint["cfg"])
        model = nabla.GPT(config).to(device)
        state = checkpoint.get("ema") if use_ema and checkpoint.get("ema") is not None else checkpoint["model"]
        model.load_state_dict(state, strict=True)
        model.eval()
        tokenizer = nabla.tok_from_dict(checkpoint["tok"])
        return cls(nabla, model, tokenizer, device, max_new, seed)

    def __call__(self, prompt: str, count: int) -> Iterable[str]:
        if type(count) is not int or not 1 <= count <= MAX_SAMPLE_COUNT:
            raise ValueError("count deve estar entre 1 e 100")
        results = self._nabla.generate(self._model, self._tokenizer, self._device,
                                        n=count, prompt=prompt, max_new=self._max_new, seed=self._seed)
        if not isinstance(results, list) or len(results) > count:
            raise ValueError("NABLA retornou amostras inválidas")
        return results
