"""MLib: ergonomic Python façade + trusted Rust exact certificate checker.

Pure Python AST construction and proposer code are untrusted. The native
`_mlib_core` extension is required to produce certificates, but is imported
lazily so syntax validation can run without Rust installed.
"""
from .dsl import Expr, Kernel, PhaseSpace
from .nabla import CandidateSyntaxError, CandidateReport, DiscoverySession, NablaCheckpointSampler, parse_candidate

__all__ = [
    "Expr", "Kernel", "PhaseSpace", "CandidateSyntaxError", "CandidateReport",
    "DiscoverySession", "NablaCheckpointSampler", "parse_candidate",
    "MlibKernelContext", "PyCertifiedTheorem",
]


def __getattr__(name):
    if name in ("MlibKernelContext", "PyCertifiedTheorem"):
        from importlib import import_module
        return getattr(import_module("._mlib_core", __name__), name)
    raise AttributeError(name)
