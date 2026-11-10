"""NABLA proposer boundary is tested without importing PyTorch or requiring CUDA."""
from __future__ import annotations

import sys
from types import ModuleType, SimpleNamespace
from unittest import TestCase
from unittest.mock import patch

from mlib_core import NablaCheckpointSampler


class _FakeModel:
    def __init__(self, config):
        self.config = config
        self.loaded = None

    def to(self, device):
        return self

    def load_state_dict(self, state, strict):
        assert strict is True
        self.loaded = state

    def eval(self):
        return self


class NablaBoundaryTests(TestCase):
    def test_weight_checkpoint_is_loaded_restrictively(self):
        observed = {}
        torch = ModuleType("torch")

        def load(path, map_location, weights_only):
            observed.update(path=path, map_location=map_location, weights_only=weights_only)
            return {"cfg": {"vocab": 4}, "model": {"w": "tensor stub"}, "tok": {"kind": "char", "chars": ["q", "0"]}}

        torch.load = load
        nabla = ModuleType("nabla_gpt_cuda")
        nabla.Cfg = lambda **x: SimpleNamespace(**x)
        nabla.GPT = _FakeModel
        nabla.tok_from_dict = lambda x: x
        nabla.generate = lambda model, tok, device, **kw: ["Q = q0"] * kw["n"]
        with patch.dict(sys.modules, {"torch": torch, "nabla_gpt_cuda": nabla}):
            sampler = NablaCheckpointSampler.from_checkpoint("fake.pt", device="cpu", use_ema=False)
            self.assertTrue(observed["weights_only"])
            self.assertEqual(observed["path"], "fake.pt")
            self.assertEqual(list(sampler("Q = ", 2)), ["Q = q0", "Q = q0"])

    def test_sampler_rejects_excessive_batch_size(self):
        sampler = NablaCheckpointSampler(None, None, None, "cpu", 8, 0)
        with self.assertRaises(ValueError):
            sampler("Q = ", 101)

    def test_sampler_rejects_nonlist_return(self):
        sampler = NablaCheckpointSampler(SimpleNamespace(generate=lambda *a, **k: "bad"), None, None, "cpu", 8, 0)
        with self.assertRaises(ValueError):
            sampler("Q = ", 1)
