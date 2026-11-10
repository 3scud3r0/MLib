module

public import LeanML.Representation.MLP
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! # Universal approximation specification
This file states the approximation property precisely. It does not assume it
as an axiom or advertise a proof of Cybenko's theorem.
-/
noncomputable section
namespace LeanML.Representation

/-- Uniform approximation by finite-width shallow networks on a specified compact domain. -/
def UniformApproximation (input : ℕ) (K : Set (Fin input → ℝ)) (σ : ℝ → ℝ) : Prop :=
  ∀ f : (Fin input → ℝ) → ℝ, ContinuousOn f K → ∀ ε : ℝ, 0 < ε →
    ∃ width : ℕ, ∃ net : ShallowNetwork input width,
      ∀ x ∈ K, |net.eval σ x-f x| < ε

/-- The approximation property restricts to smaller domains when the same
continuous target is available on the original domain. -/
theorem approximation_restrict {input : ℕ} {K S : Set (Fin input → ℝ)} {σ : ℝ → ℝ}
    (h : UniformApproximation input K σ) (hSK : S ⊆ K)
    (f : (Fin input → ℝ) → ℝ) (hf : ContinuousOn f K) (ε : ℝ) (hε : 0 < ε) :
    ∃ width : ℕ, ∃ net : ShallowNetwork input width, ∀ x ∈ S, |net.eval σ x-f x| < ε := by
  obtain ⟨width, net, hnet⟩ := h f hf ε hε
  exact ⟨width, net, fun x hx => hnet x (hSK hx)⟩
end LeanML.Representation
