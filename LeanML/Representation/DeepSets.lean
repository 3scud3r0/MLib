module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.Representation
variable {I X E Y : Type*} [Fintype I] [AddCommMonoid E]

/-- Sum aggregation followed by an arbitrary readout. -/
def deepSet (φ : X → E) (ρ : E → Y) (sample : I → X) : Y := ρ (∑ i, φ (sample i))

/-- The forward invariance direction holds without countability or continuity restrictions. -/
theorem deepSet_permute (φ : X → E) (ρ : E → Y) (sample : I → X) (p : Equiv.Perm I) :
    deepSet φ ρ (sample ∘ p) = deepSet φ ρ sample := by
  unfold deepSet
  congr 1
  exact Equiv.sum_comp p (fun i => φ (sample i))
end LeanML.Representation
