module

public import LeanML.LearningTheory.VCDimension

@[expose] public section

open scoped BigOperators
namespace LeanML.LearningTheory
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Finite-domain Sauer-Shelah: the full number of distinct hypotheses is bounded
by the binomial sum up to VC dimension. The combinatorial proof is Mathlib's.
-/
theorem sauerShelah (H : HypothesisClass X) :
    H.card ≤ ∑ k ∈ Finset.Iic (vcDimension H), (Fintype.card X).choose k :=
  (Finset.card_le_card_shatterer H).trans (Finset.card_shatterer_le_sum_vcDim (𝒜 := H))
end LeanML.LearningTheory
