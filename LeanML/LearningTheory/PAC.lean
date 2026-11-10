module

public import LeanML.LearningTheory.Loss
public import LeanML.LearningTheory.VCDimension

@[expose] public section

noncomputable section
open MeasureTheory
namespace LeanML.LearningTheory
variable {X H : Type*} [MeasurableSpace X]

/-- Distribution-free realizable PAC specification with an explicit sample law.
The sampling interface must be instantiated with an IID product law; it is
kept explicit here to separate measurability and algorithm assumptions.
-/
def PACGuarantee (sampleLaw : ∀ n : ℕ, Measure (Fin n → X))
    (learner : ∀ n : ℕ, (Fin n → X) → H) (risk : H → ℝ)
    (sampleComplexity : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 → ∀ n, sampleComplexity ε δ ≤ n →
    (sampleLaw n) {s | ε < risk (learner n s)} ≤ ENNReal.ofReal δ
end LeanML.LearningTheory
