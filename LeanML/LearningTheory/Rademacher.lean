module

public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


noncomputable section
open scoped BigOperators
namespace LeanML.LearningTheory
variable {X H : Type*}

/-- Correlation with a fixed Rademacher sign sample. -/
def signedCorrelation {n : ℕ} (sample : Fin n → X) (signs : Fin n → Bool)
    (f : X → ℝ) : ℝ := (∑ i, (if signs i then 1 else -1)*f (sample i))/n

/-- Finite-class empirical Rademacher complexity: average of the supremum over all signs. -/
def empiricalRademacher [Fintype H] [Nonempty H] {n : ℕ}
    (sample : Fin n → X) (hypotheses : H → X → ℝ) : ℝ :=
  (∑ signs : Fin n → Bool, Finset.univ.sup' Finset.univ_nonempty (fun h : H => signedCorrelation sample signs (hypotheses h)))/(2^n)
end LeanML.LearningTheory
