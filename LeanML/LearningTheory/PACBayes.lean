module
public import LeanML.Generative.ELBO
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.LearningTheory
open LeanML.Information LeanML.Generative
variable {H : Type*} [Fintype H]

/-- Finite KL on strictly positive probability vectors; supports are explicit in theorems. -/
def finiteKL (q p : FiniteDistribution H) : ℝ := ∑ h, q.mass h*Real.log (q.mass h/p.mass h)

/-- The change-of-measure variational inequality used in PAC-Bayesian arguments.
This theorem alone is not a high-probability PAC-Bayes sample bound.
-/
theorem changeOfMeasure (q p : FiniteDistribution H) (φ : H → ℝ)
    (hq : ∀ h, 0 < q.mass h) (hp : ∀ h, 0 < p.mass h) :
    (∑ h, q.mass h*φ h) ≤ finiteKL q p+Real.log (∑ h, p.mass h*Real.exp (φ h)) := by
  have hj : ∀ h, 0 < p.mass h*Real.exp (φ h) := fun h => mul_pos (hp h) (Real.exp_pos _)
  have bound := finiteELBO_le_logEvidence (fun h => p.mass h*Real.exp (φ h)) q hj hq
  have he : finiteELBO (fun h => p.mass h*Real.exp (φ h)) q =
      (∑ h, q.mass h*φ h)-finiteKL q p := by
    unfold finiteELBO finiteKL
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [Real.log_div (ne_of_gt (hj h)) (ne_of_gt (hq h)),
      Real.log_mul (ne_of_gt (hp h)) (Real.exp_ne_zero _), Real.log_exp,
      Real.log_div (ne_of_gt (hq h)) (ne_of_gt (hp h))]
    ring
  rw [he] at bound
  linarith

/-- Finite Gibbs inequality is a corollary of the same variational principle. -/
theorem finiteKL_nonneg (q p : FiniteDistribution H)
    (hq : ∀ h, 0 < q.mass h) (hp : ∀ h, 0 < p.mass h) : 0 ≤ finiteKL q p := by
  simpa [p.total] using changeOfMeasure q p (fun _ => 0) hq hp
end LeanML.LearningTheory
