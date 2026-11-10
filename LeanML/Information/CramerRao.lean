module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace LeanML.Information
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hilbert-space information inequality. In a statistical instantiation `error`
and `score` are centered L² variables and the inner identity follows from regularity.
-/
theorem information_inequality (error score : E) (hscore : 0 < ‖score‖^2)
    (hunbiased : inner ℝ error score = 1) : 1/‖score‖^2 ≤ ‖error‖^2 := by
  have h := abs_real_inner_le_norm error score
  rw [hunbiased, abs_one] at h
  have hsq := (sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1)
    (mul_nonneg (norm_nonneg error) (norm_nonneg score))).mpr h
  apply (div_le_iff₀ hscore).mpr
  nlinarith
end LeanML.Information
