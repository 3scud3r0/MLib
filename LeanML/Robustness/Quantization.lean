module
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
@[expose] public section
open scoped NNReal
noncomputable section
namespace LeanML.Robustness
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operator-norm weight error gives an input-uniform output error bound. -/
theorem quantization_error (W Q : E →L[ℝ] F) (x : E) (Δ B : ℝ)
    (hΔ : ‖W-Q‖ ≤ Δ) (hB : ‖x‖ ≤ B) : ‖W x-Q x‖ ≤ Δ*B := by
  have hnonneg : 0 ≤ Δ := (norm_nonneg (W-Q)).trans hΔ
  calc
    ‖W x-Q x‖ = ‖(W-Q) x‖ := by rw [sub_apply]
    _ ≤ ‖W-Q‖*‖x‖ := (W-Q).le_opNorm x
    _ ≤ Δ*B := mul_le_mul hΔ hB (norm_nonneg _) hnonneg

/-- An activation multiplies quantization error by its Lipschitz constant. -/
theorem activated_quantization_error (W Q : E →L[ℝ] F) (σ : F → F) (K : ℝ≥0)
    (hσ : LipschitzWith K σ) (x : E) (Δ B : ℝ)
    (hΔ : ‖W-Q‖ ≤ Δ) (hB : ‖x‖ ≤ B) :
    ‖σ (W x)-σ (Q x)‖ ≤ (K:ℝ)*(Δ*B) := by
  exact (show ‖σ (W x)-σ (Q x)‖ ≤ (K:ℝ)*‖W x-Q x‖ by
    simpa only [dist_eq_norm] using hσ.dist_le_mul (W x) (Q x)).trans
      (mul_le_mul_of_nonneg_left (quantization_error W Q x Δ B hΔ hB) K.coe_nonneg)

/-- The square-root row factor is valid for a bound on EACH output coordinate. -/
theorem euclidean_coordinate_bound {I : Type*} [Fintype I]
    (e : EuclideanSpace ℝ I) (C : ℝ) (hC : 0 ≤ C) (he : ∀ i, |e i| ≤ C) :
    ‖e‖ ≤ Real.sqrt (Fintype.card I)*C := by
  have hs : ∀ i, (e i)^2 ≤ C^2 := by
    intro i
    have h := (sq_le_sq₀ (abs_nonneg (e i)) hC).mpr (he i)
    simpa only [sq_abs] using h
  apply (sq_le_sq₀ (norm_nonneg e) (mul_nonneg (Real.sqrt_nonneg _) hC)).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), EuclideanSpace.real_norm_sq_eq]
  simpa using! Finset.sum_le_sum (fun i _ => hs i)

/-- Row vectors of an entrywise matrix error in Euclidean coordinates. -/
def matrixRowError {I J : Type*} [Fintype J] (W Q : I → J → ℝ) (i : I) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => W i j-Q i j)

def matrixOutputError {I J : Type*} [Fintype I] [Fintype J]
    (W Q : I → J → ℝ) (x : EuclideanSpace ℝ J) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (fun i => inner ℝ (matrixRowError W Q i) x)

/-- Correct dimension dependence for a uniform PER-ENTRY weight error.
The factor is sqrt(rows)*sqrt(columns)*Delta*B, not merely sqrt(rows)*Delta*B.
-/
theorem entrywise_quantization_bound {I J : Type*} [Fintype I] [Fintype J]
    (W Q : I → J → ℝ) (x : EuclideanSpace ℝ J) (Δ B : ℝ)
    (hΔ : 0 ≤ Δ) (hentry : ∀ i j, |W i j-Q i j| ≤ Δ) (hB : ‖x‖ ≤ B) :
    ‖matrixOutputError W Q x‖ ≤ Real.sqrt (Fintype.card I)*(Real.sqrt (Fintype.card J)*Δ*B) := by
  have hB0 := (norm_nonneg x).trans hB
  apply euclidean_coordinate_bound _ _ (by positivity)
  intro i
  change |inner ℝ (matrixRowError W Q i) x| ≤ Real.sqrt (Fintype.card J)*Δ*B
  have hrow : ‖matrixRowError W Q i‖ ≤ Real.sqrt (Fintype.card J)*Δ := by
    apply euclidean_coordinate_bound _ Δ hΔ
    intro j
    exact hentry i j
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul hrow hB (norm_nonneg x) (by positivity))

/-- A 1×2 row of unit coefficient errors shows why a column factor cannot be omitted. -/
theorem entrywise_bound_needs_dimension : ¬ (2:ℝ) ≤ Real.sqrt 2 := by
  intro h
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2:ℝ)]
end LeanML.Robustness
