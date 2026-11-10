module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanML.Optimization.GradientDescent
@[expose] public section
noncomputable section
namespace LeanML.Optimization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A feasible point in the adjoint range is the minimum-norm interpolant. -/
theorem adjoint_interpolant_pythagoras (A : E →L[ℝ] F) (u y : F)
    (hu : A (A.adjoint u) = y) (v : E) (hv : A v = y) :
    ‖v‖^2 = ‖A.adjoint u‖^2+‖v-A.adjoint u‖^2 := by
  have hzero : A (v-A.adjoint u) = 0 := by rw [map_sub, hv, hu, sub_self]
  have hi : inner ℝ (A.adjoint u) (v-A.adjoint u) = 0 := by
    rw [A.adjoint_inner_left, hzero, inner_zero_right]
  have hn := norm_add_sq_real (A.adjoint u) (v-A.adjoint u)
  have he : A.adjoint u+(v-A.adjoint u) = v := by abel
  rw [he, hi] at hn
  nlinarith

theorem adjoint_interpolant_minimum_norm (A : E →L[ℝ] F) (u y : F)
    (hu : A (A.adjoint u) = y) (v : E) (hv : A v = y) : ‖A.adjoint u‖ ≤ ‖v‖ := by
  have h := adjoint_interpolant_pythagoras A u y hu v hv
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖v-A.adjoint u‖])

/-- Least-squares gradients belong to the adjoint range. -/
def leastSquaresGradient (A : E →L[ℝ] F) (y : F) (w : E) : E := A.adjoint (A w-y)

/-- Updates preserve the adjoint range, the geometric source of minimum-norm bias. -/
theorem leastSquares_range_step (A : E →L[ℝ] F) (y : F) (η : ℝ) (u : F) :
    A.adjoint u-η • leastSquaresGradient A y (A.adjoint u) =
      A.adjoint (u-η • (A (A.adjoint u)-y)) := by
  simp only [leastSquaresGradient, map_sub, map_smul]
end LeanML.Optimization
