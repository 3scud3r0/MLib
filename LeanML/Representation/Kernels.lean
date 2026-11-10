module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.Representation
variable {X E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

/-- Finite-feature kernels include finite-width neural tangent kernels. -/
def featureKernel (features : X → E) (x y : X) : ℝ := inner ℝ (features x) (features y)

theorem featureKernel_symmetric (features : X → E) (x y : X) :
    featureKernel features x y = featureKernel features y x := real_inner_comm _ _

/-- The Gram quadratic form is exactly a squared Hilbert norm. -/
theorem featureKernel_quadratic (features : X → E) (sample : I → X) (c : I → ℝ) :
    (∑ i, ∑ j, c i*c j*featureKernel features (sample i) (sample j)) =
      ‖∑ i, c i • features (sample i)‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, featureKernel]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [real_inner_comm, mul_assoc]

/-- A finite NTK is positive semidefinite for every parameter feature map. -/
theorem finiteNTK_psd (features : X → E) (sample : I → X) (c : I → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*featureKernel features (sample i) (sample j) := by
  rw [featureKernel_quadratic]
  exact sq_nonneg _
end LeanML.Representation
