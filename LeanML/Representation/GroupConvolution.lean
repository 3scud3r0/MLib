module
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.LinearMap.Basic
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.Representation
variable {G : Type*} [Group G] [Fintype G]

def leftTranslate (a : G) (f : G → ℝ) (x : G) : ℝ := f (a⁻¹*x)

/-- Finite-group convolution with the signal in the first factor. -/
def groupConvolution (f k : G → ℝ) (x : G) : ℝ := ∑ y, f y*k (y⁻¹*x)

/-- Noncommutative finite-group equivariance follows by Haar/counting reindexing. -/
theorem groupConvolution_equivariant (a : G) (f k : G → ℝ) :
    groupConvolution (leftTranslate a f) k = leftTranslate a (groupConvolution f k) := by
  funext x
  unfold groupConvolution leftTranslate
  rw [← Equiv.sum_comp (Equiv.mulLeft a) (fun y => f (a⁻¹*y)*k (y⁻¹*x))]
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, mul_inv_rev, mul_assoc]
end LeanML.Representation

namespace LeanML.Representation
variable {G : Type*} [Group G] [Fintype G]

noncomputable def identitySpike : G → ℝ := by
  classical
  exact fun g => if g=1 then 1 else 0

/-- Finite-group classification: every linear translation-equivariant operator is a convolution. -/
theorem equivariant_linear_is_convolution (T : (G → ℝ) →ₗ[ℝ] (G → ℝ))
    (hT : ∀ a f, T (leftTranslate a f) = leftTranslate a (T f)) :
    ∃ k : G → ℝ, ∀ f, T f = groupConvolution f k := by
  classical
  refine ⟨T identitySpike, ?_⟩
  intro f
  have hf : f = ∑ g : G, f g • leftTranslate g (identitySpike : G → ℝ) := by
    funext x
    simp [leftTranslate, identitySpike, inv_mul_eq_one, eq_comm]
  funext x
  calc
    T f x = T (∑ g : G, f g • leftTranslate g (identitySpike : G → ℝ)) x := congrArg (fun h => T h x) hf
    _ = ∑ g, f g*T (leftTranslate g (identitySpike : G → ℝ)) x := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = groupConvolution f (T identitySpike) x := by
      unfold groupConvolution
      apply Finset.sum_congr rfl
      intro g _
      rw [hT]
      rfl
end LeanML.Representation
