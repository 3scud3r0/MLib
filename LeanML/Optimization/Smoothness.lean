module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Abel

@[expose] public section

/-! # Smooth objectives
The gradient condition is essential: Lipschitzness of an unrelated vector field
cannot imply a bound on the objective. All derivatives below are genuine Fréchet derivatives.
-/
noncomputable section
open Set InnerProductSpace
namespace LeanML.Optimization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A differentiable objective with a positive global Lipschitz bound on its gradient. -/
structure IsLSmooth (f : E → ℝ) (g : E → E) (L : ℝ) : Prop where
  constant_pos : 0 < L
  hasGradient : ∀ x, HasGradientAt f (g x) x
  lipschitz : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖

/-- First-order strong convexity, with a specified genuine gradient. -/
structure IsStronglyConvex (f : E → ℝ) (g : E → E) (μ : ℝ) : Prop where
  constant_pos : 0 < μ
  hasGradient : ∀ x, HasGradientAt f (g x) x
  lower_model : ∀ x y, f x + inner ℝ (g x) (y-x) + μ/2 * ‖y-x‖^2 ≤ f y

/-- Descent lemma, proved by monotonicity of the quadratic-corrected line restriction. -/
theorem descent_lemma {f : E → ℝ} {g : E → E} {L : ℝ}
    (hf : IsLSmooth f g L) (x y : E) :
    f y ≤ f x + inner ℝ (g x) (y-x) + L/2 * ‖y-x‖^2 := by
  let d := y-x
  let φ := fun t : ℝ => f (x+t • d) - f x - t * inner ℝ (g x) d - L/2*t^2*‖d‖^2
  let φ' := fun t : ℝ => inner ℝ (g (x+t • d)) d - inner ℝ (g x) d - L*t*‖d‖^2
  have hφ : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x+s • d) d t := by
      simpa only [one_smul] using ((hasDerivAt_id' t).smul_const d).const_add x
    have hcomp : HasDerivAt (fun s : ℝ => f (x+s • d))
        (inner ℝ (g (x+t • d)) d) t := by
      simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
        HasFDerivAt.comp_hasDerivAt t (hf.hasGradient (x+t • d)).hasFDerivAt hline
    have hquad : HasDerivAt (fun s : ℝ => L/2*s^2*‖d‖^2) (L*t*‖d‖^2) t := by
      convert (((hasDerivAt_id' t).fun_pow 2).const_mul (L/2)).mul_const (‖d‖^2) using 1; ring
    simpa only [φ, φ', one_mul] using
      ((hcomp.sub_const (f x)).fun_sub ((hasDerivAt_id' t).mul_const (inner ℝ (g x) d))).fun_sub hquad
  have hanti : AntitoneOn φ (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hφ t).continuousAt.continuousWithinAt)
      (fun t _ => (hφ t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hnorm : ‖g (x+t • d)-g x‖ ≤ L*t*‖d‖ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, mul_assoc] using
        hf.lipschitz (x+t • d) x
    have hinner := (real_inner_le_norm (g (x+t • d)-g x) d).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg d))
    rw [inner_sub_left] at hinner
    dsimp [φ']
    nlinarith
  have h := hanti (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by simp) zero_le_one
  have hxy : x+d = y := by dsimp [d]; abel
  dsimp [φ] at h
  simp only [zero_smul, add_zero, zero_mul, sub_self, one_smul,
    one_mul, one_pow, mul_one, hxy] at h
  dsimp [d] at h
  nlinarith

/-- One gradient step of size `1/L` decreases the loss. -/
theorem gradient_descent_step_decreases {f : E → ℝ} {g : E → E} {L : ℝ}
    (hf : IsLSmooth f g L) (x : E) :
    f (x-(1/L) • g x) ≤ f x - (1/(2*L))*‖g x‖^2 := by
  have h := descent_lemma hf x (x-(1/L) • g x)
  have hL : L ≠ 0 := ne_of_gt hf.constant_pos
  have hnonneg : 0 ≤ 1/L := le_of_lt (one_div_pos.mpr hf.constant_pos)
  simp only [sub_sub_cancel_left, inner_neg_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hnonneg, mul_pow] at h
  convert h using 1; field_simp; ring
end LeanML.Optimization
