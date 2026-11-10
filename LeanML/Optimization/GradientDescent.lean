module

public import Mathlib.Tactic.Abel
public import LeanML.Optimization.Smoothness
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

noncomputable section
open InnerProductSpace
namespace LeanML.Optimization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- First-order characterization of differentiable convex objectives. -/
def FirstOrderConvex (f : E → ℝ) (g : E → E) : Prop :=
  ∀ x y, f x + inner ℝ (g x) (y-x) ≤ f y

def gradientStep (g : E → E) (η : ℝ) (x : E) : E := x-η • g x

def gradientIterate (g : E → E) (η : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k+1 => gradientStep g η (gradientIterate g η x₀ k)

omit [CompleteSpace E] in
@[simp] theorem gradientIterate_zero (g : E → E) (η : ℝ) (x₀ : E) :
    gradientIterate g η x₀ 0 = x₀ := rfl

/-- Loss descent for any positive step no larger than `1/L`. -/
theorem gradientStep_descent {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hf : IsLSmooth f g L) (hη : 0 < η) (hηL : η*L ≤ 1) (x : E) :
    f (gradientStep g η x) ≤ f x-η/2*‖g x‖^2 := by
  have h := descent_lemma hf x (gradientStep g η x)
  simp only [gradientStep, sub_sub_cancel_left, inner_neg_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, mul_pow] at h
  have hprod := mul_nonneg (sub_nonneg.mpr hηL) (mul_nonneg (le_of_lt hη) (sq_nonneg ‖g x‖))
  dsimp only [gradientStep]
  nlinarith

/-- The distance potential controls the next objective gap. -/
theorem gradientStep_gap {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hf : IsLSmooth f g L) (hc : FirstOrderConvex f g)
    (hη : 0 < η) (hηL : η*L ≤ 1) (x z : E) :
    2*η*(f (gradientStep g η x)-f z) ≤ ‖x-z‖^2-‖gradientStep g η x-z‖^2 := by
  have hd := gradientStep_descent hf hη hηL x
  have hcx := hc x z
  have hn : ‖gradientStep g η x-z‖^2 =
      ‖x-z‖^2-2*η*inner ℝ (g x) (x-z)+η^2*‖g x‖^2 := by
    have heq : gradientStep g η x-z = (x-z)-η • g x := by
      dsimp [gradientStep]; abel
    rw [heq, norm_sub_sq_real, inner_smul_right, real_inner_comm (x-z) (g x),
      norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow]
    ring
  have hi : inner ℝ (g x) (z-x) = -inner ℝ (g x) (x-z) := by
    rw [← inner_neg_right, neg_sub]
  rw [hi] at hcx
  have hm := mul_le_mul_of_nonneg_left (show f (gradientStep g η x)-f z ≤
      inner ℝ (g x) (x-z)-η/2*‖g x‖^2 by linarith) (show 0 ≤ 2*η by positivity)
  nlinarith

/-- Convex smooth GD has the explicit `O(1/k)` last-iterate objective bound.
No minimizer-existence assumption is hidden: `z` is any comparison point. -/
theorem gradientDescent_rate {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hf : IsLSmooth f g L) (hc : FirstOrderConvex f g)
    (hη : 0 < η) (hηL : η*L ≤ 1) (x₀ z : E) (k : ℕ) (hk : 0 < k) :
    f (gradientIterate g η x₀ k)-f z ≤ ‖x₀-z‖^2/(2*η*k) := by
  let x := gradientIterate g η x₀
  have hmono : Antitone (fun i => f (x i)) := by
    apply antitone_nat_of_succ_le
    intro i
    have hd := gradientStep_descent hf hη hηL (x i)
    change f (gradientStep g η (x i)) ≤ f (x i)
    nlinarith [sq_nonneg ‖g (x i)‖]
  have hpotential : ∀ n : ℕ,
      2*η*(n:ℝ)*(f (x n)-f z) ≤ ‖x₀-z‖^2-‖x n-z‖^2 := by
    intro n
    induction n with
    | zero => simp [x]
    | succ n ih =>
      have hstep := gradientStep_gap hf hc hη hηL (x n) z
      have horder := hmono (Nat.le_succ n)
      have hweight : 0 ≤ 2*η*(n:ℝ) := by positivity
      have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right horder (f z)) hweight
      change 2*η*(f (x (n+1))-f z) ≤ ‖x n-z‖^2-‖x (n+1)-z‖^2 at hstep
      push_cast
      nlinarith
  apply (le_div_iff₀ (show 0 < 2*η*(k:ℝ) by positivity)).mpr
  nlinarith [hpotential k, sq_nonneg ‖x k-z‖]
end LeanML.Optimization

noncomputable section
open InnerProductSpace
namespace LeanML.Optimization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Strong convexity gives the gradient-dominance estimate used in linear convergence. -/
theorem stronglyConvex_gap_bound {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hf : IsStronglyConvex f g μ) (x z : E) :
    2*μ*(f x-f z) ≤ ‖g x‖^2 := by
  have hm := hf.lower_model x z
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm (g x) (z-x))
  have hs := sq_nonneg (μ*‖z-x‖-‖g x‖)
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*μ by linarith [hf.constant_pos])
  have hip := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*μ by linarith [hf.constant_pos])
  nlinarith

/-- Linear convergence in objective value for strongly convex smooth objectives.
This states a loss bound, separately from the stronger squared-distance bound.
-/
theorem gradientDescent_linear_rate {f : E → ℝ} {g : E → E} {L μ : ℝ}
    (hf : IsLSmooth f g L) (hstrong : IsStronglyConvex f g μ) (hμL : μ ≤ L)
    (x₀ z : E) (k : ℕ) :
    f (gradientIterate g (1/L) x₀ k)-f z ≤ (1-μ/L)^k*(f x₀-f z) := by
  have hL : 0 < L := hf.constant_pos
  have hfactor : 0 ≤ 1-μ/L := by
    apply sub_nonneg.mpr
    exact (div_le_one hL).mpr hμL
  have hstep : ∀ x, f (gradientStep g (1/L) x)-f z ≤ (1-μ/L)*(f x-f z) := by
    intro x
    have hd := gradient_descent_step_decreases hf x
    have hg := stronglyConvex_gap_bound hstrong x z
    have hscaled := mul_le_mul_of_nonneg_left hg (show 0 ≤ 1/(2*L) by positivity)
    have halg : (1/(2*L))*(2*μ*(f x-f z)) = (μ/L)*(f x-f z) := by ring
    rw [halg] at hscaled
    dsimp [gradientStep]
    nlinarith
  induction k with
  | zero => simp [gradientIterate]
  | succ k ih =>
    calc
      f (gradientIterate g (1/L) x₀ (k+1))-f z ≤
          (1-μ/L)*(f (gradientIterate g (1/L) x₀ k)-f z) := hstep _
      _ ≤ (1-μ/L)*((1-μ/L)^k*(f x₀-f z)) := mul_le_mul_of_nonneg_left ih hfactor
      _ = (1-μ/L)^(k+1)*(f x₀-f z) := by ring
end LeanML.Optimization

noncomputable section
open InnerProductSpace Set
namespace LeanML.Optimization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Connect Mathlib's convexity definition to the first-order gradient characterization. -/
theorem firstOrderConvex_of_convexOn {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x) :
    FirstOrderConvex f g := by
  intro x y
  let φ : ℝ → ℝ := fun t => f (x+t • (y-x))
  have hcφ : ConvexOn ℝ Set.univ φ := by
    simpa [φ, Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
      hc.comp_affineMap (AffineMap.lineMap x y)
  have hline : HasDerivAt (fun t : ℝ => x+t • (y-x)) (y-x) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (0:ℝ)).smul_const (y-x)).const_add x
  have hφ : HasDerivAt φ (inner ℝ (g x) (y-x)) 0 := by
    have hh := (hg x).hasFDerivAt
    have hh' : HasFDerivAt f (InnerProductSpace.toDual ℝ E (g x)) (x+(0:ℝ) • (y-x)) := by
      simpa using hh
    simpa [φ, Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      hh'.comp_hasDerivAt 0 hline
  have hs := hcφ.le_slope_of_hasDerivAt (Set.mem_univ (0:ℝ))
    (Set.mem_univ (1:ℝ)) zero_lt_one hφ
  simp [slope_def_field, φ] at hs
  linarith

/-- Standard convex formulation of the last-iterate `O(1/k)` gradient descent bound. -/
theorem gradientDescent_convex_rate {f : E → ℝ} {g : E → E} {L η : ℝ}
    (hf : IsLSmooth f g L) (hc : ConvexOn ℝ Set.univ f)
    (hη : 0 < η) (hηL : η*L ≤ 1) (x₀ z : E) (k : ℕ) (hk : 0 < k) :
    f (gradientIterate g η x₀ k)-f z ≤ ‖x₀-z‖^2/(2*η*k) :=
  gradientDescent_rate hf (firstOrderConvex_of_convexOn hc hf.hasGradient) hη hηL x₀ z k hk
end LeanML.Optimization
