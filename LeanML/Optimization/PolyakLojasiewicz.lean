module
public import LeanML.Optimization.GradientDescent
@[expose] public section
noncomputable section
namespace LeanML.Optimization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- PL concerns a genuine gradient supplied by `IsLSmooth`; convexity is not assumed. -/
structure PolyakLojasiewicz (f : E → ℝ) (g : E → E) (μ optimum : ℝ) : Prop where
  constant_pos : 0 < μ
  lower_bound : ∀ x, optimum ≤ f x
  dominance : ∀ x, 2*μ*(f x-optimum) ≤ ‖g x‖^2

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
/-- Under PL, stationary points attain the stated global optimum. -/
theorem PolyakLojasiewicz.stationary_global {f : E → ℝ} {g : E → E} {μ optimum : ℝ}
    (h : PolyakLojasiewicz f g μ optimum) (x : E) (hx : g x = 0) : f x = optimum := by
  have hd := h.dominance x
  rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hd
  nlinarith [h.lower_bound x, h.constant_pos]

/-- Linear convergence of loss values under PL, with no convexity hypothesis. -/
theorem pl_gradientDescent_rate {f : E → ℝ} {g : E → E} {L μ optimum : ℝ}
    (hf : IsLSmooth f g L) (hpl : PolyakLojasiewicz f g μ optimum) (hμL : μ ≤ L)
    (x₀ : E) (k : ℕ) :
    f (gradientIterate g (1/L) x₀ k)-optimum ≤ (1-μ/L)^k*(f x₀-optimum) := by
  have hL := hf.constant_pos
  have hfactor : 0 ≤ 1-μ/L := sub_nonneg.mpr ((div_le_one hf.constant_pos).mpr hμL)
  have hstep : ∀ x, f (gradientStep g (1/L) x)-optimum ≤ (1-μ/L)*(f x-optimum) := by
    intro x
    have hd := gradient_descent_step_decreases hf x
    have hp := mul_le_mul_of_nonneg_left (hpl.dominance x)
      (show 0 ≤ 1/(2*L) by positivity)
    have he : (1/(2*L))*(2*μ*(f x-optimum)) = (μ/L)*(f x-optimum) := by ring
    rw [he] at hp
    dsimp [gradientStep]
    nlinarith
  induction k with
  | zero => simp [gradientIterate]
  | succ k ih =>
    calc
      f (gradientIterate g (1/L) x₀ (k+1))-optimum ≤
          (1-μ/L)*(f (gradientIterate g (1/L) x₀ k)-optimum) := hstep _
      _ ≤ (1-μ/L)*((1-μ/L)^k*(f x₀-optimum)) := mul_le_mul_of_nonneg_left ih hfactor
      _ = (1-μ/L)^(k+1)*(f x₀-optimum) := by ring
end LeanML.Optimization
