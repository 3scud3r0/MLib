module
public import LeanML.Information.Shannon
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open scoped BigOperators NNReal
namespace LeanML.Reinforcement
open LeanML.Information
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- A finite discounted MDP with normalized transition probabilities. -/
structure FiniteMDP (S A : Type*) [Fintype S] where
  reward : S → A → ℝ
  transition : S → A → FiniteDistribution S
  discount : ℝ≥0
  discount_lt_one : discount < 1

def actionValue (M : FiniteMDP S A) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  M.reward s a+(M.discount:ℝ)*(∑ t, (M.transition s a).mass t*V t)

def bellman (M : FiniteMDP S A) (V : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (actionValue M V s)

/-- Finite maxima cannot amplify a uniform coordinatewise perturbation. -/
theorem max_abs_sub_le (f g : A → ℝ) (C : ℝ) (h : ∀ a, |f a-g a| ≤ C) :
    |Finset.univ.sup' Finset.univ_nonempty f-Finset.univ.sup' Finset.univ_nonempty g| ≤ C := by
  apply abs_le.mpr
  have hfg : Finset.univ.sup' Finset.univ_nonempty f ≤
      Finset.univ.sup' Finset.univ_nonempty g+C := by
    apply Finset.sup'_le
    intro a _
    have h₁ := (abs_le.mp (h a)).2
    have h₂ := Finset.le_sup' g (Finset.mem_univ a)
    linarith
  have hgf : Finset.univ.sup' Finset.univ_nonempty g ≤
      Finset.univ.sup' Finset.univ_nonempty f+C := by
    apply Finset.sup'_le
    intro a _
    have h₁ := (abs_le.mp (h a)).1
    have h₂ := Finset.le_sup' f (Finset.mem_univ a)
    linarith
  constructor <;> linarith

/-- Averaging by a probability vector is nonexpansive in the supremum norm. -/
theorem transition_nonexpansive (p : FiniteDistribution S) (U V : S → ℝ) :
    |(∑ t, p.mass t*U t)-(∑ t, p.mass t*V t)| ≤ dist U V := by
  rw [← Finset.sum_sub_distrib]
  have he : ∀ t, p.mass t*U t-p.mass t*V t = p.mass t*(U t-V t) := by intro t; ring
  simp_rw [he]
  calc
    |∑ t, p.mass t*(U t-V t)| ≤ ∑ t, |p.mass t*(U t-V t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, p.mass t*dist U V := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (p.nonneg t)]
      apply mul_le_mul_of_nonneg_left _ (p.nonneg t)
      simpa only [Real.dist_eq] using dist_le_pi_dist U V t
    _ = dist U V := by rw [← Finset.sum_mul, p.total, one_mul]

/-- Bellman optimality is a strict contraction for discount < 1. -/
theorem bellman_contracting (M : FiniteMDP S A) : ContractingWith M.discount (bellman M) := by
  refine ⟨M.discount_lt_one, LipschitzWith.of_dist_le_mul ?_⟩
  intro U V
  apply (dist_pi_le_iff (mul_nonneg M.discount.coe_nonneg dist_nonneg)).mpr
  intro s
  rw [Real.dist_eq]
  apply max_abs_sub_le
  intro a
  have h := mul_le_mul_of_nonneg_left (transition_nonexpansive (M.transition s a) U V)
    M.discount.coe_nonneg
  dsimp only [actionValue]
  simpa only [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.discount.coe_nonneg] using h

/-- The optimality operator has one and only one value-function fixed point. -/
theorem bellman_exists_unique (M : FiniteMDP S A) : ∃! V, bellman M V = V := by
  let h := bellman_contracting M
  exact ⟨ContractingWith.fixedPoint _ h, h.fixedPoint_isFixedPt, fun _ hv => h.fixedPoint_unique hv⟩

/-- Value iteration converges from every finite initial value function. -/
theorem valueIteration_converges (M : FiniteMDP S A) (V₀ : S → ℝ) :
    Filter.Tendsto (fun n => (bellman M)^[n] V₀) Filter.atTop
      (nhds (ContractingWith.fixedPoint (bellman M) (bellman_contracting M))) :=
  (bellman_contracting M).tendsto_iterate_fixedPoint V₀
end LeanML.Reinforcement
