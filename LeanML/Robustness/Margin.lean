module
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
@[expose] public section
open scoped NNReal
namespace LeanML.Robustness
variable {X C : Type*} [PseudoMetricSpace X]

/-- Strict winning scores avoid ambiguity from ties in an argmax. -/
def StrictWinner (scores : X → C → ℝ) (x : X) (winner : C) : Prop :=
  ∀ competitor, competitor ≠ winner → scores x competitor < scores x winner

/-- Pairwise decision margins survive perturbations smaller than their Lipschitz budget. -/
theorem margin_stable (scores : X → C → ℝ) (K : ℝ≥0)
    (hLip : ∀ i, LipschitzWith K (fun x => scores x i)) (x y : X) (a b : C)
    (hm : 2*(K:ℝ)*dist y x < scores x a-scores x b) : scores y b < scores y a := by
  have ha := abs_le.mp (show |scores y a-scores x a| ≤ (K:ℝ)*dist y x by
    simpa only [Real.dist_eq] using (hLip a).dist_le_mul y x)
  have hb := abs_le.mp (show |scores y b-scores x b| ≤ (K:ℝ)*dist y x by
    simpa only [Real.dist_eq] using (hLip b).dist_le_mul y x)
  linarith

/-- The usual certified radius, with the indispensable positive Lipschitz constant. -/
theorem certified_radius (scores : X → C → ℝ) (K : ℝ≥0)
    (hLip : ∀ i, LipschitzWith K (fun x => scores x i)) (x y : X) (a b : C)
    (hK : 0 < (K:ℝ)) (r : ℝ) (hr : r < (scores x a-scores x b)/(2*(K:ℝ)))
    (hy : dist y x ≤ r) : scores y b < scores y a := by
  apply margin_stable scores K hLip x y a b
  have hm := (lt_div_iff₀ (show 0 < 2*(K:ℝ) by positivity)).mp hr
  have hd := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2*(K:ℝ) by positivity)
  nlinarith

/-- Multiclass robustness requires a positive margin against EVERY competing class. -/
theorem strictWinner_stable (scores : X → C → ℝ) (K : ℝ≥0)
    (hLip : ∀ i, LipschitzWith K (fun x => scores x i)) (x y : X) (winner : C)
    (margin : ℝ) (hmargin : ∀ j, j ≠ winner → margin ≤ scores x winner-scores x j)
    (hbudget : 2*(K:ℝ)*dist y x < margin) : StrictWinner scores y winner := by
  intro j hj
  exact margin_stable scores K hLip x y winner j (hbudget.trans_le (hmargin j hj))

omit [PseudoMetricSpace X] in
/-- A classifier that actually selects a maximum must return the unique strict winner. -/
theorem classifier_eq_of_strictWinner (scores : X → C → ℝ) (classify : X → C)
    (hmax : ∀ z i, scores z i ≤ scores z (classify z)) (y : X) (c : C)
    (hc : StrictWinner scores y c) : classify y = c := by
  by_contra h
  exact (not_lt_of_ge (hmax y c)) (hc (classify y) h)
end LeanML.Robustness
