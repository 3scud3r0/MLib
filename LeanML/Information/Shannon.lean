module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace LeanML.Information

/-- A finite probability vector, permitting zero probabilities. -/
structure FiniteDistribution (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

variable {α : Type*} [Fintype α]

/-- Natural-log Shannon entropy; `negMulLog 0 = 0`. -/
def shannonEntropy (p : FiniteDistribution α) : ℝ := ∑ i, Real.negMulLog (p.mass i)

lemma FiniteDistribution.mass_le_one (p : FiniteDistribution α) (i : α) : p.mass i ≤ 1 := by
  rw [← p.total]
  exact Finset.single_le_sum (fun j _ => p.nonneg j) (Finset.mem_univ i)

theorem shannonEntropy_nonneg (p : FiniteDistribution α) : 0 ≤ shannonEntropy p := by
  exact Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (p.nonneg i) (p.mass_le_one i)

/-- Extract finite masses from an actual probability measure. -/
def FiniteDistribution.ofProbabilityMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : ProbabilityMeasure α) : FiniteDistribution α where
  mass i := (P.toMeasure {i}).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top P.toMeasure {i})]
    simp

/-- Entropy upper bound: no strictly-positive-support assumption is needed. -/
theorem shannonEntropy_le_log_card [Nonempty α] (p : FiniteDistribution α) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hw : ∑ _ : α, (1/n) = 1 := by simp [n, ne_of_gt hn]
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : α => (1/n)) (p := p.mass)
    (fun _ _ => le_of_lt (one_div_pos.mpr hn)) hw (fun i _ => p.nonneg i)
  have hleft : (∑ i : α, (1/n) • Real.negMulLog (p.mass i)) = (1/n)*shannonEntropy p := by
    simp [shannonEntropy, smul_eq_mul, Finset.mul_sum]
  have hright : (∑ i : α, (1/n) • p.mass i) = 1/n := by
    simp [smul_eq_mul, ← Finset.mul_sum, p.total]
  rw [hleft, hright] at hJ
  have hlog : Real.negMulLog (1/n) = (1/n)*Real.log n := by
    simp [Real.negMulLog_def]
  rw [hlog] at hJ
  exact (mul_le_mul_iff_right₀ (one_div_pos.mpr hn)).mp hJ
end LeanML.Information

noncomputable section
open scoped BigOperators
namespace LeanML.Information
variable {α : Type*} [Fintype α] [Nonempty α]

/-- The normalized uniform distribution on a nonempty finite type. -/
def uniformDistribution : FiniteDistribution α where
  mass _ := 1/(Fintype.card α)
  nonneg _ := by positivity
  total := by simp [ne_of_gt (show (0:ℝ) < Fintype.card α by exact_mod_cast Fintype.card_pos)]

/-- The upper entropy bound is attained by the uniform distribution. -/
theorem shannonEntropy_uniform : shannonEntropy (uniformDistribution : FiniteDistribution α) =
    Real.log (Fintype.card α) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  simp [shannonEntropy, uniformDistribution, Real.negMulLog_def, hn]

/-- Uniform maximality as a comparison of actual normalized probability vectors. -/
theorem shannonEntropy_le_uniform (p : FiniteDistribution α) :
    shannonEntropy p ≤ shannonEntropy (uniformDistribution : FiniteDistribution α) := by
  rw [shannonEntropy_uniform]
  exact shannonEntropy_le_log_card p
end LeanML.Information
