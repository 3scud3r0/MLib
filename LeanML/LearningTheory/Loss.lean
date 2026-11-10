module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section

open scoped ENNReal NNReal

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LeanML.LearningTheory
variable {X Y H : Type*}

/-- The population risk is a Bochner integral; meaningful use requires integrability. -/
def populationRisk [MeasurableSpace (X × Y)] (μ : Measure (X × Y))
    (loss : Y → Y → ℝ) (hypothesis : X → Y) : ℝ :=
  ∫ z, loss (hypothesis z.1) z.2 ∂μ

/-- The empty-sample value is zero by convention. Statistical statements use `n > 0`. -/
def empiricalRisk {n : ℕ} (sample : Fin n → X × Y) (loss : Y → Y → ℝ)
    (hypothesis : X → Y) : ℝ := (∑ i, loss (hypothesis (sample i).1) (sample i).2)/n

theorem empiricalRisk_nonneg {n : ℕ} (sample : Fin n → X × Y) (loss : Y → Y → ℝ)
    (h : X → Y) (hloss : ∀ a b, 0 ≤ loss a b) : 0 ≤ empiricalRisk sample loss h := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => hloss _ _) (Nat.cast_nonneg n)

/-- Uniform deviation and approximate ERM imply the usual excess-risk bound. -/
theorem erm_excessRisk (risk empirical : H → ℝ) (ε δ : ℝ) (h hstar : H)
    (hdev : ∀ g, |empirical g-risk g| ≤ ε)
    (herm : empirical h ≤ empirical hstar+δ) : risk h ≤ risk hstar+2*ε+δ := by
  have h₁ := abs_le.mp (hdev h)
  have h₂ := abs_le.mp (hdev hstar)
  linarith
end LeanML.LearningTheory

noncomputable section
open MeasureTheory
namespace LeanML.LearningTheory
variable {Ω H : Type*} [MeasurableSpace Ω] [Fintype H]

/-- Union-bound step turning pointwise tail estimates into finite-class uniform control. -/
theorem finiteClass_uniformDeviation (μ : Measure Ω) (risk : H → ℝ)
    (empirical : Ω → H → ℝ) (ε : ℝ) (δ : ℝ≥0∞)
    (htail : ∀ h, μ {s | ε < |empirical s h-risk h|} ≤ δ) :
    μ {s | ∃ h, ε < |empirical s h-risk h|} ≤ (Fintype.card H)*δ := by
  have hu := measure_iUnion_fintype_le μ (fun h => {s | ε < |empirical s h-risk h|})
  have hs : (∑ h : H, μ {s | ε < |empirical s h-risk h|}) ≤ ∑ _ : H, δ :=
    Finset.sum_le_sum fun h _ => htail h
  simpa [Set.ofPred_exists] using hu.trans hs

/-- A finite-class ERM generalization bound, with sampling tail assumptions exposed. -/
theorem finiteClass_erm_bound (μ : Measure Ω) (risk : H → ℝ)
    (empirical : Ω → H → ℝ) (learner : Ω → H) (reference : H)
    (ε optimizationError : ℝ) (δ : ℝ≥0∞)
    (htail : ∀ h, μ {s | ε < |empirical s h-risk h|} ≤ δ)
    (herm : ∀ s, empirical s (learner s) ≤ empirical s reference+optimizationError) :
    μ {s | risk reference+2*ε+optimizationError < risk (learner s)} ≤ (Fintype.card H)*δ := by
  apply le_trans (measure_mono (show
    {s | risk reference+2*ε+optimizationError < risk (learner s)} ⊆
    {s | ∃ h, ε < |empirical s h-risk h|} from ?_))
    (finiteClass_uniformDeviation μ risk empirical ε δ htail)
  intro s hs
  by_contra hn
  have hdev : ∀ h, |empirical s h-risk h| ≤ ε := by
    simpa only [Set.mem_ofPred_eq, not_exists, not_lt] using hn
  have bound := erm_excessRisk risk (empirical s) ε optimizationError
    (learner s) reference hdev (herm s)
  exact (not_lt_of_ge bound) hs
end LeanML.LearningTheory
