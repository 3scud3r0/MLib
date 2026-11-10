module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Analysis.SpecialFunctions.Exp
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LeanML.Privacy
variable {D X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Eventwise approximate privacy, retaining extended probabilities. -/
def PrivatePair (μ ν : Measure X) (ε δ : ℝ) : Prop :=
  ∀ A, MeasurableSet A → μ A ≤ ENNReal.ofReal (Real.exp ε)*ν A+ENNReal.ofReal δ

def DifferentiallyPrivate (adjacent : D → D → Prop) (M : D → ProbabilityMeasure X)
    (ε δ : ℝ) : Prop := 0 ≤ ε ∧ 0 ≤ δ ∧
  ∀ d d', adjacent d d' → PrivatePair (M d).toMeasure (M d').toMeasure ε δ

/-- Measurable postprocessing preserves the privacy parameters. -/
theorem PrivatePair.postprocess {μ ν : Measure X} {ε δ : ℝ} (h : PrivatePair μ ν ε δ)
    (f : X → Y) (hf : Measurable f) : PrivatePair (μ.map f) (ν.map f) ε δ := by
  intro A hA
  rw [Measure.map_apply hf hA, Measure.map_apply hf hA]
  exact h (f ⁻¹' A) (hf hA)

theorem DifferentiallyPrivate.postprocess {adjacent : D → D → Prop}
    {M : D → ProbabilityMeasure X} {ε δ : ℝ} (h : DifferentiallyPrivate adjacent M ε δ)
    (f : X → Y) (hf : Measurable f) :
    DifferentiallyPrivate adjacent (fun d => (M d).map f) ε δ := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro d d' hadj
  simpa only [ProbabilityMeasure.toMeasure_map] using (h.2.2 d d' hadj).postprocess f hf
end LeanML.Privacy
