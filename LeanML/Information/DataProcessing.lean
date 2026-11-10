module

public import LeanML.Information.Divergence
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LeanML.Information
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Deterministic processing cannot increase KL. -/
theorem dataProcessing_map (P Q : ProbabilityMeasure α) (f : α → β) (hf : Measurable f) :
    InformationTheory.klDiv (P.toMeasure.map f) (Q.toMeasure.map f) ≤ klDivergence P Q :=
  InformationTheory.klDiv_map_le P.toMeasure Q.toMeasure hf

/-- The same contraction holds for a stochastic Markov kernel. -/
theorem dataProcessing_kernel (P Q : ProbabilityMeasure α) (κ : Kernel α β)
    [IsMarkovKernel κ] :
    InformationTheory.klDiv (κ ∘ₘ P.toMeasure) (κ ∘ₘ Q.toMeasure) ≤ klDivergence P Q :=
  InformationTheory.klDiv_comp_right_le P.toMeasure Q.toMeasure κ
end LeanML.Information
