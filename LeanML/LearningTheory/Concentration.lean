module

public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

open scoped ENNReal NNReal

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace LeanML.LearningTheory
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Hoeffding's exponential tail bound in Mathlib's sub-Gaussian parameterization.
Bounded centered variables are sub-Gaussian by Hoeffding's lemma in Mathlib.
-/
theorem hoeffding_sum {X : ι → Ω → ℝ} {c : ι → ℝ≥0} (s : Finset ι)
    (hindep : iIndepFun X μ)
    (hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-ε^2/(2*∑ i ∈ s, c i)) :=
  HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep hsub hε
end LeanML.LearningTheory

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LeanML.LearningTheory
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Hoeffding for bounded independent variables after centering by their expectations. -/
theorem hoeffding_bounded_sum {X : ι → Ω → ℝ} (s : Finset ι)
    (hindep : iIndepFun X μ) (a b : ι → ℝ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, (X i ω-∫ z, X i z ∂μ)} ≤
      Real.exp (-ε^2/(2*∑ i ∈ s, (((‖b i-a i‖₊/2)^2 : ℝ≥0) : ℝ))) := by
  have hindep' := hindep.comp (fun i x => x-∫ z, X i z ∂μ)
    (fun _ => measurable_id.sub measurable_const)
  simpa only [Function.comp_apply, NNReal.coe_sum] using
    hoeffding_sum s hindep' (fun i _ =>
      hasSubgaussianMGF_of_mem_Icc (hmeas i) (hbound i)) hε
end LeanML.LearningTheory

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LeanML.LearningTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Sample-mean Hoeffding bound. The denominator is expressed using the exact
sub-Gaussian variance proxy `((b-a)/2)^2`; it equals the standard width formula.
-/
theorem hoeffding_bounded_mean {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X μ) (a b : Fin n → ℝ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ (∑ i, (X i ω-∫ z, X i z ∂μ))/(n:ℝ)} ≤
      Real.exp (-((n:ℝ)*ε)^2/(2*∑ i, (((‖b i-a i‖₊/2)^2 : ℝ≥0) : ℝ))) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h := hoeffding_bounded_sum (μ := μ) Finset.univ hindep a b hmeas hbound
    (mul_nonneg (le_of_lt hn') hε)
  have hevent : {ω | ε ≤ (∑ i, (X i ω-∫ z, X i z ∂μ))/(n:ℝ)} =
      {ω | (n:ℝ)*ε ≤ ∑ i, (X i ω-∫ z, X i z ∂μ)} := by
    ext ω
    change (ε ≤ (∑ i, (X i ω-∫ z, X i z ∂μ))/(n:ℝ)) ↔
      (n:ℝ)*ε ≤ ∑ i, (X i ω-∫ z, X i z ∂μ)
    rw [le_div_iff₀ hn', mul_comm ε]
  rw [hevent]
  simpa using h
end LeanML.LearningTheory
