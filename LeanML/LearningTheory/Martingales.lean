module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Variance
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace LeanML.LearningTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Azuma-Hoeffding under explicit conditional sub-Gaussian hypotheses. -/
theorem azuma_hoeffding [StandardBorelSpace Ω] [IsZeroOrProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    (hadapted : StronglyAdapted ℱ Y) (hzero : HasSubgaussianMGF (Y 0) (c 0) μ) (n : ℕ)
    (hcond : ∀ i < n-1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i+1)) (c (i+1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-ε^2/(2*∑ i ∈ Finset.range n, c i)) :=
  ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF hadapted hzero n hcond hε

/-- Chebyshev's inequality retains the finite-second-moment prerequisite. -/
theorem chebyshev [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ε ≤ |X ω-∫ z, X z ∂μ|} ≤ ENNReal.ofReal (variance X μ/ε^2) :=
  ProbabilityTheory.meas_ge_le_variance_div_sq hX hε
end LeanML.LearningTheory
