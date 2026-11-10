module
public import LeanML.Information.Shannon
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.Reliability
open LeanML.Information
variable {G : Type*} [Fintype G]

def meanFrequency (weights : FiniteDistribution G) (frequency : G → ℝ) : ℝ :=
  ∑ g, weights.mass g*frequency g

def groupedBrier (weights : FiniteDistribution G) (forecast frequency : G → ℝ) : ℝ :=
  ∑ g, weights.mass g*(frequency g*(forecast g-1)^2+(1-frequency g)*(forecast g)^2)

def reliability (weights : FiniteDistribution G) (forecast frequency : G → ℝ) : ℝ :=
  ∑ g, weights.mass g*(forecast g-frequency g)^2

def resolution (weights : FiniteDistribution G) (frequency : G → ℝ) : ℝ :=
  ∑ g, weights.mass g*(frequency g-meanFrequency weights frequency)^2

/-- Exact finite-group calibration/resolution/uncertainty decomposition.
The identity is algebraic; interpreting frequencies as probabilities additionally
requires that they belong to [0,1]. It does not assume forecasts are calibrated.
-/
theorem brier_decomposition (weights : FiniteDistribution G) (forecast frequency : G → ℝ) :
    groupedBrier weights forecast frequency =
      meanFrequency weights frequency*(1-meanFrequency weights frequency)-
      resolution weights frequency+reliability weights forecast frequency := by
  let m := meanFrequency weights frequency
  have hp : ∀ g, weights.mass g*(frequency g*(forecast g-1)^2+(1-frequency g)*(forecast g)^2) =
      weights.mass g*(forecast g-frequency g)^2-weights.mass g*(frequency g-m)^2+
      weights.mass g*frequency g-2*m*(weights.mass g*frequency g)+m^2*weights.mass g := by
    intro g
    ring
  unfold groupedBrier
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [weights.total]
  change reliability weights forecast frequency-resolution weights frequency+
    m-2*m*m+m^2*1 = m*(1-m)-resolution weights frequency+reliability weights forecast frequency
  ring
end LeanML.Reliability
