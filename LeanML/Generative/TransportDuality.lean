module
public import LeanML.Generative.OptimalTransport
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Linarith
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.Generative
open LeanML.Information
variable {X : Type*} [Fintype X] [PseudoMetricSpace X]

omit [PseudoMetricSpace X] in
/-- A coupling converts the marginal difference of expectations to a paired expectation. -/
theorem coupling_expectation_difference (P Q : FiniteDistribution X) (π : Coupling P Q)
    (f : X → ℝ) :
    (∑ x, P.mass x*f x)-(∑ y, Q.mass y*f y) = ∑ x, ∑ y, π.mass x y*(f x-f y) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_mul, π.left_marginal]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_mul, π.right_marginal]

/-- Weak Kantorovich-Rubinstein duality for every finite coupling. -/
theorem lipschitz_potential_le_cost (P Q : FiniteDistribution X) (π : Coupling P Q)
    (f : X → ℝ) (hf : LipschitzWith 1 f) :
    (∑ x, P.mass x*f x)-(∑ y, Q.mass y*f y) ≤ π.cost (fun x y => dist x y) := by
  rw [coupling_expectation_difference P Q π f]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (π.nonneg x y)
  have h := hf.dist_le_mul x y
  have h' : |f x-f y| ≤ dist x y := by simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using h
  exact (le_abs_self _).trans h'

/-- Every admissible dual potential lower-bounds the finite optimal cost. -/
theorem lipschitz_potential_le_optimal (P Q : FiniteDistribution X) (f : X → ℝ)
    (hf : LipschitzWith 1 f) :
    (∑ x, P.mass x*f x)-(∑ y, Q.mass y*f y) ≤ kantorovichCost P Q (fun x y => dist x y) := by
  let : Nonempty (Coupling P Q) := ⟨independentCoupling P Q⟩
  exact le_ciInf fun π => lipschitz_potential_le_cost P Q π f hf
end LeanML.Generative
