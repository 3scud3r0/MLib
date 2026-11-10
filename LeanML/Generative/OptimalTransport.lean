module

public import LeanML.Information.Shannon

@[expose] public section

noncomputable section
open scoped BigOperators
namespace LeanML.Generative
open LeanML.Information
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A finite Kantorovich coupling with both marginal constraints enforced. -/
structure Coupling (P : FiniteDistribution X) (Q : FiniteDistribution Y) where
  mass : X → Y → ℝ
  nonneg : ∀ x y, 0 ≤ mass x y
  left_marginal : ∀ x, ∑ y, mass x y = P.mass x
  right_marginal : ∀ y, ∑ x, mass x y = Q.mass y

def Coupling.cost {P : FiniteDistribution X} {Q : FiniteDistribution Y}
    (π : Coupling P Q) (c : X → Y → ℝ) : ℝ := ∑ x, ∑ y, π.mass x y*c x y

def independentCoupling (P : FiniteDistribution X) (Q : FiniteDistribution Y) : Coupling P Q where
  mass x y := P.mass x*Q.mass y
  nonneg x y := mul_nonneg (P.nonneg x) (Q.nonneg y)
  left_marginal x := by simp [← Finset.mul_sum, Q.total]
  right_marginal y := by simp [← Finset.sum_mul, P.total]

/-- The optimal cost is an infimum over actual couplings, not over arbitrary matrices. -/
def kantorovichCost (P : FiniteDistribution X) (Q : FiniteDistribution Y)
    (c : X → Y → ℝ) : ℝ := ⨅ π : Coupling P Q, π.cost c

theorem Coupling.cost_nonneg {P : FiniteDistribution X} {Q : FiniteDistribution Y}
    (π : Coupling P Q) (c : X → Y → ℝ) (hc : ∀ x y, 0 ≤ c x y) : 0 ≤ π.cost c := by
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (π.nonneg x y) (hc x y)
end LeanML.Generative

noncomputable section
open LeanML.Information
namespace LeanML.Generative
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Nonnegative costs have nonnegative optimal transport cost. -/
theorem kantorovichCost_nonneg (P : FiniteDistribution X) (Q : FiniteDistribution Y)
    (c : X → Y → ℝ) (hc : ∀ x y, 0 ≤ c x y) : 0 ≤ kantorovichCost P Q c := by
  let : Nonempty (Coupling P Q) := ⟨independentCoupling P Q⟩
  exact le_ciInf fun π => π.cost_nonneg c hc
end LeanML.Generative
