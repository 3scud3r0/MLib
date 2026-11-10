module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Operator.Basic
@[expose] public section
open scoped NNReal
noncomputable section
namespace LeanML.Robustness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- DEQ update; the activation's Lipschitz hypothesis is indispensable. -/
def deqUpdate (σ : E → E) (W : E →L[ℝ] E) (x : E) (h : E) : E := σ (W h+x)

omit [CompleteSpace E] in
theorem deq_contracting (σ : E → E) (W : E →L[ℝ] E) (x : E)
    (hσ : LipschitzWith 1 σ) (hW : ‖W‖₊ < 1) :
    ContractingWith ‖W‖₊ (deqUpdate σ W x) := by
  refine ⟨hW, ?_⟩
  have hw : LipschitzWith ‖W‖₊ (W : E → E) :=
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (f := W) le_rfl
  apply LipschitzWith.of_dist_le_mul
  intro a b
  dsimp only [deqUpdate]
  have hs := hσ.dist_le_mul (W a+x) (W b+x)
  simp only [NNReal.coe_one, one_mul, dist_add_right] at hs
  exact hs.trans (hw.dist_le_mul a b)

/-- Banach gives a unique equilibrium on the complete hidden-state space. -/
theorem deq_exists_unique (σ : E → E) (W : E →L[ℝ] E) (x : E)
    (hσ : LipschitzWith 1 σ) (hW : ‖W‖₊ < 1) : ∃! h, deqUpdate σ W x h = h := by
  let hc := deq_contracting σ W x hσ hW
  exact ⟨ContractingWith.fixedPoint _ hc, hc.fixedPoint_isFixedPt, fun _ hz => hc.fixedPoint_unique hz⟩

/-- Picard iteration converges to that equilibrium. -/
theorem deq_iterates_converge (σ : E → E) (W : E →L[ℝ] E) (x start : E)
    (hσ : LipschitzWith 1 σ) (hW : ‖W‖₊ < 1) :
    Filter.Tendsto (fun n => (deqUpdate σ W x)^[n] start) Filter.atTop
      (nhds (ContractingWith.fixedPoint (deqUpdate σ W x) (deq_contracting σ W x hσ hW))) :=
  (deq_contracting σ W x hσ hW).tendsto_iterate_fixedPoint start
end LeanML.Robustness
