module
public import Mathlib.Topology.MetricSpace.Lipschitz
public import LeanML.Representation.Activation
@[expose] public section
open scoped NNReal
noncomputable section
namespace LeanML.Robustness
variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- A map together with its certified global Lipschitz bound. -/
structure LipschitzLayer (X Y : Type*) [PseudoMetricSpace X] [PseudoMetricSpace Y] where
  eval : X → Y
  bound : ℝ≥0
  certified : LipschitzWith bound eval

def LipschitzLayer.comp (second : LipschitzLayer Y Z) (first : LipschitzLayer X Y) :
    LipschitzLayer X Z where
  eval := second.eval ∘ first.eval
  bound := second.bound * first.bound
  certified := second.certified.comp first.certified

def evaluateLayers : List (LipschitzLayer X X) → X → X
  | [] => id
  | layer :: rest => evaluateLayers rest ∘ layer.eval

def layerProduct : List (LipschitzLayer X X) → ℝ≥0
  | [] => 1
  | layer :: rest => layerProduct rest * layer.bound

/-- Depth multiplies the certified layer constants. -/
theorem network_lipschitz (layers : List (LipschitzLayer X X)) :
    LipschitzWith (layerProduct layers) (evaluateLayers layers) := by
  induction layers with
  | nil => exact LipschitzWith.id
  | cons layer rest ih => exact ih.comp layer.certified

/-- A nonexpansive network cannot increase metric perturbations. -/
theorem perturbation_nonexpansive (layers : List (LipschitzLayer X X))
    (h : layerProduct layers ≤ 1) (x y : X) :
    dist (evaluateLayers layers x) (evaluateLayers layers y) ≤ dist x y := by
  have hb := (network_lipschitz layers).dist_le_mul x y
  have hreal : (layerProduct layers : ℝ) ≤ 1 := by exact_mod_cast h
  exact hb.trans (by simpa using mul_le_mul_of_nonneg_right hreal dist_nonneg)
end LeanML.Robustness
