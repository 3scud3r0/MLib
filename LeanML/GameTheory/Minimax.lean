module
public import Mathlib.Topology.Sion
public import Mathlib.Analysis.Normed.Module.Basic
@[expose] public section
namespace LeanML.GameTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Sion's minimax theorem on two nonempty compact convex strategy sets.
This is the saddle-point formulation, reused from Mathlib's proof of Sion.
Neither a nonconvex GAN nor its training algorithm satisfies these hypotheses automatically.
-/
theorem minimax_saddle {X : Set E} {Y : Set F} {payoff : E → F → ℝ}
    (hneX : X.Nonempty) (hconvX : Convex ℝ X) (hcompactX : IsCompact X)
    (hneY : Y.Nonempty) (hconvY : Convex ℝ Y) (hcompactY : IsCompact Y)
    (hlower : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => payoff x y) X)
    (hconvex : ∀ y ∈ Y, QuasiconvexOn ℝ X (fun x => payoff x y))
    (hupper : ∀ x ∈ X, UpperSemicontinuousOn (fun y => payoff x y) Y)
    (hconcave : ∀ x ∈ X, QuasiconcaveOn ℝ Y (fun y => payoff x y)) :
    ∃ x ∈ X, ∃ y ∈ Y, IsSaddlePointOn X Y payoff x y :=
  Sion.exists_isSaddlePointOn hneX hconvX hcompactX hlower hconvex
    hconvY hneY hcompactY hupper hconcave
end LeanML.GameTheory
