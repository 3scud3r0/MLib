module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

/-! # Local reverse-mode rule
The pullback acts on continuous-linear cotangents by precomposition. This rule
supports composition and shared-input forks; it does not yet implement a DAG scheduler.
-/
noncomputable section
namespace LeanML.Optimization
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def pullback (A : E →L[ℝ] F) (cotangent : F →L[ℝ] ℝ) : E →L[ℝ] ℝ := cotangent.comp A

/-- Reverse accumulation through a composition equals pullback through its derivative. -/
theorem reverse_chain_rule {f : E → F} {g : F → G} {x : E}
    {A : E →L[ℝ] F} {B : F →L[ℝ] G}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B (f x)) :
    HasFDerivAt (g ∘ f) (B.comp A) x := hg.comp x hf

/-- Cotangent propagation obeys the contravariant composition order. -/
theorem pullback_comp (A : E →L[ℝ] F) (B : F →L[ℝ] G) (c : G →L[ℝ] ℝ) :
    pullback A (pullback B c) = pullback (B.comp A) c := rfl
end LeanML.Optimization

noncomputable section
namespace LeanML.Optimization
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A typed differentiable node with its actual Fréchet derivative. -/
structure DifferentiableNode (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  eval : E → F
  derivative : E → E →L[ℝ] F
  correct : ∀ x, HasFDerivAt eval (derivative x) x

/-- Composition preserves the derivative certificate. -/
def DifferentiableNode.comp (second : DifferentiableNode F G) (first : DifferentiableNode E F) :
    DifferentiableNode E G where
  eval := second.eval ∘ first.eval
  derivative x := (second.derivative (first.eval x)).comp (first.derivative x)
  correct x := (second.correct (first.eval x)).comp x (first.correct x)

/-- Shared-input branching is a typed DAG primitive. -/
def DifferentiableNode.fork (left : DifferentiableNode E F) (right : DifferentiableNode E G) :
    DifferentiableNode E (F × G) where
  eval x := (left.eval x, right.eval x)
  derivative x := (left.derivative x).prod (right.derivative x)
  correct x := (left.correct x).prodMk (right.correct x)

/-- Reverse propagation of a continuous-linear cotangent through one node. -/
def DifferentiableNode.reverse (node : DifferentiableNode E F) (x : E)
    (cotangent : F →L[ℝ] ℝ) : E →L[ℝ] ℝ := cotangent.comp (node.derivative x)

/-- The propagated cotangent is the derivative of the scalarized output. -/
theorem DifferentiableNode.reverse_correct (node : DifferentiableNode E F) (x : E)
    (cotangent : F →L[ℝ] ℝ) :
    HasFDerivAt (fun y => cotangent (node.eval y)) (node.reverse x cotangent) x :=
  cotangent.hasFDerivAt.comp x (node.correct x)

/-- A reverse pass traverses compositions in reverse evaluation order. -/
theorem DifferentiableNode.reverse_comp (second : DifferentiableNode F G)
    (first : DifferentiableNode E F) (x : E) (cotangent : G →L[ℝ] ℝ) :
    (second.comp first).reverse x cotangent =
      first.reverse x (second.reverse (first.eval x) cotangent) := rfl
end LeanML.Optimization

noncomputable section
namespace LeanML.Optimization
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Reverse accumulation adds both branch contributions at their shared input. -/
theorem DifferentiableNode.reverse_fork (left : DifferentiableNode E F)
    (right : DifferentiableNode E G) (x : E) (cotangent : F × G →L[ℝ] ℝ) :
    (left.fork right).reverse x cotangent =
      left.reverse x (cotangent.comp (ContinuousLinearMap.inl ℝ F G)) +
      right.reverse x (cotangent.comp (ContinuousLinearMap.inr ℝ F G)) := by
  ext u
  change cotangent (left.derivative x u, right.derivative x u) =
    cotangent (left.derivative x u, 0)+cotangent (0, right.derivative x u)
  rw [← map_add]
  congr 1
  simp
end LeanML.Optimization
