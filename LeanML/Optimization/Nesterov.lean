module

public import LeanML.Optimization.GradientDescent

@[expose] public section

noncomputable section
namespace LeanML.Optimization
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Extrapolation step used in accelerated gradient schemes. -/
def momentumPoint (β : ℝ) (x previous : E) : E := x+β • (x-previous)

/-- An accelerated step evaluates the gradient at the extrapolated point. -/
def nesterovStep (g : E → E) (η β : ℝ) (x previous : E) : E :=
  let y := momentumPoint β x previous
  y-η • g y

@[simp] theorem momentumPoint_zero (x previous : E) : momentumPoint 0 x previous = x := by
  simp [momentumPoint]

/-- Without momentum, the accelerated operator reduces to the ordinary gradient step. -/
theorem nesterovStep_zero (g : E → E) (η : ℝ) (x previous : E) :
    nesterovStep g η 0 x previous = x-η • g x := by simp [nesterovStep]
end LeanML.Optimization
