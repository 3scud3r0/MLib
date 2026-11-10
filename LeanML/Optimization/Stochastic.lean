module

public import LeanML.Optimization.GradientDescent

@[expose] public section

noncomputable section
namespace LeanML.Optimization
variable {E Ω : Type*} [AddCommGroup E] [Module ℝ E]

/-- A sample-dependent stochastic gradient update. -/
def stochasticStep (G : E → Ω → E) (η : ℝ) (x : E) (ω : Ω) : E := x-η • G x ω

/-- Classical Robbins-Monro step-size requirements. This is a hypothesis, not a convergence claim. -/
def RobbinsMonroSteps (η : ℕ → ℝ) : Prop :=
  (∀ n, 0 < η n) ∧ ¬Summable η ∧ Summable (fun n => (η n)^2)

theorem stochasticStep_deterministic (g : E → E) (η : ℝ) (x : E) (ω : Ω) :
    stochasticStep (fun x _ => g x) η x ω = x-η • g x := rfl
end LeanML.Optimization
