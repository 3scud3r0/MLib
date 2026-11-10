module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section
open scoped BigOperators
namespace LeanML.Representation
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Periodic finite-group convolution. -/
def convolution (kernel signal : G → ℝ) (x : G) : ℝ := ∑ y, kernel y*signal (x-y)

def translate (a : G) (signal : G → ℝ) (x : G) : ℝ := signal (x-a)

/-- Shared convolution kernels commute with translations. -/
theorem convolution_translate (kernel signal : G → ℝ) (a : G) :
    convolution kernel (translate a signal) = translate a (convolution kernel signal) := by
  funext x
  unfold convolution translate
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  abel
end LeanML.Representation
