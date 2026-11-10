module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Defs.Filter

@[expose] public section

/-! # Diffusion interfaces
Time-reversal of diffusions requires analytic and stochastic hypotheses beyond
this interface. No reversal or convergence theorem is asserted here.
-/
noncomputable section
namespace LeanML.Generative

structure DiffusionCoefficients (E : Type*) where
  drift : ℝ → E → E
  diffusion : ℝ → E → E

/-- Weak convergence expressed through bounded continuous test functions. -/
def WeakConvergence {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (laws : ℕ → MeasureTheory.ProbabilityMeasure E)
    (limit : MeasureTheory.ProbabilityMeasure E) : Prop :=
  Filter.Tendsto laws Filter.atTop (nhds limit)

/-- Reversal of a deterministic time-indexed path, before any stochastic law is specified. -/
def reversePath {E : Type*} (horizon : ℝ) (path : ℝ → E) (t : ℝ) : E := path (horizon-t)

theorem reversePath_involutive {E : Type*} (T : ℝ) (path : ℝ → E) :
    reversePath T (reversePath T path) = path := by
  funext t
  simp [reversePath]
end LeanML.Generative
