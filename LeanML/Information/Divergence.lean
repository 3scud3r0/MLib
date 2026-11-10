module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open scoped ENNReal NNReal

noncomputable section
open MeasureTheory
namespace LeanML.Information
variable {α : Type*} [MeasurableSpace α]

/-- Extended-valued KL retains the singular case `P ≪̸ Q` as infinity. -/
def klDivergence (P Q : ProbabilityMeasure α) : ℝ≥0∞ :=
  InformationTheory.klDiv P.toMeasure Q.toMeasure

@[simp] theorem klDivergence_self (P : ProbabilityMeasure α) : klDivergence P P = 0 := by
  exact InformationTheory.klDiv_self _

/-- Gibbs equality: zero KL characterizes equality of the probability measures. -/
theorem klDivergence_eq_zero_iff (P Q : ProbabilityMeasure α) :
    klDivergence P Q = 0 ↔ P = Q := by
  rw [klDivergence, InformationTheory.klDiv_eq_zero_iff]
  exact Subtype.val_inj

/-- Jensen-Shannon divergence of measures, using their equal mixture. -/
def jensenShannon (μ ν : Measure α) : ℝ≥0∞ :=
  let mixture := (1/2 : ℝ≥0∞) • μ + (1/2 : ℝ≥0∞) • ν
  (1/2 : ℝ≥0∞)*InformationTheory.klDiv μ mixture +
    (1/2 : ℝ≥0∞)*InformationTheory.klDiv ν mixture
end LeanML.Information

noncomputable section
open MeasureTheory
namespace LeanML.Information
variable {α : Type*} [MeasurableSpace α]

theorem jensenShannon_comm (μ ν : Measure α) : jensenShannon μ ν = jensenShannon ν μ := by
  dsimp [jensenShannon]
  rw [add_comm ((1/2 : ℝ≥0∞) • ν) ((1/2 : ℝ≥0∞) • μ)]
  exact add_comm _ _
end LeanML.Information
