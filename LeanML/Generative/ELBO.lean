module

public import LeanML.Information.Shannon
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

noncomputable section
namespace LeanML.Generative

/-- Variational lower bound in its KL-gap form. A probabilistic instantiation
must additionally derive the ELBO/KL decomposition from its densities.
-/
def elboFromGap (logEvidence posteriorKL : ℝ) : ℝ := logEvidence-posteriorKL

/-- Any nonnegative variational gap yields a lower bound on log evidence. -/
theorem elbo_le_logEvidence (logEvidence posteriorKL : ℝ) (hKL : 0 ≤ posteriorKL) :
    elboFromGap logEvidence posteriorKL ≤ logEvidence := sub_le_self _ hKL

/-- The bound is tight exactly when the variational gap vanishes. -/
theorem elbo_eq_iff (logEvidence posteriorKL : ℝ) :
    elboFromGap logEvidence posteriorKL = logEvidence ↔ posteriorKL = 0 := by
  unfold elboFromGap
  constructor <;> intro h <;> linarith
end LeanML.Generative

-- The following finite-latent ELBO is derived directly from Jensen's inequality.

noncomputable section
open scoped BigOperators
namespace LeanML.Generative
open LeanML.Information
variable {Z : Type*} [Fintype Z]

/-- Actual finite-latent ELBO from positive joint likelihoods and a variational law. -/
def finiteELBO (joint : Z → ℝ) (q : FiniteDistribution Z) : ℝ :=
  ∑ z, q.mass z*Real.log (joint z/q.mass z)

/-- Jensen's inequality proves the variational bound with all positivity assumptions explicit. -/
theorem finiteELBO_le_logEvidence (joint : Z → ℝ) (q : FiniteDistribution Z)
    (hjoint : ∀ z, 0 < joint z) (hq : ∀ z, 0 < q.mass z) :
    finiteELBO joint q ≤ Real.log (∑ z, joint z) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := q.mass) (p := fun z => joint z/q.mass z)
    (fun z _ => q.nonneg z) q.total (fun z _ => div_pos (hjoint z) (hq z))
  have hs : ∀ z, q.mass z*(joint z/q.mass z) = joint z := by
    intro z
    field_simp [ne_of_gt (hq z)]
  simpa [finiteELBO, smul_eq_mul, hs] using h
end LeanML.Generative
