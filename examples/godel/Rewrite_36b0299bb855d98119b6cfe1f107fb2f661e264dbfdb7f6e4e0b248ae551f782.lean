module
public import LeanML.Programs.VerifiedRewrite
@[expose] public section
noncomputable section
open LeanML.Programs
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
-- Generated fallback branches may be unused for a particular expression.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace LeanML.Generated.Cert_36b0299bb855d98119b6cfe1f107fb2f661e264dbfdb7f6e4e0b248ae551f782
-- BLAKE3 statement: 36b0299bb855d98119b6cfe1f107fb2f661e264dbfdb7f6e4e0b248ae551f782
-- BLAKE3 C++ proof evidence: cff8db0fee3c001e1a8f424b3afe0a77a8fb3b947a32c7a94bafe7322031a77b
-- C++ equivalence has been checked; this theorem still requires the Lean kernel.
def before (_x : Fin 1 → ℚ) : Term (ℚ) := (.loop 3 (.value (_x 0)) (fun _j0 _s0 => (.add (.value _s0) (.value (_j0 : ℚ)))))
def after (_x : Fin 1 → ℚ) : Term (ℚ) := (.add (.value (_x 0)) (.value ((3) / 1 : ℚ)))
theorem certified : VerifiedRewrite before after where
  equivalent x := by
    simp only [before, after, Term.denote, boundedLoop, ite_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
    all_goals try dsimp +instances only [Term.denote]
    all_goals try rw [ite_apply]
    all_goals change ((((x 0) + (0 : ℚ)) + (1 : ℚ)) + (2 : ℚ)) = ((x 0) + ((3) / 1 : ℚ))
    all_goals first | (ring; done) | (split_ifs; all_goals norm_num at *; all_goals ring)
  cheaper x := by
    change 5 < 21
    decide
end LeanML.Generated.Cert_36b0299bb855d98119b6cfe1f107fb2f661e264dbfdb7f6e4e0b248ae551f782
