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
namespace LeanML.Generated.Cert_0bf8820827506c39de9052eaad5d4b953a20be1735f3c24d32ab80acb85a1968
-- BLAKE3 statement: 0bf8820827506c39de9052eaad5d4b953a20be1735f3c24d32ab80acb85a1968
-- BLAKE3 C++ proof evidence: 2066a175d79e74c7e8ab17fda5ed605568a1e88dbbba92499dacb9da33af6d02
-- C++ equivalence has been checked; this theorem still requires the Lean kernel.
def outputShape : List ℕ := [2]
theorem shape_size : outputShape.prod = 2 := by decide
def before (_x : Fin 2 → ℚ) : Term (Fin 2 → ℚ) := (.loop 2 (.tensor ![(.value (_x 0)), (.value (_x 1))]) (fun _j0 _s0 => (.add (.value _s0) (.tensor ![(.value ((1) / 1 : ℚ)), (.value (_j0 : ℚ))]))))
def after (_x : Fin 2 → ℚ) : Term (Fin 2 → ℚ) := (.tensor ![(.add (.value (_x 0)) (.value ((2) / 1 : ℚ))), (.add (.value (_x 1)) (.value ((1) / 1 : ℚ)))])
theorem certified : VerifiedRewrite before after where
  equivalent x := by
    funext i
    fin_cases i
    · simp only [before, after, Term.denote, boundedLoop, ite_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
      all_goals try dsimp +instances only [Term.denote]
      all_goals try rw [ite_apply]
      all_goals change (((x 0) + ((1) / 1 : ℚ)) + ((1) / 1 : ℚ)) = ((x 0) + ((2) / 1 : ℚ))
      all_goals first | (ring; done) | (split_ifs; all_goals norm_num at *; all_goals ring)
    · simp only [before, after, Term.denote, boundedLoop, ite_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]
      all_goals try dsimp +instances only [Term.denote]
      all_goals try rw [ite_apply]
      all_goals change (((x 1) + (0 : ℚ)) + (1 : ℚ)) = ((x 1) + ((1) / 1 : ℚ))
      all_goals first | (ring; done) | (split_ifs; all_goals norm_num at *; all_goals ring)
  cheaper x := by
    change 11 < 21
    decide
end LeanML.Generated.Cert_0bf8820827506c39de9052eaad5d4b953a20be1735f3c24d32ab80acb85a1968
