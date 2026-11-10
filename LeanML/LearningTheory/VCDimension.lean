module

public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Data.ENat.Lattice

@[expose] public section

namespace LeanML.LearningTheory
variable {X : Type*} [DecidableEq X]

/-- Finite binary hypothesis classes are represented by their positive sets. -/
abbrev HypothesisClass (X : Type*) := Finset (Finset X)

def Shatters (H : HypothesisClass X) (S : Finset X) : Prop := H.Shatters S

def vcDimension (H : HypothesisClass X) : ℕ := H.vcDim

theorem shattered_card_le_vcDimension (H : HypothesisClass X) (S : Finset X)
    (h : Shatters H S) : S.card ≤ vcDimension H := h.card_le_vcDim
end LeanML.LearningTheory

namespace LeanML.LearningTheory
variable {X : Type*}

/-- Shattering for arbitrary binary hypothesis classes on possibly infinite domains. -/
def ShattersClass (H : Set (X → Bool)) (S : Finset X) : Prop :=
  ∀ labeling : X → Bool, ∃ h ∈ H, ∀ x ∈ S, h x = labeling x

/-- Extended VC dimension: infinity is preserved rather than truncated to a natural number. -/
noncomputable def extendedVCDimension (H : Set (X → Bool)) : ℕ∞ :=
  ⨆ S : {S : Finset X // ShattersClass H S}, (S.val.card : ℕ∞)

theorem ShattersClass.mono {H G : Set (X → Bool)} {S : Finset X}
    (hH : ShattersClass H S) (hHG : H ⊆ G) : ShattersClass G S := by
  intro labeling
  obtain ⟨h, hh, heq⟩ := hH labeling
  exact ⟨h, hHG hh, heq⟩

theorem shattered_card_le_extendedVCDimension (H : Set (X → Bool)) (S : Finset X)
    (h : ShattersClass H S) : (S.card : ℕ∞) ≤ extendedVCDimension H :=
  le_iSup_of_le ⟨S, h⟩ le_rfl

theorem extendedVCDimension_mono {H G : Set (X → Bool)} (hHG : H ⊆ G) :
    extendedVCDimension H ≤ extendedVCDimension G := by
  apply iSup_le
  intro S
  exact le_iSup_of_le ⟨S.val, S.property.mono hHG⟩ le_rfl
end LeanML.LearningTheory
