module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-! # Unmasked self-attention
Tokens are finite indexed vectors. The permutation acts on both query and key
indices. Positional encodings and causal masks are deliberately outside this theorem.
-/
noncomputable section
open scoped BigOperators
namespace LeanML.Representation
variable {N D : Type*} [Fintype N] [Fintype D]

def dot (x y : D → ℝ) : ℝ := ∑ d, x d * y d

def softmax (s : N → ℝ) (i : N) : ℝ := Real.exp (s i) / ∑ j, Real.exp (s j)

/-- Reindexing every input reindexes softmax, including its normalizer. -/
theorem softmax_permute (s : N → ℝ) (p : Equiv.Perm N) (i : N) :
    softmax (s ∘ p) i = softmax s (p i) := by
  unfold softmax
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp p (fun j => Real.exp (s j))]

theorem softmax_pos [Nonempty N] (s : N → ℝ) (i : N) : 0 < softmax s i := by
  unfold softmax
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

theorem softmax_sum [Nonempty N] (s : N → ℝ) : ∑ i, softmax s i = 1 := by
  have h : (∑ j, Real.exp (s j)) ≠ 0 := ne_of_gt
    (Finset.sum_pos (fun j _ => Real.exp_pos (s j)) Finset.univ_nonempty)
  simp [softmax, div_eq_mul_inv, ← Finset.sum_mul, h]

/-- Scaled dot-product attention after arbitrary shared tokenwise projections. -/
def attention (scale : ℝ) (Q K V : N → D → ℝ) (i : N) (d : D) : ℝ :=
  ∑ j, softmax (fun k => dot (Q i) (K k) / scale) j * V j d

/-- Attention commutes with any token permutation applied to queries, keys and values. -/
theorem attention_permute (scale : ℝ) (Q K V : N → D → ℝ)
    (p : Equiv.Perm N) (i : N) (d : D) :
    attention scale (Q ∘ p) (K ∘ p) (V ∘ p) i d = attention scale Q K V (p i) d := by
  unfold attention
  have h : (fun k => dot ((Q ∘ p) i) ((K ∘ p) k) / scale) =
      (fun k => dot (Q (p i)) (K k) / scale) ∘ p := rfl
  rw [h]
  simp_rw [softmax_permute]
  exact Equiv.sum_comp p (fun j => softmax (fun k => dot (Q (p i)) (K k)/scale) j * V j d)

/-- Self-attention accepts shared projections; this is the architecture-level equivariance. -/
def selfAttention (scale : ℝ) (q k v : (D → ℝ) → D → ℝ) (X : N → D → ℝ) :=
  attention scale (q ∘ X) (k ∘ X) (v ∘ X)

theorem selfAttention_permute (scale : ℝ) (q k v : (D → ℝ) → D → ℝ)
    (X : N → D → ℝ) (p : Equiv.Perm N) :
    selfAttention scale q k v (X ∘ p) = selfAttention scale q k v X ∘ p := by
  funext i d
  exact attention_permute scale (q ∘ X) (k ∘ X) (v ∘ X) p i d
end LeanML.Representation

noncomputable section
open scoped BigOperators
namespace LeanML.Representation
variable {N D : Type*} [Fintype N] [Fintype D]

/-- Row-vector multiplication by a shared projection matrix. -/
def linearProjection (W : D → D → ℝ) (x : D → ℝ) (j : D) : ℝ := ∑ i, x i*W i j

/-- The matrix self-attention architecture, with the usual square-root head scaling. -/
def matrixSelfAttention (WQ WK WV : D → D → ℝ) (X : N → D → ℝ) : N → D → ℝ :=
  selfAttention (Real.sqrt (Fintype.card D)) (linearProjection WQ)
    (linearProjection WK) (linearProjection WV) X

theorem matrixSelfAttention_permute (WQ WK WV : D → D → ℝ)
    (X : N → D → ℝ) (p : Equiv.Perm N) :
    matrixSelfAttention WQ WK WV (X ∘ p) = matrixSelfAttention WQ WK WV X ∘ p :=
  selfAttention_permute _ _ _ _ X p
end LeanML.Representation
