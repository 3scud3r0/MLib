module

public import LeanML
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

set_option autoImplicit false

open LeanML.Information LeanML.Optimization LeanML.Representation LeanML.LearningTheory

noncomputable def fairCoin : FiniteDistribution (Fin 2) where
  mass _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_two]

example : 0 ≤ shannonEntropy fairCoin := shannonEntropy_nonneg _
example : shannonEntropy fairCoin ≤ Real.log 2 := by
  simpa using shannonEntropy_le_log_card fairCoin

example (s : Fin 3 → ℝ) : (∑ i, softmax s i) = 1 := softmax_sum s

example (scale : ℝ) (Q K V : Fin 3 → Fin 2 → ℝ) (p : Equiv.Perm (Fin 3)) :
    attention scale (Q ∘ p) (K ∘ p) (V ∘ p) = attention scale Q K V ∘ p := by
  funext i d
  exact attention_permute scale Q K V p i d

example (kernel signal : Fin 3 → ℝ) (a : Fin 3) :
    convolution kernel (translate a signal) = translate a (convolution kernel signal) :=
  convolution_translate _ _ _

-- Negative check: the former Lipschitz-only definition is not the new smoothness condition.
example : ¬ IsLSmooth (fun x : ℝ => x) (fun _ => 0) 1 := by
  intro h
  have hc := h.hasGradient 0
  have hd : HasDerivAt (fun x : ℝ => x) 0 0 := by
    exact HasGradientAt.hasDerivAt' hc
  have hid := hasDerivAt_id (0:ℝ)
  have hzero : (0:ℝ) = 1 := hd.unique hid
  norm_num at hzero

example : relu (-3) = 0 := by norm_num [relu]
example : relu 4 = 4 := by norm_num [relu]

/-- A nonconstant objective with a certified, nonzero gradient. -/
theorem quadraticSmooth : IsLSmooth (fun x : ℝ => x^2/2) (fun x => x) 1 where
  constant_pos := by norm_num
  hasGradient x := by
    have h : HasDerivAt (fun y : ℝ => y^2/2) x x := by
      convert ((hasDerivAt_id' x).fun_pow 2).div_const 2 using 1; ring
    exact h.hasGradientAt'
  lipschitz x y := by simp

example (x : ℝ) : (x-(1/(1:ℝ))*x)^2/2 ≤ x^2/2-(1/(2*(1:ℝ)))*‖x‖^2 := by
  simpa [smul_eq_mul] using gradient_descent_step_decreases quadraticSmooth x

example (x : ℝ) (k : ℕ) (hk : 0 < k) :
    (gradientIterate (fun x : ℝ => x) 1 x k)^2/2 ≤ ‖x‖^2/(2*k) := by
  have hc : FirstOrderConvex (fun x : ℝ => x^2/2) (fun x => x) := by
    intro a b
    simp only [Real.inner_apply]
    nlinarith [sq_nonneg (a-b)]
  simpa using gradientDescent_rate (η := (1:ℝ)) quadraticSmooth hc (by norm_num) (by norm_num) x 0 k hk
