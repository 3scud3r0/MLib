module
public import LeanML
@[expose] public section
noncomputable section
open LeanML.Information LeanML.Optimization LeanML.Robustness
open LeanML.Reinforcement LeanML.Reliability LeanML.Generative

-- A positive binary margin survives a nonzero perturbation.
example : (0 : ℝ) < 3/4 := by
  let scores : ℝ → Bool → ℝ := fun x c => if c then x else 0
  have hlip : ∀ c, LipschitzWith 1 (fun x => scores x c) := by
    intro c
    cases c
    · exact LipschitzWith.const' (0 : ℝ)
    · exact LipschitzWith.id
  have h := margin_stable scores 1 hlip 1 (3/4) true false (by
    norm_num [scores, Real.dist_eq])
  exact h

-- A boundary crossing is possible without the strict perturbation budget.
example : ¬ StrictWinner (fun x : ℝ => fun c : Bool => if c then x else 0) 0 true := by
  intro h
  have hn := h false (by decide)
  norm_num at hn

-- The DEQ theorem applies to an actual complete-space update.
example (x : ℝ) : ∃! h, deqUpdate id (0 : ℝ →L[ℝ] ℝ) x h = h := by
  apply deq_exists_unique id 0 x LipschitzWith.id
  norm_num

theorem quadraticPL : PolyakLojasiewicz (fun x : ℝ => x^2/2) (fun x => x) 1 0 where
  constant_pos := by norm_num
  lower_bound x := by positivity
  dominance x := by
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith

example (hf : IsLSmooth (fun x : ℝ => x^2/2) (fun x => x) 1) (x : ℝ) (k : ℕ) :
    (gradientIterate (fun x : ℝ => x) 1 x k)^2/2 ≤ (1-(1:ℝ))^k*(x^2/2) := by
  simpa using pl_gradientDescent_rate hf quadraticPL (by norm_num) x k

-- A biased forecast of 3/4 when the observed frequency is 1/2 has Brier loss 5/16.
example : groupedBrier (uniformDistribution : FiniteDistribution Unit) (fun _ => 3/4) (fun _ => 1/2) = 5/16 := by
  norm_num [groupedBrier, uniformDistribution]

-- Single-state discounted reward has value r/(1-1/2) = 2r.
def oneStateMDP (r : ℝ) : FiniteMDP Unit Unit where
  reward _ _ := r
  transition _ _ := uniformDistribution
  discount := 1/2
  discount_lt_one := by norm_num

example (r : ℝ) : bellman (oneStateMDP r) (fun _ => 2*r) = fun _ => 2*r := by
  funext s
  simp [bellman, actionValue, oneStateMDP, uniformDistribution]
  ring

-- For a point-mass prior the posterior mean is its sole center, regardless of noise.
example (m x : ℝ) : posteriorMean (fun _ : Unit => 1) (fun _ => m) 1 x = m := by
  simp [posteriorMean, mixtureDensity, gaussianComponent, Real.exp_ne_zero]

-- Tweedie uses the derivative of the actual density and works away from its centers.
example (m x : ℝ) :
    posteriorMean (fun _ : Unit => 1) (fun _ => m) 1 x =
      x + deriv (fun z => Real.log (mixtureDensity (fun _ : Unit => 1) (fun _ => m) 1 z)) x := by
  simpa using tweedie_finiteGaussian (fun _ : Unit => 1) (fun _ => m) 1 x
    (by norm_num) (by intro _; norm_num)

-- A 1x2 matrix with entrywise error 1 produces dot product 2 on input (1,1).
-- Thus an output bound sqrt(rows)*Delta*B would require the false 2 <= sqrt(2).
example : ¬ (2 : ℝ) ≤ Real.sqrt 2 := entrywise_bound_needs_dimension
