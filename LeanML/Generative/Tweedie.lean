module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
@[expose] public section
noncomputable section
open scoped BigOperators
namespace LeanML.Generative
variable {I : Type*} [Fintype I] [Nonempty I]

/-- Unnormalized one-dimensional Gaussian mixture components, variance `v`. -/
def gaussianComponent (weight center : ℝ) (v x : ℝ) : ℝ :=
  weight*Real.exp (-((x-center)^2)/(2*v))

def mixtureDensity (weight center : I → ℝ) (v x : ℝ) : ℝ :=
  ∑ i, gaussianComponent (weight i) (center i) v x

def mixtureDerivative (weight center : I → ℝ) (v x : ℝ) : ℝ :=
  ∑ i, gaussianComponent (weight i) (center i) v x * (-(x-center i)/v)

def posteriorMean (weight center : I → ℝ) (v x : ℝ) : ℝ :=
  (∑ i, center i*gaussianComponent (weight i) (center i) v x)/mixtureDensity weight center v x

theorem mixtureDensity_pos (weight center : I → ℝ) (v x : ℝ) (hw : ∀ i, 0 < weight i) :
    0 < mixtureDensity weight center v x :=
  Finset.sum_pos (fun i _ => mul_pos (hw i) (Real.exp_pos _)) Finset.univ_nonempty

omit [Nonempty I] in
/-- Differentiate the actual Gaussian density, not an assumed score field. -/
theorem mixtureDensity_hasDeriv (weight center : I → ℝ) (v x : ℝ) (hv : 0 < v) :
    HasDerivAt (mixtureDensity weight center v) (mixtureDerivative weight center v x) x := by
  apply HasDerivAt.fun_sum
  intro i _
  change HasDerivAt (fun z => weight i*Real.exp (-((z-center i)^2)/(2*v)))
    (weight i*Real.exp (-((x-center i)^2)/(2*v)) * (-(x-center i)/v)) x
  have hd : HasDerivAt (fun z : ℝ => -((z-center i)^2)/(2*v)) (-(x-center i)/v) x := by
    convert (((hasDerivAt_id' x).sub_const (center i)).fun_pow 2).fun_neg.div_const (2*v) using 1
    field_simp [ne_of_gt hv]
    ring
  convert hd.exp.const_mul (weight i) using 1
  ring

/-- The mixture's logarithmic score follows from its certified derivative. -/
theorem mixtureLog_hasDeriv (weight center : I → ℝ) (v x : ℝ)
    (hv : 0 < v) (hw : ∀ i, 0 < weight i) :
    HasDerivAt (fun z => Real.log (mixtureDensity weight center v z))
      (mixtureDerivative weight center v x/mixtureDensity weight center v x) x :=
  (mixtureDensity_hasDeriv weight center v x hv).log (ne_of_gt (mixtureDensity_pos weight center v x hw))

/-- Tweedie's identity for a finite discrete prior with scalar Gaussian observation noise. -/
theorem tweedie_finiteGaussian (weight center : I → ℝ) (v x : ℝ)
    (hv : 0 < v) (hw : ∀ i, 0 < weight i) :
    posteriorMean weight center v x = x+v*deriv (fun z => Real.log (mixtureDensity weight center v z)) x := by
  rw [(mixtureLog_hasDeriv weight center v x hv hw).deriv]
  have hs : mixtureDerivative weight center v x =
      -(1/v)*(x*mixtureDensity weight center v x-
        ∑ i, center i*gaussianComponent (weight i) (center i) v x) := by
    unfold mixtureDerivative mixtureDensity
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  unfold posteriorMean
  field_simp [ne_of_gt hv, ne_of_gt (mixtureDensity_pos weight center v x hw)]
  ring
end LeanML.Generative
