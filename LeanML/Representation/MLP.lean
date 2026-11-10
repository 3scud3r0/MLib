module

public import LeanML.Representation.Activation
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

noncomputable section
open scoped BigOperators
namespace LeanML.Representation

/-- A dense affine layer followed by a coordinatewise activation. -/
structure DenseLayer (input output : ℕ) where
  weight : Matrix (Fin output) (Fin input) ℝ
  bias : Fin output → ℝ

def DenseLayer.eval {input output : ℕ} (layer : DenseLayer input output)
    (σ : ℝ → ℝ) (x : Fin input → ℝ) : Fin output → ℝ :=
  fun i => σ ((∑ j, layer.weight i j*x j)+layer.bias i)

/-- A scalar network with one hidden layer of finite width. -/
structure ShallowNetwork (input width : ℕ) where
  hidden : DenseLayer input width
  outputWeight : Fin width → ℝ
  outputBias : ℝ

def ShallowNetwork.eval {input width : ℕ} (net : ShallowNetwork input width)
    (σ : ℝ → ℝ) (x : Fin input → ℝ) : ℝ :=
  (∑ i, net.outputWeight i*net.hidden.eval σ x i)+net.outputBias

theorem DenseLayer.continuous_eval {input output : ℕ} (layer : DenseLayer input output)
    {σ : ℝ → ℝ} (hσ : Continuous σ) : Continuous (layer.eval σ) := by
  apply continuous_pi
  intro i
  apply hσ.comp
  apply Continuous.add _ continuous_const
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

theorem ShallowNetwork.continuous_eval {input width : ℕ} (net : ShallowNetwork input width)
    {σ : ℝ → ℝ} (hσ : Continuous σ) : Continuous (net.eval σ) := by
  apply Continuous.add _ continuous_const
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((continuous_apply i).comp (net.hidden.continuous_eval hσ))
end LeanML.Representation

namespace LeanML.Representation
/-- Feedforward networks with checked input/output dimensions at every composition. -/
inductive MLP : ℕ → ℕ → Type
  | layer {input output : ℕ} (dense : DenseLayer input output) : MLP input output
  | comp {input hidden output : ℕ} (first : MLP input hidden) (second : MLP hidden output) :
      MLP input output

noncomputable def MLP.eval {input output : ℕ} (σ : ℝ → ℝ) :
    MLP input output → (Fin input → ℝ) → Fin output → ℝ
  | .layer dense => dense.eval σ
  | .comp first second => second.eval σ ∘ first.eval σ

theorem MLP.continuous_eval {input output : ℕ} (net : MLP input output)
    {σ : ℝ → ℝ} (hσ : Continuous σ) : Continuous (net.eval σ) := by
  induction net with
  | layer dense => exact dense.continuous_eval hσ
  | comp first second ihfirst ihsecond => exact ihsecond.comp ihfirst
end LeanML.Representation
