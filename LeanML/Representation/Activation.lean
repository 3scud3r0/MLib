module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section
namespace LeanML.Representation

def relu (x : ℝ) : ℝ := max 0 x

theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_left _ _

@[simp] theorem relu_of_nonneg {x : ℝ} (hx : 0 ≤ x) : relu x = x := max_eq_right hx

@[simp] theorem relu_of_nonpos {x : ℝ} (hx : x ≤ 0) : relu x = 0 := max_eq_left hx

theorem continuous_relu : Continuous relu := continuous_const.max continuous_id

abbrev sigmoid := Real.sigmoid

theorem continuous_sigmoid : Continuous sigmoid := _root_.continuous_sigmoid
end LeanML.Representation
