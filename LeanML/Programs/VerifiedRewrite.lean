module
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SplitIfs
@[expose] public section
noncomputable section
namespace LeanML.Programs

/-- Row-major tensors with their static shape in the type. -/
abbrev Tensor (shape : List ℕ) := Fin shape.prod → ℚ

/-- A bounded loop; the body sees its zero-based iteration and previous state. -/
def boundedLoop {α : Type} (body : ℕ → α → α) : ℕ → α → α
  | 0, initial => initial
  | n+1, initial => body n (boundedLoop body n initial)

/-- Typed, pure program expressions. Loop bodies bind actual typed values (HOAS).
Inputs and loop locals are represented by `value`; no native code is evaluated.
-/
inductive Term : Type → Type 1
  | value {α : Type} (a : α) : Term α
  | add {α : Type} [Add α] (a b : Term α) : Term α
  | mul {α : Type} [Mul α] (a b : Term α) : Term α
  | neg {α : Type} [Neg α] (a : Term α) : Term α
  | pow {α : Type} [Pow α ℕ] (a : Term α) (n : ℕ) : Term α
  | ifLess {α : Type} (a b : Term ℚ) (yes no : Term α) : Term α
  | tensor {n : ℕ} (cells : Fin n → Term ℚ) : Term (Fin n → ℚ)
  | loop {α : Type} (n : ℕ) (initial : Term α) (body : ℕ → α → Term α) : Term α

/-- Denotational semantics of the emitted program, including actual bounded iteration. -/
def Term.denote {α : Type} : Term α → α
  | .value a => a
  | @add β inst a b => letI : Add β := inst; a.denote + b.denote
  | @mul β inst a b => letI : Mul β := inst; a.denote * b.denote
  | @neg β inst a => letI : Neg β := inst; -a.denote
  | @pow β inst a n => letI : Pow β ℕ := inst; a.denote ^ n
  | .ifLess a b yes no => if a.denote < b.denote then yes.denote else no.denote
  | .tensor cells => fun i => (cells i).denote
  | .loop n initial body => boundedLoop (fun i state => (body i state).denote) n initial.denote

/-- Sum without a hidden Fintype instance, for reproducible concrete tensor costs. -/
def finSum : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + finSum (fun i : Fin n => f i.succ)

/-- Structural cost model used by the C++ DSL, not a machine-time bound.
The loop body's syntax is sampled at iteration zero and the initial value;
generated DSL bodies have value-independent syntax, including both if branches.
-/
def Term.staticCost {α : Type} : Term α → ℕ
  | .value _ => 1
  | @add _ _ a b => 3 + a.staticCost + b.staticCost
  | @mul _ _ a b => 6 + a.staticCost + b.staticCost
  | @neg _ _ a => 2 + a.staticCost
  | @pow _ _ a n => 2 + 4*n + a.staticCost
  | .ifLess a b yes no => 1 + a.staticCost + b.staticCost + yes.staticCost + no.staticCost
  | .tensor cells => 1 + finSum (fun i => (cells i).staticCost)
  | .loop n initial body => 2 + initial.staticCost + n*(1 + (body 0 initial.denote).staticCost)

/-- A genuine rewrite theorem relates denotations and recomputed syntax costs. -/
structure VerifiedRewrite {X α : Type} (before after : X → Term α) : Prop where
  equivalent : ∀ x, (before x).denote = (after x).denote
  cheaper : ∀ x, (after x).staticCost < (before x).staticCost

theorem boundedLoop_zero {α : Type} (body : ℕ → α → α) (initial : α) :
    boundedLoop body 0 initial = initial := rfl

theorem VerifiedRewrite.trans {X α : Type} {a b c : X → Term α}
    (hab : VerifiedRewrite a b) (hbc : VerifiedRewrite b c) : VerifiedRewrite a c where
  equivalent x := (hab.equivalent x).trans (hbc.equivalent x)
  cheaper x := (hbc.cheaper x).trans (hab.cheaper x)
end LeanML.Programs
