/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos133

/-- The combinatorial form of having diameter at most two. -/
def HasDiameterTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y

open scoped Classical in
/-- A finite witness used in the definition of the extremal function. -/
structure Model (n d : ℕ) where
  V : Type
  [fintypeV : Fintype V]
  G : SimpleGraph V
  card_eq : Fintype.card V = n
  triangleFree : G.CliqueFree 3
  diameterTwo : HasDiameterTwo G
  degree_le : ∀ v, G.degree v ≤ d

/-- The smallest possible maximum degree of an `n`-vertex triangle-free
diameter-two graph.  This is the standard meaning of the function in
Problem 133. -/
noncomputable def erdos133Function (n : ℕ) : ℕ :=
  sInf {d : ℕ | Nonempty (Model n d)}

theorem erdos_133 :
    (∀ n : ℕ, 64 ≤ n →
      Real.sqrt n - 1 ≤ erdos133Function n ∧
      (erdos133Function n : ℝ) ≤ 4 * Real.sqrt n) ∧
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (erdos133Function n : ℝ))
      (fun n : ℕ => Real.sqrt n) ∧
    ¬ Filter.Tendsto
      (fun n : ℕ => (erdos133Function n : ℝ) / Real.sqrt n)
      Filter.atTop Filter.atTop := by
  sorry

end Erdos133
