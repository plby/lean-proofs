/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open Asymptotics
open scoped BigOperators Classical SimpleGraph

noncomputable section


namespace Erdos1021

open scoped Classical in
noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

end Erdos1021

namespace Erdos1021

open scoped Classical in
abbrev CliquePair (k : ℕ) := Set.powersetCard (Fin k) 2

end Erdos1021

namespace Erdos1021

open scoped Classical in
abbrev CliqueSubdivisionVertex (k : ℕ) := Fin k ⊕ CliquePair k

end Erdos1021

namespace Erdos1021

open scoped Classical in
def cliqueSubdivision (k : ℕ) : SimpleGraph (CliqueSubdivisionVertex k) where
  Adj x y :=
    match x, y with
    | Sum.inl i, Sum.inr p => i ∈ (p : Finset (Fin k))
    | Sum.inr p, Sum.inl i => i ∈ (p : Finset (Fin k))
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y <;> simpa using h
  loopless := by
    constructor
    intro x
    cases x <;> simp

end Erdos1021

namespace Erdos1021

open scoped Classical in
noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

end Erdos1021

namespace Erdos1021

open scoped Classical in
noncomputable def janzerAlpha (k : ℕ) : ℝ :=
  ((k : ℝ) - 2) / (2 * k - 3)

open scoped Classical in
def ErdosProblem1021 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
    extremalGrowth (cliqueSubdivision k) =O[atTop]
      polynomialGrowth (3 / 2 - c)

end Erdos1021

namespace Erdos1021

open scoped Classical in
theorem erdosProblem1021 : ErdosProblem1021 := by
  sorry

end Erdos1021

end
