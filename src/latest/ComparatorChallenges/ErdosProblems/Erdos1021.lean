/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1021

noncomputable def extremalGrowth {W : Type*} (H : SimpleGraph W) (n : ℕ) : ℝ :=
  SimpleGraph.extremalNumber n H

abbrev CliquePair (k : ℕ) := Set.powersetCard (Fin k) 2

abbrev CliqueSubdivisionVertex (k : ℕ) := Fin k ⊕ CliquePair k

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

noncomputable def polynomialGrowth (a : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ a

theorem erdos_1021 :
    ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧
      Erdos1021.extremalGrowth (Erdos1021.cliqueSubdivision k) =O[Filter.atTop]
        Erdos1021.polynomialGrowth (3 / 2 - c) := by
  sorry

end Erdos1021
