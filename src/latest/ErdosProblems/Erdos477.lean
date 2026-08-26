/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An affirmative answer to Erdős Problem 477, with f(X) = X^6.
https://www.erdosproblems.com/477

Informal source: Liam Price (GPT 5.6 Sol Pro), Large Powers Tile the Integers.
https://www.overleaf.com/read/whnsywnmykqm#4b6ba0
The general greedy criterion also appears in the earlier source:
https://github.com/Pengbinghui/pipeline-math/blob/main/papers/tiling-complement.pdf
Formal author: Codex.

The proof develops the determinant and curve estimates unconditionally.
Uniqueness is of the two summand values, not of a polynomial input.
-/

import ErdosProblems.Erdos477.SixthPowerTiling

namespace Erdos477

/-- The original problem, with uniqueness of the pair of summand values. -/
def OriginalStatement : Prop :=
  ∃ f : Polynomial ℤ, 2 ≤ f.natDegree ∧
    ∃ A : Set ℤ, IsTiling A (Set.range (fun k : ℤ => f.eval k))

/-- The specified stronger target using nonnegative sixth-power values. -/
def SixthPowerStatement : Prop :=
  ∃ A : Set ℤ, IsTiling A (PowerValues 6)

/-- Replacing integer inputs by nonnegative inputs does not alter the tile. -/
theorem sixth_power_formulation (A : Set ℤ) :
    IsTiling A (Set.range (fun k : ℤ => (Polynomial.X ^ 6 : Polynomial ℤ).eval k)) ↔
      IsTiling A (PowerValues 6) := by
  rw [sixth_power_value_range]

/-- The proposed polynomial has the degree required in the original question. -/
theorem sixth_power_degree_at_least_two :
    2 ≤ (Polynomial.X ^ 6 : Polynomial ℤ).natDegree := by
  rw [sixth_power_natDegree]
  decide

/-- Every integer has a unique decomposition using the set of all integer sixth powers. -/
theorem erdos477_sixth_power :
    ∃ A : Set ℤ, ∀ n : ℤ, ∃! p : ℤ × ℤ,
      p.1 ∈ A ∧ p.2 ∈ Set.range (fun k : ℤ => k ^ 6) ∧ p.1 + p.2 = n := by
  rw [even_power_range 6 (by decide)]
  exact exists_sixth_power_tiling

/-- The original affirmative answer, witnessed by the integer polynomial `X^6`. -/
theorem erdos477 : OriginalStatement := by
  obtain ⟨A, hA⟩ := exists_sixth_power_tiling
  exact ⟨Polynomial.X ^ 6, sixth_power_degree_at_least_two, A,
    (sixth_power_formulation A).mpr hA⟩

theorem erdos_477 : OriginalStatement := erdos477

#print axioms erdos477_sixth_power
-- 'Erdos477.erdos477_sixth_power' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms erdos477
-- 'Erdos477.erdos477' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos477
