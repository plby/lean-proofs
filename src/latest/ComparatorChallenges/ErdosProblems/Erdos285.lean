/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped BigOperators Topology Real

namespace Erdos285

noncomputable section

open scoped Classical in
/-- Erdős Problem 285: the least possible largest denominator in a
`k + 1`-term representation of `1` by distinct unit fractions is asymptotic
to `e / (e - 1) * (k + 1)`. -/
theorem erdos_285 :
    ∀ᵉ (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)),
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S,
        f k = (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) := by
  sorry
