/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1138

noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

noncomputable def realPi (t : ℝ) : ℕ := Nat.primeCounting ⌊t⌋₊

noncomputable def maxPrimeGap (x : ℝ) : ℕ :=
  Finset.sup (Finset.range (Nat.primeCounting' ⌈x⌉₊)) primeGap

def AsymptoticA (C : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X, ∀ y : ℝ, x / 2 < y → y < x →
    |((realPi (y + C * (maxPrimeGap x : ℝ)) : ℝ) - (realPi y : ℝ)) *
      Real.log y / (C * (maxPrimeGap x : ℝ)) - 1| < ε

theorem not_erdos_1138 : ¬(∀ C : ℝ, 1 < C → AsymptoticA C) := by
  sorry

end Erdos1138
