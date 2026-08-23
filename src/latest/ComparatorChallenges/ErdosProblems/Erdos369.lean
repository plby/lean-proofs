/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Nat BigOperators

namespace Erdos369

def Nat.largestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else n.primeFactors.sup id
end Erdos369


open Finset Nat BigOperators

namespace Erdos369

open scoped Classical in
theorem erdos_problem_369 (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ a : ℕ, N / 2 ≤ a - (k - 1) ∧ a ≤ N ∧ k ≤ a ∧
        ∀ j : ℕ, j < k → (Nat.largestPrimeFactor (a - j) : ℝ) ≤ ((a - j : ℕ) : ℝ) ^ ε := by
  sorry

end Erdos369
