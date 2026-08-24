/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/- The local verification cache for `BoundedGaps` was produced by Lake and
records this generated name for the standard order on `ℕ`.  Re-exporting the
same reducible instance name keeps that cache compatible; a clean Lake build
reduces it to the ordinary `Nat` partial order. -/

/-!
# Erdős Problem 1202

Removing half of the residue classes modulo sufficiently many primes below
`n ^ (1 - ε)` need not leave at most `ε n` positive integers up to `n`.
-/

namespace Erdos1202

/-- Positive integers at most `n` avoiding every indexed forbidden residue set. -/
def survivors {k : ℕ} (n : ℕ) (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun x ↦ ∀ i, (x : ZMod (p i)) ∉ A i

theorem not_erdos_1202 :
    ¬ (∀ ε η : ℝ, 0 < ε → 0 < η →
      ∃ k : ℕ, 0 < k ∧ ∀ (n : ℕ) (p : Fin k → ℕ)
        (A : (i : Fin k) → Finset (ZMod (p i))),
        (∀ i, (p i).Prime) →
        StrictMono p →
        (∀ i, (p i : ℝ) < (n : ℝ) ^ (1 - ε)) →
        (∀ i, (A i).card = (p i - 1) / 2) →
        ((survivors n p A).card : ℝ) ≤ ε * n) := by
  sorry

end Erdos1202
