/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Nat

namespace Erdos1056b

def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

theorem erdos_1056
    (h1056 : ∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime)
      (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
        AllModProdEqualsOne p boundaries) :
    ∀ᶠ k in Filter.atTop,
      ∃ (p : ℕ) (_ : p.Prime) (Q : Fin k → ℕ) (_ : StrictMono Q)
        (_ : ∀ i, Q i < p), ∀ i j : Fin k, (Q i)! ≡ (Q j)! [MOD p] := by
  sorry

end Erdos1056b
