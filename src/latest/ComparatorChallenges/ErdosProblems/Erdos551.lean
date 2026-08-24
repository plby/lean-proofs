/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open SimpleGraph

namespace Erdos551

def CycleCliqueRamseyProperty (k n N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), cycleGraph k ⊑ G ∨ ¬ G.IndepSetFree n

theorem cycleCliqueRamseyProperty_exists (k n : ℕ) :
    ∃ N, CycleCliqueRamseyProperty k n N := by
  sorry

open scoped Classical in
noncomputable def cycleCliqueRamseyNumber (k n : ℕ) : ℕ :=
  Nat.find (cycleCliqueRamseyProperty_exists k n)

theorem erdos_551 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ, n ≤ k →
      cycleCliqueRamseyNumber k n = (k - 1) * (n - 1) + 1 := by
  sorry

end Erdos551
