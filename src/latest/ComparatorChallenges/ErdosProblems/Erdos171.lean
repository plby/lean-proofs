/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos171

abbrev Word (t n : ℕ) := Fin n → Fin t

def ContainsLine {t n : ℕ} (A : Set (Word t n)) : Prop :=
  ∃ l : Combinatorics.Line (Fin t) (Fin n), Set.range l ⊆ A

theorem erdos_171 :
    ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset (Word t N),
        ε * (t : ℝ) ^ N ≤ (A.card : ℝ) →
          ContainsLine (A : Set (Word t N)) := by
  sorry

end Erdos171
