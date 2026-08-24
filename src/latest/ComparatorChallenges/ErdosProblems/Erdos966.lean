/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos966

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d ≠ 0 ∧ ∀ i : Fin k, a + i * d ∈ A
def HasMonochromaticAP (A : Set ℕ) (k : ℕ) {r : ℕ} (c : ℕ → Fin r) : Prop :=
  ∃ a d : ℕ,
    d ≠ 0 ∧ (∀ i : Fin k, a + i * d ∈ A) ∧
      ∃ y : Fin r, ∀ i : Fin k, c (a + i * d) = y

theorem erdos_966 :
    ∀ k r : ℕ,
      k ≥ 2 → r ≥ 2 →
        ∃ A : Set ℕ,
          ¬ HasAP A (k + 1) ∧ ∀ c : ℕ → Fin r, HasMonochromaticAP A k c := by
  sorry

end Erdos966
