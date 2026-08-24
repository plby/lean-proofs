/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos722

def IsAdmissible (n k r : ℕ) : Prop :=
  ∀ i < r, Nat.choose (k - i) (r - i) ∣ Nat.choose (n - i) (r - i)

def IsSteinerSystem (n k r : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, B.card = k) ∧
    ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (blocks.filter fun B ↦ A ⊆ B).card = 1

theorem erdos_722 :
    ∀ k r : ℕ, 0 < r → r < k →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAdmissible n k r →
        ∃ blocks : Finset (Finset (Fin n)), IsSteinerSystem n k r blocks := by
  sorry

end Erdos722
