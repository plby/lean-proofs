/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1090

theorem erdos_1090 (k : ℕ) (hk : 3 ≤ k) :
  ∃ (A : Finset (Fin 2 → ℝ)), ∀ (C : A → Fin 2),
    ∃ (S : Finset (Fin 2 → ℝ)), ∃ (hSA : S ⊆ A),
      Collinear ℝ (S : Set (Fin 2 → ℝ)) ∧ S.card ≥ k ∧
      (∀ y ∈ A, y ∈ affineSpan ℝ (S : Set (Fin 2 → ℝ)) → y ∈ S) ∧
      ∃ c, ∀ x (hx : x ∈ S), C ⟨x, hSA hx⟩ = c := by
  sorry

end Erdos1090
