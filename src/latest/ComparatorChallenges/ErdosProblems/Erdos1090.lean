import Mathlib


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

namespace Erdos1090

open scoped Classical in
theorem exists_set_with_strict_monochromatic_line_property (k : ℕ) (hk : 3 ≤ k) :
  ∃ (A : Finset (Fin 2 → ℝ)), ∀ (C : A → Fin 2),
    ∃ (S : Finset (Fin 2 → ℝ)), ∃ (hSA : S ⊆ A),
      Collinear ℝ (S : Set (Fin 2 → ℝ)) ∧ S.card ≥ k ∧
      (∀ y ∈ A, y ∈ affineSpan ℝ (S : Set (Fin 2 → ℝ)) → y ∈ S) ∧
      ∃ c, ∀ x (hx : x ∈ S), C ⟨x, hSA hx⟩ = c := by
  sorry

end Erdos1090
